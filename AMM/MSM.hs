{-# LANGUAGE AllowAmbiguousTypes #-} -- TODO added blindly, verify later
{-# LANGUAGE ScopedTypeVariables #-} -- TODO does this do anything?

module Dex.MSM where

import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)
import Plutarch.Positive
import Plutarch.Rational
import Plutarch.DataRepr
import qualified PlutusCore as PLC
import Plutarch.Unsafe (punsafeBuiltin)
import qualified Plutarch.Api.V1 as V1
import qualified Plutarch.Api.V1.AssocMap as PMap
import qualified Plutarch.Monadic as P
import Plutarch.Num
import Plutarch.Maybe

import Dex.Types
import Dex.Set
import Dex.Utils

{-
Multi-state-machines - Variant on State Machines. Concepts:

- "thread":
    A single state machine thread, represented by an utxo to be reproduced & updated correctly.
- "deference": 
    All except one threads "defer" to a "main-thread", which runs the actual checks.
- "aggregation-check": 
    The presence of the correct thread-utxos in spends/reads/outputs is checked simultaneously
    with their processing via an aggregation-function given to the state machine. The resulting
    aggregate is then subjected to a "global" check.
- "alignment-check":
    Thread-utxos in spends/outputs need to be "aligned" & checked if updated correctly.

--> MSM defined by:

- aggregation functions (foldable over TxOuts - spents/reads are TxInInfos, but that will be abstracted)
- global check function (inputs: spents/reads/outputs-aggregates, redeemer)
- thread check function (inputs: spent/output TxOut)

- kernel: utxo carrying metadata (kernel-data) about the MSM, identified by the kernel-NFT
- kernel-data: said metadata
- number of threads: non-negotiable part of the kernel-data
- transcriber function (extracting said kernel-data)

- payload: The MSM-specific part of the thread datum
- MSM-ID: identifier for the MSM


implementation details:

- each thread is defined by an unique NFT, which's tokenname is derived (hashed) from 
    - the kernel-NFT
    - the MSM-ID
    - the thread-ID

- the defining aggregation function is wrapped in a general one which also 
    - counts the threads
    - checks the thread-NFTs

- process overview (main-thread):
    - extact the kernel-data from the reads via kernel-NFT (parameter of the contract)
    - get the number of threads from the kernel-data
    - apply aggregation functions to spends/reads/outputs
        - this aggregation also checks that reads and spends are distinct, and sum to number of threads
    - apply global check to the results
    - align threads and apply thread-checks
    -
-}

pmkMSMValidator :: forall msmIdType aggType s. 
    (   PLift aggType, 
        PLift (PmsmAggregates aggType), -- TODO those could be abstracted into the type
        PIsData msmIdType, 
        POrd msmIdType, 
        PTryFrom PData (PAsData msmIdType)
    ) =>
        Term s (aggType :--> PTxOut :--> aggType) -> 
        Term s PThreadNFT -> 
        Term s (PData :--> PData :--> PScriptContext :--> POpaque)
pmkMSMValidator agg kernelNFT = plam $ \d r ctx -> (mkMSMValidator @msmIdType) agg kernelNFT d r ctx

-- TODO advantages vs. disadvantages of plutarch-level here?
mkMSMValidator :: forall msmIdType aggType s. 
    (   PLift aggType, 
        PLift (PmsmAggregates aggType), -- TODO those could be abstracted into the type
        PIsData msmIdType, 
        POrd msmIdType, 
        PTryFrom PData (PAsData msmIdType)
    ) =>
        Term s (aggType :--> PTxOut :--> aggType) -> 
        Term s PThreadNFT -> 
        Term s PData -> 
        Term s PData -> 
        Term s PScriptContext ->
        Term s POpaque
mkMSMValidator agg kernelNFT d'' r'' ctx = P.do 
    -- unpack stuff
    let d' = (flip (ptryFrom @(PmsmThreadDatum PData)) fst) d'' -- TODO just set PData at random for payloadType here, no clue why it works
    let r' = (flip (ptryFrom @(PActionRedeemer msmIdType)) fst) r''
    d <- pletFields @["threadNFT", "payload"] d' -- TODO deconstructing those here vs. later?
    r <- pletFields @["mainThreadNFT", "action"] r'
    let info = pfield @"txInfo" # ctx -- TODO assuming we never need to check scriptPurpose

    -- find out if main or deferring thread and branch accordingly
    let pass = pif  
                ((pfromData r.mainThreadNFT) #< d.threadNFT)
                (deferThread # r.mainThreadNFT # info)
                (mainThread d r info)

    pif pass (popaque $ pcon PUnit) perror

    where
        -- if deferring: Check if mainThreadID-NFT is spent in this tx
        deferThread :: Term s (PThreadNFT :--> PTxInfo :--> PBool)
        deferThread = plam $ \mainThreadNFT info -> -- TODO any advantage to making this Plutarch-level here?
            pany # (pinHasNFT # mainThreadNFT) #$ pfield @"inputs" # info  -- TODO is this lazy? worth making it so, if not? 
        
        mainThread  :: --forall s payloadType. 
                    HRecOf (PmsmThreadDatum payloadType) '["threadNFT", "payload"] s -> 
                    HRecOf (PActionRedeemer msmIdType) '["mainThreadNFT", "action"] s ->
                    Term s PTxInfo ->
                    Term s PBool
                    -- -> Term s (PTxInfo :--> PBool) -- TODO any advantage to making this Plutarch-level here?
        mainThread d r info = 
            -- check there is only one redeemer
            (pnull #$ ptail # (pto $ pfromData (pfield @"redeemers" # info)))
            -- check the main-thread-NFT is our datum-NFT
            #&& ((pfromData r.mainThreadNFT) #< d.threadNFT)
            -- MSM-checks
            #&& (pmsmChecks @aggType @msmIdType agg # kernelNFT # r.action # info)


pfindKernelDatum :: (PIsData msmIdType, POrd msmIdType, PTryFrom PData (PAsData msmIdType)) =>
    Term s (PThreadNFT :--> PBuiltinList PTxInInfo :--> PmsmRegistry 'Sorted msmIdType) -- TODO sorted correct here?
pfindKernelDatum = plam $ \kernelNFT inputs -> P.do 
    let kernelInfo = pfromJust #$ pfind # (pinHasNFT # kernelNFT) # inputs -- TODO vs plet
        kernelUtxo = pfield @"resolved" # kernelInfo 
        datum0  = pfield @"datum" # kernelUtxo
    pmatch datum0 $ \case 
        POutputDatum outputDatumRecord  -> P.do
            let datum1  = pfield @"outputDatum" # outputDatumRecord
                datum2  = pfromData datum1
                datum3  = pto datum2
                datum4 = (flip ptryFrom fst) datum3 -- TODO important a) check that it works b) handle what happens if mismatch. Not sure at all this is correct
                datum5 = pfromData datum4
            datum5

pprocessMSM :: forall aggType msmIdType s.
    (PIsData msmIdType, PLift aggType) =>
    Term s (
        PmsmRegistry 'Sorted msmIdType :--> 
        PBuiltinList PTxInInfo :--> 
        PBuiltinList PTxInInfo :--> 
        PBuiltinList PTxOut :-->
        PAsData msmIdType :--> 
        PmsmAggregates aggType
    )
pprocessMSM = phoistAcyclic $ plam $ \registry reads spends outs msmID' -> P.do
--  for each MSM:
--      get numThreads from registry
    let msmID = pfromData msmID'
        numThreads = pfromJust #$ PMap.plookup # msmID # (pto registry)
        -- aggregates = pselfFoldr # #  
--      fold over [0..numThreads], each time: 
--          compute NFT
--          try to find in spends
--              if found: try to find in outs 
--                  if found: 
--                      aggregate spend & out (those functions are provided as MSM contract param)
--                      aggegate pair into pair-collection 
--                  if not: fail 
--              if not: try to find in reads 
--                  if found: aggregate read
--                  if not: fail
    perror

    -- where 
    --     paggregate :: Term s ()
    --     paggregate = perror

pmsmChecks :: forall aggType msmIdType s. 
    (   PLift aggType,
        PLift (PmsmAggregates aggType),
        PIsData msmIdType, 
        POrd msmIdType, 
        PTryFrom PData (PAsData msmIdType)
    ) =>
    Term s (aggType :--> PTxOut :--> aggType) -> Term s (PThreadNFT :--> PAction msmIdType :--> PTxInfo :--> PBool) -- TODO any advantage to making this Plutarch-level here?
pmsmChecks agg = plam $ \kernelNFT action' info' -> P.do
    -- unpack stuff
    info <- pletFields @["inputs", "referenceInputs", "outputs", "mint"] info' -- TODO unpacking separately vs. with "redeemer" above?
    action <- pletFields @["actionType", "actionMSMs"] action'

    -- get MSM-registry from kernel
    let msmRegistry = pfindKernelDatum @msmIdType # kernelNFT # info.referenceInputs
        msmIDs = passertSetData # (pfromData action.actionMSMs)
    -- get a map from MSMs to three aggregates and pair-collection
        partialProcessMSM = pprocessMSM @aggType 
                            # msmRegistry 
                            # info.referenceInputs 
                            # info.inputs 
                            # info.outputs
        processedMSMs = pmap # partialProcessMSM # msmIDs
    -- feed this together with action type into main check (provided somewhere as well)

    pconstant True
