
module Dex.StateMachine where 

import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)
import qualified Plutarch.Monadic as P
import qualified Plutarch.Api.V1.Value as V1
import qualified Plutarch.Api.V1.Scripts as V1
import Plutarch.DataRepr
import Plutarch.TryFrom

import Dex.Types
import Dex.Utils

{-
structure:

- a state space, consisting of
    - datum space
    - value space
- an action-space, consisting of 
    - redeemer space
- a transition check function, taking old & new datum & value and redeemer

- process:
    - find the input- and output-utxos with the marker-NFT, respectively
        - if not exactly one of each exists, error (creation and closing of state machine postponed for now)
    - extract value & datum from each
    - make case distinction for action (redeemer)
        - if no match: perror
    - get respective transition function
    - feed read-datums (or whole context?), old & new datum & value and redeemer-content into transition-function
-}


newtype PStateMachineNFT (s :: S) = PStateMachineNFT (Term s PAsset) -- TODO better base type, it's a placeholder rn
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow, PEq, PPartialOrd, POrd)
instance DerivePlutusType PStateMachineNFT where type DPTStrat _ = PlutusTypeNewtype


newtype PThreadID (s :: S) = PThreadID (Term s PData) -- TODO consider better base type, it's a placeholder rn
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow, PEq)
instance DerivePlutusType PThreadID where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData PThreadID -- TODO vs. (PAsData x) ?

newtype PPayload (s :: S) = PPayload (Term s PData) -- TODO consider better base type, it's a placeholder rn
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow, PEq)
instance DerivePlutusType PPayload where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData PPayload -- TODO vs. (PAsData x) ?

newtype PStateMachineDatum (s :: S)
    = PStateMachineDatum
        ( Term
            s
            ( PDataRecord
                '[ "threadID" ':= PThreadID -- identifies the thread for matching corresponding output to the input evaluated
                , "payload" ':= PPayload -- the actual datum concerning the state machine logic
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PShow)
instance DerivePlutusType PStateMachineDatum where type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PStateMachineDatum -- TODO vs. (PAsData x) ?


newtype PStateMachine (s :: S)
    = PStateMachine
        ( Term
            s
            ( PDataRecord
                '[ "nft" ':= PStateMachineNFT
                -- , "tokenName" ':= V1.PTokenName
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PShow)
instance DerivePlutusType PStateMachine where type DPTStrat _ = PlutusTypeData


phasNFT :: Term s (PStateMachineNFT :--> PTxOut :--> PBool)
phasNFT = phoistAcyclic $ plam $ \nft' output -> P.do
    nft <- pletFields @["currencySymbol", "tokenName"] (pto nft')
    let value = pfield @"value" # output
        amount = V1.pvalueOf # value # nft.currencySymbol # nft.tokenName
    (amount #== 1)

-- pfindStateUtxo :: Term s (PStateMachineNFT :--> PBuiltinList PTxOut :--> PTxOut)
-- pfindStateUtxo = phoistAcyclic $ plam $ findStateUtxo
    
-- findStateUtxo :: forall s. Term s PStateMachineNFT -> Term s (PBuiltinList PTxOut) -> Term s PTxOut
-- findStateUtxo nft' outputs = pfindUnique # phasNFT' # outputs 
--     where 
--         phasNFT' :: Term s (PTxOut :--> PBool)
--         phasNFT' = phasNFT # PStateMachineNFT

-- pmkStateMachineCheck :: Term s (
--                         (PTxOut :--> PTxOut :--> PData :--> PScriptContext :--> POpaque)
--                         :--> PStateMachineNFT :--> PValidator) -- TODO Haskell or Plutarch level better here?
-- pmkStateMachineCheck = phoistAcyclic $ plam $ \transit nft datum redeemer context -> P.do 
--     let info' = pfield @"txInfo" # context 
--     info <- pletFields @["inputs", "outputs"] info'
--     let outputs = info.outputs 
--         inputs = pmap # (pfield @"resolved") # info.inputs -- TODO this way is not the most efficient, optimize maybe later
--     let input = pfindStateUtxo # nft # inputs
--         output = pfindStateUtxo # nft # outputs
--     (transit # input # output # ?? # redeemer # context)


-- | / O(n) /. Filter elements from a list that don't match the predicate, 
-- | and apply function to those that do
-- not used rn
-- pfilterMap :: 
--     ( PListLike list
--     , PElemConstraint list a
--     , PElemConstraint list b
-- ) => Term s ((a :--> PBool) :--> (a :--> b) :--> list a :--> list b)
-- pfilterMap =
--     phoistAcyclic $ plam $ \predicate f ->
--         precList
--             ( \self x' xs -> plet x' $ \x ->
--                 pif
--                 (predicate # x)
--                 (pcons # (f # x) # (self # xs))
--                 (self # xs)
--             )
--             (const pnil)

pcontStateMachineRecord :: Term s ( PTxOut
                            :-->    (PThreadID :--> PPayload :--> a) -- if matching -- TODO somewhat inefficient, revisit later
                            :-->    a -- if not 
                            :-->    a
                            )
pcontStateMachineRecord = phoistAcyclic $ plam $ \output ifMatch ifNot -> P.do
    let datum0 = pfield @"datum" # output
    pmatch datum0 $ \case 
        POutputDatum outputDatumRecord -> P.do

            let --datum1 :: Term s (PAsData PDatum)
                datum1 = pfield @"outputDatum" # outputDatumRecord

                --datum2 :: Term s PDatum
                datum2 = pfromData datum1 -- pfromData :: Term s (PAsData a) -> Term s a

                --datum3 :: Term s PData -- newtype PDatum (s :: S) = PDatum (Term s PData)
                datum3 = pto datum2  -- pto :: Term s a -> Term s (PInner a)

{-
(flip ptryFrom fst . pto)
  :: forall {a :: PType} {r :: PType} {s :: S}.
     PTryFrom (PInner a) r =>
     Term s a -> Term s r

((flip ptryFrom fst) . pto)
  :: forall {a :: PType} {r :: PType} {s :: S}.
     PTryFrom (PInner a) r =>
     Term s a -> Term s r

(flip ptryFrom) fst
  :: forall {a :: PType} {r :: PType} {s :: S}.
     PTryFrom a r =>
     Term s a -> Term s r

flip ptryFrom
  :: forall {a :: PType} {b :: PType} {s :: S} {r :: PType}.
     PTryFrom a b =>
     ((Term s b,
       Plutarch.Reducible.GReduce
         (Plutarch.TryFrom.PTryFromExcess a b s)
         (GHC.Generics.Rep (Plutarch.TryFrom.PTryFromExcess a b s)))
      -> Term s r)
     -> Term s a -> Term s r

ptryFrom
  :: forall (b :: PType) (a :: PType) (s :: S) (r :: PType).
     PTryFrom a b =>
     Term s a
     -> ((Term s b,
          Plutarch.Reducible.Reduce (Plutarch.TryFrom.PTryFromExcess a b s))
         -> Term s r)
     -> Term s r
-}
                --datum4 :: Term s (PAsData PStateMachineDatum)
                -- below: try and convert PData into PStateMachineDatum
                -- TODO important - below: a) check that it works b) handle what happens if mismatch. Not sure at all this is correct
                datum4 = (flip ptryFrom fst) datum3

                --datum5 :: Term s PStateMachineDatum
                -- datum5 = pfromData datum4 -- this should throw an error, hoping for compile time error --> it does indeed!

            pmatch datum4 $ \case 
                PStateMachineDatum stateMachineRecord -> P.do
                    smr <- pletFields @["threadID", "payload"] stateMachineRecord
                    (ifMatch # smr.threadID # smr.payload)
                _ -> ifNot
        _ -> ifNot

pcorresponds :: Term s (PStateMachineNFT :--> PThreadID :--> PTxOut :--> PBool)
pcorresponds = phoistAcyclic $ plam $ \nft id output -> 
    (phasNFT # nft # output) #&& 
    (pcontStateMachineRecord 
        # output
        # (plam $ \threadID _ -> (threadID #== id))
        # (pconstant False)
    )

{-
    - check if nft is present
    - try to decompose state-machine-datum into threadID and payload
    - check if correct threadID
    - if passing all, return payload
    - check that there is exactly one return, and if so, return it (unpacked from list)
-}
pgetCorrPayload :: Term s (PStateMachineNFT :--> PThreadID :--> PBuiltinList PTxOut :--> PPayload)
pgetCorrPayload = phoistAcyclic $ plam getCorrPayload

getCorrPayload  :: forall s. Term s (PStateMachineNFT)
            -> Term s (PThreadID)
            -> Term s (PBuiltinList PTxOut)
            -> Term s (PPayload)
getCorrPayload nft threadID outputs = 
    plet (pfindUnique # ppredicate # outputs) $ \output ->
        (pcontStateMachineRecord # output # getPayload' # perror)

    where
        ppredicate :: Term s (PTxOut :--> PBool)
        ppredicate = pcorresponds # nft # threadID

        getPayload' :: Term s (PThreadID :--> PPayload :--> PPayload)
        getPayload' = plam $ \_ payload -> payload




{-
our version of state machines has
    - main thread, which checks
        - the state machine logic
        - the correct consumption & reproduction of all threads
    - auxiliary threads, they only check
        - that the main thread is consumed with it

    --> this requires in the top-level validator logic:
        - case distinction: which type of thread are we dealing with in the particular utxo?
            - we could search the value or look at the datum, datum seems simpler
                - this means the state machine needs to be parameterized by the datum types for main and aux threads 
                - this also means we don't need two different NFTs, no? 
                    - We just need to check that the NFT is present and reproduced in each thread, seems simpler to do this in each thread

or 

- consider a number of state machines
- they are "linked" in a way
    - particularly: there is a "main thread" state machine which checks for presence of the others

- each state machine thread checks
    - presence of the NFT in the presently evaluated utxo
    - presence of the NFT in exactly one output-utxo
    - correct datum-update between those two utxos

--> how to best identify the corresponding output-utxo?
    - option A: have different NFTs for each thread 
        - this would for example work by 
            - sharing currency-symbol, and individual token-names for each thread
            - the input-check would search for any asset in the evaluated utxo with the currency-symbol, then find the corresponding output with that
            --> that would suck compared to option B, as the value of the evaluated utxo is less readily available than the datum
    - option B: with the datum
        - the datum carries - besides the state-machine specific stuff - some identifier of the thread 
        - that makes it also easy to ID the corresponding output-utxo
        - now the sub-validator can just check presence of the singular NFT type in both utxos and correct update of the payload-part of the datum


- TODO problem: confirming the presence of the nft in the currently validating utxo is a pain that way, 
    consider first option (matching everything in the main-thread),
    or a mix of the two (checking nfts in main-thread and datums in each utxo's thread)
-}

-- pfindCorrespondingOutput :: Term s (PStateMachineNFT :--> PThreadID :--> PBuiltinList PTxOut :--> PTxOut)
-- pfindCorrespondingOutput = phoistAcyclic $ plam $ \nft threadID outputs ->
--     plet (pcorresponds # nft # threadID) $ \f ->
--         (pfindUnique # f # outputs)

-- pmkStateMachineValidator :: Term s (PStateMachine :--> PValidator) -- TODO Haskell or Plutarch level better here?
-- pmkStateMachineValidator phoistAcyclic $ plam $ \stateMachine datum redeemer context -> P.do 
--     -- 1. unwrap datum into PStateMachineDatum, then into threadID and payload
--     stateMachineDatum <- pmatch datum
--     case stateMachineDatum of 
--         PStateMachineDatum inputDatumRecord' -> P.do 
--             inputDatumRecord <- pletFields @["threadID", "payload"] inputDatumRecord'
--     -- 2. find corresponding output-utxo with the same threadID in the datum (TODO - consider later if this could be optimized significantly)
--             let outputs = pfield @"outputs" $# pfield @"txInfo" # context 
--                 output = pfindCorrespondingOutput # outputs # inputDatumRecord.threadID
--     -- 3. check presence of nft in both utxos (TODO consider checking for the input-utxo further above, later)
--     -- 4. extract payload from output-utxo's datum
--     -- 5. feed both payloads into transition function
--         _ -> perror



    -- stateMachineDatum <- pmatch datum
    -- case stateMachineDatum of
    --     PRegistryDatum  poolsRecord     -> P.do


{-
to be used on input- and corresponding output-utxo, respectively
    - check nft presence
    - return datum-payload
-}
-- pprocessUtxo ::



-- pmkAuxThreadCheck :: Term s (PStateMachine :--> PValidator)
-- pmkAuxThreadCheck = phoistAcyclic $ plam $ \mainNFT datum redeemer context -> P.do
--     let inputs' = pfield @"inputs" #$ pfield @"txInfo" # context
--         inputs = pmap # (pfield @"resolved") # inputs' -- TODO this way is not the most efficient, optimize maybe later
--         _ = pfindStateUtxo # mainNFT # inputs -- TODO check if this works
--     (popaque $ pcon PUnit)
    




-- info :: TxInfo
-- info = scriptContextTxInfo ctx

-- ownInput :: TxOut
-- ownInput = case findOwnInput ctx of
--     Nothing -> traceError "game input missing"
--     Just i  -> txInInfoResolved i

-- ownOutput :: TxOut
-- ownOutput = case getContinuingOutputs ctx of
--     [o] -> o
--     _   -> traceError "expected exactly one game output"

-- outputDatum :: GameDatum
-- outputDatum = case gameDatum ownOutput (`findDatum` info) of
--     Nothing -> traceError "game output datum not found"
--     Just d  -> d