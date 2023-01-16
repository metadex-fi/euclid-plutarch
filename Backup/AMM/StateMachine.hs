
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

newtype PStateNFTCurrency (s :: S) = PStateNFTCurrency (Term s V1.PCurrencySymbol)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow, PEq)
instance DerivePlutusType PStateNFTCurrency where type DPTStrat _ = PlutusTypeNewtype

newtype PStateThreadNFT (s :: S) = PStateThreadNFT (Term s V1.PTokenName)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow, PEq)
instance DerivePlutusType PStateThreadNFT where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData PStateThreadNFT -- TODO vs. (PAsData x) ?

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
                '[ "threadNFT" ':= PStateThreadNFT -- identifies the thread for matching corresponding output to the input evaluated
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
                '[ "stateNFTCurrency" ':= PStateNFTCurrency -- TODO consider slight optimization: derive this instead
                , "mainThreadNFT" ':= PStateThreadNFT
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PShow)
instance DerivePlutusType PStateMachine where type DPTStrat _ = PlutusTypeData

{-
given a context, 
1. go through the consumed inputs
2. for each input belonging to the contract
    2.1. get the state machine datum -> get the thread-NFT and the payload
    2.2. check that the nft is present
    2.3. get the corresponding output and check that the nft is present h
-}
pparseThreadDatums :: Term s ()