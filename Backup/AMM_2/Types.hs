{-# LANGUAGE RoleAnnotations #-}

module Dex.Types where

import Data.ByteString (ByteString)

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
import qualified Plutarch.Monadic as P
import Plutarch.Num
import Plutarch.Lift

newtype PAsset (s :: S)
    = PAsset
        ( Term
            s
            ( PDataRecord
                '[ "currencySymbol" ':= V1.PCurrencySymbol
                , "tokenName" ':= V1.PTokenName
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PPartialOrd, POrd, PShow)
instance DerivePlutusType PAsset where type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PAsset
instance PTryFrom PData (PAsData PAsset)

-- | NFT IDing the thread of an MSM
newtype PThreadNFT (s :: S) = PThreadNFT (Term s PAsset)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PEq, PPartialOrd, POrd, PShow)
instance DerivePlutusType PThreadNFT where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData PThreadNFT

pmkAsset :: Term s (V1.PCurrencySymbol :--> V1.PTokenName :--> PAsset)
pmkAsset = phoistAcyclic $ plam $ \ccy tkn ->
    pcon $ PAsset $
        pdcons @"currencySymbol" @V1.PCurrencySymbol # pdata ccy #$ 
        pdcons @"tokenName" @V1.PTokenName # pdata tkn # 
        pdnil


-- | eligible liquidity. How much of the asset in the ML is eligible for another one
newtype PEL (s :: S) = PEL (Term s PPositive)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PEq, PPartialOrd, POrd, PNum, PFractional, PShow)
instance DerivePlutusType PEL where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData (PAsData PEL)

-- | emitted liquidity tokens. Per-asset, co-determines initial price with EL
newtype PeLPTs (s :: S) = PeLPTs (Term s PPositive)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PEq, PPartialOrd, POrd, PNum, PFractional, PShow)
instance DerivePlutusType PeLPTs where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData (PAsData PeLPTs)

-- | semi-pool id. A hash of a sorted set of assets.
newtype PSPid (s :: S) = PSPid (Term s PByteString)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow, PEq, PPartialOrd, POrd)
instance DerivePlutusType PSPid where type DPTStrat _ = PlutusTypeNewtype    

instance PTryFrom PData (PAsData PSPid) -- TODO vs. (PAsData x) ?

-- | semi-pool slice. Records EL and eLPTs for one token.
newtype PSPslice (s :: S)
    = PSPslice
        ( Term
            s
            ( PDataRecord
                '[ "EL" ':= PEL
                , "eLPTs" ':= PeLPTs
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PShow)
instance DerivePlutusType PSPslice where type DPTStrat _ = PlutusTypeData

instance PTryFrom PData (PAsData PSPslice)

-- | number of (other?) meta-liquidities for the asset
-- TODO PPositive analoguously with min/max, maybe later
newtype PnumThreads (s :: S) = PnumThreads (Term s PInteger)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PEq, PPartialOrd, POrd, PShow)
instance DerivePlutusType PnumThreads where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData (PAsData PnumThreads)

-- | meta-liquidity. Meta because it bundles liquidties of multiple "pools"
type role PML nominal nominal
newtype PML (keys :: KeyGuarantees) (s :: S)
  = PML (Term s (V1.PMap keys PSPid PSPslice))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PShow)
instance DerivePlutusType (PML keys) where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData (PAsData (PML 'Sorted))

-- | abstract datum for one MSM-thread. In practice: one ML.
type role PmsmThreadDatum nominal nominal -- TODO check later if this is correct
newtype PmsmThreadDatum (payloadType :: PType) (s :: S)
    = PmsmThreadDatum
        ( Term
            s
            ( PDataRecord
                '[ "threadNFT" ':= PThreadNFT -- Own Thread-ID-NFT. TODO check this aligns
                , "payload" ':= payloadType
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields)
instance DerivePlutusType (PmsmThreadDatum payloadType)
    where type DPTStrat _ = PlutusTypeData

-- TODO do we need both?
instance PTryFrom PData payloadType => PTryFrom PData (PmsmThreadDatum payloadType)
instance PTryFrom PData payloadType => PTryFrom PData (PAsData (PmsmThreadDatum payloadType))

-- | asset registry. Records available assets and number of MLs each
type role PmsmRegistry nominal nominal nominal
newtype PmsmRegistry (keys :: KeyGuarantees) (msmIdType :: PType) (s :: S)
  = PmsmRegistry (Term s (V1.PMap keys msmIdType PnumThreads))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PShow)
instance DerivePlutusType (PmsmRegistry keys msmIdType) where type DPTStrat _ = PlutusTypeNewtype

instance (PTryFrom PData (PAsData msmIdType), POrd msmIdType, PIsData msmIdType) 
    => PTryFrom PData (PAsData (PmsmRegistry 'Sorted msmIdType))

-- |
newtype PmsmAggregates (aggType :: PType) (s :: S)
    = PmsmAggregates
        ( Term
            s
            ( PDataRecord
                '[ "reads" ':= aggType
                , "spends" ':= aggType
                , "outs" ':= aggType
                , "pairs" ':= PList (PPair PTxOut PTxOut) -- TODO not sure if best types for list and pair
                , "numSpends" ':= PPositive -- not sure if needed
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields)
instance DerivePlutusType (PmsmAggregates aggType)
    where type DPTStrat _ = PlutusTypeData

type PAggregator (aggType :: PType) (s :: S) = Term s (aggType :--> PTxOut :--> aggType)

-- | available action types.
data PActionType (s :: S)
    = PSwapAction (Term s (PDataRecord '[]))
    | PAddLiquidityAction (Term s (PDataRecord '[]))
    | PRemoveLiquidityAction (Term s (PDataRecord '[]))
    | PAddSliceAction (Term s (PDataRecord '[]))
    | PRemoveSliceAction (Term s (PDataRecord '[]))
    | POpenPoolAction (Term s (PDataRecord '[]))
    | PClosePoolAction (Term s (PDataRecord '[]))
    | PListAssetAction (Term s (PDataRecord '[]))
    | PDelistAssetAction (Term s (PDataRecord '[]))
    | PChangeMSMThreadsAction (Term s (PDataRecord '[]))
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow)
instance DerivePlutusType PActionType where type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PActionType

-- | action-redeemer. Always carries the list of involved MSM-IDs for deference, and the intended action. 
newtype PAction (msmIdType :: PType) (s :: S)
    = PAction
        ( Term
            s
            ( PDataRecord
                '[ "actionType" ':= PActionType
                , "actionMSMs" ':= PBuiltinList (PAsData msmIdType) -- TODO surely there must be a nicer option than all the PAsData
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields)
instance DerivePlutusType (PAction msmIdType) where type DPTStrat _ = PlutusTypeData

instance (PTryFrom PData (PAsData msmIdType), POrd msmIdType, PIsData msmIdType) 
    => PTryFrom PData (PAction msmIdType)

-- | action-redeemer.
newtype PActionRedeemer (msmIdType :: PType) (s :: S)
    = PActionRedeemer
        ( Term
            s
            ( PDataRecord
                '[ "mainThreadNFT" ':= PThreadNFT
                , "action" ':= PAction msmIdType
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields)
instance DerivePlutusType (PActionRedeemer msmIdType) where type DPTStrat _ = PlutusTypeData

instance (PTryFrom PData (PAsData msmIdType), POrd msmIdType, PIsData msmIdType) 
    => PTryFrom PData (PActionRedeemer msmIdType)





-------
-- below might carry some useful notes, but starting over above, as a lot of stuff has been done on paper meanwhile


-- | asset-registry-datum. Wrapper to distinguish from MLs
-- TODO determine if required by just continuing for now
{-
four types of liquidity-actions:
    1. adding/removing liquidity to/from existing SP-slice while leaving it intact
    2. adding/removing SP-slice to/from existing SP while leaving it intact
    3. adding/removing SP to/from existing asset while leaving it intact
    4. adding/removing asset
-}
-- data PActionRedeemer (s :: S) 
--     = PSwapRedeemer (Term s (PDataRecord -- swap one asset against another.
--         '[  "firstAsset" ':= PAsset -- useful for (easier) deference:
--         ]))                         -- defer iff firstAsset < MLdatum.asset

--     | PAddLiqRedeemer (Term s (PDataRecord '[])) -- add liquidity to existing SP-slice. (1.)
--     | PRemoveLiqRedeemer (Term s (PDataRecord '[])) -- remove liquidity from SP-slice while leaving it intact. (1.)

--     | PAddSPsliceRedeemer (Term s (PDataRecord '[])) -- add a new SP-slice to an ML. (2.)
--     | PRemoveSPsliceRedeemer (Term s (PDataRecord '[])) -- remove an SP-slice from an ML. (2.)

--     | POpenPoolRedeemer (Term s (PDataRecord '[])) -- add a new connected set of SPs.* (3.)
--     | PClosePoolRedeemer (Term s (PDataRecord '[])) -- withdraw all liquidity from a connected set of SPs.* (3.)

--     | PListAssetRedeemer (Term s (PDataRecord '[])) -- add a new asset-listing to the DEX.** (4.)

-- -- below: postponed for now
--     | PDelistAssetRedeemer (Term s (PDataRecord '[])) -- deregister asset from the DEX.** (4.)
--     | PChangeNumMLsRedeemer (Term s (PDataRecord '[])) -- change number of MLs of an asset.

{-
* note: Theoretically we could drop the connectedness-requirement here, but would increase complexity
 -> i.e. what if LP1 creates SPs A(B) and B(A), then LP2 creates SP A(B,C) - now LP1 can't close their pool
    without destroying counter-SP to A(B,C) and thus deleting the price. Could be solved by i.e. somehow recording 
    that somewhere, but that is -> postponed

** note: includes (3.) for the same reasons
-}
    
--     deriving stock (Generic)
--     deriving anyclass (PlutusType, PIsData, PShow)
-- instance DerivePlutusType PActionRedeemer where type DPTStrat _ = PlutusTypeData