-- {-# LANGUAGE AllowAmbiguousTypes #-} -- TODO added blindly, verify later
-- {-# LANGUAGE ScopedTypeVariables #-} -- TODO does this do anything?
{-# LANGUAGE RoleAnnotations #-}

module Euclid.Types where

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

import Euclid.Value

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

mkAsset :: Term s V1.PCurrencySymbol -> Term s V1.PTokenName -> Term s PAsset
mkAsset ccy tkn = pcon $ PAsset $ 
                pdcons @"currencySymbol" @V1.PCurrencySymbol # (pdata ccy) 
            #$  pdcons @"tokenName" @V1.PTokenName # (pdata tkn) 
            #   pdnil

mkAssetData :: Term s (PAsData V1.PCurrencySymbol) -> Term s (PAsData V1.PTokenName) -> Term s (PAsData PAsset)
mkAssetData ccy tkn = pdata $ pcon $ PAsset $ 
                pdcons @"currencySymbol" @V1.PCurrencySymbol # ccy
            #$  pdcons @"tokenName" @V1.PTokenName # tkn 
            #   pdnil

newtype PIdNFT (s :: S) = PIdNFT (Term s PAsset)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PEq, PPartialOrd, POrd, PShow)
instance DerivePlutusType PIdNFT where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData PIdNFT

newtype PJumpSizes (s :: S) = PJumpSizes (Term s (V1.PValue Sorted Positive))
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PEq, PShow)
instance DerivePlutusType PJumpSizes where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData (PAsData PJumpSizes)

-- TODO make phantom type (asset)
newtype PAmount (s :: S) = PAmount (Term s PPositive)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PEq, PPartialOrd, POrd, PNum, PFractional, PShow)
instance DerivePlutusType PAmount where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData (PAsData PAmount)

newtype PAmounts (s :: S) = PAmounts (Term s (V1.PValue Sorted Positive))
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PEq, PShow)
instance DerivePlutusType PAmounts where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData (PAsData PAmounts)

-- TODO make phantom type (asset & pot. denominator asset)
newtype PPrice (s :: S) = PPrice (Term s PPositive)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PEq, PPartialOrd, POrd, PNum, PFractional, PShow)
instance DerivePlutusType PPrice where type DPTStrat _ = PlutusTypeNewtype

newtype PParam (s :: S)
    = PParam
        ( Term
            s
            ( PDataRecord -- TODO reconsider Sorted vs. Unsorted below
                '[ "owner" ':= V1.PPubKeyHash
                , "jumpSizes" ':= PJumpSizes 
                , "lowerPriceBounds" ':= PPrices   
                , "upperPriceBounds" ':= PPrices   
                , "baseAmountA0" ':= PAmount -- for deducing the default amounts 
                -- , "minJumpFlipA0" ':= PAmount -- for limiting abusive jumps TODO later
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PShow)
instance DerivePlutusType PParam
    where type DPTStrat _ = PlutusTypeData

instance PTryFrom PData (PAsData PParam)
instance PTryFrom PData PParam
    
-- | pre-jump storage of active asset at that time, for reactivation.
-- TODO consider instead mapping simply to an index of the asset-list later
-- TODO PPrices as keys could also be compressed, but leave it for now for correctness purposes
type role PActiveAssets nominal -- TODO reconsider the role thing here and everywhere else
newtype PActiveAssets (s :: S)
  = PActiveAssets (Term s (V1.PMap Sorted PPrices PAsset)) -- TODO reconsider Sorted vs. Unsorted here
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PShow)
instance DerivePlutusType PActiveAssets where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData (PAsData PActiveAssets)

    -- - pre-jump active asset storage: (p2,...,pN) -> asset or p2 -> ... -> pN -> asset
newtype PDirac (s :: S)
    = PDirac
        ( Term
            s
            ( PDataRecord -- TODO reconsider Sorted vs. Unsorted below
                '["owner" ':= V1.PPubKeyHash -- TODO compare later to deducing this
                , "threadNFT" ':= PIdNFT -- TODO implement the NFT-mechanics around this later
                , "paramNFT" ':= PIdNFT -- TODO consider hash of owner/tokenname/hash of NFT/...
                , "initialPrices" ':= PPrices -- for deducing the default active asset
                , "currentPrices" ':= PPrices
                , "activeAmnts" ':= PAmounts
                , "jumpStorage" ':= PActiveAssets -- (p2,...,pN) -> asset or p2 -> ... -> pN -> asset
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PShow)
instance DerivePlutusType PDirac
    where type DPTStrat _ = PlutusTypeData

instance PTryFrom PData (PAsData PDirac)
instance PTryFrom PData PDirac

data PEuclidDatum (s :: S)
  = PDiracDatum (Term s (PDataRecord '["_0" ':= PDirac]))
  | PParamDatum (Term s (PDataRecord '["_0" ':= PParam]))

  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PEq, PShow)

instance DerivePlutusType PEuclidDatum where type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PEuclidDatum
instance PTryFrom PData (PAsData PEuclidDatum)

-- | redeemer.
data PEuclidAction (s :: S)
    = PAdmin (Term s (PDataRecord '[]))
    | PFlip (Term s (PDataRecord '[]))
    | PJump (Term s (PDataRecord '[]))
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow)
instance DerivePlutusType PEuclidAction where type DPTStrat _ = PlutusTypeData


instance PTryFrom PData PEuclidAction