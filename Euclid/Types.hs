-- {-# LANGUAGE AllowAmbiguousTypes #-} -- TODO added blindly, verify later
-- {-# LANGUAGE ScopedTypeVariables #-} -- TODO does this do anything?
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE OverloadedRecordDot #-}

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
import Plutarch.Api.V1.Value ( pvalueOf )
import qualified Plutarch.Api.V1.AssocMap as PMap
import qualified Plutarch.Monadic as P
import Plutarch.Num
import Plutarch.Maybe

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

newtype PBoughtSold (s :: S)
    = PBoughtSold
        ( Term
            s
            ( PDataRecord
                '[ "bought" ':= PPositive
                , "sold" ':= PPositive
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PPartialOrd, POrd, PShow)
instance DerivePlutusType PBoughtSold where type DPTStrat _ = PlutusTypeData
instance PTryFrom PData PBoughtSold
instance PTryFrom PData (PAsData PBoughtSold)

pmkBoughtSold :: Term s (PPositive :--> PPositive :--> PBoughtSold)
pmkBoughtSold = phoistAcyclic $ plam $ \bought sold -> pcon $ PBoughtSold $ 
        pdcons @"bought" @PPositive # (pdata bought) 
    #$  pdcons @"sold"   @PPositive # (pdata sold) 
    #   pdnil

papplyToBS :: Term s ((PPositive :--> PPositive :--> PPositive) :--> PBoughtSold :--> PBoughtSold :--> PBoughtSold)
papplyToBS = phoistAcyclic $ plam $ \f x' y' -> P.do 
    x <- pletFields @["bought", "sold"] x'
    y <- pletFields @["bought", "sold"] y'
    ( pmkBoughtSold # (f # x.bought # y.bought) #$ f # x.sold # y.sold )

-- TODO phoistAcyclic below?
instance PNum PBoughtSold where
    x #+ y = papplyToBS # (plam $ \x y -> x + y) # x # y
    x #- y = papplyToBS # (plam $ \x y -> x - y) # x # y
    x #* y = papplyToBS # (plam $ \x y -> x * y) # x # y
    pnegate = ptraceError "cannot negate PPositives"
    pabs = plam $ \x -> x
    psignum = plam $ \x -> pmkBoughtSold # 1 # 1
    pfromInteger x = ptraceError "should not create PBoughtSold from a single Integer"

pdivides :: Term s (PBoughtSold :--> PBoughtSold :--> PBool)
pdivides = plam $ \x' y' -> P.do
    x <- pletFields @["bought", "sold"] x'
    y <- pletFields @["bought", "sold"] y'
    (   ( prem # (pto $ pfromData y.bought) # (pto $ pfromData x.bought) #== 0 ) #&& 
        ( prem # (pto $ pfromData y.sold)   # (pto $ pfromData x.sold)   #== 0 )   )

-- instance PIntegral PBoughtSold where
--   pdiv = papplyToBS # pdiv
--   pmod = papplyToBS # pmod
--   pquot = papplyToBS # pquot
--   prem = papplyToBS # prem

pvalueOfAsset :: Term s (V1.PValue Sorted Positive :--> PAsset :--> PPositive)
pvalueOfAsset = phoistAcyclic $ plam $ \value asset' -> P.do
    asset <- pletFields @["currencySymbol", "tokenName"] asset'
    ( ptryPositive #$ pvalueOf # value # asset.currencySymbol # asset.tokenName )

pboughtSoldOf :: Term s (PAsset :--> PAsset :--> V1.PValue Sorted Positive :--> PBoughtSold)
pboughtSoldOf = phoistAcyclic $ plam $ \bought sold value -> 
    plet (pvalueOfAsset # value) $ \pofAsset ->
        ( pmkBoughtSold # (pofAsset # bought) #$ pofAsset # sold )

newtype PParam (s :: S)
    = PParam
        ( Term
            s
            ( PDataRecord -- TODO reconsider Sorted vs. Unsorted below
                '[ "owner" ':= V1.PPubKeyHash
                , "jumpSizes" ':= V1.PValue Sorted Positive 
                , "highestPrices" ':= V1.PValue Sorted Positive   
                , "weights" ':= V1.PValue Sorted Positive
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PShow)
instance DerivePlutusType PParam
    where type DPTStrat _ = PlutusTypeData
instance PTryFrom PData (PAsData PParam)
instance PTryFrom PData PParam

newtype PDirac (s :: S)
    = PDirac
        ( Term
            s
            ( PDataRecord -- TODO reconsider Sorted vs. Unsorted below
                '["owner" ':= V1.PPubKeyHash -- TODO compare later to deducing this
                , "threadNFT" ':= PIdNFT -- TODO implement the NFT-mechanics around this later
                , "paramNFT" ':= PIdNFT -- TODO consider hash of owner/tokenname/hash of NFT/...
                , "lowestPrices" ':= V1.PValue Sorted Positive
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
  = PDiracDatum (Term s (PDataRecord '["dirac" ':= PDirac]))
  | PParamDatum (Term s (PDataRecord '["param" ':= PParam]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PEq, PShow)
instance DerivePlutusType PEuclidDatum where type DPTStrat _ = PlutusTypeData
instance PTryFrom PData PEuclidDatum
instance PTryFrom PData (PAsData PEuclidDatum)


newtype PSwap (s :: S)
    = PSwap
        ( Term
            s
            ( PDataRecord
                '["boughtAsset" ':= PAsset
                ,"soldAsset" ':= PAsset
                ,"prices" ':= PBoughtSold
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PShow)
instance DerivePlutusType PSwap
    where type DPTStrat _ = PlutusTypeData
instance PTryFrom PData (PAsData PSwap)
instance PTryFrom PData PSwap

-- | redeemer.
data PEuclidAction (s :: S)
    = PSwapRedeemer (Term s (PDataRecord '["swap" ':= PSwap]))
    | PAdminRedeemer (Term s (PDataRecord '[]))
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow)
instance DerivePlutusType PEuclidAction where type DPTStrat _ = PlutusTypeData
instance PTryFrom PData PEuclidAction