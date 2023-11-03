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
import Plutarch.Api.V1.Value as V1
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
                '[ "bought" ':= PInteger
                , "sold" ':= PInteger
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PPartialOrd, POrd, PShow)
instance DerivePlutusType PBoughtSold where type DPTStrat _ = PlutusTypeData
instance PTryFrom PData PBoughtSold
instance PTryFrom PData (PAsData PBoughtSold)

pmkBoughtSold :: Term s (PInteger :--> PInteger :--> PBoughtSold)
pmkBoughtSold = phoistAcyclic $ plam $ \bought sold -> pcon $ PBoughtSold $ 
        pdcons @"bought" @PInteger # (pdata bought) 
    #$  pdcons @"sold"   @PInteger # (pdata sold) 
    #   pdnil

papplyToBS :: Term s ((PInteger :--> PInteger :--> PInteger) :--> PBoughtSold :--> PBoughtSold :--> PBoughtSold)
papplyToBS = phoistAcyclic $ plam $ \f x' y' -> P.do 
    x <- pletFields @["bought", "sold"] x'
    y <- pletFields @["bought", "sold"] y'
    ( pmkBoughtSold # (f # x.bought # y.bought) #$ f # x.sold # y.sold )

-- TODO phoistAcyclic below?
instance PNum PBoughtSold where
    x #+ y = papplyToBS # (plam (+)) # x # y
    x #- y = papplyToBS # (plam (-)) # x # y
    x #* y = papplyToBS # (plam (*)) # x # y
    pnegate = phoistAcyclic $ plam $ \x -> pmkBoughtSold 
        # (pnegate #$ pfield @"bought" # x) 
        #$ pnegate #$ pfield @"sold" # x
    pabs = phoistAcyclic $ plam $ \x -> pmkBoughtSold 
        # (pabs #$ pfield @"bought" # x) 
        #$ pabs #$ pfield @"sold" # x
    psignum = ptraceError "signum not implemented"
    -- phoistAcyclic $ plam $ \x' -> P.do 
    --     x <- pletFields @["bought", "sold"] x'
    --     plet (psignum # x.bought) $ \bsig ->
    --         pif ( bsig #== (psignum # x.sold) )
    --             ( bsig )
    --             ( ptraceError "ill-defined signum" )
    pfromInteger x = ptraceError "should not create PBoughtSold from a single Integer"

pdivides :: Term s (PBoughtSold :--> PBoughtSold :--> PBool)
pdivides = plam $ \x' y' -> P.do
    x <- pletFields @["bought", "sold"] x'
    y <- pletFields @["bought", "sold"] y'
    (   ( prem # (pfromData y.bought) # (pfromData x.bought) #== 0 ) #&& 
        ( prem # (pfromData y.sold)   # (pfromData x.sold)   #== 0 )   )

pexp :: Term s (PBoughtSold :--> PBoughtSold :--> PBoughtSold)
pexp = plam $ \b' e' -> P.do
    b <- pletFields @["bought", "sold"] b'
    e <- pletFields @["bought", "sold"] e'
    ( pmkBoughtSold # (pexp_ # (pfromData b.bought) # (pfromData e.bought)) 
                   #$ pexp_ # (pfromData b.sold) # (pfromData e.sold) )

pexp_ :: Term s (PInteger :--> PInteger :--> PInteger)
pexp_ = phoistAcyclic $ pfix #$ plam $ \self b e -> 
    pif (e #== 0)
        ( 1 )
        ( plet (self # b #$ pdiv # e # 2) $ \b2 ->
            b2 * b2 * (pif ((pmod # e # 2) #== 0) 1 b) )

-- instance PIntegral PBoughtSold where
--   pdiv = papplyToBS # pdiv
--   pmod = papplyToBS # pmod
--   pquot = papplyToBS # pquot
--   prem = papplyToBS # prem

pvalueOfAsset :: Term s (V1.PValue anyKey anyAmount :--> PAsset :--> PInteger)
pvalueOfAsset = phoistAcyclic $ plam $ \value asset' -> P.do
    asset <- pletFields @["currencySymbol", "tokenName"] asset'
    ( V1.pvalueOf # value # asset.currencySymbol # asset.tokenName )

pboughtSoldOf :: Term s (PAsset :--> PAsset :--> V1.PValue anyKey anyAmount :--> PBoughtSold)
pboughtSoldOf = phoistAcyclic $ plam $ \bought sold value -> 
    plet (pvalueOfAsset # value) $ \pofAsset ->
        ( pmkBoughtSold # (pofAsset # bought) #$ pofAsset # sold )

pboughtSoldValue :: Term s (PAsset :--> PAsset :--> PBoughtSold :--> V1.PValue 'Sorted 'NoGuarantees)
pboughtSoldValue = phoistAcyclic $ plam $ \boughtAsset soldAsset boughtSoldAmnts -> P.do
    bought <- pletFields @["currencySymbol", "tokenName"] boughtAsset
    sold <- pletFields @["currencySymbol", "tokenName"] soldAsset
    amnts <- pletFields @["bought", "sold"] boughtSoldAmnts
    (   punionWith 
        # (plam (+))
        # ( V1.psingleton # bought.currencySymbol # bought.tokenName # amnts.bought )
        # ( V1.psingleton # sold.currencySymbol   # sold.tokenName   # amnts.sold   )  )

newtype PParam (s :: S)
    = PParam
        ( Term
            s
            ( PDataRecord -- TODO reconsider Sorted vs. Unsorted below
                '[ "owner" ':= V1.PPubKeyHash
                , "virtual" ':= V1.PValue 'Sorted 'Positive -- virtual liqudity, for range pools & sslp  
                , "weights" ':= V1.PValue 'Sorted 'Positive -- actually inverted weights in the AMM-view
                , "jumpSizes" ':= V1.PValue 'Sorted 'Positive 
                , "active" ':= PInteger -- TODO consider using PBool
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
                , "threadNFT" ':= PIdNFT
                , "paramNFT" ':= PIdNFT -- TODO consider hash of owner/tokenname/hash of NFT/...
                , "anchorPrices" ':= V1.PValue 'Sorted 'Positive
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PShow)
instance DerivePlutusType PDirac
    where type DPTStrat _ = PlutusTypeData
instance PTryFrom PData (PAsData PDirac)
instance PTryFrom PData PDirac

-- newtype PLimit (s :: S)
--     = PLimit
--         ( Term
--             s
--             ( PDataRecord -- TODO reconsider Sorted vs. Unsorted below
--                 '["owner" ':= V1.PPubKeyHash -- TODO compare later to deducing this
--                 , "swap" ':= PSwap
--                 ]
--             )
--         )
--     deriving stock (Generic)
--     deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PShow)
-- instance DerivePlutusType PLimit
--     where type DPTStrat _ = PlutusTypeData
-- instance PTryFrom PData (PAsData PLimit)
-- instance PTryFrom PData PLimit

-- newtype PPartial (s :: S)
--     = PPartial
--         ( Term
--             s
--             ( PDataRecord
--                 '["threadNFT" ':= PIdNFT
--                 , "limit" ':= PLimit
--                 ]
--             )
--         )
--     deriving stock (Generic)
--     deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PShow)
-- instance DerivePlutusType PPartial
--     where type DPTStrat _ = PlutusTypeData
-- instance PTryFrom PData (PAsData PPartial)
-- instance PTryFrom PData PPartial

-- newtype PDiode (s :: S)
--     = PDiode
--         ( Term
--             s
--             ( PDataRecord
--                 '["param" ':= PParam
--                 , "ranks" ':= V1.PValue 'Sorted 'Positive -- can only swap assets with leq/lt rank
--                 ]
--             )
--         )
--     deriving stock (Generic)
--     deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PShow)
-- instance DerivePlutusType PDiode
--     where type DPTStrat _ = PlutusTypeData
-- instance PTryFrom PData (PAsData PDiode)
-- instance PTryFrom PData PDiode

-- TODO consider saving bytes by not nesting the underlying constrs
data PEuclidDatum (s :: S)
  = PDiracDatum (Term s (PDataRecord '["dirac" ':= PDirac]))
  | PParamDatum (Term s (PDataRecord '["param" ':= PParam]))
--   | PLimitDatum (Term s (PDataRecord '["limit" ':= PLimit]))
--   | PPartialDatum (Term s (PDataRecord '["partial" ':= PPartial]))
--   | PDiodeDatum (Term s (PDataRecord '["diode" ':= PDiode]))
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
                ,"prices" ':= PBoughtSold -- denominated in some nonexistent currency A0. inverted. (actually exponents)
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
    | PAdminRedeemer (Term s (PDataRecord '[])) -- TODO unnecessary
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow)
instance DerivePlutusType PEuclidAction where type DPTStrat _ = PlutusTypeData
instance PTryFrom PData PEuclidAction