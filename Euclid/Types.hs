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
-- import Plutarch.Rational
import Plutarch.DataRepr
import qualified PlutusCore as PLC
import Plutarch.Unsafe (punsafeBuiltin)
import qualified Plutarch.Api.V1 as V1
import Plutarch.Api.V1.Value as V1
import qualified Plutarch.Api.V1.AssocMap as PMap
import qualified Plutarch.Monadic as P
import Plutarch.Num
import Plutarch.Maybe
import Plutarch.Unsafe (punsafeDowncast)
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

-- newtype PBoughtSold (s :: S)
--     = PBoughtSold
--         ( Term
--             s
--             ( PDataRecord
--                 '[ "bought" ':= PInteger
--                 , "sold" ':= PInteger
--                 ]
--             )
--         )
--     deriving stock (Generic)
--     deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PPartialOrd, POrd, PShow)
-- instance DerivePlutusType PBoughtSold where type DPTStrat _ = PlutusTypeData
-- instance PTryFrom PData PBoughtSold
-- instance PTryFrom PData (PAsData PBoughtSold)

-- pmkBoughtSold :: Term s (PInteger :--> PInteger :--> PBoughtSold)
-- pmkBoughtSold = phoistAcyclic $ plam $ \bought sold -> pcon $ PBoughtSold $ 
--         pdcons @"bought" @PInteger # (pdata bought) 
--     #$  pdcons @"sold"   @PInteger # (pdata sold) 
--     #   pdnil

-- papplyToBS :: Term s ((PInteger :--> PInteger :--> PInteger) :--> PBoughtSold :--> PBoughtSold :--> PBoughtSold)
-- papplyToBS = phoistAcyclic $ plam $ \f x' y' -> P.do 
--     x <- pletFields @["bought", "sold"] x'
--     y <- pletFields @["bought", "sold"] y'
--     ( pmkBoughtSold # (f # x.bought # y.bought) #$ f # x.sold # y.sold )

-- pincrement :: Term s (PBoughtSold :--> PBoughtSold)
-- pincrement = plam $ \x' -> P.do 
--     x <- pletFields @["bought", "sold"] x'
--     ( pmkBoughtSold # (x.bought + 1) # (x.sold + 1) )

-- TODO phoistAcyclic below?
-- instance PNum PBoughtSold where
--     x #+ y = papplyToBS # (plam (+)) # x # y
--     x #- y = papplyToBS # (plam (-)) # x # y
--     x #* y = papplyToBS # (plam (*)) # x # y
--     pnegate = phoistAcyclic $ plam $ \x -> pmkBoughtSold 
--         # (pnegate #$ pfield @"bought" # x) 
--         #$ pnegate #$ pfield @"sold" # x
--     pabs = phoistAcyclic $ plam $ \x -> pmkBoughtSold 
--         # (pabs #$ pfield @"bought" # x) 
--         #$ pabs #$ pfield @"sold" # x
--     psignum = ptraceError "signum not implemented"
--     -- phoistAcyclic $ plam $ \x' -> P.do 
--     --     x <- pletFields @["bought", "sold"] x'
--     --     plet (psignum # x.bought) $ \bsig ->
--     --         pif ( bsig #== (psignum # x.sold) )
--     --             ( bsig )
--     --             ( ptraceError "ill-defined signum" )
--     pfromInteger x = ptraceError "should not create PBoughtSold from a single Integer"

-- pdivides :: Term s (PBoughtSold :--> PBoughtSold :--> PBool)
-- pdivides = plam $ \x' y' -> P.do
--     x <- pletFields @["bought", "sold"] x'
--     y <- pletFields @["bought", "sold"] y'
--     (   ( prem # (pfromData y.bought) # (pfromData x.bought) #== 0 ) #&& 
--         ( prem # (pfromData y.sold)   # (pfromData x.sold)   #== 0 )   )

-- pexp :: Term s (PBoughtSold :--> PBoughtSold :--> PBoughtSold)
-- pexp = plam $ \b' e' -> P.do
--     b <- pletFields @["bought", "sold"] b'
--     e <- pletFields @["bought", "sold"] e'
--     ( pmkBoughtSold # (pexp_ # (pfromData b.bought) # (pfromData e.bought)) 
--                    #$ pexp_ # (pfromData b.sold) # (pfromData e.sold) )

-- pexp :: Term s (PInteger :--> PInteger :--> PInteger)
-- pexp = phoistAcyclic $ pfix #$ plam $ \self b e -> 
--     pif (e #== 0)
--         ( 1 )
--         ( plet (self # b #$ pdiv # e # 2) $ \b2 ->
--             b2 * b2 * (pif ((pmod # e # 2) #== 0) 1 b) )

-- from PRational
data PJumpsize s
  = PJumpsize (Term s PInteger) (Term s PInteger)
  deriving stock (Generic)
  deriving anyclass (PlutusType)

instance DerivePlutusType PJumpsize where type DPTStrat _ = PlutusTypeScott

-- preduce :: Term s (PRational :--> PRational)
-- preduce = phoistAcyclic $
--   plam $ \x -> unTermCont $ do
--     PRational xn xd' <- tcont $ pmatch x
--     xd <- tcont . plet $ pto xd'
--     r <- tcont . plet $ pgcd # xn # xd
--     s <- tcont . plet $ psignum # xd
--     pure . pcon $ PRational (s * pdiv # xn # r) $ punsafeDowncast $ s * pdiv # xd # r

instance PNum PJumpsize where
  x' #+ y' = ptraceError "not implemented"
    -- phoistAcyclic
    --   ( plam $ \x y -> unTermCont $ do
    --       PJumpsize xn xd' <- tcont $ pmatch x
    --       PJumpsize yn yd' <- tcont $ pmatch y
    --       xd <- tcont $ plet xd'
    --       yd <- tcont $ plet yd'
    --       pure $ pcon
    --         $ PJumpsize (xn * yd + yn * xd)
    --         $ punsafeDowncast
    --         $ xd * yd
    --   )
    --   # x'
    --   # y'

  -- TODO (Optimize): Could this be optimized with an impl in terms of `#+`.
  x' #- y' = ptraceError "not implemented"
    -- phoistAcyclic
    --   ( plam $ \x y -> unTermCont $ do
    --       PJumpsize xn xd' <- tcont $ pmatch x
    --       PJumpsize yn yd' <- tcont $ pmatch y
    --       xd <- tcont $ plet xd'
    --       yd <- tcont $ plet yd'
    --       pure $ pcon
    --         $ PJumpsize (xn * yd - yn * xd)
    --         $ punsafeDowncast
    --         $ xd * yd
    --   )
    --   # x'
    --   # y'

  x' #* y' =
    phoistAcyclic
      ( plam $ \x y -> unTermCont $ do
          PJumpsize xn xd <- tcont $ pmatch x
          PJumpsize yn yd <- tcont $ pmatch y
          pure $ pcon $ PJumpsize (xn * yn) (xd * yd)
      )
      # x'
      # y'

  pnegate = ptraceError "not implemented"
    -- phoistAcyclic $
    --   plam $ \x ->
    --     pmatch x $ \(PJumpsize xn xd) ->
    --       pcon $ PJumpsize (negate xn) xd

  pabs = ptraceError "not implemented"
    -- phoistAcyclic $
    --   plam $ \x ->
    --     pmatch x $ \(PJumpsize xn xd) ->
    --       pcon $ PJumpsize (abs xn) (abs xd)

  psignum = ptraceError "not implemented"
    -- phoistAcyclic $
    --   plam $ \x' -> plet x' $ \x ->
    --     pif
    --       (x #== 0)
    --       0
    --       $ pif
    --         (x #< 0)
    --         (-1)
    --         1

  -- not implemented to prevent accidents
  pfromInteger n = ptraceError "not implemented" -- pcon $ PJumpsize ((fromInteger n) + 1) (fromInteger n)

pfromJumpsize :: Term s (PInteger :--> PJumpsize)
pfromJumpsize = phoistAcyclic $ plam $ \n -> pcon $ PJumpsize (n + 1) n

pjumpsizePlusOne :: Term s (PJumpsize :--> PInteger)
pjumpsizePlusOne = phoistAcyclic $ plam $ \x -> pmatch x $ \(PJumpsize n _) -> n

pjumpsize :: Term s (PJumpsize :--> PInteger)
pjumpsize = phoistAcyclic $ plam $ \x -> pmatch x $ \(PJumpsize _ d) -> d

pexp :: Term s (PJumpsize :--> PInteger :--> PJumpsize)
pexp = phoistAcyclic $ pfix #$ plam $ \self b e -> 
    pif (e #== 0)
        ( pcon $ PJumpsize 1 1 )
        ( plet (self # b #$ pdiv # e # 2) $ \b2 ->
            pif ((pmod # e # 2) #== 0) (b2 * b2) (b2 * b2 * b) )

-- instance PIntegral PBoughtSold where
--   pdiv = papplyToBS # pdiv
--   pmod = papplyToBS # pmod
--   pquot = papplyToBS # pquot
--   prem = papplyToBS # prem

pvalueOfAsset :: Term s (PAsset :--> V1.PValue anyKey anyAmount :--> PInteger)
pvalueOfAsset = phoistAcyclic $ plam $ \asset' value -> P.do
    asset <- pletFields @["currencySymbol", "tokenName"] asset'
    ( V1.pvalueOf # value # asset.currencySymbol # asset.tokenName )

-- pvalueOfAsset :: Term s (V1.PValue anyKey anyAmount :--> PAsset :--> PInteger)
-- pvalueOfAsset = phoistAcyclic $ plam $ \value asset' -> P.do
--     asset <- pletFields @["currencySymbol", "tokenName"] asset'
--     ( V1.pvalueOf # value # asset.currencySymbol # asset.tokenName )

-- pboughtSoldOf :: Term s (PAsset :--> PAsset :--> V1.PValue anyKey anyAmount :--> PBoughtSold)
-- pboughtSoldOf = phoistAcyclic $ plam $ \bought sold value -> 
--     plet (pvalueOfAsset # value) $ \pofAsset ->
--         ( pmkBoughtSold # (pofAsset # bought) #$ pofAsset # sold )

-- pboughtSoldValue :: Term s (PAsset :--> PAsset :--> PBoughtSold :--> V1.PValue 'Sorted 'NoGuarantees)
-- pboughtSoldValue = phoistAcyclic $ plam $ \boughtAsset soldAsset boughtSoldAmnts -> P.do
--     bought <- pletFields @["currencySymbol", "tokenName"] boughtAsset
--     sold <- pletFields @["currencySymbol", "tokenName"] soldAsset
--     amnts <- pletFields @["bought", "sold"] boughtSoldAmnts
--     (   punionWith 
--         # (plam (+))
--         # ( V1.psingleton # bought.currencySymbol # bought.tokenName # amnts.bought )
--         # ( V1.psingleton # sold.currencySymbol   # sold.tokenName   # amnts.sold   )  )

pboughtSoldValue :: Term s (PAsset :--> PAsset :--> PInteger :--> PInteger :--> V1.PValue 'Sorted 'NoGuarantees)
pboughtSoldValue = phoistAcyclic $ plam $ \boughtAsset soldAsset boughtAmnt soldAmnt -> P.do
    bought <- pletFields @["currencySymbol", "tokenName"] boughtAsset
    sold <- pletFields @["currencySymbol", "tokenName"] soldAsset
    (   punionWith 
        # (plam (+))
        # ( V1.psingleton # bought.currencySymbol # bought.tokenName # boughtAmnt )
        # ( V1.psingleton # sold.currencySymbol   # sold.tokenName   # soldAmnt   )  )

newtype PParam (s :: S)
    = PParam
        ( Term
            s
            ( PDataRecord -- TODO reconsider Sorted vs. Unsorted below
                '[ "owner" ':= V1.PPubKeyHash
                , "virtual" ':= V1.PValue 'Sorted 'Positive -- virtual liqudity, for range pools & sslp  
                , "weights" ':= V1.PValue 'Sorted 'Positive
                , "jumpSizes" ':= V1.PValue 'Sorted 'Positive
                , "active" ':= PInteger -- TODO consider using PBool
                , "minAda" ':= PInteger
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
                , "anchorPrices" ':= V1.PValue 'Sorted 'Positive -- NOTE inverted aka selling-prices
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

-- WIP
-- newtype PPartialSwap (s :: S)
--     = PPartialSwap
--         ( Term
--             s
--             ( PDataRecord
--                 '[ "exponent"   ':= PInteger
--                 , "bought"      ':= PInteger
--                 , "sold"        ':= PInteger
--                 ]
--             )
--         )
--     deriving stock (Generic)
--     deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PShow)
-- instance DerivePlutusType PPartialSwap where type DPTStrat _ = PlutusTypeData
-- instance PTryFrom PData (PAsData PPartialSwap)
-- instance PTryFrom PData PPartialSwap

data PState s
  = PState (Term s PInteger) (Term s PInteger) (Term s PJumpsize) (Term s PJumpsize)
  deriving stock (Generic)
  deriving anyclass (PlutusType)

instance DerivePlutusType PState where type DPTStrat _ = PlutusTypeScott

-- newtype PState (s :: S)
--     = PState
--         ( Term
--             s
--             ( PDataRecord
--                 '["liqBought" ':= PInteger
--                 ,"liqSold" ':= PInteger 
--                 ,"ancJsreBought" ':= PJumpsize
--                 ,"ancJsreSold" ':= PJumpsize
--                 ]
--             )
--         )
--     deriving stock (Generic)
--     deriving anyclass (PlutusType, PIsData, PDataFields, PEq)
-- instance DerivePlutusType PState where type DPTStrat _ = PlutusTypeData
-- instance PTryFrom PData (PAsData PState)
-- instance PTryFrom PData PState


newtype PSubSwap (s :: S)
    = PSubSwap
        ( Term
            s
            ( PDataRecord
                '["deltaBought" ':= PPositive
                ,"deltaSold" ':= PPositive 
                ,"expBought" ':= PInteger
                ,"expSold" ':= PInteger
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PEq)--, PShow)
instance DerivePlutusType PSubSwap where type DPTStrat _ = PlutusTypeData
instance PTryFrom PData (PAsData PSubSwap)
-- instance PTryFrom PData PSubSwap
-- instance PUnsafeLiftDecl PSubSwap



newtype PSwap (s :: S)
    = PSwap
        ( Term
            s
            ( PDataRecord
                '["boughtAsset" ':= PAsset
                ,"soldAsset" ':= PAsset
                , "subSwaps" ':= PBuiltinList (PAsData PSubSwap) -- TODO PList vs. PBuiltinList?
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PEq)--, PShow)
instance DerivePlutusType PSwap where type DPTStrat _ = PlutusTypeData
-- instance PTryFrom PData (PAsData PSwap)
-- instance PTryFrom PData (PAsData (PBuiltinList (PAsData PSubSwap)))
instance PTryFrom PData PSwap

-- | redeemer.
data PEuclidAction (s :: S)
    = PSwapRedeemer (Term s (PDataRecord '["swap" ':= PSwap]))
    | PAdminRedeemer (Term s (PDataRecord '[])) -- TODO unnecessary
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData)--, PShow)
instance DerivePlutusType PEuclidAction where type DPTStrat _ = PlutusTypeData
instance PTryFrom PData PEuclidAction