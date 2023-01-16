-- positive builtin rational

module Dex.PositiveRational where

import Data.Text (pack)
import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)
import Plutarch.Positive
import Plutarch.Num
import qualified Plutarch.Monadic as P
import Plutarch.DataRepr
import Plutarch.Rational ( PFractional (..) )

-- import Dex.Math

-- type PPositiveRational =
--   PDataSum -- TODO vs. PDataRecord?
--     '[ '[ "num" ':= PPositive
--         , "den" ':= PPositive
--         ]
--      ]

newtype PPositiveRational (s :: S)
    = PPositiveRational
        ( Term
            s
            ( PDataRecord
                '[ "num" ':= PPositive
                , "den" ':= PPositive
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PShow)
instance DerivePlutusType PPositiveRational where type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PPositiveRational

-- to ensure we are reduced i.e. before writing out or costly computations
newtype PReducedRational (s :: S) = PReducedRational (Term s PPositiveRational)
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PShow, PEq, PPartialOrd, POrd)
instance DerivePlutusType PReducedRational where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData PReducedRational

mkPositiveRational :: Term s PPositive -> Term s PPositive -> Term s PPositiveRational
mkPositiveRational n d = pcon $ PPositiveRational $ 
            pdcons @"num" @PPositive # (pdata n) #$ pdcons @"den" @PPositive # (pdata d) # pdnil


pcombinePosRatsWith :: Term s ( (PPositive :--> PPositive :--> PPositive :--> PPositive :--> a) 
                                :--> PPositiveRational :--> PPositiveRational :--> a )
pcombinePosRatsWith = phoistAcyclic $ plam $ \f x' y' -> P.do 
        x <- pletFields @["num", "den"] x'
        y <- pletFields @["num", "den"] y'
        let xn = pfromData x.num  -- TODO surely this can be simplified with some deriving or smth
            xd = pfromData x.den
            yn = pfromData y.num
            yd = pfromData y.den 
        f # xn # xd # yn # yd

comparePosRatsWith   :: (Term s PPositive -> Term s PPositive -> Term s PBool) 
                    -> Term s PPositiveRational
                    -> Term s PPositiveRational
                    -> Term s PBool
comparePosRatsWith f x y = pcombinePosRatsWith # (plam $ \xn xd yn yd -> f (xn * yd) (xd * yn)) # x # y

instance PEq PPositiveRational where
    (#==) = comparePosRatsWith (#==)

instance PPartialOrd PPositiveRational where
    (#<=) = comparePosRatsWith (#<=)
    (#<) = comparePosRatsWith (#<)

instance POrd PPositiveRational

-- -- NOTE as opposed to PRational, reduction is not invoked automatically
-- -- TODO compare if this is better or worse for performance
instance PNum PPositiveRational where 
    x #+ y = pcombinePosRatsWith # (
            plam $ \xn xd yn yd ->
                mkPositiveRational (xn * yd + yn * xd) (xd * yd)
        ) # x # y
    
    x #- y = pcombinePosRatsWith # (
            plam $ \xn xd yn yd ->
                mkPositiveRational (xn * yd - yn * xd) (xd * yd)
        ) # x # y

    x #* y = pcombinePosRatsWith # (
            plam $ \xn xd yn yd ->
                mkPositiveRational (xn * yn) (xd * yd)
        ) # x # y

    pnegate = phoistAcyclic $ pthrow $ "PPositiveRational.pnegate: no"

    pabs = phoistAcyclic $ plam $ id -- TODO suboptimal?

    psignum = phoistAcyclic $ plam $ const 1 -- TODO suboptimal?

    pfromInteger x
        | x <= 0 =
            pthrow $ "PPositiveRational.pfromInteger: encountered nonpositive: " <> pack (show x)
        | otherwise = mkPositiveRational (pfromInteger x) 1


instance PFractional PPositiveRational where
    precip = phoistAcyclic $ plam $ \x' -> P.do 
        x <- pletFields @["num", "den"] x'
        pcon $ PPositiveRational $ 
            pdcons @"num" @PPositive # x.den #$ pdcons @"den" @PPositive # x.num # pdnil

    x #/ y = x * (precip # y) -- TODO compare performance with direct implementation

    pfromRational = phoistAcyclic $ plam $ \x -> P.do
        PRational n d <- pmatch x
        mkPositiveRational (ptryPositive # n) d

pgcd :: Term s (PPositive :--> PPositive :--> PPositive)
pgcd = phoistAcyclic $ plam $ \a b ->
  pif (b #<= a) (pgcd' # a # b) (pgcd' # b # a)
    where
      -- assumes a >= b
      pgcd' :: Term s (PPositive :--> PPositive :--> PPositive)
      pgcd' = phoistAcyclic $ pfix #$ plam $ f
        where
          f self a b =
            pif
              (b #== 0)
              a
              $ self # b #$ pmod # a # b

plcm :: Term s (PPositive :--> PPositive :--> PPositive)
plcm = phoistAcyclic $ plam $ \a b -> (pdiv # a #$ pgcd # a # b) * b

preduce :: Term s (PPositiveRational :--> PReducedRational)
preduce = phoistAcyclic $ plam $ \x' -> P.do 
    x <- pletFields @["num", "den"] x'
    let n = pfromData x.num  -- TODO surely this can be simplified with some deriving or smth
        d = pfromData x.den
        gcd = pgcd # n # d  -- TODO vs. plet?
    pcon $ PReducedRational $ mkPositiveRational (pdiv # n # gcd) ( pdiv # d # gcd)

-- preduceTwo :: Term s (PPositiveRational :--> PPositiveRational :--> (PPositiveRational, PPositiveRational))
-- preduceTwo = phoistAcyclic $ plam $ \x y -> perror
