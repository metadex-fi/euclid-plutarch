module Dex.Equations where

import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)
import Plutarch.Positive
import qualified Plutarch.Monadic as P

import Dex.Math
import Dex.Types
import Dex.PositiveRational

{-
functions:
    - check swap
    - check add/remove liquidity (how is this redundant with checking swap?)
    - check weight update

TODO optimize: 
    - find good places to preduce PPositiveRationals
    - phoist usage
    - #$ instead of # (..) #
    - list weight reduction instead of iterative pairwise
-}
pmkBalRat :: Term s (PBalance :--> PBalance :--> PPositiveRational)
pmkBalRat = phoistAcyclic $ plam $ \n d -> (mkPositiveRational (pto n) (pto d))

-- TODO add fees
pCheckSwap :: Term s (PBalance :--> PBalance :--> PWeight :--> PWeight :--> PBalance :--> PBalance :--> PBool)
pCheckSwap = phoistAcyclic $ plam $ \oldA oldB wa0 wb0 newA newB -> P.do 

    wa1 <- pletFields @["num", "den"] $ pto $ pto wa0
    wb1 <- pletFields @["num", "den"] $ pto $ pto wb0

    let wan = pfromData wa1.num  -- TODO surely this can be simplified with some deriving or smth
        wad = pfromData wa1.den
        
        wbn = pfromData wb1.num
        wbd = pfromData wb1.den 

        wa2 = wan * wbd -- TODO vs. plet? and below etc
        wb2 = wbn * wad

        gcd = pgcd # wa2 # wb2 

        wa3 = pdiv # wa2 # gcd 
        wb3 = pdiv # wb2 # gcd

    (pBalPow # oldA # newA # wa3) #<= (pBalPow # newB # oldB # wb3)

    where
        pBalPow :: Term s (PBalance :--> PBalance :--> PPositive :--> PPositiveRational)
        pBalPow = plam $ \n d w -> ppow # (preduce # (pmkBalRat # n # d)) # w


pcheckWeightUpdates :: ( PListLike list
    , PElemConstraint list PBalance
    , PElemConstraint list PWeight
    , PElemConstraint list PPositiveRational
    , PElemConstraint list PBool
    ) => Term s (list PBalance :--> list PBalance :--> list PWeight :--> list PWeight :--> PBool)
pcheckWeightUpdates = phoistAcyclic $ plam $ \oldBals newBals oldWeights newWeights -> P.do 
    let ws = pzipWith # (plam $ \w0 w1 -> (pto $ pto w0) / (pto $ pto w1)) # newWeights # oldWeights 
        bs = pzipWith # pmkBalRat # newBals # oldBals
        fits = pzipWith # (plam (#==)) # ws # bs 
    pall # (plam id) # fits


    -- plet (pallWeightUpdates # oldBals # newBals # oldWeights) $ \candidates ->
    --     pall #$ pzipWith # (plam (#==)) # candidates # newWeights -- TODO consider pushing the perror directly in here, and check lazyness
        -- TODO reformulate this whole thing maybe (i.e. multiply balances with weights instead, then check equivalence)

{-
1. update all weights individually
2. reduce them all together (TODO required for v1, but postpone just now)
-}
-- TODO vectors
-- TODO consider implementing zipWith3
-- not used rn
-- pallWeightUpdates :: ( PListLike list
--     , PElemConstraint list PBalance
--     , PElemConstraint list PWeight
--     , PElemConstraint list PPositiveRational
--     ) => Term s (list PBalance :--> list PBalance :--> list PWeight :--> list PWeight)
-- pallWeightUpdates = phoistAcyclic $ plam $ \oldBals newBals oldWeights -> 
--     pzipWith # pmkNewWeights # oldWeights #$ pzipWith # pmkBalRat # newBals # oldBals
--     where 
--         pmkNewWeights :: Term s (PWeight :--> PPositiveRational :--> PWeight)
--         pmkNewWeights = plam $ \weight balRat -> 
--             pcon $ PWeight $ preduce # ((pto $ pto weight) * balRat)


-- not used rn
-- psingleWeightUpdate :: Term s (PBalance :--> PBalance :--> PWeight :--> PWeight)
-- psingleWeightUpdate = phoistAcyclic $ plam $ \oldBal newBal weight -> 
--     pcon $ PWeight $ preduce # ((pto $ pto weight) * (pmkBalRat # newBal # oldBal))


{-
1. start with list of updated weights (individually reduced)
2. get lcm of their denominators
3. multiply lcm with each weight
4. required to reduce them again or...? (for now just do it, optimize later)
-}
-- reduceWeights :: ...
