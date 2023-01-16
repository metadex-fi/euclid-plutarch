module Euclid.Value where

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
import qualified Plutarch.Api.V1.Value as V1
import qualified Euclid.Plutarch.AssocMap as AssocMap
import qualified Plutarch.Monadic as P
import Plutarch.Num
import Plutarch.Maybe
import Plutarch.Api.V1.Value qualified as V1


-- | Applies a function to every amount in the map.
-- | copied from Value as it's not exported
pmapAmounts :: Term s ((PInteger :--> PInteger) :--> V1.PValue k a :--> V1.PValue k 'NoGuarantees)
pmapAmounts = phoistAcyclic $
  plam $ \f v -> pcon $ V1.PValue $ AssocMap.pmap # plam (AssocMap.pmap # f #) # pto v

pvalNeg :: Term s (V1.PValue 'Sorted any :--> V1.PValue 'Sorted 'NoGuarantees)
pvalNeg = phoistAcyclic $ plam $ \a -> pmapAmounts # plam negate # a

pvalSub :: Term s (V1.PValue 'Sorted 'Positive :--> V1.PValue 'Sorted 'Positive :--> V1.PValue 'Sorted 'V1.NonZero)
pvalSub = phoistAcyclic $ plam $ \x y -> V1.pnormalize # ((V1.pforgetPositive x) <> (pvalNeg # y))

pvalScale :: Term s (V1.PValue k a :--> PInteger :--> V1.PValue k 'NoGuarantees)
pvalScale = phoistAcyclic $ plam $ \v i -> 
    pcon $ V1.PValue $ AssocMap.pmap # plam (AssocMap.pmap # (plam (i*)) #) # pto v

-- | unsafe because the scalar could be zero
punsafeValScale :: Term s (V1.PValue k V1.NonZero :--> PInteger :--> V1.PValue k 'V1.NonZero)
punsafeValScale = phoistAcyclic $ plam $ \v i -> 
    pcon $ V1.PValue $ AssocMap.pmap # plam (AssocMap.pmap # (plam (i*)) #) # pto v

pnullVal :: Term s (V1.PValue 'Sorted 'V1.NonZero :--> PBool)
pnullVal = phoistAcyclic $ plam $ \val -> AssocMap.pnull # (pto val)

-- -- | note: assumes it's not empty
punaryVal :: Term s (V1.PValue 'Sorted 'V1.NonZero :--> PBool)
punaryVal = phoistAcyclic $ plam $ \val -> 
    pmatch (pto $ pto val) $ \case 
        PCons ccy ccys  ->  (pnull # ccys) 
                        #&& (pnull #$ ptail # (pto $ pfromData $ psndBuiltin # ccy))
        PNil -> ptraceError "empty Value"

pfirstKVPair :: Term s (AssocMap.PMap 'Sorted k v :--> PBuiltinPair (PAsData k) (PAsData v))
pfirstKVPair = phoistAcyclic $ plam $ \m -> phead # (pto m)

pfirstAmnt :: Term s (V1.PValue 'Sorted 'V1.NonZero :--> PInteger)
pfirstAmnt = phoistAcyclic $ plam $ \val -> 
    pfromData $ psndBuiltin 
        #$ pfirstKVPair #$ pfromData $ psndBuiltin 
        #$ pfirstKVPair # (pto val)

ptailVal :: Term s (V1.PValue 'Sorted 'V1.NonZero :--> V1.PValue 'Sorted 'V1.NonZero)
ptailVal = phoistAcyclic $ plam $ \val ->
    pcon $ V1.PValue $ pcon $ AssocMap.PMap $ -- pack it back up
        pmatch (pto $ pto val) $ \case -- unpack Value --> outer Map --> List of Pairs
            PCons cHead cTail -> -- unpack into first ccy-pair and the rest
                pmatch (pto $ pfromData $ psndBuiltin # cHead) $ \case -- unpack first ccy's tkn-Map into List of Pairs
                    PCons _ tTail ->  -- unpack into first tkn-pair and the rest
                        pmatch tTail $ \case
                            PNil -> cTail -- if this was the only tkn: drop the ccy, return rest-ccys
                            PCons _ _ -> -- if >1 tkns in the first ccy, drop the 1st tkn & pack up the rest
                                pcons -- add reduced ccy-Pair to ccy-List-of-Pairs
                                    # ( ppairDataBuiltin 
                                        # (pfstBuiltin # cHead) 
                                        # (pdata $ pcon $ AssocMap.PMap $ tTail)
                                        ) -- pack 1st ccy-name with rest tkn-List-of-Pairs
                                    # cTail
                    PNil -> ptraceError "no tokens"
            PNil -> ptraceError "no currencies"


-- | Prices of each non-first asset denominated in first one. Also listing the first one here
newtype PPrices (s :: S) = PPrices (Term s (V1.PValue Sorted Positive))
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, POrd, PEq, PShow)
instance DerivePlutusType PPrices where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData (PAsData PPrices)

-- | helper for instance PPartialOrd PPrices
pfirstPriceDiff :: Term s (PPrices :--> PPrices :--> PInteger)
pfirstPriceDiff = phoistAcyclic $ plam $ \a b -> 
    pfirstAmnt #$ pvalSub # (pto a) # (pto b)

-- note that this works differently than PValue - 
-- we want to enable POrd, to use prices as keys in PMaps
-- TODO performance
instance PPartialOrd PPrices where 
    a #< b = (pfirstPriceDiff # a # b) #< 0
    a #<= b = (a #== b) #|| (a #< b)