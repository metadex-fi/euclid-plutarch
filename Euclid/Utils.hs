{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Euclid.Utils where

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
import qualified Plutarch.Monadic as P
import Plutarch.Num
import Plutarch.Maybe
import Plutarch.Api.V1.Value qualified as V1
import Plutarch.Api.V1.AssocMap qualified as AssocMap

import Euclid.Types
-- import Euclid.Value

-- pfirstAsset :: Term s (V1.PValue 'Sorted 'V1.NonZero :--> (PAsData PAsset))
-- pfirstAsset = phoistAcyclic $ plam $ \val -> 
--     plet (pfirstKVPair # (pto val)) $ \fstPair ->
--         mkAssetData 
--             (pfstBuiltin # fstPair)
--             (pfstBuiltin #$ pfirstKVPair #$ pfromData $ psndBuiltin # fstPair)

punpackEuclidDatum :: Term s (POutputDatum :--> PEuclidDatum)
punpackEuclidDatum = phoistAcyclic $ plam $ \datum0 ->
    pmatch datum0 $ \case 
        POutputDatum outputDatumRecord -> P.do
            let datum1  = pfield @"outputDatum" # outputDatumRecord
                datum2  = pfromData datum1
                datum3  = pto datum2
                datum4 = (flip ptryFrom fst) datum3 -- TODO important a) check that it works b) handle what happens if mismatch. Not sure at all this is correct
                datum5 = pfromData datum4
            datum5
        _ -> ptraceError "error unpacking datum"

-- pinsecWith :: 
--     Term
--         s
--         ( (PInteger :--> PInteger :--> PInteger)
--             :--> V1.PValue 'Sorted any0
--             :--> V1.PValue 'Sorted any1
--             :--> V1.PValue 'Sorted 'NoGuarantees
--         )
-- pinsecWith = phoistAcyclic $
--     plam $ \combine x y ->
--         pcon . V1.PValue $
--         AssocMap.pinsecWith
--             # plam (\x y -> AssocMap.pinsecWith # combine # x # y)
--             # pto x
--             # pto y 

-- ppriceOf :: Term s (PPrices :--> V1.PCurrencySymbol :--> V1.PTokenName :--> PInteger)
-- ppriceOf = phoistAcyclic $
--   plam $ \prices ccy tkn ->
--     AssocMap.pfoldAt
--       # ccy
--       # ( pconstant 0 ) -- TODO needs to crash if not found, to avoid dust attacks increasing costs 
--       # plam (\m -> AssocMap.pfoldAt # tkn # (pconstant 0) # plam pfromData # pfromData m)
--       # (pto $ pto prices)

-- TODO do we need those passert*SortedPositive?
-- passertPricesSortedPositive :: Term s (PPrices :--> PPrices)
-- passertPricesSortedPositive = plam $ \prices -> 
--     pcon $ PPrices $ 
--         V1.passertPositive #$ V1.passertSorted #$ pto prices

-- passertAmntsSortedPositive :: Term s (PAmounts :--> PAmounts)
-- passertAmntsSortedPositive = plam $ \amnts -> 
--     pcon $ PAmounts $ 
--         V1.passertPositive #$ V1.passertSorted #$ pto amnts

poutHasNFT :: Term s (PIdNFT :--> PTxOut :--> PBool)
poutHasNFT = phoistAcyclic $ plam $ \nft' output -> P.do
    nft <- pletFields @["currencySymbol", "tokenName"] (pto $ pto nft')
    let value = pfield @"value" # output
        amount = V1.pvalueOf # value # nft.currencySymbol # nft.tokenName
    (amount #== 1)

pinHasNFT :: Term s (PIdNFT :--> PTxInInfo :--> PBool)
pinHasNFT = phoistAcyclic $ plam $ \nft input -> 
    poutHasNFT # nft # (pfield @"resolved" # input)

-- pconcatAll :: (PIsListLike list (list a), PIsListLike list a) => Term s (list (list a) :--> list a)
-- pconcatAll = phoistAcyclic $ plam $ \ls ->
--     pfoldr # pconcat # pnil # ls

-- type PCurrencyTokensPairList = PBuiltinList (PBuiltinPair (PAsData V1.PCurrencySymbol) (PAsData PMap Sorted PTokenName PInteger))
-- type PTokenAmountPairList = PBuiltinList (PBuiltinPair (PAsData PAsset) (PAsData PInteger))

-- WIP
-- pflatten :: Term s (V1.PValue 'Sorted any :--> AssocMap.PMap 'Sorted PAsset PInteger)
-- pflatten = phoistAcyclic $ plam $ \val ->
--     pcon $ AssocMap.PMap $ 
--         pconcatAll #$ pmap # f # (pto $ pto val)

--     where 
--         f' :: Term s ((PAsData V1.PCurrencySymbol) :--> PBuiltinPair (PAsData V1.PTokenName) (PAsData PInteger) :--> PBuiltinPair (PAsData PAsset) (PAsData PInteger))
--         f' = plam $ \ccy pair ->
--             ppairDataBuiltin 
--                 # (mkAssetData ccy (pfstBuiltin # pair))
--                 #$ psndBuiltin # pair

--         f :: Term s (PCurrencyTokensPairList :--> PTokenAmountPairList)
--         f = plam $ \ccyPairs ->
--             pmap # (f' #$ pfstBuiltin # ccyPairs) # (pto $ psndBuiltin # ccyPairs)

-- Thanks for not exporting this, Plutarch
-- | Applies a function to every amount in the map.
pmapAmounts :: Term s ((PInteger :--> PInteger) :--> PValue k a :--> PValue k 'NoGuarantees)
pmapAmounts = phoistAcyclic $
  plam $
    \f v -> pcon $ PValue $ AssocMap.pmap # plam (AssocMap.pmap # f #) # pto v