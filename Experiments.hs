{-# LANGUAGE QualifiedDo #-}

module Experiments where

import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)
import Plutarch.Api.V1.Value
import qualified Plutarch.Monadic as P

-- experiments
alwaysSucceeds0 :: ClosedTerm PValidator
alwaysSucceeds0 = plam $ \_ _ _ -> popaque $ pcon PUnit

{-
  "cborHex": "4746010000222499",
  "d8184a8202 4746010000222499" <-- "scriptref" in reference script utxo
  "hash": "52c6af0c9b744b4eecce838538a52ceb155038b3de68e2bb2fa8fc37",
  "rawHex": "46010000222499"
"d8184a82024746010000222499" <-- "scriptref" in reference script utxo
-}

-- original
-- alwaysSucceeds1 :: ClosedTerm PValidator
-- alwaysSucceeds1 = plam $ \_ _ _ -> popaque (pcon PUnit)

alwaysFails :: ClosedTerm PValidator
alwaysFails = plam $ \_ _ _ -> perror

matchDatumRedeemer :: ClosedTerm PValidator
matchDatumRedeemer = plam $ \d r _ -> pif (d #== r) (popaque $ pcon PUnit) perror

unmatchDatumRedeemer :: ClosedTerm PValidator
unmatchDatumRedeemer = plam $ \d r _ -> pif (d #== r) perror (popaque $ pcon PUnit)

matchAlways :: ClosedTerm (PData :--> (PData :--> (PScriptContext :--> POpaque))) -- verbosely
matchAlways = plam $ \d r _ -> pif (d #== r) (popaque $ pcon PUnit) (popaque $ pcon PUnit)

matchSquare :: ClosedTerm PValidator
matchSquare = plam $ \d r _ -> 
  let dInt = pasInt # d 
      rInt = pasInt # r
  in pif (dInt * dInt #== rInt) (popaque $ pcon PUnit) perror

-- match redeemer to reference utxo datum
matchReference :: ClosedTerm PValidator 
matchReference = plam $ \_ r ctx ->
  let info = pfield @"txInfo" # ctx
      refs = pfield @"referenceInputs" @(PBuiltinList PTxInInfo) # info
      -- cond = plam $ const $ pconstant True
      cond = plam $ \ref ->
        let txo = pfield @"resolved" # ref
            dat = pfield @"datum" # txo
        in pmatch dat $ \case
          POutputDatum inline -> 
            let val = pfield @"outputDatum" # inline
                val' = pfromData $ pto val -- pto unwraps Datum newtype, then pfromData unwraps PAsData PData into PData
            in val' #== r
          _ -> pconstant False
  in pif 
      (pany # cond # refs)
      (popaque $ pcon PUnit)
      perror


pfac :: Term s (PInteger :--> PInteger)
pfac = pfix #$ plam f
  where
    f :: Term s (PInteger :--> PInteger) -> Term s PInteger -> Term s PInteger
    f self n = pif (n #== 1) n $ n * (self #$ n - 1)

phoistPfac :: Term s (PInteger :--> PInteger)
phoistPfac = phoistAcyclic pfac

pfib :: Term s (PInteger :--> PInteger)
pfib = pfix #$ plam $ \self n ->
        pif
          (n #== 0)
          0
          $ pif
            (n #== 1)
            1
            $ self # (n - 1) + self # (n - 2)

phoistPfib :: Term s (PInteger :--> PInteger)
phoistPfib = phoistAcyclic pfib


-- calculations

dB :: Float -> Float -> Float -> Float -> Float -> Float 
dB balA balB a b dA = balB * ((balA / (balA + dA))**(a / b) - 1)

newB :: Float -> Float -> Float -> Float -> Float -> Float 
newB balA balB a b dA = balB + dB balA balB a b dA

pAB :: Float -> Float -> Float -> Float -> Float 
pAB balA balB a b = (balA / a) / (balB / b)


-- PValue

ptestValueEq :: Term s PString
ptestValueEq = P.do
  let ccy1 = pcon $ PCurrencySymbol $ phexByteStr "01"
      ccy2 = pcon $ PCurrencySymbol $ phexByteStr "02"
      tkn3 = pcon $ PTokenName $ phexByteStr "03"
      tkn4 = pcon $ PTokenName $ phexByteStr "04"
      val1 = Plutarch.Api.V1.Value.psingleton # ccy1 # tkn3 # 1
      val2 = Plutarch.Api.V1.Value.psingleton # ccy2 # tkn4 # 1
      val3 = punionWith # (plam (+)) # val1 # val1
      val4 = punionWith # (plam (+)) # val2 # val2
  pshow $ punionWith # (plam (-)) # val1 # val3


-- | type PMintingPolicy = PData :--> Contexts.PScriptContext :--> POpaque
pmintAlways :: ClosedTerm PMintingPolicy
pmintAlways = plam $ \_ _ -> popaque $ pcon PUnit