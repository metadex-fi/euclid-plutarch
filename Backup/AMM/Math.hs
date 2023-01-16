
module Dex.Math where

import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)
import Plutarch.Positive

import Dex.PositiveRational
import Dex.Set
import Dex.Utils

peven :: Term s (PPositive :--> PBool)
peven = phoistAcyclic $ plam $ \x -> (pmod # x # 2) #== 0

ppow :: Term s (PReducedRational :--> PPositive :--> PPositiveRational)
ppow = phoistAcyclic $ plam $ \b e -> ppowCostly # (pto b) # e -- TODO check if this makes it worse
  where 
    ppowCostly :: Term s (PPositiveRational :--> PPositive :--> PPositiveRational)
    ppowCostly = pfix #$ plam pow
    pow :: Term s (PPositiveRational :--> PPositive :--> PPositiveRational)
        -> Term s PPositiveRational 
        -> Term s PPositive 
        -> Term s PPositiveRational
    pow self b e = pif (e #== 1) b $ 
      plet (self # (b * b) # (pdiv # e # 2)) $ \n ->
        pif (peven # e) n $ n * b

pmin :: POrd a => Term s (a :--> a :--> a)
pmin = phoistAcyclic $ plam $ \a b -> pif (a #<= b) a b

pminList :: (POrd a, PIsListLike list a) => Term s (list a :--> a)
pminList = pselfFoldr # pmin 

preducePosList :: PIsListLike list PPositive => Term s (list PPositive :--> list PPositive)
preducePosList = phoistAcyclic $ plam $ \l -> 
  plet (pgcdList # l) $ \gcd ->
    pmap # (pdivBy # gcd) # l
      where 
        pdivBy :: Term s (PPositive :--> PPositive :--> PPositive)
        pdivBy = phoistAcyclic $ plam $ \a b -> pdiv # b # a

pgcdList :: PIsListLike list PPositive => Term s (list PPositive :--> PPositive)
pgcdList = pselfFoldr # pgcd
  
plcmList :: PIsListLike list PPositive => Term s (list PPositive :--> PPositive)
plcmList = phoistAcyclic $ plam $ \l -> 
  pfoldr  # (plam $ (*)) 
          # (pdiv # (phead # l) # (pgcdList # l)) 
          #$ ptail # l
    
