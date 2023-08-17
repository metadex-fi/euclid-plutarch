-- contains only evaluations/experiments for ppow, not actually used

module Power where

import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)


peven :: Term s (PInteger :--> PBool)
peven = phoistAcyclic $ plam $ \x -> (pmod # x # 2) #== 0

{-
ghci> eval $ ppow1 # 20 # 20
"(ExBudget {exBudgetCPU = ExCPU 13774800, exBudgetMemory = ExMemory 28341},[])"
-}
ppow1 :: Term s (PInteger :--> PInteger :--> PInteger) -- cheaper (tied)
ppow1 = plam $ \b e -> pif (e #< 0) (ptraceError "power error") $ pif (e #== 0) 1 $ ppow' # b # e
  where 
    ppow' :: Term s (PInteger :--> PInteger :--> PInteger)
    ppow' = pfix #$ plam pow
    pow :: Term s (PInteger :--> PInteger :--> PInteger) -> Term s PInteger -> Term s PInteger -> Term s PInteger
    pow self b e = pif (e #== 1) b $ 
      plet (self # (b * b) # (pdiv # e # 2)) $ \n ->
        pif (peven # e) n $ n * b
{-
ghci> eval $ ppow2 # 20 # 20
"(ExBudget {exBudgetCPU = ExCPU 13774800, exBudgetMemory = ExMemory 28341},[])"
-}
ppow2 :: Term s (PInteger :--> PInteger :--> PInteger) -- cheaper (tied)
ppow2 = plam $ \b e -> pif (e #< 0) (ptraceError "power error") $ pif (e #== 0) 1 $ ppow' # b # e
  where 
    ppow' :: Term s (PInteger :--> PInteger :--> PInteger)
    ppow' = phoistAcyclic $ pfix #$ plam pow
    pow :: Term s (PInteger :--> PInteger :--> PInteger) -> Term s PInteger -> Term s PInteger -> Term s PInteger
    pow self b e = pif (e #== 1) b $ 
      plet (self # (b * b) # (pdiv # e # 2)) $ \n ->
        pif (peven # e) n $ n * b
{-
ghci> eval $ ppow3 # 20 # 20
"(ExBudget {exBudgetCPU = ExCPU 17135833, exBudgetMemory = ExMemory 29970},[])"
-}
-- > too expensive
-- ppow3 :: Term s (PInteger :--> PInteger :--> PInteger) -- more expensive (tied)
-- ppow3 = plam $ \b e -> pif (e #< 0) (ptraceError "power error") $ pif (e #== 0) 1 $ ppow' # b # e
--   where 
--     ppow' :: Term s (PInteger :--> PInteger :--> PInteger)
--     ppow' = pfix #$ plam pow
--     pOneOrBase :: Term s (PInteger :--> PInteger :--> PInteger)
--     pOneOrBase = plam $ \b e -> (pmod # e # 2) * b + (pmod # (e + 1) # 2)
--     pow :: Term s (PInteger :--> PInteger :--> PInteger) -> Term s PInteger -> Term s PInteger -> Term s PInteger
--     pow self b e = pif (e #== 1) b $ 
--       (self # (b * b) # (pdiv # e # 2)) * (pOneOrBase # b # e)
{-
ghci> eval $ ppow4 # 20 # 20
"(ExBudget {exBudgetCPU = ExCPU 17135833, exBudgetMemory = ExMemory 29970},[])"
-}
-- > too expensive
-- ppow4 :: Term s (PInteger :--> PInteger :--> PInteger) -- more expensive (tied)
-- ppow4 = plam $ \b e -> pif (e #< 0) (ptraceError "power error") $ pif (e #== 0) 1 $ ppow' # b # e
--   where 
--     ppow' :: Term s (PInteger :--> PInteger :--> PInteger)
--     ppow' = pfix #$ plam pow
--     pOneOrBase :: Term s (PInteger :--> PInteger :--> PInteger)
--     pOneOrBase = phoistAcyclic $ plam $ \b e -> (pmod # e # 2) * b + (pmod # (e + 1) # 2)
--     pow :: Term s (PInteger :--> PInteger :--> PInteger) -> Term s PInteger -> Term s PInteger -> Term s PInteger
--     pow self b e = pif (e #== 1) b $ 
--       (self # (b * b) # (pdiv # e # 2)) * (pOneOrBase # b # e)
{-
ghci> eval $ phoistPpow1 # 20 # 20
"(ExBudget {exBudgetCPU = ExCPU 13774800, exBudgetMemory = ExMemory 28341},[])"
-}
phoistPpow1 :: Term s (PInteger :--> PInteger :--> PInteger)
phoistPpow1 = phoistAcyclic ppow1
{-
ghci> eval $ phoistPpow2 # 20 # 20
"(ExBudget {exBudgetCPU = ExCPU 13774800, exBudgetMemory = ExMemory 28341},[])"
-}
phoistPpow2 :: Term s (PInteger :--> PInteger :--> PInteger)
phoistPpow2 = phoistAcyclic ppow2
{-
ghci> eval $ phoistPpow3 # 20 # 20
"(ExBudget {exBudgetCPU = ExCPU 17135833, exBudgetMemory = ExMemory 29970},[])"
-}
-- phoistPpow3 :: Term s (PInteger :--> PInteger :--> PInteger) -- distinctly more expensive
-- phoistPpow3 = phoistAcyclic ppow3
{-
ghci> eval $ phoistPpow4 # 20 # 20
"(ExBudget {exBudgetCPU = ExCPU 17135833, exBudgetMemory = ExMemory 29970},[])"
-}
-- phoistPpow4 :: Term s (PInteger :--> PInteger :--> PInteger) -- distinctly more expensive
-- phoistPpow4 = phoistAcyclic ppow4


{-
ghci> eval $ ppowTest1 # 19 # 20
"(ExBudget {exBudgetCPU = ExCPU 28482372, exBudgetMemory = ExMemory 59288},[])"
ghci> length $ pt ppowTest1
836
-}
ppowTest1 :: Term s (PInteger :--> PInteger :--> PInteger)
ppowTest1 = plam $ \x y -> (ppow1 # x # y) + (ppow1 # y # x)

{-
ghci> eval $ ppowTest2 # 19 # 20
"(ExBudget {exBudgetCPU = ExCPU 28827372, exBudgetMemory = ExMemory 60788},[])"
ghci> length $ pt ppowTest2
563
-}
ppowTest2 :: Term s (PInteger :--> PInteger :--> PInteger)
ppowTest2 = plam $ \x y -> (phoistPpow1 # x # y) + (phoistPpow1 # y # x)

{-
ghci> eval $ ppowTest3 # 19 # 20
"(ExBudget {exBudgetCPU = ExCPU 28344372, exBudgetMemory = ExMemory 58688},[])"
ghci> length $ pt ppowTest3
653
-}
ppowTest3 :: Term s (PInteger :--> PInteger :--> PInteger)
ppowTest3 = plam $ \x y -> (ppow2 # x # y) + (ppow2 # y # x)

{-
ghci> eval $ ppowTest4 # 19 # 20
"(ExBudget {exBudgetCPU = ExCPU 28689372, exBudgetMemory = ExMemory 60188},[])"
ghci> length $ pt ppowTest4
577
-}
ppowTest4 :: Term s (PInteger :--> PInteger :--> PInteger)
ppowTest4 = plam $ \x y -> (phoistPpow2 # x # y) + (phoistPpow2 # y # x)

{-
ghci> eval $ ppowTest5 # 19 # 20
"(ExBudget {exBudgetCPU = ExCPU 34731855, exBudgetMemory = ExMemory 60943},[])"
ghci> length $ pt ppowTest5
541
-} 
-- > too expensive
-- ppowTest5 :: Term s (PInteger :--> PInteger :--> PInteger)
-- ppowTest5 = plam $ \x y -> (phoistPpow3 # x # y) + (phoistPpow3 # y # x)

{-
ghci> eval $ ppowTest6 # 19 # 20
"(ExBudget {exBudgetCPU = ExCPU 35904855, exBudgetMemory = ExMemory 66043},[])"
ghci> length $ pt ppowTest6
575
-}
-- > too expensive
-- ppowTest6 :: Term s (PInteger :--> PInteger :--> PInteger)
-- ppowTest6 = plam $ \x y -> (phoistPpow4 # x # y) + (phoistPpow4 # y # x)

{-
ghci> length $ pt $ ppowTestLarge1 # 12345 # 67890
1522
ghci> eval $  ppowTestLarge1 # 12345 # 67890
"(ExBudget {exBudgetCPU = ExCPU 3331290728, exBudgetMemory = ExMemory 658950},[])"
-}
ppowTestLarge1 :: Term s (PInteger :--> PInteger :--> PInteger)
ppowTestLarge1 = plam $ \x y -> ((ppow1 # x # y) + (ppow1 # y # x)) * ((ppow1 # x # y) - (ppow1 # y # x))

{-
ghci> length $ pt $ ppowTestLarge2 # 12345 # 67890
635
ghci> eval $  ppowTestLarge2 # 12345 # 67890
"(ExBudget {exBudgetCPU = ExCPU 3331911728, exBudgetMemory = ExMemory 661650},[])"
-}
ppowTestLarge2 :: Term s (PInteger :--> PInteger :--> PInteger)
ppowTestLarge2 = plam $ \x y -> ((phoistPpow1 # x # y) + (phoistPpow1 # y # x)) * ((phoistPpow1 # x # y) - (phoistPpow1 # y # x))

{-
ghci> length $ pt $ ppowTestLarge3 # 12345 # 67890
945
ghci> eval $  ppowTestLarge3 # 12345 # 67890
"(ExBudget {exBudgetCPU = ExCPU 3330738728, exBudgetMemory = ExMemory 656550},[])"
-}
ppowTestLarge3 :: Term s (PInteger :--> PInteger :--> PInteger)
ppowTestLarge3 = plam $ \x y -> ((ppow2 # x # y) + (ppow2 # y # x)) * ((ppow2 # x # y) - (ppow2 # y # x))

{-
ghci> length $ pt $ ppowTestLarge4 # 12345 # 67890
649
ghci> eval $  ppowTestLarge4 # 12345 # 67890
"(ExBudget {exBudgetCPU = ExCPU 3331359728, exBudgetMemory = ExMemory 659250},[])"
-}
ppowTestLarge4 :: Term s (PInteger :--> PInteger :--> PInteger)
ppowTestLarge4 = plam $ \x y -> ((phoistPpow2 # x # y) + (phoistPpow2 # y # x)) * ((phoistPpow2 # x # y) - (phoistPpow2 # y # x))

-- >
ppow = phoistPpow2