
module Dex.Set where

import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)
import Plutarch.Positive
import qualified Plutarch.Monadic as P
import Plutarch.Lift

-- a PBuiltinList that should always be sorted and deduplicated
-- newtype PSet (a :: PType) (s :: S) = PSet (Term s (PBuiltinList a))
--   deriving stock (Generic)
--   deriving anyclass (PlutusType, PShow)--, PIsData)--,  PEq, PPartialOrd, POrd)
-- instance DerivePlutusType (PSet a) where type DPTStrat _ = PlutusTypeNewtype

-- instance PListLike PSet where
--   type PElemConstraint PSet a = PLift a

--not used rn
-- psafeSelfFoldr :: 
--     ( PIsListLike list a
--     , Monoid (PLifted a)
--     , PUnsafeLiftDecl a -- TODO check if those types don't break things
--     ) => Term s ((a :--> a :--> a) :--> list a :--> a)
-- psafeSelfFoldr = phoistAcyclic $ plam $ \f l -> 
--     pif (pnull # l)
--         (pconstant mempty)
--         (pselfFoldr # f # l)


-- TODO find a more elegant way to represent this information than just a check function
-- TODO check out how AssocMap is doing it 
passertSet :: 
    ( PIsListLike list (PAsData a)
    , PPartialOrd a
    , PIsData a
    ) =>
    Term s (list (PAsData a) :--> list (PAsData a))
passertSet = phoistAcyclic $ plam $ \l ->
    pif (pnull # l) 
        l
        $ P.do
            let head = pfromData $ phead # l
                _ = pfoldr # pcheckTwoElems # head #$ ptail # l -- TODO check if this works
            l
    where
        pcheckTwoElems :: (PPartialOrd a, PIsData a) => Term s ((PAsData a) :--> a :--> a)
        pcheckTwoElems = plam $ \snd' fst -> 
            plet (pfromData snd') $ \snd ->
                pif (snd #<= fst)
                    perror 
                    snd

-- pSetFromList :: 
--     ( PListLike list
--     , PElemConstraint list a
--     ) =>
--     Term s (list a :--> PSet a)
-- pSetFromList = phoistAcyclic $ plam $ \l ->
--     pdedupli

-- taken and adjusted from haskell implementation
-- psort :: 
--     ( POrd a
--     , PListLike list
--     , PElemConstraint list a
--     ) => 
--     Term s (list a :--> list a)
-- psort = phoistAcyclic $ plam $ \l -> (mergeAll . sequences) l
--   where
--     sequences (a:b:xs)
--       | a `cmp` b == GT = descending b [a]  xs
--       | otherwise       = ascending  b (a:) xs
--     sequences xs = [xs]

--     descending a as (b:bs)
--       | a `cmp` b == GT = descending b (a:as) bs
--     descending a as bs  = (a:as): sequences bs

--     ascending a as (b:bs)
--       | a `cmp` b /= GT = ascending b (\ys -> as (a:ys)) bs
--     ascending a as bs   = let !x = as [a]
--                           in x : sequences bs

--     mergeAll [x] = x
--     mergeAll xs  = mergeAll (mergePairs xs)

--     mergePairs (a:b:xs) = let !x = merge a b
--                           in x : mergePairs xs
--     mergePairs xs       = xs

--     merge as@(a:as') bs@(b:bs')
--       | a `cmp` b == GT = b:merge as  bs'
--       | otherwise       = a:merge as' bs
--     merge [] bs         = bs
--     merge as []         = as