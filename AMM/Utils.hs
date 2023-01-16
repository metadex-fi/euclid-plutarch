
module Dex.Utils where 

import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)
import Plutarch.Positive
import qualified Plutarch.Monadic as P
import qualified Plutarch.Api.V1.Value as V1

import Dex.Types

-- -- TODO consider later implementing this more directly for probably marginal efficiency gains
-- pfindUnique :: PIsListLike list a => Term s ((a :--> PBool) :--> list a :--> a)
-- pfindUnique = phoistAcyclic $ plam $ \predicate list -> 
--     plet (pfilter # predicate # list) $ \results ->
--         pif (pnull #$ ptail # results)
--         (phead # results)
--         perror 

-- -- TODO could be made slightly more efficient (factor 2)
-- pfindN :: PIsListLike list a => Term s ((a :--> PBool) :--> PPositive :--> list a :--> list a)
-- pfindN = phoistAcyclic $ plam $ \predicate expectedLength list ->
--     plet (pfilter # predicate # list) $ \filtered -> 
--         pif ((ptryPositive #$ plength # filtered) #== expectedLength)
--             filtered 
--             perror

poutHasNFT :: Term s (PThreadNFT :--> PTxOut :--> PBool)
poutHasNFT = phoistAcyclic $ plam $ \nft' output -> P.do
    nft <- pletFields @["currencySymbol", "tokenName"] (pto $ pto nft')
    let value = pfield @"value" # output
        amount = V1.pvalueOf # value # nft.currencySymbol # nft.tokenName
    (amount #== 1)

pinHasNFT :: Term s (PThreadNFT :--> PTxInInfo :--> PBool)
pinHasNFT = phoistAcyclic $ plam $ \nft input -> 
    poutHasNFT # nft # (pfield @"resolved" # input)

-- pselfFoldr :: PIsListLike list a => Term s ((a :--> a :--> a) :--> list a :--> a)
-- pselfFoldr = phoistAcyclic $ plam $ \f l -> pfoldr # f # (phead # l) #$ ptail # l

pfor ::