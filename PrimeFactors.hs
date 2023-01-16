{-# LANGUAGE RoleAnnotations #-}

module Dex.PrimeFactors where 

{-
Represent numbers as map from prime factors to their exponents.
This makes multiplication, division, exponentiation, drawing nth roots, and representing fractionals far simpler.
The only expensive operation - addition - can be computed offchain and need only be verified onchain.
Note that the empty map represents one, not zero.
Note also that only positive numbers are representable for now.
-}

import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)
import qualified Plutarch.Api.V1.AssocMap as AssocMap
import Plutarch.Positive 
import Plutarch.Num 
import qualified PlutusLedgerApi.V1 as Plutus
import Plutarch.Lift
import Plutarch.TryFrom
import qualified PlutusTx.Monoid as PlutusTx
import qualified PlutusTx.Semigroup as PlutusTx
import Plutarch.Unsafe

-- TODO assert prime status maybe somewhere
newtype PPrime (s :: S) = PPrime (Term s PPositive)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PEq, PPartialOrd, POrd, PNum, PShow)
instance DerivePlutusType PPrime where type DPTStrat _ = PlutusTypeNewtype

data ExponentGuarantees = Any | NonZero -- | Positive -- keeping positive here, might be useful later

-- ripping most of this from PPrimeFactors'
type role PPrimeFactors nominal nominal nominal
newtype PPrimeFactors (keys :: KeyGuarantees) (exponents :: ExponentGuarantees) (s :: S)
  = PPrimeFactors (Term s (AssocMap.PMap keys PPrime PInteger))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PShow)
instance DerivePlutusType (PPrimeFactors keys exponents) where type DPTStrat _ = PlutusTypeNewtype

instance PEq (PPrimeFactors 'Sorted norm) where
    a #== b = pto a #== pto b

instance Semigroup (Term s (PPrimeFactors 'Sorted 'NonZero)) where
    a <> b = pnormalize #$ punionWith # plam (+) # a # b

instance PlutusTx.Semigroup (Term s (PPrimeFactors 'Sorted 'NonZero)) where
    a <> b = pnormalize #$ punionWith # plam (+) # a # b

instance Semigroup (Term s (PPrimeFactors 'Sorted 'Any)) where
    a <> b = punionWith # plam (+) # a # b

instance PlutusTx.Semigroup (Term s (PPrimeFactors 'Sorted 'Any)) where
    a <> b = punionWith # plam (+) # a # b

instance
    Semigroup (Term s (PPrimeFactors 'Sorted norm)) =>
    Monoid (Term s (PPrimeFactors 'Sorted norm))
    where
        mempty = pcon (PPrimeFactors AssocMap.pempty)

instance
    PlutusTx.Semigroup (Term s (PPrimeFactors 'Sorted norm)) =>
    PlutusTx.Monoid (Term s (PPrimeFactors 'Sorted norm))
    where
        mempty = pcon (PPrimeFactors AssocMap.pempty)

instance
    PlutusTx.Semigroup (Term s (PPrimeFactors 'Sorted 'Any)) =>
    PlutusTx.Group (Term s (PPrimeFactors 'Sorted 'Any))
    where
        inv a = pmapExponents # plam negate # a

instance
    PlutusTx.Semigroup (Term s (PPrimeFactors 'Sorted 'NonZero)) =>
    PlutusTx.Group (Term s (PPrimeFactors 'Sorted 'NonZero))
    where
        inv a = punsafeCoerce $ PlutusTx.inv (punsafeCoerce a :: Term s (PPrimeFactors 'Sorted 'Any))


pmult :: Term s (PPrimeFactors 'Sorted norm0 :--> PPrimeFactors 'Sorted norm1 :--> PPrimeFactors 'Sorted 'Any)
pmult = phoistAcyclic $ plam $ \x y -> 
    (punsafeCoerce x) <> (punsafeCoerce y)


pdiv :: Term s (PPrimeFactors 'Sorted norm0 :--> PPrimeFactors 'Sorted norm1 :--> PPrimeFactors 'Sorted 'Any)
pdiv = phoistAcyclic $ plam $ \numerator denominator -> 
    (punsafeCoerce numerator)
    <>
    (PlutusTx.inv $ punsafeCoerce denominator)

ppow :: Term s (PInteger :--> PPrimeFactors 'Sorted norm :--> PPrimeFactors 'Sorted 'Any)
ppow = phoistAcyclic $ plam $ \exp -> 
    pmapExponents # (plam $ (*) exp)

-- passertAdd :: Term s (PPrimeFactors 'Sorted norm0 :--> PPrimeFactors 'Sorted norm1 :--> PPrimeFactors 'Sorted 'NonZero :--> )
-- passertAdd = 

zeroData :: ClosedTerm (PAsData PInteger)
zeroData = pdata 0

punionWith :: Term s ((PInteger :--> PInteger :--> PInteger) 
                :--> PPrimeFactors 'Sorted norm0 :--> PPrimeFactors 'Sorted norm1 :--> PPrimeFactors 'Sorted 'Any)
punionWith = phoistAcyclic $ plam $ \f x y -> 
    pcon . PPrimeFactors $ 
        AssocMap.punionWith # f # (pto x) # (pto y)

pnormalize :: Term s (PPrimeFactors 'Sorted norm :--> PPrimeFactors 'Sorted 'NonZero)
pnormalize = phoistAcyclic $
  plam $ \pf ->
    pcon . PPrimeFactors $
        AssocMap.pmapMaybeData # plam nonZero # pto pf -- TODO vs. pmapMaybe?
  where
    nonZero intData =
        pif (intData #== zeroData) (pcon PNothing) (pcon $ PJust intData)

pmapExponents :: Term s ((PInteger :--> PInteger) :--> PPrimeFactors 'Sorted norm :--> PPrimeFactors 'Sorted 'Any)
pmapExponents = phoistAcyclic $ plam $ \f pf -> 
    pcon . PPrimeFactors $ 
        AssocMap.pmap # f # pto pf




pfoldr :: PIsListLike list a => Term s ((a :--> b :--> b) :--> b :--> list a :--> b)
pfoldr = phoistAcyclic $
  plam $ \f z ->
    precList
      (\self x xs -> f # x # (self # xs))
      (const z)

ptoRational :: Term s (PPrimeFactors sort norm :--> PRational)
ptoRational = phoistAcyclic $
    plam $ \f map ->
        precList
            ( \self x xs -> f # x # (self # xs)


                # (ppairDataBuiltin # (pfstBuiltin # x) # (f #$ psndBuiltin # x))
                # (self # xs)
            )
            (const $ PPair 0 0)
            # pto map

{-
NOTE at some point we have actual integer amounts in the ledger, how does this change things here?
    - one thought: verify factorization onchain
        - consider storing actual value in datum as prime factors as well
            -> would only need to 
                - verify the new prime factor amount equals the new ledger amount
                - would this obsolete addition if we only need it for computing new balances? Do we? (as it seems we don't)
    - ENTRYPOINT think about this again

NOTE the important bits to optimize are 
    - swapping costs
    - not dying from huge exponentiations (both memory and cpu)


verifying addition:

    a + b ?= c
=>  a/c + b/c ?= 1
=>  num(a/c) + num(b/c) ?= den(a/c) + den(b/c)

if factor is in num(a/c), it can't be in den(a/c).
    if it's not in den(a/c), we can extract it from den(a/c) + den(b/c).
        => can't do common factor elimination in num(a/c) + num(b/c) ?= den(a/c) + den(b/c)
?> 

we only need to prove it if it's true - does this make it easier?

are there common factors in num(a/c) + num(b/c)?

can we memoize powered primes?

can we somehow use matrices/tensors? I.e. primes x exponents x summands or something along those lines

TODO later version: consider optional caching in utxos - i.e. powers of primes. Either reference or compute yourself
-}