{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Euclid.Minting where

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
import qualified Plutarch.Api.V1.AssocMap as AssocMap
import qualified Plutarch.Monadic as P
import Plutarch.Num
import Plutarch.Maybe

import Euclid.Utils
import Euclid.Types

-- | for now, allow minting to the owner without further restrictions.
-- | this might enable certain types of spam, which we defer to being filtered
-- | in the frontend for now. Ultimately, the NFTs are to protect the owner.
-- |
-- | type PMintingPolicy = PData :--> Contexts.PScriptContext :--> POpaque
peuclidMinting :: ClosedTerm PMintingPolicy
peuclidMinting = phoistAcyclic $ plam $ \_ ctx -> P.do
    let info' = pfield @"txInfo" # ctx
    info <- pletFields @["mint", "signatories"] info'
    let owner = pto $ pfromData $ phead #$ info.signatories
        mints = pto $ pto $ pfromData info.mint
        tkns = pto $ pfromData $ psndBuiltin #$ phead #$ ptail # mints

    pif  -- TODO can we handle it better than this?
        (   ( (pfromData $ pfstBuiltin #$phead # mints) #== ( V1.padaSymbol) ) #&&
            ( pnull #$ ptail #$ ptail # mints ) )
        ( f # owner # tkns ) -- tkns are expected to be sorted
        ( ptraceError "dirac minting failure" )

    where 
        f :: Term s (PByteString :--> PBuiltinList (PBuiltinPair (PAsData V1.PTokenName) (PAsData PInteger)) :--> POpaque)
        f = pfix #$ plam $ \self owner tkns ->
            pif 
                ( pnull # tkns )
                ( popaque $ pcon PUnit )
                ( self 
                    # (psha2_256 # owner) 
                    #$ pfilter 
                        # ( plam $ \tkn -> pnot #$ (pto $ pfromData $ pfstBuiltin # tkn) #== owner )
                        # tkns )

-- TODO compare with old version (probably more efficient, but dysfunctional rn - update: in what way?)
        -- hash supposed owner until it matches first tkn, then pop, repeat with next one, until all passed
        -- f :: Term s (PByteString :--> PBuiltinList (PBuiltinPair (PAsData V1.PTokenName) (PAsData PInteger)) :--> POpaque)
        -- f = pfix #$ plam $ \self owner tkns ->
        --     pmatch tkns $ \case 
        --         PCons x xs ->
        --             plet (psha2_256 # owner) $ \owner' -> 
        --                 pif 
        --                     (owner #== (pto $ pfromData $ pfstBuiltin # x))
        --                     (self # owner # xs)
        --                     (self # owner' # (pcons # x # xs)) -- TODO this could be more efficient
        --         PNil -> popaque $ pcon PUnit
