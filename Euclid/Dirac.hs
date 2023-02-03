{-# LANGUAGE AllowAmbiguousTypes #-} -- TODO added blindly, verify later
{-# LANGUAGE ScopedTypeVariables #-} -- TODO does this do anything?
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE OverloadedRecordDot #-}
-- {-# LANGUAGE ExistentialQuantification #-}


module Euclid.Dirac where

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

ppickedPricesFitDirac :: Term s (PBoughtSold :--> PBoughtSold :--> PBoughtSold :--> PBoughtSold :--> PBool)
ppickedPricesFitDirac = plam $ \prices lowestPrices highestPrices jumpSizes ->
    ( prices #<= highestPrices ) #&&
    ( prem # (prices #- lowestPrices) # jumpSizes #== zeroBS) -- #- implicitly checks lowestPrices #<= prices

pboughtAssetAvailable :: Term s (PBoughtSold :--> PBoughtSold :--> PBoughtSold :--> PBool)
pboughtAssetAvailable = plam $ \prices weights oldBalances -> P.do 
    p <- pletFields @["bought", "sold"] prices
    w <- pletFields @["bought", "sold"] weights
    b <- pletFields @["bought", "sold"] oldBalances
    (   ( (pfromData p.sold)   * (pfromData w.sold)   * (pfromData b.bought) ) #<= 
        ( (pfromData p.bought) * (pfromData w.bought) * (pfromData b.sold)   )   )

pnewAmmPricesInRange :: Term s (PBoughtSold :--> PBoughtSold :--> PBoughtSold :--> PBoughtSold :--> PBool)
pnewAmmPricesInRange = plam $ \prices weights newBalances jumpSizes -> P.do 
    p <- pletFields @["bought", "sold"] prices
    w <- pletFields @["bought", "sold"] weights
    b <- pletFields @["bought", "sold"] newBalances
    j <- pletFields @["bought", "sold"] jumpSizes
    let newBoughtAmmPrice   = (pfromData b.bought) * (pfromData w.sold)
        newSoldAmmPrice     = (pfromData b.sold)   * (pfromData w.bought)
    (   ( newBoughtAmmPrice #< ((pfromData p.bought) + (pfromData j.bought)) ) #&&
        ( ((pfromData p.sold) - (pfromData j.sold)) #< newSoldAmmPrice       )   )


pswap :: Term s (PDirac :--> PSwap :--> PScriptContext :--> PBool)
pswap = phoistAcyclic $ plam $ \dirac' swap' ctx -> P.do 
    info <- pletFields @["inputs", "referenceInputs", "outputs", "mint"] 
            $ pfield @"txInfo" # ctx

    dirac <- pletFields @["owner", "threadNFT", "paramNFT", "lowestPrices"] dirac'
        
    let oldTxO' = pfromJust #$ pfind # (poutHasNFT # dirac.threadNFT) # info.outputs
        newTxO' = pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # dirac.threadNFT) # info.inputs 
        refTxO = pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # dirac.paramNFT) # info.referenceInputs 

    oldTxO <- pletFields @["address", "value"] oldTxO'
    newTxO <- pletFields @["address", "value", "datum"] newTxO'

    PDiracDatum newDirac <- pmatch $ punpackEuclidDatum # newTxO.datum
    PParamDatum param' <- pmatch $ punpackEuclidDatum #$ pfield @"datum" # refTxO
    param <- pletFields @["jumpSizes", "highestPrices", "weights"] $ pfield @"param" # param'
    swap <- pletFields @["boughtAsset", "soldAsset", "prices"] swap'

    let pof             = pboughtSoldOf # swap.boughtAsset # swap.soldAsset -- TODO vs. plets
        
        oldBalances     = pof # oldTxO.value
        newBalances     = pof # newTxO.value
        weights         = pof # param.weights
        jumpSizes       = pof # param.jumpSizes
        highestPrices   = pof # param.highestPrices
        lowestPrices    = pof # dirac.lowestPrices

    (   ( dirac' #== (pfield @"dirac" # newDirac)                                           ) #&&
        ( ppickedPricesFitDirac # swap.prices # lowestPrices # highestPrices # jumpSizes    ) #&&
        ( pboughtAssetAvailable # swap.prices # weights # oldBalances                       ) #&&
        ( oldBalances #* swap.prices #<= newBalances #* swap.prices                         ) #&& -- TODO explicit fees?
        ( pnewAmmPricesInRange # swap.prices # weights # newBalances # jumpSizes            )   )

padmin :: Term s ((PAsData V1.PPubKeyHash) :--> PScriptContext :--> PBool)
padmin = plam $ \owner ctx -> P.do
    let signer = phead #$ pfromData $ pfield @"signatories" #$ pfield @"txInfo" # ctx
    (signer #== owner)

peuclidValidator :: ClosedTerm PValidator
peuclidValidator = phoistAcyclic $ plam $ \dat' red' ctx -> P.do 
    let dat = (flip (ptryFrom @PEuclidDatum) fst) dat'
        pass = (pmatch dat $ \case 
            PParamDatum param -> 
                padmin 
                # (pfield @"owner" #$ pfield @"param" # param)
                # ctx

            PDiracDatum dirac' -> P.do
                let red = (flip (ptryFrom @PEuclidAction) fst) red'
                let dirac = pfield @"dirac" #$ dirac'
                pmatch red $ \case 
                    PAdminRedeemer _ ->
                        padmin 
                        # (pfield @"owner" # dirac)
                        # ctx
                    PSwapRedeemer swap -> pswap # dirac # (pfield @"swap" # swap) # ctx
                    _ -> ( ptraceError "unknown redeemer" )
            ) 
    pif 
        pass 
        ( popaque $ pcon PUnit )
        ( ptraceError "dirac validation failure" )

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
        tkns = pto $ pfromData $ psndBuiltin #$ phead # mints

    pif 
        ( pnull #$ ptail # mints )
        ( f # owner # tkns ) -- tkns are expected to be sorted
        ( ptraceError "dirac minting failure" )

    where 
        -- hash supposed owner until it matches first tkn, then pop, repeat with next one, until all passed
        f :: Term s (PByteString :--> PBuiltinList (PBuiltinPair (PAsData V1.PTokenName) (PAsData PInteger)) :--> POpaque)
        f = pfix #$ plam $ \self owner tkns ->
            pmatch tkns $ \case 
                PCons x xs -> 
                    plet (psha2_256 # owner) $ \owner' ->
                        pif 
                            (owner #== (pto $ pfromData $ pfstBuiltin # x))
                            (self # owner' # xs)
                            (self # owner' # (pcons # x # xs)) -- TODO this could be more efficient
                PNil -> popaque $ pcon PUnit
