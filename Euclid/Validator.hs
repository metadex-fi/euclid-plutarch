{-# LANGUAGE AllowAmbiguousTypes #-} -- TODO added blindly, verify later
{-# LANGUAGE ScopedTypeVariables #-} -- TODO does this do anything?
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE OverloadedRecordDot #-}
-- {-# LANGUAGE ExistentialQuantification #-}


module Euclid.Validator where

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
    ( pdivides # jumpSizes #$ prices #- lowestPrices ) -- #- implicitly checks lowestPrices #<= prices

pboughtAssetAvailable :: Term s (PBoughtSold :--> PBoughtSold :--> PBool)
pboughtAssetAvailable = plam $ \prices oldAmmPrices -> P.do 
    swpp <- pletFields @["bought", "sold"] prices
    ammp <- pletFields @["bought", "sold"] oldAmmPrices
    (   ( (pfromData swpp.sold)   * (pfromData ammp.bought) ) #<= 
        ( (pfromData swpp.bought) * (pfromData ammp.sold)   )   )

pnewAmmPricesInRange :: Term s (PBoughtSold :--> PBoughtSold :--> PBoughtSold :--> PBool)
pnewAmmPricesInRange = plam $ \prices newAmmPrices jumpSizes -> P.do 
    swpp <- pletFields @["bought", "sold"] prices
    ammp <- pletFields @["bought", "sold"] newAmmPrices
    jmps <- pletFields @["bought", "sold"] jumpSizes
    (   ( (pfromData ammp.bought) #< ((pfromData swpp.bought) + (pfromData jmps.bought)) ) #&&
        ( ((pfromData swpp.sold) - (pfromData jmps.sold)) #< (pfromData ammp.sold)       )   )

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
        oldAmmPrices    = oldBalances #* weights
        newAmmPrices    = newBalances #* weights

    (   ( dirac' #== (pfield @"dirac" # newDirac)                                           ) #&&
        ( ppickedPricesFitDirac # swap.prices # lowestPrices # highestPrices # jumpSizes    ) #&&
        ( pboughtAssetAvailable # swap.prices # oldAmmPrices                                ) #&&
        ( oldBalances #* swap.prices #<= newBalances #* swap.prices                         ) #&& -- TODO explicit fees?
        ( pnewAmmPricesInRange # swap.prices # newAmmPrices # jumpSizes                     )   )

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