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

ppricesFitDirac :: Term s (PBoughtSold :--> PBoughtSold :--> PBoughtSold :--> PBool)
ppricesFitDirac = plam $ \swapPrices lowestPrices jumpSizes ->
    pdivides # jumpSizes #$ swapPrices #- lowestPrices -- #- implicitly checks lowestPrices #<= swapPrices

pboughtAssetForSale :: Term s (PBoughtSold :--> PBoughtSold :--> PBool)
pboughtAssetForSale = phoistAcyclic $ plam $ \swapPrices ammPrices -> P.do 
    swpp <- pletFields @["bought", "sold"] swapPrices
    ammp <- pletFields @["bought", "sold"] ammPrices
    (   ( (pfromData swpp.sold) * (pfromData ammp.bought) ) #<= -- results from ammp <= swpp, with *p := *p.bought / *p.sold
        ( (pfromData ammp.sold) * (pfromData swpp.bought) )   ) -- ==> ammp.bought / ammp.sold <= swpp.bought / swpp.sold

-- TODO maybe this could be combined somehow with ppricesFitDirac later
ppricesBoxed :: Term s (PBoughtSold :--> PBoughtSold :--> PBoughtSold :--> PBool)
ppricesBoxed = plam $ \swapPrices ammPrices jumpSizes ->
    ( ammPrices #< swapPrices ) #&& 
    ( swapPrices #<= ( ammPrices #+ jumpSizes ) )

 -- TODO explicit fees?
pvalueEquation :: Term s (PBoughtSold :--> PBoughtSold :--> PBoughtSold :--> PBool)
pvalueEquation = plam $ \swapPrices oldLiquidity newLiquidity -> P.do
    let oldA0' = swapPrices * oldLiquidity
        newA0' = swapPrices * newLiquidity
    oldA0 <- pletFields @["bought", "sold"] oldA0'
    newA0 <- pletFields @["bought", "sold"] newA0'
    (   ( (pfromData oldA0.bought) + (pfromData oldA0.sold) ) #< -- NOTE inequality here, TODO reconsider
        ( (pfromData newA0.bought) + (pfromData newA0.sold) )   )

-- TODO could do this more efficiently, maybe
pothersUnchanged :: Term s ( PAsset 
                        :--> PAsset 
                        :--> PBoughtSold 
                        :--> PBoughtSold 
                        :--> V1.PValue 'Sorted 'Positive 
                        :--> V1.PValue 'Sorted 'Positive 
                        :--> PBool )
pothersUnchanged = plam $ \boughtAsset soldAsset oldBalances newBalances oldValue newValue ->
    plet (pboughtSoldValue # boughtAsset # soldAsset) $ \toValue ->
        ( V1.punionWith # plam (-) # oldValue #$ toValue # oldBalances ) #==
        ( V1.punionWith # plam (-) # newValue #$ toValue # newBalances )


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
    param <- pletFields @["virtual", "weights", "jumpSizes"] $ pfield @"param" # param'
    swap <- pletFields @["boughtAsset", "soldAsset", "prices"] swap'

    let pof             = pboughtSoldOf # swap.boughtAsset # swap.soldAsset -- TODO vs. plets
        passetForSale   = pboughtAssetForSale # swap.prices
        
        virtual         = pof # param.virtual
        weights         = pof # param.weights
        jumpSizes       = pof # param.jumpSizes
        
        lowestPrices    = pof # dirac.lowestPrices

        oldBalances     = pof # oldTxO.value
        newBalances     = pof # newTxO.value

        oldLiquidity    = virtual #+ oldBalances
        newLiquidity    = virtual #+ newBalances

        oldAmmPrices    = oldLiquidity #* weights
        newAmmPrices    = newLiquidity #* weights

    (   ( dirac' #== (pfield @"dirac" # newDirac)                       ) #&&
        ( ppricesFitDirac   # swap.prices # lowestPrices # jumpSizes    ) #&&
        ( passetForSale     # oldAmmPrices                              ) #&&
        ( passetForSale     # newAmmPrices                              ) #&&
        ( ppricesBoxed      # swap.prices # oldAmmPrices # jumpSizes    ) #&&
        ( pvalueEquation    # swap.prices # oldLiquidity # newLiquidity ) #&&
        ( pothersUnchanged  # swap.boughtAsset 
                            # swap.soldAsset 
                            # oldBalances
                            # newBalances
                            # oldTxO.value 
                            # newTxO.value )  )

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