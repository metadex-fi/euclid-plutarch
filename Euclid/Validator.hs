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
import PlutusTx.Monoid qualified as PlutusTx
import PlutusTx.Semigroup qualified as PlutusTx

import Euclid.Utils
import Euclid.Types

pcalcSwapPrices :: Term s (PBoughtSold :--> PBoughtSold :--> PBoughtSold :--> PBoughtSold)
pcalcSwapPrices = plam $ \anchorPrices jumpSizes exponents -> P.do 
    anchors <- pletFields @["bought", "sold"] anchorPrices
    jss <- pletFields @["bought", "sold"] jumpSizes
    es <- pletFields @["bought", "sold"] exponents
    let bought = pcalcSwapPrices_ # (pfromData anchors.bought) # (pfromData jss.bought) # (pfromData es.bought)
        sold   = pcalcSwapPrices_ # (pfromData anchors.sold  ) # (pfromData jss.sold  ) # (pfromData es.sold  )
    ( pmkBoughtSold # bought # sold )

pcalcSwapPrices_ :: Term s (PInteger :--> PInteger :--> PInteger :--> PInteger)
pcalcSwapPrices_ = phoistAcyclic $ plam $ \anchor js e -> 
    pdiv # (anchor * (pexp_ # (js + 1) # e)) # (pexp_ # js # e)

-- TODO consider rounding-error based trickery (also in other places)
-- NOTE prices are inverted/selling, so buying decreases amm-price and vice versa
pboughtAssetForSale :: Term s (PBoughtSold :--> PBoughtSold :--> PBool)
pboughtAssetForSale = phoistAcyclic $ plam $ \swapPrices ammPrices -> P.do 
    swpp <- pletFields @["bought", "sold"] swapPrices
    ammp <- pletFields @["bought", "sold"] ammPrices
    (   ( (pfromData swpp.bought) #<= (pfromData ammp.bought) ) #&&
        ( (pfromData ammp.sold  ) #<= (pfromData swpp.sold  ) )   )

 -- TODO explicit fees?
pvalueEquation :: Term s (PBoughtSold :--> PBoughtSold :--> PBool)
pvalueEquation = plam $ \swapPrices addedBalances -> P.do
    added <- pletFields @["bought", "sold"] addedBalances
    swpp <- pletFields @["bought", "sold"] swapPrices
    (   ( (pnegate #$ pfromData added.bought) * (pfromData swpp.sold) ) #<=
        ( (pfromData added.sold) * (pfromData swpp.bought) )   )
    -- TODO reconsider #<= vs #< (using #<= now for better fit with offchain)

-- TODO could do this more efficiently, maybe
-- NOTE/TODO hacking ambiguous equality measure manually here
pothersUnchanged :: Term s ( PAsset 
                        :--> PAsset 
                        :--> PBoughtSold 
                        :--> V1.PValue 'Sorted 'NoGuarantees 
                        :--> PBool )
pothersUnchanged = plam $ \boughtAsset soldAsset addedBalances addedValue ->
    V1.pcheckBinRel
        # plam (#==)
        # addedValue
        #$ pboughtSoldValue # boughtAsset # soldAsset # addedBalances

        -- NOTE: this seems to work as well
    -- AssocMap.pall # (AssocMap.pall # plam (#== 0)) # pto (
    --     V1.punionWith # plam (-) # addedValue 
    --     #$ pboughtSoldValue # boughtAsset # soldAsset # addedBalances
    -- )

    -- ((pboughtSoldValue # boughtAsset # soldAsset # addedBalances) #== addedValue)

pswap :: Term s (PDirac :--> PSwap :--> PScriptContext :--> PBool)
pswap = phoistAcyclic $ plam $ \dirac' swap' ctx -> P.do 
    info <- pletFields @["inputs", "referenceInputs", "outputs", "mint"] 
            $ pfield @"txInfo" # ctx

    dirac <- pletFields @["owner", "threadNFT", "paramNFT", "anchorPrices"] dirac'
        
    let refTxO = pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # dirac.paramNFT) # info.referenceInputs 
        oldTxO' = pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # dirac.threadNFT) # info.inputs 
        newTxO' = pfromJust #$ pfind # (poutHasNFT # dirac.threadNFT) # info.outputs

    oldTxO <- pletFields @["address", "value"] oldTxO'
    newTxO <- pletFields @["address", "value", "datum"] newTxO'

    PDiracDatum newDirac <- pmatch $ punpackEuclidDatum # newTxO.datum


    -- here: instead match against Param or Diode, and proceed accordingly


    PParamDatum param' <- pmatch $ punpackEuclidDatum #$ pfield @"datum" # refTxO

    param <- pletFields @["virtual", "weights", "jumpSizes", "active"] $ pfield @"param" # param'
    swap <- pletFields @["boughtAsset", "soldAsset", "prices"] swap'

    let pof             = pboughtSoldOf # swap.boughtAsset # swap.soldAsset -- TODO vs. plets
        pof_            = pboughtSoldOf # swap.boughtAsset # swap.soldAsset
        
        virtual         = pof #$ V1.pforgetPositive param.virtual
        weights         = pof #$ V1.pforgetPositive param.weights
        jumpSizes       = pof #$ V1.pforgetPositive param.jumpSizes
        
        anchorPrices    = pof #$ V1.pforgetPositive dirac.anchorPrices

        oldValue        = oldTxO.value
        newValue        = newTxO.value

        -- addedValue      = V1.punionWith newValue <> (PlutusTx.inv oldValue)
        addedValue      = V1.punionWith # plam (+) # newValue #$ pmapAmounts # plam negate # oldValue
        addedBalances   = pboughtSoldOf # swap.boughtAsset # swap.soldAsset # addedValue

        oldLiquidity    = virtual #+ (pof_ # oldValue)
        newLiquidity    = virtual #+ (pof_ # newValue)

        oldAmmPrices    = oldLiquidity #* weights -- NOTE: inverted/selling prices
        newAmmPrices    = newLiquidity #* weights -- NOTE: inverted/selling prices

        realSwapPrices  = pcalcSwapPrices # anchorPrices # jumpSizes # swap.prices
        passetForSale   = pboughtAssetForSale # realSwapPrices

    (   ( (pfromData param.active) #== 1                                ) #&&
        ( dirac' #== (pfield @"dirac" # newDirac)                       ) #&&
        ( passetForSale     # oldAmmPrices                              ) #&&
        ( passetForSale     # newAmmPrices                              ) #&&
        ( pvalueEquation    # realSwapPrices # addedBalances            ) #&& 
        ( pothersUnchanged  # swap.boughtAsset 
                            # swap.soldAsset 
                            # addedBalances
                            # addedValue )  
        )

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
                    -- _ -> ( ptraceError "unknown redeemer" )
            ) 
    pif 
        pass 
        ( popaque $ pcon PUnit )
        ( ptraceError "dirac validation failure" )