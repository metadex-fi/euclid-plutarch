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
    plet (js + 1) $ \jspp ->
        pif (0 #<= e)
            ( pdiv # (anchor * (pexp_ # jspp # e)) # (pexp_ # js # e) )
            (
                plet (pnegate # e) $ \en -> 
                    pdiv # (anchor * (pexp_ # js # en)) # (pexp_ # jspp # en)
            )

-- TODO probably not the most efficient way to do this
pupdateAnchorPrices :: Term s (PAsset :--> PAsset :--> PBoughtSold :--> V1.PValue 'Sorted 'Positive :--> V1.PValue 'Sorted 'Positive)
pupdateAnchorPrices = plam $ \boughtAsset soldAsset newAnchors oldAnchors -> P.do
    bought <- pletFields @["currencySymbol", "tokenName"] boughtAsset
    sold <- pletFields @["currencySymbol", "tokenName"] soldAsset
    new <- pletFields @["bought", "sold"] newAnchors
    let newBought = V1.psingleton # bought.currencySymbol # bought.tokenName # new.bought
        newSold = V1.psingleton # sold.currencySymbol # sold.tokenName # new.sold
        replace = V1.punionWith # (plam (\x _ -> x))

    V1.passertPositive #$ replace # newSold #$ replace # newBought # oldAnchors

pCorrectSigns :: Term s (PBoughtSold :--> PBool)
pCorrectSigns = plam $ \addedBalances -> -- 0 #< (pfromData $ pfield @"sold" # addedBalances)
    pif (0 #< (pfromData $ pfield @"sold" # addedBalances)) (pconstant True) (ptraceError "sold <= 0")
    -- checking that the sold asset is being deposited suffices


-- TODO consider rounding-error based trickery (also in other places)
-- NOTE prices are inverted/selling, so buying decreases amm-price and vice versa
-- previously pboughtAssetForSale
pPricesFitAmm :: Term s (PBoughtSold :--> PBoughtSold :--> PBool)
pPricesFitAmm = plam $ \swapPrices ammPrices -> P.do 
    swpp <- pletFields @["bought", "sold"] swapPrices
    ammp <- pletFields @["bought", "sold"] ammPrices
    (   ( pif ( (pfromData swpp.bought) #<= (pfromData ammp.bought) ) (pconstant True) (
            ptraceError $ " I\n\n" <> 
            (pshow $ (pfromData swpp.bought)) <> "\n\n" <>
            (pshow $ (pfromData ammp.bought)) <> "\n\n" <>
            (pshow $ (pfromData swpp.bought) #- (pfromData ammp.bought))
        )) #&&
        ( pif ( (pfromData ammp.sold  ) #<= (pfromData swpp.sold  ) ) (pconstant True) (
            ptraceError $ " J\n\n" <> 
            (pshow $ (pfromData swpp.sold)) <> "\n\n" <>
            (pshow $ (pfromData ammp.sold)) <> "\n\n" <>
            (pshow $ (pfromData swpp.sold) #- (pfromData ammp.sold))
        ))   )
    -- (   ( (pfromData swpp.bought) #<= (pfromData ammp.bought) ) #&&
    --     ( (pfromData ammp.sold  ) #<= (pfromData swpp.sold  ) )   )

 -- TODO explicit fees?
pvalueEquation :: Term s (PBoughtSold :--> PBoughtSold :--> PBool)
pvalueEquation = plam $ \swapPrices addedBalances -> P.do
    added <- pletFields @["bought", "sold"] addedBalances
    swpp <- pletFields @["bought", "sold"] swapPrices
    -- let boughtA0 = (pnegate #$ pfromData added.bought) * (pfromData swpp.sold)
    --     soldA0 = (pfromData added.sold) * (pfromData swpp.bought)
    -- (pif (pconstant True) (ptraceError $  "added.bought:" <> (pshow added.bought) <> 
    --                 "\nadded.sold:" <> (pshow added.sold) <> 
    --                 "\nswpp.bought:" <> (pshow swpp.bought) <> 
    --                 "\nswpp.sold:" <> (pshow swpp.sold) <> 
    --                 "\nboughtA0:" <> (pshow boughtA0) <> 
    --                 "\nsoldA0:" <> (pshow soldA0) <>
    --                 "\npasses:" <> (pshow (boughtA0 #<= soldA0))
    --                 ) (pconstant True))
    -- (pif (boughtA0 #<= soldA0) (pconstant True) (ptraceError $ (pshow boughtA0) <> " - " <> (pshow soldA0) <> " = " <> (pshow $ boughtA0 #- soldA0)))
    (   ( (pnegate #$ pfromData added.bought) * (pfromData swpp.sold) ) #<=
        ( (pfromData added.sold) * (pfromData swpp.bought) )   )
    -- TODO reconsider #<= vs #< (using #<= now for better fit with offchain)

-- TODO could do this more efficiently, maybe
-- NOTE/TODO hacking ambiguous equality measure manually here
-- NOTE/TODO checking inequality, as sometimes ADA-requirement increases. Check that this does not create exploits
pothersUnchanged :: Term s ( PAsset 
                        :--> PAsset 
                        :--> PBoughtSold 
                        :--> V1.PValue 'Sorted 'NoGuarantees 
                        :--> PBool )
pothersUnchanged = plam $ \boughtAsset soldAsset addedBalances addedValue ->
    V1.pcheckBinRel
        # plam (#<=)
        # (pboughtSoldValue # boughtAsset # soldAsset # addedBalances)
        # addedValue

        -- NOTE: this seems to work as well (edited the comparison without testing though)
    -- AssocMap.pall # (AssocMap.pall # plam (0 #<=)) # pto (
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

    PDiracDatum newDirac' <- pmatch $ punpackEuclidDatum # newTxO.datum
    newDirac <- pletFields @["owner", "threadNFT", "paramNFT", "anchorPrices"] $ pfield @"dirac" # newDirac'

    -- here: instead match against Param or Diode, and proceed accordingly

    PParamDatum param' <- pmatch $ punpackEuclidDatum #$ pfield @"datum" # refTxO

    param <- pletFields @["virtual", "weights", "jumpSizes", "active"] $ pfield @"param" # param'
    swap <- pletFields @["boughtAsset", "soldAsset", "prices"] swap'

    let pof             = pboughtSoldOf # swap.boughtAsset # swap.soldAsset -- TODO vs. plets
        pof'            = pboughtSoldOf # swap.boughtAsset # swap.soldAsset
        
        virtual         = pof #$ V1.pforgetPositive param.virtual
        weights         = pof #$ V1.pforgetPositive param.weights
        jumpSizes       = pof #$ V1.pforgetPositive param.jumpSizes
        
        anchorPrices    = pof #$ V1.pforgetPositive dirac.anchorPrices

        oldValue        = oldTxO.value
        newValue        = newTxO.value

        addedValue      = V1.punionWith # plam (+) # newValue #$ pmapAmounts # plam negate # oldValue
        addedBalances   = pboughtSoldOf # swap.boughtAsset # swap.soldAsset # addedValue

        -- oldLiquidity    = virtual #+ (pof' # oldValue)
        newLiquidity    = virtual #+ (pof' # newValue)

        -- oldAmmPrices    = oldLiquidity #* weights -- NOTE: inverted/selling prices
        newAmmPrices    = newLiquidity #* weights -- NOTE: inverted/selling prices

        realSwapPrices  = pcalcSwapPrices # anchorPrices # jumpSizes # swap.prices
        -- passetForSale   = pboughtAssetForSale # realSwapPrices

        newAnchorPrices = pupdateAnchorPrices # swap.boughtAsset # swap.soldAsset # realSwapPrices # dirac.anchorPrices

        -- newAnchorPrices = V1.passertPositive #$ 
        --     V1.punionWith
        --         # (plam $ \_ y -> y)
        --         # dirac.anchorPrices
        --         #$ pboughtSoldValue # swap.boughtAsset # swap.soldAsset # realSwapPrices

    -- (   ( (pfromData param.active) #== 1                                ) #&&

    --     ( dirac.owner       #== newDirac.owner                          ) #&&
    --     ( dirac.threadNFT   #== newDirac.threadNFT                      ) #&&
    --     ( dirac.paramNFT    #== newDirac.paramNFT                       ) #&&
    --     ( newAnchorPrices   #== newDirac.anchorPrices                   ) #&&

    --     ( passetForSale     # oldAmmPrices                              ) #&&
    --     ( passetForSale     # newAmmPrices                              ) #&&
    --     ( pvalueEquation    # realSwapPrices # addedBalances            ) #&& 
    --     ( pothersUnchanged  # swap.boughtAsset 
    --                         # swap.soldAsset 
    --                         # addedBalances
    --                         # addedValue )  
    --     )

    (   ( pif ( (pfromData param.active) #== 1                                ) (pconstant True) (ptraceError "A")) #&&

        ( pif ( dirac.owner         #== newDirac.owner                  ) (pconstant True) (ptraceError "B")) #&&
        ( pif ( dirac.threadNFT     #== newDirac.threadNFT              ) (pconstant True) (ptraceError "C")) #&&
        ( pif ( dirac.paramNFT      #== newDirac.paramNFT               ) (pconstant True) (ptraceError "D")) #&&
        ( pif ( newAnchorPrices     #== newDirac.anchorPrices           ) (pconstant True) (ptraceError "E")) #&&
        ( pif ( pCorrectSigns       # addedBalances                     ) (pconstant True) (ptraceError "F")) #&&
        ( pif ( pPricesFitAmm       # realSwapPrices # newAmmPrices     ) (pconstant True) (ptraceError "G")) #&&
        ( pif ( pvalueEquation      # realSwapPrices # addedBalances    ) (pconstant True) (ptraceError "H")) #&& 
        ( pif ( pothersUnchanged    # swap.boughtAsset 
                                    # swap.soldAsset 
                                    # addedBalances
                                    # addedValue )  (pconstant True) (ptraceError "F")) 
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