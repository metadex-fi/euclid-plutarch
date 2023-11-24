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

-- TODO probably not the most efficient way to do this
pupdateAnchorPrices :: Term s (PAsset :--> PAsset :--> PInteger  :--> PInteger :--> V1.PValue 'Sorted 'Positive :--> V1.PValue 'Sorted 'Positive)
pupdateAnchorPrices = plam $ \boughtAsset soldAsset newAncBought newAncSold oldAnchors -> P.do
    bought <- pletFields @["currencySymbol", "tokenName"] boughtAsset
    sold <- pletFields @["currencySymbol", "tokenName"] soldAsset
    let newBought = V1.psingleton # bought.currencySymbol # bought.tokenName # newAncBought
        newSold = V1.psingleton # sold.currencySymbol # sold.tokenName # newAncSold
        replace = V1.punionWith # (plam (\x _ -> x))

    V1.passertPositive #$ replace # newSold #$ replace # newBought # oldAnchors

-- TODO could do this more efficiently, maybe
-- NOTE/TODO hacking ambiguous equality measure manually here
-- NOTE/TODO checking inequality, as sometimes ADA-requirement increases. Check that this does not create exploits
pothersUnchanged :: Term s ( PAsset 
                        :--> PAsset 
                        :--> PInteger
                        :--> PInteger 
                        :--> V1.PValue 'Sorted 'NoGuarantees 
                        :--> PBool )
pothersUnchanged = plam $ \boughtAsset soldAsset addedBought addedSold addedAmnts ->
    V1.pcheckBinRel
        # plam (#<=)
        # (pboughtSoldValue # boughtAsset # soldAsset # addedBought # addedSold)
        # addedAmnts

        -- NOTE: this seems to work as well (edited the comparison without testing though)
    -- AssocMap.pall # (AssocMap.pall # plam (0 #<=)) # pto (
    --     V1.punionWith # plam (-) # addedAmnts 
    --     #$ pboughtSoldValue # boughtAsset # soldAsset # addedBalances
    -- )

    -- ((pboughtSoldValue # boughtAsset # soldAsset # addedBalances) #== addedAmnts)

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
    swap <- pletFields @["boughtAsset", "soldAsset", "boughtExp", "soldExp"] swap'

    -- TODO vs. plets
    let pvalueOfBought  = pvalueOfAsset # swap.boughtAsset
        pvalueOfSold    = pvalueOfAsset # swap.soldAsset

        jsBought        = pvalueOfBought # param.jumpSizes
        jsSold          = pvalueOfSold # param.jumpSizes

        jsppBought      = jsBought #+ 1
        jsppSold        = jsSold #+ 1

        jseBought       = pexp # jsBought # swap.boughtExp
        jseSold         = pexp # jsSold # swap.soldExp

        jsppeBought     = pexp # jsppBought # swap.boughtExp
        jsppeSold       = pexp # jsppSold # swap.soldExp

        virtualBought   = pvalueOfBought # param.virtual
        virtualSold     = pvalueOfSold # param.virtual

        weightBought    = pvalueOfBought # param.weights
        weightSold      = pvalueOfSold # param.weights
        
        oldValue        = oldTxO.value
        newValue        = newTxO.value

        addedAmnts      = V1.punionWith # plam (+) # newValue #$ pmapAmounts # plam negate # oldValue
        addedBought     = pvalueOfAsset # swap.boughtAsset # addedAmnts
        addedSold       = pvalueOfAsset # swap.soldAsset # addedAmnts

        newAmmBought    = (virtualBought #+ (pvalueOfBought # newValue)) #* weightBought    -- NOTE: inverted/selling price
        newAmmSold      = (virtualSold #+ (pvalueOfSold # newValue)) #* weightSold          -- NOTE: inverted/selling price

        oldAnchorBought = pvalueOfBought # dirac.anchorPrices   -- NOTE: inverted/selling price
        oldAnchorSold   = pvalueOfSold # dirac.anchorPrices     -- NOTE: inverted/selling price

        ancJsppeBought  = oldAnchorBought #* jsppeBought
        ancJsppeSold    = oldAnchorSold #* jsppeSold

        -- aka currently used spotprices, rounded down (we don't need those to be exact, otherwise this would be incorrect)
        newAnchorBought = pdiv # ancJsppeBought # jseBought
        newAnchorSold   = pdiv # ancJsppeSold   # jseSold
        newAnchorPrices = pupdateAnchorPrices # swap.boughtAsset # swap.soldAsset # newAnchorBought # newAnchorSold # dirac.anchorPrices

        -- checks
        correctSigns    = pif (0 #< addedSold) (pconstant True) (ptraceError "sold <= 0") -- checking that the sold asset is being deposited suffices
        valueEquation   = pif ((-addedBought * ancJsppeSold * jseBought) #<= (addedSold * ancJsppeBought * jseSold)) (pconstant True) (ptraceError "value equation")
        priceFitBought  = pif (ancJsppeBought #<= (newAmmBought #* jseBought)) (pconstant True) (ptraceError "price fit bought")
        priceFitSold    = pif ((newAmmSold #* jseSold) #<= ancJsppeSold) (pconstant True) (ptraceError "price fit sold")

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

    (   ( pif ( (pfromData param.active) #== 1                          ) (pconstant True) (ptraceError "active")) #&&

        ( pif ( dirac.owner         #== newDirac.owner                  ) (pconstant True) (ptraceError "owner")) #&&
        ( pif ( dirac.threadNFT     #== newDirac.threadNFT              ) (pconstant True) (ptraceError "threadNFT")) #&&
        ( pif ( dirac.paramNFT      #== newDirac.paramNFT               ) (pconstant True) (ptraceError "paramNFT")) #&&
        ( pif ( newAnchorPrices     #== newDirac.anchorPrices           ) (pconstant True) (ptraceError "newAnchorPrices")) #&&

        ( correctSigns      ) #&&
        ( priceFitBought    ) #&&
        ( priceFitSold      ) #&&
        ( valueEquation     ) #&& 

        ( pif ( pothersUnchanged    # swap.boughtAsset 
                                    # swap.soldAsset 
                                    # addedBought
                                    # addedSold
                                    # addedAmnts )  (pconstant True) (ptraceError "others unchanged")) 
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