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
-- import Plutarch.Rational
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
--              -> changed to equality because we're ensuring minAda now
-- TODO probably not the most efficient way to do this
pothersUnchanged :: Term s ( PAsset 
                        :--> PAsset 
                        :--> PInteger
                        :--> PInteger 
                        :--> V1.PValue 'Sorted 'NoGuarantees 
                        :--> PBool )
pothersUnchanged = plam $ \boughtAsset soldAsset addedBought addedSold addedAmnts ->
    V1.pcheckBinRel
        # plam (#==)
        # (pboughtSoldValue # boughtAsset # soldAsset # addedBought # addedSold)
        # addedAmnts

        -- NOTE: this seems to work as well (edited the comparison without testing though)
    -- AssocMap.pall # (AssocMap.pall # plam (0 #<=)) # pto (
    --     V1.punionWith # plam (-) # addedAmnts 
    --     #$ pboughtSoldValue # boughtAsset # soldAsset # addedBalances
    -- )

    -- ((pboughtSoldValue # boughtAsset # soldAsset # addedBalances) #== addedAmnts)

psubSwap :: Term s (PJumpsize :--> PJumpsize :--> PInteger :--> PInteger :--> PState :--> (PAsData PSubSwap) :--> PState)
psubSwap = phoistAcyclic $ plam $ \baseJsreBought baseJsreSold weightBought weightSold state swap' -> P.do 
    -- state <- pletFields @["balanceBought", "balanceSold", "ancJsreBought", "ancJsreSold"] state'
    PState oldLiqBought oldLiqSold oldAncJsreBought oldAncJsreSold <- pmatch state
    swap <- pletFields @["deltaBought", "deltaSold", "expBought", "expSold"] swap'

    (
        plet (oldAncJsreBought #* (pexp # baseJsreBought # swap.expBought)) $ \newAncJsreBought ->
        plet (oldAncJsreSold #* (pexp # baseJsreSold # swap.expSold)) $ \newAncJsreSold ->

            P.do 

            PJumpsize jsppeBought ancJseBought  <- pmatch newAncJsreBought
            PJumpsize ancJsppeSold jseSold      <- pmatch newAncJsreSold

            let deltaBought = pfromData $ pto swap.deltaBought
                deltaSold   = pfromData $ pto swap.deltaSold

            (
                plet (oldLiqBought #- deltaBought) $ \newLiqBought ->
                plet (oldLiqSold #+ deltaSold) $ \newLiqSold ->

                plet (deltaBought * ancJsppeSold * jsppeBought #<= deltaSold * ancJseBought * jseSold) $ \valueEquation ->
                plet (ancJseBought #<= newLiqBought * jsppeBought * weightBought) $ \priceFitBought ->
                plet (newLiqSold * jseSold * weightSold #<= ancJsppeSold) $ \priceFitSold ->

                -- pif (valueEquation)
                --     (pif (priceFitBought)
                --         (pif (priceFitSold)
                --             (pcon $ PState newLiqBought newLiqSold newAncJsreBought newAncJsreSold)
                --             (ptraceError "priceFitSold"))
                --         (ptraceError "priceFitBought"))
                --     (ptraceError "valueEquation")
                pif (valueEquation #&& priceFitBought #&& priceFitSold)
                    (pcon $ PState newLiqBought newLiqSold newAncJsreBought newAncJsreSold)
                    (ptraceError "subswap validation failure")

             )
     )

pswap :: Term s (PDirac :--> PSwap :--> PScriptContext :--> PBool)
pswap = plam $ \dirac' swap' ctx -> P.do 
    info <- pletFields @["inputs", "referenceInputs", "outputs", "mint"] 
            $ pfield @"txInfo" # ctx

    dirac <- pletFields @["owner", "threadNFT", "paramNFT", "anchorPrices"] dirac'
        
    -- let refTxO = pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # dirac.paramNFT) # info.referenceInputs 
    --     oldTxO' = pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # dirac.threadNFT) # info.inputs 
    --     newTxO' = pfromJust #$ pfind # (poutHasNFT # dirac.threadNFT) # info.outputs
    (
        plet (pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # dirac.paramNFT) # info.referenceInputs ) $ \refTxO ->
        plet (pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # dirac.threadNFT) # info.inputs ) $ \oldTxO' ->
        plet (pfromJust #$ pfind # (poutHasNFT # dirac.threadNFT) # info.outputs) $ \newTxO' ->

            P.do

            oldTxO <- pletFields @["address", "value"] oldTxO'
            newTxO <- pletFields @["address", "value", "datum"] newTxO'

            PDiracDatum newDirac' <- pmatch $ punpackEuclidDatum # newTxO.datum
            newDirac <- pletFields @["owner", "threadNFT", "paramNFT", "anchorPrices"] $ pfield @"dirac" # newDirac'

            PParamDatum param' <- pmatch $ punpackEuclidDatum #$ pfield @"datum" # refTxO

            param <- pletFields @["virtual", "weights", "jumpSizes", "active", "minAda"] $ pfield @"param" # param'
            swap <- pletFields @["boughtAsset", "soldAsset", "subSwaps"] swap'

            (
                plet (pvalueOfAsset # swap.boughtAsset) $ \pvalueOfBought ->
                plet (pvalueOfAsset # swap.soldAsset) $ \pvalueOfSold ->

                plet (pvalueOfBought # param.virtual) $ \virtualBought ->
                plet (pvalueOfSold # param.virtual) $ \virtualSold ->

                plet (pvalueOfAsset # swap.boughtAsset # oldTxO.value) $ \oldBalBought ->
                plet (pvalueOfAsset # swap.soldAsset   # oldTxO.value) $ \oldBalSold ->

                plet (pvalueOfAsset # swap.boughtAsset # newTxO.value) $ \newBalBought ->
                plet (pvalueOfAsset # swap.soldAsset   # newTxO.value) $ \newBalSold ->

                plet (pfromJumpsize #$ pvalueOfBought # param.jumpSizes) $ \baseJsreBought ->
                plet (pfromJumpsize #$ pvalueOfSold # param.jumpSizes) $ \baseJsreSold -> 

                plet ( pcon $ PState 
                    ( virtualBought #+ oldBalBought ) 
                    ( virtualSold   #+ oldBalSold )  
                    ( pcon $ PJumpsize 1 (pvalueOfBought # dirac.anchorPrices)  ) 
                    ( pcon $ PJumpsize (pvalueOfSold # dirac.anchorPrices) 1    )
                    ) $ \initialState ->

                plet (psubSwap 
                    # baseJsreBought 
                    # baseJsreSold 
                    # (pvalueOfBought # param.weights) 
                    # (pvalueOfSold # param.weights)
                    ) $ \pstep ->

                -- TODO is this the best way to fold that?
                plet (pfoldl # pstep # initialState # swap.subSwaps) $ \finalState ->

                    P.do

                    -- new <- pletFields @["liqBought", "balanceSold", "ancJsreBought", "ancJsreSold"] finalState
                    PState newLiqBought newLiqSold newAncJsreBought newAncJsreSold <- pmatch finalState

                    PJumpsize jsppeBought ancJseBought <- pmatch newAncJsreBought
                    PJumpsize ancJsppeSold jseSold <- pmatch newAncJsreSold

                    let newAnchorBought     = pdiv # ancJseBought # jsppeBought
                        newAnchorSold       = pdiv # ancJsppeSold # jseSold
                        newAnchorPrices     = pupdateAnchorPrices # swap.boughtAsset # swap.soldAsset # newAnchorBought # newAnchorSold # dirac.anchorPrices

                        newValueAda         = V1.plovelaceValueOf # newTxO.value
                        newActualLiqBought  = virtualBought #+ newBalBought
                        newActualLiqSold    = virtualSold   #+ newBalSold

                        -- TODO probably not the most efficient way to do this
                        addedAmnts          = V1.punionWith # plam (+) # newTxO.value #$ pmapAmounts # plam negate # oldTxO.value
                        addedBought         = newBalBought #- oldBalBought
                        addedSold           = newBalSold #- oldBalSold


                    -- (   ( pif ((pfromData param.active) #== 1)     (pconstant True) ( ptraceError "not active" )           ) #&&

                    --     ( pif (dirac.owner       #== newDirac.owner)  (pconstant True) ( ptraceError "owner" )         ) #&&
                    --     ( pif (dirac.threadNFT   #== newDirac.threadNFT) (pconstant True) ( ptraceError "threadNFT" )      ) #&&
                    --     ( pif (dirac.paramNFT    #== newDirac.paramNFT)  (pconstant True) ( ptraceError "paramNFT" )      ) #&&

                    --     ( pif (newAnchorPrices   #== newDirac.anchorPrices) (pconstant True) ( ptraceError "newAnchorPrices" )   ) #&&

                    --     ( pif (param.minAda      #<= newValueAda) (pconstant True) ( ptraceError "minAda" )             ) #&& 
                    --     ( pif (newLiqBought      #<= newActualLiqBought) (pconstant True) ( ptraceError "newLiqBought" )      ) #&&
                    --     ( pif (newLiqSold        #<= newActualLiqSold)  (pconstant True) ( ptraceError "newLiqSold" )       ) #&&

                    --     ( pif (pothersUnchanged  # swap.boughtAsset
                    --                         # swap.soldAsset 
                    --                         # addedBought
                    --                         # addedSold
                    --                         # addedAmnts) (pconstant True) ( ptraceError "pothersUnchanged" ))
                    --  )
                    (   ( (pfromData param.active) #== 1                ) #&&

                        ( dirac.owner       #== newDirac.owner          ) #&&
                        ( dirac.threadNFT   #== newDirac.threadNFT      ) #&&
                        ( dirac.paramNFT    #== newDirac.paramNFT       ) #&&

                        ( newAnchorPrices   #== newDirac.anchorPrices   ) #&&

                        ( param.minAda      #<= newValueAda             ) #&& 
                        ( newLiqBought      #<= newActualLiqBought      ) #&&
                        ( newLiqSold        #<= newActualLiqSold        ) #&&

                        ( pothersUnchanged  # swap.boughtAsset
                                            # swap.soldAsset 
                                            # addedBought
                                            # addedSold
                                            # addedAmnts )
                     )

             )


     )

-- pswap :: Term s (PDirac :--> PSwap :--> PScriptContext :--> PBool)
-- pswap = phoistAcyclic $ plam $ \dirac' swap' ctx -> P.do 
--     info <- pletFields @["inputs", "referenceInputs", "outputs", "mint"] 
--             $ pfield @"txInfo" # ctx

--     dirac <- pletFields @["owner", "threadNFT", "paramNFT", "anchorPrices"] dirac'
        
--     -- let refTxO = pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # dirac.paramNFT) # info.referenceInputs 
--     --     oldTxO' = pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # dirac.threadNFT) # info.inputs 
--     --     newTxO' = pfromJust #$ pfind # (poutHasNFT # dirac.threadNFT) # info.outputs
--     (
--         plet (pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # dirac.paramNFT) # info.referenceInputs ) $ \refTxO ->
--         plet (pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # dirac.threadNFT) # info.inputs ) $ \oldTxO' ->
--         plet (pfromJust #$ pfind # (poutHasNFT # dirac.threadNFT) # info.outputs) $ \newTxO' ->

--             P.do

--             oldTxO <- pletFields @["address", "value"] oldTxO'
--             newTxO <- pletFields @["address", "value", "datum"] newTxO'

--             PDiracDatum newDirac' <- pmatch $ punpackEuclidDatum # newTxO.datum
--             newDirac <- pletFields @["owner", "threadNFT", "paramNFT", "anchorPrices"] $ pfield @"dirac" # newDirac'

--             -- here: instead match against Param or Diode, and proceed accordingly

--             PParamDatum param' <- pmatch $ punpackEuclidDatum #$ pfield @"datum" # refTxO

--             param <- pletFields @["virtual", "weights", "jumpSizes", "active", "minAda"] $ pfield @"param" # param'
--             swap <- pletFields @["boughtAsset", "soldAsset", "boughtExp", "soldExp"] swap'
            
--             -- let oldValue        = oldTxO.value
--             --     newValue        = newTxO.value

--                 -- oldAnchorBought = pvalueOfBought # dirac.anchorPrices   -- NOTE: inverted/selling price
--                 -- oldAnchorSold   = pvalueOfSold # dirac.anchorPrices     -- NOTE: inverted/selling price

--             (
--                 plet (oldTxO.value) $ \oldValue ->
--                 plet (newTxO.value) $ \newValue ->

--                 plet (pvalueOfAsset # swap.boughtAsset) $ \pvalueOfBought ->
--                 plet (pvalueOfAsset # swap.soldAsset) $ \pvalueOfSold ->

--                 plet (pexp # (pfromJumpsize #$ pvalueOfBought # param.jumpSizes) # swap.boughtExp) $ \jsreBought ->
--                 plet (pexp # (pfromJumpsize #$ pvalueOfSold # param.jumpSizes) # swap.soldExp) $ \jsreSold -> 
                    
--                 plet (pjumpsize # jsreSold) $ \jseSold ->
--                 plet (pjumpsizePlusOne # jsreBought) $ \jsppeBought ->

--                 plet (V1.punionWith # plam (+) # newValue #$ pmapAmounts # plam negate # oldValue) $ \addedAmnts ->
--                 plet (pvalueOfAsset # swap.boughtAsset # addedAmnts) $ \addedBought ->
--                 plet (pvalueOfAsset # swap.soldAsset # addedAmnts) $ \addedSold ->

--                 plet ((pvalueOfBought # dirac.anchorPrices) #* (pjumpsize # jsreBought)) $ \ancJseBought ->
--                 plet ((pvalueOfSold # dirac.anchorPrices) #* (pjumpsizePlusOne # jsreSold)) $ \ancJsppeSold ->
                    
--                     P.do



--                     -- TODO vs. plets
--                     -- let pvalueOfBought  = pvalueOfAsset # swap.boughtAsset
--                     --     pvalueOfSold    = pvalueOfAsset # swap.soldAsset


--                     --     jsreBought      = pexp # (pfromJumpsize #$ pvalueOfBought # param.jumpSizes) # swap.boughtExp
--                     --     jsreSold        = pexp # (pfromJumpsize #$ pvalueOfSold # param.jumpSizes) # swap.soldExp

--                     -- let --jseBought       = pjumpsize # jsreBought
--                         -- jseSold         = pjumpsize # jsreSold

--                         -- jsppeBought     = pjumpsizePlusOne # jsreBought
--                         -- jsppeSold       = pjumpsizePlusOne # jsreSold

--                     let virtualBought   = pvalueOfBought # param.virtual
--                         virtualSold     = pvalueOfSold # param.virtual

--                         weightBought    = pvalueOfBought # param.weights
--                         weightSold      = pvalueOfSold # param.weights
                        
--                         -- addedAmnts      = V1.punionWith # plam (+) # newValue #$ pmapAmounts # plam negate # oldValue
--                         -- addedBought     = pvalueOfAsset # swap.boughtAsset # addedAmnts -- TODO could probably instead just use the newValues
--                         -- addedSold       = pvalueOfAsset # swap.soldAsset # addedAmnts

--                         newValueBought  = pvalueOfAsset # swap.boughtAsset # newValue
--                         newValueSold    = pvalueOfAsset # swap.soldAsset # newValue

--                         -- ancJseBought    = oldAnchorBought #* jseBought
--                         -- ancJsppeSold    = oldAnchorSold #* jsppeSold

--                         -- aka currently used spotprices, rounded down (we don't need those to be exact, otherwise this would be incorrect)
--                         newAnchorBought = pdiv # ancJseBought # jsppeBought
--                         newAnchorSold   = pdiv # ancJsppeSold # jseSold
--                         newAnchorPrices = pupdateAnchorPrices # swap.boughtAsset # swap.soldAsset # newAnchorBought # newAnchorSold # dirac.anchorPrices

--                         -- oldValueAda     = V1.plovelaceValueOf # oldValue
--                         newValueAda     = V1.plovelaceValueOf # newValue
                        
--                         -- checks
--                         correctSigns    = 0 #< addedSold -- checking that the sold asset is being deposited suffices
--                         valueEquation   = (-addedBought * ancJsppeSold * jsppeBought) #<= (addedSold * ancJseBought * jseSold)
--                         priceFitBought  = ancJseBought #<= (virtualBought + newValueBought) * jsppeBought * weightBought
--                         priceFitSold    = (virtualSold + newValueSold) * jseSold * weightSold #<= ancJsppeSold
--                         lockedAdaKept   = (param.minAda #<= newValueAda) -- (oldValueAda #== newValueAda) #|| (param.minAda #<= newValueAda) -- TODO FIXME

--                         -- correctSigns    = pif (0 #< addedSold) (pconstant True) (ptraceError "sold <= 0") -- checking that the sold asset is being deposited suffices
--                         -- valueEquation   = pif ((-addedBought * ancJsppeSold * jsppeBought) #<= (addedSold * ancJseBought * jseSold)) (pconstant True) (ptraceError "value equation")
--                         -- priceFitBought  = pif (ancJseBought #<= (virtualBought + newValueBought) * jsppeBought * weightBought) (pconstant True) (ptraceError "price fit bought")
--                         -- priceFitSold    = pif ((virtualSold + newValueSold) * jseSold * weightSold #<= ancJsppeSold) (pconstant True) (ptraceError "price fit sold")
--                         -- lockedAdaKept   = pif ((V1.plovelaceValueOf # addedAmnts) #< 0) 
--                         --                         (pif (param.minAda #<= (V1.plovelaceValueOf # newValue)) (pconstant True) (ptraceError "minAda"))
--                         --                         (pconstant True)

--                     (   ( (pfromData param.active) #== 1                          ) #&&

--                         ( dirac.owner         #== newDirac.owner                  ) #&&
--                         ( dirac.threadNFT     #== newDirac.threadNFT              ) #&&
--                         ( dirac.paramNFT      #== newDirac.paramNFT               ) #&&
--                         ( newAnchorPrices     #== newDirac.anchorPrices           ) #&&

--                         ( correctSigns      ) #&&
--                         ( priceFitBought    ) #&&
--                         ( priceFitSold      ) #&&
--                         ( valueEquation     ) #&& 
--                         ( lockedAdaKept     ) #&& 

--                         ( pothersUnchanged    # swap.boughtAsset 
--                                                     # swap.soldAsset 
--                                                     # addedBought
--                                                     # addedSold
--                                                     # addedAmnts )
--                         )

--                     -- (   ( pif ( (pfromData param.active) #== 1                          ) (pconstant True) (ptraceError "active")) #&&

--                     --     ( pif ( dirac.owner         #== newDirac.owner                  ) (pconstant True) (ptraceError "owner")) #&&
--                     --     ( pif ( dirac.threadNFT     #== newDirac.threadNFT              ) (pconstant True) (ptraceError "threadNFT")) #&&
--                     --     ( pif ( dirac.paramNFT      #== newDirac.paramNFT               ) (pconstant True) (ptraceError "paramNFT")) #&&
--                     --     ( pif ( newAnchorPrices     #== newDirac.anchorPrices           ) (pconstant True) (ptraceError "newAnchorPrices")) #&&

--                     --     ( correctSigns      ) #&&
--                     --     ( priceFitBought    ) #&&
--                     --     ( priceFitSold      ) #&&
--                     --     ( valueEquation     ) #&& 
--                     --     ( lockedAdaKept     ) #&& 

--                     --     ( pif ( pothersUnchanged    # swap.boughtAsset 
--                     --                                 # swap.soldAsset 
--                     --                                 # addedBought
--                     --                                 # addedSold
--                     --                                 # addedAmnts )  (pconstant True) (ptraceError "others unchanged")) 
--                     --     )
--                     )
--                 ) 

    

padmin :: Term s ((PAsData V1.PPubKeyHash) :--> PScriptContext :--> PBool)
padmin = plam $ \owner ctx -> P.do
    let signer = phead #$ pfromData $ pfield @"signatories" #$ pfield @"txInfo" # ctx
    (signer #== owner)

peuclidValidator :: ClosedTerm PValidator
peuclidValidator = plam $ \dat' red' ctx -> P.do 
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
            ) 
    pif 
        pass 
        ( popaque $ pcon PUnit )
        ( ptraceError "dirac validation failure" )