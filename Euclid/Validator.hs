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
pothersUnchanged = plam $ \boughtAsset soldAsset addedBought addedSold addedValue ->
    V1.pcheckBinRel
        # plam (#<=)
        # (pboughtSoldValue_ # boughtAsset # soldAsset # addedBought # addedSold)
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

    param <- pletFields @["virtual", "weights", "jumpSize", "active"] $ pfield @"param" # param'
    swap <- pletFields @["boughtAsset", "soldAsset", "exponent"] swap'


    let pof             = pboughtSoldOf # swap.boughtAsset # swap.soldAsset -- TODO vs. plets
        pof'            = pboughtSoldOf # swap.boughtAsset # swap.soldAsset
        exp             = pfromData swap.exponent
        
        virtual         = pof #$ V1.pforgetPositive param.virtual
        weights         = pof #$ V1.pforgetPositive param.weights
        
        oldValue        = oldTxO.value
        newValue        = newTxO.value

        addedValue      = V1.punionWith # plam (+) # newValue #$ pmapAmounts # plam negate # oldValue
        addedBought     = pvalueOfAsset # addedValue # swap.boughtAsset
        addedSold       = pvalueOfAsset # addedValue # swap.soldAsset
        correctSigns    = pif (0 #< addedSold) (pconstant True) (ptraceError "sold <= 0") -- checking that the sold asset is being deposited suffices

        -- oldLiquidity    = virtual #+ (pof' # oldValue)
        newLiquidity    = virtual #+ (pof' # newValue)
        newAmmPrices    = newLiquidity #* weights -- NOTE: inverted/selling prices

    ammPrices <- pletFields @["bought", "sold"] newAmmPrices
    anchorPrices <- pletFields @["bought", "sold"] $ pof #$ V1.pforgetPositive dirac.anchorPrices

    let jumpSize        = pfromData param.jumpSize
        jumpSizePP      = jumpSize + 1
        jse             = pif (0 #<= exp) (pexp_ # jumpSize # exp) (pexp_ # jumpSizePP # (-exp))
        jsppe           = pif (0 #<= exp) (pexp_ # jumpSizePP # exp) (pexp_ # jumpSize # (-exp))

        ammBought       = pfromData ammPrices.bought
        ammSold         = pfromData ammPrices.sold
        anchorBought    = pfromData anchorPrices.bought
        anchorSold      = pfromData anchorPrices.sold

        ancBoughtJsppe  = anchorBought * jsppe
        ancSoldJsppe    = anchorSold * jsppe
        priceFitBought  = ancBoughtJsppe    #<= (ammBought * jse)
        priceFitSold    = (ammSold * jse)   #<= ancSoldJsppe
        
        valueEquation   = -addedBought * ancSoldJsppe #<= addedSold * anchorBought * jse

        -- aka currently used spotprices, rounded down (we don't need those to be exact, otherwise this would be incorrect)
        newAncBought    = pdiv # ancBoughtJsppe # jse
        newAncSold      = pdiv # ancSoldJsppe   # jse
        newAnchorPrices = pupdateAnchorPrices # swap.boughtAsset # swap.soldAsset # newAncBought # newAncSold # dirac.anchorPrices

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

    (   ( pif ( (pfromData param.active) #== 1                          ) (pconstant True) (ptraceError "A")) #&&

        ( pif ( dirac.owner         #== newDirac.owner                  ) (pconstant True) (ptraceError "B")) #&&
        ( pif ( dirac.threadNFT     #== newDirac.threadNFT              ) (pconstant True) (ptraceError "C")) #&&
        ( pif ( dirac.paramNFT      #== newDirac.paramNFT               ) (pconstant True) (ptraceError "D")) #&&
        ( pif ( newAnchorPrices     #== newDirac.anchorPrices           ) (pconstant True) (ptraceError "E")) #&&

        ( correctSigns                                            ) #&&
        ( pif priceFitBought    (pconstant True) (ptraceError "F")) #&&
        ( pif priceFitSold      (pconstant True) (ptraceError "G")) #&&
        ( pif valueEquation     (pconstant True) (ptraceError "H")) #&& 

        ( pif ( pothersUnchanged    # swap.boughtAsset 
                                    # swap.soldAsset 
                                    # addedBought
                                    # addedSold
                                    # addedValue )  (pconstant True) (ptraceError "I")) 
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