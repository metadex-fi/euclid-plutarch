{-# LANGUAGE AllowAmbiguousTypes #-} -- TODO added blindly, verify later
{-# LANGUAGE ScopedTypeVariables #-} -- TODO does this do anything?
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
import Euclid.Value

popenDirac :: Term s PBool
popenDirac = pconstant True

pcloseDirac :: Term s PBool
pcloseDirac = pconstant True

pfstBuiltinData :: PIsData a => Term s (PBuiltinPair (PAsData a) b :--> a)
pfstBuiltinData = phoistAcyclic $ plam $ \pair -> pfromData $ pfstBuiltin # pair

psndBuiltinData :: PIsData b => Term s (PBuiltinPair a (PAsData b) :--> b)
psndBuiltinData = phoistAcyclic $ plam $ \pair -> pfromData $ psndBuiltin # pair

-- | sum the equivalent amounts of the tokens in first asset
pSumEquivalentA0' :: Term s (PPrices :--> V1.PCurrencySymbol :--> (AssocMap.PMap keys V1.PTokenName PInteger) :--> PInteger)
pSumEquivalentA0' = plam $ \prices ccy tknAmnts -> 
    pfoldr
        # (plam $ \pair acc -> (ppriceOf # prices # ccy #$ pfstBuiltinData # pair) * (psndBuiltinData # pair) + acc)
        # 0 
        # (pto tknAmnts)

-- | sum the equivalent amounts of the assets in first asset
psumEquivalentA0 :: Term s (PPrices :--> (V1.PValue a b) :--> PInteger)
psumEquivalentA0 = phoistAcyclic $ plam $ \prices val ->
    pfoldr 
        # (plam $ \pair acc -> (pSumEquivalentA0' # prices # (pfstBuiltinData # pair) #$ psndBuiltinData # pair) + acc) 
        # 0 
        # (pto $ pto val) -- get the list of pairs of CurrencySymbols and Maps from TokenNames to Amounts


pflipDirac :: Term s    
                (       V1.PValue 'Sorted 'Positive 
                :-->    V1.PValue 'Sorted 'Positive
                :-->    PAmounts
                :-->    PAmounts
                :-->    PPrices
                :-->    PBool
                )
pflipDirac = plam $ \oldVal newVal oldAmnt newAmnt prices -> P.do
    let valDiff = pvalSub # newVal # oldVal -- TODO vs. plets
        amntDiff = pvalSub # (pto newAmnt) # (pto oldAmnt)
        diffA0equiv = psumEquivalentA0 # prices # valDiff

    (valDiff #== amntDiff) #&& (0 #<= diffA0equiv) -- TODO add fees here

{-
core thought:
- we can divide the full tensor by initial-price-tensors of one less dimension
- either we are in a fully filled sub-tensor (1)
- or we are in one that's split up by some kind of diagonal thing (2)
- intuition: (1) is the case always except when all current prices are above initial prices
- the diagonal in (2) can be deduced by ???

alternative approach:
- just calculate which asset would be the "smartest" to have active here
- i.e. by
    - stepping through each non-first asset; for each
        - compare current price to initial price
            - if higher: consider it valid
            - if not: invalid
    - if no result: return first asset
    - if exactly one result: return that
    - if more than one result: 
        - pick one of them as new "first asset"
        - calculate prices of the others in that first one
        - recurse

design considerations:
- subtraction is useful, but does not check asset-alignment
- lookups each time seems costly
--> maybe first check alignment once via i.e. checkBinRel with a check that both are nonzero

implementation:
- (somewhere check asset alignmment once) <- TODO
- for one recursion:
    - punionWith a custom subtraction which zeroes negative values
    - pnormalize (TODO later those two could be combined into one step for constant gains)
    - check if zero, one or many results
    - branch accordingly
-}
pdefaultActiveAsset :: Term s (PPrices :--> PPrices :--> PAsset)
pdefaultActiveAsset = phoistAcyclic $ plam $ \initPs currentPs ->
     pfromData $ 
        f # (V1.pforgetPositive $ pto initPs) # (V1.pforgetPositive $ pto currentPs)

    where 
        f :: Term s (V1.PValue 'Sorted V1.NonZero :--> V1.PValue 'Sorted V1.NonZero :--> PAsData PAsset)
        f = pfix #$ plam f'

        f' :: Term s (V1.PValue 'Sorted V1.NonZero :--> V1.PValue 'Sorted V1.NonZero :--> PAsData PAsset)
            -> Term s (V1.PValue 'Sorted V1.NonZero)
            -> Term s (V1.PValue 'Sorted V1.NonZero)
            -> Term s (PAsData PAsset)
        f' self initPs currentPs =
            plet (pposSub # initPs # currentPs) $ \diff -> -- check which prices are larger than init
                pif 
                    (pnullVal # diff)
                    (pfirstAsset # initPs) -- if none: return denominator-asset
                    (pif 
                        (punaryVal # diff)
                        (pfirstAsset # diff) -- if one: return that
                        {- 
                            if more than one - recurse by:
                                - removing first asset from both prices
                                - "normalize" results to have same new-first-asset-price 
                                    by multiplying with other's new first asset price
                                - recurse 
                        -}
                        (P.do
                            let initPsTail = ptailVal # initPs -- TODO vs. plets
                                currentPsTail = ptailVal # currentPs
                                initPsNorm = punsafeValScale # initPsTail #$ pfirstAmnt # currentPsTail
                                currentPsNorm = punsafeValScale # currentPsTail #$ pfirstAmnt # initPsTail
                            self # initPsNorm # currentPsNorm
                        )
                    )

        -- | subtract & remove negative amounts (Integers)
        pposSub' :: Term s (PInteger :--> PInteger :--> PInteger)
        pposSub' = phoistAcyclic $ plam $ \x y -> 
            pif (x #< y)
                (y - x)
                0

        -- | subtract & remove negative amounts (Values)
        pposSub :: Term s (V1.PValue 'Sorted 'V1.NonZero :--> V1.PValue 'Sorted V1.NonZero :--> V1.PValue 'Sorted V1.NonZero)
        pposSub = phoistAcyclic $ plam $ \x y -> 
            V1.pnormalize #$
                V1.punionWith
                    # pposSub'
                    # x
                    # y

-- those arguments feel safer than just handing over the records. Also less ugly.
pjumpDirac :: forall s. Term s ( PParam 
                            :--> PPrices 
                            :--> PPrices 
                            :--> PPrices 
                            :--> PAmounts 
                            :--> PAmounts 
                            :--> V1.PValue 'V1.Sorted 'V1.Positive 
                            :--> V1.PValue 'V1.Sorted 'V1.Positive 
                            :--> PActiveAssets 
                            :--> PActiveAssets 
                            :--> PBool )
pjumpDirac = plam $ \   refDat 
                        initPrices
                        oldPrices 
                        newPrices 
                        oldAmnts 
                        newAmnts 
                        oldVal 
                        newVal 
                        oldStorage 
                        newStorage -> P.do 
    ref <- pletFields @[ "jumpSizes"
                        , "lowerPriceBounds"
                        , "upperPriceBounds"
                        , "baseAmountA0"
                        -- , "minJumpFlipA0"
                        ] refDat

    -- three stages: pre-Jump ("old") --> post-Jump-pre-Flip ("mid") --> post-Flip ("new")
    let oldActiveAsset = pfromData $ pfirstAsset #$ V1.pforgetPositive $ pto oldAmnts
        midActiveAsset = getMidActiveAsset # initPrices # newPrices # oldStorage
        midAmnts = calcMidAmnts # midActiveAsset # newPrices # ref.baseAmountA0

    -- check 
    --  that jump size is correct & no assets added or removed to the price list
    (   ( jumpSizeCorrect # oldPrices # newPrices # ref.jumpSizes ) #&&
    --  that the jump lands within the ranges
        ( withinRanges # newPrices # ref.lowerPriceBounds # ref.upperPriceBounds ) #&&
    --  that there is only one active asset pre-jump (TODO later: option to pre-jump flip if not so)
        ( oneActiveAssetPreJump # oldAmnts ) #&&
    --      if it's different than default: that it's added to the storage correctly
    --  if jump-target is in storage:
    --      if so:
    --          that active asset is loaded correctly from there --> getMidActiveAsset
    --          that it's deleted correctly 
        (storageChecks # oldStorage # newStorage # oldActiveAsset # initPrices # oldPrices # newPrices ) #&&
    --  that pre-flip active amounts are generated correctly from active asset, prices, default amount
    --  --> not a check but computation
    --  that minimum amount is flipped TODO later
        -- (minAmntFlipped ) #&&
    --  flip check
        ( pflipDirac # oldVal # newVal # midAmnts # newAmnts # newPrices ) 
        )

    -- assert things that are stored tagged as sorted are actually sorted:
    --      prices in newPrices = passertPricesSortedPositive # newDat.prices
    --      amnts in newAmnts = passertAmntsSortedPositive # newDat.activeAmnts
    --      jumpStorage implicitly in storageChecks
    
    where 
        -- | check that all non-zero diffs in prices are a multiple of the resp. jump size
        jumpSizeCorrect :: Term s (PPrices :--> PPrices :--> PJumpSizes :--> PBool)
        jumpSizeCorrect = plam $ \oldPrices newPrices jumpSizes -> 
            V1.pcheckBinRel  -- if there is addition or removal of a price: div by zero (error desired)
                # (plam $ \js pd -> (pmod # pd # js) #== 0) -- TODO try prem for performance later
                # (pto jumpSizes) 
                #$ V1.punionWith # (plam (-)) # (pto newPrices) # (pto oldPrices) -- sign is irrelevant here

        withinRanges :: Term s (PPrices :--> PPrices :--> PPrices :--> PBool)
        withinRanges = plam $ \newPrices lowerBounds upperBounds -> 
            -- lower bounds noninclusive to allow not storing zeroes, yet still getting a nonzero price check
            ((pto lowerBounds) #< (pto newPrices)) #&& ((pto newPrices) #< (pto upperBounds))


        oneActiveAssetPreJump :: Term s (PAmounts :--> PBool)
        oneActiveAssetPreJump = plam $ \amnts -> punaryVal #$ V1.pforgetPositive $ pto amnts

        -- checks that loaded asset is deleted, and old active asset is stored, unless it's the default
        -- TODO consider making the Maps work with AsData's here instead
        storageChecks :: Term s (PActiveAssets :--> PActiveAssets :--> PAsset :--> PPrices :--> PPrices :--> PPrices :--> PBool)
        storageChecks = plam $ \oldStorage newStorage oldActiveAsset initPrices oldPrices newPrices -> 
            (pto $ newStorage) #==
                ( AssocMap.pdelete # newPrices #$ -- TODO double-check later that deletion works correctly if key is not in Map
                     (pif 
                        ( oldActiveAsset #== (pdefaultActiveAsset # initPrices # oldPrices) )
                        ( pto $ oldStorage )
                        ( AssocMap.pinsert # oldPrices # oldActiveAsset #$ pto $ oldStorage )
                    )
                )

        -- | simply divide first asset's base amount by price of active asset & pack up
        calcMidAmnts :: Term s (PAsset :--> PPrices :--> PAmount :--> PAmounts)
        calcMidAmnts = plam $ \activeAsset' prices baseAmountA0 -> P.do 
            activeAsset <- pletFields @["currencySymbol", "tokenName"] activeAsset'
            pcon $ PAmounts $ 
                V1.passertPositive #$ -- TODO later optimize here
                    V1.psingleton 
                    # activeAsset.currencySymbol
                    # activeAsset.tokenName
                    #$ pdiv 
                        # (pto $ pto baseAmountA0)
                        #$ ppriceOf # prices # activeAsset.currencySymbol # activeAsset.tokenName
            
        -- if it's in the jump storage, get it from there, otherwise calculate default
        getMidActiveAsset :: Term s (PPrices :--> PPrices :--> PActiveAssets :--> PAsset)
        getMidActiveAsset = plam $ \initialPrices newPrices oldStorage ->
            pmatch (AssocMap.plookup # newPrices # (pto oldStorage)) $ \case 
                PJust storedActiveAsset -> storedActiveAsset
                PNothing -> pdefaultActiveAsset # initialPrices # newPrices


        -- minAmntFlipped ::
        -- minAmntFlipped = 


-- padminRef :: Term s (PData :--> PScriptContext :--> PBool)
-- padminRef = plam $ \dat' ctx -> P.do
--     let signer = phead #$ pfromData $ pfield @"signatories" #$ pfield @"txInfo" # ctx
--         dat = (flip (ptryFrom @PReferenceDatum) fst) dat'
--         owner = pfield @"owner" # dat
--     (signer #== owner)
        
-- -- TODO something about this just being a copy of padminRef with the @P*Datum changed. i.e. merge the datum types into sum type
-- padminDirac :: Term s (PData :--> PScriptContext :--> PBool)
-- padminDirac = plam $ \dat' ctx -> P.do
--     let signer = phead #$ pfromData $ pfield @"signatories" #$ pfield @"txInfo" # ctx
--         dat = (flip (ptryFrom @PDiracDatum) fst) dat'
--         owner = pfield @"owner" # dat
--     (signer #== owner)

-- TODO check everything else stays the same, no minting, no changes to the ref etc. Also staking-wdrwls and delegations
pswap :: Term s (PDirac :--> PEuclidAction :--> PScriptContext :--> PBool) -- ClosedTerm PValidator
pswap = phoistAcyclic $ plam $ \dat red ctx -> P.do 
    info <- pletFields @["inputs", "referenceInputs", "outputs", "mint"] 
            $ pfield @"txInfo" # ctx

    oldDat <- pletFields @["owner", "threadNFT", "paramNFT", "initialPrices", "currentPrices", "activeAmnts", "jumpStorage"] dat
        
    let oldTxO = pfromJust #$ pfind # (poutHasNFT # oldDat.threadNFT) # info.outputs
        newTxO = pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # oldDat.threadNFT) # info.inputs 

    old <- pletFields @["address", "value"] oldTxO
    new <- pletFields @["address", "value", "datum"] newTxO

    PDiracDatum newDat' <- pmatch $ punpackEuclidDatum # new.datum
    newDat <- pletFields @["owner", "threadNFT", "paramNFT", "initialPrices", "currentPrices", "activeAmnts", "jumpStorage"] $ pfield @"_0" # newDat'

    let oldAmnts = oldDat.activeAmnts 
        newAmnts = passertAmntsSortedPositive # newDat.activeAmnts

    (   ( oldDat.owner          #== newDat.owner            ) #&&
        ( oldDat.threadNFT      #== newDat.threadNFT        ) #&&
        ( oldDat.paramNFT       #== newDat.paramNFT         ) #&&
        ( oldDat.initialPrices  #== newDat.initialPrices    ) #&&
        ( old.address           #== new.address             ) #&&

        ( pmatch red $ \case 
            PFlip _ -> 
                ( oldDat.currentPrices  #== newDat.currentPrices    ) #&&
                ( oldDat.jumpStorage    #== newDat.jumpStorage      ) #&&

                ( pflipDirac 
                    # old.value 
                    # new.value 
                    # oldAmnts 
                    # newAmnts 
                    # oldDat.currentPrices
                ) 

            PJump _ -> P.do 
                let newPrices = passertPricesSortedPositive # newDat.currentPrices
                
                    refTxO = pfield @"resolved" #$ pfromJust #$ pfind # (pinHasNFT # oldDat.paramNFT) # info.referenceInputs 
                PParamDatum refDat <- pmatch $ punpackEuclidDatum #$ pfield @"datum" # refTxO
                ( pjumpDirac
                    # (pfield @"_0" # refDat) 
                    # oldDat.initialPrices
                    # oldDat.currentPrices
                    # newPrices
                    # oldAmnts
                    # newAmnts
                    # old.value
                    # new.value
                    # oldDat.jumpStorage
                    # newDat.jumpStorage
                    )
            _ -> ptraceError "unknown action/redeemer" 
            ))

padmin :: Term s ((PAsData V1.PPubKeyHash) :--> PScriptContext :--> PBool)
padmin = plam $ \owner ctx -> P.do
    let signer = phead #$ pfromData $ pfield @"signatories" #$ pfield @"txInfo" # ctx
    (signer #== owner)


pdiracValidator :: ClosedTerm PValidator
pdiracValidator = phoistAcyclic $ plam $ \dat' red' ctx -> P.do 
    let dat = (flip (ptryFrom @PEuclidDatum) fst) dat'
        pass = (pmatch dat $ \case 
            PParamDatum param -> 
                padmin 
                # (pfield @"owner" #$ pfield @"_0" # param)
                # ctx

            PDiracDatum dirac' -> P.do
                let red = (flip (ptryFrom @PEuclidAction) fst) red'
                let dirac = pfield @"_0" #$ dirac'
                pmatch red $ \case 
                    PAdmin _ ->
                        padmin 
                        # (pfield @"owner" # dirac)
                        # ctx
                    _ -> pswap # dirac # red # ctx
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
pdiracMinting :: ClosedTerm PMintingPolicy
pdiracMinting = phoistAcyclic $ plam $ \_ ctx -> P.do
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
