
module Dex.Pool where 

import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)
import qualified Plutarch.Monadic as P
import qualified Plutarch.Api.V1.Value as V1
import qualified Plutarch.Api.V1.Scripts as V1
import Plutarch.DataRepr
import Plutarch.TryFrom
import Plutarch.Positive

import Dex.Types
import Dex.Set
import Dex.Utils
import Dex.Equations

-- pmkSemiPoolNFT :: Term s (V1.PCurrencySymbol :--> PPool :--> PAsset :--> PAsset)
-- pmkSemiPoolNFT = phoistAcyclic $ plam $ \nftCcy pool asset -> P.do 
--     let assets = pcons # (pdata asset) #$ passertSet # (pto pool)      -- TODO vs. plet? -- TODO consider the passertSet elsewhere
--         assetsHash = phashAssetList # assets
--         nftTkn = pcon $ V1.PTokenName $ assetsHash
--     pmkAsset # nftCcy # nftTkn

pmkSemiPoolNFT :: Term s (V1.PCurrencySymbol :--> PPoolID :--> PString :--> PAsset :--> PAsset)
pmkSemiPoolNFT = phoistAcyclic $ plam $ \nftCcy poolID prefix asset -> P.do 
    let hash = psha2_256 # ((pencodeUtf8 # prefix) <> (pto poolID) <> (pmkAssetString # asset))     -- TODO vs. plet? 
        nftTkn = pcon $ V1.PTokenName $ hash
    (pmkAsset # nftCcy # nftTkn)


-- TODO vs. haskell-level and those cool HRecOf-things?
mkSwapValidator :: Term s (V1.PCurrencySymbol :--> PPoolID :--> PAsset :--> PAsset :--> PAsset :--> PScriptContext :--> POpaque)
mkSwapValidator = phoistAcyclic $ plam $ \nftCcy poolID liquidityAsset firstSwapAsset secondSwapAsset context -> P.do
    let pmkSemiPoolNFT' = pmkSemiPoolNFT # nftCcy # poolID -- TODO  vs plam
        info            = pfield @"txInfo" # context -- TODO assuming we never need to check scriptPurpose
    pif 
        (liquidityAsset #== secondSwapAsset) 
        (pSecondAssetSwap # (pmkSemiPoolNFT' # "liquidity") # firstSwapAsset # info) -- TODO a bit inefficient that way, reconsider later
        (pif
            (liquidityAsset #== firstSwapAsset)
            (pFirstAssetSwap # pmkSemiPoolNFT' # firstSwapAsset # secondSwapAsset # info)
            perror
        )

pfindInputUtxo :: Term s (PAsset :--> PBuiltinList PTxInInfo :--> PTxOut)
pfindInputUtxo = phoistAcyclic $ plam $ \nft inputs -> 
    pfield @"resolved" #$ pfindUnique # (phasNFT' # nft) # inputs

pfindOutputUtxo :: Term s (PAsset :--> PBuiltinList PTxOut :--> PTxOut)
pfindOutputUtxo = phoistAcyclic $ plam $ \nft outputs -> pfindUnique # (phasNFT # nft) # outputs

pfindMetaDatum :: Term s (PAsset :--> PBuiltinList PTxInInfo :--> PAssetMeta)
pfindMetaDatum = phoistAcyclic $ plam $ \nft inputs -> P.do 
    let utxo    = pfindInputUtxo # nft # inputs -- TODO vs plet
        datum0  = pfield @"datum" # utxo
    pmatch datum0 $ \case 
        POutputDatum outputDatumRecord  -> P.do
            let datum1  = pfield @"outputDatum" # outputDatumRecord
                datum2  = pfromData datum1
                datum3  = pto datum2
                datum4 = (flip ptryFrom fst) datum3 -- TODO important a) check that it works b) handle what happens if mismatch. Not sure at all this is correct
            pmatch datum4 $ \case 
                PAssetMetaDatum assetMetaRecord -> (pfield @"meta" # assetMetaRecord) 
                _                               -> perror
        _                               -> perror

pBalanceOf :: Term s (PAsset :--> PTxOut :--> PBalance)
pBalanceOf = phoistAcyclic $ plam $ \asset' utxo -> P.do 
    asset <- pletFields @["currencySymbol", "tokenName"] asset'
    let value   = pfield @"value" # utxo  --TODO vs plet
        amount  = ptryPositive #$ V1.pvalueOf # value # asset.currencySymbol # asset.tokenName -- error if zero should be expected
    pcon $ PBalance $ amount

pBalanceOf' :: Term s (PAsset :--> PTxInInfo :--> PBalance)
pBalanceOf' = phoistAcyclic $ plam $ \asset ininfo ->
    pBalanceOf # asset #$ pfield @"resolved" # ininfo

-- TODO could be made slightly more efficient (factor 2)
psumBalancesOf :: Term s (PAsset :--> PAsset :--> PNumLiqUtxos :--> PBuiltinList PTxInInfo :--> PBalance)
psumBalancesOf = phoistAcyclic $ plam $ \nft asset numLiqUtxos inputs' ->
    plet (pfindN # (phasNFT' # nft) # (pto numLiqUtxos) # inputs') $ \inputs ->
        pfoldr  # (plam $ \elem total -> (pBalanceOf' # asset # elem) + total) 
                # (pBalanceOf' # asset #$ phead # inputs)
                #$ ptail # inputs

pFirstAssetSwap :: Term s ((PString :--> PAsset :--> PAsset) :--> PAsset :--> PAsset :--> PTxInfo :--> POpaque)
pFirstAssetSwap = phoistAcyclic $ plam $ \pmkSemiPoolNFT' firstSwapAsset secondSwapAsset info' -> P.do 

    let pmkLiquidityNFT = pmkSemiPoolNFT' # "liquidity" --TODO vs plet
        firstLiqNFT     = pmkLiquidityNFT # firstSwapAsset
        secondLiqNFT    = pmkLiquidityNFT # secondSwapAsset
    info                <- pletFields @["inputs", "referenceInputs", "mint", "outputs", "wdrl"] info' -- TODO check mint and wdrl = zero
    let firstSpentUtxo  = pfindInputUtxo # firstLiqNFT # info.inputs
        secondSpentUtxo = pfindInputUtxo # secondLiqNFT # info.inputs 
        firstOutUtxo    = pfindOutputUtxo # firstLiqNFT # info.outputs 
        secondOutUtxo   = pfindOutputUtxo # secondLiqNFT # info.outputs 
        pmkAssetMetaNFT = pmkSemiPoolNFT' # "assetMeta"
        firstMetaNFT    = pmkAssetMetaNFT # firstSwapAsset 
        secondMetaNFT   = pmkAssetMetaNFT # secondSwapAsset
        firstMetaDatum  = pfindMetaDatum # firstMetaNFT # info.referenceInputs
        secondMetaDatum = pfindMetaDatum # secondMetaNFT # info.referenceInputs

    firstMeta   <- pletFields @["weight", "numLiqUtxos"] firstMetaDatum
    secondMeta  <- pletFields @["weight", "numLiqUtxos"] secondMetaDatum

    let firstReadBalances   = psumBalancesOf # firstLiqNFT # firstSwapAsset # firstMeta.numLiqUtxos # info.inputs 
        secondReadBalances  = psumBalancesOf # secondLiqNFT # secondSwapAsset # secondMeta.numLiqUtxos # info.inputs 
        firstSpentBalance   = pBalanceOf # firstSwapAsset # firstSpentUtxo
        secondSpentBalance  = pBalanceOf # secondSwapAsset # secondSpentUtxo
        firstOutBalance     = pBalanceOf # firstSwapAsset # firstOutUtxo
        secondOutBalance    = pBalanceOf # secondSwapAsset # secondOutUtxo

        firstOldBalance     = firstReadBalances + firstSpentBalance
        secondOldBalance    = secondReadBalances + secondSpentBalance
        firstNewBalance     = firstReadBalances + firstOutBalance 
        secondNewBalance    = secondReadBalances + secondOutBalance
    
    pif 
        (pCheckSwap # firstOldBalance 
                    # secondOldBalance 
                    # firstMeta.weight 
                    # secondMeta.weight 
                    # firstNewBalance
                    # secondNewBalance)
        (popaque $ pcon PUnit)
        perror

pSecondAssetSwap :: Term s ((PAsset :--> PAsset) :--> PAsset :--> PTxInfo :--> POpaque)
pSecondAssetSwap = phoistAcyclic $ plam $ \pmkSemiPoolNFT' firstSwapAsset info -> P.do 
    let inputs  = pfield @"inputs" # info -- TODO vs plet
        fstNFT  = pmkSemiPoolNFT' # firstSwapAsset
        _       = pfindInputUtxo # fstNFT # inputs -- TODO check this works
    (popaque $ pcon PUnit)
