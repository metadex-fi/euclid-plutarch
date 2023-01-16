{-# LANGUAGE TemplateHaskell #-}

module Dex.Types where

import Data.ByteString (ByteString)

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
import qualified Plutarch.Monadic as P
import Plutarch.Num

import Dex.PositiveRational
import Dex.Set

newtype PAsset (s :: S)
    = PAsset
        ( Term
            s
            ( PDataRecord
                '[ "currencySymbol" ':= V1.PCurrencySymbol
                , "tokenName" ':= V1.PTokenName
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PEq, PPartialOrd, POrd, PShow)
instance DerivePlutusType PAsset where type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PAsset

pmkAsset :: Term s (V1.PCurrencySymbol :--> V1.PTokenName :--> PAsset)
pmkAsset = phoistAcyclic $ plam $ \ccy tkn ->
    pcon $ PAsset $
        pdcons @"currencySymbol" @V1.PCurrencySymbol # pdata ccy #$ 
        pdcons @"tokenName" @V1.PTokenName # pdata tkn # 
        pdnil

-- TODO into phantom type (param: token)
newtype PBalance (s :: S) = PBalance (Term s PPositive)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PEq, PPartialOrd, POrd, PNum, PFractional, PShow)
instance DerivePlutusType PBalance where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData (PAsData PBalance)

-- TODO into phantom type (param: token)
newtype PWeight (s :: S) = PWeight (Term s PReducedRational)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PEq, PPartialOrd, POrd, PShow)
instance DerivePlutusType PWeight where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData PWeight

-- TODO into phantom type (param: token)
newtype PNumLiqUtxos (s :: S) = PNumLiqUtxos (Term s PPositive)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PEq, PPartialOrd, POrd, PShow)
instance DerivePlutusType PNumLiqUtxos where type DPTStrat _ = PlutusTypeNewtype

instance PTryFrom PData (PAsData PNumLiqUtxos)

-- TODO check out the stuff using KeyGuarantees and consider using this instead, or ripping it
 -- TODO why is PTxInfo allowed to have PBuiltinList PTxInInfo/PTxOut without PAsData?
newtype PPool (s :: S) = PPool (Term s (PBuiltinList (PAsData PAsset)))
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow)
instance DerivePlutusType PPool where type DPTStrat _ = PlutusTypeNewtype

instance PEq PPool where -- TODO consider moving the passertSets to construction only
    l'' #== r'' = P.do 
        let l' = pto l'' -- TODO vs. plet
            r' = pto r'' 
            l = passertSet # l'
            r = passertSet # r'
        l #== r

newtype PPoolID (s :: S) = PPoolID (Term s PByteString)
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow, PEq, PPartialOrd, POrd)
instance DerivePlutusType PPoolID where type DPTStrat _ = PlutusTypeNewtype    

instance PTryFrom PData (PAsData PPoolID) -- TODO vs. (PAsData x) ?

-- pconcatByteStrings :: -- TODO generalize, but for some reason Semigroup constraint does not register
--     ( PIsListLike list PByteString
--     ) => Term s (list PByteString :--> PByteString)
-- pconcatByteStrings = plam $ \l ->
--     psafeSelfFoldr # (punsafeBuiltin PLC.AppendByteString) # l

pmkAssetString :: Term s (PAsset :--> PByteString)
pmkAssetString = phoistAcyclic $ plam $ \asset' -> P.do
    asset <- pletFields @'["currencySymbol", "tokenName"] $ asset'
    let ccyStr = pfromData $ pto asset.currencySymbol -- TODO vs plet?
        tknStr = pfromData $ pto asset.tokenName
    (ccyStr <> tknStr)

phashAsset :: Term s (PAsset :--> PByteString)
phashAsset = phoistAcyclic $ plam $ \asset -> 
    psha2_256 #$ pmkAssetString # asset

phashAssetList :: Term s (PBuiltinList (PAsData PAsset) :--> PByteString)
phashAssetList = phoistAcyclic $ plam $ \assets ->
    psha2_256 #$ 
            pfoldr # pconcatAssets # (pconstant mempty) # assets
    where 
        pconcatAssets :: Term s ((PAsData PAsset) :--> PByteString :--> PByteString)
        pconcatAssets = plam $ \asset bs -> (pmkAssetString # (pfromData asset)) <> bs


pmkPoolID :: Term s (PPool :--> PPoolID)
pmkPoolID = phoistAcyclic $ plam $ \pool ->
    pcon $ PPoolID $ phashAssetList #$ passertSet # (pto pool) --TODO consider moving passertSet to construction, or using sorted-tags


data PActionRedeemer (s :: S) 
    = PCreateRedeemer (Term s (PDataRecord '["createPool" ':= PPool]))
    | PCloseRedeemer (Term s (PDataRecord '[]))
    | PSwapRedeemer (Term s (PDataRecord 
        '[  "firstAsset" ':= PAsset 
        ,   "secondAsset" ':= PAsset
        ]))
    | PAddRedeemer (Term s (PDataRecord '[]))
    | PRemoveRedeemer (Term s (PDataRecord '[]))
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow)
instance DerivePlutusType PActionRedeemer where type DPTStrat _ = PlutusTypeData

newtype PAssetMeta (s :: S)
    = PAssetMeta
        ( Term
            s
            ( PDataRecord
                '[-- "poolID" ':= PPoolID -- TODO check if all of those are needed
                --, "asset" ':= PAsset
                --, 
                "weight" ':= PWeight
                , "numLiqUtxos" ':= PNumLiqUtxos
                , "emittedLPT" ':= PBalance
                ]
            )
        )
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PDataFields, PShow)
instance DerivePlutusType PAssetMeta where type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PAssetMeta

data PDexDatum (s :: S)
    = PRegistryDatum (Term s (PDataRecord '["pools" ':= PBuiltinList (PAsData PPoolID)]))
    | PAssetMetaDatum (Term s (PDataRecord '["meta" ':= PAssetMeta]))
    | PLiquidityDatum (Term s (PDataRecord 
        '[  "pool" ':= PPoolID
        ,   "asset" ':= PAsset
        ]))
    deriving stock (Generic)
    deriving anyclass (PlutusType, PIsData, PShow)
instance DerivePlutusType PDexDatum where type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PDexDatum -- TODO vs. (PAsData x) ?