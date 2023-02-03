module Euclid.Test where

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
import qualified Plutarch.Api.V1.Value as V1
import qualified Plutarch.Api.V1.AssocMap as AssocMap
import qualified Plutarch.Monadic as P
import Plutarch.Num
import Plutarch.Maybe

import Cardano.Binary qualified as CBOR
import Codec.Serialise qualified as Codec
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Short qualified as SBS

import Euclid.Utils
import Euclid.Types
import Euclid.Value

mkValue :: [(ByteString, ByteString, Integer)] -> Term s (V1.PValue 'Sorted 'V1.NonZero)
mkValue params = foldr (<>) mempty $ map mkSingleton params
    where 
        mkSingleton :: (ByteString, ByteString, Integer) -> Term s (V1.PValue 'Sorted 'V1.NonZero)
        mkSingleton (ccy, tkn, amnt) = 
            V1.pconstantSingleton 
                (pcon $ V1.PCurrencySymbol $ pconstant ccy) 
                (pcon $ V1.PTokenName $ pconstant tkn) 
                (pconstant amnt)

-- pmkSampleDiracDatum :: Term s PString 
-- pmkSampleDiracDatum = P.do 
--     let 

-- for reference:
-- mkScriptInfo :: Script -> ScriptInfo
-- mkScriptInfo script =
--   let scriptRaw = LBS.toStrict $ Codec.serialise script
--       scriptCBOR = CBOR.serialize' $ SBS.toShort scriptRaw
--    in ScriptInfo
--         { cborHex = Base16.encodeBase16 scriptCBOR
--         , rawHex = Base16.encodeBase16 scriptRaw
--         , hash = scriptHash script
--         }