{-# LANGUAGE TemplateHaskell #-}

{- | Module     : Main
     Maintainer : emi@haskell.fyi
     Description: Example usage of 'plutarch-script-export'.

Example usage of 'plutarch-script-export'.
-}
module Main (main) where

import Data.Default (def)
import Data.Function ((&))
import Data.Text (Text, unpack)
import Development.GitRev (gitBranch, gitHash)
import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)
import ScriptExport.API (runServer)
import ScriptExport.Options (parseOptions)
import ScriptExport.ScriptInfo (mkValidatorInfo, mkPolicyInfo)
import ScriptExport.Types (Builders, insertBuilder)

-- local modules
-- import Dex.Math
-- import Dex.Equations
-- import Dex.Validator
import Evaluate
import Experiments
-- import ExperimentsMap
import Euclid.Types 
import Euclid.Dirac

main :: IO ()
main =
  parseOptions >>= runServer revision builders
  where
    -- This encodes the git revision of the server. It's useful for the caller
    -- to be able to ensure they are compatible with it.
    revision :: Text
    revision = $(gitBranch) <> "@" <> $(gitHash)

builders :: Builders
builders =
  def
    & insertBuilder @() "alwaysSucceeds0" (\_ -> mkValidatorInfo alwaysSucceeds0)
    -- & insertBuilder @() "alwaysSucceeds1" (\_ -> mkValidatorInfo alwaysSucceeds1)
    & insertBuilder @() "alwaysFails" (\_ -> mkValidatorInfo alwaysFails)
    & insertBuilder @() "matchDatumRedeemer" (\_ -> mkValidatorInfo matchDatumRedeemer)
    & insertBuilder @() "unmatchDatumRedeemer" (\_ -> mkValidatorInfo unmatchDatumRedeemer)
    & insertBuilder @() "matchAlways" (\_ -> mkValidatorInfo matchAlways)
    & insertBuilder @() "matchSquare" (\_ -> mkValidatorInfo matchSquare)
    & insertBuilder @() "matchReference" (\_ -> mkValidatorInfo matchReference)
    & insertBuilder @() "diracValidator" (\_ -> mkValidatorInfo pdiracValidator)
    & insertBuilder @() "diracMinting" (\_ -> mkPolicyInfo pdiracMinting)

{-
type PValidator :: S -> Type
type PValidator =
  PData :--> (PData :--> (PScriptContext :--> POpaque))
  :: S -> Type

popaque ::
  forall (s :: S) (a :: PType).
  Term s a -> Term s POpaque

type role PUnit nominal phantom
type PUnit :: forall {k}. k -> Type
data PUnit @{k} s = PUnit

pcon ::
  forall (a :: PType) (s :: S).
  PlutusType a => a s -> Term s a
-}
