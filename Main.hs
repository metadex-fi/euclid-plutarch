{-# LANGUAGE TemplateHaskell #-}

{- | Module     : Main
     Maintainer : emi@haskell.fyi
     Description: Example usage of 'plutarch-script-export'.

Example usage of 'plutarch-script-export'.
-}
module Main (main) where

import Data.Default (def)
import Data.Map (fromList)
import Data.Text (unpack)
import Plutarch (compile)
import Plutarch.Api.V2 (PValidator)
import Plutarch.Prelude (
  ClosedTerm,
  PInteger,
  PUnit (PUnit),
  pcon,
  pconstant,
  plam,
  plet,
  popaque,
  tcont,
  unTermCont,
  (#),
  (:-->),
 )
import Ply ((#))
import Ply.Plutarch.TypedWriter (mkEnvelope)
import ScriptExport.Export (exportMain)
import ScriptExport.ScriptInfo (
  Linker,
  RawScriptExport (RawScriptExport),
  RoledScript (RoledScript),
  ScriptExport (ScriptExport),
  ScriptRole (ValidatorRole),
  fetchTS,
  getParam,
  mkValidatorInfo,
  mkPolicyInfo,
  toRoledScript,
 )
import ScriptExport.Types (
  Builders,
  insertBuilder,
  insertScriptExportWithLinker,
  insertStaticBuilder,
 )

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
main = exportMain builders

{-
This is the collection of builders. API and file will be created based on provided
builders. There are various `insertXYZBuilder` functions to provide versatile ways
of adding builders.
`insertStaticBuilder` will insert builder that does not have any
argument--as "static" suggests.
`insertBuilder` will insert builder from a function. Argument type
needs `Aeson.FromJSON` and return type needs `Aeson.ToJSON`.
`insertScriptExportWithLinker` is similar to `insertBuilder` but
specialized to `RawScriptExport` and `Linker`. It will automatically
handle linker given parameter. Also, it will return serialized
`RawScript` if no parameter is given.
-}
builders :: Builders
builders =
  mconcat
    [ insertStaticBuilder "alwaysSucceeds0" (mkValidatorInfo alwaysSucceeds0)
        -- , insertStaticBuilder "alwaysSucceeds1" (mkValidatorInfo alwaysSucceeds1)
    , insertStaticBuilder "alwaysFails" (mkValidatorInfo alwaysFails)
    , insertStaticBuilder "matchDatumRedeemer" (mkValidatorInfo matchDatumRedeemer)
    , insertStaticBuilder "unmatchDatumRedeemer" (mkValidatorInfo unmatchDatumRedeemer)
    , insertStaticBuilder "matchAlways" (mkValidatorInfo matchAlways)
    , insertStaticBuilder "matchSquare" (mkValidatorInfo matchSquare)
    , insertStaticBuilder "matchReference" (mkValidatorInfo matchReference)
    , insertStaticBuilder "euclidValidator" (mkValidatorInfo peuclidValidator)
    , insertStaticBuilder "euclidMinting" (mkPolicyInfo peuclidMinting)
    -- , insertBuilder @Integer
    --     "alwaysSucceedsParam"
    --     (\x -> mkValidatorInfo (alwaysSucceedsParam Plutarch.Prelude.# pconstant x))
    -- , insertStaticBuilder "my-onchain-project" myproject
    -- , insertScriptExportWithLinker "my-onchain-project-param" myProjectParameterized myProjectLinker
    ]

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
