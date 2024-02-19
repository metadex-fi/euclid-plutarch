{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Evaluate where

import Data.Default (def)
import Data.Text (Text, unpack)
import Plutarch --(ClosedTerm, pcon, plam, popaque, (#))
import Plutarch.Api.V2 --(PValidator, PScriptContext)
import Plutarch.Prelude --(PUnit (PUnit), PData, (:-->), POpaque, perror, (#==), pconstant, pif, PBuiltinList(PNil, PCons), pmatch, pfield, PMaybe(PNothing), pany)
import Plutarch.Builtin --(pasInt)


-- for development
import Plutarch.Evaluate
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget)
-- import PlutusLedgerApi.V1.Scripts (Script (Script))
import qualified UntypedPlutusCore as UPLC
import Data.Text qualified as T
import Plutarch.Script
import Plutarch.Internal
import Control.Monad.Reader (ReaderT (ReaderT), ask, runReaderT)
import Untyped (UTerm, conv) -- from metatheory
import PlutusCore.Quote
import Control.Monad.Error.Class (MonadError)
import PlutusCore.Pretty -- (prettyPlcReadableDebug)

{-
for development:

evalTerm ::
  Config ->
  ClosedTerm a ->
  Either Text (Either E.EvalError (ClosedTerm a), ExBudget, [Text])

(plutarch-plutus/Plutarch/Evaluate.hs)

type Config :: Type
data Config = Config {tracingMode :: TracingMode}
        -- Defined in ‘Plutarch.Internal’

data TracingMode = NoTracing | DoTracing | DetTracing

-- | Default is to be efficient
instance Default Config where
  def =
    Config
      { tracingMode = NoTracing
      }

-}

-- shows budgets
eval :: forall a. ClosedTerm a -> String
eval term = case evaluated of 
    Left compileError -> unpack compileError
    Right (output, budget, log) -> show (budget, log)
  where 
    conf = Config { tracingMode = DoTracing } -- TODO difference to DetTracing?
    evaluated :: Either Text (Either EvalError (ClosedTerm a), ExBudget, [Text])
    evaluated = evalTerm conf term

-- prints the compiled code
pt :: ClosedTerm a -> String
pt term = printTerm def term

toScript :: ClosedTerm a -> Script
toScript term = either (error . T.unpack) id $ compile def term

toUProgram :: ClosedTerm a -> UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
toUProgram term = unScript $ toScript term

toUTerm :: ClosedTerm a -> UPLC.Term UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
toUTerm t = case asClosedRawTerm t of
  TermMonad (ReaderT t') -> case t' def of 
    Right t'' -> compile' t''

fakeNameTerm :: UPLC.Term UPLC.DeBruijn uni fun ann -> UPLC.Term UPLC.NamedDeBruijn uni fun ann
fakeNameTerm = UPLC.termMapNames UPLC.fakeNameDeBruijn 

toFakeNameUTerm :: ClosedTerm a -> UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
toFakeNameUTerm = fakeNameTerm . toUTerm

eraseIndex :: UPLC.NamedDeBruijn -> UPLC.NamedDeBruijn
eraseIndex (UPLC.NamedDeBruijn name ix) = UPLC.NamedDeBruijn name 0

eraseIndexTerm :: UPLC.Term UPLC.NamedDeBruijn uni fun ann -> UPLC.Term UPLC.NamedDeBruijn uni fun ann
eraseIndexTerm = UPLC.termMapNames eraseIndex

unDeBruijn :: ClosedTerm a -> Doc ann
unDeBruijn = prettyPlcReadableDebug . toFakeNameUTerm
-- unDeBruijn = prettyPlcReadableDebug . eraseIndexTerm . toFakeNameUTerm

convTerm :: ClosedTerm a -> UTerm
convTerm = conv . toFakeNameUTerm

-- unDeBruijn :: (PlutusCore.Quote.MonadQuote m, UPLC.AsFreeVariableError e, 
--   Control.Monad.Error.Class.MonadError e m) => 
--     ClosedTerm a -> m (UPLC.Term UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ())
-- unDeBruijn = UPLC.unDeBruijnTerm . toFakeNameUTerm
