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