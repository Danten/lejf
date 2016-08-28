module Evaluate where

import Data.Maybe (fromMaybe)

import Data.Text (Text)

import qualified Data.Map as Map

import Data.Vector (Vector)
import qualified Data.Vector as V

import Evaluate.Error
import Evaluate.Eval

import Syntax.Common
import Syntax.Internal
import Syntax.Subst

import Utils

pickBranch :: Constructor -> Vector (Branch mon def pf nb nf b f) -> Eval def pf nb nf b f (Term mon def pf nb nf b f)
pickBranch c bs = do
  let bs' = V.filter (\(Branch c' _) -> c == c') bs
  case bs' V.!? 0 of
    Just (Branch _ t) -> pure t

evaluate :: (Ord nf, Convert nb nf, Ord f, Convert b f)
 => Term ty def pf nb nf b f -> Args def pf nb nf b f
 -> Eval def pf nb nf b f (ty, Env def pf nb nf b f)
evaluate (Do p) args | null args = ask >>= \ e -> pure (p, e)
                     | otherwise = fail "evaluate applied to too many arguments"
evaluate (TLam b t) args = do
  (arg , args') <- eval_pop args
  n <- unpackType arg
  bindType b n $ evaluate t args'
evaluate (Lam b t) args = do
  (arg, args') <- eval_pop args
  p <- unpackPush arg
  bindVal b p $ evaluate t args'
evaluate (Case x bs) args = do
  (c,p) <- unpackCon x
  t <- pickBranch c bs
  bindVal' x p $ evaluate t args
evaluate (Derefence x t) args = do
  p <- unpackThunkVal x
  bindVal' x p $ evaluate t args

evaluateSubst :: (Ord nf, Convert nb nf, Ord f, Convert b f, Subst ty)
  => Term (ty def pf nb nf b f) def pf nb nf b f -> Args def pf nb nf b f
  -> Eval def pf nb nf b f (ty def pf nb nf b f)
evaluateSubst term args = do
  (ty, env) <- evaluate term args
  let valSubst free = fromMaybe (Var free) $ Map.lookup free (valEnv env)
      typSubst free = fromMaybe (NVar free) $ Map.lookup free (typEnv env)
  pure $ subst valSubst typSubst ty

runEval :: Eval def pf nb nf b f a -> Either Text a
runEval (Eval m) = case m (Env Map.empty Map.empty) of
  Left e -> Left (error2Text e)
  Right x -> Right x
