{-# LANGUAGE MultiParamTypeClasses #-}
module Evaluate where

import           Data.Maybe      (fromMaybe)

import           Data.Text       (Text)

import qualified Data.Map        as Map

import           Data.Vector     (Vector)
import qualified Data.Vector     as V

import           Evaluate.Error
import           Evaluate.Eval

import           Syntax.Common
import           Syntax.Internal
import           Syntax.Subst

pickBranch :: Constructor -> Vector (Branch mon) -> Eval mon
pickBranch c bs = do
  let bs' = V.filter (\(Branch c' _) -> c == c') bs
  case bs' V.!? 0 of
    Just (Branch _ t) -> pure t

evaluateL :: LeftTerm a -> (Variable -> Val -> a -> Eval b) -> Eval b
evaluateL (Case x bs) cont = do
  (c,p) <- unpackCon x
  t <- pickBranch c bs
  cont x p t
evaluateL (Derefence x t) cont = do
  p <- unpackThunkVal x
  cont x p t

evaluateR :: RightTerm a -> Arg -> (a -> Eval b) -> Eval b
evaluateR (TLam b t) arg cont = do
  n <- unpackType arg
  bindType b n $ cont t
evaluateR (Lam b t) arg cont = do
  p <- unpackPush arg
  bindVal b p $ cont t

evaluate :: Term ty -> Args -> Eval (ty, Env)
evaluate (Do p) args | null args = ask >>= \ e -> pure (p, e)
                     | otherwise = fail "evaluate applied to too many arguments"
evaluate (RightTerm t) args = do
  (arg, args') <- eval_pop args
  evaluateR t arg $ \t' -> evaluate t' args'
evaluate (LeftTerm t) args = evaluateL t $ \x v t' -> do
  bindVal' x v $ evaluate t' args

evaluateSubst :: (Subst ty) => Term ty -> Args -> Eval ty
evaluateSubst term args = do
  (ty, env) <- evaluate term args
  let valSubst free = fromMaybe (Var free) $ Map.lookup free (valEnv env)
      typSubst free = fromMaybe (NVar free) $ Map.lookup free (typEnv env)
  pure $ subst valSubst typSubst ty

runEval :: Eval a -> Either Text a
runEval (Eval m) = case m (Env Map.empty Map.empty) of
  Left e  -> Left (error2Text e)
  Right x -> Right x
