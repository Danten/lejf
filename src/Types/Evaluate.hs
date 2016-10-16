{-# LANGUAGE MultiParamTypeClasses #-}
module Types.Evaluate where

import           Data.Map        (Map)
import qualified Data.Map        as Map

import           Data.Text

import           Evaluate        (runEval)
import qualified Evaluate        as Eval

import           Syntax.Common
import           Syntax.Internal
import           Syntax.Subst

import           Types.Errors
import           Types.TC

evaluateSubst' :: (Subst ty) => Term ty -> Args -> TC (Either Text ty)
evaluateSubst' t args = case runEval (Eval.evaluateSubst t args) of
  Left e  -> pure (Left e)
  Right x -> pure (Right x)

evaluateSubst :: (Subst ty) => Term ty -> Args -> TC ty
evaluateSubst t args = do
  m <- evaluateSubst' t args
  case m of
    Left e  -> abort $ EvaluationError e
    Right x -> pure x

evalCon' :: (Subst ty) => (Signature -> Map TConstructor (Term ty))
  -> TConstructor -> Args -> TC (Either Text ty)
evalCon' tType d args = do
  env <- reader (tType . sig)
  case Map.lookup d env of
    Nothing   -> abort $ NotInScope (NIS_TConstructor d)
    Just term -> evaluateSubst' term args

evalCon :: (Subst ty) => (Signature -> Map TConstructor (Term ty))
  -> TConstructor -> Args -> TC ty
evalCon tType d args = do
  m <- evalCon' tType d args
  case m of
    Left e  -> abort $ EvaluationError e
    Right x -> pure x
