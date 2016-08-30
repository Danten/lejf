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

import           Utils

evaluateSubst' :: (Ord nf, Convert nb nf, Ord f, Convert b f, Subst ty)
  => Term (ty def pf nb nf b f) def pf nb nf b f
  -> Args def pf nb nf b f
  -> TC def pf nb nf b f (Either Text (ty def pf nb nf b f))
evaluateSubst' t args = case runEval (Eval.evaluateSubst t args) of
  Left e  -> pure (Left e)
  Right x -> pure (Right x)

evaluateSubst :: (Ord nf, Convert nb nf, Ord f, Convert b f, Subst ty)
  => Term (ty def pf nb nf b f) def pf nb nf b f
  -> Args def pf nb nf b f
  -> TC def pf nb nf b f (ty def pf nb nf b f)
evaluateSubst t args = do
  m <- evaluateSubst' t args
  case m of
    Left e  -> abort $ EvaluationError e
    Right x -> pure x

evalCon' :: (Ord nf, Convert nb nf, Ord f, Convert b f, Subst ty)
  => (Signature def pf nb nf b f
      -> Map TConstructor (Term (ty def pf nb nf b f) def pf nb nf b f))
  -> TConstructor -> Args def pf nb nf b f
  -> TC def pf nb nf b f (Either Text (ty def pf nb nf b f))
evalCon' tType d args = do
  env <- reader (tType . sig)
  case Map.lookup d env of
    Nothing   -> abort $ NotInScope (NIS_TConstructor d)
    Just term -> evaluateSubst' term args

evalCon :: (Ord nf, Convert nb nf, Ord f, Convert b f, Subst ty)
  => (Signature def pf nb nf b f
      -> Map TConstructor (Term (ty def pf nb nf b f) def pf nb nf b f))
  -> TConstructor -> Args def pf nb nf b f
  -> TC def pf nb nf b f (ty def pf nb nf b f)
evalCon tType d args = do
  m <- evalCon' tType d args
  case m of
    Left e  -> abort $ EvaluationError e
    Right x -> pure x
