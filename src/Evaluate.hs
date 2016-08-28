module Evaluate where

import Data.Maybe (fromMaybe)

import Data.Text (Text)
import qualified Data.Text as Text

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Vector (Vector)
import qualified Data.Vector as V

import Syntax.Common
import Syntax.Internal

import Utils

data Env def pf nb nf b f = Env
  { valEnv :: Map f (Val def pf nb nf b f)
  , typEnv :: Map nf (NType def pf nb nf b f)}
  -- maybe signature of definitions?

data Error
  = FromMonadFail String

newtype Eval def pf nb nf b f a = Eval
  {runEval' :: Env def pf nb nf b f
            -> Either (Error) a}

instance Functor (Eval def pf nb nf b f) where
  fmap f (Eval m) = Eval $ fmap f . m

instance Applicative (Eval def pf nb nf bound free) where
  pure x = Eval $ const (Right x)
  Eval f <*> Eval m = Eval $ \ e -> case (f e, m e) of
    (Left xs, _) -> Left xs
    (Right _, Left ys) -> Left ys
    (Right x, Right y) -> Right (x y)

instance Monad (Eval def pf nb nf bound free) where
  return = pure
  Eval f >>= k = Eval $ \ e -> case f e of
    Left xs -> Left xs
    Right y -> runEval' (k y) e
  fail s = Eval $ \ _ -> Left $ (FromMonadFail s)

local :: Endo (Env def pf nb nf b f) -> Endo (Eval def pf nb nf b f a)
local f (Eval m) = Eval $ m . f

ask :: Eval def pf nb nf b f (Env def pf nb nf b f)
ask = Eval $ Right

bindVal' :: (Ord f) => f -> Val def pf nb nf b f -> Endo (Eval def pf nb nf b f a)
bindVal' f p = local (\ e -> e { valEnv = Map.insert f p (valEnv e)})

bindVal :: (Convert b f, Ord f) => b -> Val def pf nb nf b f -> Endo (Eval def pf nb nf b f a)
bindVal b = bindVal' (convert b)

bindType :: (Convert nb nf, Ord nf) => nb -> NType def pf nb nf b f -> Endo (Eval def pf nb nf b f a)
bindType b ty = local (\ e -> e { typEnv = Map.insert (convert b) ty (typEnv e)})

abort :: Error -> Eval def pf nb nf b f a
abort e = Eval $ \ _ -> Left e

unpackPush :: Arg def pf nb nf b f -> Eval def pf nb nf b f (Val def pf nb nf b f)
unpackPush (Push v) = pure v

unpackType :: Arg def pf nb nf b f -> Eval def pf nb nf b f (NType def pf nb nf b f)
unpackType (Type n) = pure n

eval_pop :: Vector a -> Eval def pf nb nf b f (a, Vector a)
eval_pop xs | null xs = fail "eval_pop: empty vector"
            | otherwise = pure (V.head xs, V.tail xs)

unpackCon :: Ord f => f -> Eval def pf nb nf b f (Constructor, Val def pf nb nf b f)
unpackCon f = do
  env <- ask
  case Map.lookup f (valEnv env) of
    Just (Con c args) -> pure (c, args)

unpackThunkVal :: Ord f => f -> Eval def pf nb nf b f (Val def pf nb nf b f)
unpackThunkVal f = do
  env <- ask
  case Map.lookup f (valEnv env) of
    Just (ThunkVal v) -> pure v
    Just (Thunk c) -> error "need to evaluate a call"

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

error2Text :: Error -> Text
error2Text (FromMonadFail s) = Text.pack s

runEval :: Eval def pf nb nf b f a -> Either Text a
runEval (Eval m) = case m (Env Map.empty Map.empty) of
  Left e -> Left (error2Text e)
  Right x -> Right x
