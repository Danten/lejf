{-# LANGUAGE MultiParamTypeClasses #-}
module Evaluate.Eval where

import           Data.Map        (Map)
import qualified Data.Map        as Map

import           Data.Vector     (Vector)
import qualified Data.Vector     as V

import           Evaluate.Error

import           Syntax.Common
import           Syntax.Internal

import           Utils

data Env = Env
  { valEnv :: Map Variable Val
  , typEnv :: Map NTVariable NType
  }
  -- maybe signature of definitions?

newtype Eval a = Eval
  {runEval' :: Env -> Either (Error) a}

instance Functor Eval where
  fmap f (Eval m) = Eval $ fmap f . m

instance Applicative Eval where
  pure x = Eval $ const (Right x)
  Eval f <*> Eval m = Eval $ \ e -> case (f e, m e) of
    (Left xs, _)       -> Left xs
    (Right _, Left ys) -> Left ys
    (Right x, Right y) -> Right (x y)

instance Monad Eval where
  return = pure
  Eval f >>= k = Eval $ \ e -> case f e of
    Left xs -> Left xs
    Right y -> runEval' (k y) e
  fail s = Eval $ \ _ -> Left $ (FromMonadFail s)

local :: Endo Env -> Endo (Eval a)
local f (Eval m) = Eval $ m . f

ask :: Eval Env
ask = Eval $ Right

bindVal' :: Variable -> Val -> Endo (Eval a)
bindVal' f p = local (\ e -> e { valEnv = Map.insert f p (valEnv e)})

bindVal :: Binder -> Val -> Endo (Eval a)
bindVal b = bindVal' (convert b)

bindType :: NTBinder -> NType -> Endo (Eval a)
bindType b ty = local (\ e -> e { typEnv = Map.insert (convert b) ty (typEnv e)})

abort :: Error -> Eval a
abort e = Eval $ \ _ -> Left e

unpackPush :: Arg -> Eval Val
unpackPush (Push v) = pure v

unpackType :: Arg -> Eval NType
unpackType (Type n) = pure n

eval_pop :: Vector a -> Eval (a, Vector a)
eval_pop xs | null xs = fail "eval_pop: empty vector"
            | otherwise = pure (V.head xs, V.tail xs)

unpackCon :: Variable -> Eval (Constructor, Val)
unpackCon f = do
  env <- ask
  case Map.lookup f (valEnv env) of
    Just (Con c args) -> pure (c, args)

unpackThunkVal :: Variable -> Eval Val
unpackThunkVal f = do
  env <- ask
  case Map.lookup f (valEnv env) of
    Just (ThunkVal v) -> pure v
    Just (Thunk c)    -> error "need to evaluate a call"
