{-# LANGUAGE MultiParamTypeClasses #-}
module Types.TC where

import           Data.Map               (Map)
import qualified Data.Map               as Map

import           Data.Vector            (Vector)
import qualified Data.Vector            as V

import           Syntax.Common
import           Syntax.Internal

import           Types.Errors

import           Utils

newtype TC a = TC
  {runTC' :: Env -> Either (Error Env) a}

data Signature = Signature
  { pconType :: Map TConstructor (Term PType) -- need to change when we add polymorphism
  , nconType :: Map TConstructor (Term NType)
  , sigType  :: Map Definition NType
  }

instance Monoid Signature where
  mempty = Signature mempty mempty mempty
  (Signature a1 a2 a3) `mappend` (Signature b1 b2 b3)
    = Signature (a1 `mappend` b1)
                (a2 `mappend` b2)
                (a3 `mappend` b3)

data Env = Env
  { context    :: Map Variable PType
  , sig        :: Signature
  , nameOfTerm :: QName
  }

instance Functor TC where
  fmap f (TC m) = TC $ fmap f . m

instance Applicative TC where
  pure x = TC $ const (Right x)
  TC f <*> TC m = TC $ \ e -> case (f e, m e) of
    (Left xs, _)       -> Left xs
    (Right _, Left ys) -> Left ys
    (Right x, Right y) -> Right (x y)

instance Monad TC where
  return = pure
  TC f >>= k = TC $ \ e -> case f e of
    Left xs -> Left xs
    Right y -> runTC' (k y) e
  fail s = TC $ \ e -> Left $ Error e (FromMonadFail s)

local :: Endo Env -> Endo (TC a)
local f (TC m) = TC $ m . f

ask :: TC Env
ask = TC Right

reader :: (Env -> a) -> TC a
reader f = fmap f ask

abort :: ErrorType -> TC a
abort t = TC $ \ e -> Left $ Error e t

lookupContext :: Variable -> TC PType
lookupContext f = do
  ctx <- ask
  case Map.lookup f (context ctx) of
    Nothing -> abort $ NotInScope (NIS_Variable f)
    Just p  -> pure p

lookupConType :: Constructor -> PCoProduct -> TC PType
lookupConType c mapping = case Map.lookup c mapping of
  Nothing -> abort $ NotInScope (NIS_Constructor c mapping)
  Just p  -> pure p

lookupProjType :: Projection -> NObject -> TC NType
lookupProjType p mapping = case Map.lookup p mapping of
    Nothing -> abort $ NotInScope (NIS_Projection p mapping)
    Just n  -> pure n

lookupDef :: Definition -> TC NType
lookupDef n = do
  ctx <- ask
  case Map.lookup n (sigType . sig $ ctx) of
    Nothing -> abort $ NotInScope (NIS_Def n)
    Just m  -> pure m

updateContext :: Variable -> PType -> Endo Env
updateContext f p env = env { context = Map.insert f p (context env)}

addTele :: Vector (Binder, PType) -> Endo Env
addTele tele env | V.null tele = env
                 | otherwise   = env {context = context env `Map.union` tele'}
  where
    tele' = Map.fromList $ V.toList $ fmap (\(x,p) -> (convert x,p))tele
