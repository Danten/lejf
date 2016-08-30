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

newtype TC def pf nb nf bound free a = TC
  {runTC' :: Env def pf nb nf bound free
          -> Either (Error Env def pf nb nf bound free) a}

data Signature def pf nb nf b f = Signature
  { pconType :: Map TConstructor (Term (PType def pf nb nf b f) def pf nb nf b f) -- need to change when we add polymorphism
  , nconType :: Map TConstructor (Term (NType def pf nb nf b f) def pf nb nf b f)
  , sigType  :: Map def (NType def pf nb nf b f)
  }

instance (Ord def) => Monoid (Signature def pf nb nf b f) where
  mempty = Signature mempty mempty mempty
  (Signature a1 a2 a3) `mappend` (Signature b1 b2 b3)
    = Signature (a1 `mappend` b1)
                (a2 `mappend` b2)
                (a3 `mappend` b3)

data Env def pf nb nf bound free = Env
  { context    :: Map free (PType def pf nb nf bound free)
  , sig        :: Signature def pf nb nf bound free
  , nameOfTerm :: QName
  }

instance Functor (TC def pf nb nf bound free) where
  fmap f (TC m) = TC $ fmap f . m

instance Applicative (TC def pf nb nf bound free) where
  pure x = TC $ const (Right x)
  TC f <*> TC m = TC $ \ e -> case (f e, m e) of
    (Left xs, _)       -> Left xs
    (Right _, Left ys) -> Left ys
    (Right x, Right y) -> Right (x y)

instance Monad (TC def pf nb nf bound free) where
  return = pure
  TC f >>= k = TC $ \ e -> case f e of
    Left xs -> Left xs
    Right y -> runTC' (k y) e
  fail s = TC $ \ e -> Left $ Error e (FromMonadFail s)

local :: Endo (Env def pf nb nf bound free) -> Endo (TC def pf nb nf bound free a)
local f (TC m) = TC $ m . f

ask :: TC def pf nb nf bound free (Env def pf nb nf bound free)
ask = TC Right

reader :: (Env def pf nb nf b f -> a) -> TC def pf nb nf b f a
reader f = fmap f ask

abort :: ErrorType def pf nb nf bound free -> TC def pf nb nf bound free a
abort t = TC $ \ e -> Left $ Error e t

lookupContext :: (Ord free) => free -> TC def pf nb nf bound free (PType def pf nb nf bound free)
lookupContext f = do
  ctx <- ask
  case Map.lookup f (context ctx) of
    Nothing -> abort $ NotInScope (NIS_Variable f)
    Just p  -> pure p

lookupConType :: Constructor -> PCoProduct def pf nb nf b f -> TC def pf nb nf b f (PType def pf nb nf b f)
lookupConType c mapping = case Map.lookup c mapping of
  Nothing -> abort $ NotInScope (NIS_Constructor c mapping)
  Just p  -> pure p

lookupProjType :: Projection -> NObject def pf nb nf bound free -> TC def pf nb nf bound free (NType def pf nb nf bound free)
lookupProjType p mapping = case Map.lookup p mapping of
    Nothing -> abort $ NotInScope (NIS_Projection p mapping)
    Just n  -> pure n

lookupDef :: (Ord def) => def -> TC def pf nb nf bound free (NType def pf nb nf bound free)
lookupDef n = do
  ctx <- ask
  case Map.lookup n (sigType . sig $ ctx) of
    Nothing -> abort $ NotInScope (NIS_Def n)
    Just m  -> pure m

updateContext :: (Ord free) => free -> PType def pf nb nf bound free -> Endo (Env def pf nb nf bound free)
updateContext f p env = env { context = Map.insert f p (context env)}

addTele :: (Ord free, Convert bound free) => Vector (bound, PType def pf nb nf bound free) -> Endo (Env def pf nb nf bound free)
addTele tele env | V.null tele = env
                 | otherwise   = env {context = context env `Map.union` tele'}
  where
    tele' = Map.fromList $ V.toList $ fmap (\(x,p) -> (convert x,p))tele
