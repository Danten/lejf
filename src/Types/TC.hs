{-# language RankNTypes #-}
module Types.TC where

import Control.Lens.Operators
import Control.Lens.Prism
import Control.Monad (unless)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Vector (Vector)
import qualified Data.Vector as V

import Evaluate(runEval)
import qualified Evaluate as Eval

import Syntax.Common
import Syntax.Internal
import Syntax.Subst

import Types.Errors

import Utils

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
  { context :: Map free (PType def pf nb nf bound free)
  , sig :: Signature def pf nb nf bound free
  , nameOfTerm :: QName
  }

instance Functor (TC def pf nb nf bound free) where
  fmap f (TC m) = TC $ fmap f . m

instance Applicative (TC def pf nb nf bound free) where
  pure x = TC $ const (Right x)
  TC f <*> TC m = TC $ \ e -> case (f e, m e) of
    (Left xs, _) -> Left xs
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
    Just n -> pure n

lookupDef :: (Ord def) => def -> TC def pf nb nf bound free (NType def pf nb nf bound free)
lookupDef n = do
  ctx <- ask
  case Map.lookup n (sigType . sig $ ctx) of
    Nothing -> abort $ NotInScope (NIS_Def n)
    Just m -> pure m

updateContext :: (Ord free) => free -> PType def pf nb nf bound free -> Endo (Env def pf nb nf bound free)
updateContext f p env = env { context = Map.insert f p (context env)}

addTele :: (Ord free, Convert bound free) => Vector (bound, PType def pf nb nf bound free) -> Endo (Env def pf nb nf bound free)
addTele tele env | V.null tele = env
                 | otherwise   = env {context = context env `Map.union` tele'}
  where
    tele' = Map.fromList $ V.toList $ fmap (\(x,p) -> (convert x,p))tele

evaluateSubst :: (Ord nf, Convert nb nf, Ord f, Convert b f, Subst ty)
  => Term (ty def pf nb nf b f) def pf nb nf b f
  -> Args def pf nb nf b f
  -> TC def pf nb nf b f (ty def pf nb nf b f)
evaluateSubst t args = case runEval (Eval.evaluateSubst t args) of
  Left e -> abort $ EvaluationError e
  Right x -> pure x

make_unpackSubst :: (Ord nf, Convert nb nf, Ord f, Convert b f, Subst ty)
  => (ty def pf nb nf b f -> TypeType def pf nb nf b f)
  -> (Signature def pf nb nf b f
  -> Map TConstructor (Term (ty def pf nb nf b f) def pf nb nf b f))
  -> Prism' (ty def pf nb nf b f) (TConstructor, Args def pf nb nf b f)
  -> Prism' (ty def pf nb nf b f) a
  -> ty def pf nb nf b f
  -> (TypeType def pf nb nf b f -> ErrorType def pf nb nf b f)
  -> TC def pf nb nf b f a
make_unpackSubst tyTy tType priCon pri ty_orig err = do
  env <- reader (tType . sig)
  let go path ty | Just (d,args) <- ty ^? priCon =
         if d `elem` map fst path then abort $ TEvalCycle d path
         else case Map.lookup d env of
            Nothing -> abort $ NotInScope (NIS_TConstructor d)
            Just term -> do
              n <- evaluateSubst term args
              go ((d, args):path) n
      go path n | Just x <- n ^? pri = pure x
                | otherwise = abort $ err (ByPath path $ tyTy n)
  go [] ty_orig

unpackPos :: (Ord nf, Convert nb nf, Ord f, Convert b f)
  => Prism' (PType def pf nb nf b f) a -> PType def pf nb nf b f
  -> (TypeType def pf nb nf b f -> ErrorType def pf nb nf b f)
  -> TC def pf nb nf b f a
unpackPos = make_unpackSubst Positive pconType _PCon

unpackNeg :: (Ord nf, Convert nb nf, Ord f, Convert b f)
  => Prism' (NType def pf nb nf b f) a -> NType def pf nb nf b f
  -> (TypeType def pf nb nf b f -> ErrorType def pf nb nf b f)
  -> TC def pf nb nf b f a
unpackNeg = make_unpackSubst Negative nconType _NCon

inferedIsCheckedNeg :: (Eq defs, Eq pf, Eq nb, Eq nf, Eq f)
  => ProgType defs pf nb nf b f -> NType defs pf nb nf b f -> NType defs pf nb nf b f -> TC defs pf nb nf b f ()
inferedIsCheckedNeg pa n n' = unless (n == n') $ abort $ InferedDon'tMatchChecked pa (Negative n) (Negative n')

inferedIsCheckedPos :: (Eq defs, Eq pf, Eq nb, Eq nf, Eq f)
  => ProgType defs pf nb nf b f -> PType defs pf nb nf b f -> PType defs pf nb nf b f -> TC defs pf nb nf b f ()
inferedIsCheckedPos pa p p' = unless (p == p') $ abort $ InferedDon'tMatchChecked pa (Positive p) (Positive p')
