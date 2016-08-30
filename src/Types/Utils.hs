{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
module Types.Utils where

import           Control.Lens.Operators
import           Control.Lens.Prism
import           Control.Monad          (unless)

import           Data.Map               (Map)

import           Syntax.Common
import           Syntax.Internal
import           Syntax.Subst

import           Types.Equality
import           Types.Errors
import           Types.Evaluate
import           Types.TC

import           Utils

make_unpackSubst :: (Ord nf, Convert nb nf, Ord f, Convert b f, Subst ty)
  => (ty def pf nb nf b f -> TypeType def pf nb nf b f)
  -> (Signature def pf nb nf b f
  -> Map TConstructor (Term (ty def pf nb nf b f) def pf nb nf b f))
  -> Prism' (ty def pf nb nf b f) (TConstructor, Args def pf nb nf b f)
  -> Prism' (ty def pf nb nf b f) a
  -> ty def pf nb nf b f
  -> (TypeType def pf nb nf b f -> ErrorType def pf nb nf b f)
  -> TC def pf nb nf b f a
make_unpackSubst tyTy tType priCon pri ty_orig err = go [] ty_orig
  where
    go path ty | Just (d,args) <- ty ^? priCon =
      if d `elem` map fst path
        then abort $ TEvalCycle d path
        else go ((d, args): path) =<< evalCon tType d args
    go path n | Just x <- n ^? pri = pure x
              | otherwise = abort $ err (ByPath path $ tyTy n)

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

inferedIsCheckedNeg :: (Ord defs, Ord pf, Ord nb, Ord nf, Ord f, Convert nb nf, Convert b f)
  => ProgType defs pf nb nf b f -> NType defs pf nb nf b f -> NType defs pf nb nf b f -> TC defs pf nb nf b f ()
inferedIsCheckedNeg pa n n' = do
  b <- checkNegEquality n n'
  unless b $ abort $ InferedDon'tMatchChecked pa (Negative n) (Negative n')

inferedIsCheckedPos :: (Ord defs, Ord pf, Ord nb, Ord nf, Ord f, Convert nb nf, Convert b f)
  => ProgType defs pf nb nf b f -> PType defs pf nb nf b f -> PType defs pf nb nf b f -> TC defs pf nb nf b f ()
inferedIsCheckedPos pa p p' = do
  b <- checkPosEquality p p'
  unless b $ abort $ InferedDon'tMatchChecked pa (Positive p) (Positive p')
