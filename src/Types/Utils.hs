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

make_unpackSubst :: (Subst ty)
  => (ty -> TypeType)
  -> (Signature
  -> Map TConstructor (Term ty))
  -> Prism' ty (TConstructor, Args)
  -> Prism' ty a
  -> ty
  -> (TypeType -> ErrorType)
  -> TC a
make_unpackSubst tyTy tType priCon pri ty_orig err = go [] ty_orig
  where
    go path ty | Just (d,args) <- ty ^? priCon =
      if d `elem` map fst path
        then abort $ TEvalCycle d path
        else go ((d, args): path) =<< evalCon tType d args
    go path n | Just x <- n ^? pri = pure x
              | otherwise = abort $ err (ByPath path $ tyTy n)

unpackPos :: Prism' PType a -> PType -> (TypeType -> ErrorType) -> TC a
unpackPos = make_unpackSubst Positive pconType _PCon

unpackNeg :: Prism' NType a -> NType -> (TypeType -> ErrorType) -> TC a
unpackNeg = make_unpackSubst Negative nconType _NCon

inferedIsCheckedNeg :: ProgType -> NType -> NType -> TC ()
inferedIsCheckedNeg pa n n' = do
  b <- checkNegEquality n n'
  unless b $ abort $ InferedDon'tMatchChecked pa (Negative n) (Negative n')

inferedIsCheckedPos :: ProgType -> PType -> PType -> TC ()
inferedIsCheckedPos pa p p' = do
  b <- checkPosEquality p p'
  unless b $ abort $ InferedDon'tMatchChecked pa (Positive p) (Positive p')
