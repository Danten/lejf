{-# language OverloadedStrings #-}
module Types.Rules where

import Data.Foldable
import qualified Data.Vector as V

import Syntax.Common
import Syntax.Decl
import Syntax.Internal
import Syntax.Subst

import Types.Errors
import Types.TC

import Utils

tcLit :: Literal -> PType defs pf nb nf bound free -> TC defs pf nb nf bound free ()
tcLit (LInt _) (PLit TInt) = return ()
tcLit l@(LInt _) p = abort $ InferedDon'tMatchChecked (PT_Lit l) (Positive $ PLit TInt) (Positive p)
tcLit (LStr _) (PLit TString) = return ()
tcLit l@(LStr _) p = abort $ InferedDon'tMatchChecked (PT_Lit l) (Positive $ PLit TString) (Positive p)

tcVal :: (Ord free, Ord defs, Eq pf, Eq nb, Ord nf, Convert nb nf, Convert bound free)
      => Val defs pf nb nf bound free -> PType defs pf nb nf bound free  -> TC defs pf nb nf bound free ()
tcVal (Var x) p = do
  p' <- lookupContext x
  inferedIsCheckedPos (PT_Var x) p' p
tcVal (Lit l) p = tcLit l p
tcVal v@(Con c a) p = do
  m <- unpackPos _PCoProduct p (flip ShouldBeButIsA "Labeled sum" $ PT_Val v)
  p' <- lookupConType c m
  tcVal a p'
tcVal v@(Thunk ca) p = do
  n <- unpackPos _Ptr p $ ShouldBeButIsA (PT_Val v) "pointer"
  n' <- tcAct ca
  inferedIsCheckedNeg (PT_Act ca) n' n
tcVal (ThunkVal v) p_orig = do
  n <- unpackPos _Ptr p_orig $ ShouldBeButIsA (PT_Val v) "pointer to monadic value"
  p <- unpackNeg _Mon n $ ShouldBeButIsA (PT_Val v) "pointer to monadic value"
  tcVal v p
tcVal v@(Struct vs) p = do
  ps <- unpackPos _PStruct p $ ShouldBeButIsA (PT_Val v) "struct"
  if length vs == length ps
    then sequence_ (V.zipWith tcVal vs ps)
    else abort $ StructArityMisMatch vs ps

tcArg :: (Ord free, Ord defs, Eq pf, Eq nb, Ord nf, Convert nb nf, Convert bound free)
      => Arg defs pf nb nf bound free -> NType defs pf nb nf bound free
      -> TC defs pf nb nf bound free (NType defs pf nb nf bound free)
tcArg (Push v) n_orig = do
  (p, n) <- unpackNeg _Fun n_orig $ PushArgumentToNoFun v
  tcVal v p
  pure n
tcArg (Proj p) n_orig = do
  mapping <- unpackNeg _NObject n_orig $ ProjArgumentToNoObject p
  lookupProjType p mapping
tcArg (Type m) n_orig = do
  (b, n) <- unpackNeg _Forall n_orig undefined
  pure $ substNTypeOne (convert b) m n

tcArgs :: (Ord free, Ord defs, Eq pf, Eq nb, Ord nf, Convert nb nf, Convert bound free)
       => Args defs pf nb nf bound free -> NType defs pf nb nf bound free
       -> TC defs pf nb nf bound free (NType defs pf nb nf bound free)
tcArgs = go . toList
  where
    go [] m = pure m
    go (a : as) m = do
      m' <- tcArg a m
      go as m'

tcCall :: (Ord free, Ord defs, Eq pf, Eq nb, Ord nf, Convert nb nf, Convert bound free)
       => Call defs pf nb nf bound free -> TC defs pf nb nf bound free (NType defs pf nb nf bound free)
tcCall (Apply (CDef d) xs) = do
  n <- lookupDef d
  tcArgs xs n
tcCall (Apply (CVar x) xs) = do
  p <- lookupContext x
  n <- unpackPos _Ptr p $ ShouldBeButIsA (PT_Var x) "pointer"
  tcArgs xs n

tcAct :: (Ord free, Ord defs, Eq pf, Eq nb, Ord nf, Convert nb nf, Convert bound free)
  =>Act defs pf nb nf bound free -> TC defs pf nb nf bound free (NType defs pf nb nf bound free)
tcAct (Call ca) = tcCall ca
tcAct (PutStrLn x) = do
  tcVal x (PLit TString)
  return $ Mon $ PStruct V.empty
tcAct ReadLn = return $ Mon $ PLit TString

tcMonad :: (Ord free, Ord defs, Eq pf, Eq nb, Ord nf, Convert nb nf, Convert bound free)
  => CMonad defs pf nb nf bound free -> NType defs pf nb nf bound free -> TC defs pf nb nf bound free ()
tcMonad t@(Return r) n = do
  p <- unpackNeg _Mon n $ ShouldBeButIsA (PT_Mon t) "monadic"
  tcVal r p
tcMonad (Act a) n = do
  n' <- tcAct a
  inferedIsCheckedNeg (PT_Act a) n' n
tcMonad (Bind a b m) n = do
  n' <- tcAct a
  p <- unpackNeg _Mon n' $ ShouldBeButIsA (PT_Act a) "monadic"
  local (addTele $ V.singleton (b,p)) (tcMonad m n)

tcTerm :: (Ord free, Convert bound free,Ord defs, Eq pf, Eq nb, Ord nf, Convert nb nf)
       => Term (CMonad defs pf nb nf bound free) defs pf nb nf bound free -> NType defs pf nb nf bound free
       -> TC defs pf nb nf bound free ()
tcTerm (Lam b t') n_orig = do
  (p, n) <- unpackNeg _Fun n_orig $ ShouldBeButIsA PT_Equation "function"
  local (addTele $ V.singleton (b,p)) $ tcTerm t' n
tcTerm (TLam _b t') n_orig = do
  (_bt, n) <- unpackNeg _Forall n_orig $ ShouldBeButIsA PT_Equation "forall"
  tcTerm t' n
tcTerm (New bs) n_orig = do
  mapping <- unpackNeg _NObject n_orig $ ShouldBeButIsA PT_Equation "object"
  for_ bs $ \ (CoBranch p t') -> do
    n <- lookupProjType p mapping
    tcTerm t' n
tcTerm (Do r) n = tcMonad r n
tcTerm (Case x bs) n = do
  p_orig <- lookupContext x
  mapping <- unpackPos _PCoProduct p_orig (flip ShouldBeButIsA "labeled sum" $ PT_Var x)
  for_ bs $ \ (Branch c t) -> do
    p <- lookupConType c mapping
    local (updateContext x p) $ tcTerm t n
tcTerm (Split x bs t') n = do
  p_orig <- lookupContext x
  struct <- unpackPos _PStruct p_orig (flip ShouldBeButIsA "struct" $ PT_Var x)
  if V.length bs == V.length struct
    then local (addTele $ V.zip bs struct) (tcTerm t' n)
    else abort $ StructBoundArityMisMatch bs struct
tcTerm (Derefence v t) n = do
  p <- lookupContext v
  case p of
    Ptr (Mon p') -> local (updateContext v p') $ tcTerm t n
    p' -> abort $ ShouldBeButIsA (PT_Var v) "pointer to a monadic value" (Positive p')
tcTerm (With ca b t) n = do
  p <- tcCall ca
  local (addTele $ V.singleton (b, Ptr p)) $ tcTerm t n
tcTerm (Let (v,p) b t) n = do
  tcVal v p
  local (addTele $ curry V.singleton b p) (tcTerm t n)


tcDecl :: (Ord free , Eq pf, Eq nb, Ord nf, Convert bound free, Convert nb nf)
       => Decl pb pf nb nf bound free -> TC QName pf nb nf bound free ()
tcDecl (DDef n nt t) = local (\e -> e { nameOfTerm = n}) $ tcTerm t nt -- we should check that nt makes sense
tcDecl (DData{}) = pure ()
tcDecl (CoData{}) = pure ()
tcDecl (Template ns) = tcNameSpace (flip const) ns
tcDecl (Module ns) = tcNameSpace (flip const) ns
tcDecl (Specialise{}) = fail "Not implemented tcDecl:Specialise"

tcNameSpace :: (Ord free, Convert bound free, Convert nb nf, Eq pf, Eq nb, Ord nf)
            => (a -> Endo (Env QName pf nb nf bound free)) -> NameSpace a pb pf nb nf bound free -> TC QName pf nb nf bound free ()
tcNameSpace up (Namespace _ t tele decls)
  = local (up t)
  $ local (addTele tele)
  $ traverse_ tcDecl decls

tcProgram :: (Ord free, Convert bound free, Convert nb nf
             , Eq pf, Eq nb, Ord nf)
          => Program pb pf nb nf bound free -> TC QName pf nb nf bound free ()
tcProgram (Program ns) = tcNameSpace (const id) ns
