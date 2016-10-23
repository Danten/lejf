{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
module Types.Rules where

import           Data.Foldable
import qualified Data.Vector     as V

import           Syntax.Decl
import           Syntax.Internal
import           Syntax.Subst

import           Types.Errors
import           Types.TC
import           Types.Utils

import           Utils

tcLit :: Literal -> PType -> TC ()
tcLit (LInt _) (PLit TInt) = return ()
tcLit l@(LInt _) p = abort $ InferedDon'tMatchChecked (PT_Lit l) (Positive $ PLit TInt) (Positive p)
tcLit (LStr _) (PLit TString) = return ()
tcLit l@(LStr _) p = abort $ InferedDon'tMatchChecked (PT_Lit l) (Positive $ PLit TString) (Positive p)

tcVal :: Val -> PType -> TC ()
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
  n' <- tcCall ca
  inferedIsCheckedNeg (PT_Call ca) n' n
tcVal (ThunkVal v) p_orig = do
  n <- unpackPos _Ptr p_orig $ ShouldBeButIsA (PT_Val v) "pointer to monadic value"
  p <- unpackNeg _Mon n $ ShouldBeButIsA (PT_Val v) "pointer to monadic value"
  tcVal v p
tcVal v@(Struct vs) p = do
  ps <- unpackPos _PStruct p $ ShouldBeButIsA (PT_Val v) "struct"
  if length vs == length ps
    then sequence_ (V.zipWith tcVal vs ps)
    else abort $ StructArityMisMatch vs ps

tcArg :: Arg -> NType -> TC NType
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

tcArgs :: Args -> NType -> TC NType
tcArgs = go . toList
  where
    go [] m = pure m
    go (a : as) m = do
      m' <- tcArg a m
      go as m'

tcCall :: Call -> TC NType
tcCall (Apply (CDef d) xs) = do
  n <- lookupDef d
  tcArgs xs n
tcCall (Apply (CVar x) xs) = do
  p <- lookupContext x
  n <- unpackPos _Ptr p $ ShouldBeButIsA (PT_Var x) "pointer"
  tcArgs xs n

tcAct :: Act -> TC NType
-- tcAct (Call ca) = tcCall ca
tcAct (PutStrLn x) = do
  tcVal x (PLit TString)
  return $ Mon $ PStruct V.empty
tcAct ReadLn = return $ Mon $ PLit TString
tcAct (Malloc p x) = do
  tcVal x p
  return $ Mon $ p

tcMonad :: CMonad -> NType -> TC ()
tcMonad t@(Return r) n = do
  p <- unpackNeg _Mon n $ ShouldBeButIsA (PT_Mon t) "monadic"
  tcVal r p
tcMonad (Act a) n = do
  n' <- tcAct a
  inferedIsCheckedNeg (PT_Act a) n' n
tcMonad (TCall c) n = do -- TODO this is actually a tail-call and should check that we are not using stack vars
  n' <- tcCall c
  inferedIsCheckedNeg (PT_Call c) n' n
tcMonad (Bind a b m) n = do
  n' <- tcAct a
  p <- unpackNeg _Mon n' $ ShouldBeButIsA (PT_Act a) "monadic"
  local (addTele $ V.singleton (b,p)) (tcMonad m n)
tcMonad (With ca b m) n = do
  p <- tcCall ca
  local (addTele $ V.singleton (b, Ptr p)) $ tcMonad m n
tcMonad (CLeftTerm t) n = do
  tcLeftTerm t $ \ m -> tcMonad m n

tcLeftTerm :: LeftTerm a -> (a -> TC ()) -> TC ()
tcLeftTerm (Case x bs) cont = do
  p_orig <- lookupContext x
  mapping <- unpackPos _PCoProduct p_orig (flip ShouldBeButIsA "labeled sum" $ PT_Var x)
  for_ bs $ \ (Branch c t) -> do
    p <- lookupConType c mapping
    local (updateContext x p) $ cont t
tcLeftTerm (Split x bs t) cont = do
  p_orig <- lookupContext x
  struct <- unpackPos _PStruct p_orig (flip ShouldBeButIsA "struct" $ PT_Var x)
  if V.length bs == V.length struct
    then local (addTele $ V.zip bs struct) $ cont t
    else abort $ StructBoundArityMisMatch bs struct
tcLeftTerm (Derefence v t) cont = do
  p <- lookupContext v
  case p of
    Ptr (Mon p') -> local (updateContext v p') $ cont t
    p' -> abort $ ShouldBeButIsA (PT_Var v) "pointer to a monadic value" (Positive p')

tcRightTerm :: RightTerm a -> NType -> (a -> NType -> TC ()) -> TC ()
tcRightTerm (Lam b t') n_orig cont = do
  (p, n) <- unpackNeg _Fun n_orig $ ShouldBeButIsA PT_Equation "function"
  local (addTele $ V.singleton (b,p)) $ cont t' n
tcRightTerm (TLam _b t') n_orig cont = do
  (_bt, n) <- unpackNeg _Forall n_orig $ ShouldBeButIsA PT_Equation "forall"
  cont t' n
tcRightTerm (New bs) n_orig cont = do
  mapping <- unpackNeg _NObject n_orig $ ShouldBeButIsA PT_Equation "object"
  for_ bs $ \ (CoBranch p t') -> do
    n <- lookupProjType p mapping
    cont t' n


tcTerm :: Term CMonad -> NType -> TC ()
tcTerm (Do r) n = tcMonad r n
tcTerm (LeftTerm t) n = tcLeftTerm t $ \t' -> tcTerm t' n
tcTerm (RightTerm t) n = tcRightTerm t n $ tcTerm
  {-
tcTerm (Let (v,p) b t) n = do
  tcVal v p
  local (addTele $ curry V.singleton b p) (tcTerm t n)
-}


tcDecl :: Decl -> TC ()
tcDecl (DDef n nt t)  = local (\e -> e { nameOfTerm = n}) $ tcTerm t nt -- we should check that nt makes sense
tcDecl (DData{})      = pure ()
tcDecl (CoData{})     = pure ()
tcDecl (Template ns)  = tcNameSpace id ns
tcDecl (Module ns)    = tcNameSpace id ns
tcDecl (Specialise{}) = fail "Not implemented tcDecl:Specialise"

tcNameSpace :: (Endo Env) -> NameSpace -> TC ()
tcNameSpace up (Namespace _ decls)
  = local up
  $ traverse_ tcDecl decls

tcProgram :: Program -> TC ()
tcProgram (Program ns) = tcNameSpace id ns
