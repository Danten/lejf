{-# language OverloadedStrings, RankNTypes #-}
module Types where

import Control.Lens.Operators
import Control.Lens.Prism
import Control.Monad

import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text

import Data.Foldable

import Evaluate (Eval, runEval)
import qualified Evaluate as Eval

import Syntax.Concrete
import Syntax.Common
import Syntax.Internal

import Syntax.Pretty (Pretty)
import qualified Syntax.Pretty as Pretty

import Utils

newtype TC def pf nb nf bound free a = TC
  {runTC' :: Env def pf nb nf bound free
          -> Either (Error def pf nb nf bound free) a}

data Signature def pf nb nf b f = Signature
  { pconType :: Map TConstructor (Term (PType def pf nb nf b f) def pf nb nf b f) -- need to change when we add polymorphism
  , nconType :: Map TConstructor (Term (NType def pf nb nf b f) def pf nb nf b f)
  , sigType :: Map def (NType def pf nb nf b f)
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

  {-
instance (Ord free, Ord def) => Monoid (Env def pf nb nf free) where
  mempty = Env mempty mempty
  (Env a1 a2) `mappend` (Env b1 b2) = Env (a1 `mappend` b1) (a2 `mappend` b2)
-}

data Error def pf nb nf bound free
  = Error (Env def pf nb nf bound free) (ErrorType def pf nb nf bound free)

data ProgType def pf nb nf bound free
  = PT_Act (Act def pf nb nf bound free)
  | PT_Mon (CMonad def pf nb nf bound free)
  -- | PT_Term (Term def pf nb nf bound free)
  | PT_Equation
  | PT_Val (Val def pf nb nf bound free)
  | PT_Proj Projection
  | PT_Lit Literal
  | PT_Var free
  | PT_Con Constructor
  | PT_Def def

type TypeEvaluationPath def pf nb nf b f = [(TConstructor, Args def pf nb nf b f)]

data TypeType def pf nb nf b f
  = Positive (PType def pf nb nf b f)
  | ByPath (TypeEvaluationPath def pf nb nf b f) (TypeType def pf nb nf b f)
  | Negative (NType def pf nb nf b f)

data NotInScope def pf nb nf bound free
  = NIS_Constructor Constructor (PCoProduct def pf nb nf bound free)
  | NIS_TConstructor TConstructor
  | NIS_Projection Projection (NObject def pf nb nf bound free)
  | NIS_Def def
  | NIS_Variable free

data ErrorType def pf nb nf bound free
  = FromMonadFail String
  | NotInScope (NotInScope def pf nb nf bound free)
  | StructArityMisMatch (Vector (Val def pf nb nf bound free)) (Vector (PType def pf nb nf bound free))
  | StructBoundArityMisMatch (Vector bound) (Vector (PType def pf nb nf bound free))
  | ShouldBeButIsA (ProgType def pf nb nf bound free) Text (TypeType def pf nb nf bound free)
  | PushArgumentToNoFun (Val def pf nb nf bound free) (TypeType def pf nb nf bound free)
  | ProjArgumentToNoObject Projection (TypeType def pf nb nf bound free)
  | TEvalCycle TConstructor (TypeEvaluationPath def pf nb nf bound free)
  | EvaluationError Text
  | InferedDon'tMatchChecked (ProgType def pf nb nf bound free)
        (TypeType def pf nb nf bound free)
        (TypeType def pf nb nf bound free)

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
    -- tele' :: Map Variable (PType bound free)
    tele' = Map.fromList $ V.toList $ fmap (\(x,p) -> (convert x,p))tele


{-
evaluate :: (Ord nf, Convert nb nf)
  => Term ty def pf nb nf b f -> Args def pf nb nf b f -> TC def pf nb nf b f ty
evaluate t args = case runEval (Eval.evaluate t args) of
  Left e -> abort $ EvaluationError e
  Right x -> pure $ fst x
-}

evaluateSubst :: (Ord nf, Convert nb nf, Ord f, Convert b f, Subst ty)
  => Term (ty def pf nb nf b f) def pf nb nf b f
  -> Args def pf nb nf b f
  -> TC def pf nb nf b f (ty def pf nb nf b f)
evaluateSubst t args = case runEval (Eval.evaluateSubst t args) of
  Left e -> abort $ EvaluationError e
  Right x -> pure x

{-
make_unpack :: (Ord nf, Convert nb nf)
  => (ty -> TypeType def pf nb nf b f)
  -> (Signature def pf nb nf b f
  -> Map TConstructor (Term ty def pf nb nf b f))
  -> Prism' ty (TConstructor, Args def pf nb nf b f)
  -> Prism' ty a
  -> ty
  -> (TypeType def pf nb nf b f -> ErrorType def pf nb nf b f)
  -> TC def pf nb nf b f a
make_unpack tyTy tType priCon pri ty_orig err = do
  env <- reader (tType . sig)
  let go path ty | Just (d,args) <- ty ^? priCon =
         if d `elem` map fst path then abort $ TEvalCycle d path
         else case Map.lookup d env of
            Nothing -> abort $ NotInScope (NIS_TConstructor d)
            Just term -> do
              n <- evaluate term args
              go ((d, args):path) n
      go path n | Just x <- n ^? pri = pure x
                | otherwise = abort $ err (ByPath path $ tyTy n)
  go [] ty_orig
-}

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

tcLit :: () => Literal -> PType defs pf nb nf bound free -> TC defs pf nb nf bound free ()
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


collectDecl :: Decl pb pf nb nf bound free -> Signature QName pf nb nf bound free
collectDecl (DData n _k ty) = Signature (Map.singleton (TConstructor n) ty) mempty mempty
collectDecl (DDef n nt _) = Signature mempty mempty (Map.singleton n nt)
collectDecl (CoData n _k ty) = Signature mempty (Map.singleton (TConstructor n) ty) mempty
collectDecl (Template{}) = mempty
collectDecl (Module{}) = mempty
collectDecl (Specialise{}) = mempty

collectNameSpace :: NameSpace a pb pf nb nf bound free -> Signature QName pf nb nf bound free
collectNameSpace (Namespace _ _ _ decls) = foldMap collectDecl decls

collectProgram :: Program pb pf nb nf bound free -> Signature QName pf nb nf bound free
collectProgram (Program ns) = collectNameSpace ns

runTC :: (Ord free, Ord nf, Eq pf, Eq nb, Convert bound free, Convert nb nf
         , Pretty pf, Pretty nb, Pretty nf, Pretty bound, Pretty free)
      => Program pb pf nb nf bound free ->IO ()
runTC m = case runTC' (tcProgram m) (Env mempty (collectProgram m) undefined) of
  Right x -> pure x
  Left xs -> {-mapM_-} Text.putStrLn (error2Text xs) >> error "Typechecking failed"

ttText :: (Pretty def, Pretty pf, Pretty nb, Pretty nf, Pretty f) => TypeType def pf nb nf b f -> Text
ttText (Positive p) = Pretty.pprint p
ttText (Negative n) = Pretty.pprint n
ttText (ByPath [] t) = ttText t
ttText (ByPath ds tf) = foldr (\(n,a) t -> Pretty.pprint n <> Pretty.toText 0 (Pretty.args a) <> " ~> " <> t) (ttText tf) ds

ptText :: (Pretty def, Pretty pf, Pretty nb, Pretty nf, Pretty b, Pretty f)
       => ProgType def pf nb nf b f -> Text
ptText (PT_Act a) = Pretty.pprint a
ptText (PT_Proj p) = Pretty.pprint p
ptText (PT_Val v) = Pretty.pprint v
ptText (PT_Mon m) = Pretty.pprint m
ptText (PT_Con c) = Pretty.pprint c
ptText (PT_Def d) = Pretty.pprint d
ptText (PT_Var x) = Pretty.pprint x
ptText (PT_Lit l) = Pretty.pprint l
ptText (PT_Equation) = "!EQUATION!"

nisText :: (Pretty def) => NotInScope def pf nb nf b f-> Text
nisText (NIS_Def d) = "definition «" <> Pretty.pprint d <> "»"

errorType2Text :: (Pretty def, Pretty pf, Pretty nb, Pretty nf, Pretty bound, Pretty free)
  => ErrorType def pf nb nf bound free -> Text
errorType2Text (FromMonadFail s) = Text.pack s
errorType2Text (TEvalCycle c cs) = "Cycle detected when evaluating «" <> Pretty.pprint c <> "»\n" <>
  "evaluation causes the following path" <> foldr (\(d,as) r -> Pretty.pprint (PCon d as) <> " ~> " <> r) "" cs
errorType2Text (StructBoundArityMisMatch bs ty) = "Trying to split a struct of type «" <> Pretty.pprint (PStruct ty) <> "»\n" <>
  "but the binders you provided «" <> Pretty.toText 0 (Pretty.intersperse ", " $ V.toList $ fmap Pretty.pretty bs) <> "»"
errorType2Text (PushArgumentToNoFun v t) = "Trying to push value «" <> ptText (PT_Val v) <> "»\n" <>
 "but the transformation should be of type «" <> ttText t <> "»\n" <>
 "which is not a function type! We can only push values when the transformation is a function."
errorType2Text (ProjArgumentToNoObject p t) = "Trying to project «" <> Pretty.pprint p <> "»\n" <>
 "but the transformation should be of type «" <> ttText t <> "»\n" <>
 "which is not an object type! We can only project when the transformation is an object."
errorType2Text (NotInScope n) = "Not in scope: " <> nisText n
errorType2Text (StructArityMisMatch _ _) = "Struct arity mis-match"
errorType2Text (InferedDon'tMatchChecked p i c) = "Infered type don't match the checked type:\n"
  <> "For term «" <> ptText p <> "»\n"
  <> "We infered «" <> ttText i <> "» but "
  <> "one would expect «" <> ttText c <> "»\n\n"
errorType2Text (ShouldBeButIsA p desc t) = "The program is not of the correct type:\n"
  <> "We expect a term of type «" <> ttText t <> "» but "
  <> "the term «" <> ptText p <> "» builds " <> desc
errorType2Text (EvaluationError e) = e

error2Text :: (Pretty def, Pretty pf, Pretty nb, Pretty nf, Pretty b, Pretty f)
  => Error def pf nb nf b f -> Text
error2Text (Error env t)
  = let QName root loc = nameOfTerm env in foldr (\x y -> x `mappend`"." `mappend` y) loc root `mappend` ": " `mappend` errorType2Text t
