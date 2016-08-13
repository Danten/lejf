{-# language OverloadedStrings #-}
module Types where

import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text

import Data.Foldable

import Control.Monad

import Syntax.Concrete
import Syntax.Common
import Syntax.Internal

import Syntax.Pretty (Pretty)
import qualified Syntax.Pretty as Pretty

newtype TC def pf nb nf bound free a = TC
  {runTC' :: Env def pf nb nf free
          -> Either (Error def pf nb nf bound free) a}
type Endo a = a -> a

data Signature def pf nb nf = Signature
  { pconType :: Map TConstructor (PType pf nb nf) -- need to change when we add polymorphism
  , nconType :: Map TConstructor (NType pf nb nf)
  , sigType :: Map def (NType pf nb nf)
  }

instance (Ord def) => Monoid (Signature def pf nb nf) where
  mempty = Signature mempty mempty mempty
  (Signature a1 a2 a3) `mappend` (Signature b1 b2 b3)
    = Signature (a1 `mappend` b1)
                (a2 `mappend` b2)
                (a3 `mappend` b3)

data Env def pf nb nf free = Env
  { context :: Map free (PType pf nb nf)
  , sig :: Signature def pf nb nf
  , nameOfTerm :: QName
  }

  {-
instance (Ord free, Ord def) => Monoid (Env def pf nb nf free) where
  mempty = Env mempty mempty
  (Env a1 a2) `mappend` (Env b1 b2) = Env (a1 `mappend` b1) (a2 `mappend` b2)
-}

data Error def pf nb nf bound free
  = Error (Env def pf nb nf free) (ErrorType def pf nb nf bound free)

data ProgType def pf nb nf bound free
  = PT_Act (Act def pf nb nf bound free)
  | PT_Mon (CMonad def pf nb nf bound free)
  | PT_Term (Term def pf nb nf bound free)
  | PT_Val (Val def pf nb nf bound free)
  | PT_Proj Projection
  | PT_Lit Literal
  | PT_Var free
  | PT_Con Constructor
  | PT_Def def

data TypeType pf nb nf
  = Positive (PType pf nb nf)
  | PositiveCon TConstructor (PType pf nb nf)
  | Negative (NType pf nb nf)
  | NegativeCon TConstructor (NType pf nb nf)

data NotInScope def pf nb nf
  = NIS_Constructor Constructor (PCoProduct pf nb nf)
  | NIS_TConstructor TConstructor
  | NIS_Projection Projection (NObject pf nb nf)
  | NIS_Def def

data ErrorType def pf nb nf bound free
  = FromMonadFail String
  | NotInScope (NotInScope def pf nb nf)
  | ConstructorIsOfWrongType Constructor (PCoProduct pf nb nf)
  | StructArityMisMatch (Vector (Val def pf nb nf bound free)) (Vector (PType pf nb nf))
  | StructBoundArityMisMatch (Vector bound) (Vector (PType pf nb nf))
  | ShouldBeButIsA (ProgType def pf nb nf bound free) Text (TypeType pf nb nf)
  | PushArgumentToNoFun (Val def pf nb nf bound free) (TypeType pf nb nf)
  | ProjArgumentToNoObject Projection (TypeType pf nb nf)
  | InferedDon'tMatchChecked (ProgType def pf nb nf bound free)
        (TypeType pf nb nf)
        (TypeType pf nb nf)

(<>) :: Monoid m => m -> m -> m
(<>) = mappend

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

local :: Endo (Env def pf nb nf free) -> Endo (TC def pf nb nf bound free a)
local f (TC m) = TC $ m . f

ask :: TC def pf nb nf bound free (Env def pf nb nf free)
ask = TC Right

reader :: (Env def pf nb nf f -> a) -> TC def pf nb nf b f a
reader f = fmap f ask

abort :: ErrorType def pf nb nf bound free -> TC def pf nb nf bound free a
abort t = TC $ \ e -> Left $ Error e t

abort' :: String -> TC def pf nb nf bound free a
abort' = abort . FromMonadFail

lookupContext :: (Ord free) => free -> TC def pf nb nf bound free (PType pf nb nf)
lookupContext f = do
  ctx <- ask
  case Map.lookup f (context ctx) of
    Nothing -> abort' "Variable not in scope"
    Just p  -> pure p

lookupConType :: Constructor -> PCoProduct pf nb nf -> TC def pf nb nf b f (PType pf nb nf)
lookupConType c mapping = case Map.lookup c mapping of
  Nothing -> abort $ NotInScope (NIS_Constructor c mapping)
  Just p  -> pure p

lookupProjType :: Projection -> NObject pf nb nf -> TC def pf nb nf bound free (NType pf nb nf)
lookupProjType p mapping = case Map.lookup p mapping of
    Nothing -> abort $ NotInScope (NIS_Projection p mapping)
    Just n -> pure n

lookupDef :: (Ord def) => def -> TC def pf nb nf bound free (NType pf nb nf)
lookupDef n = do
  ctx <- ask
  case Map.lookup n (sigType . sig $ ctx) of
    Nothing -> abort $ NotInScope (NIS_Def n)-- "Name, " <> Text.pack (show n) <> ", is not in scope"
    Just m -> pure m

updateContext :: (Ord free) => free -> PType pf nb nf -> Endo (Env def pf nb nf free)
updateContext f p env = env { context = Map.insert f p (context env)}

addTele :: (Ord free, Convert bound free) => Vector (bound, PType pf nb nf) -> Endo (Env def pf nb nf free)
addTele tele env | V.null tele = env -- for now we don't support telescopes
                 | otherwise   = env {context = context env `Map.union` tele'}
  where
    -- tele' :: Map Variable (PType bound free)
    tele' = Map.fromList $ V.toList $ fmap (\(x,p) -> (convert x,p))tele

unpackPCoProduct :: PType pf nb nf -> (TypeType pf nb nf -> ErrorType def pf nb nf b f) -> TC def pf nb nf b f (PCoProduct pf nb nf)
unpackPCoProduct (PCoProduct x) _ = pure x
unpackPCoProduct (PCon d) err = do
  -- this should continue to expand as long as it doesn't see the same data constructor
  -- but it doesn't currently
  env <- reader (pconType . sig)
  case Map.lookup d env of
    Nothing -> abort $ NotInScope (NIS_TConstructor d)
    Just (PCoProduct x) -> pure x
    Just p -> abort $ err (PositiveCon d p)
unpackPCoProduct p err = abort $ err (Positive p)

unpackPStruct :: PType pf nb nf -> (TypeType pf nb nf -> ErrorType def pf nb nf b f) -> TC def pf nb nf b f (PStruct pf nb nf)
unpackPStruct (PStruct x) _ = pure x
unpackPStruct (PCon d) err = do
  -- this should continue to expand as long as it doesn't see the same data constructor
  -- but it doesn't currently
  env <- reader (pconType . sig)
  case Map.lookup d env of
    Nothing -> abort $ NotInScope (NIS_TConstructor d)
    Just (PStruct x) -> pure x
    Just p -> abort $ err (PositiveCon d p)
unpackPStruct p err = abort $ err (Positive p)

unpackNObject :: NType pf nb nf -> (TypeType pf nb nf -> ErrorType def pf nb nf b f) -> TC def pf nb nf b f (NObject pf nb nf)
unpackNObject (NObject x) _err = pure x
unpackNObject (NCon d) err = do
  -- this should continue to expand as long as it doesn't see the same data constructor
  -- but it doesn't currently
  env <- reader (nconType . sig)
  case Map.lookup d env of
    Nothing -> abort $ NotInScope (NIS_TConstructor d)
    Just (NObject x) -> pure x
    Just n -> abort $ err (NegativeCon d n)
unpackNObject n err = abort $ err (Negative n)

unpackFunType :: NType pf nb nf -> (TypeType pf nb nf -> ErrorType def pf nb nf b f) -> TC def pf nb nf b f (PType pf nb nf, NType pf nb nf)
unpackFunType (Fun p n) _ = pure (p, n)
{-
unpackFunType (NCon d) err =  do
  env <- reader ()
-}
unpackFunType n err = abort $ err (Negative n)

unpackForallType :: NType pf nb nf -> (TypeType pf nb nf -> ErrorType def pf nb nf b f)
  -> TC def pf nb nf b f (nb, NType pf nb nf)
unpackForallType (Forall b n) _err = pure (b, n)


tcLit :: () => Literal -> PType pf nb nf -> TC defs pf nb nf bound free ()
tcLit (LInt _) (PLit TInt) = return ()
tcLit l@(LInt _) p = abort $ InferedDon'tMatchChecked (PT_Lit l) (Positive $ PLit TInt) (Positive p)
tcLit (LStr _) (PLit TString) = return ()
tcLit l@(LStr _) p = abort $ InferedDon'tMatchChecked (PT_Lit l) (Positive $ PLit TString) (Positive p)

tcVal :: (Ord free, Ord defs, Eq pf, Eq nb, Eq nf, Convert nb nf)
      => Val defs pf nb nf bound free -> PType pf nb nf -> TC defs pf nb nf bound free ()
tcVal (Var x) p = do
  p' <- lookupContext x
  unless (p == p') $ abort $ InferedDon'tMatchChecked (PT_Var x) (Positive p') (Positive p)
tcVal (Lit l) p = tcLit l p
tcVal v@(Con c a) p = do
  m <- unpackPCoProduct p (flip ShouldBeButIsA "Labeled sum" $ PT_Val v)
  p' <- lookupConType c m
  tcVal a p'
tcVal (Thunk ca) (Ptr n) = do
  n' <- tcAct ca
  unless (n == n') $ abort $ InferedDon'tMatchChecked (PT_Act ca) (Negative n') (Negative n)
tcVal v@(Thunk _) p = abort $ ShouldBeButIsA (PT_Val v) "pointer" (Positive p)
tcVal (Struct vs) (PStruct ps)
   | length vs == length ps
     = sequence_ (V.zipWith tcVal vs ps)
   |otherwise = abort $ StructArityMisMatch vs ps
tcVal v@(Struct _) p = abort $ ShouldBeButIsA (PT_Val v) "struct" (Positive p)
tcVal (ThunkVal v) (Ptr (Mon p)) = tcVal v p
tcVal v@(ThunkVal _) p = abort $ ShouldBeButIsA (PT_Val v) "pointer to monadic value" (Positive p)

tcArg :: (Ord free, Ord defs, Eq pf, Eq nb, Eq nf, Convert nb nf)
      => Arg defs pf nb nf bound free -> NType pf nb nf -> TC defs pf nb nf bound free (NType pf nb nf)
tcArg (Push v) n_orig = do
  (p, n) <- unpackFunType n_orig $ PushArgumentToNoFun v
  tcVal v p
  pure n
tcArg (Proj p) n_orig = do
  mapping <- unpackNObject n_orig $ ProjArgumentToNoObject p
  lookupProjType p mapping
tcArg (Type m) n_orig = do
  (b, n) <- unpackForallType n_orig undefined
  pure $ substNTypeOne (convert b) m n

tcArgs :: (Ord free, Ord defs, Eq pf, Eq nb, Eq nf, Convert nb nf)
       => Args defs pf nb nf bound free -> NType pf nb nf -> TC defs pf nb nf bound free (NType pf nb nf)
tcArgs = go . toList
  where
    go [] m = pure m
    go (a : as) m = do
      m' <- tcArg a m
      go as m'

tcCall :: (Ord free, Ord defs, Eq pf, Eq nb, Eq nf, Convert nb nf)
       => Call defs pf nb nf bound free -> TC defs pf nb nf bound free (NType pf nb nf)
tcCall (Apply (CDef d) xs) = do
  n <- lookupDef d
  tcArgs xs n
tcCall (Apply (CVar x) xs) = do
  p <- lookupContext x
  case p of
    Ptr n -> tcArgs xs n

  {-
tcRHS :: (Ord free, Ord defs, Show defs,Eq pf, Eq nb, Eq nf)
      => RHS defs pf nb nf bound free -> NType pf nb nf -> TC defs pf nb nf free ()
tcRHS (Return v) (Mon p) = tcVal v p
tcRHS (Call ca) n = do
  m <- tcCall ca
  unless (m == n) $ abort "Call types mismatch"
-}

tcAct :: (Ord free, Ord defs, Eq pf, Eq nb, Eq nf, Convert nb nf)
  =>Act defs pf nb nf bound free -> TC defs pf nb nf bound free (NType pf nb nf)
tcAct (Call ca) = tcCall ca
tcAct (PutStrLn x) = do
  tcVal x (PLit TString)
  return $ Mon $ PStruct V.empty
tcAct ReadLn = return $ Mon $ PLit TString

tcMonad :: (Ord free, Ord defs, Eq pf, Eq nb, Eq nf, Convert nb nf)
  => CMonad defs pf nb nf bound free -> NType pf nb nf -> TC defs pf nb nf bound free ()
tcMonad (Return r) (Mon p) = tcVal r p
tcMonad t@(Return _) n = abort $ ShouldBeButIsA (PT_Mon t) "monadic" (Negative n)
tcMonad (Act a) n = do
  n' <- tcAct a
  unless (n == n') $ abort $ InferedDon'tMatchChecked (PT_Act a) (Negative n') (Negative n)

tcTerm :: (Ord free, Convert bound free,Ord defs, Eq pf, Eq nb, Eq nf, Convert nb nf)
       => Term defs pf nb nf bound free -> NType pf nb nf -> TC defs pf nb nf bound free ()
tcTerm t@(Lam b t') n_orig = do
  (p, n) <- unpackFunType n_orig $ ShouldBeButIsA (PT_Term t) "function"
  local (addTele $ V.singleton (b,p)) $ tcTerm t' n
tcTerm t@(New bs) n_orig = do
  mapping <- unpackNObject n_orig $ ShouldBeButIsA (PT_Term t) "object"
  for_ bs $ \ (CoBranch p t') -> do
    n <- lookupProjType p mapping
    tcTerm t' n
tcTerm (Do r) n = tcMonad r n
tcTerm (Case x bs) n = do
  p_orig <- lookupContext x
  mapping <- unpackPCoProduct p_orig (flip ShouldBeButIsA "labeled sum" $ PT_Var x)
  for_ bs $ \ (Branch c t) -> do
    p <- lookupConType c mapping
    local (updateContext x p) $ tcTerm t n
tcTerm (Split x bs t') n = do
  p_orig <- lookupContext x
  struct <- unpackPStruct p_orig (flip ShouldBeButIsA "struct" $ PT_Var x)
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


tcDecl :: (Ord free , Eq pf, Eq nb, Eq nf, Convert bound free, Convert nb nf)
       => Decl pb pf nb nf bound free -> TC QName pf nb nf bound free ()
tcDecl (DDef n nt t) = local (\e -> e { nameOfTerm = n}) $ tcTerm t nt -- we should check that nt makes sense
tcDecl (DData _ _) = pure ()
tcDecl (CoData _ _) = pure ()

tcNameSpace :: (Ord free, Convert bound free, Convert nb nf, Eq pf, Eq nb, Eq nf)
            => (a -> Endo (Env QName pf nb nf free)) -> NameSpace a pb pf nb nf bound free -> TC QName pf nb nf bound free ()
tcNameSpace up (Namespace _ t tele decls)
  = local (up t)
  $ local (addTele tele)
  $ traverse_ tcDecl decls

tcProgram :: (Ord free, Convert bound free, Convert nb nf
             , Eq pf, Eq nb, Eq nf)
          => Program pb pf nb nf bound free -> TC QName pf nb nf bound free ()
tcProgram (Program ns) = tcNameSpace (const id) ns


collectDecl :: (Ord free) => Decl pb pf nb nf bound free -> Signature QName pf nb nf
collectDecl (DData n cs) = Signature (Map.singleton (TConstructor n) cs) mempty mempty
collectDecl (DDef n nt _) = Signature mempty mempty (Map.singleton n nt)
collectDecl (CoData n ty) = Signature mempty (Map.singleton (TConstructor n) ty) mempty


collectNameSpace :: (Ord free) => NameSpace a pb pf nb nf bound free -> Signature QName pf nb nf
collectNameSpace (Namespace _ _ _ decls) = foldMap collectDecl decls

collectProgram :: (Ord free) => Program pb pf nb nf bound free -> Signature QName pf nb nf
collectProgram (Program ns) = collectNameSpace ns

runTC :: (Ord free, Eq nf, Eq pf, Eq nb, Convert bound free, Convert nb nf
         , Pretty pf, Pretty nb, Pretty nf, Pretty bound, Pretty free)
      => Program pb pf nb nf bound free ->IO ()
runTC m = case runTC' (tcProgram m) (Env mempty (collectProgram m) undefined) of
  Right x -> pure x
  Left xs -> {-mapM_-} Text.putStrLn (error2Text xs) >> error "Typechecking failed"

ttText :: (Pretty pf, Pretty nb, Pretty nf) => TypeType pf nb nf -> Text
ttText (Positive p) = Pretty.pprint p
ttText (PositiveCon d p) = Pretty.pprint d <> " which expands to " <> Pretty.pprint p
ttText (Negative n) = Pretty.pprint n

ptText :: (Pretty def, Pretty pf, Pretty nb, Pretty nf, Pretty b, Pretty f)
       => ProgType def pf nb nf b f -> Text
ptText (PT_Act a) = Pretty.pprint a
ptText (PT_Term _) = "Term"
ptText (PT_Proj p) = Pretty.pprint p
ptText (PT_Val v) = Pretty.pprint v
ptText (PT_Mon m) = Pretty.pprint m
ptText (PT_Con c) = Pretty.pprint c
ptText (PT_Def d) = Pretty.pprint d
ptText (PT_Var x) = Pretty.pprint x
ptText (PT_Lit l) = Pretty.pprint l

errorType2Text :: (Pretty def, Pretty pf, Pretty nb, Pretty nf, Pretty bound, Pretty free)
  => ErrorType def pf nb nf bound free -> Text
errorType2Text (FromMonadFail s) = Text.pack s
errorType2Text (NotInScope _) = "Not in scope"
errorType2Text (StructArityMisMatch _ _) = "Struct arity mis-match"
errorType2Text (InferedDon'tMatchChecked p i c) = "Infered type don't match the checked type:\n"
  <> "For term «" <> ptText p <> "»\n"
  <> "We infered «" <> ttText i <> "» but "
  <> "one would expect «" <> ttText c <> "»\n\n"
errorType2Text (ShouldBeButIsA p desc t) = "The program is not of the correct type:\n"
  <> "We expect a term of type «" <> ttText t <> "» but "
  <> "the term «" <> ptText p <> "» builds " <> desc

error2Text :: (Pretty def, Pretty pf, Pretty nb, Pretty nf, Pretty b, Pretty f)
  => Error def pf nb nf b f -> Text
error2Text (Error env t)
  = let QName root loc = nameOfTerm env in foldr (\x y -> x `mappend`"." `mappend` y) loc root `mappend` ": " `mappend` errorType2Text t
