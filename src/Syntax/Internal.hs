{-# LANGUAGE LambdaCase #-}
module Syntax.Internal where

import           Control.Lens.Prism

import           Data.Map           (Map)
import           Data.Text          (Text)
import           Data.Vector        (Vector)

import           Syntax.Common

-- Would like to merge this with NType, but difficult to give a unifying type for Mon
-- Adding an extra type argument breaks a lot of stuff, and we then need to rethink Subst
data Kind def pf nb nf b f
  = KFun (PType def pf nb nf b f) (Kind def pf nb nf b f)
  | KForall nb (Kind def pf nb nf b f)
  | KVar nf
  | KObject (KObject def pf nb nf b f)
  | KUniverse
  deriving (Show, Eq)

type Object = Map Projection
type KObject def pf nb nf b f = Object (Kind def pf nb nf b f)
type NObject def pf nb nf b f = Object (NType def pf nb nf b f)

_Fun :: Prism' (NType d pf nb nf b f) (PType d pf nb nf b f, NType d pf nb nf b f)
_Fun = prism' (uncurry Fun) $ \case
   Fun p n -> Just (p, n)
   _ -> Nothing

_Forall :: Prism' (NType d pf nb nf b f) (nb, NType d pf nb nf b f)
_Forall = prism' (uncurry Forall) $ \case
   Forall p n -> Just (p, n)
   _ -> Nothing

_NObject :: Prism' (NType d pf nb nf b f) (NObject d pf nb nf b f)
_NObject = prism' NObject $ \case
   NObject n -> Just n
   _ -> Nothing

_NCon :: Prism' (NType d pf nb nf b f) (TConstructor, Args d pf nb nf b f)
_NCon = prism' (uncurry NCon) $ \case
  NCon d a -> Just (d, a)
  _ -> Nothing

_Mon :: Prism' (NType d pf nb nf b f) (PType d pf nb nf b f)
_Mon = prism' Mon $ \case
  Mon d -> Just d
  _ -> Nothing

data NType def pf nb nf b f
  = Fun (PType def pf nb nf b f) (NType def pf nb nf b f)
    -- ^ Functions, so far not dependent
  | Forall nb (NType def pf nb nf b f)
  | NVar nf
  | NCon TConstructor (Args def pf nb nf b f)
  | NObject (NObject def pf nb nf b f)
  | Mon (PType def pf nb nf b f)
  deriving (Show, Eq, Ord)

data TLit = TInt | TString
  deriving (Show, Eq, Ord)

type PCoProduct def pf nb nf b f = Map Constructor (PType def pf nb nf b f)
type PStruct def pf nb nf b f = Vector (PType def pf nb nf b f)

_PCon :: Prism' (PType d pf nb nf b f) (TConstructor, Args d pf nb nf b f)
_PCon = prism' (uncurry PCon) $ \case
  PCon d a -> Just (d,a)
  _ -> Nothing

_PCoProduct :: Prism' (PType d pf nb nf b f) (PCoProduct d pf nb nf b f)
_PCoProduct = prism' PCoProduct $ \case
  PCoProduct d -> Just d
  _ -> Nothing

_PStruct :: Prism' (PType d pf nb nf b f) (PStruct d pf nb nf b f)
_PStruct = prism' PStruct $ \case
  PStruct d -> Just d
  _ -> Nothing

_Ptr :: Prism' (PType d pf nb nf b f) (NType d pf nb nf b f)
_Ptr = prism' Ptr $ \case
  Ptr d -> Just d
  _ -> Nothing


data PType def pf nb nf b f
  = PCon TConstructor (Args def pf nb nf b f)
  | PCoProduct (PCoProduct def pf nb nf b f)
  | PStruct (PStruct def pf nb nf b f)
  | PVar pf
  | Ptr (NType def pf nb nf b f)
  | PLit TLit
  deriving (Show, Eq, Ord)

data CallFun defs free = CDef defs | CVar free deriving (Show, Eq, Ord)
data Call defs pf nb nf bound free = Apply (CallFun defs free) (Args defs pf nb nf bound free) deriving (Show, Eq, Ord)

-- can infer
data Act defs pf nb nf bound free
  = PutStrLn (Val defs pf nb nf bound free)
  | ReadLn
  | Call (Call defs pf nb nf bound free)
  deriving (Show, Eq, Ord)

-- must check
data CMonad defs pf nb nf bound free
  = Act (Act defs pf nb nf bound free)
  | Return (Val defs pf nb nf bound free)
  | Bind(Act defs pf nb nf bound free) bound (CMonad defs pf nb nf bound free)
  deriving (Show)

-- must check
data Term mon defs pf nb nf bound free
  = Do mon
  | Lam bound (Term mon defs pf nb nf bound free)
  | TLam nb (Term mon defs pf nb nf bound free)
  | Case free (Vector (Branch mon defs pf nb nf bound free))
  | Split free (Vector bound) (Term mon defs pf nb nf bound free)
  | Derefence free (Term mon defs pf nb nf bound free)
  | New (Vector (CoBranch mon defs pf nb nf bound free))
  | With (Call defs pf nb nf bound free) bound
         (Term mon defs pf nb nf bound free) -- This allocates on the stack
  | Let (Val defs pf nb nf bound free, PType defs pf nb nf bound free) bound
        (Term mon defs pf nb nf bound free) -- This allocates on the stack
  deriving (Show)


data Branch mon defs pf nb nf bound free = Branch Constructor (Term mon defs pf nb nf bound free)
  deriving (Show)
data CoBranch mon defs pf nb nf bound free = CoBranch Projection (Term mon defs pf nb nf bound free)
  deriving (Show)

-- can infer
data Arg defs pf nb nf bound free
  = Push (Val defs pf nb nf bound free) -- maybe we want (CMonad) and auto-lift computations to closest Do-block
  -- Could have a run CMonad if it is guaranteed to be side-effect free (including free from non-termination aka it terminates)
  | Proj Projection
  | Type (NType defs pf nb nf bound free)
  deriving (Show, Eq, Ord)

type Args defs pf nb nf bound free = Vector (Arg defs pf nb nf bound free)

data Literal = LInt Int | LStr Text
  deriving (Show, Eq, Ord)

-- must check
data Val defs pf nb nf bound free
  = Var free
  | Lit Literal
  | Con Constructor (Val defs pf nb nf bound free)
  | Struct (Vector (Val defs pf nb nf bound free))
  | Thunk (Act defs pf nb nf bound free) -- or be monadic code?
  | ThunkVal (Val defs pf nb nf bound free)
  deriving (Show, Eq, Ord)

