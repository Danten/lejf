{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}
module Syntax.Internal where

import           Control.Lens.Prism

import           Data.Map           (Map)
import           Data.Text          (Text)
import           Data.Vector        (Vector)

import           Syntax.Common

-- Would like to merge this with NType, but difficult to give a unifying type for Mon
-- Adding an extra type argument breaks a lot of stuff, and we then need to rethink Subst
data Kind
  = KFun PType Kind
  | KForall NTBinder Kind
  | KVar NTVariable
  | KObject KObject
  | KUniverse
  deriving (Show, Eq)

type Object = Map Projection
type KObject = Object Kind
type NObject = Object NType

_Fun :: Prism' NType (PType, NType)
_Fun = prism' (uncurry Fun) $ \case
   Fun p n -> Just (p, n)
   _ -> Nothing

_Forall :: Prism' NType (NTBinder, NType)
_Forall = prism' (uncurry Forall) $ \case
   Forall p n -> Just (p, n)
   _ -> Nothing

_NObject :: Prism' NType NObject
_NObject = prism' NObject $ \case
   NObject n -> Just n
   _ -> Nothing

_NCon :: Prism' NType (TConstructor, Args)
_NCon = prism' (uncurry NCon) $ \case
  NCon d a -> Just (d, a)
  _ -> Nothing

_Mon :: Prism' NType PType
_Mon = prism' Mon $ \case
  Mon d -> Just d
  _ -> Nothing

data NType
  = Fun PType NType
    -- ^ Functions, so far not dependent
  | Forall NTBinder NType
  | NVar NTVariable
  | NCon TConstructor Args
  | NObject NObject
  | Mon PType
  deriving (Show, Eq, Ord)

data TLit = TInt | TString
  deriving (Show, Eq, Ord)

type PCoProduct = Map Constructor PType
type PStruct = Vector PType

_PCon :: Prism' PType (TConstructor, Args)
_PCon = prism' (uncurry PCon) $ \case
  PCon d a -> Just (d,a)
  _ -> Nothing

_PCoProduct :: Prism' PType PCoProduct
_PCoProduct = prism' PCoProduct $ \case
  PCoProduct d -> Just d
  _ -> Nothing

_PStruct :: Prism' PType PStruct
_PStruct = prism' PStruct $ \case
  PStruct d -> Just d
  _ -> Nothing

_Ptr :: Prism' PType NType
_Ptr = prism' Ptr $ \case
  Ptr d -> Just d
  _ -> Nothing


data PType
  = PCon TConstructor Args
  | PCoProduct PCoProduct
  | PStruct PStruct
  | PVar PTVariable
  | Ptr NType
  | PLit TLit
  deriving (Show, Eq, Ord)


data CallFun = CDef Definition | CVar Variable deriving (Show, Eq, Ord)
data Call = Apply CallFun Args deriving (Show, Eq, Ord)

type TailCall = Call -- further checks should be done

-- can infer
data Act
  = PutStrLn Val
  | ReadLn
  | Malloc PType Val
  deriving (Show, Eq, Ord)

-- must check
data CMonad
  = Act Act
  | TCall TailCall
  | Return Val
  | CLeftTerm (LeftTerm CMonad)
  | Bind Act Binder CMonad
  | With Call Binder CMonad -- This allocates on the stack
  deriving (Show)

-- must check
data Term mon
  = Do mon
  | RightTerm (RightTerm (Term mon))
  | LeftTerm (LeftTerm (Term mon))
 -- Explicit substitution, not sure yet I want this
 -- | Let (ValSimple (ActSimple (CallSimple defs (Args nty defs free) free) free) free, PType defs pf nb nf bound free) bound
 --      (Term mon defs pf nb nf bound free) -- This allocates on the stack
  deriving (Show)

-- introduction for negatives,
-- (maybe it should have the CDef cut here)
data RightTerm cont
  = Lam Binder cont
  | TLam NTBinder cont
  | New (Vector (CoBranch cont))
  deriving (Show)

pattern Lam' :: Binder -> Term mon -> Term mon
pattern Lam' b t = RightTerm (Lam b t)

pattern TLam' :: NTBinder -> Term mon -> Term mon
pattern TLam' b t = RightTerm (TLam b t)

pattern New' :: Vector (CoBranch (Term mon)) -> Term mon
pattern New' bs = RightTerm (New bs)

-- elimination for positives + Cuts
--(maybe it should just have CVar -calls)
data LeftTerm cont
  = Case Variable (Vector (Branch cont))
  | Split Variable (Vector Binder) cont
  | Derefence Variable cont
  deriving (Show)

pattern Case' :: Variable -> (Vector (Branch (Term mon))) -> Term mon
pattern Case' v bs = LeftTerm (Case v bs)

pattern Split' :: Variable -> Vector Binder -> Term mon -> Term mon
pattern Split' v bs t = LeftTerm (Split v bs t)

pattern Derefence' :: Variable -> Term mon -> Term mon
pattern Derefence' v t = LeftTerm (Derefence v t)

data Branch cont = Branch Constructor cont
  deriving (Show)
data CoBranch cont = CoBranch Projection cont
  deriving (Show)

-- can infer
data Arg
  = Push Val -- maybe we want (CMonad) and auto-lift computations to closest Do-block
  -- Could have a run CMonad if it is guaranteed to be side-effect free (including free from non-termination aka it terminates)
  | Proj Projection
  | Type NType
  deriving (Show, Eq, Ord)

-- type Arg defs pf nb nf bound free = ArgSimple

type Args = Vector Arg

data Literal = LInt Int | LStr Text
  deriving (Show, Eq, Ord)

-- must check
data Val
  = Var Variable
  | Lit Literal
  | Con Constructor Val
  | Struct (Vector Val)
  | Thunk Call -- or be monadic code?
  | ThunkVal Val
  deriving (Show, Eq, Ord)
