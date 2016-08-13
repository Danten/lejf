{-# Language MultiParamTypeClasses #-}
module Syntax.Internal where

import Data.Map (Map)
import Data.Text(Text)
import Data.Vector (Vector)

import Syntax.Common


{-
Two kind of types, NType for computations and PType for Values

Notice that Lambdas are not values by this definition

the point is that `t : Mon P'
can always be evaluated to a `Return p'

-}
data NType pf nb nf
  = Fun (PType pf nb nf) (NType pf nb nf)
    -- ^ Functions, so far not dependent
  | Forall nb (NType pf nb nf)
  | NVar nf
  | NCon TConstructor -- [NType pf nb nf]
  | Mon (PType pf nb nf)
  deriving (Show, Eq)

data TLit = TInt | TString
  deriving (Show, Eq)

type PCoProduct pf nb nf = Map Constructor (PType pf nb nf)
type PStruct pf nb nf = Vector (PType pf nb nf)

data PType pf nb nf
  = PCon TConstructor -- [NType pf nb nf]
  | PCoProduct (PCoProduct pf nb nf)
  | PStruct (PStruct pf nb nf)
  | PVar pf
  | Ptr (NType pf nb nf)
  | PLit TLit
  deriving (Show, Eq)

data CallFun defs free = CDef defs | CVar free deriving (Show)
data Call defs pf nb nf bound free = Apply (CallFun defs free) (Args defs pf nb nf bound free) deriving (Show)

-- can infer
data Act defs pf nb nf bound free
  = PutStrLn (Val defs pf nb nf bound free)
  | ReadLn
  | Call (Call defs pf nb nf bound free)
  deriving (Show)

-- must check
data CMonad defs pf nb nf bound free
  = Act (Act defs pf nb nf bound free)
  | Return (Val defs pf nb nf bound free)
  | Bind(Act defs pf nb nf bound free) bound (CMonad defs pf nb nf bound free)
  deriving (Show)

-- must check
data Term defs pf nb nf bound free
  = Do (CMonad defs pf nb nf bound free)
  | Lam bound (Term defs pf nb nf bound free)
  | TLam nb (Term defs pf nb nf bound free)
  | Case free (Vector (Branch defs pf nb nf bound free))
  | Split free (Vector bound) (Term defs pf nb nf bound free)
  | Derefence free (Term defs pf nb nf bound free)
  | New (Vector (CoBranch defs pf nb nf bound free))
  | With (Call defs pf nb nf bound free) bound (Term defs pf nb nf bound free) -- This allocates on the stack
  | Let (Val defs pf nb nf bound free) bound (Term defs pf nb nf bound free) -- This allocates on the stack
  deriving (Show)

data Branch defs pf nb nf bound free = Branch Constructor (Term defs pf nb nf bound free)
  deriving (Show)
data CoBranch defs pf nb nf bound free = CoBranch Projection (Term defs pf nb nf bound free)
  deriving (Show)

-- can infer
data Arg defs pf nb nf bound free
  = Push (Val defs pf nb nf bound free) -- maybe we want (CMonad) and auto-lift computations to closest Do-block
  -- Could have a run CMonad if it is guaranteed to be side-effect free (including free from non-termination aka it terminates)
  | Proj Projection
  | Type (NType pf nb nf)
  deriving (Show)

type Args defs pf nb nf bound free = Vector (Arg defs pf nb nf bound free)

data Literal = LInt Int | LStr Text
  deriving (Show)

-- must check
data Val defs pf nb nf bound free
  = Var free
  | Lit Literal
  | Con Constructor (Val defs pf nb nf bound free)
  | Struct (Vector (Val defs pf nb nf bound free))
  | Thunk (Act defs pf nb nf bound free) -- or be monadic code?
  | ThunkVal (Val defs pf nb nf bound free)
  deriving (Show)

class Convert a b where
  convert :: a -> b

instance Convert Binder Variable where
  convert (Binder x) = Variable x

class SubstVal a where
  substVal :: (free -> Val defs pf nb nf bound free') -> a defs pf nb nf bound free -> a defs pf nb nf bound free'

substValOne :: (Eq free, SubstVal a) => free -> Val defs pf nb nf bound free -> a defs pf nb nf bound free -> a defs pf nb nf bound free
substValOne x v = substVal $ \ y -> if x == y then v else Var y

instance SubstVal Arg where
  substVal s (Push v) = Push (substVal s v)
  substVal _ (Proj p) = Proj p -- change phantom type
  substVal _ (Type n) = Type n

instance SubstVal Act where
  substVal s (PutStrLn x) = PutStrLn $ substVal s x
  substVal _ ReadLn = ReadLn
  substVal s (Call (Apply (CDef d) as)) = Call $ Apply (CDef d) (fmap (substVal s) as)
  substVal s (Call (Apply (CVar x) as)) = case s x of
    Var y -> Call (Apply (CVar y) $ fmap (substVal s) as)
    Thunk (Call (Apply c bs)) -> Call $ Apply c $ bs `mappend` fmap (substVal s) as
    -- v | null as -> Return v
    _ -> error "Erroneous substitution"

instance SubstVal CMonad where
  substVal s (Act a) = Act $ substVal s a
  substVal s (Return p) = Return $ substVal s p
  substVal s (Bind m b k) = Bind (substVal s m) b (substVal s k)

instance SubstVal Val where
  substVal s (Var y) = s y
  substVal _ (Lit l) = Lit l
  substVal s (Con c v) = Con c (substVal s v)
  substVal s (Struct xs) = Struct (fmap (substVal s) xs)
  substVal s (Thunk r) = Thunk $ substVal s r
  substVal s (ThunkVal r) = ThunkVal $ substVal s r

class SubstNType a where
  substNType :: (nf -> NType pf nb nf') -> a pf nb nf -> a pf nb nf'

substNTypeOne :: (Eq nf, SubstNType a) => nf -> NType pf nb nf -> a pf nb nf -> a pf nb nf
substNTypeOne x v = substNType $ \ y -> if x == y then v else NVar y


instance SubstNType NType where
  substNType s (NVar x) = s x
  substNType s (Fun p n) = Fun (substNType s p) (substNType s n)
  substNType s (Forall b n) = Forall b (substNType s n) -- ?? why does this work ??
  substNType _ (NCon c) = NCon c
  substNType s (Mon p)  = Mon (substNType s p)

instance SubstNType PType where
  substNType _ (PCon c) = PCon c
  substNType _ (PLit l) = PLit l
  substNType _ (PVar x) = PVar x
  substNType s (Ptr n)  = Ptr (substNType s n)
  substNType s (PStruct c) = PStruct (fmap (substNType s) c)
  substNType s (PCoProduct c) = PCoProduct (fmap (substNType s) c)
