{-# Language MultiParamTypeClasses #-}
module Syntax.Internal where

import Data.Vector (Vector)
import Syntax.Common


{-
Two kind of types, NType for computations and PType for Values

Notice that Lambdas are not values by this definition

the point is that `t : Lazy P'
can always be evaluated to a `Return p'

-}
data NType bound free
  = Fun (PType bound free) (NType bound free)
    -- ^ Functions, so far not dependent
  | Forall bound (NType bound free)
  | NVar free
  | NCon Constructor [NType bound free]
  | Lazy (PType bound free ) -- Strict version as well?
  deriving (Show)

data PType bound free
  = PCon Constructor [PType bound free]
  | PVar free
  | Ptr (NType bound free)
  deriving (Show)

-- Maybe unify these into a single type?
data CallFun defs free = CDef defs | CVar free deriving (Show)
data Call defs bound free = Apply (CallFun defs free) (Args defs bound free) deriving (Show)

data Term decls defs bound free
  = Call (Call defs bound free)
  | Force (Call defs bound free) bound (Term decls defs bound free)
  | Lam bound (Term decls defs bound free)
  | Case free (Vector (Branch decls defs bound free))
  | New (Vector (CoBranch decls defs bound free))
  | With (Val defs bound free) bound (Term decls defs bound free) -- This allocates on the stack
  | ReturnWhere decls (Val defs bound free)
  | Return (Val defs bound free) -- Similar to the Where but empty,
  deriving (Show)

data Branch decls defs bound free = Branch Constructor (Vector bound) (Term decls defs bound free)
  deriving (Show)
data CoBranch decls defs bound free = CoBranch Projection (Term decls defs bound free)
  deriving (Show)

data Arg defs bound free = Push (Val defs bound free) | Proj Projection | Type (NType bound free)
  deriving (Show)

type Args defs bound free = Vector (Arg defs bound free)

data Val defs bound free
  = Var free
  | Con Constructor (Vector (Val defs bound free))
  | Thunk (Call defs bound free)
  deriving (Show)

class Convert a b where
  convert :: a -> b

instance Convert Binder Variable where
  convert (Binder x) = Variable x

-- Should maybe be parallel substitution?
-- (free -> Val defs bound free') -> a defs bound free -> a defs bound free'
class Subst a where
  subst :: Eq free => free -> Val defs bound free -> a defs bound free -> a defs bound free

substs :: (Subst a, Eq free) => free -> Val defs bound free -> Vector (a defs bound free) -> Vector (a defs bound free)
substs x v = fmap (subst x v)

instance Subst Call where
  subst x val (Apply cf as) = Apply cf' (substs x val as)
    where
      cf' = case cf of
        CVar y | x == y -> case val of
            Var y' -> CVar y'
        _ -> cf

instance Subst Arg where
  subst x val (Push v) = Push (subst x val v)
  subst _x _val a@(Proj{}) = a
  subst _x _val a@(Type{}) = a

instance Subst Val where
  subst x val r@(Var y) | x == y = val
                        | otherwise = r
  subst x val (Con c xs) = Con c (substs x val xs)
  subst x val (Thunk c) = Thunk (subst x val c)
