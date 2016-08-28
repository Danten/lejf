module Syntax.Subst where

import Syntax.Internal

class Subst a where
  subst :: (free -> Val defs pf nb nf' bound free')
        -> (nf   -> NType defs pf nb nf' bound free')
        -> a defs pf nb nf bound free
        -> a defs pf nb nf' bound free'

substVal :: Subst a => (free -> Val defs pf nb nf bound free') -> a defs pf nb nf bound free -> a defs pf nb nf bound free'
substVal f = subst f NVar

substValOne :: (Eq free, Subst a) => free -> Val defs pf nb nf bound free -> a defs pf nb nf bound free -> a defs pf nb nf bound free
substValOne x v = substVal $ \ y -> if x == y then v else Var y

substNType :: Subst a => (nf -> NType def pf nb nf' b f) -> a def pf nb nf b f -> a def pf nb nf' b f
substNType f = subst Var f

substNTypeOne :: (Eq nf, Subst a) => nf -> NType def pf nb nf b f -> a def pf nb nf b f -> a def pf nb nf b f
substNTypeOne x v = substNType $ \ y -> if x == y then v else NVar y

instance Subst Arg where
  subst sv sn (Push v) = Push (subst sv sn v)
  subst _  _  (Proj p) = Proj p -- change phantom type
  subst sv sn (Type n) = Type (subst sv sn n)

instance Subst Act where
  subst sv sn (PutStrLn x) = PutStrLn $ subst sv sn x
  subst _  _  ReadLn = ReadLn
  subst sv sn (Call (Apply (CDef d) as)) = Call $ Apply (CDef d) (fmap (subst sv sn) as)
  subst sv sn (Call (Apply (CVar x) as)) = case sv x of
    Var y -> Call (Apply (CVar y) $ fmap (subst sv sn) as)
    Thunk (Call (Apply c bs)) -> Call $ Apply c $ bs `mappend` fmap (subst sv sn) as
    -- v | null as -> Return v
    _ -> error "Erroneous substitution"

instance Subst CMonad where
  subst sv sn (Act a) = Act $ subst sv sn a
  subst sv sn (Return p) = Return $ subst sv sn p
  subst sv sn (Bind m b k) = Bind (subst sv sn m) b (subst sv sn k)

instance Subst Val where
  subst sv _n (Var y) = sv y
  subst _v _n (Lit l) = Lit l
  subst sv sn (Con c v) = Con c (subst sv sn v)
  subst sv sn (Struct xs) = Struct (fmap (subst sv sn) xs)
  subst sv sn (Thunk r) = Thunk $ subst sv sn r
  subst sv sn (ThunkVal r) = ThunkVal $ subst sv sn r

instance Subst NType where
  subst _v sn (NVar x) = sn x
  subst sv sn (Fun p n) = Fun (subst sv sn p) (subst sv sn n)
  subst sv sn (Forall b n) = Forall b (subst sv sn n) -- ?? why does this work ??
  subst sv sn (NObject o) = NObject (fmap (subst sv sn) o)
  subst sv sn (NCon c as) = NCon c $ fmap (subst sv sn) as
  subst sv sn (Mon p)  = Mon (subst sv sn p)

instance Subst PType where
  subst sv sn (PCon c a) = PCon c $ fmap (subst sv sn) a
  subst _v _n (PLit l) = PLit l
  subst _v _n (PVar x) = PVar x
  subst sv sn (Ptr n)  = Ptr (subst sv sn n)
  subst sv sn (PStruct c) = PStruct (fmap (subst sv sn) c)
  subst sv sn (PCoProduct c) = PCoProduct (fmap (subst sv sn) c)