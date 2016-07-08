{-# Language OverloadedStrings #-}
module Syntax.Pretty where

import qualified Data.Vector as Vector
import Data.Vector (Vector)

import qualified Data.Text as Text
import Data.Text (Text)
import Data.String (IsString,fromString)

import Syntax.Concrete
import Syntax.Internal
import Syntax.Common

(<>) :: Monoid m => m -> m -> m
(<>) = mappend

data Doc = Atom Text | Group Int Doc | Doc :$$ Doc
         | Doc :<%> Doc | Doc :<> Doc

instance IsString Doc where
  fromString = Atom . fromString

instance Monoid Doc where
  mempty = ""
  mappend = (:<>)

class Pretty a where
  pretty :: a -> Doc

  useParen :: a -> Bool

prettyParen :: Pretty a => a -> Doc
prettyParen x | useParen x = "(" <> pretty x <> ")"
              | otherwise  = pretty x

prettyMany :: Pretty a => Doc -> [a] -> Doc
prettyMany _ [] = Atom ""
prettyMany _ [x] = pretty x
prettyMany sep (x : xs) = pretty x :<> sep :<> prettyMany sep xs

instance Pretty QName where
  pretty (QName xs name) = name' -- foldr (\x rs -> Atom x :<> "." :<> rs) name' xs
    where name' = Atom name
  useParen _ = False
  {-# INLINE useParen #-}

instance Pretty Variable where
  pretty (Variable x) = Atom x
  useParen _ = False
  {-# INLINE useParen #-}

instance Pretty Binder where
  pretty (Binder x) = Atom x
  useParen _ = False
  {-# INLINE useParen #-}

instance Pretty Constructor where
  pretty (Constructor x) = pretty x
  useParen _ = False
  {-# INLINE useParen #-}

instance Pretty Projection where
  pretty (Projection p) = pretty p
  useParen _ = False
  {-# INLINE useParen #-}

instance Pretty a => Pretty (Vector a) where
  pretty = foldr (:$$) "" . fmap pretty
  useParen x = Vector.length x > 1
  {-# INLINE useParen #-}

instance (Pretty a, Pretty b) => Pretty (PType a b) where
  pretty (PVar v) = pretty v
  pretty (PCon c as) = pretty c :<> args as
  pretty (Ptr n) = "Ptr" :<%> prettyParen n

  useParen (PVar _) = False
  useParen (PCon _ as) = not $ null as
  useParen (Ptr _) = True
  {-# INLINE useParen #-}

instance (Pretty a, Pretty b) => Pretty (NType a b) where
  pretty (Fun p n) = pretty p :<%> "->" :<%> pretty n
  pretty (Forall b n) = "forall" :<%> pretty b <> "." :<%> pretty n
  pretty (NCon c ns) = pretty c :<> args ns
  pretty (NVar v) = pretty v
  pretty (Lazy p) = "Lazy" :<%> prettyParen p

  useParen (NVar v) = useParen v
  useParen (NCon _ as) = not $ null as
  useParen (Fun _ _) = True
  useParen (Forall _ _) = True
  useParen (Lazy _) = True
  {-# INLINE useParen #-}

instance (Pretty a, Pretty b) => Pretty (CallFun a b) where
  pretty (CDef q) = pretty q
  pretty (CVar x) = pretty x

  useParen (CDef q) = useParen q
  useParen (CVar x) = useParen x
  {-# INLINE useParen #-}

instance (Pretty a,Pretty b, Pretty c) => Pretty (Call a b c) where
  pretty (Apply c as) = pretty c :<> args as

  useParen (Apply _ as) = not $ null as
  {-# INLINE useParen #-}

instance (Pretty a, Pretty b, Pretty c) => Pretty (Val a b c) where
  pretty (Var x) = pretty x
  pretty (Con c xs) = pretty c :<> args xs
  pretty (Thunk ct) = "Thunk{" :<> pretty ct :<> "}"

  useParen (Var x) = useParen x
  useParen (Con _ xs) = not $ null xs
  useParen (Thunk _) = False
  {-# INLINE useParen #-}

instance (Pretty a, Pretty b, Pretty c) => Pretty (Arg a b c) where
  pretty (Push x) = pretty x
  pretty (Proj p) = "." :<> pretty p
  pretty (Type n) = "#" :<> prettyParen n

  useParen (Push x) = useParen x
  useParen (Proj p) = useParen p
  useParen (Type n) = useParen n
  {-# INLINE useParen #-}

instance (Pretty a, Pretty b, Convert a b, Eq b) => Pretty (WhereClause a b) where
  pretty (WhereClause _name decls) = "where" :$$ pretty decls

  useParen _ = True -- ever used?
  {-# INLINE useParen #-}

-- we should have a way of only putting parentheses on things that need it
args :: (Traversable t, Pretty a) => t a -> Doc
args = foldr (\a as -> " " :<> prettyParen a :<> as) ""

-- Args contains no thunks, the thunks could potentially be dot-patterns
equations :: (Pretty n, Pretty d, Pretty b, Pretty f, Convert b f, Eq f) => QName -> Args n b f -> Term d n b f -> Doc
equations name = go
  where

  lhs xs = pretty name :<> args xs

  go xs (Lam x t) = go (xs <> Vector.singleton (Push . Var $ convert x)) t
  go xs (Call ca) = lhs xs :<%> "=" :<%> pretty ca
  go xs (Return p) = lhs xs :<%> "=" :<%> pretty p
  go xs (ReturnWhere decls p) = Group 2 $ lhs xs :<%> "=" :<%> Group (-2) (pretty p)
    :$$ Group 2 (pretty decls)
  go xs (Force ca b t) = Group 2 $ lhs xs :<%> "with!" :<%> pretty ca :$$
    go (xs <> Vector.singleton (Push . Var $ convert b)) t
  go xs (With v b t) = Group 2 $ lhs xs :<%> "with" :<%> pretty v :$$
    go (xs <> Vector.singleton (Push . Var $ convert b)) t
  go xs (New bs) = foldr (:$$) "" $ fmap cont bs
    where
      cont (CoBranch p t) = go (xs <> Vector.singleton (Proj p)) t
  go xs (Case x bs) = foldr (:$$) ""
    $ fmap cont bs
    where
      cont (Branch c bs' t) = go xs' t
        where xs' = substs x (Con c $ fmap (Var . convert) bs') xs
  -- b2c (Binder x) = Var $ Variable x


instance (Pretty a, Pretty b, Convert a b, Eq b) => Pretty (Decl a b) where
  pretty (DData name vars consts) = Group 2 $
    "data" :<%> pretty name :<%>
       (if null vars
          then "where"
          else prettyMany "," vars :<%> "where"
       ) :$$
       foldr (:$$) ""
         [ if null ps
             then pretty c
             else pretty c :<%> "of" :<%> prettyMany ", " ps
         | (c, ps) <- consts]
  pretty (CoData name vars projs) = Group 2 $
    "codata" :<%> pretty name :<%>
     (if null vars
         then "where"
         else prettyMany "," vars :<%> "where"
     ) :$$
     foldr (:$$) ""
       [ pretty p :<%> "is" :<%> pretty nt
       | (p, nt) <- projs]
  pretty (Template (Namespace name vars tele decls)) = Group 2 $
    "template" :<%> pretty name :<%> args vars :<%> "where" :$$
     pretty decls
  pretty (DDef name typ ter) =
    pretty name :<%> ":" :<%> pretty typ :$$
    equations name Vector.empty ter

  useParen _ = True
  {-# INLINE useParen #-}

instance (Pretty a, Pretty b, Convert a b, Eq b) => Pretty (Program a b) where
  pretty (Program (Namespace name _ _telescope decls)) = Group 2 $
    "module" :<%> pretty name :<%> "where" :$$
      pretty decls

  useParen _ = True
  {-# INLINE useParen #-}

toText :: Int -> Doc -> Text
toText _ (Atom t) = t
toText i (Group i' d) = toText (i + i') d
toText i (d :$$ d') = toText i d <> "\n" <> Text.replicate i " " <> toText i d'
toText i (d :<%> d') = toText i d <> " " <> toText i d'
toText i (d :<> d') = toText i d <> toText i d'

pprint :: Pretty a => a -> Text
pprint = toText 0 . pretty
