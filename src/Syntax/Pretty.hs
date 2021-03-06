{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
module Syntax.Pretty where


import qualified Data.Map        as Map
import           Data.String     (IsString, fromString)
import           Data.Text       (Text)
import qualified Data.Text       as Text
import           Data.Vector     (Vector)
import qualified Data.Vector     as Vector

import           Syntax.Common
import           Syntax.Decl
import           Syntax.Internal
import           Syntax.Subst

import           Utils

data Doc = Atom Text | Group Int Doc | Doc :$$ Doc
         | Doc :<%> Doc | Doc :<%%> Doc | Doc :<> Doc

instance IsString Doc where
  fromString = Atom . fromString

instance Monoid Doc where
  mempty = ""
  mappend = (:<>)

type PrettyT a = a -> Doc
class Pretty a where
  pretty :: PrettyT a

  useParen :: a -> Bool

prettyParen :: Pretty a => a -> Doc
prettyParen x | useParen x = "(" <> pretty x <> ")"
              | otherwise  = pretty x

intersperse :: Doc -> [Doc] -> Doc
intersperse _ []         = Atom ""
intersperse _ [x]        = x
intersperse sep (x : xs) = x :<> sep :<> intersperse sep xs

instance Pretty Int where
  pretty = Atom . Text.pack . show

  useParen _ = False

instance Pretty QName where
  pretty (QName _xs name) = name' -- foldr (\x rs -> Atom x :<> "." :<> rs) name' xs
    where name' = Atom name
  useParen _ = False
  {-# INLINE useParen #-}

instance Pretty Definition where
  pretty (Definition x) = pretty x
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

instance Pretty NTVariable where
  pretty (NTVariable x) = Atom x
  useParen _ = False
  {-# INLINE useParen #-}

instance Pretty NTBinder where
  pretty (NTBinder x) = Atom x
  useParen _ = False
  {-# INLINE useParen #-}

instance Pretty PTVariable where
  pretty (PTVariable x) = Atom x
  useParen _ = False
  {-# INLINE useParen #-}

instance Pretty Constructor where
  pretty (Constructor x) = pretty x
  useParen _ = False
  {-# INLINE useParen #-}

instance Pretty TConstructor where
  pretty (TConstructor x) = pretty x
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

instance Pretty TLit where
  pretty TInt    = "Int"
  pretty TString = "String"

  useParen _ = False
  {-# INLINE useParen #-}

instance Pretty PType where
  pretty (PVar v) = pretty v
  pretty (PLit l) = pretty l
  pretty (PCon c as) = pretty c :<> args as
  pretty (PCoProduct xs) = "[" :<%> intersperse " | "  (fmap (\(c, x) -> pretty c :<%> ":" :<%> pretty x) (Map.toList xs)) :<%> "]"
  pretty (PStruct xs) = "(" :<> intersperse ", " (Vector.toList $ fmap pretty xs) :<> ")"
  pretty (Ptr n) = "Ptr" :<%> prettyParen n

  useParen (PVar{})       = False
  useParen (PLit l)       = useParen l
  useParen (PCon _ as)    =  not $ null as
  useParen (PCoProduct{}) = False
  useParen (PStruct{})    = False
  useParen (Ptr{})        = True
  {-# INLINE useParen #-}

instance Pretty Kind where
  pretty (KFun p n) = pretty p :<%> "→" :<%> pretty n
  pretty (KForall b n) = "forall" :<%> pretty b <> "." :<%> pretty n
  pretty (KObject xs) = "<" :<%> intersperse " & " (fmap (\(p, x) -> pretty p :<%> "as" :<%> pretty x) (Map.toList xs)) :<%> ">"
  pretty (KVar v) = pretty v
  pretty (KUniverse) = "Type"

  useParen (KFun _ _)    = True
  useParen (KForall _ _) = True
  useParen (KObject _)   = False
  useParen (KVar v)      = useParen v
  useParen (KUniverse)   = False
  {-# INLINE useParen #-}

instance Pretty NType where
  pretty (Fun p n) = pretty p :<%> "→" :<%> pretty n
  pretty (Forall b n) = "forall" :<%> pretty b <> "." :<%> pretty n
  pretty (NObject xs) = "<" :<%> intersperse " & " (fmap (\(p, x) -> pretty p :<%> "as" :<%> pretty x) (Map.toList xs)) :<%> ">"
  pretty (NCon c ns) = pretty c :<> args ns
  pretty (NVar v) = pretty v
  pretty (Mon p) = "{" :<> pretty p :<> "}"

  useParen (Fun _ _)    = True
  useParen (Forall _ _) = True
  useParen (NObject _)  = False
  useParen (NCon _ as)  = not $ null as
  useParen (NVar v)     = useParen v
  useParen (Mon _)      = False
  {-# INLINE useParen #-}

instance Pretty CallFun where
  pretty (CDef q) = pretty q
  pretty (CVar x) = "*" :<> pretty x

  useParen (CDef q) = useParen q
  useParen (CVar x) = useParen x
  {-# INLINE useParen #-}

instance Pretty Call where
  pretty (Apply c as) = pretty c :<> args as

  useParen (Apply _ as) = not $ null as
  {-# INLINE useParen #-}

instance Pretty Literal where
  pretty (LInt x) = pretty x
  pretty (LStr x) = "\"" <> Atom x <> "\""

  useParen _ = False
  {-# INLINE useParen #-}

instance Pretty Val where
  pretty (Var x) = pretty x
  pretty (Lit l) = pretty l
  pretty (Con c xs) = pretty c :<%> prettyParen xs
  pretty (Struct xs) = "⦃" :<> intersperse ", " (Vector.toList $ fmap pretty xs) :<> "⦄"
  pretty (Thunk ct) = "Thunk{" :<> pretty ct :<> "}"
  pretty (ThunkVal ct) = "$" :<> prettyParen ct

  useParen (Var x)      = useParen x
  useParen (Lit l)      = useParen l
  useParen (Con _ _)    = True
  useParen (Struct _)   = False
  useParen (Thunk _)    = False
  useParen (ThunkVal _) = False
  {-# INLINE useParen #-}

instance Pretty Arg where
  pretty (Push x) = pretty x
  pretty (Proj p) = "." :<> prettyParen p
  pretty (Type n) = "#" :<> prettyParen n

  useParen (Push x) = useParen x
  useParen (Proj p) = useParen p
  useParen (Type n) = useParen n
  {-# INLINE useParen #-}

{-
instance (Pretty nb, Pretty pf, Pretty nf, Pretty pb, Eq f, Convert b f,Pretty f) => Pretty (WhereClause pb pf nb nf b f) where
  pretty (WhereClause _name decls) = "where" :$$ pretty decls

  useParen _ = True -- ever used?
  {-# INLINE useParen #-}
-}

-- we should have a way of only putting parentheses on things that need it
args :: (Traversable t, Pretty a) => t a -> Doc
args = foldr (\a as -> " " :<> prettyParen a :<> as) ""

instance Pretty Act where
  pretty (PutStrLn s) = "PutStrLn" :<%> pretty s
  pretty ReadLn       = "ReadLn"

  useParen (PutStrLn _) = True
  useParen ReadLn       = False

{-
instance (Pretty d, Pretty pf, Pretty nb, Pretty nf, Pretty f) => Pretty (RHS d pf nb nf b f) where
  pretty (Call c) = pretty c
  pretty (Return v) = pretty v
  pretty (Act a) = pretty a

  useParen (Call c) = useParen c
  useParen (Return v) = useParen v
  useParen (Act a) = useParen a
-}

data Equation mon
  = Equation Call mon -- (CMonad d pf nb nf b f)

splitLines :: Vector Doc -> Doc
splitLines xs | null xs = ""
              | length xs == 1 = Vector.head xs
              | otherwise = foldr1 (:$$) xs

equations :: Definition -> Term mon -> Vector (Equation mon)
equations name = go Vector.empty
  where
    append xs y = xs <> Vector.singleton y
    mkCa = Apply (CDef name)
    prv = Push . Var . convert

    -- goL xs (With v b t) = Vector.singleton $ EqWith (mkCa xs) v $ go (append xs $ prv b) t
    goL xs (Derefence v t) = go (fmap (substValOne v (ThunkVal $ Var $ v)) xs) t
    goL xs (Split x bs t) = go (fmap (substValOne x (Struct $ fmap (Var . convert) bs)) xs) t
    goL xs (Case x bs) = bs >>= \ (Branch c t) ->
      let xs' = fmap (substValOne x (Con c (Var x))) xs
       in go xs' t

    goR xs (Lam x t) = go (append xs $ prv x) t
    goR xs (TLam x t) = go (append xs $ Type $ NVar $ convert x) t
    goR xs (New bs) = bs >>= \ (CoBranch p t) -> go (append xs $ Proj p) t

    -- go :: (Eq f, Convert b f) => Args d pf nb nf b f -> Term d pf nb nf b f -> Vector (Equation d pf nb nf b f)
    go xs (RightTerm t) = goR xs t
    go xs (LeftTerm t) = goL xs t
    go xs (Do c) = Vector.singleton (Equation (mkCa xs) c)

instance Pretty CMonad where
  pretty (Act a)      = pretty a
  pretty (TCall c)    = pretty c
  pretty (Return r)   = "return" :<%> prettyParen r
  pretty (Bind a b m) = pretty b :<%> "<-" :<%> pretty a :<> ";" :<%> pretty m
  pretty (With c b m) = pretty b :<%> ":=" :<%> pretty c :<> ";" :<%> pretty m

  useParen (Act a)       = useParen a
  useParen (TCall c)     = useParen c
  useParen (Return _)    = True
  useParen (Bind _ _ _)  = True
  useParen (With{})      = True
  useParen (CLeftTerm{}) = True

instance (Pretty mon) => Pretty (Equation mon) where
  pretty (Equation c r) = pretty c :<%> "= do {" :<%>  pretty r :<%> "}"
  {-
  pretty (EqLet ca (v,p) eqs) = Group 2 $ pretty ca :<%> "let"
    :<%> pretty v :<%> ":" :<%> pretty p
    :$$ splitLines (fmap pretty eqs)
-}

  useParen _ = True

instance Pretty Using where
  pretty (Using vs) = "using" :<%> "(" :<> args vs :<> ")"
  pretty (Except vs) | null vs   = ""
                     | otherwise = "hiding" :<%> "(" :<> args vs :<> ")"

  useParen _ = True

instance Pretty Atom where
  pretty (AtomName n)   = pretty n
  pretty (AtomModule n) = "module" :<%> pretty n

  useParen (AtomName n)   = useParen n
  useParen (AtomModule _) = True

instance Pretty Renaming where
  pretty (Renaming xs)
    | null xs   = ""
    | otherwise = "renaming" :<%>
        "(" :<> foldr (\ a r -> " " :<> inner a :<> r) "" xs :<> ")"
    where
      inner (atm , n) = pretty atm :<%> "to" :<%> pretty n :<> ";"

  useParen _ = True

instance Pretty ModuleOps where
  pretty (ModuleOps use ren) = pretty use :<%%> pretty ren

  useParen _ = True

instance Pretty Decl where
  pretty (DData name ki ty) = Group 2 $ "data" :<%> pretty name :<%> ":" :<%> pretty ki :$$
    pretty (equations (Definition name) ty)
  pretty (CoData name ki ty) = Group 2 $ "codata" :<%> pretty name :<%> ":" :<%> pretty ki :$$
    pretty (equations (Definition name) ty)
  pretty (Module ns) = prettyNs "module" "" ns
  pretty (Template ns) = prettyNs "template" "" ns
  pretty (Specialise name temp tybinds _tele ren) =
    "module" :<%> pretty name :<%> pretty temp :<> args tybinds :<%%> pretty ren
  pretty (DDef name typ ter) =
    pretty name :<%> ":" :<%> pretty typ :$$
      pretty (equations (Definition name) ter)

  useParen _ = True
  {-# INLINE useParen #-}

prettyNs :: Text -> Doc -> PrettyT NameSpace
prettyNs modu pArgs (Namespace name decls) = Group 2 $
    Atom modu :<%> pretty name :<> pArgs :<%> "where" :$$
      pretty decls

instance Pretty Program where
  pretty (Program ns) = prettyNs "module" "" ns

  useParen _ = True
  {-# INLINE useParen #-}

toText :: Int -> Doc -> Text
toText _ (Atom t) = t
toText i (Group i' d) = toText (i + i') d
toText i (d :$$ d') = toText i d <> "\n" <> Text.replicate i " " <> toText i d'
toText i (d :<%> d') = toText i d <> " " <> toText i d'
toText i (d :<%%> d') = let pre = toText i d
                            pos = toText i d'
  in if " " `Text.isSuffixOf` pre
     then pre <> pos
     else pre <> " " <> pos
toText i (d :<> d') = toText i d <> toText i d'

pprint :: Pretty a => a -> Text
pprint = toText 0 . pretty
