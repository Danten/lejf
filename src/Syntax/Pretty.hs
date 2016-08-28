{-# Language OverloadedStrings #-}
module Syntax.Pretty where


import qualified Data.Map as Map
import Data.String (IsString,fromString)
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Vector as Vector
import Data.Vector (Vector)

import Syntax.Common
import Syntax.Concrete
import Syntax.Internal
import Syntax.Subst

import Utils

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


-- MAYBE REMOVE??
intersperse :: Doc -> [Doc] -> Doc
intersperse _ [] = Atom ""
intersperse _ [x] = x
intersperse sep (x : xs) = x :<> sep :<> intersperse sep xs

instance Pretty Int where
  pretty = Atom . Text.pack . show

  useParen _ = False

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
  pretty TInt = "Int"
  pretty TString = "String"

  useParen _ = False
  {-# INLINE useParen #-}

instance (Pretty d, Pretty pf, Pretty nb, Pretty nf, Pretty f) => Pretty (PType d pf nb nf b f) where
  pretty (PVar v) = pretty v
  pretty (PLit l) = pretty l
  pretty (PCon c as) = pretty c :<> args as
  pretty (PCoProduct xs) = "[" :<%> intersperse " | "  (fmap (\(c, x) -> pretty c :<%> ":" :<%> pretty x) (Map.toList xs)) :<%> "]"
  pretty (PStruct xs) = "(" :<> intersperse ", " (Vector.toList $ fmap pretty xs) :<> ")"
  pretty (Ptr n) = "Ptr" :<%> prettyParen n

  useParen (PVar{}) = False
  useParen (PLit l) = useParen l
  useParen (PCon _ as) =  not $ null as
  useParen (PCoProduct{}) = False
  useParen (PStruct{}) = False
  useParen (Ptr{}) = True
  {-# INLINE useParen #-}

instance (Pretty d, Pretty pf, Pretty nb, Pretty nf, Pretty f) => Pretty (Kind d pf nb nf b f) where
  pretty (KFun p n) = pretty p :<%> "->" :<%> pretty n
  pretty (KForall b n) = "forall" :<%> pretty b <> "." :<%> pretty n
  pretty (KObject xs) = "<" :<%> intersperse " & " (fmap (\(p, x) -> pretty p :<%> "as" :<%> pretty x) (Map.toList xs)) :<%> ">"
  pretty (KVar v) = pretty v
  pretty (KUniverse) = "Type"

  useParen (KFun _ _) = True
  useParen (KForall _ _) = True
  useParen (KObject _) = False
  useParen (KVar v) = useParen v
  useParen (KUniverse) = False
  {-# INLINE useParen #-}

instance (Pretty d, Pretty pf, Pretty nb, Pretty nf, Pretty f) => Pretty (NType d pf nb nf b f) where
  pretty (Fun p n) = pretty p :<%> "->" :<%> pretty n
  pretty (Forall b n) = "forall" :<%> pretty b <> "." :<%> pretty n
  pretty (NObject xs) = "<" :<%> intersperse " & " (fmap (\(p, x) -> pretty p :<%> "as" :<%> pretty x) (Map.toList xs)) :<%> ">"
  pretty (NCon c ns) = pretty c :<> args ns
  pretty (NVar v) = pretty v
  pretty (Mon p) = "{" :<> pretty p :<> "}"

  useParen (Fun _ _) = True
  useParen (Forall _ _) = True
  useParen (NObject _) = False
  useParen (NCon _ as) = not $ null as
  useParen (NVar v) = useParen v
  useParen (Mon _) = False
  {-# INLINE useParen #-}

instance (Pretty a, Pretty b) => Pretty (CallFun a b) where
  pretty (CDef q) = pretty q
  pretty (CVar x) = "*" :<> pretty x

  useParen (CDef q) = useParen q
  useParen (CVar x) = useParen x
  {-# INLINE useParen #-}

instance (Pretty d, Pretty pf, Pretty f, Pretty nb, Pretty nf) => Pretty (Call d pf nb nf b f) where
  pretty (Apply c as) = pretty c :<> args as

  useParen (Apply _ as) = not $ null as
  {-# INLINE useParen #-}

instance Pretty Literal where
  pretty (LInt x) = pretty x
  pretty (LStr x) = "\"" <> Atom x <> "\""

  useParen _ = False
  {-# INLINE useParen #-}

instance (Pretty f, Pretty d, Pretty pf, Pretty nb, Pretty nf) => Pretty (Val d pf nb nf b f) where
  pretty (Var x) = pretty x
  pretty (Lit l) = pretty l
  pretty (Con c xs) = pretty c :<%> prettyParen xs
  pretty (Struct xs) = "⦃" :<> intersperse ", " (Vector.toList $ fmap pretty xs) :<> "⦄"
  pretty (Thunk ct) = "Thunk{" :<> pretty ct :<> "}"
  pretty (ThunkVal ct) = "$" :<> prettyParen ct

  useParen (Var x) = useParen x
  useParen (Lit l) = useParen l
  useParen (Con _ _) = True
  useParen (Struct _) = False
  useParen (Thunk _) = False
  useParen (ThunkVal _) = False
  {-# INLINE useParen #-}

instance (Pretty d, Pretty pf, Pretty f, Pretty nb, Pretty nf) => Pretty (Arg d pf nb nf b f) where
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

instance (Pretty d, Pretty pf, Pretty nb, Pretty nf, Pretty f) => Pretty (Act d pf nb nf b f) where
  pretty (PutStrLn s) = "PutStrLn" :<%> pretty s
  pretty (Call c) = pretty c
  pretty ReadLn = "ReadLn"

  useParen (PutStrLn _) = True
  useParen (Call c) = useParen c
  useParen ReadLn = False

{-
instance (Pretty d, Pretty pf, Pretty nb, Pretty nf, Pretty f) => Pretty (RHS d pf nb nf b f) where
  pretty (Call c) = pretty c
  pretty (Return v) = pretty v
  pretty (Act a) = pretty a

  useParen (Call c) = useParen c
  useParen (Return v) = useParen v
  useParen (Act a) = useParen a
-}

data Equation mon d pf nb nf b f
  = Equation (Call d pf nb nf b f) mon -- (CMonad d pf nb nf b f)
  | EqWith (Call d pf nb nf b f) (Call d pf nb nf b f) (Vector (Equation mon d pf nb nf b f))
  | EqLet (Call d pf nb nf b f) (Val d pf nb nf b f, PType d pf nb nf b f)
          (Vector (Equation mon d pf nb nf b f))

splitLines :: Vector Doc -> Doc
splitLines xs | null xs = ""
              | length xs == 1 = Vector.head xs
              | otherwise = foldr1 (:$$) xs

equations :: (Eq f, Convert b f, Convert nb nf) => d -> Term mon d pf nb nf b f -> Vector (Equation mon d pf nb nf b f)
equations name = go Vector.empty
  where
    append xs y = xs <> Vector.singleton y
    mkCa = Apply (CDef name)
    prv = Push . Var . convert

    -- go :: (Eq f, Convert b f) => Args d pf nb nf b f -> Term d pf nb nf b f -> Vector (Equation d pf nb nf b f)
    go xs (Lam x t) = go (append xs $ prv x) t
    go xs (TLam x t) = go (append xs $ Type $ NVar $ convert x) t
    go xs (Do c) = Vector.singleton (Equation (mkCa xs) c)
    go xs (With v b t) = Vector.singleton $ EqWith (mkCa xs) v $ go (append xs $ prv b) t
    go xs (Let v b t) = Vector.singleton $ EqLet (mkCa xs) v $ go (append xs $ prv b) t
    go xs (Derefence v t) = go (fmap (substValOne v (ThunkVal $ Var $ v)) xs) t
    go xs (New bs) = bs >>= \ (CoBranch p t) -> go (append xs $ Proj p) t
    go xs (Split x bs t) = go (fmap (substValOne x (Struct $ fmap (Var . convert) bs)) xs) t
    go xs (Case x bs) = bs >>= \ (Branch c t) ->
      let xs' = fmap (substValOne x (Con c (Var x))) xs
       in go xs' t

instance (Pretty d, Pretty pf, Pretty nb, Pretty nf, Pretty b, Pretty f) => Pretty (CMonad d pf nb nf b f) where
  pretty (Act a) = pretty a
  pretty (Return r) = "return" :<%> prettyParen r
  pretty (Bind a b m) = pretty b :<%> "<-" :<%> pretty a :<> ";" :<%> pretty m

  useParen (Act a) = useParen a
  useParen (Return _) = True
  useParen (Bind _ _ _) = True

instance (Pretty mon, Pretty d,Pretty pf, Pretty nb, Pretty nf, Pretty b, Pretty f) => Pretty (Equation mon d pf nb nf b f) where
  pretty (Equation c r) = pretty c :<%> "=" :<%> pretty r
  pretty (EqWith ca r eqs) = Group 2 $ pretty ca :<%> "with" :<%> pretty r :$$ splitLines (fmap pretty eqs)
  pretty (EqLet ca (v,p) eqs) = Group 2 $ pretty ca :<%> "let"
    :<%> pretty v :<%> ":" :<%> pretty p
    :$$ splitLines (fmap pretty eqs)

  useParen _ = True

instance Pretty Using where
  pretty (Using vs) = "using" :<%> "(" :<> args vs :<> ")"
  pretty (Except vs) | null vs   = ""
                     | otherwise = "hiding" :<%> "(" :<> args vs :<> ")"

  useParen _ = True

instance Pretty Atom where
  pretty (AtomName n) = pretty n
  pretty (AtomModule n) = "module" :<%> pretty n

  useParen (AtomName n) = useParen n
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

instance (Pretty nb, Pretty pf, Pretty nf, Pretty pb, Eq f, Convert b f, Pretty b,Pretty f, Convert nb nf)
  => Pretty (Decl pb pf nb nf b f) where
  pretty (DData name ki ty) = Group 2 $ "data" :<%> pretty name :<%> ":" :<%> pretty ki :$$
    pretty (equations name ty)
  pretty (CoData name ki ty) = Group 2 $ "codata" :<%> pretty name :<%> ":" :<%> pretty ki :$$
    pretty (equations name ty)
  pretty (Module ns) = prettyNs "module" args ns
  pretty (Template ns) = prettyNs "template" args ns
  pretty (Specialise name temp tybinds _tele ren) =
    "module" :<%> pretty name :<%> pretty temp :<> args tybinds :<%%> pretty ren
  pretty (DDef name typ ter) =
    pretty name :<%> ":" :<%> pretty typ :$$
      pretty (equations name ter)

  useParen _ = True
  {-# INLINE useParen #-}

prettyNs :: (Eq f, Convert b f, Convert nb nf, Pretty b, Pretty f, Pretty pb, Pretty pf, Pretty nb, Pretty nf) => Text -> (tybinds -> Doc) -> PrettyT (NameSpace tybinds pb pf nb nf b f)
prettyNs modu pArgs (Namespace name tybinds _telescope decls) = Group 2 $
    Atom modu :<%> pretty name :<> pArgs tybinds :<%> "where" :$$
      pretty decls

instance (Eq f, Convert b f, Pretty b, Pretty f, Pretty pb, Pretty pf, Pretty nb, Pretty nf, Convert nb nf) => Pretty (Program pb pf nb nf b f) where
  pretty (Program ns) = prettyNs "module" (\ () -> "") ns

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
