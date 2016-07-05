module Syntax.Concrete where

import Data.Vector
import Data.Text

newtype Program = Program NoTNameSpace

newtype Variable = Variable Text deriving (Eq,Ord,Show)
newtype Binder = Binder Text deriving (Show)
newtype Constructor = Constructor QName deriving (Eq,Ord, Show)
newtype Projection = Projection QName deriving (Show)

data QName = QName [Text] Text deriving (Eq, Ord, Show)


type TypNameSpace = NameSpace (Vector Binder)
type NoTNameSpace = NameSpace ()

data NameSpace tybinds
  = Namespace QName tybinds (Vector (Binder, PType)) (Vector Decl)
  deriving (Show)

data WhereClause = WhereClause (Maybe QName) (Vector Decl)
  deriving (Show)

-- missing import statement
data Decl
  = DData QName [Variable] [(Constructor, [PType])]
  | CoData QName [Variable] [(Projection, NType)]
  | DDef QName NType (Term WhereClause)
  | Template TypNameSpace
  | Module TypNameSpace
  | Specialise QName {- = -} QName (Vector PType) (Vector Val) ModuleOps
  | ModuleApply QName {- = -} QName (Vector NType) (Vector Val) ModuleOps
  | ModuleClosure QName (Vector (Binder, Val, PType)) (Vector Decl)
  -- ^ This is the result of Specialise
  -- One can think of this as a new module (no telescope) where all terms
  -- have `With`-cuts
  | Open QName ModuleOps
  -- should we add something for an alias?
  deriving (Show)

-- public and private modifiers missing
data ModuleOps
  = ModuleOps Using Renaming ModuleName
  deriving (Show)

type ModuleName = Maybe QName

data Using
  = Using (Vector QName)
   -- ^ Using lists only the names we want
  | Except (Vector QName)
   -- ^ Everything except these
  | All
   -- ^ Everything, could be Except []
  deriving (Show)

-- rename (f,g) means that what was called f in previous module is called g here
data Renaming = Renaming (Vector (Atom, QName)) deriving (Show)
data Atom = AtomName QName | AtomModule QName deriving (Show)

{-
Two kind of types, NType for computations and PType for Values

Notice that Lambdas are not values by this definition

the point is that `t : Lazy P'
can always be evaluated to a `Return p'

-}

data NType
  = Fun PType NType
    -- ^ Functions, so far not dependent
  | Forall Binder NType
  | NVar Variable
  | Lazy PType -- Strict version as well?
  deriving (Show)

data PType
  = PCon Constructor [PType]
  | PVar Variable
  | Ptr NType
  deriving (Show)

-- Maybe unify these into a single type?
data CallFun = CDef QName | CVar Variable deriving (Show)
data Call = Apply CallFun Args deriving (Show)

data Term decl
  = Call Call
  | Force Call Binder (Term decl)
  | Lam Binder (Term decl)
  | Case Variable (Vector (Branch decl))
  | New (Vector (CoBranch decl))
  | With Val Binder (Term decl) -- This allocates on the stack
  | ReturnWhere decl Val
  | Return Val -- Similar to the Where but empty,
  deriving (Show)

data Branch decl = Branch Constructor (Vector Binder) (Term decl)
  deriving (Show)
data CoBranch decl = CoBranch Projection (Term decl)
  deriving (Show)

data Arg = Push Val | Proj Projection | Type NType
  deriving (Show)

type Args = Vector Arg

data Val
  = Var Variable
  | Con Constructor (Vector Val)
  | Thunk Call -- lazy, but maybe could be strict?
  deriving (Show)

class Subst a where
  subst :: Variable -> Val -> a -> a

instance Subst a => Subst (Vector a) where
  subst x val = fmap (subst x val)

instance Subst Call where
  subst x val (Apply cf as) = Apply cf' (subst x val as)
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
  subst x val (Con c xs) = Con c (subst x val xs)
  subst x val (Thunk c) = Thunk (subst x val c)
