module Syntax.Decl where

import           Data.Vector

import           Syntax.Common
import           Syntax.Internal

newtype Program = Program NameSpace

data NameSpace
  = Namespace QName (Vector Decl)
  deriving (Show)


-- missing import statement
data Decl
  = DData QName Kind (Term PType) -- [(Constructor, Maybe (PType pf nb nf))]
  | CoData QName Kind (Term NType)
  | DDef QName NType (Term CMonad)
  | Template NameSpace
  | Module NameSpace
  | Specialise QName {- = -} Definition (Vector PType) (Vector Val) ModuleOps
  -- | ModuleApply QName {- = -} QName (Vector (NType pf nb nf)) (Vector (Val QName pf nb nf bound free)) ModuleOps
  -- | ModuleClosure QName (Vector (bound, Val QName pf nb nf bound free, PType pf nb nf)) (Vector (Decl pb pf nb nf bound free))
  -- ^ This is the result of Specialise
  -- One can think of this as a new module (no telescope) where all terms
  -- have `With`-cuts
  -- | Open QName ModuleOps
  -- should we add something for an alias?
  deriving (Show)

-- public and private modifiers missing
data ModuleOps
  = ModuleOps Using Renaming
  deriving (Show)

type ModuleName = Maybe QName

data Using
  = Using (Vector QName)
   -- ^ Using lists only the names we want
  | Except (Vector QName)
   -- ^ Everything except these
  deriving (Show)

-- rename (f,g) means that what was called f in previous module is called g here
data Renaming = Renaming (Vector (Atom, QName)) deriving (Show)
data Atom = AtomName QName | AtomModule QName deriving (Show)

