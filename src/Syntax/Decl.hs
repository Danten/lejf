module Syntax.Decl where

import Data.Vector

import Syntax.Common
import Syntax.Internal

newtype Program pb pf nb nf bound free = Program (NameSpace () pb pf nb nf bound free)

data NameSpace tybinds pb pf nb nf bound free
  = Namespace QName tybinds (Vector (bound, PType QName pf nb nf bound free)) (Vector (Decl pb pf nb nf bound free))
  deriving (Show)

-- Currently not used
data WhereClause pb pf nb nf bound free = WhereClause (Maybe QName) (Vector (Decl pb pf nb nf bound free))
  deriving (Show)

-- missing import statement
data Decl pb pf nb nf bound free
  = DData QName (Kind QName pf nb nf bound free) (Term (PType QName pf nb nf bound free) QName pf nb nf bound free) -- [(Constructor, Maybe (PType pf nb nf))]
  | CoData QName (Kind QName pf nb nf bound free) (Term (NType QName pf nb nf bound free) QName pf nb nf bound free)
  | DDef QName (NType QName pf nb nf bound free) (Term (CMonad QName pf nb nf bound free) QName pf nb nf bound free)
  | Template (NameSpace (Vector pb) pb pf nb nf bound free)
  | Module (NameSpace (Vector nb) pb pf nb nf bound free)
  | Specialise QName {- = -} QName (Vector (PType QName pf nb nf bound free)) (Vector (Val QName pf nb nf bound free)) ModuleOps
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

