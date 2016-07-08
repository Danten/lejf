module Syntax.Concrete where

import Data.Vector

import Syntax.Common
import Syntax.Internal

newtype Program bound free = Program (NoTNameSpace bound free)


type TypNameSpace = NameSpace (Vector Binder)
type NoTNameSpace = NameSpace ()

data NameSpace tybinds bound free
  = Namespace QName tybinds (Vector (bound, PType bound free)) (Vector (Decl bound free))
  deriving (Show)

data WhereClause bound free = WhereClause (Maybe QName) (Vector (Decl bound free))
  deriving (Show)

-- missing import statement
data Decl bound free
  = DData QName [bound] [(Constructor, [PType bound free])]
  | CoData QName [bound] [(Projection, NType bound free)]
  | DDef QName (NType bound free) (Term (WhereClause bound free) QName bound free)
  | Template (TypNameSpace bound free)
  | Module (TypNameSpace bound free)
  | Specialise QName {- = -} QName (Vector (PType bound free)) (Vector (Val QName bound free)) ModuleOps
  | ModuleApply QName {- = -} QName (Vector (NType bound free)) (Vector (Val QName bound free)) ModuleOps
  | ModuleClosure QName (Vector (bound, Val QName bound free, PType bound free)) (Vector (Decl bound free))
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

