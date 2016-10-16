module Types.Collect where

import qualified Data.Map      as Map
import           Syntax.Common
import           Syntax.Decl
import           Types.TC

collectDecl :: Decl -> Signature
collectDecl (DData n _k ty) = Signature (Map.singleton (TConstructor n) ty) mempty mempty
collectDecl (DDef n nt _) = Signature mempty mempty (Map.singleton (Definition n) nt)
collectDecl (CoData n _k ty) = Signature mempty (Map.singleton (TConstructor n) ty) mempty
collectDecl (Template ns) = collectNameSpace ns
collectDecl (Module ns) = collectNameSpace ns
collectDecl (Specialise{}) = mempty

-- Could be in parallel
collectNameSpace :: NameSpace -> Signature
collectNameSpace (Namespace _ decls) = foldMap collectDecl decls

collectProgram :: Program -> Signature
collectProgram (Program ns) = collectNameSpace ns
