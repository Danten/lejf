module Types.Collect where

import qualified Data.Map as Map
import Syntax.Common
import Syntax.Concrete
import Types.TC

collectDecl :: Decl pb pf nb nf bound free -> Signature QName pf nb nf bound free
collectDecl (DData n _k ty) = Signature (Map.singleton (TConstructor n) ty) mempty mempty
collectDecl (DDef n nt _) = Signature mempty mempty (Map.singleton n nt)
collectDecl (CoData n _k ty) = Signature mempty (Map.singleton (TConstructor n) ty) mempty
collectDecl (Template{}) = mempty
collectDecl (Module{}) = mempty
collectDecl (Specialise{}) = mempty

collectNameSpace :: NameSpace a pb pf nb nf bound free -> Signature QName pf nb nf bound free
collectNameSpace (Namespace _ _ _ decls) = foldMap collectDecl decls

collectProgram :: Program pb pf nb nf bound free -> Signature QName pf nb nf bound free
collectProgram (Program ns) = collectNameSpace ns
