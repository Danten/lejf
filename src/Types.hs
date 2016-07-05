module Types where

import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad.Par
import Control.Monad.Reader

import Syntax.Concrete

type TC = ReaderT Env Par
type Endo a = a -> a

data Env = Env
  { context :: Map Variable PType
  , tyVars  :: Map Variable NType
  , dataKinds :: Map Constructor Int -- Maybe need to be Vector Polarity?
  , sigTerm :: Map QName NType
  }

emptyEnv :: Env
emptyEnv = Env mempty mempty mempty mempty

addTele :: Vector (Binder, PType) -> Endo Env
addTele tele env | V.null tele = env -- for now we don't support telescopes
                 | otherwise   = env {context = context env `Map.union` tele'}
  where
    tele' :: Map Variable PType
    tele' = Map.fromList $ V.toList $ fmap (\(Binder x,p) -> (Variable x,p))tele

tcTerm :: Term WhereClause -> NType -> TC ()
tcTerm (Lam b t) (Fun p n) = local (addTele $ V.singleton (b,p)) $ tcTerm t n
tcTerm t nt = error $ "Not impletmented tcTerm: " ++ show t
  ++ " of type " ++ show nt


tcDecl :: Decl -> TC ()
tcDecl (DDef _ nt t) = tcTerm t nt -- we should check that nt makes sense
tcDecl (DData _ _ _) = return ()

tcNameSpace :: (a -> Endo Env) -> NameSpace a -> TC ()
tcNameSpace up (Namespace _ t tele decls)
  = local (up t)
  $ local (addTele tele)
  $ mapM_ tcDecl decls

tcProgram :: Program -> TC ()
tcProgram (Program ns) = tcNameSpace (const id) ns

runTC :: TC a -> IO a
runTC m = runParIO $ runReaderT m emptyEnv
