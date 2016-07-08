module Types where

import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text

import Data.Foldable

import Syntax.Concrete
import Syntax.Common
import Syntax.Internal

newtype TC bound free a = TC {runTC' :: Env bound free -> Either [Text] a}
type Endo a = a -> a

instance Functor (TC bound free) where
  fmap f (TC m) = TC $ fmap f . m

instance Applicative (TC bound free) where
  pure x = TC $ const (Right x)
  TC f <*> TC m = TC $ \ e -> case (f e, m e) of
    (Left xs, Left ys) -> Left (xs ++ ys)
    (Left xs, Right _) -> Left xs
    (Right _, Left ys) -> Left ys
    (Right x, Right y) -> Right (x y)

local :: (Env bound free -> Env bound free) -> TC bound free a -> TC bound free a
local f (TC m) = TC $ m . f

data Env bound free= Env
  { context :: Map free (PType bound free)
  , tyVars  :: Map free (NType bound free)
  , dataKinds :: Map Constructor Int -- Maybe need to be Vector Polarity?
  , sigTerm :: Map QName (NType bound free)
  }

emptyEnv :: Ord free => Env bound free
emptyEnv = Env mempty mempty mempty mempty

addTele :: (Ord free, Convert bound free) => Vector (bound, PType bound free) -> Endo (Env bound free)
addTele tele env | V.null tele = env -- for now we don't support telescopes
                 | otherwise   = env {context = context env `Map.union` tele'}
  where
    -- tele' :: Map Variable (PType bound free)
    tele' = Map.fromList $ V.toList $ fmap (\(x,p) -> (convert x,p))tele

tcVal :: (Show defs, Show bound, Show free) => Val defs bound free -> PType bound free -> TC bound free ()
tcVal v pt = error $ "Not implemented tcVal: " ++ show v
  ++ " of type " ++ show pt

tcTerm :: (Ord free, Convert bound free, Show free, Show bound, Show defs)
       => Term (WhereClause bound free) defs bound free -> NType bound free -> TC bound free ()
tcTerm (Lam b t) (Fun p n) = local (addTele $ V.singleton (b,p)) $ tcTerm t n
tcTerm (Return v) (Lazy p) = tcVal v p
tcTerm (Case x bs) n = do
  for_ bs $ \ (Branch c xs t) -> do
    -- we should check that c is a constructor of the correct type x splits on
    -- we should also add xs to the environment
    tcTerm t n
tcTerm t nt = error $ "Not impletmented tcTerm: " ++ show t
  ++ " of type " ++ show nt


tcDecl :: (Ord free, Show free, Show bound, Convert bound free) => Decl bound free -> TC bound free ()
tcDecl (DDef _ nt t) = tcTerm t nt -- we should check that nt makes sense
tcDecl (DData _ _ _) = pure ()

tcNameSpace :: (Ord free, Convert bound free, Show free, Show bound)
            => (a -> Endo (Env bound free)) -> NameSpace a bound free -> TC bound free ()
tcNameSpace up (Namespace _ t tele decls)
  = local (up t)
  $ local (addTele tele)
  $ traverse_ tcDecl decls

tcProgram :: (Ord free, Convert bound free, Show free, Show bound) => Program bound free -> TC bound free ()
tcProgram (Program ns) = tcNameSpace (const id) ns

runTC :: (Ord free) => TC bound free a ->IO a
runTC m = case runTC' m emptyEnv of
  Right x -> pure x
  Left xs -> mapM_ Text.putStrLn xs >> error "Typechecking failed"
