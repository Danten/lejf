{-# LANGUAGE MultiParamTypeClasses #-}
module Types.Equality where

import           Control.Monad   (foldM)

import qualified Data.Map as Map
import           Data.Maybe      (isJust)
import           Data.Set        (Set)
import qualified Data.Set        as Set

import qualified Data.Vector     as V

import           Syntax.Internal
import           Types.Evaluate
import           Types.TC
import           Utils

data EqSet def pf nb nf b f = EqSet
  { pEqs :: Set (Dup (PType def pf nb nf b f))
  , nEqs :: Set (Dup (NType def pf nb nf b f))
  }

instance (Ord def, Ord pf, Ord nb, Ord nf, Ord f) => Monoid (EqSet def pf nb nf b f) where
  mempty = EqSet mempty mempty
  e `mappend` e' = EqSet (pEqs e `mappend` pEqs e')
                         (nEqs e `mappend` nEqs e')

newtype TC' def pf nb nf b f a = TC' { unTC' :: TC def pf nb nf b f (Maybe a)}

instance Functor (TC' def pf nb nf b f) where
  fmap f = TC' . fmap (fmap f) . unTC'

instance Applicative (TC' def pf nb nf b f) where
  pure = TC' . pure . pure
  TC' f <*> TC' x = TC' $ do
    f' <- f
    x' <- x
    pure $ do
      f'' <- f'
      x'' <- x'
      pure (f'' x'')

instance Monad (TC' def pf nb nf b f) where
  TC' tc >>= f = TC' $ do
    m <- tc
    case m of
      Nothing -> pure Nothing
      Just x  -> unTC' (f x)

lift :: TC def pf nb nf b f a -> TC' def pf nb nf b f a
lift = TC' . fmap pure

tcfail :: TC' def pf nb nf b f a
tcfail = TC' (pure Nothing)

type EqCheck ty def pf nb nf b f = Dup (ty def pf nb nf b f) -> EndoM (TC' def pf nb nf b f) (EqSet def pf nb nf b f)

negEq :: (Ord def, Ord pf, Ord nb, Ord nf, Ord f, Convert nb nf, Convert b f) => EqCheck NType def pf nb nf b f
negEq st aOrig | st `Set.member` nEqs aOrig = pure aOrig
               | otherwise = uncurry go st (aOrig {nEqs = Set.insert st (nEqs aOrig)})
  where
    go (Fun p n) (Fun p' n') a = do
      negEq (n,n') =<< posEq (p,p') a
    go (Forall b n) (Forall b' n') a | b == b' = negEq (n,n') a -- TODO α-equality
    go (NVar x) (NVar y) a | x == y = pure a
    go (NObject xs) (NObject ys) a | Map.keys xs == Map.keys ys =
      foldM (flip negEq) a $ zip (Map.elems xs) (Map.elems ys)
    go (Mon p) (Mon p') a = posEq (p,p') a
    go s@(NCon c xs) t a = do
      m <- lift $ evalCon' nconType c xs
      case m of
        Left _   -> go' s t a
        Right s' -> negEq (s', t) a
    go s t a = go' s t a

    go' s (NCon c xs) a = do
      m <- lift $ evalCon' nconType c xs
      case m of
        Left _   -> tcfail
        Right t' -> negEq (s, t') a
    go' _ _ _ = tcfail

posEq :: (Ord def, Ord pf, Ord nb, Ord nf, Ord f, Convert nb nf, Convert b f) =>  EqCheck PType def pf nb nf b f
posEq st aOrig | st `Set.member` pEqs aOrig = return aOrig
               | otherwise = uncurry go st (aOrig {pEqs = Set.insert st (pEqs aOrig)})
  where
    go (PVar x) (PVar y) a | x == y = pure a
    go (PLit x) (PLit y) a | x == y = pure a
    go (Ptr n) (Ptr n') a = negEq (n, n') a
    go (PStruct xs) (PStruct ys) a | length xs == length ys = do
      foldM (flip posEq) a $ V.zip xs ys
    go (PCoProduct xs) (PCoProduct ys) a | Map.keys xs == Map.keys ys = do
      foldM (flip posEq) a $ zip (Map.elems xs) (Map.elems ys)
    go p@(PCon d args) p' a = do
      m <- lift $ evalCon' pconType d args
      case m of
        Left _  -> go' p p' a
        Right s -> posEq (s, p') a
    go s t a = go' s t a

    go' p (PCon d args) a = do
      m <- lift $ evalCon' pconType d args
      case m of
        Left _   -> tcfail
        Right p' -> posEq (p, p') a
    go' _ _ _ = tcfail

checkNegEquality :: (Ord def, Ord pf, Ord nb, Ord nf, Ord f, Convert nb nf, Convert b f)
  => NType def pf nb nf b f -> NType def pf nb nf b f -> TC def pf nb nf b f Bool
checkNegEquality s t = isJust <$> unTC' (negEq (s,t) mempty)

checkPosEquality :: (Ord def, Ord pf, Ord nb, Ord nf, Ord f, Convert nb nf, Convert b f)
  => PType def pf nb nf b f -> PType def pf nb nf b f -> TC def pf nb nf b f Bool
checkPosEquality s t = isJust <$> unTC' (posEq (s,t) mempty)
