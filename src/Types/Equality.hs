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

data EqSet = EqSet
  { pEqs :: Set (Dup PType)
  , nEqs :: Set (Dup NType)
  }

instance Monoid EqSet where
  mempty = EqSet mempty mempty
  e `mappend` e' = EqSet (pEqs e `mappend` pEqs e')
                         (nEqs e `mappend` nEqs e')

newtype TC' a = TC' { unTC' :: TC (Maybe a)}

instance Functor TC' where
  fmap f = TC' . fmap (fmap f) . unTC'

instance Applicative TC' where
  pure = TC' . pure . pure
  TC' f <*> TC' x = TC' $ do
    f' <- f
    x' <- x
    pure $ do
      f'' <- f'
      x'' <- x'
      pure (f'' x'')

instance Monad TC' where
  TC' tc >>= f = TC' $ do
    m <- tc
    case m of
      Nothing -> pure Nothing
      Just x  -> unTC' (f x)

lift :: TC a -> TC' a
lift = TC' . fmap pure

tcfail :: TC' a
tcfail = TC' (pure Nothing)

type EqCheck ty = Dup ty -> EndoM TC' EqSet

negEq :: EqCheck NType
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

posEq :: EqCheck PType
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

checkNegEquality :: NType -> NType -> TC Bool
checkNegEquality s t = isJust <$> unTC' (negEq (s,t) mempty)

checkPosEquality :: PType -> PType -> TC Bool
checkPosEquality s t = isJust <$> unTC' (posEq (s,t) mempty)
