{-# LANGUAGE MultiParamTypeClasses #-}
module Utils where

type Endo a = a -> a
type EndoM m a = a -> m a
type Dup  a = (a, a)

(<>) :: Monoid m => m -> m -> m
(<>) = mappend

class Convert a b where
  convert :: a -> b
