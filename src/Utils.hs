{-# language MultiParamTypeClasses #-}
module Utils where

type Endo a = a -> a

(<>) :: Monoid m => m -> m -> m
(<>) = mappend

class Convert a b where
  convert :: a -> b
