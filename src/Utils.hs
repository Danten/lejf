module Utils where

type Endo a = a -> a

(<>) :: Monoid m => m -> m -> m
(<>) = mappend
