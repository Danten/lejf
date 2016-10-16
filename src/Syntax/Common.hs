{-# LANGUAGE MultiParamTypeClasses #-}
module Syntax.Common where

import           Data.Text
import           Utils

newtype Variable = Variable Text deriving (Eq,Ord,Show)
newtype Binder = Binder Text deriving (Show, Eq, Ord)

newtype PTVariable = PTVariable Text deriving (Eq,Ord,Show)
newtype PTBinder = PTBinder Text deriving (Show, Eq, Ord)

newtype NTVariable = NTVariable Text deriving (Eq,Ord,Show)
newtype NTBinder = NTBinder Text deriving (Show, Eq, Ord)

newtype Definition = Definition QName deriving (Eq,Ord,Show)
newtype Constructor = Constructor QName deriving (Eq,Ord, Show)
newtype TConstructor = TConstructor QName deriving (Eq,Ord, Show)
newtype Projection = Projection QName deriving (Eq,Ord,Show)

data QName = QName [Text] Text deriving (Eq, Ord, Show)

instance Convert Binder Variable where
  convert (Binder x) = Variable x

instance Convert NTBinder NTVariable where
  convert (NTBinder x) = NTVariable x
