module Syntax.Common where

import Data.Text

newtype Variable = Variable Text deriving (Eq,Ord,Show)
newtype Binder = Binder Text deriving (Show, Eq)
newtype Constructor = Constructor QName deriving (Eq,Ord, Show)
newtype TConstructor = TConstructor QName deriving (Eq,Ord, Show)
newtype Projection = Projection QName deriving (Eq,Ord,Show)

data QName = QName [Text] Text deriving (Eq, Ord, Show)
