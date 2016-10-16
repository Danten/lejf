{-# LANGUAGE MultiParamTypeClasses #-}
module Types where

import qualified Data.Text.IO  as Text

import           Syntax.Decl   (Program)

import qualified Types.Collect as Collect
import           Types.Errors  (error2Text)
import qualified Types.Rules   as Rules
import           Types.TC      (Env (Env), nameOfTerm, runTC')

runTC :: Program -> IO ()
runTC m = case runTC' (Rules.tcProgram m) (Env mempty (Collect.collectProgram m) undefined) of
  Right x -> pure x
  Left xs -> {-mapM_-} Text.putStrLn (error2Text nameOfTerm xs) >> error "Typechecking failed"

