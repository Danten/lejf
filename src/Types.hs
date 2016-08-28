module Types where

import qualified Data.Text.IO as Text

import Syntax.Decl (Program)
import Syntax.Pretty (Pretty)

import qualified Types.Collect as Collect
import Types.Errors (error2Text)
import qualified Types.Rules as Rules
import Types.TC(runTC', Env(Env), nameOfTerm)

import Utils (Convert)

runTC :: (Ord free, Ord nf, Eq pf, Eq nb, Convert bound free, Convert nb nf
         , Pretty pf, Pretty nb, Pretty nf, Pretty bound, Pretty free)
      => Program pb pf nb nf bound free -> IO ()
runTC m = case runTC' (Rules.tcProgram m) (Env mempty (Collect.collectProgram m) undefined) of
  Right x -> pure x
  Left xs -> {-mapM_-} Text.putStrLn (error2Text nameOfTerm xs) >> error "Typechecking failed"

