{-# LANGUAGE OverloadedStrings #-}
module Types.Errors where

import           Data.Vector     (Vector)
import qualified Data.Vector     as V

import           Data.Text       (Text)
import qualified Data.Text       as Text

import           Syntax.Common
import           Syntax.Internal
import           Syntax.Pretty   ()

import qualified Syntax.Pretty   as Pretty

import           Utils

data Error env
  = Error env ErrorType

data ProgType
  = PT_Act Act
  | PT_Call Call
  | PT_Mon CMonad
  -- | PT_Term (Term def pf nb nf bound free)
  | PT_Equation
  | PT_Val Val
  | PT_Proj Projection
  | PT_Lit Literal
  | PT_Var Variable
  | PT_Con Constructor
  | PT_Def Definition

type TypeEvaluationPath = [(TConstructor, Args)]

data TypeType
  = Positive PType
  | ByPath TypeEvaluationPath TypeType
  | Negative NType

data NotInScope
  = NIS_Constructor Constructor PCoProduct
  | NIS_TConstructor TConstructor
  | NIS_Projection Projection NObject
  | NIS_Def Definition
  | NIS_Variable Variable

data ErrorType
  = FromMonadFail String
  | NotInScope NotInScope
  | StructArityMisMatch (Vector Val) (Vector PType)
  | StructBoundArityMisMatch (Vector Binder) (Vector PType)
  | ShouldBeButIsA ProgType Text TypeType
  | PushArgumentToNoFun Val TypeType
  | ProjArgumentToNoObject Projection TypeType
  | TEvalCycle TConstructor TypeEvaluationPath
  | EvaluationError Text
  | InferedDon'tMatchChecked ProgType
        TypeType
        TypeType

ttText :: TypeType -> Text
ttText (Positive p) = Pretty.pprint p
ttText (Negative n) = Pretty.pprint n
ttText (ByPath [] t) = ttText t
ttText (ByPath ds tf) = foldr (\(n,a) t -> Pretty.pprint n <> Pretty.toText 0 (Pretty.args a) <> " ~> " <> t) (ttText tf) ds

ptText :: ProgType -> Text
ptText (PT_Act a)    = Pretty.pprint a
ptText (PT_Call c)   = Pretty.pprint c
ptText (PT_Proj p)   = Pretty.pprint p
ptText (PT_Val v)    = Pretty.pprint v
ptText (PT_Mon m)    = Pretty.pprint m
ptText (PT_Con c)    = Pretty.pprint c
ptText (PT_Def d)    = Pretty.pprint d
ptText (PT_Var x)    = Pretty.pprint x
ptText (PT_Lit l)    = Pretty.pprint l
ptText (PT_Equation) = "!EQUATION!"

nisText :: NotInScope -> Text
nisText (NIS_Def d) = "definition «" <> Pretty.pprint d <> "»"

errorType2Text :: ErrorType -> Text
errorType2Text (FromMonadFail s) = Text.pack s
errorType2Text (TEvalCycle c cs) = "Cycle detected when evaluating «" <> Pretty.pprint c <> "»\n" <>
  "evaluation causes the following path" <> foldr (\(d,as) r -> Pretty.pprint (PCon d as) <> " ~> " <> r) "" cs
errorType2Text (StructBoundArityMisMatch bs ty) = "Trying to split a struct of type «" <> Pretty.pprint (PStruct ty) <> "»\n" <>
  "but the binders you provided «" <> Pretty.toText 0 (Pretty.intersperse ", " $ V.toList $ fmap Pretty.pretty bs) <> "»"
errorType2Text (PushArgumentToNoFun v t) = "Trying to push value «" <> ptText (PT_Val v) <> "»\n" <>
 "but the transformation should be of type «" <> ttText t <> "»\n" <>
 "which is not a function type! We can only push values when the transformation is a function."
errorType2Text (ProjArgumentToNoObject p t) = "Trying to project «" <> Pretty.pprint p <> "»\n" <>
 "but the transformation should be of type «" <> ttText t <> "»\n" <>
 "which is not an object type! We can only project when the transformation is an object."
errorType2Text (NotInScope n) = "Not in scope: " <> nisText n
errorType2Text (StructArityMisMatch _ _) = "Struct arity mis-match"
errorType2Text (InferedDon'tMatchChecked p i c) = "Infered type don't match the checked type:\n"
  <> "For term «" <> ptText p <> "»\n"
  <> "We infered «" <> ttText i <> "» but "
  <> "one would expect «" <> ttText c <> "»\n\n"
errorType2Text (ShouldBeButIsA p desc t) = "The program is not of the correct type:\n"
  <> "We expect a term of type «" <> ttText t <> "» but "
  <> "the term «" <> ptText p <> "» builds " <> desc
errorType2Text (EvaluationError e) = e

error2Text :: (env -> QName) -> Error env -> Text
error2Text nameOfTerm (Error env t)
  = let QName root loc = nameOfTerm env in foldr (\x y -> x `mappend`"." `mappend` y) loc root `mappend` ": " `mappend` errorType2Text t
