{-# Language OverloadedStrings #-}
module Main where

import qualified Data.Map as Map
import Data.Text()
import qualified Data.Text.IO as Text
import Data.Vector as V

import Syntax.Concrete
import Syntax.Common
import Syntax.Internal
import Syntax.Pretty

import Types

test :: Program Binder Variable Binder Variable Binder Variable
test = Program $ Namespace qmain () V.empty decls
  where
    qmain = QName [] "Main"
    qid = QName ["Main"] "id"
    qid2 = QName ["Main"] "id2"
    qid3 = QName ["Main"] "id3"
    qdbl = QName ["Main"] "double"
    qnat = QName ["Main"] "Nat"
    qpair = QName ["Main"] "Pair"
    qswap = QName ["Main"] "swap"
    csuc = Constructor $ QName ["Main", "Nat"] "Suc"
    czer = Constructor $ QName ["Main", "Nat"] "Zero"
    pfst = Projection $ QName ["Main", "Nat"] "fst"
    psnd = Projection $ QName ["Main", "Nat"] "snd"
    nil = Struct V.empty
    natD = DData qnat $ PCoProduct $ Map.fromList [(czer, PStruct V.empty), (csuc, Ptr $ Mon natt)]
    idD = DDef qid (Fun natt (Mon natt)) $
         Lam (Binder "n") $
         Case (Variable "n") $ V.fromList
         [ Branch czer $ Split (Variable "n") V.empty $ Do $ Return $ Con czer nil
         , Branch csuc
            $ Do $ Return $ Con csuc $ Var $ Variable "n"
         ]
    idD2 = DDef qid2 (Fun natt (Mon natt)) $
         Lam (Binder "n") $
         Case (Variable "n") $ V.fromList
         [ Branch czer $ Do $ Return $ Con czer nil
         , Branch csuc
            $ Do $ Return $ Con csuc $ Thunk $ Call (Apply (CVar $ Variable "n") V.empty)
         ]
    idD3 = DDef qid3 (Fun natt (Mon natt)) $
         Lam (Binder "n") $
         Case (Variable "n") $ V.fromList
         [ Branch czer $ Do $ Return $ Con czer nil
         , Branch csuc $ Derefence (Variable "n")
            $ With (Apply (CDef qid3) $ V.singleton (Push $ Var $ Variable $ "n")) (Binder "r")
            $ Do $ Return $ Con csuc $ Var $ Variable "r"
         ]
    dblD = DDef qdbl (Fun natt (Mon natt)) $
         Lam (Binder "n") $
         Case (Variable "n") $ V.fromList
         [ Branch czer $ Do $ Return $ Con czer nil
         , Branch csuc $ Derefence (Variable $ "n")
            $ With (Apply (CDef qdbl) $ V.singleton (Push $ Var $ Variable $ "n")) (Binder "r")
            $ Do $ Return $ Con csuc $ ThunkVal $ Con csuc $ Var $ Variable "r"
         ]
    swapD = DDef qswap (Fun (Ptr pairt) pairt) $
          Lam (Binder "x") $
          New $ V.fromList
          [ CoBranch pfst $ Do $ Act $ Call (Apply (CVar $ Variable "x") $ V.singleton (Proj psnd))
          , CoBranch psnd $ Do $ Act $ Call (Apply (CVar $ Variable "x") $ V.singleton (Proj pfst))
          ]
    natt = PCon (TConstructor qnat)
    pairD = CoData qpair $ NObject $ Map.fromList [(pfst, Mon natt),(psnd, Mon natt)]
    pairt = NCon (TConstructor qpair)
    decls = V.fromList [natD , idD, idD2, idD3,dblD,pairD,swapD]

main :: IO ()
main = do
  Text.putStrLn $ pprint test
  () <- runTC test
  putStrLn "The code Typechecks"
