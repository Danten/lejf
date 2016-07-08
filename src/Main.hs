{-# Language OverloadedStrings #-}
module Main where

import Data.Text()
import qualified Data.Text.IO as Text
import Data.Vector as V

import Syntax.Concrete
import Syntax.Common
import Syntax.Internal
import Syntax.Pretty

import Types

test :: Program Binder Variable
test = Program $ Namespace qmain () V.empty decls
  where
    qmain = QName [] "Main"
    qid = QName ["Main"] "id"
    qid2 = QName ["Main"] "id2"
    qid3 = QName ["Main"] "id3"
    qnat = QName ["Main"] "Nat"
    qpair = QName ["Main"] "Pair"
    qswap = QName ["Main"] "swap"
    csuc = Constructor $ QName ["Main", "Nat"] "Suc"
    czer = Constructor $ QName ["Main", "Nat"] "Zero"
    pfst = Projection $ QName ["Main", "Nat"] "fst"
    psnd = Projection $ QName ["Main", "Nat"] "snd"
    natD = DData qnat [] [(czer, []), (csuc,[Ptr $ Lazy natt])]
    idD = DDef qid (Fun natt (Lazy natt)) $
         Lam (Binder "x") $
         Case (Variable "x") $ V.fromList
         [ Branch czer V.empty $ Return $ Con czer V.empty
         , Branch csuc (V.singleton $ Binder "n")
            $ Return $ Con csuc $ V.singleton $ Var $ Variable "n"
         ]
    idD2 = DDef qid2 (Fun natt (Lazy natt)) $
         Lam (Binder "x") $
         Case (Variable "x") $ V.fromList
         [ Branch czer V.empty $ Return $ Con czer V.empty
         , Branch csuc (V.singleton $ Binder "n")
            $ Return $ Con csuc $ V.singleton $ Thunk $ Apply (CVar $ Variable "n") V.empty
         ]
    idD3 = DDef qid3 (Fun natt (Lazy natt)) $
         Lam (Binder "x") $
         Case (Variable "x") $ V.fromList
         [ Branch czer V.empty $ Return $ Con czer V.empty
         , Branch csuc (V.singleton $ Binder "n")
            $ Force (Apply (CDef qid3) $ V.singleton (Push $ Var $ Variable $ "n")) (Binder "r")
            $ Return $ Con csuc $ V.singleton $ Var $ Variable "r"
         ]
    swapD = DDef qswap (Fun (Ptr pairt) pairt) $
          Lam (Binder "x") $
          New $ V.fromList
          [ CoBranch pfst $ Call (Apply (CVar $ Variable "x") $ V.singleton (Proj psnd))
          , CoBranch psnd $ Call (Apply (CVar $ Variable "x") $ V.singleton (Proj pfst))
          ]
    natt = PCon (Constructor qnat) []
    pairD = CoData qpair [] [(pfst, Lazy natt),(psnd, Lazy natt)]
    pairt = NCon (Constructor qpair) []
    decls = V.fromList [natD , idD, idD2, idD3,pairD,swapD]

main :: IO ()
main = do
  Text.putStrLn $ pprint test
  x <- runTC $ tcProgram test
  x `seq` putStrLn "The code Typechecks"
