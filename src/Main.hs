{-# Language OverloadedStrings #-}
module Main where

import Data.Text()
import qualified Data.Text.IO as Text
import Data.Vector as V
import Syntax.Concrete
import Syntax.Pretty

import Types

test :: Program
test = Program $ Namespace qmain () V.empty decls
  where
    qmain = QName [] "Main"
    qid = QName ["Main"] "id"
    qid2 = QName ["Main"] "id2"
    qid3 = QName ["Main"] "id3"
    qnat = QName ["Main"] "Nat"
    csuc = Constructor $ QName ["Main", "Nat"] "Suc"
    czer = Constructor $ QName ["Main", "Nat"] "Zero"
    natD = DData qnat [] [(czer, []), (csuc,[Ptr $ Lazy nat])]
    idD = DDef qid (Fun nat (Lazy nat)) $
         Lam (Binder "x") $
         Case (Variable "x") $ V.fromList
         [ Branch czer V.empty $ Return $ Con czer V.empty
         , Branch csuc (V.singleton $ Binder "n")
            $ Return $ Con csuc $ V.singleton $ Var $ Variable "n"
         ]
    idD2 = DDef qid2 (Fun nat (Lazy nat)) $
         Lam (Binder "x") $
         Case (Variable "x") $ V.fromList
         [ Branch czer V.empty $ Return $ Con czer V.empty
         , Branch csuc (V.singleton $ Binder "n")
            $ Return $ Con csuc $ V.singleton $ Thunk $ Apply (CVar $ Variable "n") V.empty
         ]
    idD3 = DDef qid3 (Fun nat (Lazy nat)) $
         Lam (Binder "x") $
         Case (Variable "x") $ V.fromList
         [ Branch czer V.empty $ Return $ Con czer V.empty
         , Branch csuc (V.singleton $ Binder "n")
            $ Force (Apply (CDef qid3) $ V.singleton (Push $ Var $ Variable $ "n")) (Binder "r")
            $ Return $ Con csuc $ V.singleton $ Var $ Variable "r"
         ]
    nat = PCon (Constructor qnat) []
    decls = V.fromList [natD , idD, idD2, idD3]

main :: IO ()
main = do
  Text.putStrLn $ pprint test
  () <- runTC $ tcProgram test
  return ()
