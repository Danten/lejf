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
    qnpair = QName ["Main"] "NPair"
    qpair = QName ["Main"] "Pair"
    qswap = QName ["Main"] "swap"
    qnswap = QName ["Main"] "nat-swap"
    qVector = QName ["Main"] "Vector"
    qTestVector = QName ["Main"] "Test::Vector"
    csuc = Constructor $ QName ["Main", "Nat"] "Suc"
    czer = Constructor $ QName ["Main", "Nat"] "Zero"
    pfst = Projection $ QName ["Main", "Nat"] "fst"
    psnd = Projection $ QName ["Main", "Nat"] "snd"
    nil = Struct V.empty
    natD = DData qnat KUniverse $ Do $ PCoProduct $ Map.fromList [(czer, PStruct V.empty), (csuc, Ptr $ Mon natt)]
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
    swapD = DDef qswap (Forall (Binder "α") $ Forall (Binder "β") $ Fun (Ptr (pairt na nb)) (pairt nb na)) $
          TLam (Binder "α") $ TLam (Binder "β") $
          Lam (Binder "x") $
          New $ V.fromList
          [ CoBranch pfst $ Do $ Act $ Call (Apply (CVar $ Variable "x") $ V.singleton (Proj psnd))
          , CoBranch psnd $ Do $ Act $ Call (Apply (CVar $ Variable "x") $ V.singleton (Proj pfst))
          ]
    nswapD = DDef qnswap (Fun (Ptr npairt) npairt) $
          Lam (Binder "x") $
          New $ V.fromList
          [ CoBranch pfst $ Do $ Act $ Call (Apply (CVar $ Variable "x") $ V.singleton (Proj psnd))
          , CoBranch psnd $ Do $ Act $ Call (Apply (CVar $ Variable "x") $ V.singleton (Proj pfst))
          ]
    na = NVar (Variable "α")
    nb = NVar (Variable "β")
    natt = PCon (TConstructor qnat) V.empty
    pairD = CoData qpair (KForall (Binder "α") $ KForall (Binder "β") KUniverse)
      $ TLam (Binder "α") $ TLam (Binder "β")
      $ Do $ NObject $ Map.fromList [(pfst, NVar (Variable "α")),(psnd, NVar (Variable "β"))]
    pairt a b = NCon (TConstructor qpair) $ V.fromList [Type a, Type b]
    npairD = CoData qnpair KUniverse $ Do $ NCon (TConstructor qpair) $ V.fromList [Type $ Mon natt, Type $ Mon natt]
    npairt = NCon (TConstructor qnpair) V.empty
    vectorD = DData qVector (KForall (Binder "α") $ KFun natt $ KUniverse)
      $ TLam (Binder "α") $ Lam (Binder "n")
      $ Case (Variable "n") $ V.fromList
        [ Branch czer $ Do $ PStruct V.empty
        , Branch csuc $ Derefence (Variable "n")
          $ Do $ PStruct $ V.fromList [Ptr $ na, PCon (TConstructor qVector) $ V.fromList [Type na, Push $ Var (Variable "n")]]
        ]
    testVector =  DDef qTestVector (Mon $ PCon (TConstructor qVector) $ V.fromList [Type $ Mon natt, Push $ Con csuc $ ThunkVal $ Con csuc $ ThunkVal $ Con czer $ Struct V.empty])
      $ Do $ Return $ Struct $ V.fromList [ThunkVal $ Con czer $ Struct V.empty, Struct $ V.fromList
                                          [ThunkVal $ Con csuc $ ThunkVal $ Con czer $ Struct V.empty
                                          ,Struct V.empty
                                          ]]
    decls = V.fromList [natD , idD, idD2, idD3,dblD,pairD,npairD,swapD,nswapD, vectorD, testVector]

main :: IO ()
main = do
  Text.putStrLn $ pprint test
  () <- runTC test
  putStrLn "The code Typechecks"
