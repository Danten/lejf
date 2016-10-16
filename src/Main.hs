{-# LANGUAGE OverloadedStrings #-}
module Main where

import qualified Data.Map        as Map
import           Data.Text       ()
import qualified Data.Text.IO    as Text
import           Data.Vector     as V

import           Syntax.Common
import           Syntax.Decl
import           Syntax.Internal
import           Syntax.Pretty

import           Types

natModule :: Decl
natModule = Module $ Namespace qnat decls
  where
    decls = V.fromList [natD, idD, idD2, idD3, dblD]
    natt = PCon (TConstructor qnat) V.empty
    qnat = QName ["Main"] "Nat"
    natD = DData qnat KUniverse $ Do $ PCoProduct $ Map.fromList [(czer, PStruct V.empty), (csuc, Ptr $ Mon natt)]
    csuc = Constructor $ QName ["Main", "Nat"] "Suc"
    czer = Constructor $ QName ["Main", "Nat"] "Zero"
    qid = QName ["Main"] "id"
    idD = DDef qid (Fun natt (Mon natt)) $
         Lam' (Binder "n") $
         Case' (Variable "n") $ V.fromList
         [ Branch czer $ Split' (Variable "n") V.empty $ Do $ Return $ Con czer nil
         , Branch csuc $ Do $ Return $ Con csuc $ Var $ Variable "n"
         ]
    qid2 = QName ["Main"] "id2"
    idD2 = DDef qid2 (Fun natt (Mon natt)) $
         Lam' (Binder "n") $
         Case' (Variable "n") $ V.fromList
         [ Branch czer $ Do $ Return $ Con czer nil
         , Branch csuc
            $ Do $ Return $ Con csuc $ Thunk $ Apply (CVar $ Variable "n") V.empty
         ]
    qid3 = QName ["Main"] "id3"
    did3 = Definition qid3
    idD3 = DDef qid3 (Fun natt (Mon natt)) $
         Lam' (Binder "n") $
         Case' (Variable "n") $ V.fromList
         [ Branch czer $ Do $ Return $ Con czer nil
         , Branch csuc $ Derefence' (Variable "n")
            $ Do $ With (Apply (CDef did3) $ V.singleton (Push $ Var $ Variable $ "n")) (Binder "r")
            $ Return $ Con csuc $ Var $ Variable "r"
         ]
    qdbl = QName ["Main"] "double"
    ddbl = Definition qdbl
    dblD = DDef qdbl (Fun natt (Mon natt)) $
         Lam' (Binder "n") $
         Case' (Variable "n") $ V.fromList
         [ Branch czer $ Do $ Return $ Con czer nil
         , Branch csuc $ Derefence' (Variable $ "n")
            $ Do $ With (Apply (CDef ddbl) $ V.singleton (Push $ Var $ Variable $ "n")) (Binder "r")
            $ Return $ Con csuc $ ThunkVal $ Con csuc $ Var $ Variable "r"
         ]
    nil = Struct V.empty


test :: Program
test = Program $ Namespace qmain decls
  where
    qmain = QName [] "Main"
    qnpair = QName ["Main"] "NPair"
    qpair = QName ["Main"] "Pair"
    qswap = QName ["Main"] "swap"
    dswap = Definition qswap
    qnswap = QName ["Main"] "nat-swap"
    qVector = QName ["Main"] "Vector"
    qTestVector = QName ["Main"] "Test::Vector"
    pfst = Projection $ QName ["Main", "Pair"] "fst"
    psnd = Projection $ QName ["Main", "Pair"] "snd"
    qnat = QName ["Main"] "Nat"
    natt = PCon (TConstructor qnat) V.empty
    csuc = Constructor $ QName ["Main", "Nat"] "Suc"
    czer = Constructor $ QName ["Main", "Nat"] "Zero"
    swapD = DDef qswap (Forall (NTBinder "α") $ Forall (NTBinder "β") $ Fun (Ptr (pairt na nb)) (pairt nb na)) $
          TLam' (NTBinder "α") $ TLam' (NTBinder "β") $
          Lam' (Binder "x") $
          New' $ V.fromList
          [ CoBranch pfst $ Do $ TCall (Apply (CVar $ Variable "x") $ V.singleton (Proj psnd))
          , CoBranch psnd $ Do $ TCall (Apply (CVar $ Variable "x") $ V.singleton (Proj pfst))
          ]
    nswapD = DDef qnswap (Fun (Ptr npairt) npairt) $
          Do $ TCall $ Apply (CDef dswap) $ V.fromList [Type $ Mon natt, Type $ Mon natt]
    na = NVar (NTVariable "α")
    nb = NVar (NTVariable "β")
    pairD = CoData qpair (KForall (NTBinder "α") $ KForall (NTBinder "β") KUniverse)
      $ TLam' (NTBinder "α") $ TLam' (NTBinder "β")
      $ Do $ NObject $ Map.fromList [(pfst, NVar (NTVariable "α")),(psnd, NVar (NTVariable "β"))]
    pairt a b = NCon (TConstructor qpair) $ V.fromList [Type a, Type b]
    npairD = CoData qnpair KUniverse $ Do $ NCon (TConstructor qpair) $ V.fromList [Type $ Mon natt, Type $ Mon natt]
    npairt = NCon (TConstructor qnpair) V.empty
    vectorD = DData qVector (KForall (NTBinder "α") $ KFun natt $ KUniverse)
      $ TLam' (NTBinder "α") $ Lam' (Binder "n")
      $ Case' (Variable "n") $ V.fromList
        [ Branch czer $ Do $ PStruct V.empty
        , Branch csuc $ Derefence' (Variable "n")
          $ Do $ PStruct $ V.fromList [Ptr $ na, PCon (TConstructor qVector) $ V.fromList [Type na, Push $ Var (Variable "n")]]
        ]
    testVector =  DDef qTestVector (Mon $ PCon (TConstructor qVector) $ V.fromList [Type $ Mon natt, Push $ Con csuc $ ThunkVal $ Con csuc $ ThunkVal $ Con czer $ Struct V.empty])
      $ Do $ Return $ Struct $ V.fromList [ThunkVal $ Con czer $ Struct V.empty, Struct $ V.fromList
                                          [ThunkVal $ Con csuc $ ThunkVal $ Con czer $ Struct V.empty
                                          ,Struct V.empty
                                          ]]
    decls = V.fromList [natModule,pairD,npairD,swapD,nswapD, vectorD, testVector]

main :: IO ()
main = do
  Text.putStrLn $ pprint test
  () <- runTC test
  putStrLn "The code Typechecks"
