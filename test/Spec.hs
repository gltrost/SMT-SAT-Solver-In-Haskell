module Main (main) where

import Test.Hspec 
import Control.Exception (evaluate)
import PROP
import SAT

main :: IO ()
main = hspec $ do
  describe "Provability of expressions:" $ do
-- Basic examples that should return True
    it ("isClauseSat test 1") $ do
      isClauseSat [Just True] [p] `shouldBe` True

    it ("isClauseSat test 3") $ do
      isClauseSat [Just False,Just True] [p,q] `shouldBe` True      

    it ("isClauseSat test 4") $ do
      isClauseSat [Just False,Just False,Just True] [p,q,r] `shouldBe` False 

    it ("isClauseSat test 5") $ do
      isClauseSat [Just False,Nothing,Nothing] [p,q,r] `shouldBe` False 

-- Literals 
p = Lit {var = 1, value = True}
q = Lit {var = 2, value = True}
r = Lit {var = 3, value = False}

-- Basic examples that should return Some True
t1 = [[p]]
t2 = [[p,p]]
t3 = [[p],[p]]

