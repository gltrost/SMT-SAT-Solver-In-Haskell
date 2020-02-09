module Main (main) where

import Test.Hspec 
-- import Control.Exception (evaluate)
import PROP
import SAT

main :: IO ()
main = hspec $ do
  describe "Provability of expressions:" $ do
-- Basic examples for isClauseSat

    it "isClauseSat test 0" $ 
      isClauseSat [] [] `shouldBe` False -- left up to interpretation

    it "isClauseSat test 1" $ 
      isClauseSat [Just True] [p] `shouldBe` True

    it "isClauseSat test 2" $ 
      isClauseSat [Just False,Just True] [p,q] `shouldBe` True      

    it "isClauseSat test 3" $ 
      isClauseSat [Just False,Just False,Just True] [p,q,r] `shouldBe` False 

    it "isClauseSat test 4" $ 
      isClauseSat [Just False,Nothing,Nothing] [p,q,r] `shouldBe` False 

-- Basic examples for isClauseConflict
    it "isClauseConflict test 1" $ 
      isClauseConflict [] [] `shouldBe` True

    it "isClauseConflict test 1" $ 
      isClauseConflict [Just False] [p] `shouldBe` True

    it "isClauseConflict test 2" $ 
      isClauseConflict [Just False,Just False] [p,q] `shouldBe` True      

    it "isClauseConflict test 3" $ 
      isClauseConflict [Just False,Just False, Just True] [p,q,r] `shouldBe` True      

    it "isClauseConflict test 4" $ 
      isClauseConflict [Nothing] [p] `shouldBe` False 

    it "isClauseConflict test 5" $ 
      isClauseConflict [Just True,Nothing,Nothing] [p,q,r] `shouldBe` False 

-- Basic examples for isClauseUnitUnr
    it "isClauseUnitUnr test 0" $ 
      isClauseUnitUnr [] [] `shouldBe` []

    it "isClauseUnitUnr test 1" $ 
      isClauseUnitUnr [Just False] [p] `shouldBe` []

    it "isClauseUnitUnr test 2" $ 
      isClauseUnitUnr [Nothing,Just False] [p,q] `shouldBe` [p]     

    it "isClauseUnitUnr test 3" $ 
      isClauseUnitUnr [Just False,Nothing] [p,q] `shouldBe` [q]     

    it "isClauseUnitUnr test 4" $ 
      isClauseUnitUnr [Nothing] [p] `shouldBe` [p] 

    it "isClauseUnitUnr test 5" $ 
      isClauseUnitUnr [Nothing,Nothing,Just False] [p,q,r] `shouldBe` [p,q] 

-- Basic examples for partialEvalClause
    it "partialEvalClause test 0" $ 
      partialEvalClause [] [] `shouldBe` Conflicting -- should this be true??? 

    it "partialEvalClause test 1" $ 
      partialEvalClause [Just True,Just True,Just False] [p,q,r] `shouldBe` Satisfied

    it "partialEvalClause test 2" $ 
      partialEvalClause [Just False, Just False, Just True] [p,q,r] `shouldBe` Conflicting    

    it "partialEvalClause test 3" $ 
      partialEvalClause [Just False, Just False, Nothing] [p,q,r] `shouldBe` Unit r    

    it "partialEvalClause test 4" $ 
      partialEvalClause [Just False, Nothing, Just True] [p,q,r] `shouldBe` Unit q 

    it "partialEvalClause test 5" $ 
      partialEvalClause [Nothing,Nothing,Just True] [p,q,r] `shouldBe` Unresolved

-- Basic examples for isSat
    it "isSat test 0" $ 
      isSat [] Cnf{clauses=[],nvars=0}  `shouldBe` True  -- should this be true??? 

    it "isSat test 1" $ 
      isSat [Just True,Just True,Just False] Cnf{clauses=[[p]],nvars=3} `shouldBe` True 

    it "isSat test 2" $ 
      isSat [Just False, Just True, Just False] Cnf{clauses=[[p,q],[r]],nvars=3}  `shouldBe` True     

    it "isSat test 3" $ 
      isSat [Just True, Just False, Just True] Cnf{clauses=[[p,r],[q,r]],nvars=3}  `shouldBe` False     

    it "isSat test 4" $ 
      isSat [Just True, Just True, Just False] Cnf{clauses=[[p,r],[q],[]],nvars=3}  `shouldBe` False 

    it "isSat test 5" $ 
      isSat [Nothing,Nothing,Just True] Cnf{clauses=[[p,q,r]],nvars=3}  `shouldBe` False

-- Basic examples for isConflict
    it "isConflict test 0" $ 
      isConflict [] Cnf{clauses=[],nvars=0}  `shouldBe` False  -- should this be true??? 

    it "isConflict test 1" $ 
      isConflict [Just False] Cnf{clauses=[[p]],nvars=1} `shouldBe` True 

    it "isConflict test 2" $ 
      isConflict [Just False, Just True, Just True] Cnf{clauses=[[p,q],[r]],nvars=3}  `shouldBe` True     

    it "isConflict test 3" $ 
      isConflict [Just True, Just True, Nothing] Cnf{clauses=[[p],[r]],nvars=2}  `shouldBe` False     

    it "isConflict test 4" $ 
      isConflict [Nothing, Just True, Just True] Cnf{clauses=[[p,r],[q]],nvars=3}  `shouldBe` False 

    it "isConflict test 5" $ 
      isConflict [Nothing,Nothing,Just True] Cnf{clauses=[[p,q,r]],nvars=3}  `shouldBe` False      

-- Basic examples for isUnit
    it "isUnit test 0" $ 
      isUnit [] Cnf{clauses=[],nvars=0}  `shouldBe` Nothing -- should this be true??? 

    it "isUnit test 1" $ 
      isUnit [Just False] Cnf{clauses=[[p]],nvars=1} `shouldBe` Nothing

    it "isUnit test 2" $ 
      isUnit [Just False, Just True, Just True] Cnf{clauses=[[p,q],[r]],nvars=3}  `shouldBe` Nothing  

    it "isUnit test 3" $ 
      isUnit [Just True, Just True, Nothing] Cnf{clauses=[[p],[r]],nvars=2}  `shouldBe` Just r

    it "isUnit test 4" $ 
      isUnit [Nothing, Just True, Just True] Cnf{clauses=[[p,r],[q]],nvars=3}  `shouldBe` Just p

    it "isUnit test 5" $ 
      isUnit [Nothing,Nothing,Just True] Cnf{clauses=[[p,q,r]],nvars=3}  `shouldBe` Nothing  


-- Literals 
p = Lit {var = 1, value = True}
q = Lit {var = 2, value = True}
r = Lit {var = 3, value = False}

-- Basic clauses 
cnf1 = [[p]]
cnf2 = [[p,p]]
cnf3 = [[p],[p]]


