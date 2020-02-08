{-# LANGUAGE TypeOperators #-}

module PROP
  ( Lit (..),
    Clause,
    Prop,
    (&),
    (\/),
    cShow,
    pShow,
    ClauseStatus,
    CnfStatus,
    Pval,
    Cnf) where

type Var = Int
data Lit = Lit {
  var :: Var, 
  value :: Bool } 
  deriving (Eq)
type Clause = [Lit]
type Prop = [Clause]

(&) :: Prop -> Prop -> Prop
a & b = a ++ b 

(\/) :: Clause -> Clause -> Clause
a \/ b = a ++ b

infixr 3 &
infixr 2 \/

instance Show Lit where
  show Lit {var = v, value = val} = 
    "(" ++ show v ++ "," ++ show val ++ ")"

cShow :: Clause -> String
cShow [] = ""
cShow [x] = show x
cShow (x : xs) = show x ++ " \\/ " ++ show xs 

pShow :: Prop -> String
pShow [] = ""
pShow [x] = cShow x
pShow (x : xs) = "(" ++ cShow x ++ ")" ++ " & " ++ pShow xs  



data ClauseStatus =
    Satisfied
  | Conflicting
  | Unit Lit 
  | Unresolved
  deriving (Eq,Show)

data CnfStatus =
    Sat
  | Conflict
  | Unit_clause Lit
  | Other   

data Cnf = Cnf {
  clauses :: [Clause],
  nvars :: Int} 

type Pval = [Maybe Bool] 
