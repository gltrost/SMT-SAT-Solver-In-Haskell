module SAT where

import PROP
import Debug.Trace
import Control.Applicative
import Control.Monad

-- Compare each value of it's valuation in pval
-- Both must be the same truth-value OR both must be Nothing for this to come out True


isClauseSat :: Pval -> Clause -> Bool
isClauseSat pval clause = 
  case clause of 
    [] -> False  --why?
    Lit {var = v, value = val}  : xs ->
      if (Just val) == (pval !! (v-1)) then True -- Comment: why is ocaml code (val -1 )?? 
      else isClauseSat pval xs


-- previously ==? 
-- eqOpt compares two bool options a and b and returns True if they're both Nothing or the same option

eqOpt :: Maybe Bool -> Maybe Bool -> Bool
eqOpt a b = (a == b)

-- previously ==?? 
-- =?? returns True only when a and b are both not Nothing and also not-equal 
neqOpt :: Maybe Bool -> Maybe Bool -> Bool
neqOpt a b = if (a == Nothing) then False else (a == b)

 
-- previously ==??? 
eqOptOpt :: Maybe Lit -> Maybe Lit -> Bool
eqOptOpt a b = (a == b)

-- Compare each value of it's valuation in pval 
-- Both must be the same truth-value OR both must be Nothing for this to come out True
isClauseSat :: Pval -> Clause -> Bool 
isClauseSat pval clause = 
  case c of 
    [] -> False  -- why? 
    x : xs -> 
      if (Just x.value) == (pval !! (x.var-1)) then True 
      else is_clause_sat pval xs

isClauseConflict :: Pval -> Clause -> Bool 
isClauseConflict pval clause = 
  case clause of 
    [] -> True
    x : xs -> 
      if (Just (not x.value)) == (pval !! (x.var-1)) then isClauseConflict pval xs 
      else False

-- note: "ghost" in "ghost cOld" was taken out 
isClauseUnitUnr :: Pval -> Clause -> Clause -> [Lit] -> [Lit]                     
isClauseUnitUnr pval clause cOld listlit  =                     
  case clause of 
    [] -> listlit
    x : xs -> 
      if Nothing == (pval !! (x.var-1)) then 
        isClauseUnitUnr pval xs cOld (x : listlit)
      else isClauseUnitUnr pval xs cOld listlit


isClauseUnitUnr2 :: Pval -> Clause -> [Lit]
isClauseUnitUnr2 pval clause = isClauseUnitUnr pval c c []

-- uses is_clause_sat, is_clause_conflict and isClauseUnitUnr2
-- to see if c is Satisfied, Conflicting, etc.. 
partialEvalClause :: Pval -> Clause -> ClauseStatus 
partialEvalClause pval clause = 
  if isClauseSat pval c then Satisfied
  else if isClauseConflict pval clause then Conflicting
  else
    (case isClauseUnitUnr2 pval clause of 
      [x] -> Unit x
      x : xs -> Unresolved)

--Functionality: checks all clauses in cnf of partialEvalClause 
--  to see if the cnf is Sat 
-- High-level: we iterate through the disjuncts that are in cnf.clauses 
--             we then case on each disjunct to see if it's satisfied using partialEvalClauses 
--               if any of the disjuncts isn't satisfied, we return False
--               if all the disjuncts are satisfied, we return True  

isSat' :: Pval -> Cnf -> Int -> Bool -> Bool
isSat' pval cnf index resultant = 
  if (index >= cnf.clauses) then resultant 
  else 
    case partialEvalClause pval (cnf.clauses !! index) of
    Satisfied -> isSat' pval cnf (index+1) resultant 
    _ -> isSat' pval cnf (index+1) False

isSat :: Pval -> Cnf -> Bool
isSat pval cnf = isSat' pval cnf 0 True

--checks all clauses in cnf of partialEvalClause 
  -- to see if the cnf is Conflict   
isConflict' :: Pval -> Cnf -> Bool -> Int -> Bool
isConflict' pval1 cnf1 resultant index = 
  if (index >= length cnf1.clauses) then resultant 
  else 
    case partialEvalClause pval1 (cnf1.clauses !! index) of
      Conflicting -> resultant := isConflict' pval1 cnf1 True (index + 1)   
      _ -> isConflict' pval1 cnf1 resultant (index + 1)   
 
isConflict :: Pval -> Cnf -> Bool 
isConflict pval cnf = isConflict' pval cnf False 0

--checks all clauses in cnf of partialEvalClause 
--  to see if the cnf is Unit_clause   
isUnit' :: Pval -> Cnf -> Maybe Lit -> Int -> Maybe Lit 
isUnit' pval1 cnf1 =
  if (index >= length cnf1.clauses) then resultant   
  else  
    case partialEvalClause pval1 (cnf1.clauses !! index) of
      Unit x -> isUnit' pval1 cnf1 (Just x) (index + 1)
      _ -> isUnit' pval1 cnf1  (Just x) (index + 1)

isUnit :: Pval -> Cnf -> Maybe Lit -> Int -> Maybe Lit 
isUnit pval cnf1 = isUnit' pval cnf1 Nothing 0 
  

-- uses isSat, isConflicting and is_Unit
--   to see if cnf is either Sat, Conflicting, Unit_clause or Other..   
partialEvalCnf :: Pval -> Cnf -> CnfStatus 
partialEvalCnf pval1 cnf1  =
  if isSat pval1 cnf1 then Sat 
  else
    if isConflict pval1 cnf1 then  Conflict 
    else
      case is_Unit pval1 cnf1 of
        Nothing -> Other
        Just x ->  Unit_clause x
       
     
-- ****************************************************************************
-- Backtracking mechanism for partial valuations                              
-- ****************************************************************************

backtrack (diff: int list) (pval1: ((bool) option) array) : unit =
   case diff of
    [] -> ()
    x : xs ->  (Array.set pval1 x Nothing); backtrack xs pval1 
  

exception Sat_found

-- Finds a lit in c that is assigned to Nothing in pval  
find_unassigned_clause (pval1: ((bool) option) array) (c: lit list) :
  lit option =
   case c of
    [] -> Nothing
    x : xs ->
    if eqOpt (Array.get pval1 x.var) Nothing then  Just x 
    else
      find_unassigned_clause pval1 xs 
    

-- Finds a lit in cnf that is assigned to Nothing in pval  
let find_unassigned (pval1: ((bool) option) array) (cnf1: cnf) : lit option =
  let i = ref 0 in
  let newlit = ref Nothing in  
    while (!i < (Array.length (cnf1.clauses))) && (eqOptOpt (!newlit) Nothing) do      
         case find_unassigned_clause pval1 (Array.get (cnf1.clauses) !i) of
        | Nothing -> ()
        | Just x -> newlit := (Just x)
         let new_i = (!i) + 1 in i := new_i       
    !newlit
  


-- ****************************************************************************
-- Unit clause propagation                                                    
-- ****************************************************************************


pre_setAndPropagate (l: lit) (pval: ((bool) option) array) (cnf: cnf)
               (listvar: int list) : (bool) * (int list) =
    Array.set pval l.var (Just (l.value));
     case partialEvalCnf pval cnf of
    | Sat -> raise Sat_found
    | Conflict -> (True, listvar)
    | Unit_clause n -> pre_setAndPropagate n pval cnf ((n.var) :: listvar)
    | Other ->
       case find_unassigned pval cnf of
      | Nothing -> raise Sat_found
      | Just x -> pre_setAndPropagate x pval cnf listvar
      
    
  

let setAndPropagate (l: lit) (pval: ((bool) option) array) (cnf: cnf) : 
  (bool) * (int list) = pre_setAndPropagate l pval cnf []

-- ****************************************************************************
-- Improvements to your SAT solver (choose at least one of the following list)
-- - Pure literal rule                                                        
-- - Failed literal rule                                                      
-- - Probing                                                                  
-- - Adding clauses via resolution                                            
-- - Variable elimination                                                     
-- - Adjacency data structures                                                
-- ****************************************************************************

is_in_pos (l: lit) (c: lit list) : bool =
   case c of
    [] -> True
    x : xs ->
    if ((x.var) == (l.var)) && (not (x.value)) then  False 
    else    
      is_in_pos l xs 
    

-- ****************************************************************************
-- Main algorithm for transforming a formula                                  
-- pval_to_val                                                                
-- cnf_status                                                                 
-- dpll                                                                       
-- sat                                                                        
-- ****************************************************************************


let pval_to_val (pval: ((bool) option) array) : ((bool) array) option =
  let values = Array.make (Array.length pval) False in
    let o = (Array.length pval) in
    let o1 = 0 in
    for_loop_to index = if index < o then 
       case (Array.get pval index) of
      | Just x -> values.(index) <- x
      | Nothing -> values.(index) <- False
       for_loop_to (index + 1)  in for_loop_to o1;
    Just values
  

-- takes in a pval and cnf and gives us 
let cnf_status (pval: ((bool) option) array) (cnf: cnf) : (bool) * (((bool) array) option) =
   case partialEvalCnf pval cnf of
  | Sat -> (True, pval_to_val pval)
  | Conflict -> (False, Nothing)
  | Unit_clause a ->
     case setAndPropagate a pval cnf of
    | (True, l) -> (False, Nothing)
    | (False, _) -> (True, pval_to_val pval)
  | Other -> (False, pval_to_val pval)
  

dpll (cnf_nvars : int) (pval: ((bool) option) array) (cnf: cnf) : ((bool) array) option = 
    Array.set pval (cnf_nvars - 1) (Just True);                      -- Set a certain var in pval to Just True 
     case (cnf_status pval cnf) of
    | (True, Just x) ->  Just x            -- cnf is Sat and we return stripped-pval 
    | (False, Just x) -> dpll (cnf_nvars - 1) pval cnf                                   -- cnf is unresolved and we keep going 
    | (False, Nothing) ->     -- cnf can't be Sat of current configuration 
         pval.(cnf_nvars - 1) <- (Just False);                        -- Set a certain var in pval to Just True 
         case cnf_status pval cnf of
        | (True, Just x) ->  Just x         -- cnf is Sat and we return stripped-pval 
        | (False, Just x) -> dpll (cnf_nvars - 1) pval cnf                                 -- cnf is unresolved and we keep going 
        | (False, Nothing) -> Nothing            -- cnf can't be Sat of current configuration 
        | _ -> assert False -- absurd 
    | _ ->  assert False -- absurd 
    

-- Notes: note that cnf.nvars will always be one greater than the length of pval 
let sat (cnf: cnf) : ((bool) array) option =
  let pval =    print_cnf cnf;
                print_int cnf.nvars ; 
                print_string " \n" ; 
                Array.make (cnf.nvars) Nothing in
  dpll (cnf.nvars) pval cnf