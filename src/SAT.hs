module SAT where

import PROP
-- import Debug.Trace
-- import Control.Applicative
-- import Control.Monad

-- Compare 
-- Both must be the same truth-value OR both must be Nothing for this to come out True
--             [Maybe Bool] -> [(Int,Bool)] -> Bool
isClauseSat :: Pval -> Clause -> Bool
isClauseSat pval clause = 
  case clause of 
    [] -> False  --why?
    Lit {var = v, value = val}  : xs ->
      if (Just val) == (pval !! (v-1)) then True -- Comment: why is ocaml code (val -1 )?? 
      else isClauseSat pval xs


-- previously ==?? 
-- =?? returns True only when a and b are both not Nothing and also not-equal 
neqOpt :: Maybe Bool -> Maybe Bool -> Bool
neqOpt a b = if (a == Nothing || b == Nothing) then False else not (a == b)

--                 [Maybe Bool] -> [(Int,Bool)]
isClauseConflict :: Pval -> Clause ->  Bool 
isClauseConflict pval clause = 
  case clause of 
    [] -> True  
    Lit{var=var,value = val} : xs -> 
      let xPval = pval !! (var-1) in 
        if (xPval == Nothing) then False 
        else 
          if (Just (not val) == xPval) then isClauseConflict pval xs
          else False 

isClauseUnitUnr :: Pval -> Clause  -> [Lit]                     
isClauseUnitUnr pval clause  =             
  case clause of 
    [] -> []
    Lit{var=var,value = val} : xs -> 
      let result = isClauseUnitUnr pval xs in 
        if Nothing == pval !! (var-1) then Lit{var=var,value = val} : result 
        else result 

-- uses is_clause_sat, is_clause_conflict and isClauseUnitUnr
-- to see if c is Satisfied, Conflicting, Unit x or Unresolved 
partialEvalClause :: Pval -> Clause -> ClauseStatus 
partialEvalClause pval clause = 
  if isClauseSat pval clause then Satisfied
  else if isClauseConflict pval clause then Conflicting
  else
    (case isClauseUnitUnr pval clause of 
      [x] -> Unit x
      _ -> Unresolved)

-- Functionality: checks all clauses in cnf of partialEvalClause 
-- to see if the cnf is Sat 
-- High-level: 
--   we iterate through the disjuncts that are in cnf.clauses 
--   we apply partialEvalClauses to each disjunct to see if it's Satisfied  
--   if any of the disjuncts isn't Satisfied, we return False
--   if all the disjuncts are Satisfied, we return True  

isSat' :: Pval -> Cnf -> Int -> Bool -> Bool
isSat' pval Cnf {clauses = cls, nvars = nvs} idx result =  
  if (idx >= length cls) then result 
  else 
    case (partialEvalClause pval (cls !! idx)) of
      Satisfied -> isSat' pval Cnf {clauses = cls, nvars = nvs} (idx+1) result 
      _ ->  False

-- isSat :: Pval -> Cnf -> Bool
isSat pval cnf = isSat' pval cnf 0 True

--checks all clauses in cnf of partialEvalClause 
  -- to see if the cnf is Conflict   
isConflict' :: Pval -> Cnf -> Bool -> Int -> Bool
isConflict' pval cnf resultant index =  error "Not yet implemented"
  -- if (index >= length cnf.clauses) then resultant 
  -- else 
  --   case partialEvalClause pval ((cnf.clauses) !! index) of
  --     Conflicting ->  isConflict' pval cnf True (index + 1)   
  --     _ -> isConflict' pval cnf resultant (index + 1)   
 
isConflict :: Pval -> Cnf -> Bool 
isConflict pval cnf = isConflict' pval cnf False 0

--checks all clauses in cnf of partialEvalClause 
--  to see if the cnf is UnitClause   
isUnit' :: Pval -> Cnf -> Maybe Lit -> Int -> Maybe Lit 
isUnit' pval cnf resultant index = error "Not yet implemented"
  -- if (index >= length cnf.clauses) then resultant   
  -- else  
  --   case partialEvalClause pval ((cnf.clauses) !! index) of
  --     Unit x -> isUnit' pval cnf (Just x) (index + 1)
  --     _ -> isUnit' pval cnf  resultant (index + 1)

isUnit :: Pval -> Cnf -> Maybe Lit -> Int -> Maybe Lit 
isUnit pval cnf =  error "Not yet implemented"
	-- isUnit' pval cnf Nothing 0 
  

-- uses isSat, isConflicting and is_Unit
--   to see if cnf is either Sat, Conflicting, UnitClause or Other..   
partialEvalCnf :: Pval -> Cnf -> CnfStatus 
partialEvalCnf pval cnf  = error "Not yet implemented"
  -- if isSat pval cnf then Sat 
  -- else
  --   if isConflict pval cnf then  Conflict 
  --   else
  --     case isUnit pval cnf of
  --       Nothing -> Other
  --       Just x ->  UnitClause x
       
     
-- ****************************************************************************
-- Backtracking mechanism for partial valuations                              
-- ****************************************************************************

--           [Int] ->  [Maybe Bool] -> [Maybe Bool]
-- backtrack :: [Int] ->  Pval         -> Pval 
backtrack diff pval = error "Not yet implemented"
--    case pval of
--     [] -> []
--     x : xs -> 
--       let rest = backtrack diff xs in 
--         if (x `elem` diff) then Nothing : rest
--         else x : rest 



-- Finds a lit in c that is assigned to Nothing in pval  
findUnassignedClause :: Pval -> [Lit] -> Maybe Lit 
findUnassignedClause pval c =  error "Not yet implemented"
  -- case c of
  --   [] -> Nothing
  --   x : xs ->
  --     if  (pval !! (x.var)) == Nothing then Just x 
  --     else findUnassignedClause pval xs 
    

-- Finds a lit in cnf that is assigned to Nothing in pval  
findUnassigned' :: Pval -> Cnf -> Int -> Maybe a -> Maybe Lit 
findUnassigned' pval cnf i newlit = error "Not yet implemented"
  -- if (i >= (length (cnf.clauses)) || newlit == Nothing) then newlit
  -- else   
  --   case findUnassignedClause pval ((cnf.clauses) !! i) of
  --     Nothing -> Nothing  
  --     Just x ->  findUnassigned' pval cnf i+1 (Just x)
  
findUnassigned :: Pval -> Cnf -> Maybe Lit
findUnassigned pval cnf  = findUnassigned' pval cnf 0 Nothing 

-- ****************************************************************************
-- Unit clause propagation                                                    
-- ****************************************************************************
listSet :: Eq a => [a] -> a -> a -> [a]
listSet (z:zs) x y  = 
  if z == x then y : zs 
  else listSet zs x y

preSetAndPropagate :: Lit -> Pval -> Cnf -> [Int] -> (Bool,[Int]) 
preSetAndPropagate l pval cnf listvar =  error "Not yet implemented"
  -- case partialEvalCnf pval cnf of
  --   Sat -> error "Sat_found"
  --   Conflict -> (True, listvar)
  --   UnitClause n -> preSetAndPropagate n pval cnf ((n.var) : listvar)
  --   Other ->
  --     case findUnassigned pval cnf of
  --       Nothing -> error "Sat_found"
  --       Just x -> preSetAndPropagate x pval cnf listvar
    
--          (Int,Bool) -> [Maybe Bool] -> [([(Int,Bool)],Int)] -> (Bool,[Int])    
setAndPropagate :: Lit -> Pval         -> Cnf                  -> (Bool,[Int])
setAndPropagate l pval cnf  =  error "Not yet implemented"
  -- let g = listSet pval (pval !! (l.var)) (Just (l.value)) in
  -- preSetAndPropagate l g cnf []


-- ****************************************************************************
-- Improvements to your SAT solver (choose at least one of the following list)
-- - Pure literal rule                                                        
-- - Failed literal rule                                                      
-- - Probing                                                                  
-- - Adding clauses via resolution                                            
-- - Variable elimination                                                     
-- - Adjacency data structures                                                
-- ****************************************************************************

isInPos :: Lit -> [Lit] -> Bool
isInPos l c =  error "Not yet implemented"
  -- case c of
  --   [] -> True
  --   x : xs ->
  --     if ((x.var) == (l.var)) && (not (x.value)) then False 
  --     else isInPos l xs 

-- ****************************************************************************
-- Main algorithm for transforming a formula                                  
-- pvalToVal                                                                
-- cnfStatus                                                                 
-- dpll                                                                       
-- sat                                                                        
-- ****************************************************************************

-- pvalToVal :: Pval -> Maybe [Bool] =
-- pvalToVal pval values o o1 =
--   forLoopTo index = if index < o then 
--     case (Array.get pval index) of
--       Just x -> values.(index) <- x
--       Nothing -> values.(index) <- False
--       forLoopTo (index + 1) in forLoopTo o1;
--     Just values    

-- pvalToVal :: Pval -> Maybe [Bool] =
-- pvalToVal pval = pvalToVal' pval (take (length pval) (repeat False)) (length pval) 0

-- takes in a pval and cnf and gives us 
cnfStatus :: Pval -> Cnf -> (Bool, Maybe [Bool])
cnfStatus pval cnf = error "Not yet implemented"
  -- case partialEvalCnf pval cnf of
  --   Sat -> (True, pvalToVal pval)
  --   Conflict -> (False, Nothing)
  --   UnitClause a ->
  --     case setAndPropagate a pval cnf of
  --       (True, l) -> (False, Nothing)
  --       (False, _) -> (True, pvalToVal pval)
  --   Other -> (False, pvalToVal pval)
  
dpll :: Int -> [Maybe Bool] -> Cnf -> [Maybe Bool]
dpll cnf_nvars pval cnf =  error "Not yet implemented"
  -- let gggg = listSet pval (cnf.(nvars - 1)) (Just True) in  					 -- Set a certain var in pval to Just True 
  --   case (cnfStatus gggg cnf) of
  --     (True, Just x) ->  Just x    																	 -- cnf is Sat and we return stripped-gggg 
  --     (False, Just x) -> dpll (cnf_nvars - 1) gggg cnf  						 -- cnf is unresolved and we keep going 
  --     (False, Nothing) ->    																				 -- cnf can't be Sat of current configuration 
  --       (let newPval = listSet pval.(cnf_nvars - 1) Just False in 	 -- Set a certain var in pval to Just True 
  --       case (cnfStatus, newPval) cnf of
  --         (True, Just x) ->  Just x   															 -- cnf is Sat and we return stripped-newPval 
  --         (False, Just x) -> dpll (cnf_nvars - 1) newPval cnf    		 -- cnf is unresolved and we keep going 
  --         (False, Nothing) -> Nothing  															 -- cnf can't be Sat of current configuration 
  --         _ -> error "Absurd")																			 -- absurd 
  --     _ ->  error "Absurd"																					 -- absurd 
    

-- Notes: note that cnf.nvars will always be one greater than the length of pval 
sat :: Cnf -> Maybe [Bool]
sat cnf = error "Not yet implemented"
  -- let pval = take (cnf.nvars) (cycle Nothing) in
  -- dpll (cnf.nvars) pval cnf