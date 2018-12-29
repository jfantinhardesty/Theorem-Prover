module Proof where

data Formula = Var String | Bottom | Implies Formula Formula | Not Formula | And Formula Formula | Or Formula Formula deriving (Eq,Show)

data Sequent = S ([Formula],[Formula]) deriving Show

-- is there a formula in both lists m and n that satisfies predicate p?
exists p m n = foldl (\b x -> any (p x) n) False m

isNot phi = case phi of
                   (Not p) -> True
                   _ -> False

isImplies phi = case phi of
                   (Implies p q) -> True
                   _ -> False
                   
isOr phi = case phi of
                   (Or p q) -> True
                   _ -> False
                   
isAnd phi = case phi of
                   (And p q) -> True
                   _ -> False

find p [] = error "find: not found"
find p (x:xs) = if p x then x else find p xs

delete x [] = []
delete x (y:ys) = if x == y then ys else y: (delete x ys)

data DerivationStatus = Valid | Partial [Sequent] | Failed [(String,Bool)] deriving Show

oneStep (S (gamma,delta))
    -- Axiom Rule Applies
    | exists (\x -> (== x)) gamma delta = Valid                    

    -- Bottom left Axiom
    | any (== Bottom) gamma = Valid

    -- (=> Left) Rule
    | any isImplies gamma = 
              let (phi `Implies` psi) = find isImplies gamma 
                  gamma' = delete (phi `Implies` psi) gamma 
              in 
                  Partial [S(gamma',phi:delta), S(psi:gamma',delta)] 

    -- (=> Right) Rule
    | any isImplies delta = 
              let  (phi `Implies` psi) = find isImplies delta
                   delta' = delete (phi `Implies` psi) delta
              in 
                  Partial [S(phi:gamma,psi:delta')] 
 
    -- Not Left Rule
    | any isNot gamma = 
              let (Not phi) = find isNot gamma
                  gamma' = delete (Not phi) gamma 
              in
                   Partial[S(gamma', phi:delta)]
    -- Not Right
    | any isNot delta = 
              let (Not phi) = find isNot delta
                  delta' = delete (Not phi) delta 
              in
                   Partial[S(phi : gamma, delta')]
                   
    -- (Or Left) Rule
    | any isOr gamma = 
              let (phi `Or` psi) = find isOr gamma 
                  gamma' = delete (phi `Or` psi) gamma 
              in 
                  Partial [S(phi:gamma',delta), S(gamma',psi:delta)] 
    
    -- (Or Right) Rule
    | any isOr delta = 
              let  (phi `Or` psi) = find isOr delta
                   delta' = delete (phi `Or` psi) delta
              in 
                  Partial [S(gamma,phi:(psi:delta'))]

    -- (And Left) Rule
    | any isAnd gamma = 
              let (phi `And` psi) = find isAnd gamma 
                  gamma' = delete (phi `And` psi) gamma 
              in 
                  Partial [S(phi:(psi:gamma'),delta)] 
    
    -- (And Right) Rule
    | any isAnd delta = 
              let  (phi `And` psi) = find isAnd delta
                   delta' = delete (phi `And` psi) delta
              in 
                  Partial [S(delta',phi:delta), S(delta',psi:delta)] 
                  
    -- no rule applies
    | otherwise = let build_assign value p = 
                            case p of 
                               (Var x) -> (x,value) 
                               _ -> error "oneStep: should never happen?"  
                  in
                       Failed ((map (build_assign True) gamma)  ++ (map (build_assign False) delta))
                      

prove [] = Valid
prove [S([],[])] = Failed []
prove (seq:seqs) = 
      case (oneStep seq) of
          Valid -> prove seqs
          (Partial subgoals) ->  prove (subgoals ++ seqs)
          (Failed s) -> Failed s


--- Test
--- prove ([S ([Implies (Var "a") (Var "b")], [Or (Not (Var "a")) (Var "b")])])
--- prove ([S ([Not (Or (Var "a") (Var "b"))], [And (Not (Var "a")) (Not (Var "b"))])])
--- prove ([S ([Implies (Var "a") (Var "a")], [Or (Not (Var "a")) (Var "a")])])