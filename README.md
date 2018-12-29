# Theorem-Prover
Basic theorem prover developed in Haskell. Uses sequent calculus for proofs.

Here are some examples for running that all return Valid

prove ([S ([Implies (Var "a") (Var "b")], [Or (Not (Var "a")) (Var "b")])])

prove ([S ([Not (Or (Var "a") (Var "b"))], [And (Not (Var "a")) (Not (Var "b"))])])

prove ([S ([Implies (Var "a") (Var "a")], [Or (Not (Var "a")) (Var "a")])])
