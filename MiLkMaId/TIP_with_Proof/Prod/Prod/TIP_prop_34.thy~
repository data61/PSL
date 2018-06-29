(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_34
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun t2 :: "Nat => Nat => Nat" where
  "t2 (Z) y = y"
| "t2 (S z) y = S (t2 z y)"

fun t22 :: "Nat => Nat => Nat" where
  "t22 (Z) y = Z"
| "t22 (S z) y = t2 y (t22 z y)"

fun mult :: "Nat => Nat => Nat => Nat" where
  "mult (Z) y z = z"
| "mult (S x2) y z = mult x2 y (t2 y z)"

theorem property0 :
  "((t22 x y) = (mult x y Z))"
  oops

end
