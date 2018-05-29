(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_17
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun x :: "Nat => Nat => bool" where
"x (Z) (Z) = True"
| "x (Z) (S z2) = False"
| "x (S x2) (Z) = False"
| "x (S x2) (S y2) = x x2 y2"

fun t2 :: "Nat => Nat => bool" where
"t2 (Z) z = True"
| "t2 (S z2) (Z) = False"
| "t2 (S z2) (S x2) = t2 z2 x2"

theorem property0 :
  "((t2 n Z) = (x n Z))"
  oops

end
