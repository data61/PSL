(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_22
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun max :: "Nat => Nat => Nat" where
"max (Z) y = y"
| "max (S z) (Z) = S z"
| "max (S z) (S x2) = S (max z x2)"

theorem property0 :
  "((max (max a b) c) = (max a (max b c)))"
  oops

end
