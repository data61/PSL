(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_16
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun last :: "Nat list => Nat" where
  "last (nil2) = Z"
| "last (cons2 y (nil2)) = y"
| "last (cons2 y (cons2 x2 x3)) = last (cons2 x2 x3)"

theorem property0 :
  "((xs = (nil2)) ==> ((last (cons2 x xs)) = x))"
  find_proof DInd
  apply (induct)
   apply auto
  done 

end