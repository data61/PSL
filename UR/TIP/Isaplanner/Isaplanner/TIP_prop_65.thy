(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_65
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun t22 :: "Nat => Nat => Nat" where
  "t22 (Z) y = y"
| "t22 (S z) y = S (t22 z y)"

fun t2 :: "Nat => Nat => bool" where
  "t2 x (Z) = False"
| "t2 (Z) (S z) = True"
| "t2 (S x2) (S z) = t2 x2 z"

theorem property0 :
  "t2 i (S (t22 m i))"
  oops

end
