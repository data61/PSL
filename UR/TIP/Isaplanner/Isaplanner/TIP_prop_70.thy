(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_70
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun t2 :: "Nat => Nat => bool" where
  "t2 (Z) y = True"
| "t2 (S z) (Z) = False"
| "t2 (S z) (S x2) = t2 z x2"

theorem property0 :
  "((t2 m n) ==> (t2 m (S n)))"
  oops

end
