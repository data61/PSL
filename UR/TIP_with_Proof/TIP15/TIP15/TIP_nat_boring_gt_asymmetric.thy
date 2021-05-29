(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_nat_boring_gt_asymmetric
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun lt :: "Nat => Nat => bool" where
"lt x (Z) = False"
| "lt (Z) (S z) = True"
| "lt (S n) (S z) = lt n z"

fun gt :: "Nat => Nat => bool" where
"gt x y = lt y x"

theorem property0 :
  "((gt x y) ==> (~ (gt y x)))"
  oops

end
