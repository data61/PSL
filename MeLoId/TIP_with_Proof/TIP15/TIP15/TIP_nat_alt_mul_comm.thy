(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_nat_alt_mul_comm
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun altmul :: "Nat => Nat => Nat" where
"altmul (Z) y = Z"
| "altmul (S z) (Z) = Z"
| "altmul (S z) (S x2) =
     plus (plus (plus (S Z) (altmul z x2)) z) x2"

theorem property0 :
  "((altmul x y) = (altmul y x))"
  oops

end
