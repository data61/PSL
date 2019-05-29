(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_nat_acc_alt_mul_same
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun times :: "Nat => Nat => Nat" where
"times (Z) y = Z"
| "times (S z) y = plus y (times z y)"

fun accplus :: "Nat => Nat => Nat" where
"accplus (Z) y = y"
| "accplus (S z) y = accplus z (S y)"

fun accaltmul :: "Nat => Nat => Nat" where
"accaltmul (Z) y = Z"
| "accaltmul (S z) (Z) = Z"
| "accaltmul (S z) (S x2) =
     accplus (S z) (accplus x2 (accaltmul z x2))"

theorem property0 :
  "((accaltmul x y) = (times x y))"
  oops

end
