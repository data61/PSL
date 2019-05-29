(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_nat_acc_alt_mul_comm
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun accplus :: "Nat => Nat => Nat" where
"accplus (Z) y = y"
| "accplus (S z) y = accplus z (S y)"

fun accaltmul :: "Nat => Nat => Nat" where
"accaltmul (Z) y = Z"
| "accaltmul (S z) (Z) = Z"
| "accaltmul (S z) (S x2) =
     accplus (S z) (accplus x2 (accaltmul z x2))"

theorem property0 :
  "((accaltmul x y) = (accaltmul y x))"
  oops

end
