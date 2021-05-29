(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_weird_nat_add3acc_assoc3
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun add3acc :: "Nat => Nat => Nat => Nat" where
"add3acc (Z) (Z) z = z"
| "add3acc (Z) (S x3) z = add3acc Z x3 (S z)"
| "add3acc (S x2) y z = add3acc x2 (S y) z"

theorem property0 :
  "((add3acc x1 (add3acc x2 x3 x4) x5) =
      (add3acc x1 x2 (add3acc x3 x4 x5)))"
  oops

end
