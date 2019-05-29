(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_nat_pow_pow
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun times :: "Nat => Nat => Nat" where
"times (Z) y = Z"
| "times (S z) y = plus y (times z y)"

fun formulapow3 :: "Nat => Nat => Nat" where
"formulapow3 x (Z) = S Z"
| "formulapow3 x (S z) = times x (formulapow3 x z)"

fun formulapow2 :: "Nat => Nat => Nat" where
"formulapow2 x (Z) = S Z"
| "formulapow2 x (S z) = times x (formulapow2 x z)"

fun formulapow :: "Nat => Nat => Nat" where
"formulapow x (Z) = S Z"
| "formulapow x (S z) = times x (formulapow x z)"

theorem property0 :
  "((formulapow x (times y z)) = (formulapow2 (formulapow3 x y) z))"
  oops

end
