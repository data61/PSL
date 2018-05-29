(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_nat_pow_one
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun times :: "Nat => Nat => Nat" where
"times (Z) y = Z"
| "times (S z) y = plus y (times z y)"

fun formulapow :: "Nat => Nat => Nat" where
"formulapow x (Z) = S Z"
| "formulapow x (S z) = times x (formulapow x z)"

theorem property0 :
  "((formulapow (S Z) x) = (S Z))"
  oops

end
