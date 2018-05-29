(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_nat_pow_le_factorial
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun times :: "Nat => Nat => Nat" where
"times (Z) y = Z"
| "times (S z) y = plus y (times z y)"

fun lt :: "Nat => Nat => bool" where
"lt x (Z) = False"
| "lt (Z) (S z) = True"
| "lt (S n) (S z) = lt n z"

fun formulapow :: "Nat => Nat => Nat" where
"formulapow x (Z) = S Z"
| "formulapow x (S z) = times x (formulapow x z)"

fun factorial :: "Nat => Nat" where
"factorial (Z) = S Z"
| "factorial (S y) = times (S y) (factorial y)"

theorem property0 :
  "lt
     (formulapow (S (S Z)) (plus (S (S (S (S Z)))) n))
     (factorial (plus (S (S (S (S Z)))) n))"
  oops

end
