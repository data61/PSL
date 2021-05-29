(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_mod_same
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun minus :: "Nat => Nat => Nat" where
"minus (Z) y = Z"
| "minus (S z) (S y2) = minus z y2"

fun lt :: "Nat => Nat => bool" where
"lt x (Z) = False"
| "lt (Z) (S z) = True"
| "lt (S n) (S z) = lt n z"

(*fun did not finish the proof*)
function mod2 :: "Nat => Nat => Nat" where
"mod2 x (Z) = Z"
| "mod2 x (S z) =
     (if lt x (S z) then x else mod2 (minus x (S z)) (S z))"
by pat_completeness auto

fun go :: "Nat => Nat => Nat => Nat" where
"go x y (Z) = Z"
| "go (Z) (Z) (S x2) = Z"
| "go (Z) (S x5) (S x2) = minus (S x2) (S x5)"
| "go (S x3) (Z) (S x2) = go x3 x2 (S x2)"
| "go (S x3) (S x4) (S x2) = go x3 x4 (S x2)"

fun modstructural :: "Nat => Nat => Nat" where
"modstructural x y = go x Z y"

theorem property0 :
  "((mod2 m n) = (modstructural m n))"
  oops

end
