(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_nat_min_max_distrib
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun le :: "Nat => Nat => bool" where
"le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

theorem property0 :
  "((let y2 :: Nat = (if le y z then y else z)
     in (if le x y2 then y2 else x)) =
      (if le x z then
         (let x3 :: Nat = (if le x y then y else x)
          in % (y4 :: Nat) => (if le x3 y4 then x3 else y4))
         z
         else
         (let x2 :: Nat = (if le x y then y else x)
          in % (y3 :: Nat) => (if le x2 y3 then x2 else y3))
         x))"
  oops

end
