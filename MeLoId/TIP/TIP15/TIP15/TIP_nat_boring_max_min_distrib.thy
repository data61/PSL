(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_nat_boring_max_min_distrib
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun le :: "Nat => Nat => bool" where
"le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

theorem property0 :
  "((let y2 :: Nat = (if le y z then z else y)
     in (if le x y2 then x else y2)) =
      (if le x z then
         (let x3 :: Nat = (if le x y then x else y)
          in % (y4 :: Nat) => (if le x3 y4 then y4 else x3))
         x
         else
         (let x2 :: Nat = (if le x y then x else y)
          in % (y3 :: Nat) => (if le x2 y3 then y3 else x2))
         z))"
  oops

end
