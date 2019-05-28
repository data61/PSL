(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_weird_nat_mul3_assoc2
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun add3 :: "Nat => Nat => Nat => Nat" where
  "add3 (Z) (Z) z = z"
| "add3 (Z) (S x3) z = plus (S Z) (add3 Z x3 z)"
| "add3 (S x2) y z = plus (S Z) (add3 x2 y z)"

fun mul3 :: "Nat => Nat => Nat => Nat" where
  "mul3 (Z) y z = Z"
| "mul3 (S x2) (Z) z = Z"
| "mul3 (S x2) (S x3) (Z) = Z"
| "mul3 (S x2) (S x3) (S x4) =
     (let fail :: Nat =
       plus
         (S Z)
         (add3
            (mul3 x2 x3 x4)
            (add3 (mul3 (S Z) x3 x4) (mul3 x2 (S Z) x4) (mul3 x2 x3 (S Z)))
            (add3 x2 x3 x4))
     in (if (x2 = Z) then
           (if (x3 = Z) then (if (x4 = Z) then S Z else fail) else fail)
           else
           fail))"

theorem property0 :
  "((mul3 (mul3 x1 x2 x3) x4 x5) = (mul3 x1 (mul3 x2 x3 x4) x5))"
  oops

end
