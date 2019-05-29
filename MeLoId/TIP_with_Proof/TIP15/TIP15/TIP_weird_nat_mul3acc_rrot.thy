(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_weird_nat_mul3acc_rrot
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun add3acc :: "Nat => Nat => Nat => Nat" where
  "add3acc (Z) (Z) z = z"
| "add3acc (Z) (S x3) z = add3acc Z x3 (S z)"
| "add3acc (S x2) y z = add3acc x2 (S y) z"

fun mul3acc :: "Nat => Nat => Nat => Nat" where
  "mul3acc (Z) y z = Z"
| "mul3acc (S x2) (Z) z = Z"
| "mul3acc (S x2) (S x3) (Z) = Z"
| "mul3acc (S x2) (S x3) (S x4) =
     (let fail :: Nat =
       plus
         (S Z)
         (add3acc
            (mul3acc x2 x3 x4)
            (add3acc
               (mul3acc (S Z) x3 x4) (mul3acc x2 (S Z) x4) (mul3acc x2 x3 (S Z)))
            (add3acc (S x2) (S x3) (S x4)))
     in (if (x2 = Z) then
           (if (x3 = Z) then (if (x4 = Z) then S Z else fail) else fail)
           else
           fail))"

theorem property0 :
  "((mul3acc x y z) = (mul3acc z x y))"
  oops

end
