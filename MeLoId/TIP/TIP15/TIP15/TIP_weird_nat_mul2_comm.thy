(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_weird_nat_mul2_comm
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

fun mul2 :: "Nat => Nat => Nat" where
"mul2 (Z) y = Z"
| "mul2 (S z) (Z) = Z"
| "mul2 (S z) (S x2) = plus (S Z) (add3acc z x2 (mul2 z x2))"

theorem property0 :
  "((mul2 x y) = (mul2 y x))"
  oops

end
