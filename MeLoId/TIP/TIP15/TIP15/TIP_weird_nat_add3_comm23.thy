(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_weird_nat_add3_comm23
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

theorem property0 :
  "((add3 x y z) = (add3 x z y))"
  oops

end
