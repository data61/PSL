(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_bin_nat_times
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

datatype Bin = One | ZeroAnd "Bin" | OneAnd "Bin"

fun s :: "Bin => Bin" where
"s (One) = ZeroAnd One"
| "s (ZeroAnd xs) = OneAnd xs"
| "s (OneAnd ys) = ZeroAnd (s ys)"

fun plus2 :: "Bin => Bin => Bin" where
"plus2 (One) y = s y"
| "plus2 (ZeroAnd z) (One) = s (ZeroAnd z)"
| "plus2 (ZeroAnd z) (ZeroAnd ys) = ZeroAnd (plus2 z ys)"
| "plus2 (ZeroAnd z) (OneAnd xs) = OneAnd (plus2 z xs)"
| "plus2 (OneAnd x2) (One) = s (OneAnd x2)"
| "plus2 (OneAnd x2) (ZeroAnd zs) = OneAnd (plus2 x2 zs)"
| "plus2 (OneAnd x2) (OneAnd ys2) = ZeroAnd (s (plus2 x2 ys2))"

fun times :: "Bin => Bin => Bin" where
"times (One) y = y"
| "times (ZeroAnd xs1) y = ZeroAnd (times xs1 y)"
| "times (OneAnd xs12) y = plus2 (ZeroAnd (times xs12 y)) y"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun times2 :: "Nat => Nat => Nat" where
"times2 (Z) y = Z"
| "times2 (S z) y = plus y (times2 z y)"

fun toNat :: "Bin => Nat" where
"toNat (One) = S Z"
| "toNat (ZeroAnd xs) = plus (toNat xs) (toNat xs)"
| "toNat (OneAnd ys) = plus (plus (S Z) (toNat ys)) (toNat ys)"

theorem property0 :
  "((toNat (times x y)) = (times2 (toNat x) (toNat y)))"
  oops

end
