(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_bin_nat_plus_assoc
imports "../../Test_Base"
begin

datatype Bin = One | ZeroAnd "Bin" | OneAnd "Bin"

fun s :: "Bin => Bin" where
"s (One) = ZeroAnd One"
| "s (ZeroAnd xs) = OneAnd xs"
| "s (OneAnd ys) = ZeroAnd (s ys)"

fun plus :: "Bin => Bin => Bin" where
"plus (One) y = s y"
| "plus (ZeroAnd z) (One) = s (ZeroAnd z)"
| "plus (ZeroAnd z) (ZeroAnd ys) = ZeroAnd (plus z ys)"
| "plus (ZeroAnd z) (OneAnd xs) = OneAnd (plus z xs)"
| "plus (OneAnd x2) (One) = s (OneAnd x2)"
| "plus (OneAnd x2) (ZeroAnd zs) = OneAnd (plus x2 zs)"
| "plus (OneAnd x2) (OneAnd ys2) = ZeroAnd (s (plus x2 ys2))"

theorem property0 :
  "((plus x (plus y z)) = (plus (plus x y) z))"
  oops

end
