(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_bin_nat_s
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

datatype Bin = One | ZeroAnd "Bin" | OneAnd "Bin"

fun s :: "Bin => Bin" where
"s (One) = ZeroAnd One"
| "s (ZeroAnd xs) = OneAnd xs"
| "s (OneAnd ys) = ZeroAnd (s ys)"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun toNat :: "Bin => Nat" where
"toNat (One) = S Z"
| "toNat (ZeroAnd xs) = plus (toNat xs) (toNat xs)"
| "toNat (OneAnd ys) = plus (plus (S Z) (toNat ys)) (toNat ys)"

theorem property0 :
  "((toNat (s n)) = (plus (S Z) (toNat n)))"
  oops

end
