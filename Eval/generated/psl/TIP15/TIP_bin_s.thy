(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_bin_s
imports Main PSL.PSL
begin

datatype Bin = One | ZeroAnd "Bin" | OneAnd "Bin"

fun toNat :: "Bin => int" where
"toNat (One) = 1"
| "toNat (ZeroAnd xs) = (toNat xs) + (toNat xs)"
| "toNat (OneAnd ys) = (1 + (toNat ys)) + (toNat ys)"

fun s :: "Bin => Bin" where
"s (One) = ZeroAnd One"
| "s (ZeroAnd xs) = OneAnd xs"
| "s (OneAnd ys) = ZeroAnd (s ys)"

theorem property0 :
  "((toNat (s n)) = (1 + (toNat n)))"
  try_hard
  oops
end
