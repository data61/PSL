(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_nat_max_comm
imports Main Smart_Isabelle.Smart_Isabelle
begin

datatype Nat = Z | S "Nat"

fun le :: "Nat => Nat => bool" where
"le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

prove_by_preprocessed_abduction property0 :
  "((if le x y then y else x) = (if le y x then x else y))"
end
