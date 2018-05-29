(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_66
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun len :: "'a list => Nat" where
"len (nil2) = Z"
| "len (cons2 y xs) = S (len xs)"

fun filter :: "('a => bool) => 'a list => 'a list" where
"filter x (nil2) = nil2"
| "filter x (cons2 z xs) =
     (if x z then cons2 z (filter x xs) else filter x xs)"

fun t2 :: "Nat => Nat => bool" where
"t2 (Z) y = True"
| "t2 (S z) (Z) = False"
| "t2 (S z) (S x2) = t2 z x2"

theorem property0 :
  "t2 (len (filter p xs)) (len xs)"
  oops

end
