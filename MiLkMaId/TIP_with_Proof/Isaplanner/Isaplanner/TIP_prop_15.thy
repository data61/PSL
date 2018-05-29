(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_15
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun len :: "'a list => Nat" where
"len (nil2) = Z"
| "len (cons2 y xs) = S (len xs)"

fun t2 :: "Nat => Nat => bool" where
"t2 x (Z) = False"
| "t2 (Z) (S z) = True"
| "t2 (S x2) (S z) = t2 x2 z"

fun ins :: "Nat => Nat list => Nat list" where
"ins x (nil2) = cons2 x (nil2)"
| "ins x (cons2 z xs) =
     (if t2 x z then cons2 x (cons2 z xs) else cons2 z (ins x xs))"

theorem property0 :
  "((len (ins x xs)) = (S (len xs)))"
  oops

end
