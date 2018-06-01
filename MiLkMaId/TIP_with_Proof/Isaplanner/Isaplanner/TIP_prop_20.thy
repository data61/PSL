(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_20
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun len :: "'a list => Nat" where
  "len (nil2) = Z"
| "len (cons2 y xs) = S (len xs)"

fun t2 :: "Nat => Nat => bool" where
  "t2 (Z) y = True"
| "t2 (S z) (Z) = False"
| "t2 (S z) (S x2) = t2 z x2"

fun insort :: "Nat => Nat list => Nat list" where
  "insort x (nil2) = cons2 x (nil2)"
| "insort x (cons2 z xs) =
     (if t2 x z then cons2 x (cons2 z xs) else cons2 z (insort x xs))"

fun sort :: "Nat list => Nat list" where
  "sort (nil2) = nil2"
| "sort (cons2 y xs) = insort y (sort xs)"

theorem property0 :
  "((len (sort xs)) = (len xs))"
  oops

end