(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_52
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun y :: "'a list => 'a list => 'a list" where
  "y (nil2) y2 = y2"
| "y (cons2 z2 xs) y2 = cons2 z2 (y xs y2)"

fun x :: "Nat => Nat => bool" where
  "x (Z) (Z) = True"
| "x (Z) (S z2) = False"
| "x (S x2) (Z) = False"
| "x (S x2) (S y22) = x x2 y22"

fun rev :: "'a list => 'a list" where
  "rev (nil2) = nil2"
| "rev (cons2 y2 xs) = y (rev xs) (cons2 y2 (nil2))"

fun count :: "Nat => Nat list => Nat" where
  "count z (nil2) = Z"
| "count z (cons2 z2 ys) =
     (if x z z2 then S (count z ys) else count z ys)"

theorem property0 :
  "((count n xs) = (count n (rev xs)))"
  oops

end