(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_80
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun take :: "Nat => 'a list => 'a list" where
  "take (Z) z = nil2"
| "take (S z2) (nil2) = nil2"
| "take (S z2) (cons2 x2 x3) = cons2 x2 (take z2 x3)"

fun len :: "'a list => Nat" where
  "len (nil2) = Z"
| "len (cons2 z xs) = S (len xs)"

fun t2 :: "Nat => Nat => Nat" where
  "t2 (Z) z = Z"
| "t2 (S z2) (Z) = S z2"
| "t2 (S z2) (S x2) = t2 z2 x2"

theorem property0 :
  "((take n (x xs ys)) = (x (take n xs) (take (t2 n (len xs)) ys)))"
  oops

end
