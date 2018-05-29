(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_50
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = nil2"
| "take (S z) (nil2) = nil2"
| "take (S z) (cons2 x2 x3) = cons2 x2 (take z x3)"

fun len :: "'a list => Nat" where
  "len (nil2) = Z"
| "len (cons2 y xs) = S (len xs)"

fun butlast :: "'a list => 'a list" where
  "butlast (nil2) = nil2"
| "butlast (cons2 y (nil2)) = nil2"
| "butlast (cons2 y (cons2 x2 x3)) =
     cons2 y (butlast (cons2 x2 x3))"

fun t2 :: "Nat => Nat => Nat" where
  "t2 (Z) y = Z"
| "t2 (S z) (Z) = S z"
| "t2 (S z) (S x2) = t2 z x2"

theorem property0 :
  "((butlast xs) = (take (t2 (len xs) (S Z)) xs))"
  oops

end
