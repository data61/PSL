(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_63
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun len :: "'a list => Nat" where
  "len (nil2) = Z"
| "len (cons2 y xs) = S (len xs)"

fun last :: "Nat list => Nat" where
  "last (nil2) = Z"
| "last (cons2 y (nil2)) = y"
| "last (cons2 y (cons2 x2 x3)) = last (cons2 x2 x3)"

fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
| "drop (S z) (nil2) = nil2"
| "drop (S z) (cons2 x2 x3) = drop z x3"

fun t2 :: "Nat => Nat => bool" where
  "t2 x (Z) = False"
| "t2 (Z) (S z) = True"
| "t2 (S x2) (S z) = t2 x2 z"

theorem property0 :
  "((t2 n (len xs)) ==> ((last (drop n xs)) = (last xs)))"
  oops

end
