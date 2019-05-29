(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_68
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "Nat => Nat => bool" where
  "x (Z) (Z) = True"
| "x (Z) (S z2) = False"
| "x (S x2) (Z) = False"
| "x (S x2) (S y2) = x x2 y2"

fun len :: "'a list => Nat" where
  "len (nil2) = Z"
| "len (cons2 z xs) = S (len xs)"

fun delete :: "Nat => Nat list => Nat list" where
  "delete y (nil2) = nil2"
| "delete y (cons2 z2 xs) =
     (if x y z2 then delete y xs else cons2 z2 (delete y xs))"

fun t2 :: "Nat => Nat => bool" where
  "t2 (Z) z = True"
| "t2 (S z2) (Z) = False"
| "t2 (S z2) (S x2) = t2 z2 x2"

theorem property0 :
  "t2 (len (delete n xs)) (len xs)"
  oops

end
