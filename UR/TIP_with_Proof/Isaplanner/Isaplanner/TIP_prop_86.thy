(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_86
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "Nat => Nat => bool" where
"x (Z) (Z) = True"
| "x (Z) (S z2) = False"
| "x (S x2) (Z) = False"
| "x (S x2) (S y2) = x x2 y2"

fun elem :: "Nat => Nat list => bool" where
"elem y (nil2) = False"
| "elem y (cons2 z2 xs) = (if x y z2 then True else elem y xs)"

fun t2 :: "Nat => Nat => bool" where
"t2 y (Z) = False"
| "t2 (Z) (S z2) = True"
| "t2 (S x2) (S z2) = t2 x2 z2"

fun ins :: "Nat => Nat list => Nat list" where
"ins y (nil2) = cons2 y (nil2)"
| "ins y (cons2 z2 xs) =
     (if t2 y z2 then cons2 y (cons2 z2 xs) else cons2 z2 (ins y xs))"

theorem property0 :
  "((t2 y z) ==> ((elem y (ins z xs)) = (elem y xs)))"
  oops

end
