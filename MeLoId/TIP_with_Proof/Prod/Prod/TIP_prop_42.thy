(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_42
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun y :: "Nat => Nat => bool" where
  "y (Z) (Z) = True"
| "y (Z) (S z2) = False"
| "y (S x2) (Z) = False"
| "y (S x2) (S y22) = y x2 y22"

fun x :: "bool => bool => bool" where
  "x True y2 = True"
| "x False y2 = y2"

fun elem :: "Nat => Nat list => bool" where
  "elem z (nil2) = False"
| "elem z (cons2 z2 xs) = x (y z z2) (elem z xs)"

fun union :: "Nat list => Nat list => Nat list" where
  "union (nil2) y2 = y2"
| "union (cons2 z2 xs) y2 =
     (if elem z2 y2 then union xs y2 else cons2 z2 (union xs y2))"

theorem property0 :
  "((elem z y2) ==> (elem z (union y2 z2)))"
  oops

end
