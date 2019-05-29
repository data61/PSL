(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_37
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

fun delete :: "Nat => Nat list => Nat list" where
"delete y (nil2) = nil2"
| "delete y (cons2 z2 xs) =
     (if x y z2 then delete y xs else cons2 z2 (delete y xs))"

theorem property0 :
  "(~ (elem y (delete y xs)))"
  oops

end
