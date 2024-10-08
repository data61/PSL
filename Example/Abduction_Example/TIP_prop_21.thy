(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_21
  imports Smart_Isabelle.Smart_Isabelle
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun rotate :: "Nat => 'a list => 'a list" where
  "rotate (Z) z = z"
| "rotate (S z2) (nil2) = nil2"
| "rotate (S z2) (cons2 x2 x3) =
     rotate z2 (x x3 (cons2 x2 (nil2)))"

fun length :: "'a list => Nat" where
  "length (nil2) = Z"
| "length (cons2 z xs) = S (length xs)"

prove property0 :
  "((rotate (length y) (x y z)) = (x z y))"

end
