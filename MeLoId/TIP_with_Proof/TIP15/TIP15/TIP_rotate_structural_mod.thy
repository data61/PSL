(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_rotate_structural_mod
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
"x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun rotate :: "Nat => 'a list => 'a list" where
"rotate (Z) z = z"
| "rotate (S z2) (nil2) = nil2"
| "rotate (S z2) (cons2 z22 xs1) =
     rotate z2 (x xs1 (cons2 z22 (nil2)))"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) z = z"
| "plus (S z2) z = S (plus z2 z)"

fun minus :: "Nat => Nat => Nat" where
"minus (Z) z = Z"
| "minus (S z2) (S y2) = minus z2 y2"

fun length :: "'a list => Nat" where
"length (nil2) = Z"
| "length (cons2 z l) = plus (S Z) (length l)"

fun le :: "Nat => Nat => bool" where
"le (Z) z = True"
| "le (S z2) (Z) = False"
| "le (S z2) (S x2) = le z2 x2"

fun take :: "Nat => 'a list => 'a list" where
"take y z =
   (if le y Z then nil2 else
      (case z of
         nil2 => nil2
         | cons2 z2 xs => (case y of S x2 => cons2 z2 (take x2 xs))))"

fun go :: "Nat => Nat => Nat => Nat" where
"go y z (Z) = Z"
| "go (Z) (Z) (S x2) = Z"
| "go (Z) (S x5) (S x2) = minus (S x2) (S x5)"
| "go (S x3) (Z) (S x2) = go x3 x2 (S x2)"
| "go (S x3) (S x4) (S x2) = go x3 x4 (S x2)"

fun modstructural :: "Nat => Nat => Nat" where
"modstructural y z = go y Z z"

fun drop :: "Nat => 'a list => 'a list" where
"drop y z =
   (if le y Z then z else
      (case z of
         nil2 => nil2
         | cons2 z2 xs1 => (case y of S x2 => drop x2 xs1)))"

theorem property0 :
  "((rotate n xs) =
      (x (drop (modstructural n (length xs)) xs)
         (take (modstructural n (length xs)) xs)))"
  oops

end
