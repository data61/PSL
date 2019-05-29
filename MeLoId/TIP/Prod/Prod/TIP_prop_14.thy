(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_14
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "bool => bool => bool" where
"x True z = z"
| "x False z = False"

fun t2 :: "Nat => Nat => bool" where
"t2 (Z) z = True"
| "t2 (S z2) (Z) = False"
| "t2 (S z2) (S x2) = t2 z2 x2"

fun insert :: "Nat => Nat list => Nat list" where
"insert y (nil2) = cons2 y (nil2)"
| "insert y (cons2 z2 xs) =
     (if t2 y z2 then cons2 y (cons2 z2 xs) else cons2 z2 (insert y xs))"

fun isort :: "Nat list => Nat list" where
"isort (nil2) = nil2"
| "isort (cons2 z xs) = insert z (isort xs)"

fun sorted :: "Nat list => bool" where
"sorted (nil2) = True"
| "sorted (cons2 z (nil2)) = True"
| "sorted (cons2 z (cons2 y2 xs)) =
     x (t2 z y2) (sorted (cons2 y2 xs))"

theorem property0 :
  "sorted (isort y)"
  oops

end
