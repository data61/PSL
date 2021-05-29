(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_48
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun length :: "'a list => Nat" where
  "length (nil2) = Z"
| "length (cons2 y xs) = S (length xs)"

fun t2 :: "Nat => Nat => bool" where
  "t2 (Z) y = True"
| "t2 (S z) (Z) = False"
| "t2 (S z) (S x2) = t2 z x2"

fun insert :: "Nat => Nat list => Nat list" where
  "insert x (nil2) = cons2 x (nil2)"
| "insert x (cons2 z xs) =
     (if t2 x z then cons2 x (cons2 z xs) else cons2 z (insert x xs))"

fun isort :: "Nat list => Nat list" where
  "isort (nil2) = nil2"
| "isort (cons2 y xs) = insert y (isort xs)"

theorem property0 :
  "((length (isort x)) = (length x))"
  oops

end
