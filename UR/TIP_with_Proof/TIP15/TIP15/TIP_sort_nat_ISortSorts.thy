(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_nat_ISortSorts
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun le :: "Nat => Nat => bool" where
"le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

fun ordered :: "Nat list => bool" where
"ordered (nil2) = True"
| "ordered (cons2 y (nil2)) = True"
| "ordered (cons2 y (cons2 y2 xs)) =
     ((le y y2) & (ordered (cons2 y2 xs)))"

fun insert :: "Nat => Nat list => Nat list" where
"insert x (nil2) = cons2 x (nil2)"
| "insert x (cons2 z xs) =
     (if le x z then cons2 x (cons2 z xs) else cons2 z (insert x xs))"

fun isort :: "Nat list => Nat list" where
"isort (nil2) = nil2"
| "isort (cons2 y xs) = insert y (isort xs)"

theorem property0 :
  "ordered (isort xs)"
  oops

end
