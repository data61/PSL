(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_nat_StoogeSortIsSort
  imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun reverse :: "'a list => 'a list" where
  "reverse (nil2) = nil2"
| "reverse (cons2 z xs) = x (reverse xs) (cons2 z (nil2))"

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) z = z"
| "plus (S z2) z = S (plus z2 z)"

fun minus :: "Nat => Nat => Nat" where
  "minus (Z) z = Z"
| "minus (S z2) (S y2) = minus z2 y2"

fun lt :: "Nat => Nat => bool" where
  "lt y (Z) = False"
| "lt (Z) (S z2) = True"
| "lt (S n) (S z2) = lt n z2"

fun length :: "'a list => Nat" where
  "length (nil2) = Z"
| "length (cons2 z l) = plus (S Z) (length l)"

fun le :: "Nat => Nat => bool" where
  "le (Z) z = True"
| "le (S z2) (Z) = False"
| "le (S z2) (S x2) = le z2 x2"

fun sort2 :: "Nat => Nat => Nat list" where
  "sort2 y z =
   (if le y z then cons2 y (cons2 z (nil2)) else
      cons2 z (cons2 y (nil2)))"

fun take :: "Nat => 'a list => 'a list" where
  "take y z =
   (if le y Z then nil2 else
      (case z of
         nil2 => nil2
         | cons2 z2 xs => (case y of S x2 => cons2 z2 (take x2 xs))))"

fun insert :: "Nat => Nat list => Nat list" where
  "insert y (nil2) = cons2 y (nil2)"
| "insert y (cons2 z2 xs) =
     (if le y z2 then cons2 y (cons2 z2 xs) else
        cons2 z2 (insert y xs))"

fun isort :: "Nat list => Nat list" where
  "isort (nil2) = nil2"
| "isort (cons2 z xs) = insert z (isort xs)"

(*fun did not finish the proof*)
function idiv :: "Nat => Nat => Nat" where
  "idiv y z = (if lt y z then Z else S (idiv (minus y z) z))"
  by pat_completeness auto

fun drop :: "Nat => 'a list => 'a list" where
  "drop y z =
   (if le y Z then z else
      (case z of
         nil2 => nil2
         | cons2 z2 xs1 => (case y of S x2 => drop x2 xs1)))"

fun splitAt :: "Nat => 'a list =>
              (('a list), ('a list)) pair" where
  "splitAt y z = pair2 (take y z) (drop y z)"

function stooge1sort2 :: "Nat list => Nat list"
  and stoogesort :: "Nat list => Nat list"
  and stooge1sort1 :: "Nat list => Nat list" where
  "stooge1sort2 y =
   (case splitAt (idiv (length y) (S (S (S Z)))) (reverse y) of
      pair2 ys2 zs2 => x (stoogesort zs2) (reverse ys2))"
| "stoogesort (nil2) = nil2"
| "stoogesort (cons2 z (nil2)) = cons2 z (nil2)"
| "stoogesort (cons2 z (cons2 y2 (nil2))) = sort2 z y2"
| "stoogesort (cons2 z (cons2 y2 (cons2 x3 x4))) =
     stooge1sort2
       (stooge1sort1 (stooge1sort2 (cons2 z (cons2 y2 (cons2 x3 x4)))))"
| "stooge1sort1 y =
     (case splitAt (idiv (length y) (S (S (S Z)))) y of
        pair2 ys2 zs1 => x ys2 (stoogesort zs1))"
  by pat_completeness auto

theorem property0 :
  "((stoogesort xs) = (isort xs))"
  oops

end
