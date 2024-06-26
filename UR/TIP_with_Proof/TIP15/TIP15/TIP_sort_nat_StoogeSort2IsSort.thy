(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_nat_StoogeSort2IsSort
  imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) z = z"
| "plus (S z2) z = S (plus z2 z)"

fun times :: "Nat => Nat => Nat" where
  "times (Z) z = Z"
| "times (S z2) z = plus z (times z2 z)"

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

function stooge2sort2 :: "Nat list => Nat list"
  and stoogesort2 :: "Nat list => Nat list"
  and stooge2sort1 :: "Nat list => Nat list" where
  "stooge2sort2 y =
   (case
      splitAt (idiv (S (times (S (S Z)) (length y))) (S (S (S Z)))) y
      of
      pair2 ys2 zs1 => x (stoogesort2 ys2) zs1)"
| "stoogesort2 (nil2) = nil2"
| "stoogesort2 (cons2 z (nil2)) = cons2 z (nil2)"
| "stoogesort2 (cons2 z (cons2 y2 (nil2))) = sort2 z y2"
| "stoogesort2 (cons2 z (cons2 y2 (cons2 x3 x4))) =
     stooge2sort2
       (stooge2sort1 (stooge2sort2 (cons2 z (cons2 y2 (cons2 x3 x4)))))"
| "stooge2sort1 y =
     (case splitAt (idiv (length y) (S (S (S Z)))) y of
        pair2 ys2 zs1 => x ys2 (stoogesort2 zs1))"
  by pat_completeness auto

theorem property0 :
  "((stoogesort2 xs) = (isort xs))"
  oops

end
