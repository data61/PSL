(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_nat_QSortCount
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) z = z"
| "plus (S z2) z = S (plus z2 z)"

fun lt :: "Nat => Nat => bool" where
  "lt y (Z) = False"
| "lt (Z) (S z2) = True"
| "lt (S n) (S z2) = lt n z2"

fun le :: "Nat => Nat => bool" where
  "le (Z) z = True"
| "le (S z2) (Z) = False"
| "le (S z2) (S x2) = le z2 x2"

fun gt :: "Nat => Nat => bool" where
  "gt y z = lt z y"

fun filter :: "('a => bool) => 'a list => 'a list" where
  "filter q (nil2) = nil2"
| "filter q (cons2 z xs) =
     (if q z then cons2 z (filter q xs) else filter q xs)"

(*fun did not finish the proof*)
function qsort :: "Nat list => Nat list" where
  "qsort (nil2) = nil2"
| "qsort (cons2 z xs) =
     x (qsort (filter (% (z2 :: Nat) => le z2 z) xs))
       (x (cons2 z (nil2))
          (qsort (filter (% (x2 :: Nat) => gt x2 z) xs)))"
  by pat_completeness auto

fun count :: "'a => 'a list => Nat" where
  "count y (nil2) = Z"
| "count y (cons2 z2 ys) =
     (if (y = z2) then plus (S Z) (count y ys) else count y ys)"

theorem property0 :
  "((count y (qsort xs)) = (count y xs))"
  oops

end
