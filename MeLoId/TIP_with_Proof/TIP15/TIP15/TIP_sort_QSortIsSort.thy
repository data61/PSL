(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_QSortIsSort
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun insert :: "int => int list => int list" where
  "insert y (nil2) = cons2 y (nil2)"
| "insert y (cons2 z2 xs) =
     (if y <= z2 then cons2 y (cons2 z2 xs) else
        cons2 z2 (insert y xs))"

fun isort :: "int list => int list" where
  "isort (nil2) = nil2"
| "isort (cons2 z xs) = insert z (isort xs)"

fun filter :: "('a => bool) => 'a list => 'a list" where
  "filter p (nil2) = nil2"
| "filter p (cons2 z xs) =
     (if p z then cons2 z (filter p xs) else filter p xs)"

(*fun did not finish the proof*)
function qsort :: "int list => int list" where
  "qsort (nil2) = nil2"
| "qsort (cons2 z xs) =
     x (qsort (filter (% (z2 :: int) => z2 <= z) xs))
       (x (cons2 z (nil2)) (qsort (filter (% (x2 :: int) => x2 > z) xs)))"
  by pat_completeness auto

theorem property0 :
  "((qsort xs) = (isort xs))"
  oops

end
