(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_MSortBUIsSort
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun map :: "('a => 'b) => 'a list => 'b list" where
  "map f (nil2) = nil2"
| "map f (cons2 y xs) = cons2 (f y) (map f xs)"

fun lmerge :: "int list => int list => int list" where
  "lmerge (nil2) y = y"
| "lmerge (cons2 z x2) (nil2) = cons2 z x2"
| "lmerge (cons2 z x2) (cons2 x3 x4) =
     (if z <= x3 then cons2 z (lmerge x2 (cons2 x3 x4)) else
        cons2 x3 (lmerge (cons2 z x2) x4))"

fun pairwise :: "(int list) list => (int list) list" where
  "pairwise (nil2) = nil2"
| "pairwise (cons2 xs (nil2)) = cons2 xs (nil2)"
| "pairwise (cons2 xs (cons2 ys xss)) =
     cons2 (lmerge xs ys) (pairwise xss)"

(*fun did not finish the proof*)
function mergingbu :: "(int list) list => int list" where
  "mergingbu (nil2) = nil2"
| "mergingbu (cons2 xs (nil2)) = xs"
| "mergingbu (cons2 xs (cons2 z x2)) =
     mergingbu (pairwise (cons2 xs (cons2 z x2)))"
  by pat_completeness auto

fun msortbu :: "int list => int list" where
  "msortbu x = mergingbu (map (% (y :: int) => cons2 y (nil2)) x)"

fun insert :: "int => int list => int list" where
  "insert x (nil2) = cons2 x (nil2)"
| "insert x (cons2 z xs) =
     (if x <= z then cons2 x (cons2 z xs) else cons2 z (insert x xs))"

fun isort :: "int list => int list" where
  "isort (nil2) = nil2"
| "isort (cons2 y xs) = insert y (isort xs)"

theorem property0 :
  "((msortbu xs) = (isort xs))"
  oops

end
