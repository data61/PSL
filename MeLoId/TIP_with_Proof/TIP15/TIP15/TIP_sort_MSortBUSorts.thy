(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_MSortBUSorts
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun ordered :: "int list => bool" where
  "ordered (nil2) = True"
| "ordered (cons2 y (nil2)) = True"
| "ordered (cons2 y (cons2 y2 xs)) =
     ((y <= y2) & (ordered (cons2 y2 xs)))"

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

theorem property0 :
  "ordered (msortbu xs)"
  oops

end
