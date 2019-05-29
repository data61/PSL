(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_nat_MSortBU2Permutes
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

fun lmerge :: "Nat list => Nat list => Nat list" where
  "lmerge (nil2) y = y"
| "lmerge (cons2 z x2) (nil2) = cons2 z x2"
| "lmerge (cons2 z x2) (cons2 x3 x4) =
     (if le z x3 then cons2 z (lmerge x2 (cons2 x3 x4)) else
        cons2 x3 (lmerge (cons2 z x2) x4))"

fun pairwise :: "(Nat list) list => (Nat list) list" where
  "pairwise (nil2) = nil2"
| "pairwise (cons2 xs (nil2)) = cons2 xs (nil2)"
| "pairwise (cons2 xs (cons2 ys xss)) =
     cons2 (lmerge xs ys) (pairwise xss)"

(*fun did not finish the proof*)
function mergingbu2 :: "(Nat list) list => Nat list" where
  "mergingbu2 (nil2) = nil2"
| "mergingbu2 (cons2 xs (nil2)) = xs"
| "mergingbu2 (cons2 xs (cons2 z x2)) =
     mergingbu2 (pairwise (cons2 xs (cons2 z x2)))"
  by pat_completeness auto

fun risers :: "Nat list => (Nat list) list" where
  "risers (nil2) = nil2"
| "risers (cons2 y (nil2)) = cons2 (cons2 y (nil2)) (nil2)"
| "risers (cons2 y (cons2 y2 xs)) =
     (if le y y2 then
        (case risers (cons2 y2 xs) of
           nil2 => nil2
           | cons2 ys yss => cons2 (cons2 y ys) yss)
        else
        cons2 (cons2 y (nil2)) (risers (cons2 y2 xs)))"

fun msortbu2 :: "Nat list => Nat list" where
  "msortbu2 x = mergingbu2 (risers x)"

fun elem :: "'a => 'a list => bool" where
  "elem x (nil2) = False"
| "elem x (cons2 z xs) = ((z = x) | (elem x xs))"

fun deleteBy :: "('a => ('a => bool)) => 'a => 'a list =>
                 'a list" where
  "deleteBy x y (nil2) = nil2"
| "deleteBy x y (cons2 y2 ys) =
     (if (x y) y2 then ys else cons2 y2 (deleteBy x y ys))"

fun isPermutation :: "'a list => 'a list => bool" where
  "isPermutation (nil2) (nil2) = True"
| "isPermutation (nil2) (cons2 z x2) = False"
| "isPermutation (cons2 x3 xs) y =
     ((elem x3 y) &
        (isPermutation
           xs (deleteBy (% (x4 :: 'a) => % (x5 :: 'a) => (x4 = x5)) x3 y)))"

theorem property0 :
  "isPermutation (msortbu2 xs) xs"
  oops

end
