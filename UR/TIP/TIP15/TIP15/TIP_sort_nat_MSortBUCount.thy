(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_sort_nat_MSortBUCount
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun map :: "('a => 'b) => 'a list => 'b list" where
  "map f (nil2) = nil2"
| "map f (cons2 y xs) = cons2 (f y) (map f xs)"

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
function mergingbu :: "(Nat list) list => Nat list" where
  "mergingbu (nil2) = nil2"
| "mergingbu (cons2 xs (nil2)) = xs"
| "mergingbu (cons2 xs (cons2 z x2)) =
     mergingbu (pairwise (cons2 xs (cons2 z x2)))"
  by pat_completeness auto

fun msortbu :: "Nat list => Nat list" where
  "msortbu x = mergingbu (map (% (y :: Nat) => cons2 y (nil2)) x)"

fun count :: "'a => 'a list => Nat" where
  "count x (nil2) = Z"
| "count x (cons2 z ys) =
     (if (x = z) then plus (S Z) (count x ys) else count x ys)"

theorem property0 :
  "((count x (msortbu xs)) = (count x xs))"
  oops

end
