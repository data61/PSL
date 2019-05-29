(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_nat_BSortIsSort
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun le :: "Nat => Nat => bool" where
  "le (Z) z = True"
| "le (S z2) (Z) = False"
| "le (S z2) (S x2) = le z2 x2"

fun sort2 :: "Nat => Nat => Nat list" where
  "sort2 y z =
   (if le y z then cons2 y (cons2 z (nil2)) else
      cons2 z (cons2 y (nil2)))"

fun pairs :: "Nat list => Nat list => Nat list" where
  "pairs (nil2) z = z"
| "pairs (cons2 z2 x2) (nil2) = cons2 z2 x2"
| "pairs (cons2 z2 x2) (cons2 x3 x4) =
     x (sort2 z2 x3) (pairs x2 x4)"

fun stitch :: "Nat list => Nat list => Nat list" where
  "stitch (nil2) z = z"
| "stitch (cons2 z2 xs) z = cons2 z2 (pairs xs z)"

fun insert :: "Nat => Nat list => Nat list" where
  "insert y (nil2) = cons2 y (nil2)"
| "insert y (cons2 z2 xs) =
     (if le y z2 then cons2 y (cons2 z2 xs) else
        cons2 z2 (insert y xs))"

fun isort :: "Nat list => Nat list" where
  "isort (nil2) = nil2"
| "isort (cons2 z xs) = insert z (isort xs)"

function evens :: "'a list => 'a list"
  and odds :: "'a list => 'a list" where
  "evens (nil2) = nil2"
| "evens (cons2 z xs) = cons2 z (odds xs)"
| "odds (nil2) = nil2"
| "odds (cons2 z xs) = evens xs"
  by pat_completeness auto

(*fun did not finish the proof*)
function bmerge :: "Nat list => Nat list => Nat list" where
  "bmerge (nil2) z = nil2"
| "bmerge (cons2 z2 x2) (nil2) = cons2 z2 x2"
| "bmerge (cons2 z2 x2) (cons2 x3 x4) =
     (let fail :: Nat list =
       stitch
         (bmerge (evens (cons2 z2 x2)) (evens (cons2 x3 x4)))
         (bmerge (odds (cons2 z2 x2)) (odds (cons2 x3 x4)))
     in (case x2 of
           nil2 =>
             (case x4 of
                nil2 => sort2 z2 x3
                | cons2 x5 x6 => fail)
           | cons2 x7 x8 => fail))"
  by pat_completeness auto

(*fun did not finish the proof*)
function bsort :: "Nat list => Nat list" where
  "bsort (nil2) = nil2"
| "bsort (cons2 z (nil2)) = cons2 z (nil2)"
| "bsort (cons2 z (cons2 x2 x3)) =
     bmerge
       (bsort (evens (cons2 z (cons2 x2 x3))))
       (bsort (odds (cons2 z (cons2 x2 x3))))"
  by pat_completeness auto

theorem property0 :
  "((bsort xs) = (isort xs))"
  oops

end
