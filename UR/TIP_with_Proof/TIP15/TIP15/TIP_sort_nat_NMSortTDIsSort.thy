(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_nat_NMSortTDIsSort
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
| "minus (S z) (S y2) = minus z y2"

(*fun did not finish the proof*)
function nmsorttdhalf1 :: "Nat => Nat" where
  "nmsorttdhalf1 x =
   (if (x = (S Z)) then Z else
      (case x of
         Z => Z
         | S y => plus (S Z) (nmsorttdhalf1 (minus x (S (S Z))))))"
  by pat_completeness auto

fun length :: "'a list => Nat" where
  "length (nil2) = Z"
| "length (cons2 y l) = plus (S Z) (length l)"

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

fun take :: "Nat => 'a list => 'a list" where
  "take x y =
   (if le x Z then nil2 else
      (case y of
         nil2 => nil2
         | cons2 z xs => (case x of S x2 => cons2 z (take x2 xs))))"

fun insert :: "Nat => Nat list => Nat list" where
  "insert x (nil2) = cons2 x (nil2)"
| "insert x (cons2 z xs) =
     (if le x z then cons2 x (cons2 z xs) else cons2 z (insert x xs))"

fun isort :: "Nat list => Nat list" where
  "isort (nil2) = nil2"
| "isort (cons2 y xs) = insert y (isort xs)"

fun drop :: "Nat => 'a list => 'a list" where
  "drop x y =
   (if le x Z then y else
      (case y of
         nil2 => nil2
         | cons2 z xs1 => (case x of S x2 => drop x2 xs1)))"

(*fun did not finish the proof*)
function nmsorttd :: "Nat list => Nat list" where
  "nmsorttd (nil2) = nil2"
| "nmsorttd (cons2 y (nil2)) = cons2 y (nil2)"
| "nmsorttd (cons2 y (cons2 x2 x3)) =
     (let k :: Nat = nmsorttdhalf1 (length (cons2 y (cons2 x2 x3)))
     in lmerge
          (nmsorttd (take k (cons2 y (cons2 x2 x3))))
          (nmsorttd (drop k (cons2 y (cons2 x2 x3)))))"
  by pat_completeness auto

theorem property0 :
  "((nmsorttd xs) = (isort xs))"
  oops

end
