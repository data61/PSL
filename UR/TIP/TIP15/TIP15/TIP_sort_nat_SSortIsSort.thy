(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_sort_nat_SSortIsSort
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

fun ssortminimum1 :: "Nat => Nat list => Nat" where
  "ssortminimum1 x (nil2) = x"
| "ssortminimum1 x (cons2 y1 ys1) =
     (if le y1 x then ssortminimum1 y1 ys1 else ssortminimum1 x ys1)"

fun insert :: "Nat => Nat list => Nat list" where
  "insert x (nil2) = cons2 x (nil2)"
| "insert x (cons2 z xs) =
     (if le x z then cons2 x (cons2 z xs) else cons2 z (insert x xs))"

fun isort :: "Nat list => Nat list" where
  "isort (nil2) = nil2"
| "isort (cons2 y xs) = insert y (isort xs)"

fun deleteBy :: "('a => ('a => bool)) => 'a => 'a list =>
                 'a list" where
  "deleteBy x y (nil2) = nil2"
| "deleteBy x y (cons2 y2 ys) =
     (if (x y) y2 then ys else cons2 y2 (deleteBy x y ys))"

(*fun did not finish the proof*)
function ssort :: "Nat list => Nat list" where
  "ssort (nil2) = nil2"
| "ssort (cons2 y ys) =
     (let m :: Nat = ssortminimum1 y ys
     in cons2
          m
          (ssort
             (deleteBy
                (% (z :: Nat) => % (x2 :: Nat) => (z = x2)) m (cons2 y ys))))"
  by pat_completeness auto

theorem property0 :
  "((ssort xs) = (isort xs))"
  oops

end
