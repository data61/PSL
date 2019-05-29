(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_nat_BubSortCount
  imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

fun count :: "'a => 'a list => Nat" where
  "count x (nil2) = Z"
| "count x (cons2 z ys) =
     (if (x = z) then plus (S Z) (count x ys) else count x ys)"

fun bubble :: "Nat list => (bool, (Nat list)) pair" where
  "bubble (nil2) = pair2 False (nil2)"
| "bubble (cons2 y (nil2)) = pair2 False (cons2 y (nil2))"
| "bubble (cons2 y (cons2 y2 xs)) =
     (if le y y2 then
        (case bubble (cons2 y2 xs) of
           pair2 b22 ys22 => pair2 b22 (cons2 y ys22))
        else
        (case bubble (cons2 y xs) of
           pair2 b2 ys2 => pair2 True (cons2 y2 ys2)))"

(*fun did not finish the proof*)
function bubsort :: "Nat list => Nat list" where
  "bubsort x =
   (case bubble x of pair2 b1 ys => (if b1 then bubsort ys else x))"
  by pat_completeness auto

theorem property0 :
  "((count x (bubsort xs)) = (count x xs))"
  oops

end
