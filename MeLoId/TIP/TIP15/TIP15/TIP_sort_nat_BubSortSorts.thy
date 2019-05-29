(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_sort_nat_BubSortSorts
  imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

fun ordered :: "Nat list => bool" where
  "ordered (nil2) = True"
| "ordered (cons2 y (nil2)) = True"
| "ordered (cons2 y (cons2 y2 xs)) =
     ((le y y2) & (ordered (cons2 y2 xs)))"

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
  "ordered (bubsort xs)"
  oops

end
