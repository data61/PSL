(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_sort_ISortCount
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun insert :: "int => int list => int list" where
"insert x (nil2) = cons2 x (nil2)"
| "insert x (cons2 z xs) =
     (if x <= z then cons2 x (cons2 z xs) else cons2 z (insert x xs))"

fun isort :: "int list => int list" where
"isort (nil2) = nil2"
| "isort (cons2 y xs) = insert y (isort xs)"

fun count :: "'a => 'a list => int" where
"count x (nil2) = 0"
| "count x (cons2 z ys) =
     (if (x = z) then 1 + (count x ys) else count x ys)"

theorem property0 :
  "((count x (isort xs)) = (count x xs))"
  oops

end
