(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_sort_HSort2IsSort
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Heap = Node "Heap" "int" "Heap" | Nil

fun insert :: "int => int list => int list" where
  "insert x (nil2) = cons2 x (nil2)"
| "insert x (cons2 z xs) =
     (if x <= z then cons2 x (cons2 z xs) else cons2 z (insert x xs))"

fun isort :: "int list => int list" where
  "isort (nil2) = nil2"
| "isort (cons2 y xs) = insert y (isort xs)"

fun hmerge :: "Heap => Heap => Heap" where
  "hmerge (Node z x2 x3) (Node x4 x5 x6) =
   (if x2 <= x5 then Node (hmerge x3 (Node x4 x5 x6)) x2 z else
      Node (hmerge (Node z x2 x3) x6) x5 x4)"
| "hmerge (Node z x2 x3) (Nil) = Node z x2 x3"
| "hmerge (Nil) y = y"

(*fun did not finish the proof*)
function toList :: "Heap => int list" where
  "toList (Node p y q) = cons2 y (toList (hmerge p q))"
| "toList (Nil) = nil2"
  by pat_completeness auto

fun hinsert :: "int => Heap => Heap" where
  "hinsert x y = hmerge (Node Nil x Nil) y"

fun toHeap2 :: "int list => Heap" where
  "toHeap2 (nil2) = Nil"
| "toHeap2 (cons2 y xs) = hinsert y (toHeap2 xs)"

fun hsort2 :: "int list => int list" where
  "hsort2 x = toList (toHeap2 x)"

theorem property0 :
  "((hsort2 xs) = (isort xs))"
  oops

end
