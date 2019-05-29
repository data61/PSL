(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_sort_nat_HSort2Sorts
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

datatype Heap = Node "Heap" "Nat" "Heap" | Nil

fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

fun ordered :: "Nat list => bool" where
  "ordered (nil2) = True"
| "ordered (cons2 y (nil2)) = True"
| "ordered (cons2 y (cons2 y2 xs)) =
     ((le y y2) & (ordered (cons2 y2 xs)))"

fun hmerge :: "Heap => Heap => Heap" where
  "hmerge (Node z x2 x3) (Node x4 x5 x6) =
   (if le x2 x5 then Node (hmerge x3 (Node x4 x5 x6)) x2 z else
      Node (hmerge (Node z x2 x3) x6) x5 x4)"
| "hmerge (Node z x2 x3) (Nil) = Node z x2 x3"
| "hmerge (Nil) y = y"

(*fun did not finish the proof*)
function toList :: "Heap => Nat list" where
  "toList (Node q y r) = cons2 y (toList (hmerge q r))"
| "toList (Nil) = nil2"
  by pat_completeness auto

fun hinsert :: "Nat => Heap => Heap" where
  "hinsert x y = hmerge (Node Nil x Nil) y"

fun toHeap2 :: "Nat list => Heap" where
  "toHeap2 (nil2) = Nil"
| "toHeap2 (cons2 y xs) = hinsert y (toHeap2 xs)"

fun hsort2 :: "Nat list => Nat list" where
  "hsort2 x = toList (toHeap2 x)"

theorem property0 :
  "ordered (hsort2 xs)"
  oops

end
