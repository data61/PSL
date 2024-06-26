(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_nat_HSortCount
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

datatype Heap = Node "Heap" "Nat" "Heap" | Nil

fun toHeap :: "Nat list => Heap list" where
  "toHeap (nil2) = nil2"
| "toHeap (cons2 y z) = cons2 (Node Nil y Nil) (toHeap z)"

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

fun hmerge :: "Heap => Heap => Heap" where
  "hmerge (Node z x2 x3) (Node x4 x5 x6) =
   (if le x2 x5 then Node (hmerge x3 (Node x4 x5 x6)) x2 z else
      Node (hmerge (Node z x2 x3) x6) x5 x4)"
| "hmerge (Node z x2 x3) (Nil) = Node z x2 x3"
| "hmerge (Nil) y = y"

fun hpairwise :: "Heap list => Heap list" where
  "hpairwise (nil2) = nil2"
| "hpairwise (cons2 q (nil2)) = cons2 q (nil2)"
| "hpairwise (cons2 q (cons2 r qs)) =
     cons2 (hmerge q r) (hpairwise qs)"

(*fun did not finish the proof*)
function hmerging :: "Heap list => Heap" where
  "hmerging (nil2) = Nil"
| "hmerging (cons2 q (nil2)) = q"
| "hmerging (cons2 q (cons2 z x2)) =
     hmerging (hpairwise (cons2 q (cons2 z x2)))"
  by pat_completeness auto

fun toHeap2 :: "Nat list => Heap" where
  "toHeap2 x = hmerging (toHeap x)"

(*fun did not finish the proof*)
function toList :: "Heap => Nat list" where
  "toList (Node q y r) = cons2 y (toList (hmerge q r))"
| "toList (Nil) = nil2"
  by pat_completeness auto

fun hsort :: "Nat list => Nat list" where
  "hsort x = toList (toHeap2 x)"

fun count :: "'a => 'a list => Nat" where
  "count x (nil2) = Z"
| "count x (cons2 z ys) =
     (if (x = z) then plus (S Z) (count x ys) else count x ys)"

theorem property0 :
  "((count x (hsort xs)) = (count x xs))"
  oops

end
