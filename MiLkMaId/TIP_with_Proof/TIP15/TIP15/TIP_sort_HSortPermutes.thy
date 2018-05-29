(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_HSortPermutes
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Heap = Node "Heap" "int" "Heap" | Nil

fun toHeap :: "int list => Heap list" where
  "toHeap (nil2) = nil2"
| "toHeap (cons2 y z) = cons2 (Node Nil y Nil) (toHeap z)"

fun hmerge :: "Heap => Heap => Heap" where
  "hmerge (Node z x2 x3) (Node x4 x5 x6) =
   (if x2 <= x5 then Node (hmerge x3 (Node x4 x5 x6)) x2 z else
      Node (hmerge (Node z x2 x3) x6) x5 x4)"
| "hmerge (Node z x2 x3) (Nil) = Node z x2 x3"
| "hmerge (Nil) y = y"

fun hpairwise :: "Heap list => Heap list" where
  "hpairwise (nil2) = nil2"
| "hpairwise (cons2 p (nil2)) = cons2 p (nil2)"
| "hpairwise (cons2 p (cons2 q qs)) =
     cons2 (hmerge p q) (hpairwise qs)"

(*fun did not finish the proof*)
function hmerging :: "Heap list => Heap" where
  "hmerging (nil2) = Nil"
| "hmerging (cons2 p (nil2)) = p"
| "hmerging (cons2 p (cons2 z x2)) =
     hmerging (hpairwise (cons2 p (cons2 z x2)))"
  by pat_completeness auto

fun toHeap2 :: "int list => Heap" where
  "toHeap2 x = hmerging (toHeap x)"

(*fun did not finish the proof*)
function toList :: "Heap => int list" where
  "toList (Node p y q) = cons2 y (toList (hmerge p q))"
| "toList (Nil) = nil2"
  by pat_completeness auto

fun hsort :: "int list => int list" where
  "hsort x = toList (toHeap2 x)"

fun elem :: "'a => 'a list => bool" where
  "elem x (nil2) = False"
| "elem x (cons2 z xs) = ((z = x) | (elem x xs))"

fun deleteBy :: "('a => ('a => bool)) => 'a => 'a list =>
                 'a list" where
  "deleteBy x y (nil2) = nil2"
| "deleteBy x y (cons2 y2 ys) =
     (if (x y) y2 then ys else cons2 y2 (deleteBy x y ys))"

fun isPermutation :: "'a list => 'a list => bool" where
  "isPermutation (nil2) (nil2) = True"
| "isPermutation (nil2) (cons2 z x2) = False"
| "isPermutation (cons2 x3 xs) y =
     ((elem x3 y) &
        (isPermutation
           xs (deleteBy (% (x4 :: 'a) => % (x5 :: 'a) => (x4 = x5)) x3 y)))"

theorem property0 :
  "isPermutation (hsort xs) xs"
  oops

end
