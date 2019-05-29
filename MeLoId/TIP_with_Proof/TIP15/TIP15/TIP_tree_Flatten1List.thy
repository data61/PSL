(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_tree_Flatten1List
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

(*fun did not finish the proof*)
function flatten1 :: "('a Tree) list => 'a list" where
  "flatten1 (nil2) = nil2"
| "flatten1 (cons2 (Node (Node x3 x4 x5) x2 q) ps) =
     flatten1 (cons2 (Node x3 x4 x5) (cons2 (Node (Nil) x2 q) ps))"
| "flatten1 (cons2 (Node (Nil) x2 q) ps) =
     cons2 x2 (flatten1 (cons2 q ps))"
| "flatten1 (cons2 (Nil) ps) = flatten1 ps"
  by pat_completeness auto

fun flatten0 :: "'a Tree => 'a list" where
  "flatten0 (Node p z q) =
   x (flatten0 p) (x (cons2 z (nil2)) (flatten0 q))"
| "flatten0 (Nil) = nil2"

fun concatMap :: "('a => 'b list) => 'a list => 'b list" where
  "concatMap f (nil2) = nil2"
| "concatMap f (cons2 z xs) = x (f z) (concatMap f xs)"

theorem property0 :
  "((flatten1 ps) = (concatMap (% (y :: 'b Tree) => flatten0 y) ps))"
  oops

end
