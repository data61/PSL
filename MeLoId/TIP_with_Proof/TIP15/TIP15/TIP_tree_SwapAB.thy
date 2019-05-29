(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_tree_SwapAB
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil

fun x :: "'a list => 'a list => 'a list" where
"x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun swap :: "int => int => int Tree => int Tree" where
"swap y z (Node p x2 q) =
   (if (x2 = y) then Node (swap y z p) z (swap y z q) else
      (if (x2 = z) then Node (swap y z p) y (swap y z q) else
         Node (swap y z p) x2 (swap y z q)))"
| "swap y z (Nil) = Nil"

fun flatten0 :: "'a Tree => 'a list" where
"flatten0 (Node p z q) =
   x (flatten0 p) (x (cons2 z (nil2)) (flatten0 q))"
| "flatten0 (Nil) = nil2"

fun elem :: "'a => 'a list => bool" where
"elem y (nil2) = False"
| "elem y (cons2 z2 xs) = ((z2 = y) | (elem y xs))"

theorem property0 :
  "((elem a (flatten0 p)) ==>
      ((elem b (flatten0 p)) ==>
         ((elem a (flatten0 (swap a b p))) &
            (elem b (flatten0 (swap a b p))))))"
  oops

end
