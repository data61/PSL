(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_tree_Flatten2
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil

fun x :: "'a list => 'a list => 'a list" where
"x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun flatten2 :: "'a Tree => 'a list => 'a list" where
"flatten2 (Node p z2 q) z = flatten2 p (cons2 z2 (flatten2 q z))"
| "flatten2 (Nil) z = z"

fun flatten0 :: "'a Tree => 'a list" where
"flatten0 (Node p z q) =
   x (flatten0 p) (x (cons2 z (nil2)) (flatten0 q))"
| "flatten0 (Nil) = nil2"

theorem property0 :
  "((flatten2 p (nil2)) = (flatten0 p))"
  oops

end
