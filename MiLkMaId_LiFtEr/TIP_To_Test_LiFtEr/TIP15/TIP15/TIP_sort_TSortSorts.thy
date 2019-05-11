(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_sort_TSortSorts
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Tree = TNode "Tree" "int" "Tree" | TNil

fun ordered :: "int list => bool" where
"ordered (nil2) = True"
| "ordered (cons2 y (nil2)) = True"
| "ordered (cons2 y (cons2 y2 xs)) =
     ((y <= y2) & (ordered (cons2 y2 xs)))"

fun flatten :: "Tree => int list => int list" where
"flatten (TNode p z q) y = flatten p (cons2 z (flatten q y))"
| "flatten (TNil) y = y"

fun add :: "int => Tree => Tree" where
"add x (TNode p z q) =
   (if x <= z then TNode (add x p) z q else TNode p z (add x q))"
| "add x (TNil) = TNode TNil x TNil"

fun toTree :: "int list => Tree" where
"toTree (nil2) = TNil"
| "toTree (cons2 y xs) = add y (toTree xs)"

fun tsort :: "int list => int list" where
"tsort x = flatten (toTree x) (nil2)"

theorem property0 :
  "ordered (tsort xs)"
  oops

end
