(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_nat_TSortSorts
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

datatype Tree = TNode "Tree" "Nat" "Tree" | TNil

fun le :: "Nat => Nat => bool" where
"le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

fun ordered :: "Nat list => bool" where
"ordered (nil2) = True"
| "ordered (cons2 y (nil2)) = True"
| "ordered (cons2 y (cons2 y2 xs)) =
     ((le y y2) & (ordered (cons2 y2 xs)))"

fun flatten :: "Tree => Nat list => Nat list" where
"flatten (TNode q z r) y = flatten q (cons2 z (flatten r y))"
| "flatten (TNil) y = y"

fun add :: "Nat => Tree => Tree" where
"add x (TNode q z r) =
   (if le x z then TNode (add x q) z r else TNode q z (add x r))"
| "add x (TNil) = TNode TNil x TNil"

fun toTree :: "Nat list => Tree" where
"toTree (nil2) = TNil"
| "toTree (cons2 y xs) = add y (toTree xs)"

fun tsort :: "Nat list => Nat list" where
"tsort x = flatten (toTree x) (nil2)"

theorem property0 :
  "ordered (tsort xs)"
  oops

end
