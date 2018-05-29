(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_TSortPermutes
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Tree = TNode "Tree" "int" "Tree" | TNil

fun flatten :: "Tree => int list => int list" where
"flatten (TNode p z q) y = flatten p (cons2 z (flatten q y))"
| "flatten (TNil) y = y"

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
  "isPermutation (tsort xs) xs"
  oops

end
