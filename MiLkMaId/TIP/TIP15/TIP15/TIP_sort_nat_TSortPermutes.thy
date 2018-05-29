(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_sort_nat_TSortPermutes
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

datatype Tree = TNode "Tree" "Nat" "Tree" | TNil

fun le :: "Nat => Nat => bool" where
"le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

fun flatten :: "Tree => Nat list => Nat list" where
"flatten (TNode q z r) y = flatten q (cons2 z (flatten r y))"
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
  "isPermutation (tsort xs) xs"
  oops

end
