(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_list_nat_SelectPermutations
imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun select :: "'a => (('a, ('a list)) pair) list =>
               (('a, ('a list)) pair) list" where
"select x (nil2) = nil2"
| "select x (cons2 (pair2 y2 ys) x2) =
     cons2 (pair2 y2 (cons2 x ys)) (select x x2)"

fun select2 :: "'a list => (('a, ('a list)) pair) list" where
"select2 (nil2) = nil2"
| "select2 (cons2 y xs) =
     cons2 (pair2 y xs) (select y (select2 xs))"

fun formula :: "(('a, ('a list)) pair) list =>
                ('a list) list" where
"formula (nil2) = nil2"
| "formula (cons2 (pair2 y2 ys) z) =
     cons2 (cons2 y2 ys) (formula z)"

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

fun all :: "('a => bool) => 'a list => bool" where
"all p (nil2) = True"
| "all p (cons2 y xs) = ((p y) & (all p xs))"

theorem property0 :
  "all
     (% (x :: 'a list) => isPermutation x xs) (formula (select2 xs))"
  oops

end
