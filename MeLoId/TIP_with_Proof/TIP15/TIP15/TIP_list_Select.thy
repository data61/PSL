(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_list_Select
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

fun map :: "('a => 'b) => 'a list => 'b list" where
"map f (nil2) = nil2"
| "map f (cons2 y xs) = cons2 (f y) (map f xs)"

theorem property0 :
  "((map
       (% (x :: ('b, ('b list)) pair) => (case x of pair2 y z => y))
       (select2 xs)) =
      xs)"
  oops

end
