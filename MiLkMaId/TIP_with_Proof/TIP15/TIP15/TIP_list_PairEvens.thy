(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_list_PairEvens
  imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun pairs :: "'t list => (('t, 't) pair) list" where
  "pairs (nil2) = nil2"
| "pairs (cons2 y (nil2)) = nil2"
| "pairs (cons2 y (cons2 y2 xs)) = cons2 (pair2 y y2) (pairs xs)"

fun map :: "('a => 'b) => 'a list => 'b list" where
  "map f (nil2) = nil2"
| "map f (cons2 y xs) = cons2 (f y) (map f xs)"

fun length :: "'a list => int" where
  "length (nil2) = 0"
| "length (cons2 y l) = 1 + (length l)"

function evens :: "'a list => 'a list"
  and odds :: "'a list => 'a list" where
  "evens (nil2) = nil2"
| "evens (cons2 y xs) = cons2 y (odds xs)"
| "odds (nil2) = nil2"
| "odds (cons2 y xs) = evens xs"
  by pat_completeness auto

theorem property0 :
  "((let eta :: int = length xs
     in ((let md :: int = eta mod 2
          in (if
                (((if (eta = 0) then 0 else (if eta <= 0 then 0 - 1 else 1)) =
                    (if 2 <= 0 then 0 - (0 - 1) else 0 - 1)) &
                   (md ~= 0))
                then
                md - 2
                else
                md)) =
           0)) ==>
      ((map
          (% (x :: ('a, 'a) pair) => (case x of pair2 y z => y))
          (pairs xs)) =
         (evens xs)))"
  oops

end