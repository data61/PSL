(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_list_nat_elem_nub_l
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun filter :: "('a => bool) => 'a list => 'a list" where
"filter p (nil2) = nil2"
| "filter p (cons2 y xs) =
     (if p y then cons2 y (filter p xs) else filter p xs)"

(*fun did not finish the proof*)
function nubBy :: "('a => ('a => bool)) => 'a list => 'a list" where
"nubBy x (nil2) = nil2"
| "nubBy x (cons2 z xs) =
     cons2 z (nubBy x (filter (% (y2 :: 'a) => (~ ((x z) y2))) xs))"
  by pat_completeness auto

fun elem :: "'a => 'a list => bool" where
"elem x (nil2) = False"
| "elem x (cons2 z xs) = ((z = x) | (elem x xs))"

theorem property0 :
  "((elem x xs) ==>
      (elem x (nubBy (% (y :: 'a) => % (z :: 'a) => (y = z)) xs)))"
  oops

end
