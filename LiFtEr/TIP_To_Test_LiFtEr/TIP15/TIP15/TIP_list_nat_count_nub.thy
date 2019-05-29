(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_list_nat_count_nub
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun filter :: "('a => bool) => 'a list => 'a list" where
"filter q (nil2) = nil2"
| "filter q (cons2 y xs) =
     (if q y then cons2 y (filter q xs) else filter q xs)"

(*fun did not finish the proof*)
function nubBy :: "('a => ('a => bool)) => 'a list => 'a list" where
"nubBy x (nil2) = nil2"
| "nubBy x (cons2 z xs) =
     cons2 z (nubBy x (filter (% (y2 :: 'a) => (~ ((x z) y2))) xs))"
by pat_completeness auto

(*fun did not finish the proof*)
function elem :: "'a => 'a list => bool" where
"elem x (nil2) = False"
| "elem x (cons2 z xs) = ((z = x) | (elem x xs))"
by pat_completeness auto

fun count :: "'a => 'a list => Nat" where
"count x (nil2) = Z"
| "count x (cons2 z ys) =
     (if (x = z) then plus (S Z) (count x ys) else count x ys)"

theorem property0 :
  "((elem x xs) ==>
      ((count x (nubBy (% (y :: 'a) => % (z :: 'a) => (y = z)) xs)) =
         (S Z)))"
  oops

end
