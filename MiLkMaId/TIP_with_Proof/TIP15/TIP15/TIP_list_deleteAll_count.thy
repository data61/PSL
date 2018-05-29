(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_list_deleteAll_count
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun deleteBy :: "('a => ('a => bool)) => 'a => 'a list =>
                 'a list" where
"deleteBy x y (nil2) = nil2"
| "deleteBy x y (cons2 y2 ys) =
     (if (x y) y2 then ys else cons2 y2 (deleteBy x y ys))"

fun deleteAll :: "'a => 'a list => 'a list" where
"deleteAll x (nil2) = nil2"
| "deleteAll x (cons2 z ys) =
     (if (x = z) then deleteAll x ys else cons2 z (deleteAll x ys))"

fun count :: "'a => 'a list => int" where
"count x (nil2) = 0"
| "count x (cons2 z ys) =
     (if (x = z) then 1 + (count x ys) else count x ys)"

theorem property0 :
  "(((deleteAll x xs) =
       (deleteBy (% (y :: 'a) => % (z :: 'a) => (y = z)) x xs)) ==>
      ((count x xs) <= 1))"
  oops

end
