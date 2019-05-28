(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_list_weird_concat_map_bind
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun x :: "'a list => 'a list => 'a list" where
"x (nil2) y2 = y2"
| "x (cons2 z2 xs) y2 = cons2 z2 (x xs y2)"

fun y :: "'a list => ('a => 'b list) => 'b list" where
"y (nil2) y2 = nil2"
| "y (cons2 z2 xs) y2 = x (y2 z2) (y xs y2)"

(*fun did not finish the proof*)
function weirdconcat :: "('a list) list => 'a list" where
"weirdconcat (nil2) = nil2"
| "weirdconcat (cons2 (nil2) xss) = weirdconcat xss"
| "weirdconcat (cons2 (cons2 z2 xs) xss) =
     cons2 z2 (weirdconcat (cons2 xs xss))"
by pat_completeness auto

fun map :: "('a => 'b) => 'a list => 'b list" where
"map f (nil2) = nil2"
| "map f (cons2 y2 xs) = cons2 (f y2) (map f xs)"

theorem property0 :
  "((weirdconcat (map f xs)) = (y xs f))"
  oops

end
