(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_list_assoc
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun x :: "'a list => 'a list => 'a list" where
"x (nil2) y2 = y2"
| "x (cons2 z2 xs) y2 = cons2 z2 (x xs y2)"

fun y :: "'a list => ('a => 'b list) => 'b list" where
"y (nil2) y2 = nil2"
| "y (cons2 z2 xs) y2 = x (y2 z2) (y xs y2)"

theorem property0 :
  "((y (y m f) g) = (y m (% (z :: 'a) => y (f z) g)))"
  oops

end
