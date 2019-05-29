(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_list_nat_Interleave
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"


(*fun did not finish the proof*)
function interleave :: "'a list => 'a list => 'a list" where
"interleave (nil2) y = y"
| "interleave (cons2 z xs) y = cons2 z (interleave y xs)"
by pat_completeness auto

function evens :: "'a list => 'a list"
         and odds :: "'a list => 'a list" where
"evens (nil2) = nil2"
| "evens (cons2 y xs) = cons2 y (odds xs)"
| "odds (nil2) = nil2"
| "odds (cons2 y xs) = evens xs"
by pat_completeness auto

theorem property0 :
  "((interleave (evens xs) (odds xs)) = xs)"
  oops

end
