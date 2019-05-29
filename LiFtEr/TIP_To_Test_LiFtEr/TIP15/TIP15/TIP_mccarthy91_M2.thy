(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_mccarthy91_M2
imports "../../Test_Base"
begin

(*fun did not finish the proof*)
function m :: "int => int" where
"m x = (if x > 100 then x - 10 else m (m (x + 11)))"
by pat_completeness auto

theorem property0 :
  "((n >= 101) ==> ((m n) = (n - 10)))"
  oops

end
