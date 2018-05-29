(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_nicomachus_theorem
imports "../../Test_Base"
begin

(*fun did not finish the proof*)
function sum :: "int => int" where
"sum x = (if (x = 0) then 0 else (sum (x - 1)) + x)"
by pat_completeness auto

(*fun did not finish the proof*)
function cubes :: "int => int" where
"cubes x =
   (if (x = 0) then 0 else (cubes (x - 1)) + ((x * x) * x))"
  by pat_completeness auto

theorem property0 :
  "((cubes n) = ((sum n) * (sum n)))"
  oops

end
