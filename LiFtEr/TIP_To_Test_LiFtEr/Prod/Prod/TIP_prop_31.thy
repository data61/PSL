(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_31
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (nil2) y = y"
| "qrev (cons2 z xs) y = qrev xs (cons2 z y)"

theorem property0 :
  "((qrev (qrev x (nil2)) (nil2)) = x)"
  oops

end
