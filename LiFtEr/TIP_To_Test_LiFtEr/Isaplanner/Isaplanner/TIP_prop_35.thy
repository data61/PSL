(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_35
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun dropWhile :: "('a => bool) => 'a list => 'a list" where
"dropWhile x (nil2) = nil2"
| "dropWhile x (cons2 z xs) =
     (if x z then dropWhile x xs else cons2 z xs)"

theorem property0 :
  "((dropWhile (% (x :: 'a) => False) xs) = xs)"
  oops

end
