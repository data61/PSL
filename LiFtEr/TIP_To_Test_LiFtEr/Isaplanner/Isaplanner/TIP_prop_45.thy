(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_45
  imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun zip :: "'a list => 'b list => (('a, 'b) pair) list" where
  "zip (nil2) y = nil2"
| "zip (cons2 z x2) (nil2) = nil2"
| "zip (cons2 z x2) (cons2 x3 x4) = cons2 (pair2 z x3) (zip x2 x4)"

theorem property0 :
  "((zip (cons2 x xs) (cons2 y ys)) =
      (cons2 (pair2 x y) (zip xs ys)))"
  oops

end
