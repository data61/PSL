(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_44
imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun zip :: "'a list => 'b list => (('a, 'b) pair) list" where
"zip (nil2) y = nil2"
| "zip (cons2 z x2) (nil2) = nil2"
| "zip (cons2 z x2) (cons2 x3 x4) = cons2 (pair2 z x3) (zip x2 x4)"

fun zipConcat :: "'a => 'a list => 'b list =>
                  (('a, 'b) pair) list" where
"zipConcat x y (nil2) = nil2"
| "zipConcat x y (cons2 y2 ys) = cons2 (pair2 x y2) (zip y ys)"

theorem property0 :
  "((zip (cons2 x xs) ys) = (zipConcat x xs ys))"
  oops

end
