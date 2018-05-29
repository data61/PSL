(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_39
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "Nat => Nat => bool" where
"x (Z) (Z) = True"
| "x (Z) (S z2) = False"
| "x (S x2) (Z) = False"
| "x (S x2) (S y2) = x x2 y2"

fun count :: "Nat => Nat list => Nat" where
"count y (nil2) = Z"
| "count y (cons2 z2 ys) =
     (if x y z2 then S (count y ys) else count y ys)"

fun t2 :: "Nat => Nat => Nat" where
"t2 (Z) z = z"
| "t2 (S z2) z = S (t2 z2 z)"

theorem property0 :
  "((t2 (count n (cons2 y (nil2))) (count n xs)) =
      (count n (cons2 y xs)))"
  oops

end
