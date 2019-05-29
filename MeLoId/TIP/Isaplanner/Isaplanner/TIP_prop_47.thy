(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_47
  imports "../../Test_Base"
begin

datatype 'a Tree = Leaf | Node "'a Tree" "'a" "'a Tree"

datatype Nat = Z | S "Nat"

fun mirror :: "'a Tree => 'a Tree" where
  "mirror (Leaf) = Leaf"
| "mirror (Node l y r) = Node (mirror r) y (mirror l)"

fun max :: "Nat => Nat => Nat" where
  "max (Z) y = y"
| "max (S z) (Z) = S z"
| "max (S z) (S x2) = S (max z x2)"

fun height :: "'a Tree => Nat" where
  "height (Leaf) = Z"
| "height (Node l y r) = S (max (height l) (height r))"

theorem property0 :
  "((height (mirror a1)) = (height a1))"
  oops

end
