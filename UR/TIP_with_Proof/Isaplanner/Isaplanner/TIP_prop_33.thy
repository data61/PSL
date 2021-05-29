(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_33
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun x :: "Nat => Nat => bool" where
  "x (Z) (Z) = True"
| "x (Z) (S z2) = False"
| "x (S x2) (Z) = False"
| "x (S x2) (S y2) = x x2 y2"

fun min :: "Nat => Nat => Nat" where
  "min (Z) z = Z"
| "min (S z2) (Z) = Z"
| "min (S z2) (S y1) = S (min z2 y1)"

fun t2 :: "Nat => Nat => bool" where
  "t2 (Z) z = True"
| "t2 (S z2) (Z) = False"
| "t2 (S z2) (S x2) = t2 z2 x2"

theorem property0 :(* A bit similar to TIP_prop_24.thy *)
  "((x (min a b) a) = (t2 a b))"
  find_proof DInd
  apply (induct rule: TIP_prop_33.x.induct)
     apply auto
  done 
    (*Why does "x.induct" lead to the shortest proof?
  Because "x"'s pattern-matching is complete, meaning that it does not involve any wild-card.*)

end