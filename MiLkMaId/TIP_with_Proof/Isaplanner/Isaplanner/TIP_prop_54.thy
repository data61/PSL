(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_54
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun t22 :: "Nat => Nat => Nat" where
  "t22 (Z) y = y"
| "t22 (S z) y = S (t22 z y)"

fun t2 :: "Nat => Nat => Nat" where
  "t2 (Z) y = Z"
| "t2 (S z) (Z) = S z"
| "t2 (S z) (S x2) = t2 z x2"

lemma "t2 (t22 z y) y = z \<longrightarrow> t2 (S (t22 z y)) y = S z"
  apply(induct z arbitrary:)
   apply auto
  oops

theorem property0 : "((t2 (t22 m n) n) = m)"
  apply(induct n rule: t22.induct)
   apply clarsimp
   apply(induct_tac y)
    apply fastforce+
  apply clarsimp
  apply(induct_tac z)
   apply fastforce+
  oops

theorem property0 : "((t2 (t22 m n) n) = m)"
  apply(induct m arbitrary: )
   apply clarsimp
   apply(induct_tac n)
  apply fastforce+
  apply clarsimp
  oops (*difficult to proceed any further.*)

end