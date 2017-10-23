(* Title:  PSL/PaMpeR/Test/Test_Assertion_Using_AFP.thy
   Author: Yutaka Nagashima, CIIRC, CTU
*)
theory Test_Assertion_Using_AFP
  imports
  Assertion_Checker
  "~~/src/Doc/Datatypes/Datatypes"
  "Paraconsistency/Paraconsistency"
  "Native_Word/Native_Word_Test"
  "Buildings/Algebra"
  "LightweightJava/Lightweight_Java_Equivalence"
  "Word_Lib/Word_Lemmas"
  "Buildings/Chamber"
  "Buildings/Prelim"
  "Abortable_Linearizable_Modules/Consensus"
  "Name_Carrying_Type_Inference/SimplyTyped"
  "Coinductive_Languages/Coinductive_Language"
  "Ribbon_Proofs/More_Finite_Map"
begin

find_theorems name:"pelims" -name:"Quickcheck" -name:"Nitpick"
lemma "Datatypes.even Datatypes.Zero  = False"
  apply -
  assert_nth_true 7 (*pelims*)
  find_theorems name:"False" name:"psimps"
  assert_nth_true 6 (*fact_psimp*)
  oops

lemma "depth (\<pi> \<cdot> A) = depth A"
  assert_nth_true 12 (*lift_definition*)
  assert_nth_false 13 (*primcorec*)
  oops

lemma "Coinductive_Language.Plus Coinductive_Language.Zero r = r"
  assert_nth_true 13 (*primcorec*)
  oops

end