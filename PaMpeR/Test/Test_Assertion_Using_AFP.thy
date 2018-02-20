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
  "Coinductive/Coinductive_List"
  "Landau_Symbols/Landau_Library"
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

lemma
  assumes "True"
  shows "True"
  assert_nth_true 1
  assert_nth_false 2
  assert_nth_true 1
  asserts_check [1, 0, 0]
    apply simp
  done

lemma "case True of True \<Rightarrow> True | _ \<Rightarrow> True"
  assert_nth_true 2
  by simp_all

lemma "x \<and> x"
  assert_nth_false 3
  assert_nth_true 46
  oops

lemma "x \<or> x"
  assert_nth_true 47
  oops

lemma "\<not> False"
  assert_nth_true 48
  oops

lemma "\<And>x. x \<and> x"
  assert_nth_false 4
  assert_nth_true 30
  assert_nth_false 46
    oops

lemma "x \<Longrightarrow> x"
    assert_nth_true 28
    oops

lemma "\<exists>x. True \<and> x"
  assert_nth_true 32
  oops

lemma "\<exists>x. True \<and> x"
  assert_nth_true 32
  assert_nth_true 15 (*?*) (* these quantifiers are actually functions?*)
  oops

lemma "(\<exists>x. True \<and> x) \<and> True"
  assert_nth_false 32
  assert_nth_true 39
  oops

lemma "(\<forall>x. True \<and> x) \<and> True"
  assert_nth_true 38
  oops

lemma "(\<exists>x. True \<and> x)"
  assert_nth_false 39
  oops

lemma "True \<and> (\<forall>x. x =x)"
  assert_nth_true 38
  assert_nth_false 39
    oops

lemma "True \<Longrightarrow> (\<And>x. x =x)"
  assert_nth_true 37
  assert_nth_true 28
  assert_nth_true 37
  oops

schematic_goal "?x = True"
  assert_nth_true 18
  oops

schematic_goal "True \<or> False" "?x = True"
  apply -
  assert_nth_false 18
  assert_nth_true 21
   prefer 2
  assert_nth_true 18
  oops

lemma "True \<longrightarrow> True"
  apply -
  assert_nth_false 31
  assert_nth_false 36
  oops

lemma "True \<or> False" "\<forall>x. True \<or> x"
  assert_nth_false 31
  asserts_check [0,0,0,0]
  defer
  asserts_check [0,0,0,0]
  assert_nth_true 31
  by auto

definition "MyTrue \<equiv> True"

lemma "MyTrue"
  assert_nth_false 21
  by (simp add: MyTrue_def)

find_theorems  name:"psimp" -name:"nitpick" name:"transpose"
lemma "transpose [] = []"
  assert_nth_true 5 (*pinduct*)
  assert_nth_true 6 (*psimp*)
  oops

find_theorems  name:"cases"
lemma "Option.Some True = Option.Some True"
  assert_nth_true 8 (*caeses*)
  oops

lemma "True \<and> (Option.None = Option.None)"
  apply (rule conjI)
   assert_nth_false 8 (*cases*)
   apply auto[1]
  assert_nth_true 8 (*cases*)
  oops

find_theorems name:"intros" name:"sorted"
lemma "sorted []"
  assert_nth_true 9 (*intros*)
  assert_nth_true 10 (*recursive simp exists sorted*)
  oops

primrec power::"Nat.nat \<Rightarrow> Nat.nat \<Rightarrow> Nat.nat" where
  "power x (Suc n) = times x (power x n)"
| "power x 0 = x"

print_theorems

lemma "power 0 0 = 0"
  assert_nth_false 1 (*local assumption*)
  assert_nth_true 10 (*recursive simp*)
  oops

lemma
  assumes my_ass:"True"
  shows "True"
  find_theorems name:"local"
  find_theorems name:"my_ass"
  assert_nth_true 1 (*local assumption*)
  assert_nth_false 11 (*Num*)
  oops

lemma "\<And>x. (1::Real.real) = 1" assert_nth_false 83
  assert_nth_true 84 assert_nth_true 85
  oops

lemma "\<And>x. (1::Rat.rat) + 1 > 2" assert_nth_true 83
  assert_nth_true 84 assert_nth_true 85
  oops

inductive evn :: "Nat.nat \<Rightarrow> bool" where
zero: "evn 0" |
step: "evn n \<Longrightarrow> evn (Suc (Suc n))"

lemma "\<And>x. evn 0 \<Longrightarrow> True" "False"
  apply - assert_nth_true 82
  oops

lemma "\<And>x. False \<Longrightarrow> evn 0" "False"
  apply - assert_nth_false 82
  oops

lemma "False" "\<And>x. False \<Longrightarrow> evn 0" 
  apply - assert_nth_false 82
  oops


lemma "\<And>x. False \<Longrightarrow> True" "False"
  apply - assert_nth_false 82
  oops

lemma "\<And>x. (True \<longrightarrow> True) \<Longrightarrow> True" "False"
  apply - assert_nth_false 82
  oops

lemma "\<And>x. (True \<and> True) \<Longrightarrow> True" "False"
  apply - assert_nth_false 82
  oops
end