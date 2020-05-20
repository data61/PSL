theory Refine_Folds
imports
  Autoref_Misc
begin

section \<open>Fold binary predicate over finite nonempty set\<close>

definition "FOLD_bin_ne b X = do {
  ASSERT (X \<noteq> {});
  x \<leftarrow> SPEC (\<lambda>x. x \<in> X);
  let X = X - {x};
  FOREACH X (\<lambda>x r. RETURN (b x r)) x
}"

lemma Fold_bin_spec:
  assumes 1: "X \<noteq> {}"
  assumes 2: "finite X"
  assumes refl: "\<And>x. c x x"
  assumes idem1: "\<And>x y. c (b x y) x"
  assumes idem2: "\<And>x y. c (b x y) y"
  assumes trans: "\<And>x y z. c x y \<Longrightarrow> c y z \<Longrightarrow> c x z"
  shows "FOLD_bin_ne b X \<le> SPEC (\<lambda>r. \<forall>x \<in> X. c r x)"
  using 1 2
  unfolding FOLD_bin_ne_def
  apply refine_vcg
  subgoal for x
    apply (rule FOREACH_rule[where I = "\<lambda>it r. (\<forall>x \<in> (insert x (X - {x} - it)). c r x)"])
    subgoal by simp
    subgoal by (simp add: refl)
    subgoal
      using idem1 idem2 trans
      by simp fast
    subgoal by simp
    done
  done

subsection \<open>@{term Inf}/@{term Sup}/@{term Max}/@{term Min}\<close>

lemma inf_Inf_absorb[simp]:
  fixes x::"'a::conditionally_complete_lattice"
  shows "x \<in> X \<Longrightarrow> finite X \<Longrightarrow> inf x (Inf X) = Inf X"
  by (subst cInf_insert[symmetric]) (auto simp: insert_absorb)

lemma sup_Sup_absorb[simp]:
  fixes x::"'a::conditionally_complete_lattice"
  shows "x \<in> X \<Longrightarrow> finite X \<Longrightarrow> sup x (Sup X) = Sup X"
  by (subst cSup_insert[symmetric]) (auto simp: insert_absorb)

definition "Inf_ne X = FOLD_bin_ne inf X"
definition "Sup_ne X = FOLD_bin_ne sup X"
definition "Min_ne X = FOLD_bin_ne min X"
definition "Max_ne X = FOLD_bin_ne max X"
lemma [autoref_itype]:
  "Inf_ne ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_nres"
  "Sup_ne ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_nres"
  "Min_ne ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_nres"
  "Max_ne ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_nres"
  by simp_all

lemma Inf_ne_spec:
  fixes X::"'a::conditionally_complete_lattice set"
  assumes "X \<noteq> {}"
  assumes "finite X"
  shows "Inf_ne X \<le> SPEC (\<lambda>r. r = Inf X)"
  using assms
  unfolding Inf_ne_def FOLD_bin_ne_def
  apply refine_vcg
  apply (rule_tac I = "\<lambda>it r. r = (Inf (insert x (X - {x} - it)))" in FOREACH_rule)
  apply (auto simp: assms it_step_insert_iff cInf_insert_If ac_simps)
  done

lemma Sup_ne_spec:
  fixes X::"'a::conditionally_complete_lattice set"
  assumes "X \<noteq> {}"
  assumes "finite X"
  shows "Sup_ne X \<le> SPEC (\<lambda>r. r = Sup X)"
  using assms
  unfolding Sup_ne_def  FOLD_bin_ne_def
  apply (refine_rcg refine_vcg)
  apply (rule_tac I = "\<lambda>it r. r = (Sup (insert x (X - {x} - it)))" in FOREACH_rule)
  apply (auto simp: assms it_step_insert_iff cSup_insert_If ac_simps)
  done

lemma Min_ne_spec:
  fixes X::"'a::linorder set"
  assumes "X \<noteq> {}"
  assumes "finite X"
  shows "Min_ne X \<le> SPEC (\<lambda>r. r = Min X)"
  using assms
  unfolding Min_ne_def  FOLD_bin_ne_def
  apply refine_vcg
  apply (rule_tac I = "\<lambda>it r. r = (Min (insert x (X - {x} - it)))" in FOREACH_rule)
  apply (auto simp: assms it_step_insert_iff Min.insert_remove ac_simps)
  done

lemma Max_ne_spec:
  fixes X::"'a::linorder set"
  assumes "X \<noteq> {}"
  assumes "finite X"
  shows "Max_ne X \<le> SPEC (\<lambda>r. r = Max X)"
  using assms
  unfolding Max_ne_def  FOLD_bin_ne_def
  apply refine_vcg
  apply (rule_tac I = "\<lambda>it r. r = (Max (insert x (X - {x} - it)))" in FOREACH_rule)
  apply (auto simp: assms it_step_insert_iff Max.insert_remove ac_simps Max.in_idem)
  done

subsection \<open>Implementations\<close>
context includes autoref_syntax begin

schematic_goal FOLD_bin_ne_impl:
  assumes [autoref_rules(overloaded)]: "(del_impl,op_set_delete) \<in> R \<rightarrow> \<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>C"
  assumes [autoref_rules(overloaded)]: "(pick_impl,op_set_pick) \<in> \<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>nres_rel"
  assumes [autoref_ga_rules]: "is_set_to_list R C tsl"
  assumes[unfolded comps, autoref_rules(overloaded)]: "(bi, b) \<in> R \<rightarrow> R \<rightarrow> R"
  assumes[autoref_rules]: "(Xi, X) \<in> \<langle>R\<rangle>C"
  shows "(?f, (OP FOLD_bin_ne ::: ((R \<rightarrow> R \<rightarrow> R) \<rightarrow> \<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>nres_rel)) $ b $ X) \<in> \<langle>R\<rangle>nres_rel"
  unfolding FOLD_bin_ne_def[abs_def] autoref_tag_defs comps
  by (autoref_monadic (plain))
concrete_definition FOLD_bin_ne_impl uses FOLD_bin_ne_impl
lemmas [autoref_rules(overloaded)] = FOLD_bin_ne_impl.refine [OF GEN_OP_D GEN_OP_D SIDE_GEN_ALGO_D]
  \<comment> \<open>TODO: really? overloaded here?\<close>

schematic_goal Inf_ne_impl:
  assumes [autoref_rules(overloaded)]: "(del_impl,op_set_delete) \<in> R \<rightarrow> \<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>C"
  assumes [autoref_rules(overloaded)]: "(pick_impl,op_set_pick) \<in> \<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>nres_rel"
  assumes [autoref_ga_rules]: "is_set_to_list R C tsl"
  assumes[autoref_rules(overloaded)]: "(infi, inf) \<in> R \<rightarrow> R \<rightarrow> R"
  assumes[autoref_rules]: "(Xi, X) \<in> \<langle>R\<rangle>C"
  shows "(?f, (OP Inf_ne ::: (\<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>nres_rel)) $ X) \<in> \<langle>R\<rangle>nres_rel"
  unfolding Inf_ne_def[abs_def] FOLD_bin_ne_def[abs_def] autoref_tag_defs
  by (autoref_monadic (plain))
concrete_definition Inf_ne_impl uses Inf_ne_impl
lemmas [autoref_rules(overloaded)] = Inf_ne_impl.refine [OF GEN_OP_D GEN_OP_D SIDE_GEN_ALGO_D]

schematic_goal Sup_ne_impl:
  assumes [autoref_rules(overloaded)]: "(del_impl,op_set_delete) \<in> R \<rightarrow> \<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>C"
  assumes [autoref_rules(overloaded)]: "(pick_impl,op_set_pick) \<in> \<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>nres_rel"
  assumes [autoref_ga_rules]: "is_set_to_list R C tsl"
  assumes[autoref_rules(overloaded)]: "(supi, sup) \<in> R \<rightarrow> R \<rightarrow> R"
  assumes[autoref_rules]: "(Xi, X) \<in> \<langle>R\<rangle>C"
  shows "(?f, (OP Sup_ne ::: (\<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>nres_rel)) $ X) \<in> \<langle>R\<rangle>nres_rel"
  unfolding Sup_ne_def[abs_def] FOLD_bin_ne_def[abs_def] autoref_tag_defs
  by (autoref_monadic (plain))
concrete_definition Sup_ne_impl uses Sup_ne_impl
lemmas [autoref_rules(overloaded)] = Sup_ne_impl.refine [OF GEN_OP_D GEN_OP_D SIDE_GEN_ALGO_D]

schematic_goal Min_ne_impl:
  assumes [autoref_rules(overloaded)]: "(del_impl,op_set_delete) \<in> R \<rightarrow> \<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>C"
  assumes [autoref_rules(overloaded)]: "(pick_impl,op_set_pick) \<in> \<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>nres_rel"
  assumes [autoref_ga_rules]: "is_set_to_list R C tsl"
  assumes[autoref_rules(overloaded)]: "(mini, min) \<in> R \<rightarrow> R \<rightarrow> R"
  assumes[autoref_rules]: "(Xi, X) \<in> \<langle>R\<rangle>C"
  shows "(?f, (OP Min_ne ::: (\<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>nres_rel)) $ X) \<in> \<langle>R\<rangle>nres_rel"
  unfolding Min_ne_def[abs_def] FOLD_bin_ne_def[abs_def] autoref_tag_defs
  by (autoref_monadic (plain))
concrete_definition Min_ne_impl uses Min_ne_impl
lemmas [autoref_rules(overloaded)] = Min_ne_impl.refine [OF GEN_OP_D GEN_OP_D SIDE_GEN_ALGO_D]

schematic_goal Max_ne_impl:
  assumes [autoref_rules(overloaded)]: "(del_impl,op_set_delete) \<in> R \<rightarrow> \<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>C"
  assumes [autoref_rules(overloaded)]: "(pick_impl,op_set_pick) \<in> \<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>nres_rel"
  assumes [autoref_ga_rules]: "is_set_to_list R C tsl"
  assumes[autoref_rules(overloaded)]: "(maxi, max) \<in> R \<rightarrow> R \<rightarrow> R"
  assumes[autoref_rules]: "(Xi, X) \<in> \<langle>R\<rangle>C"
  shows "(?f, (OP Max_ne ::: (\<langle>R\<rangle>C \<rightarrow> \<langle>R\<rangle>nres_rel)) $ X) \<in> \<langle>R\<rangle>nres_rel"
  unfolding Max_ne_def[abs_def] FOLD_bin_ne_def[abs_def] autoref_tag_defs
  by (autoref_monadic (plain))
concrete_definition Max_ne_impl uses Max_ne_impl
lemmas [autoref_rules(overloaded)] = Max_ne_impl.refine [OF GEN_OP_D GEN_OP_D SIDE_GEN_ALGO_D]

end

end
