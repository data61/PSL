(*  Title:       Herbrand Interpretation
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Herbrand Intepretation\<close>

theory Herbrand_Interpretation
  imports Clausal_Logic
begin

text \<open>
The material formalized here corresponds roughly to Sections 2.2 (``Herbrand
Interpretations'') of Bachmair and Ganzinger, excluding the formula and term
syntax.

A Herbrand interpretation is a set of ground atoms that are to be considered true.
\<close>

type_synonym 'a interp = "'a set"

definition true_lit :: "'a interp \<Rightarrow> 'a literal \<Rightarrow> bool" (infix "\<Turnstile>l" 50) where
  "I \<Turnstile>l L \<longleftrightarrow> (if is_pos L then (\<lambda>P. P) else Not) (atm_of L \<in> I)"

lemma true_lit_simps[simp]:
  "I \<Turnstile>l Pos A \<longleftrightarrow> A \<in> I"
  "I \<Turnstile>l Neg A \<longleftrightarrow> A \<notin> I"
  unfolding true_lit_def by auto

lemma true_lit_iff[iff]: "I \<Turnstile>l L \<longleftrightarrow> (\<exists>A. L = Pos A \<and> A \<in> I \<or> L = Neg A \<and> A \<notin> I)"
  by (cases L) simp+

definition true_cls :: "'a interp \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<Turnstile>" 50) where
  "I \<Turnstile> C \<longleftrightarrow> (\<exists>L \<in># C. I \<Turnstile>l L)"

lemma true_cls_empty[iff]: "\<not> I \<Turnstile> {#}"
  unfolding true_cls_def by simp

lemma true_cls_singleton[iff]: "I \<Turnstile> {#L#} \<longleftrightarrow> I \<Turnstile>l L"
  unfolding true_cls_def by simp

lemma true_cls_add_mset[iff]: "I \<Turnstile> add_mset C D \<longleftrightarrow> I \<Turnstile>l C \<or> I \<Turnstile> D"
  unfolding true_cls_def by auto

lemma true_cls_union[iff]: "I \<Turnstile> C + D \<longleftrightarrow> I \<Turnstile> C \<or> I \<Turnstile> D"
  unfolding true_cls_def by auto

lemma true_cls_mono: "set_mset C \<subseteq> set_mset D \<Longrightarrow> I \<Turnstile> C \<Longrightarrow> I \<Turnstile> D"
  unfolding true_cls_def subset_eq by metis

lemma
  assumes "I \<subseteq> J"
  shows
    false_to_true_imp_ex_pos: "\<not> I \<Turnstile> C \<Longrightarrow> J \<Turnstile> C \<Longrightarrow> \<exists>A \<in> J. Pos A \<in># C" and
    true_to_false_imp_ex_neg: "I \<Turnstile> C \<Longrightarrow> \<not> J \<Turnstile> C \<Longrightarrow> \<exists>A \<in> J. Neg A \<in># C"
  using assms unfolding subset_iff true_cls_def by (metis literal.collapse true_lit_simps)+

lemma true_cls_replicate_mset[iff]: "I \<Turnstile> replicate_mset n L \<longleftrightarrow> n \<noteq> 0 \<and> I \<Turnstile>l L"
  by (simp add: true_cls_def)

lemma pos_literal_in_imp_true_cls[intro]: "Pos A \<in># C \<Longrightarrow> A \<in> I \<Longrightarrow> I \<Turnstile> C"
  using true_cls_def by blast

lemma neg_literal_notin_imp_true_cls[intro]: "Neg A \<in># C \<Longrightarrow> A \<notin> I \<Longrightarrow> I \<Turnstile> C"
  using true_cls_def by blast

lemma pos_neg_in_imp_true: "Pos A \<in># C \<Longrightarrow> Neg A \<in># C \<Longrightarrow> I \<Turnstile> C"
  using true_cls_def by blast

definition true_clss :: "'a interp \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>s" 50) where
  "I \<Turnstile>s CC \<longleftrightarrow> (\<forall>C \<in> CC. I \<Turnstile> C)"

lemma true_clss_empty[iff]: "I \<Turnstile>s {}"
  by (simp add: true_clss_def)

lemma true_clss_singleton[iff]: "I \<Turnstile>s {C} \<longleftrightarrow> I \<Turnstile> C"
  unfolding true_clss_def by blast

lemma true_clss_insert[iff]: "I \<Turnstile>s insert C DD \<longleftrightarrow> I \<Turnstile> C \<and> I \<Turnstile>s DD"
  unfolding true_clss_def by blast

lemma true_clss_union[iff]: "I \<Turnstile>s CC \<union> DD \<longleftrightarrow> I \<Turnstile>s CC \<and> I \<Turnstile>s DD"
  unfolding true_clss_def by blast

lemma true_clss_mono: "DD \<subseteq> CC \<Longrightarrow> I \<Turnstile>s CC \<Longrightarrow> I \<Turnstile>s DD"
  by (simp add: subsetD true_clss_def)

abbreviation satisfiable :: "'a clause set \<Rightarrow> bool" where
  "satisfiable CC \<equiv> \<exists>I. I \<Turnstile>s CC"

definition true_cls_mset :: "'a interp \<Rightarrow> 'a clause multiset \<Rightarrow> bool" (infix "\<Turnstile>m" 50) where
  "I \<Turnstile>m CC \<longleftrightarrow> (\<forall>C \<in># CC. I \<Turnstile> C)"

lemma true_cls_mset_empty[iff]: "I \<Turnstile>m {#}"
  unfolding true_cls_mset_def by auto

lemma true_cls_mset_singleton[iff]: "I \<Turnstile>m {#C#} \<longleftrightarrow> I \<Turnstile> C"
  by (simp add: true_cls_mset_def)

lemma true_cls_mset_union[iff]: "I \<Turnstile>m CC + DD \<longleftrightarrow> I \<Turnstile>m CC \<and> I \<Turnstile>m DD"
  unfolding true_cls_mset_def by auto

lemma true_cls_mset_add_mset[iff]: "I \<Turnstile>m add_mset C CC \<longleftrightarrow> I \<Turnstile> C \<and> I \<Turnstile>m CC"
  unfolding true_cls_mset_def by auto

lemma true_cls_mset_image_mset[iff]: "I \<Turnstile>m image_mset f A \<longleftrightarrow> (\<forall>x \<in># A. I \<Turnstile> f x)"
  unfolding true_cls_mset_def by auto

lemma true_cls_mset_mono: "set_mset DD \<subseteq> set_mset CC \<Longrightarrow> I \<Turnstile>m CC \<Longrightarrow> I \<Turnstile>m DD"
  unfolding true_cls_mset_def subset_iff by auto

lemma true_clss_set_mset[iff]: "I \<Turnstile>s set_mset CC \<longleftrightarrow> I \<Turnstile>m CC"
  unfolding true_clss_def true_cls_mset_def by auto

lemma true_cls_mset_true_cls: "I \<Turnstile>m CC \<Longrightarrow> C \<in># CC \<Longrightarrow> I \<Turnstile> C"
  using true_cls_mset_def by auto

end
