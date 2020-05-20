(*  Title:      Util_Set.thy
    Date:       Feb 2008
    Author:     David Trachtenherz
*)

section \<open>Convenience results for set quantifiers\<close>

theory Util_Set
imports Main
begin

subsection \<open>Some auxiliary results for HOL rules\<close>

lemma conj_disj_absorb: "(P \<and> Q \<or> Q) = Q" by blast
lemma disj_eq_distribL: "((a \<or> b) = (a \<or> c)) = (a \<or> (b = c))" by blast
lemma disj_eq_distribR: "((a \<or> c) = (b \<or> c)) = ((a = b) \<or> c)" by blast


subsubsection \<open>Some auxiliary results for  \<open>Let\<close>\<close>

lemma Let_swap: "f (let x=a in g x) = (let x=a in f (g x))" by simp


subsubsection \<open>Some auxiliary \<open>if\<close>-rules\<close>

lemma if_P': "\<lbrakk> P; x = z \<rbrakk> \<Longrightarrow> (if P then x else y) = z" by simp
lemma if_not_P': "\<lbrakk> \<not> P; y = z \<rbrakk> \<Longrightarrow> (if P then x else y) = z" by simp

lemma if_P_both: "\<lbrakk> Q x; Q y \<rbrakk> \<Longrightarrow> Q (if P then x else y)" by simp
lemma if_P_both_in_set: "\<lbrakk> x \<in> s; y \<in> s \<rbrakk> \<Longrightarrow> (if P then x else y) \<in> s" by simp


subsubsection \<open>Some auxiliary rules for function composition\<close>

lemma comp2_conv: "f1 \<circ> f2 = (\<lambda>x. f1 (f2 x))" by (simp add: comp_def)
lemma comp3_conv: "f1 \<circ> f2 \<circ> f3 = (\<lambda>x. f1 (f2 (f3 x)))" by (simp add: comp_def)


subsection \<open>Some auxiliary lemmata for quantifiers\<close>

subsubsection \<open>Auxiliary results for universal and existential quantifiers\<close>

lemma ball_cong2: "
  \<lbrakk> I \<subseteq> A; \<forall>x\<in>A. f x = g x \<rbrakk> \<Longrightarrow> (\<forall>x\<in>I. P (f x)) = (\<forall>x\<in>I. P (g x))" by fastforce
lemma bex_cong2: "
  \<lbrakk> I \<subseteq> A; \<forall>x\<in>I. f x = g x \<rbrakk> \<Longrightarrow> (\<exists>x\<in>I. P (f x)) = (\<exists>x\<in>I. P (g x))" by simp
lemma ball_all_cong: "
  \<forall>x. f x = g x \<Longrightarrow> (\<forall>x\<in>I. P (f x)) = (\<forall>x\<in>I. P (g x))" by simp
lemma bex_all_cong: "
  \<forall>x. f x = g x \<Longrightarrow> (\<exists>x\<in>I. P (f x)) = (\<exists>x\<in>I. P (g x))" by simp
lemma all_cong: "
  \<forall>x. f x = g x \<Longrightarrow> (\<forall>x. P (f x)) = (\<forall>x. P (g x))" by simp
lemma ex_cong: "
  \<forall>x. f x = g x \<Longrightarrow> (\<exists>x. P (f x)) = (\<exists>x. P (g x))" by simp

(*lemma all_eqI: "(\<And>x. P x = Q x) \<Longrightarrow> (\<forall>x. P x) = (\<forall>x. Q x)"*)
lemmas all_eqI = iff_allI
(*lemma ex_eqI: "(\<And>x. P x = Q x) \<Longrightarrow> (\<exists>x. P x) = (\<exists>x. Q x)"*)
lemmas ex_eqI = iff_exI

lemma all_imp_eqI: "
  \<lbrakk> P = P'; \<And>x. P x \<Longrightarrow> Q x = Q' x \<rbrakk> \<Longrightarrow>
  (\<forall>x. P x \<longrightarrow> Q x) = (\<forall>x. P' x \<longrightarrow> Q' x)"
by blast
lemma ex_imp_eqI: "
  \<lbrakk> P = P'; \<And>x. P x \<Longrightarrow> Q x = Q' x \<rbrakk> \<Longrightarrow>
  (\<exists>x. P x \<and> Q x) = (\<exists>x. P' x \<and> Q' x)"
by blast


subsubsection \<open>Auxiliary results for \<open>empty\<close> sets\<close>

lemma empty_imp_not_in: "x \<notin> {}" by blast
lemma ex_imp_not_empty: "\<exists>x. x \<in> A \<Longrightarrow> A \<noteq> {}" by blast
lemma in_imp_not_empty: "x \<in> A \<Longrightarrow> A \<noteq> {}" by blast
lemma not_empty_imp_ex: "A \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A" by blast
lemma not_ex_in_conv: "(\<not> (\<exists>x. x \<in> A)) = (A = {})" by blast


subsubsection \<open>Some auxiliary results for subset and membership relation\<close>

lemma bex_subset_imp_bex: "\<lbrakk> \<exists>x\<in>A. P x; A \<subseteq> B \<rbrakk> \<Longrightarrow> \<exists>x\<in>B. P x" by blast
lemma bex_imp_ex: "\<exists>x\<in>A. P x \<Longrightarrow> \<exists>x. P x" by blast
lemma ball_subset_imp_ball: "\<lbrakk> \<forall>x\<in>B. P x; A \<subseteq> B \<rbrakk> \<Longrightarrow> \<forall>x\<in>A. P x" by blast
lemma all_imp_ball: "\<forall>x. P x \<Longrightarrow> \<forall>x\<in>A. P x" by blast

lemma mem_Collect_eq_not: "(a \<notin> {x. P x}) = (\<not> P a)" by blast
lemma Collect_not_in_imp_not: "a \<notin> {x. P x} \<Longrightarrow> \<not> P a" by blast
lemma Collect_not_imp_not_in: "\<not> P a \<Longrightarrow> a \<notin> {x. P x}" by blast
lemma Collect_is_subset: "{x \<in> A. P x} \<subseteq> A" by blast

end
