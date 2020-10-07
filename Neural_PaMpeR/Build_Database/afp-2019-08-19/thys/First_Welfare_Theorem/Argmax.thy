(* License: LGPL *)


section \<open>Arg Min and Arg Max sets\<close>

theory Argmax
  imports
    "HOL-Analysis.Analysis"
begin

subsection \<open> Definitions and Lemmas by Julian Parsert \<close>


text \<open> definition of argmax and argmin returing a set. \<close>

definition arg_min_set :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where
    "arg_min_set f S = {x. is_arg_min f (\<lambda>x. x\<in>S) x}"

definition arg_max_set :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where
    "arg_max_set f S = {x. is_arg_max f (\<lambda>x. x\<in>S) x}"


text \<open> Useful lemmas for @{term "arg_max_set"} and @{term "arg_min_set"}. \<close>

lemma no_better_in_s:
  assumes "x \<in> arg_max_set f S"
  shows "\<nexists>y. y \<in> S \<and> (f y) > (f x)"
  by (metis arg_max_set_def assms is_arg_max_def mem_Collect_eq)

lemma argmax_sol_in_s:
  assumes "x \<in> arg_max_set f S"
  shows "x \<in> S"
  by (metis CollectD arg_max_set_def assms is_arg_max_def)

lemma leq_all_in_sol:
  fixes f :: "'a \<Rightarrow> ('b :: preorder)"
  assumes "x \<in> arg_max_set f S"
  shows "\<forall>y \<in> S. f y \<ge> f x \<longrightarrow> y \<in> arg_max_set f S"
  using assms le_less_trans by (auto simp: arg_max_set_def is_arg_max_def)

lemma all_leq:
  fixes f :: "'a \<Rightarrow> ('b :: linorder)"
  assumes "x \<in> arg_max_set f S"
  shows "\<forall>y \<in> S. f x \<ge> f y"
  by (meson assms leI no_better_in_s)

lemma all_in_argmax_equal:
  fixes f :: "'a \<Rightarrow> ('b :: linorder)"
  assumes "x \<in> arg_max_set f S"
  shows "\<forall>y \<in> arg_max_set f S. f x = f y"
    by (meson all_leq argmax_sol_in_s assms le_less no_better_in_s)

end
