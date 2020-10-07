(* License: LGPL *)
(*
Author: Julian Parsert <julian.parsert@gmail.com>
Author: Cezary Kaliszyk
*)


theory Common
  imports
    "HOL-Analysis.Analysis"
    "../Preferences"
    "../Utility_Functions"
    "../Argmax"
begin


section \<open> Pareto Ordering \<close>

text \<open> Allows us to define a Pareto Ordering. \<close>

locale pareto_ordering =
  fixes agents :: "'i set"
  fixes U :: "'i \<Rightarrow> 'a \<Rightarrow> real"
begin
notation U ("U[_]")

definition pareto_dominating (infix "\<succ>Pareto"  60)
  where
    "X \<succ>Pareto Y \<longleftrightarrow>
      (\<forall>i \<in> agents. U[i] (X i) \<ge> U[i] (Y i)) \<and>
      (\<exists>i \<in> agents. U[i] (X i) > U[i] (Y i))"

lemma trans_strict_pareto: "X \<succ>Pareto Y \<Longrightarrow> Y \<succ>Pareto Z \<Longrightarrow> X \<succ>Pareto Z"
proof -
  assume a1: "X \<succ>Pareto Y"
  assume "Y \<succ>Pareto Z"
  then have f3: "\<forall>i \<in> agents. U[i] (Z i) \<le> U[i] (X i)"
    by (meson a1 order_trans pareto_dominating_def)
  moreover have "\<exists>i \<in> agents. \<not> U[i] (X i) \<le> U[i] (Y i)"
    using a1 pareto_dominating_def by fastforce
  ultimately show ?thesis
    by (metis \<open>Y \<succ>Pareto Z\<close> less_eq_real_def pareto_dominating_def)
qed

lemma anti_sym_strict_pareto: "X \<succ>Pareto Y \<Longrightarrow> \<not>Y \<succ>Pareto X"
  using pareto_dominating_def by auto

end

subsection \<open> Budget constraint\<close>

text \<open> Definition returns all afforedable bundles given wealth W \<close>
text \<open> f is a function that computes the value given a bundle\<close>
definition budget_constraint
  where
    "budget_constraint f S W = {x \<in> S. f x \<le> W}"


subsection \<open> Feasiblity \<close>

definition feasible_private_ownership
  where
    "feasible_private_ownership A F \<E> Cs Ps X Y \<longleftrightarrow>
      (\<Sum>i\<in>A. X i) \<le> (\<Sum>i\<in>A. \<E> i) + (\<Sum>j\<in>F. Y j) \<and>
      (\<forall>i\<in>A. X i \<in> Cs) \<and> (\<forall>j\<in>F. Y j \<in> Ps j)"

lemma feasible_private_ownershipD:
  assumes "feasible_private_ownership A F \<E> Cs Ps X Y"
  shows "(\<Sum>i\<in>A. X i) \<le> (\<Sum>i\<in>A. \<E> i) + (\<Sum>j\<in>F. Y j)"
    and "(\<forall>i\<in>A. X i \<in> Cs)" and "(\<forall>j\<in>F. Y j \<in> Ps j)"
  using assms feasible_private_ownership_def apply blast
  by (meson assms feasible_private_ownership_def)
    (meson assms feasible_private_ownership_def)

end
