(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Derivation Bounds\<close>

text \<open>Starting from this point onwards we apply the results on matrices to derive
  complexity bounds in \isafor. So, here begins the connection to the definitions
  and prerequisites that have originally been defined within \isafor.

This theory contains the notion of a derivation bound.\<close>

theory Derivation_Bound
imports
  "Abstract-Rewriting.Abstract_Rewriting"
begin

definition deriv_bound :: "'a rel \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool"
where
  "deriv_bound r a n \<longleftrightarrow> \<not> (\<exists> b. (a, b) \<in> r ^^ Suc n)"

lemma deriv_boundI [intro?]:
  "(\<And>b m. n < m \<Longrightarrow> (a, b) \<in> r ^^ m \<Longrightarrow> False) \<Longrightarrow> deriv_bound r a n"
  by (auto simp: deriv_bound_def) (metis lessI relpow_Suc_I)

lemma deriv_boundE:
  assumes "deriv_bound r a n"
    and "(\<And>b m. n < m \<Longrightarrow> (a, b) \<in> r ^^ m \<Longrightarrow> False) \<Longrightarrow> P"
  shows "P"
  using assms(1)
  by (intro assms)
     (auto simp: deriv_bound_def relpow_add relcomp.simps dest!: less_imp_Suc_add, metis relpow_E2)

lemma deriv_bound_iff:
  "deriv_bound r a n \<longleftrightarrow> (\<forall>b m. n < m \<longrightarrow> (a, b) \<notin> r ^^ m)"
  by (auto elim: deriv_boundE intro: deriv_boundI)

lemma deriv_bound_empty [simp]:
  "deriv_bound {} a n"
  by (simp add: deriv_bound_def)

lemma deriv_bound_mono:
  assumes "m \<le> n" and "deriv_bound r a m"
  shows "deriv_bound r a n"
  using assms by (auto simp: deriv_bound_iff)

lemma deriv_bound_image: 
  assumes b: "deriv_bound r' (f a) n"
    and step: "\<And> a b. (a, b) \<in> r \<Longrightarrow> (f a, f b) \<in> r'\<^sup>+"
  shows "deriv_bound r a n"
proof
  fix b m
  assume "(a, b) \<in> r ^^ m"
  from relpow_image [OF step this] have "(f a, f b) \<in> r'\<^sup>+ ^^ m" .
  from trancl_steps_relpow [OF subset_refl this]
    obtain k where "k \<ge> m" and "(f a, f b) \<in> r' ^^ k" by auto
  moreover assume "n < m"
  moreover with deriv_bound_mono [OF _ b, of "m - 1"]
    have "deriv_bound r' (f a) (m - 1)" by simp
  ultimately show False using b by (simp add: deriv_bound_iff)
qed

lemma deriv_bound_subset:
  assumes "r \<subseteq> r'\<^sup>+"
    and b: "deriv_bound r' a n"
  shows "deriv_bound r a n"
  using assms by (intro deriv_bound_image [of _ "\<lambda>x. x", OF b]) auto

lemma deriv_bound_SN_on:
  assumes "deriv_bound r a n"
  shows "SN_on r {a}"
proof
  fix f
  assume steps: "\<forall> i. (f i, f (Suc i)) \<in> r" and "f 0 \<in> {a}"
  with assms have "(f 0, f (Suc n)) \<notin> r ^^ Suc n" by (blast elim: deriv_boundE)
  moreover have "(f 0, f (Suc n)) \<in> r ^^ Suc n"
    using steps unfolding relpow_fun_conv by (intro exI [of _ f]) auto
  ultimately show False ..
qed

lemma deriv_bound_steps:
  assumes "(a, b) \<in> r ^^ n"
    and "deriv_bound r a m"
  shows "n \<le> m"
  using assms by (auto iff: not_less deriv_bound_iff)
end
