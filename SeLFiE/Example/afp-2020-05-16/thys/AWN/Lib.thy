(*  Title:       Lib.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Generic functions and lemmas"

theory Lib
imports Main
begin

definition
  TT :: "'a \<Rightarrow> bool"
where
  "TT = (\<lambda>_. True)"

lemma TT_True [intro, simp]: "TT a"
  unfolding TT_def by simp

lemma in_set_tl: "x \<in> set (tl xs) \<Longrightarrow> x \<in> set xs"
  by (metis Nil_tl insert_iff list.collapse set_simps(2))

lemma nat_le_eq_or_lt [elim]:
    fixes x :: nat
  assumes "x \<le> y"
      and eq: "x = y \<Longrightarrow> P x y"
      and lt: "x < y \<Longrightarrow> P x y"
    shows "P x y"
  using assms unfolding nat_less_le by auto

lemma disjoint_commute:
  "(A \<inter> B = {}) \<Longrightarrow> (B \<inter> A = {})"
  by auto

definition
  default :: "('i \<Rightarrow> 's) \<Rightarrow> ('i \<Rightarrow> 's option) \<Rightarrow> ('i \<Rightarrow> 's)"
where
  "default df f = (\<lambda>i. case f i of None \<Rightarrow> df i | Some s \<Rightarrow> s)"

end
