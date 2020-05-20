(* Author: Matthias Brun,   ETH Zürich, 2019 *)
(* Author: Dmitriy Traytel, ETH Zürich, 2019 *)

section \<open>Preliminaries\<close>

(*<*)
theory Nominal2_Lemmas
  imports "Nominal2.Nominal2"
begin
(*>*)

text \<open>Auxiliary freshness lemmas and simplifier setup.\<close>

declare
  fresh_star_Pair[simp] fresh_star_insert[simp] fresh_Nil[simp]
  pure_supp[simp] pure_fresh[simp]

lemma fresh_star_Nil[simp]: "{} \<sharp>* t"
  unfolding fresh_star_def by auto

lemma supp_flip[simp]:
  fixes a b :: "_ :: at"
  shows "supp (a \<leftrightarrow> b) = (if a = b then {} else {atom a, atom b})"
  by (auto simp: flip_def supp_swap)

lemma Abs_lst_eq_flipI:
  fixes a b :: "_ :: at" and t :: "_ :: fs"
  assumes "atom b \<sharp> t"
  shows "[[atom a]]lst. t = [[atom b]]lst. (a \<leftrightarrow> b) \<bullet> t"
  by (metis Abs1_eq_iff(3) assms flip_commute flip_def swap_fresh_fresh)

lemma atom_not_fresh_eq:
  assumes "\<not> atom a \<sharp> x"
  shows   "a = x"
  using assms atom_eq_iff fresh_ineq_at_base by blast

lemma fresh_set_fresh_forall:
  shows "atom y \<sharp> xs = (\<forall>x \<in> set xs. atom y \<sharp> x)"
  by (induct xs) (simp_all add: fresh_Cons)

lemma finite_fresh_set_fresh_all[simp]:
  fixes S :: "(_ :: fs) set"
  shows "finite S \<Longrightarrow> atom a \<sharp> S \<longleftrightarrow> (\<forall>x \<in> S. atom a \<sharp> x)"
  unfolding fresh_def by (simp add: supp_of_finite_sets)

lemma case_option_eqvt[eqvt]:
  "p \<bullet> case_option a b opt = case_option (p \<bullet> a) (p \<bullet> b) (p \<bullet> opt)"
  by (cases opt) auto

(*<*)
end
(*>*)
