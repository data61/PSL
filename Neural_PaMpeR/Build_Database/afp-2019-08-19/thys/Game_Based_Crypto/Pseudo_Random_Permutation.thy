(* Title: Pseudo_Random_Permutation.thy
  Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Random permutation\<close>

theory Pseudo_Random_Permutation imports
  CryptHOL.Computational_Model
begin

locale random_permutation =
  fixes A :: "'b set"
begin

definition random_permutation :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> ('b \<times> ('a \<rightharpoonup> 'b)) spmf"
where
  "random_permutation \<sigma> x =
  (case \<sigma> x of Some y \<Rightarrow> return_spmf (y, \<sigma>)
   | None \<Rightarrow> spmf_of_set (A - ran \<sigma>) \<bind> (\<lambda>y. return_spmf (y, \<sigma>(x \<mapsto> y))))"

lemma weight_random_oracle [simp]:
  "\<lbrakk> finite A; A - ran \<sigma> \<noteq> {} \<rbrakk> \<Longrightarrow> weight_spmf (random_permutation \<sigma> x) = 1"
by(simp add: random_permutation_def weight_bind_spmf o_def split: option.split)

lemma lossless_random_oracle [simp]:
  "\<lbrakk> finite A; A - ran \<sigma> \<noteq> {} \<rbrakk> \<Longrightarrow> lossless_spmf (random_permutation \<sigma> x)"
by(simp add: lossless_spmf_def)

sublocale finite: callee_invariant_on random_permutation "\<lambda>\<sigma>. finite (dom \<sigma>)" \<I>_full
by(unfold_locales)(auto simp add: random_permutation_def split: option.splits)

lemma card_dom_random_oracle:
  assumes "interaction_any_bounded_by \<A> q"
  and "(y, \<sigma>') \<in> set_spmf (exec_gpv random_permutation \<A> \<sigma>)"
  and fin: "finite (dom \<sigma>)"
  shows "card (dom \<sigma>') \<le> q + card (dom \<sigma>)"
by(rule finite.interaction_bounded_by'_exec_gpv_count[OF assms(1-2)])
  (auto simp add: random_permutation_def fin card_insert_if simp del: fun_upd_apply split: option.split_asm)

end

end
