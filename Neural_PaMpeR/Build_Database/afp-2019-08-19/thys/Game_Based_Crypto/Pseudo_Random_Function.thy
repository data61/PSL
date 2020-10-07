(* Title: Pseudo_Random_Function.thy
  Author: Andreas Lochbihler, ETH Zurich *)

theory Pseudo_Random_Function imports
  CryptHOL.Computational_Model
begin

subsection \<open>Pseudo-random function\<close>

locale random_function =
  fixes p :: "'a spmf"
begin

type_synonym ('b,'a') dict = "'b \<rightharpoonup> 'a'"

definition random_oracle :: "('b, 'a) dict \<Rightarrow> 'b \<Rightarrow> ('a \<times> ('b, 'a) dict) spmf"
where
  "random_oracle \<sigma> x =
  (case \<sigma> x of Some y \<Rightarrow> return_spmf (y, \<sigma>)
   | None \<Rightarrow> p \<bind> (\<lambda>y. return_spmf (y, \<sigma>(x \<mapsto> y))))"

definition forgetful_random_oracle :: "unit \<Rightarrow> 'b \<Rightarrow> ('a \<times> unit) spmf"
where
  "forgetful_random_oracle \<sigma> x = p \<bind> (\<lambda>y. return_spmf (y, ()))"

lemma weight_random_oracle [simp]:
  "weight_spmf p = 1 \<Longrightarrow> weight_spmf (random_oracle \<sigma> x) = 1"
by(simp add: random_oracle_def weight_bind_spmf o_def split: option.split)

lemma lossless_random_oracle [simp]:
  "lossless_spmf p \<Longrightarrow> lossless_spmf (random_oracle \<sigma> x)"
by(simp add: lossless_spmf_def)

sublocale finite: callee_invariant_on random_oracle "\<lambda>\<sigma>. finite (dom \<sigma>)" \<I>_full
by(unfold_locales)(auto simp add: random_oracle_def split: option.splits)

lemma card_dom_random_oracle:
  assumes "interaction_any_bounded_by \<A> q"
  and "(y, \<sigma>') \<in> set_spmf (exec_gpv random_oracle \<A> \<sigma>)"
  and fin: "finite (dom \<sigma>)"
  shows "card (dom \<sigma>') \<le> q + card (dom \<sigma>)"
by(rule finite.interaction_bounded_by'_exec_gpv_count[OF assms(1-2)])
  (auto simp add: random_oracle_def fin card_insert_if simp del: fun_upd_apply split: option.split_asm)

end

subsection \<open>Pseudo-random function\<close>

locale "prf" =
  fixes key_gen :: "'key spmf"
  and "prf" :: "'key \<Rightarrow> 'domain \<Rightarrow> 'range"
  and rand :: "'range spmf"
begin

sublocale random_function "rand" .

definition prf_oracle :: "'key \<Rightarrow> unit \<Rightarrow> 'domain \<Rightarrow> ('range \<times> unit) spmf"
where "prf_oracle key \<sigma> x = return_spmf (prf key x, ())"

type_synonym ('domain', 'range') adversary = "(bool, 'domain', 'range') gpv"

definition game_0 :: "('domain, 'range) adversary \<Rightarrow> bool spmf"
where
  "game_0 \<A> = do {
     key \<leftarrow> key_gen;
     (b, _) \<leftarrow> exec_gpv (prf_oracle key) \<A> ();
     return_spmf b
   }"

definition game_1 :: "('domain, 'range) adversary \<Rightarrow> bool spmf"
where
  "game_1 \<A> = do {
     (b, _) \<leftarrow> exec_gpv random_oracle \<A> Map.empty;
     return_spmf b
   }"

definition advantage :: "('domain, 'range) adversary \<Rightarrow> real"
where "advantage \<A> = \<bar>spmf (game_0 \<A>) True - spmf (game_1 \<A>) True\<bar>"

lemma advantage_nonneg: "advantage \<A> \<ge> 0"
by(simp add: advantage_def)

abbreviation lossless :: "('domain, 'range) adversary \<Rightarrow> bool"
where "lossless \<equiv> lossless_gpv \<I>_full"

abbreviation (input) ibounded_by :: "('domain, 'range) adversary \<Rightarrow> enat \<Rightarrow> bool"
where "ibounded_by \<equiv> interaction_any_bounded_by"

end

end
