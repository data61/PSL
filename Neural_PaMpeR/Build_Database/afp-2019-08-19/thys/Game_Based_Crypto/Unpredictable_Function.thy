(* Title: Unpredictable_Function.thy
  Author: Andreas Lochbihler, ETH Zurich 
  Author: S. Reza Sefidgar, ETH Zurich *)

subsection \<open>Unpredictable function\<close>

theory Unpredictable_Function imports
  Guessing_Many_One
begin

locale upf =
  fixes key_gen :: "'key spmf"
  and hash :: "'key \<Rightarrow> 'x \<Rightarrow> 'hash"
begin

type_synonym ('x', 'hash') adversary = "(unit, 'x' + ('x' \<times> 'hash'), 'hash' + unit) gpv"

definition oracle_hash :: "'key \<Rightarrow> ('x, 'hash, 'x set) callee"
where
  "oracle_hash k = (\<lambda>L y. do {
    let t = hash k y;
    let L = insert y L;
    return_spmf (t, L)
  })"

definition oracle_flag :: "'key \<Rightarrow> ('x \<times> 'hash, unit, bool \<times> 'x set) callee"
where
  "oracle_flag = (\<lambda>key (flg, L) (y, t).
    return_spmf ((), (flg \<or> (t = (hash key y) \<and> y \<notin> L), L)))"

abbreviation "oracle" :: "'key \<Rightarrow> ('x + 'x \<times> 'hash, 'hash + unit, bool \<times> 'x set) callee"
where "oracle key \<equiv> \<dagger>(oracle_hash key) \<oplus>\<^sub>O oracle_flag key"

definition game :: "('x, 'hash) adversary \<Rightarrow> bool spmf"
where
  "game \<A> = do {
    key \<leftarrow> key_gen;
    (_, (flag', L')) \<leftarrow> exec_gpv (oracle key) \<A> (False, {});
    return_spmf flag'
  }"

definition advantage :: "('x, 'hash) adversary \<Rightarrow> real"
where "advantage \<A> = spmf (game \<A>) True"

type_synonym ('x', 'hash') adversary1 = "('x' \<times> 'hash', 'x', 'hash') gpv"

definition game1 :: "('x, 'hash) adversary1 \<Rightarrow> bool spmf"
where
  "game1 \<A> = do {
    key \<leftarrow> key_gen;
    ((m, h), L) \<leftarrow> exec_gpv (oracle_hash key) \<A> {};
    return_spmf (h = hash key m \<and> m \<notin> L)
  }"

definition advantage1 :: "('x, 'hash) adversary1 \<Rightarrow> real"
  where "advantage1 \<A> = spmf (game1 \<A>) True"

lemma advantage_advantage1:
  assumes bound: "interaction_bounded_by (Not \<circ> isl) \<A> q"
  shows "advantage \<A> \<le> advantage1 (guessing_many_one.reduction q (\<lambda>_ :: unit. \<A>) ()) * q"
proof -
  let ?init = "map_spmf (\<lambda>key. (key, (), {})) key_gen"
  let ?oracle = "\<lambda>key . oracle_hash key"
  let ?eval = "\<lambda>key (_ :: unit) L (x, h). return_spmf (h = hash key x \<and> x \<notin> L)"

  interpret guessing_many_one ?init ?oracle ?eval .

  have [simp]: "oracle_flag key = eval_oracle key ()" for key
    by(simp add: oracle_flag_def eval_oracle_def fun_eq_iff)
  have "game \<A> = game_multi (\<lambda>_. \<A>)"
    by(auto simp add: game_multi_def game_def bind_map_spmf intro!: bind_spmf_cong[OF refl])
  hence "advantage \<A> = advantage_multi (\<lambda>_. \<A>)" by(simp add: advantage_def advantage_multi_def)
  also have "\<dots> \<le> advantage_single (reduction q (\<lambda>_. \<A>)) * q" using bound
    by(rule many_single_reduction)(auto simp add: oracle_hash_def)
  also have "advantage_single (reduction q (\<lambda>_. \<A>)) = advantage1 (reduction q (\<lambda>_. \<A>) ())" for \<A>
    unfolding advantage1_def advantage_single_def
    by(auto simp add: game1_def game_single_def bind_map_spmf o_def intro!: bind_spmf_cong[OF refl] arg_cong2[where f=spmf])
  finally show ?thesis .
qed

end

end
