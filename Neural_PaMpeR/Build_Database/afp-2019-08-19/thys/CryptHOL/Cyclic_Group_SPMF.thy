(* Title: Cyclic_Group_SPMF.thy
  Author: Andreas Lochbihler, ETH Zurich *)

theory Cyclic_Group_SPMF imports
  Cyclic_Group
  "HOL-Probability.SPMF"
begin

definition sample_uniform :: "nat \<Rightarrow> nat spmf"
where "sample_uniform n = spmf_of_set {..<n}"

lemma spmf_sample_uniform: "spmf (sample_uniform n) x = indicator {..<n} x / n"
by(simp add: sample_uniform_def spmf_of_set)

lemma weight_sample_uniform: "weight_spmf (sample_uniform n) = indicator (range Suc) n"
by(auto simp add: sample_uniform_def weight_spmf_of_set split: split_indicator elim: lessE)

lemma weight_sample_uniform_0 [simp]: "weight_spmf (sample_uniform 0) = 0"
by(auto simp add: weight_sample_uniform indicator_def)

lemma weight_sample_uniform_gt_0 [simp]: "0 < n \<Longrightarrow> weight_spmf (sample_uniform n) = 1"
by(auto simp add: weight_sample_uniform indicator_def gr0_conv_Suc)

lemma lossless_sample_uniform [simp]: "lossless_spmf (sample_uniform n) \<longleftrightarrow> 0 < n"
by(auto simp add: lossless_spmf_def intro: ccontr)

lemma set_spmf_sample_uniform [simp]: "0 < n \<Longrightarrow> set_spmf (sample_uniform n) = {..<n}"
by(simp add: sample_uniform_def)

lemma (in cyclic_group) sample_uniform_one_time_pad:
  assumes [simp]: "c \<in> carrier G"
  shows
  "map_spmf (\<lambda>x. \<^bold>g [^] x \<otimes> c) (sample_uniform (order G)) = 
   map_spmf (\<lambda>x. \<^bold>g [^] x) (sample_uniform (order G))"
   (is "?lhs = ?rhs")
proof(cases "finite (carrier G)")
  case False
  thus ?thesis by(simp add: order_def sample_uniform_def)
next
  case True
  have "?lhs = map_spmf (\<lambda>x. x \<otimes> c) ?rhs"
    by(simp add: pmf.map_comp o_def option.map_comp)
  also have rhs: "?rhs = spmf_of_set (carrier G)"
    using True by(simp add: carrier_conv_generator inj_on_generator sample_uniform_def)
  also have "map_spmf (\<lambda>x. x \<otimes> c) \<dots> = spmf_of_set ((\<lambda>x. x \<otimes> c) ` carrier G)"
    by(simp add: inj_on_multc)
  also have "(\<lambda>x. x \<otimes> c) ` carrier G = carrier G"
    using True by(rule endo_inj_surj)(auto simp add: inj_on_multc)
  finally show ?thesis using rhs by simp
qed

end
