(* Title: Geometric.thy
   Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>The geometric distribution\<close>

theory Geometric imports
  Bernoulli
  While_SPMF
begin

text \<open>
  We define the geometric distribution as a least fixpoint, which is more elegant than
  as a loop. To prove probabilistic termination, we prove it equivalent to a loop and use
  the proof rules for probabilistic termination.
\<close>

context notes [[function_internals]] begin
partial_function (spmf) geometric_spmf :: "real \<Rightarrow> nat spmf" where
  "geometric_spmf p = do {
     b \<leftarrow> bernoulli p;
     if b then return_spmf 0 else map_spmf ((+) 1) (geometric_spmf p)
  }"
end

lemma geometric_spmf_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible P"
    and "P (\<lambda>geometric_spmf. return_pmf None)"
    and "\<And>geometric_spmf'. P geometric_spmf' \<Longrightarrow> P (\<lambda>p. bernoulli p \<bind> (\<lambda>b. if b then return_spmf 0 else map_spmf ((+) 1) (geometric_spmf' p)))"
  shows "P geometric_spmf"
  using assms by(rule geometric_spmf.fixp_induct)

lemma spmf_geometric_nonpos: "p \<le> 0 \<Longrightarrow> geometric_spmf p = return_pmf None"
  by(induction rule: geometric_spmf_fixp_induct) simp_all

lemma spmf_geometric_ge_1: "1 \<le> p \<Longrightarrow> geometric_spmf p = return_spmf 0"
  by(simp add: geometric_spmf.simps)

context
  fixes p :: real 
  and body :: "bool \<times> nat \<Rightarrow> (bool \<times> nat) spmf"
  defines [simp]: "body \<equiv> \<lambda>(b, x). map_spmf (\<lambda>b'. (\<not> b', x + (if b' then 0 else 1))) (bernoulli p)"
begin

interpretation loop_spmf fst body 
  rewrites "body \<equiv> \<lambda>(b, x). map_spmf (\<lambda>b'. (\<not> b', x + (if b' then 0 else 1))) (bernoulli p)" 
  by(fact body_def)

lemma geometric_spmf_conv_while:
  shows "geometric_spmf p = map_spmf snd (while (True, 0))"
proof -
  have "map_spmf ((+) x) (geometric_spmf p) = map_spmf snd (while (True, x))" (is "?lhs = ?rhs") for x
  proof(rule spmf.leq_antisym)
    show "ord_spmf (=) ?lhs ?rhs"
    proof(induction arbitrary: x rule: geometric_spmf_fixp_induct)
      case adm show ?case by simp
      case bottom show ?case by simp
      case (step geometric')
      show ?case using step.IH[of "Suc x"]
        apply(rewrite while.simps)
        apply(clarsimp simp add: map_spmf_bind_spmf bind_map_spmf intro!: ord_spmf_bind_reflI)
        apply(rewrite while.simps)
        apply(clarsimp simp add: spmf.map_comp o_def)
        done
    qed
    have "ord_spmf (=) ?rhs ?lhs"
      and "ord_spmf (=) (map_spmf snd (while (False, x))) (return_spmf x)"
    proof(induction arbitrary: x and x rule: while_fixp_induct)
      case adm show ?case by simp
      case bottom case 1 show ?case by simp
      case bottom case 2 show ?case by simp
    next
      case (step while')
      case 1 show ?case using step.IH(1)[of "Suc x"] step.IH(2)[of x]
        by(rewrite geometric_spmf.simps)(clarsimp simp add: map_spmf_bind_spmf bind_map_spmf spmf.map_comp o_def intro!: ord_spmf_bind_reflI)
      case 2 show ?case by simp
    qed
    then show "ord_spmf (=) ?rhs ?lhs" by -
  qed
  from this[of 0] show ?thesis by(simp cong: map_spmf_cong)
qed

lemma lossless_geometric [simp]: "lossless_spmf (geometric_spmf p) \<longleftrightarrow> p > 0"
proof(cases "0 < p \<and> p < 1")
  case True
  let ?body = "\<lambda>(b, x :: nat). map_spmf (\<lambda>b'. (\<not> b', x + (if b' then 0 else 1))) (bernoulli p)"
  have "lossless_spmf (while (True, 0))"
  proof(rule termination_0_1_immediate)
    have "{x. x} = {True}" by auto
    then show "p \<le> spmf (map_spmf fst (?body s)) False" for s :: "bool \<times> nat" using True
      by(cases s)(simp add: spmf.map_comp o_def spmf_map vimage_def spmf_conv_measure_spmf[symmetric])
    show "0 < p" using True by simp
  qed(clarsimp)
  with True show ?thesis by(simp add: geometric_spmf_conv_while)
qed(auto simp add: spmf_geometric_nonpos spmf_geometric_ge_1)

end

lemma spmf_geometric:
  assumes p: "0 < p" "p < 1"
  shows "spmf (geometric_spmf p) n = (1 - p) ^ n * p" (is "?lhs n = ?rhs n")
proof(rule spmf_ub_tight)
  fix n
  have "ennreal (?lhs n) \<le> ennreal (?rhs n)" using p
  proof(induction arbitrary: n rule: geometric_spmf_fixp_induct)
    case adm show ?case by(rule cont_intro)+
    case bottom show ?case by simp
    case (step geometric_spmf')
    then show ?case
      by(cases n)(simp_all add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite ennreal_mult spmf_map vimage_def mult.assoc spmf_conv_measure_spmf[symmetric] mult_mono split: split_indicator)
  qed
  then show "?lhs n \<le> ?rhs n" using p by(simp)
next
  have "(\<Sum>i. ennreal (p * (1 - p) ^ i)) = ennreal (p * (1 / (1 - (1 - p))))" using p
    by (intro suminf_ennreal_eq sums_mult geometric_sums) auto
  then show "(\<Sum>\<^sup>+ x. ennreal ((1 - p) ^ x * p)) = weight_spmf (geometric_spmf p)"
    using lossless_geometric[of p] p unfolding lossless_spmf_def
    by (simp add: nn_integral_count_space_nat field_simps)
qed

end
