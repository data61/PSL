(* Title: Bernoulli.thy
   Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Distributions built from coin flips\<close>

subsection \<open> The Bernoulli distribution\<close>

theory Bernoulli imports "HOL-Probability.Probability" begin

lemma zero_lt_num [simp]: "0 < (numeral n :: _ :: {canonically_ordered_monoid_add, semiring_char_0})"
  by (metis not_gr_zero zero_neq_numeral)

lemma ennreal_mult_numeral: "ennreal x * numeral n = ennreal (x * numeral n)"
  by (simp add: ennreal_mult'')

lemma one_plus_ennreal: "0 \<le> x \<Longrightarrow> 1 + ennreal x = ennreal (1 + x)"
by simp

text \<open>
  We define the Bernoulli distribution as a least fixpoint instead of a loop because this
  avoids the need to add a condition flag to the distribution, which we would have to project
  out at the end again.  As the direct termination proof is so simple, we do not bother to prove
  it equivalent to a while loop.
\<close>

partial_function (spmf) bernoulli :: "real \<Rightarrow> bool spmf" where
  "bernoulli p = do {
     b \<leftarrow> coin_spmf;
     if b then return_spmf (p \<ge> 1 / 2)
     else if p < 1 / 2 then bernoulli (2 * p)
     else bernoulli (2 * p - 1)
   }"

lemma pmf_bernoulli_None: "pmf (bernoulli p) None = 0"
proof -
  have "ereal (pmf (bernoulli p) None) \<le> (INF n\<in>UNIV. ereal (1 / 2 ^ n))"
  proof(rule INF_greatest)
    show "ereal (pmf (bernoulli p) None) \<le> ereal (1 / 2 ^ n)" for n
    proof(induction n arbitrary: p)
      case (Suc n)
      show ?case using Suc.IH[of "2 * p"] Suc.IH[of "2 * p - 1"]
        by(subst bernoulli.simps)(simp add: UNIV_bool max_def field_simps spmf_of_pmf_pmf_of_set[symmetric] pmf_bind_pmf_of_set ennreal_pmf_bind nn_integral_pmf_of_set del: spmf_of_pmf_pmf_of_set)
    qed(simp add: pmf_le_1)
  qed
  also have "\<dots> = ereal 0"
  proof(rule LIMSEQ_unique)
    show "(\<lambda>n. ereal (1 / 2 ^ n)) \<longlonglongrightarrow> \<dots>" by(rule LIMSEQ_INF)(simp add: field_simps decseq_SucI)
    show "(\<lambda>n. ereal (1 / 2 ^ n)) \<longlonglongrightarrow> ereal 0" by(simp add: LIMSEQ_divide_realpow_zero)
  qed
  finally show ?thesis by simp
qed

lemma lossless_bernoulli [simp]: "lossless_spmf (bernoulli p)"
by(simp add: lossless_iff_pmf_None pmf_bernoulli_None)

lemma [simp]: assumes "0 \<le> p" "p \<le> 1"
  shows bernoulli_True: "spmf (bernoulli p) True = p" (is ?True)
  and bernoulli_False: "spmf (bernoulli p) False = 1 - p" (is ?False)
proof -
  { have "ennreal (spmf (bernoulli p) b) \<le> ennreal (if b then p else 1 - p)" for b using assms
    proof(induction arbitrary: p rule: bernoulli.fixp_induct[case_names adm bottom step])
      case adm show ?case by(rule cont_intro)+
    next
      case (step bernoulli' p)
      show ?case using step.prems step.IH[of "2 * p"] step.IH[of "2 * p - 1"]
        by(auto simp add: UNIV_bool max_def divide_le_posI_ennreal ennreal_mult_numeral numeral_mult_ennreal field_simps spmf_of_pmf_pmf_of_set[symmetric] ennreal_pmf_bind nn_integral_pmf_of_set one_plus_ennreal simp del: spmf_of_pmf_pmf_of_set ennreal_plus)
    qed simp }
  note this[of True] this[of False]
  moreover have "spmf (bernoulli p) True + spmf (bernoulli p) False = 1"
    by(simp add: spmf_False_conv_True)
  ultimately show ?True ?False using assms by(auto simp add: ennreal_le_iff2)
qed

lemma bernoulli_neg [simp]:
  assumes "p \<le> 0"
  shows "bernoulli p = return_spmf False"
proof -
  from assms have "ord_spmf (=) (bernoulli p) (return_spmf False)"
  proof(induction arbitrary: p rule: bernoulli.fixp_induct[case_names adm bottom step])
    case (step bernoulli' p)
    show ?case using step.prems step.IH[of "2 * p"]
      by(auto simp add: ord_spmf_return_spmf2 set_bind_spmf bind_UNION field_simps)
  qed simp_all
  from ord_spmf_eq_leD[OF this, of True] have "spmf (bernoulli p) True = 0" by simp
  moreover then have "spmf (bernoulli p) False = 1" by(simp add: spmf_False_conv_True)
  ultimately show ?thesis by(auto intro: spmf_eqI split: split_indicator)
qed

lemma bernoulli_pos [simp]:
  assumes "1 \<le> p"
  shows "bernoulli p = return_spmf True"
proof -
  from assms have "ord_spmf (=) (bernoulli p) (return_spmf True)"
  proof(induction arbitrary: p rule: bernoulli.fixp_induct[case_names adm bottom step])
    case (step bernoulli' p)
    show ?case using step.prems step.IH[of "2 * p - 1"]
      by(auto simp add: ord_spmf_return_spmf2 set_bind_spmf bind_UNION field_simps)
  qed simp_all
  from ord_spmf_eq_leD[OF this, of False] have "spmf (bernoulli p) False = 0" by simp
  moreover then have "spmf (bernoulli p) True = 1" by(simp add: spmf_False_conv_True)
  ultimately show ?thesis by(auto intro: spmf_eqI split: split_indicator)
qed

context begin interpretation pmf_as_function .
lemma bernoulli_eq_bernoulli_pmf:
  "bernoulli p = spmf_of_pmf (bernoulli_pmf p)"
by(rule spmf_eqI; simp)(transfer; auto simp add: max_def min_def)
end

end
