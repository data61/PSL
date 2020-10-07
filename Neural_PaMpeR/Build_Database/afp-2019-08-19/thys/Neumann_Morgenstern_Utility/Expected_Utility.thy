(* License: LGPL *)

theory Expected_Utility
imports
  Neumann_Morgenstern_Utility_Theorem
begin

section \<open> Definition of vNM-utility function \<close>

text \<open> We define a version of the vNM Utility function using the locale mechanism. 
       Currently this definition and system U have no proven relation yet. \<close>

text \<open> Important: u is actually not the von Neuman Utility Function, 
       but a Bernoulli Utility Function. The Expected value p 
       given u is the von Neumann Utility Function. \<close>

locale vNM_utility =
  fixes outcomes :: "'a set"
  fixes relation :: "'a pmf relation"
  fixes u :: "'a \<Rightarrow> real"
  assumes "relation \<subseteq> (lotteries_on outcomes \<times> lotteries_on outcomes)"
  assumes "\<And>p q.  p \<in> lotteries_on outcomes \<Longrightarrow> 
                  q \<in> lotteries_on outcomes \<Longrightarrow> 
        p \<succeq>[relation] q \<longleftrightarrow> measure_pmf.expectation p u \<ge> measure_pmf.expectation q u"
begin

lemma vNM_utilityD:
  shows "relation \<subseteq> (lotteries_on outcomes \<times> lotteries_on outcomes)"
    and "p \<in> lotteries_on outcomes \<Longrightarrow> q \<in> lotteries_on outcomes \<Longrightarrow> 
    p \<succeq>[relation] q \<longleftrightarrow> measure_pmf.expectation p u \<ge> measure_pmf.expectation q u"
  using vNM_utility_axioms vNM_utility_def by (blast+)

lemma not_outside:
  assumes "p \<succeq>[relation] q"
  shows "p \<in> lotteries_on outcomes"
    and "q \<in> lotteries_on outcomes"
proof (goal_cases)
  case 1
  then show ?case
    by (meson assms contra_subsetD mem_Sigma_iff vNM_utility_axioms vNM_utility_def)
next
  case 2
  then show ?case
    by (metis assms mem_Sigma_iff subsetCE vNM_utility_axioms vNM_utility_def)
qed

lemma utility_ge:
  assumes "p \<succeq>[relation] q"
  shows "measure_pmf.expectation p u \<ge> measure_pmf.expectation q u"
  using assms vNM_utility_axioms vNM_utility_def
  by (metis (no_types, lifting) not_outside(1) not_outside(2))

end (* vNM_Utility *)

sublocale vNM_utility \<subseteq> ordinal_utility "(lotteries_on outcomes)" relation "(\<lambda>p. measure_pmf.expectation p u)"
proof (standard, goal_cases)
  case (2 x y)
  then show ?case
    using not_outside(1) by blast
next
  case (3 x y)
  then show ?case 
    by (auto simp add: not_outside(2))
qed (metis (mono_tags, lifting) vNM_utility_axioms vNM_utility_def)

context vNM_utility
begin

lemma strict_preference_iff_strict_utility:
 assumes "p \<in> lotteries_on outcomes" 
 assumes "q \<in> lotteries_on outcomes"
 shows "p \<succ>[relation] q \<longleftrightarrow> measure_pmf.expectation p u > measure_pmf.expectation q u"
  by (meson assms(1) assms(2) less_eq_real_def not_le util_def)

lemma pos_distrib_left:
  assumes "c > 0"
  shows "(\<Sum>z\<in>outcomes. pmf q z * (c * u z)) = c * (\<Sum>z\<in>outcomes. pmf q z * (u z))"
proof -
  have "(\<Sum>z\<in>outcomes. pmf q z * (c * u z)) = (\<Sum>z\<in>outcomes. pmf q z * c * u z)"
    by (simp add: ab_semigroup_mult_class.mult_ac(1))
  also have "... = (\<Sum>z\<in>outcomes. c * pmf q z *  u z)"
    by (simp add: mult.commute)
  also have "... = c * (\<Sum>z\<in>outcomes. pmf q z *  u z)"
    by (simp add: ab_semigroup_mult_class.mult_ac(1) sum_distrib_left)
  finally show ?thesis .
qed

lemma sum_pmf_util_commute:
  "(\<Sum>a\<in>outcomes. pmf p a * u a) = (\<Sum>a\<in>outcomes. u a * pmf p a)"
  by (simp add: mult.commute)



section \<open> Finite outcomes \<close>
context
  assumes fnt: "finite outcomes"
begin

lemma sum_equals_pmf_expectation:
  assumes "p \<in> lotteries_on outcomes"
  shows"(\<Sum>z\<in>outcomes. (pmf p z) * (u z)) = measure_pmf.expectation p u"
proof -
  have fnt: "finite outcomes"
    by (simp add: vNM_utilityD(1) fnt)
  have "measure_pmf.expectation p u = (\<Sum>a\<in>outcomes. pmf p a * u a)"
    using support_in_outcomes assms fnt integral_measure_pmf_real
      sum_pmf_util_commute by fastforce
  then show ?thesis
    using real_scaleR_def by presburger
qed

lemma expected_utility_weak_preference:
  assumes "p \<in> lotteries_on outcomes" 
    and "q \<in> lotteries_on outcomes"
  shows   "p \<succeq>[relation] q \<longleftrightarrow> (\<Sum>z\<in>outcomes. (pmf p z) * (u z)) \<ge> (\<Sum>z\<in>outcomes. (pmf q z) * (u z))"
  using sum_equals_pmf_expectation[of p, OF assms(1)] 
        sum_equals_pmf_expectation[of q, OF assms(2)]
   vNM_utility_def assms(1) assms(2) util_def_conf by presburger

lemma diff_leq_zero_weak_preference:
  assumes "p \<in> lotteries_on outcomes"
    and "q \<in> lotteries_on outcomes"
  shows "p \<succeq> q \<longleftrightarrow> ((\<Sum>a\<in>outcomes. pmf q a * u a) - (\<Sum>a\<in>outcomes. pmf p a * u a) \<le> 0)"
  using assms(1) assms(2) diff_le_0_iff_le
  by (metis (mono_tags, lifting) expected_utility_weak_preference)

lemma expected_utility_strict_preference:
  assumes "p \<in> lotteries_on outcomes" 
    and "q \<in> lotteries_on outcomes"
  shows   "p \<succ>[relation] q \<longleftrightarrow> measure_pmf.expectation p u > measure_pmf.expectation q u"
  using assms expected_utility_weak_preference less_eq_real_def not_le
  by (metis (no_types, lifting) util_def_conf)

lemma scale_pos_left: 
  assumes "c > 0" 
  shows "vNM_utility outcomes relation (\<lambda>x. c * u x)"
proof(standard, goal_cases)
  case 1
  then show ?case
    using vNM_utility_axioms vNM_utility_def by blast
next
  case (2 p q)
  have "q \<in> lotteries_on outcomes" and "p \<in> lotteries_on outcomes"
    using "2"(2) by (simp add: fnt "2"(1))+
  then have *: "p \<succeq> q = (measure_pmf.expectation q u \<le> measure_pmf.expectation p u)"
    using expected_utility_weak_preference[of p q] assms by blast
  have dist_c: "(\<Sum>z\<in>outcomes. (pmf q z) * (c * u z)) = c * (\<Sum>z\<in>outcomes. (pmf q z) * (u z))"
    using pos_distrib_left[of c q] assms by blast
  have dist_c': "(\<Sum>z\<in>outcomes. (pmf p z) * (c * u z)) = c * (\<Sum>z\<in>outcomes. (pmf p z) * (u z))"
    using pos_distrib_left[of c p] assms by blast
  have "p \<succeq> q \<longleftrightarrow> ((\<Sum>z\<in>outcomes. (pmf q z) * (c * u z)) \<le> (\<Sum>z\<in>outcomes. (pmf p z) * (c * u z)))"
  proof (rule iffI)
    assume "p \<succeq> q"
    then have "(\<Sum>z\<in>outcomes. pmf q z * (u z)) \<le> (\<Sum>z\<in>outcomes. pmf p z * (u z))" 
      using utility_ge
      using "2"(1) "2"(2) sum_equals_pmf_expectation by presburger
    then show "(\<Sum>z\<in>outcomes. pmf q z * (c * u z)) \<le> (\<Sum>z\<in>outcomes. pmf p z * (c * u z))" 
      using dist_c dist_c'
      by (simp add: assms)
  next
    assume "(\<Sum>z\<in>outcomes. pmf q z * (c * u z)) \<le> (\<Sum>z\<in>outcomes. pmf p z * (c * u z))"
    then have "(\<Sum>z\<in>outcomes. pmf q z * (u z)) \<le> (\<Sum>z\<in>outcomes. pmf p z * (u z))"
      using "2"(1) real_mult_le_cancel_iff2 assms by (simp add: dist_c dist_c')
    then show "p \<succeq> q"
      using "2"(2) assms "2"(1) by (simp add: * sum_equals_pmf_expectation)
  qed
  then show ?case
    by (simp add: "*" assms)
qed

lemma strict_alt_def:
  assumes "p \<in> lotteries_on outcomes" 
    and "q \<in> lotteries_on outcomes"
  shows "p \<succ>[relation] q \<longleftrightarrow> 
            (\<Sum>z\<in>outcomes. (pmf p z) * (u z)) > (\<Sum>z\<in>outcomes. (pmf q z) * (u z))"
  using sum_equals_pmf_expectation[of p, OF assms(1)] assms(1) assms(2)
    sum_equals_pmf_expectation[of q, OF assms(2)] strict_prefernce_iff_strict_utility
  by presburger

lemma strict_alt_def_utility_g:
  assumes "p \<succ>[relation] q"
  shows "(\<Sum>z\<in>outcomes. (pmf p z) * (u z)) > (\<Sum>z\<in>outcomes. (pmf q z) * (u z))"
  using assms not_outside(1) not_outside(2) strict_alt_def
  by meson

end (* finite outcomes *)

end (* Definition of vNM Utility Function as locale *)

lemma vnm_utility_is_ordinal_utility:
  assumes "vNM_utility outcomes relation u"
  shows "ordinal_utility (lotteries_on outcomes) relation (\<lambda>p. measure_pmf.expectation p u)"
proof (standard, goal_cases)
  case (1 x y)
  then show ?case
    using assms vNM_utility_def by blast
next
  case (2 x y)
  then show ?case 
    using assms vNM_utility.not_outside(1) by blast
next
  case (3 x y)
  then show ?case 
    using assms vNM_utility.not_outside(2) by blast
qed

lemma vnm_utility_imp_reational_prefs:
  assumes "vNM_utility outcomes relation u"
  shows "rational_preference (lotteries_on outcomes) relation"
proof (standard,goal_cases)
  case (1 x y)
  then show ?case
    using assms vNM_utility.not_outside(1) by blast
next
  case (2 x y)
  then show ?case
    using assms vNM_utility.not_outside(2) by blast
next
  case 3
  have t: "trans relation"
    using assms ordinal_utility.util_imp_trans vnm_utility_is_ordinal_utility by blast
  have "refl_on (lotteries_on outcomes) relation"
    by (meson assms order_refl refl_on_def vNM_utility_def)
  then show ?case
    using preorder_on_def t by blast
next
  case 4
  have "total_on (lotteries_on outcomes) relation"
    using ordinal_utility.util_imp_total[of "lotteries_on outcomes" 
        relation "(\<lambda>p. (\<Sum>z\<in>outcomes. (pmf p z) * (u z)))"]
      assms vnm_utility_is_ordinal_utility
    using ordinal_utility.util_imp_total by blast
  then show ?case
    by simp
qed

theorem expected_utilty_theorem_form_vnm_utility:
  assumes fnt: "finite outcomes" and "outcomes \<noteq> {}"
  shows "rational_preference (lotteries_on outcomes) \<R> \<and> 
         independent_vnm (lotteries_on outcomes) \<R> \<and> 
         continuous_vnm (lotteries_on outcomes) \<R> \<longleftrightarrow> 
         (\<exists>u. vNM_utility outcomes \<R> u)"
proof
  assume "rational_preference (\<P> outcomes) \<R> \<and> independent_vnm (\<P> outcomes) \<R> \<and> continuous_vnm (\<P> outcomes) \<R>"
  with Von_Neumann_Morgenstern_Utility_Theorem[of outcomes \<R>, OF assms] have
  "(\<exists>u. ordinal_utility (\<P> outcomes) \<R> (\<lambda>x. measure_pmf.expectation x u))" using assms by blast
  then obtain u where
    u: "ordinal_utility (\<P> outcomes) \<R> (\<lambda>x. measure_pmf.expectation x u)"
    by auto
  have "vNM_utility outcomes \<R> u"
  proof (standard, goal_cases)
    case 1
    then show ?case
      using u ordinal_utility.relation_subset_crossp by blast
  next
    case (2 p q)
    then show ?case
      using assms(2) expected_value_is_utility_function fnt u by blast
  qed
  then show "\<exists>u. vNM_utility outcomes \<R> u" 
    by blast
next
  assume a: "\<exists>u. vNM_utility outcomes \<R> u"
  then have "rational_preference (\<P> outcomes) \<R>"
    using vnm_utility_imp_reational_prefs by auto
  moreover have "independent_vnm (\<P> outcomes) \<R>"
    using a by (meson assms(2) fnt vNM_utility_implies_independence vnm_utility_is_ordinal_utility)
  moreover have "continuous_vnm (\<P> outcomes) \<R>"
    using a by (meson assms(2) fnt vNM_utilty_implies_continuity vnm_utility_is_ordinal_utility)
  ultimately show "rational_preference (\<P> outcomes) \<R> \<and> independent_vnm (\<P> outcomes) \<R> \<and> continuous_vnm (\<P> outcomes) \<R>"
    by auto
qed

end
