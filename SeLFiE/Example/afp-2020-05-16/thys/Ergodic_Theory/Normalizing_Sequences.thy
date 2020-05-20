(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>Normalizing sequences\<close>

theory Normalizing_Sequences
  imports Transfer_Operator Asymptotic_Density
begin

text \<open>In this file, we prove the main result in~\cite{gouezel_normalizing_sequences}: in a
conservative system, if a renormalized sequence $S_n f/B_n$ converges in distribution towards
a limit which is not a Dirac mass at $0$, then $B_n$ can not grow exponentially fast. We also prove
the easier result that, in a probability preserving system, normalizing sequences grow at most
polynomially.\<close>


subsection \<open>Measure of the preimages of disjoint sets.\<close>

text \<open>We start with a general result about conservative maps:
If $A_n$ are disjoint sets, and $P$ is a finite mass measure which is absolutely continuous
with respect to $M$, then $T^{-n}A_n$ is most often small: $P(T^{-n} A_n)$ tends to $0$
in Cesaro average. The proof is written in terms of densities and positive transfer operators,
so we first write it in ennreal.\<close>

theorem (in conservative) disjoint_sets_emeasure_Cesaro_tendsto_zero:
  fixes P::"'a measure" and A::"nat \<Rightarrow> 'a set"
  assumes [measurable]: "\<And>n. A n \<in> sets M"
      and "disjoint_family A"
          "absolutely_continuous M P" "sets P = sets M"
          "emeasure P (space M) \<noteq> \<infinity>"
  shows "(\<lambda>n. (\<Sum>i<n. emeasure P (space M \<inter> (T^^i)-`(A i)))/n) \<longlonglongrightarrow> 0"
proof (rule order_tendstoI)
  fix delta::ennreal assume "delta > 0"

  have "\<exists>epsilon. epsilon \<noteq> 0 \<and> epsilon \<noteq> \<infinity> \<and> 4 * epsilon < delta"
    apply (cases delta)
     apply (rule exI[of _ "delta/5"]) using \<open>delta>0\<close> apply (auto simp add: ennreal_divide_eq_top_iff ennreal_divide_numeral numeral_mult_ennreal intro!: ennreal_lessI)
    apply (rule exI[of _ 1]) by auto
  then obtain epsilon where "epsilon \<noteq> 0" "epsilon \<noteq> \<infinity>" "4 * epsilon < delta"
    by auto
  then have "epsilon > 0" using not_gr_zero by blast

  define L::ennreal where "L = (1/epsilon) * (1+ emeasure P (space M))"
  have "L \<noteq> \<infinity>"
    unfolding L_def using assms(5) divide_ennreal_def ennreal_mult_eq_top_iff \<open>epsilon \<noteq> 0\<close> by auto
  have "L \<noteq> 0"
    unfolding L_def using \<open>epsilon \<noteq> \<infinity>\<close> by (simp add: ennreal_divide_eq_top_iff)
  have "emeasure P (space M) \<le> epsilon * L" unfolding L_def
    using \<open>epsilon \<noteq> 0\<close> \<open>epsilon \<noteq> \<infinity>\<close> \<open>emeasure P (space M) \<noteq> \<infinity>\<close>
    apply (cases epsilon)
    apply (metis (no_types, lifting) add.commute add.right_neutral add_left_mono ennreal_divide_times infinity_ennreal_def mult.left_neutral mult_divide_eq_ennreal zero_le_one)
    by simp
  then have "emeasure P (space M) / L \<le> epsilon"
    using \<open>L \<noteq> 0\<close> \<open>L \<noteq> \<infinity>\<close> by (metis divide_le_posI_ennreal mult.commute not_gr_zero)
  then have "c * (emeasure P (space M)/L) \<le> c * epsilon" for c by (rule mult_left_mono, simp)


  text \<open>We introduce the density of $P$.\<close>
  define f where "f = RN_deriv M P"
  have [measurable]: "f \<in> borel_measurable M"
    unfolding f_def by auto
  have [simp]: "P = density M f"
    unfolding f_def apply (rule density_RN_deriv[symmetric]) using assms by auto
  have "space P = space M"
    by auto
  interpret Pc: finite_measure P
    apply standard unfolding \<open>space P = space M\<close> using assms(5) by auto

  have *: "AE x in P. eventually (\<lambda>n. (\<Sum>i<n. (nn_transfer_operator^^i) f x) > L * f x) sequentially"
  proof -
    have "AE x in M. f x \<noteq> \<infinity>"
      unfolding f_def apply (intro RN_deriv_finite Pc.sigma_finite_measure)
      unfolding \<open>space P = space M\<close> using assms by auto
    moreover have "AE x in M. f x > 0 \<longrightarrow> (\<Sum>n. (nn_transfer_operator^^n) f x) = \<infinity>"
      using recurrence_series_infinite_transfer_operator by auto
    ultimately have "AE x in M. f x > 0 \<longrightarrow> ((\<Sum>n. (nn_transfer_operator^^n) f x) = \<infinity> \<and> f x \<noteq> \<infinity>)"
      by auto
    then have AEP: "AE x in P. (\<Sum>n. (nn_transfer_operator^^n) f x) = \<infinity> \<and> f x \<noteq> \<infinity>"
      unfolding \<open>P = density M f\<close> using AE_density[of f M] by auto
    moreover have "eventually (\<lambda>n. (\<Sum>i<n. (nn_transfer_operator^^i) f x) > L * f x) sequentially"
      if "(\<Sum>n. (nn_transfer_operator^^n) f x) = \<infinity> \<and> f x \<noteq> \<infinity>" for x
    proof -
      have "(\<lambda>n. (\<Sum>i<n. (nn_transfer_operator^^i) f x)) \<longlonglongrightarrow> (\<Sum>i. (nn_transfer_operator^^i) f x)"
        by (simp add: summable_LIMSEQ)
      moreover have "(\<Sum>i. (nn_transfer_operator^^i) f x) > L * f x"
        using that \<open>L \<noteq> \<infinity>\<close> by (auto simp add: ennreal_mult_less_top top.not_eq_extremum)
      ultimately show ?thesis
        by (rule order_tendstoD(1))
    qed
    ultimately show ?thesis
      by auto
  qed
  have "\<exists>U N. U \<in> sets P \<and> (\<forall>n \<ge> N. \<forall>x \<in> U. (\<Sum>i<n. (nn_transfer_operator^^i) f x) > L * f x) \<and> emeasure P (space P - U) < epsilon"
    apply (rule Pc.Egorov_lemma[OF _ *]) using \<open>epsilon\<noteq>0\<close> by (auto simp add: zero_less_iff_neq_zero)
  then obtain U N1 where [measurable]: "U \<in> sets M" and U: "emeasure P (space M - U) < epsilon"
                          "\<And>n x. n \<ge> N1 \<Longrightarrow> x \<in> U \<Longrightarrow> L * f x < (\<Sum>i<n. (nn_transfer_operator^^i) f x)"
    unfolding \<open>sets P = sets M\<close> \<open>space P = space M\<close> by blast
  have "U \<subseteq> space M" by (rule sets.sets_into_space, simp)

  define K where "K = N1 + 1"
  have "K \<ge> N1" "K \<ge> 1" unfolding K_def by auto
  have *: "K * emeasure P (space M) / epsilon \<noteq> \<infinity>"
    using \<open>emeasure P (space M) \<noteq> \<infinity>\<close> \<open>epsilon \<noteq> 0\<close> ennreal_divide_eq_top_iff ennreal_mult_eq_top_iff by auto
  obtain N2::nat where N2: "N2 \<ge> K * emeasure P (space M) / epsilon"
    using ennreal_archimedean[OF *] by auto
  define N where "N = 2 * K + N2"
  have "(\<Sum>k\<in>{..<n}. emeasure P (space M \<inter> (T^^k)-`(A k))) / n < delta" if "n \<ge> N" for n
  proof -
    have "n \<ge> 2 * K" "of_nat n \<ge> ((of_nat N2)::ennreal)" using that unfolding N_def by auto
    then have "n \<ge> K * emeasure P (space M) / epsilon"
      using N2 order_trans by blast
    then have "K * emeasure P (space M) \<le> n * epsilon"
      using \<open>epsilon > 0\<close> \<open>epsilon \<noteq> \<infinity>\<close>
      by (smt divide_ennreal_def divide_right_mono_ennreal ennreal_mult_divide_eq ennreal_mult_eq_top_iff infinity_ennreal_def mult.commute not_le order_le_less)
    have "n \<ge> 1" using \<open>n \<ge> 2 * K\<close> \<open>K \<ge> 1\<close> by auto

    have *: "((\<Sum>k\<in>{K..<n-K}. indicator (A k) ((T^^k) x))::ennreal) \<le> (\<Sum>i\<in>{K..<n}. indicator (A (i-j)) ((T^^(i-j)) x))"
      if "j < K" for j x
    proof -
      have "(\<Sum>k \<in> {K..<n-K}. indicator (A k) ((T^^k) x)) \<le> ((\<Sum>k\<in>{K-j..<n-j}. indicator (A k) ((T^^k) x))::ennreal)"
        apply (rule sum_mono2) using \<open>j < K\<close> by auto
      also have "... = (\<Sum>i\<in>{K..<n}. indicator (A (i-j)) ((T^^(i-j)) x))"
        apply (rule sum.reindex_bij_betw[symmetric], rule bij_betw_byWitness[of _ "\<lambda>x. x+j"]) using \<open>j < K\<close> by auto
      finally show ?thesis by simp
    qed

    have "L * (\<Sum> k \<in> {K..<n-K}. emeasure P (U \<inter> (T^^k)-`(A k))) = L * (\<Sum> k \<in> {K..<n-K}.(\<integral>\<^sup>+x. indicator (U \<inter> (T^^k)-`(A k)) x \<partial>P))"
      by auto
    also have "... = (\<Sum> k \<in> {K..<n-K}. (\<integral>\<^sup>+x. L * indicator (U \<inter> (T^^k)-`(A k)) x \<partial>P))"
      unfolding sum_distrib_left by (intro sum.cong nn_integral_cmult[symmetric], auto)
    also have "... = (\<Sum> k \<in> {K..<n-K}. (\<integral>\<^sup>+x. f x * (L * indicator (U \<inter> (T^^k)-`(A k)) x) \<partial>M))"
      unfolding \<open>P = density M f\<close> by (intro sum.cong nn_integral_density, auto)
    also have "... = (\<Sum> k \<in> {K..<n-K}. (\<integral>\<^sup>+x. f x * L * indicator U x * indicator (A k) ((T^^k) x) \<partial>M))"
      by (intro sum.cong nn_integral_cong, auto simp add: algebra_simps indicator_def)
    also have "... \<le> (\<Sum> k \<in> {K..<n-K}. (\<integral>\<^sup>+x. (\<Sum>j \<in> {..<K}. (nn_transfer_operator^^j) f x) * indicator (A k) ((T^^k) x) \<partial>M))"
      apply (intro sum_mono nn_integral_mono)
      using U(2)[OF \<open>K \<ge> N1\<close>] unfolding indicator_def using less_imp_le by (auto simp add: algebra_simps)
    also have "... = (\<integral>\<^sup>+x. (\<Sum>k\<in>{K..<n-K}. (\<Sum>j \<in> {..<K}. (nn_transfer_operator^^j) f x * indicator (A k) ((T^^k) x))) \<partial>M)"
      apply (subst nn_integral_sum, simp) unfolding sum_distrib_right by auto
    also have "... = (\<integral>\<^sup>+x. (\<Sum>j \<in> {..<K}. (\<Sum>k\<in>{K..<n-K}. (nn_transfer_operator^^j) f x * indicator (A k) ((T^^k) x))) \<partial>M)"
      by (rule nn_integral_cong, rule sum.swap)
    also have "... = (\<Sum>j \<in> {..<K}. (\<integral>\<^sup>+x. (nn_transfer_operator^^j) f x * (\<Sum>k\<in>{K..<n-K}. indicator (A k) ((T^^k) x)) \<partial>M))"
      apply (subst nn_integral_sum, simp) unfolding sum_distrib_left by auto
    also have "... \<le> (\<Sum>j \<in> {..<K}. (\<integral>\<^sup>+x. (nn_transfer_operator^^j) f x * (\<Sum>i\<in>{K..<n}. indicator (A (i-j)) ((T^^(i-j)) x)) \<partial>M))"
      apply (rule sum_mono, rule nn_integral_mono) using * by (auto simp add: mult_left_mono)
    also have "... = (\<Sum>i\<in>{K..<n}. (\<Sum>j \<in> {..<K}. (\<integral>\<^sup>+x. (nn_transfer_operator^^j) f x * indicator (A (i-j)) ((T^^(i-j)) x) \<partial>M)))"
      unfolding sum_distrib_left using sum.swap by (subst nn_integral_sum, auto)
    also have "... = (\<Sum>i\<in>{K..<n}. (\<Sum>j \<in> {..<K}. (\<integral>\<^sup>+x. f x * indicator (A (i-j)) ((T^^(i-j)) ((T^^j) x)) \<partial>M)))"
      by (subst nn_transfer_operator_intg_Tn, auto)
    also have "... = (\<Sum>i\<in>{K..<n}. (\<integral>\<^sup>+x. f x * (\<Sum>j \<in> {..<K}. indicator (A (i-j)) ((T^^(i-j)) ((T^^j) x))) \<partial>M))"
      unfolding sum_distrib_left by (subst nn_integral_sum, auto)
    also have "... = (\<Sum>i\<in>{K..<n}. (\<integral>\<^sup>+x. (\<Sum>j \<in> {..<K}. indicator (A (i-j)) ((T^^((i-j)+j)) x)) \<partial>P))"
      unfolding \<open>P = density M f\<close> funpow_add comp_def apply (rule sum.cong, simp) by (rule nn_integral_density[symmetric], auto)
    also have "... = (\<Sum>i\<in>{K..<n}. (\<integral>\<^sup>+x. (\<Sum>j \<in> {..<K}. indicator (A (i-j)) ((T^^i) x)) \<partial>P))"
      by auto
    also have "... \<le> (\<Sum>i\<in>{K..<n}. (\<integral>\<^sup>+x. (1::ennreal) \<partial>P))"
      apply (rule sum_mono) apply (rule nn_integral_mono) apply (rule disjoint_family_indicator_le_1)
      using assms(2) apply (auto simp add: disjoint_family_on_def)
      by (metis Int_iff diff_diff_cancel equals0D le_less le_trans)
    also have "... \<le> n * emeasure P (space M)"
      using assms(4) by (auto intro!: mult_right_mono)
    finally have *: "L * (\<Sum> k \<in> {K..<n-K}. emeasure P (U \<inter> (T^^k)-`(A k))) \<le> n * emeasure P (space M)"
      by simp
    have Ineq: "(\<Sum> k \<in> {K..<n-K}. emeasure P (U \<inter> (T^^k)-`(A k))) \<le> n * emeasure P (space M) / L"
      using divide_right_mono_ennreal[OF *, of L] \<open>L \<noteq> 0\<close>
      by (metis (no_types, lifting) \<open>L \<noteq> \<infinity>\<close> ennreal_mult_divide_eq infinity_ennreal_def mult.commute)

    have I: "{..<K} \<union> {K..<n-K} \<union> {n-K..<n} = {..<n}" using \<open>n \<ge> 2 * K\<close> by auto
    have "(\<Sum>k\<in>{..<n}. emeasure P (space M \<inter> (T^^k)-`(A k))) \<le> (\<Sum>k\<in>{..<n}. emeasure P (U \<inter> (T^^k)-`(A k)) + epsilon)"
    proof (rule sum_mono)
      fix k
      have "emeasure P (space M \<inter> (T^^k)-`(A k)) \<le> emeasure P ((U \<inter> (T^^k)-`(A k)) \<union> (space M - U))"
        by (rule emeasure_mono, auto)
      also have "... \<le> emeasure P (U \<inter> (T^^k)-`(A k)) + emeasure P (space M - U)"
        by (rule emeasure_subadditive, auto)
      also have "... \<le> emeasure P (U \<inter> (T^^k)-`(A k)) + epsilon"
        using U(1) by auto
      finally show "emeasure P (space M \<inter> (T ^^ k) -` A k) \<le> emeasure P (U \<inter> (T ^^ k) -` A k) + epsilon"
        by simp
    qed
    also have "... = (\<Sum>k\<in>{..<K} \<union> {K..<n-K} \<union> {n-K..<n}. emeasure P (U \<inter> (T^^k)-`(A k))) + (\<Sum>k\<in>{..<n}. epsilon)"
      unfolding sum.distrib I by simp
    also have "... = (\<Sum>k\<in>{..<K}. emeasure P (U \<inter> (T^^k)-`(A k))) + (\<Sum>k\<in>{K..<n-K}. emeasure P (U \<inter> (T^^k)-`(A k)))
                      + (\<Sum>k\<in>{n-K..<n}. emeasure P (U \<inter> (T^^k)-`(A k))) + n * epsilon"
      apply (subst sum.union_disjoint) apply simp apply simp using \<open>n \<ge> 2 * K\<close>
      apply (simp add: ivl_disj_int_one(2) ivl_disj_un_one(2))
      by (subst sum.union_disjoint, auto)
    also have "... \<le> (\<Sum>k\<in>{..<K}. emeasure P (space M)) + n * emeasure P (space M) / L + (\<Sum>k\<in>{n-K..<n}. emeasure P (space M)) + n * epsilon"
      apply (intro add_mono sum_mono Ineq emeasure_mono) using \<open>U \<subseteq> space M\<close> by auto
    also have "... = K * emeasure P (space M) + n * emeasure P (space M)/L + K * emeasure P (space M) + n * epsilon"
      using \<open>n \<ge> 2 * K\<close> by auto
    also have "... \<le> n * epsilon + n * epsilon + n * epsilon + n * epsilon"
      apply (intro add_mono)
      using \<open>K * emeasure P (space M) \<le> n * epsilon\<close> \<open>of_nat n * (emeasure P (space M)/L) \<le> of_nat n * epsilon\<close>
      ennreal_times_divide by auto
    also have "... = n * (4 * epsilon)"
      by (metis (no_types, lifting) add.assoc distrib_right mult.left_commute mult_2 numeral_Bit0)
    also have "... < n * delta"
      using \<open>4 * epsilon < delta\<close> \<open>n \<ge> 1\<close>
      by (simp add: ennreal_mult_strict_left_mono ennreal_of_nat_eq_real_of_nat)
    finally show ?thesis
      apply (subst divide_less_ennreal)
      using \<open>n \<ge> 1\<close> of_nat_less_top by (auto simp add: mult.commute)
  qed
  then show "eventually (\<lambda>n. (\<Sum>k\<in>{..<n}. emeasure P (space M \<inter> (T^^k)-`(A k))) / n < delta) sequentially"
    unfolding eventually_sequentially by auto
qed (simp)

text \<open>We state the previous theorem using measures instead of emeasures. This is clearly
equivalent, but one has to play with ennreal carefully to prove it.\<close>

theorem (in conservative) disjoint_sets_measure_Cesaro_tendsto_zero:
  fixes P::"'a measure" and A::"nat \<Rightarrow> 'a set"
  assumes [measurable]: "\<And>n. A n \<in> sets M"
      and "disjoint_family A"
          "absolutely_continuous M P" "sets P = sets M"
          "emeasure P (space M) \<noteq> \<infinity>"
  shows "(\<lambda>n. (\<Sum>i<n. measure P (space M \<inter> (T^^i)-`(A i)))/n) \<longlonglongrightarrow> 0"
proof -
  have "space P = space M"
    using assms(4) sets_eq_imp_space_eq by blast
  moreover have "emeasure P Q \<le> emeasure P (space P)" for Q
    by (simp add: emeasure_space)
  ultimately have [simp]: "emeasure P Q \<noteq> \<top>" for Q
    using \<open>emeasure P (space M) \<noteq> \<infinity>\<close> neq_top_trans by auto
  have *: "ennreal ((\<Sum>i<n. measure P (space M \<inter> (T^^i)-`(A i)))/n) = (\<Sum>i<n. emeasure P (space M \<inter> (T^^i)-`(A i)))/n" if "n > 0" for n
    apply (subst divide_ennreal[symmetric])
      apply (auto intro!: sum_nonneg that simp add: ennreal_of_nat_eq_real_of_nat[symmetric])
    apply(subst sum_ennreal[symmetric], simp)
    apply (subst emeasure_eq_ennreal_measure) by auto
  have "eventually (\<lambda>n. ennreal ((\<Sum>i<n. measure P (space M \<inter> (T^^i)-`(A i)))/n) = (\<Sum>i<n. emeasure P (space M \<inter> (T^^i)-`(A i)))/n) sequentially"
    unfolding eventually_sequentially apply (rule exI[of _ 1]) using * by auto
  then have *: "(\<lambda>n. ennreal ((\<Sum>i<n. measure P (space M \<inter> (T^^i)-`(A i)))/n)) \<longlonglongrightarrow> ennreal 0"
    using disjoint_sets_emeasure_Cesaro_tendsto_zero[OF assms] tendsto_cong by force
  show ?thesis
    apply (subst tendsto_ennreal_iff[symmetric]) using * apply auto
    unfolding eventually_sequentially apply (rule exI[of _ 1])
    by (auto simp add: divide_simps intro!: sum_nonneg)
qed

text \<open>As convergence to $0$ in Cesaro mean is equivalent to convergence to $0$ along a density
one sequence, we obtain the equivalent formulation of the previous theorem.\<close>

theorem (in conservative) disjoint_sets_measure_density_one_tendsto_zero:
  fixes P::"'a measure" and A::"nat \<Rightarrow> 'a set"
  assumes [measurable]: "\<And>n. A n \<in> sets M"
      and "disjoint_family A"
          "absolutely_continuous M P" "sets P = sets M"
          "emeasure P (space M) \<noteq> \<infinity>"
  shows "\<exists>B. lower_asymptotic_density B = 1 \<and> (\<lambda>n. measure P (space M \<inter> (T^^n)-`(A n)) * indicator B n) \<longlonglongrightarrow> 0"
by (rule cesaro_imp_density_one[OF _ disjoint_sets_measure_Cesaro_tendsto_zero[OF assms]], simp)


subsection \<open>Normalizing sequences do not grow exponentially in conservative systems\<close>

text \<open>We prove the main result in~\cite{gouezel_normalizing_sequences}: in a
conservative system, if a renormalized sequence $S_n f/B_n$ converges in distribution towards
a limit which is not a Dirac mass at $0$, then $B_n$ can not grow exponentially fast. The proof
is expressed in the following locale. The main theorem is Theorem~\verb+subexponential_growth+
below. To prove it, we need several preliminary estimates.\<close>

text \<open>We will use the fact that a real random variables which is not the Dirac mass at $0$
gives positive mass to a set separated away from $0$.\<close>

lemma (in real_distribution) not_Dirac_0_imp_positive_mass_away_0:
  assumes "prob {0} < 1"
  shows "\<exists>a. a > 0 \<and> prob {x. abs(x) > a} > 0"
proof -
  have "1 = prob UNIV"
    using prob_space by auto
  also have "... = prob {0} + prob (UNIV -{0})"
    by (subst finite_measure_Union[symmetric], auto)
  finally have "0 < prob (UNIV -{0})"
    using assms by auto
  also have "... \<le> prob (\<Union>n::nat. {x. abs(x)>(1/2)^n})"
    apply (rule finite_measure_mono)
    by (auto, meson one_less_numeral_iff reals_power_lt_ex semiring_norm(76) zero_less_abs_iff)
  finally have "prob (\<Union>n::nat. {x. abs(x)>(1/2)^n}) \<noteq> 0"
    by simp
  then have "\<exists>n. prob {x. abs(x)>(1/2)^n} \<noteq> 0"
    using measure_countably_zero[of "\<lambda>n. {x. abs(x)>(1/2)^n}"] by force
  then obtain N where N: "prob {x. abs(x) > (1/2)^N} \<noteq> 0"
    by blast
  show ?thesis
    apply (rule exI[of _ "(1/2)^N"]) using N by (auto simp add: zero_less_measure_iff)
qed

locale conservative_limit =
  conservative M + PS: prob_space P + PZ: real_distribution Z
    for M::"'a measure" and P::"'a measure" and Z::"real measure" +
  fixes f g::"'a \<Rightarrow> real" and B::"nat \<Rightarrow> real"
  assumes PabsM: "absolutely_continuous M P"
      and Bpos: "\<And>n. B n > 0"
      and M [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M" "sets P = sets M"
      and non_trivial: "PZ.prob {0} < 1"
      and conv: "weak_conv_m (\<lambda>n. distr P borel (\<lambda>x. (g x + birkhoff_sum f n x) / B n)) Z"
begin

text \<open>For measurability statements, we want every question about $Z$ or $P$ to reduce to a
question about Borel sets of $M$. We add in the next lemma all the statements that are needed
so that this happens automatically.\<close>
lemma PSZ [simp, measurable_cong]:
  "space P = space M"
  "h \<in> borel_measurable P \<longleftrightarrow> h \<in> borel_measurable M"
  "A \<in> sets P \<longleftrightarrow> A \<in> sets M"
using M sets_eq_imp_space_eq real_distribution_def by auto

text \<open>The first nontrivial upper bound is the following lemma, asserting that $B_{n+1}$ can not
be much larger than $\max B_i$ for $i \leq n$. This is proved by saying that $S_{n+1} f = f +
(S_n f) \circ T$, and we know that $S_n f$ is not too large on a set of very large measure, so
the same goes for $(S_n f) \circ T$ by a non-singularity argument. Excepted that the measure $P$
does not have to be nonsingular for the map $T$, so one has to tweak a little bit this idea,
using transfer operators and conservativity. This is easier to do when the density of $P$ is
bounded by $1$, so we first give the proof under this assumption, and then we reduce to this
case by replacing $M$ with $M+P$ in the second lemma below.\<close>

text \<open>First, let us prove the lemma assuming that the density $h$ of $P$ is bounded by $1$.\<close>

lemma upper_bound_C_aux:
  assumes "P = density M h" "\<And>x. h x \<le> 1"
      and [measurable]: "h \<in> borel_measurable M"
  shows "\<exists>C\<ge>1. \<forall>n. B (Suc n) \<le> C * Max {B i|i. i \<le> n}"
proof -
  obtain a0 where a0: "a0 > 0" "PZ.prob {x. abs(x) > a0} > 0"
    using PZ.not_Dirac_0_imp_positive_mass_away_0[OF non_trivial] by blast
  define a where "a = a0/2"
  have "a > 0" using \<open>a0 > 0\<close> unfolding a_def by auto
  define alpha where "alpha = PZ.prob {x. abs (x) > a0}/4"
  have "alpha > 0" unfolding alpha_def using a0 by auto
  have "PZ.prob {x. abs (x) > 2 * a} > 3 * alpha"
    using a0 unfolding a_def alpha_def by auto

  text \<open>First step: choose $K$ such that, with probability $1-\alpha$, one has
  $\sum_{1 \leq k < K} h(T^k x) \geq 1$. This follows directly from conservativity.\<close>
  have "\<exists>K. K \<ge> 1 \<and> PS.prob {x \<in> space M. (\<Sum>i\<in>{1..<K}. h ((T^^i) x)) \<ge> 1} \<ge> 1 - alpha"
  proof -
    have *: "AE x in P. eventually (\<lambda>n. (\<Sum>i<n. h ((T^^i) x)) > 2) sequentially"
    proof -
      have "AE x in M. h x > 0 \<longrightarrow> (\<Sum>i. h ((T^^i) x)) = \<infinity>"
        using recurrence_series_infinite by auto
      then have AEP: "AE x in P. (\<Sum>i. h ((T^^i) x)) = \<infinity>"
        unfolding \<open>P = density M h\<close> using AE_density[of h M] by auto
      moreover have "eventually (\<lambda>n. (\<Sum>i<n. h ((T^^i) x)) > 2) sequentially"
        if "(\<Sum>i. h ((T^^i) x)) = \<infinity>" for x
      proof -
        have "(\<lambda>n. (\<Sum>i<n. h ((T^^i) x))) \<longlonglongrightarrow> (\<Sum>i. h ((T^^i) x))"
          by (simp add: summable_LIMSEQ)
        moreover have "(\<Sum>i. h ((T^^i) x)) > 2"
          using that by auto
        ultimately show ?thesis
          by (rule order_tendstoD(1))
      qed
      ultimately show ?thesis
        by auto
    qed
    have "\<exists>U N. U \<in> sets P \<and> (\<forall>n \<ge> N. \<forall>x \<in> U. (\<Sum>i<n. h ((T^^i) x)) > 2) \<and> emeasure P (space P - U) < alpha"
      apply (rule PS.Egorov_lemma)
        apply measurable using M(3) measurable_ident_sets apply blast
      using * \<open>alpha > 0\<close> by auto
    then obtain U N1 where [measurable]: "U \<in> sets M" and U: "emeasure P (space M - U) < alpha"
                            "\<And>n x. n \<ge> N1 \<Longrightarrow> x \<in> U \<Longrightarrow> 2 < (\<Sum>i<n. h ((T^^i) x))"
      by auto
    have "U \<subseteq> space M" by (rule sets.sets_into_space, simp)
    define K where "K = N1+1"
    then have "K \<ge> 1" by auto
    have Ux: "(\<Sum>i\<in>{1..<K}. h ((T^^i) x)) \<ge> 1" if "x \<in> U" for x
    proof -
      have *: "1 < t" if "2 < 1 + t" for t::ennreal
        apply (cases t) using that apply auto
        by (metis ennreal_add_left_cancel_less ennreal_less_iff ennreal_numeral le_numeral_extra(1) numeral_One one_add_one)

      have "2 < (\<Sum>i \<in> {..<K}. h ((T^^i) x))"
        apply (rule U(2)) unfolding K_def using that by auto
      also have "... = (\<Sum>i \<in> {0}. h ((T^^i) x)) + (\<Sum>i \<in> {1..<K}. h ((T^^i) x))"
        apply (subst sum.union_disjoint[symmetric]) apply simp apply simp apply simp
        apply (rule sum.cong) using \<open>K \<ge> 1\<close> by auto
      also have "... = h x + (\<Sum>i \<in> {1..<K}. h ((T^^i) x))"
        by auto
      also have "... \<le> 1 + (\<Sum>i \<in> {1..<K}. h ((T^^i) x))"
        using assms by auto
      finally show ?thesis using less_imp_le[OF *] by auto
    qed
    have "PS.prob {x \<in> space M. (\<Sum>i\<in>{1..<K}. h ((T^^i) x)) \<ge> 1} \<ge> 1 - alpha"
    proof -
      have "PS.prob (space P - U) < alpha"
        using U(1) by (simp add: PS.emeasure_eq_measure ennreal_less_iff)
      then have "1 - alpha < PS.prob U"
        using PS.prob_compl by auto
      also have "... \<le> PS.prob {x \<in> space M. (\<Sum>i\<in>{1..<K}. h ((T^^i) x)) \<ge> 1}"
        apply (rule PS.finite_measure_mono) using Ux sets.sets_into_space[OF \<open>U \<in> sets M\<close>] by auto
      finally show ?thesis by simp
    qed
    then show ?thesis using \<open>K \<ge> 1\<close> by auto
  qed
  then obtain K where K: "K \<ge> 1" "PS.prob {x \<in> space M. (\<Sum>i\<in>{1..<K}. h ((T^^i) x)) \<ge> 1} \<ge> 1 - alpha"
    by blast

  text \<open>Second step: obtain $D$ which controls the tails of the $K$ first Birkhoff sums of $f$.\<close>
  have "\<exists>D. PS.prob {x \<in> space M. \<forall>k < K. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<le> D} \<ge> 1 - alpha"
  proof -
    have D: "\<exists>D. PS.prob {x \<in> space P. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<ge> D} < alpha/K \<and> D \<ge> 1" for k
      apply (rule PS.random_variable_small_tails) using \<open>K \<ge> 1\<close> \<open>alpha > 0\<close> by auto
    have "\<exists>D. \<forall>k. PS.prob {x \<in> space P. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<ge> D k} < alpha/K \<and> D k \<ge> 1"
      apply (rule choice) using D by auto
    then obtain D where D: "\<And>k. PS.prob {x \<in> space P. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<ge> D k} < alpha/K"
      by blast
    define D0 where "D0 = Max (D`{..K})"
    have "PS.prob {x \<in> space M. \<forall>k < K. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<le> D0} \<ge> 1 - alpha"
    proof -
      have D1: "PS.prob {x \<in> space M. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<ge> D0} < alpha/K" if "k \<le> K" for k
      proof -
        have "D k \<le> D0"
          unfolding D0_def apply (rule Max_ge) using that by auto
        have "PS.prob {x \<in> space M. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<ge> D0}
                \<le> PS.prob {x \<in> space P. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<ge> D k}"
          apply (rule PS.finite_measure_mono) using \<open>D k \<le> D0\<close> by auto
        then show ?thesis using D[of k] by auto
      qed
      have "PS.prob (\<Union>k\<in> {..<K}. {x \<in> space M. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<ge> D0}) \<le>
              (\<Sum>k \<in> {..<K}. PS.prob {x \<in> space M. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<ge> D0})"
        by (rule PS.finite_measure_subadditive_finite, auto)
      also have "... \<le> (\<Sum>k \<in> {..<K}. alpha/K)"
        apply (rule sum_mono) using less_imp_le[OF D1] by auto
      also have "... = alpha"
        using \<open>K \<ge> 1\<close> by auto
      finally have "PS.prob (\<Union>k\<in> {..<K}. {x \<in> space M. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<ge> D0}) \<le> alpha"
        by simp
      then have "1 - alpha \<le> 1 - PS.prob (\<Union>k\<in> {..<K}. {x \<in> space M. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<ge> D0})"
        by simp
      also have "... = PS.prob (space P - (\<Union>k\<in> {..<K}. {x \<in> space M. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<ge> D0}))"
        by (rule PS.prob_compl[symmetric], auto)
      also have "... \<le> PS.prob {x \<in> space M. \<forall>k < K. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<le> D0}"
        by (rule PS.finite_measure_mono, auto)
      finally show ?thesis by simp
    qed
    then show ?thesis by blast
  qed
  then obtain D where D: "PS.prob {x \<in> space M. \<forall>k < K. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<le> D} \<ge> 1 - alpha"
    by blast

  text \<open>Third step: obtain $\epsilon$ small enough so that, for any set $U$ with probability less
  than $\epsilon$ and for any $k\leq K$, one has $\int_U \hat T^k h < \delta$, where $\delta$ is
  very small.\<close>
  define delta where "delta = alpha/(2 * K)"
  then have "delta > 0" using \<open>alpha > 0\<close> \<open>K \<ge> 1\<close> by auto
  have "\<exists>epsilon > (0::real). \<forall>U \<in> sets P. \<forall>k \<le> K. emeasure P U < epsilon \<longrightarrow> (\<integral>\<^sup>+x\<in>U. ((nn_transfer_operator^^k) h) x \<partial>P) \<le> delta"
  proof -
    have *: "\<exists>epsilon>(0::real). \<forall>U\<in>sets P. emeasure P U < epsilon \<longrightarrow> (\<integral>\<^sup>+x\<in>U. ((nn_transfer_operator^^k) h) x \<partial>P) < delta"
      for k
    proof (rule small_nn_integral_on_small_sets[OF _ \<open>0 < delta\<close>])
      have "(\<integral>\<^sup>+x. ((nn_transfer_operator^^k) h) x \<partial>P) = (\<integral>\<^sup>+x. h x * ((nn_transfer_operator^^k) h) x \<partial>M)"
        unfolding \<open>P = density M h\<close> by (rule nn_integral_density, auto)
      also have "... \<le> (\<integral>\<^sup>+x. 1 * ((nn_transfer_operator^^k) h) x \<partial>M)"
        apply (intro nn_integral_mono mult_right_mono) using assms(2) by auto
      also have "... = (\<integral>\<^sup>+x. 1 * h x \<partial>M)"
        by (rule nn_transfer_operator_intTn_g, auto)
      also have "... = emeasure P (space M)"
        using PS.emeasure_space_1 by (simp add: emeasure_density \<open>P = density M h\<close>)
      also have "... < \<infinity>"
        using PS.emeasure_space_1 by simp
      finally show "(\<integral>\<^sup>+x. ((nn_transfer_operator^^k) h) x \<partial>P) \<noteq> \<infinity>"
        by auto
    qed (simp)
    have "\<exists>epsilon. \<forall>k. epsilon k > (0::real) \<and> (\<forall>U\<in>sets P. emeasure P U < epsilon k \<longrightarrow> (\<integral>\<^sup>+x\<in>U. ((nn_transfer_operator^^k) h) x \<partial>P) < delta)"
      apply (rule choice) using * by blast
    then obtain epsilon::"nat \<Rightarrow> real" where E: "\<And>k. epsilon k > 0"
                              "\<And>k U. U \<in> sets P \<Longrightarrow> emeasure P U < epsilon k \<Longrightarrow> (\<integral>\<^sup>+x\<in>U. ((nn_transfer_operator^^k) h) x \<partial>P) < delta"
      by blast
    define epsilon0 where "epsilon0 = Min (epsilon`{..K})"
    have "epsilon0 \<in> epsilon`{..K}" unfolding epsilon0_def by (rule Min_in, auto)
    then have "epsilon0 > 0" using E(1) by auto
    have small_setint: "(\<integral>\<^sup>+x\<in>U. ((nn_transfer_operator^^k) h) x \<partial>P) \<le> delta"
              if "k \<le> K" "U \<in> sets P" "emeasure P U < epsilon0" for k U
    proof -
      have *: "epsilon0 \<le> epsilon k"
        unfolding epsilon0_def apply (rule Min_le) using \<open>k \<le> K\<close> by auto
      show ?thesis
        apply (rule less_imp_le[OF E(2)[OF \<open>U \<in> sets P\<close>]])
        using ennreal_leI[OF *] \<open>emeasure P U < epsilon0\<close> by auto
    qed
    then show ?thesis using \<open>epsilon0 > 0\<close> by auto
  qed
  then obtain epsilon::real where "epsilon > 0" and
    small_setint: "\<And>k U. k \<le> K \<Longrightarrow> U \<in> sets P \<Longrightarrow> emeasure P U < epsilon \<Longrightarrow> (\<integral>\<^sup>+x\<in>U. ((nn_transfer_operator^^k) h) x \<partial>P) \<le> delta"
    by blast

  text \<open>Fourth step: obtain an index after which the convergence in distribution ensures that
  the probability to be larger than $2 a$ and to be very large is comparable for $(g+S_n f)/B_n$
  and for $Z$.\<close>
  obtain C0 where "PZ.prob {x. abs(x) \<ge> C0} < epsilon" "C0 \<ge> 1"
    using PZ.random_variable_small_tails[OF \<open>epsilon > 0\<close>, of "\<lambda>x. x"] by auto
  have A: "eventually (\<lambda>n. measure (distr P borel (\<lambda>x. (g x + birkhoff_sum f n x) / B n)) {x. abs (x) > 2 * a} > 3 * alpha) sequentially"
    apply (rule open_set_weak_conv_lsc[of _ Z])
    by (auto simp add: PZ.real_distribution_axioms conv \<open>PZ.prob {x. abs (x) > 2 * a} > 3 * alpha\<close>)
  have B: "eventually (\<lambda>n. measure (distr P borel (\<lambda>x. (g x + birkhoff_sum f n x) / B n)) {x. abs (x) \<ge> C0} < epsilon) sequentially"
    apply (rule closed_set_weak_conv_usc[of _ Z])
    by (auto simp add: PZ.real_distribution_axioms conv \<open>PZ.prob {x. abs(x) \<ge> C0} < epsilon\<close>)
  obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> measure (distr P borel (\<lambda>x. (g x + birkhoff_sum f n x) / B n)) {x. abs (x) > 2 * a} > 3 * alpha"
                    "\<And>n. n \<ge> N \<Longrightarrow> measure (distr P borel (\<lambda>x. (g x + birkhoff_sum f n x) / B n)) {x. abs (x) \<ge> C0} < epsilon"
    using eventually_conj[OF A B] unfolding eventually_sequentially by blast

  text \<open>Fifth step: obtain a trivial control on $B_n$ for $n$ smaller than $N$.\<close>
  define C1 where "C1 = Max {B k/B 0 |k. k \<le> N+K+1}"
  define C where "C = max (max C0 C1) (max (D / (a * B 0)) (C0/a))"
  have "C \<ge> 1" unfolding C_def using \<open>C0 \<ge> 1\<close> by auto

  text \<open>Now, we can put everything together. If $n$ is large enough, we prove that
  $B_{n+1} \leq C \max_{i\leq n} B_i$, by contradiction.\<close>
  have geK: "B (Suc n) \<le> C * Max {B i |i. i \<le> n}" if "n > N + K" for n
  proof (rule ccontr)
    have "Suc n \<ge> N" using that by auto
    let ?h = "(\<lambda>x. (g x + birkhoff_sum f (Suc n) x) / B (Suc n))"
    have "measure (distr P borel ?h) {x. abs (x) > 2 * a}
              = measure P (?h-` {x. abs (x) > 2 * a} \<inter> space P)"
      by (rule measure_distr, auto)
    also have "... = measure P {x \<in> space M. abs(?h x) > 2 * a}"
      by (rule HOL.cong[of "measure P"], auto)
    finally have A: "PS.prob {x \<in> space M. abs(?h x) > 2 * a} > 3 * alpha"
      using N(1)[OF \<open>Suc n \<ge> N\<close>] by auto

    have *: "PS.prob {y \<in> space M. C0 \<le> \<bar>g y + birkhoff_sum f (Suc n - k) y\<bar> / \<bar>B (Suc n - k)\<bar>} < epsilon"
      if "k \<in> {1..<K}" for k
    proof -
      have "Suc n - k \<ge> N" using that \<open>n > N + K\<close> by auto
      let ?h = "(\<lambda>x. (g x + birkhoff_sum f (Suc n-k) x) / B (Suc n-k))"
      have "measure (distr P borel ?h) {x. abs (x) \<ge> C0}
                = measure P (?h-` {x. abs (x) \<ge> C0} \<inter> space P)"
        by (rule measure_distr, auto)
      also have "... = measure P {x \<in> space M. abs(?h x) \<ge> C0}"
        by (rule HOL.cong[of "measure P"], auto)
      finally show ?thesis
        using N(2)[OF \<open>Suc n - k \<ge> N\<close>] by auto
    qed
    have P_le_epsilon: "emeasure P {y \<in> space M. C0 \<le> \<bar>g y + birkhoff_sum f (Suc n - k) y\<bar> / \<bar>B (Suc n - k)\<bar>} < ennreal epsilon"
      if "k \<in> {1..<K}" for k
      using *[OF that] \<open>epsilon > 0\<close> ennreal_lessI unfolding PS.emeasure_eq_measure by auto

    assume "\<not>(B (Suc n) \<le> C * Max {B i |i. i \<le> n})"
    then have "C * Max {B i |i. i \<le> n} \<le> B (Suc n)" by simp
    moreover have "C * B 0 \<le> C * Max {B i |i. i \<le> n}"
      apply (rule mult_left_mono, rule Max_ge) using \<open>C \<ge> 1\<close> by auto
    ultimately have "C * B 0 \<le> B (Suc n)"
      by auto

    have "(D / (a * B 0)) * B 0 \<le> C * B 0"
      apply (rule mult_right_mono) unfolding C_def using Bpos[of 0] by auto
    then have "(D / (a * B 0)) * B 0 \<le> B (Suc n)"
      using \<open>C * B 0 \<le> B (Suc n)\<close> by simp
    then have "D \<le> a * B (Suc n)"
      using Bpos[of 0] \<open>a > 0\<close> by (auto simp add: divide_simps algebra_simps)

    define X where "X = {x \<in> space M. abs((g x + birkhoff_sum f (Suc n) x)/B(Suc n)) > 2 * a}
                        \<inter> {x \<in> space M. \<forall>k < K. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<le> D}
                        \<inter> {x \<in> space M. (\<Sum>i\<in>{1..<K}. h ((T^^i) x)) \<ge> 1}"
    have [measurable]: "X \<in> sets M" unfolding X_def by auto
    have "3 * alpha + (1-alpha) + (1-alpha) \<le>
            PS.prob {x \<in> space M. abs((g x + birkhoff_sum f (Suc n) x)/B(Suc n)) > 2 * a}
          + PS.prob {x \<in> space M. \<forall>k < K. abs(g x + birkhoff_sum f k x - g((T^^k) x)) \<le> D}
          + PS.prob {x \<in> space M. (\<Sum>i\<in>{1..<K}. h ((T^^i) x)) \<ge> 1}"
      using A D K(2) by auto
    also have "... \<le> 2 + PS.prob X"
      unfolding X_def by (rule PS.sum_measure_le_measure_inter3, auto)
    finally have "PS.prob X \<ge> alpha" by auto

    have I: "(\<lambda>y. abs((g y + birkhoff_sum f (Suc n - k) y)/ B (Suc n - k))) ((T^^k) x) \<ge> C0" if "x \<in> X" "k \<in> {1..<K}" for x k
    proof -
      have "2 * a * B(Suc n) \<le> abs(g x + birkhoff_sum f (Suc n) x)"
        using \<open>x \<in> X\<close> Bpos[of "Suc n"] unfolding X_def by (auto simp add: divide_simps)
      also have "... = abs(g((T^^k) x) + birkhoff_sum f (Suc n -k) ((T^^k) x) + (g x + birkhoff_sum f k x - g((T^^k) x)))"
        using \<open>n > N+K\<close> \<open>k \<in> {1..<K}\<close> birkhoff_sum_cocycle[of f k "Suc n - k" x] by auto
      also have "... \<le> abs(g((T^^k) x) + birkhoff_sum f (Suc n -k) ((T^^k) x)) + abs(g x + birkhoff_sum f k x - g((T^^k) x))"
        by auto
      also have "... \<le> abs(g((T^^k) x) + birkhoff_sum f (Suc n -k) ((T^^k) x)) + D"
        using \<open>x \<in> X\<close> \<open>k \<in> {1..<K}\<close> unfolding X_def by auto
      also have "... \<le> abs(g((T^^k) x) + birkhoff_sum f (Suc n -k) ((T^^k) x)) + a * B (Suc n)"
        using \<open>D \<le> a * B (Suc n)\<close> by simp
      finally have *: "a * B (Suc n) \<le> abs(g((T^^k) x) + birkhoff_sum f (Suc n -k) ((T^^k) x))"
        by simp
      have "(C0/a) * B (Suc n - k) \<le> C * B (Suc n - k)"
        apply (rule mult_right_mono) unfolding C_def using less_imp_le[OF Bpos] by auto
      also have "... \<le> C * Max {B i |i. i \<le> n}"
        apply (rule mult_left_mono, rule Max_ge) using \<open>k \<in> {1..<K}\<close> \<open>C \<ge> 1\<close> by auto
      also have "... \<le> B (Suc n)"
        by fact
      finally have "C0 * B (Suc n - k) \<le> a * B (Suc n)"
        using \<open>a>0\<close> by (simp add: divide_simps algebra_simps)
      then have "C0 * B (Suc n - k) \<le> abs(g((T^^k) x) + birkhoff_sum f (Suc n -k) ((T^^k) x))"
        using * by auto
      then show ?thesis
        using Bpos[of "Suc n - k"] by (simp add: divide_simps)
    qed
    have J: "1 \<le> (\<Sum>k\<in>{1..<K}. (\<lambda>y. h y * indicator {y \<in> space M. abs((g y + birkhoff_sum f (Suc n - k) y)/ B (Suc n - k)) \<ge> C0} y) ((T^^k) x))"
      if "x \<in> X" for x
    proof -
      have "x \<in> space M"
        using \<open>x \<in> X\<close> unfolding X_def by auto
      have "1 \<le> (\<Sum>k \<in> {1..<K}. h ((T^^k) x))"
        using \<open>x \<in> X\<close> unfolding X_def by auto
      also have "... = (\<Sum>k \<in> {1..<K}. h ((T^^k) x) * indicator {y \<in> space M. abs((g y + birkhoff_sum f (Suc n - k) y)/ B (Suc n - k)) \<ge> C0} ((T^^k) x))"
        apply (rule sum.cong)
        unfolding indicator_def using I[OF \<open>x \<in> X\<close>] T_spaceM_stable(2)[OF \<open>x \<in> space M\<close>] by auto
      finally show ?thesis by simp
    qed
    have "ennreal alpha \<le> emeasure P X"
      using \<open>PS.prob X \<ge> alpha\<close> by (simp add: PS.emeasure_eq_measure)
    also have "... = (\<integral>\<^sup>+x. indicator X x \<partial>P)"
      by auto
    also have "... \<le> (\<integral>\<^sup>+x. (\<Sum>k\<in>{1..<K}. (\<lambda>y. h y
      * indicator {y \<in> space M. abs((g y + birkhoff_sum f (Suc n - k) y)/ B (Suc n - k)) \<ge> C0} y) ((T^^k) x)) \<partial>P)"
      apply (rule nn_integral_mono) using J unfolding indicator_def by fastforce
    also have "... = (\<Sum>k\<in>{1..<K}. (\<integral>\<^sup>+x. (\<lambda>y. h y
      * indicator {y \<in> space M. abs((g y + birkhoff_sum f (Suc n - k) y)/ B (Suc n - k)) \<ge> C0} y) ((T^^k) x) \<partial>P))"
      by (rule nn_integral_sum, auto)
    also have "... = (\<Sum>k\<in>{1..<K}. (\<integral>\<^sup>+x. (\<lambda>y. h y
      * indicator {y \<in> space M. abs((g y + birkhoff_sum f (Suc n - k) y)/ B (Suc n - k)) \<ge> C0} y) ((T^^k) x) * h x \<partial>M))"
      unfolding \<open>P = density M h\<close> by (auto intro!: sum.cong nn_integral_densityR[symmetric])
    also have "... = (\<Sum>k\<in>{1..<K}. (\<integral>\<^sup>+x. h x
      * indicator {y \<in> space M. abs((g y + birkhoff_sum f (Suc n - k) y)/ B (Suc n - k)) \<ge> C0} x * ((nn_transfer_operator^^k) h) x \<partial>M))"
      by (auto intro!: sum.cong nn_transfer_operator_intTn_g[symmetric])
    also have "... = (\<Sum>k\<in>{1..<K}. (\<integral>\<^sup>+x.
        ((nn_transfer_operator^^k) h) x * indicator {y \<in> space M. abs((g y + birkhoff_sum f (Suc n - k) y)/ B (Suc n - k)) \<ge> C0} x \<partial>P))"
      unfolding \<open>P = density M h\<close> by (subst nn_integral_density, auto intro!: sum.cong simp add: algebra_simps)
    also have "... \<le> (\<Sum>k\<in>{1..<K}. ennreal delta)"
      by (rule sum_mono, rule small_setint, auto simp add: P_le_epsilon)
    also have "... = ennreal (\<Sum>k\<in>{1..<K}. delta)"
      using less_imp_le[OF \<open>delta > 0\<close>] by (rule sum_ennreal)
    finally have "alpha \<le> (\<Sum>k\<in>{1..<K}. delta)"
      apply (subst ennreal_le_iff[symmetric]) using \<open>delta > 0\<close> by auto
    also have "... \<le> K * delta"
      using \<open>delta > 0\<close> by auto
    finally show False
      unfolding delta_def using \<open>K \<ge> 1\<close> \<open>alpha > 0\<close> by (auto simp add: divide_simps algebra_simps)
  qed
  text \<open>If $n$ is not large, we get the same bound in a trivial way, as there are only finitely
  many cases to consider and we have adjusted the constant $C$ so that it works for all of them.\<close>
  have leK: "B (Suc n) \<le> C * Max {B i |i. i \<le> n}" if "n \<le> N+K" for n
  proof -
    have "B (Suc n)/B 0 \<le> Max {B k/B 0 |k. k \<le> N+K+1}"
      apply (rule Max_ge, simp) using \<open>n \<le> N+K\<close> by auto
    also have "... \<le> C" unfolding C_def C1_def by auto
    finally have "B (Suc n) \<le> C * B 0"
      using Bpos[of 0] by (simp add: divide_simps)
    also have "... \<le> C * Max {B i |i. i \<le> n}"
      apply (rule mult_left_mono) apply (rule Max_ge) using \<open>C \<ge> 1\<close> by auto
    finally show ?thesis by simp
  qed
  have "B (Suc n) \<le> C * Max {B i |i. i \<le> n}" for n
    using geK[of n] leK[of n] by force
  then show ?thesis
    using \<open>C \<ge> 1\<close> by auto
qed

text \<open>Then, we prove the lemma without further assumptions, reducing to the previous case by
replacing $m$ with $m+P$. We do this at the level of densities since the addition of measures
is not defined in the library (and it would be problematic as measures carry their sigma-algebra,
so what should one do when the sigma-algebras do not coincide?)\<close>

lemma upper_bound_C:
  "\<exists>C\<ge>1. \<forall>n. B (Suc n) \<le> C * Max {B i|i. i \<le> n}"
proof -
  text \<open>We introduce the density of $P$, and show that it is almost everywhere finite.\<close>
  define h where "h = RN_deriv M P"
  have [measurable]: "h \<in> borel_measurable M"
    unfolding h_def by auto
  have P [simp]: "P = density M h"
    unfolding h_def apply (rule density_RN_deriv[symmetric]) using PabsM by auto
  have "space P = space M"
    by auto
  have *: "AE x in M. h x \<noteq> \<infinity>"
    unfolding h_def apply (rule RN_deriv_finite)
    using PS.sigma_finite_measure_axioms PabsM by auto
  have **: "null_sets (density M (\<lambda>x. 1 + h x)) = null_sets M"
    by (rule null_sets_density, auto)

  text \<open>We introduce the new system with invariant measure $M+P$, given by the density $1+h$.\<close>
  interpret A: conservative "density M (\<lambda>x. 1 + h x)" T
    apply (rule conservative_density) using * by auto
  interpret B: conservative_limit T "density M (\<lambda>x. 1 + h x)" P Z f g B
    apply standard
    using conv Bpos non_trivial absolutely_continuousI_density[OF \<open>h \<in> borel_measurable M\<close>]
    unfolding absolutely_continuous_def ** by auto

  text \<open>We obtain the result by applying the result above to the new dynamical system.
  We have to check the additional assumption that the density of $P$ with respect to the new measure
  $M + P$ is bounded by $1$. Since this density if $h/(1+h)$, this is trivial modulo a computation
  in ennreal that is not automated (yet?).\<close>
  have z: "1 = ennreal 1" by auto
  have Trivial: "a = (1+a) * (a/(1+a))" if "a \<noteq> \<top>" for a::ennreal
    apply (cases a) apply auto unfolding z ennreal_plus_if apply (subst divide_ennreal) apply simp apply simp
    apply (subst ennreal_mult'[symmetric]) using that by auto
  have Trivial2: "a / (1+a) \<le> 1" for a::ennreal
    apply (cases a) apply auto unfolding z ennreal_plus_if apply (subst divide_ennreal) by auto
  show ?thesis
    apply (rule B.upper_bound_C_aux[of "\<lambda>x. h x/(1 + h x)"])
    using * Trivial Trivial2 by (auto simp add: density_density_eq density_unique_iff)
qed

text \<open>The second main upper bound is the following. Again, it proves that
$B_{n+1} \leq L \max_{i \leq n} B_i$, for some constant $L$, but with two differences. First,
$L$ only depends on the distribution of $Z$ (which is stronger). Second, this estimate is only
proved along a density $1$ sequence of times (which is weaker). The first point implies that
this lemma will also apply to $T^j$, with the same $L$, which amounts to replacing $L$ by $L^{1/j}$,
making it in practice arbitrarily close to $1$. The second point is problematic at first sight, but
for the exceptional times we will use the bound of the previous lemma so this will not really
create problems.

For the proof, we split the sum $S_{n+1} f$ as $S_n f + f \circ T^n$. If $B_{n+1}$ is much larger
than $B_n$, we deduce that $S_n f$ is much smaller than $S_{n+1}f$ with large probability, which
means that $f \circ T^n$ is larger than anything that has been seen before. Since preimages of
distinct events have a measure that tends to $0$ along a density $1$ subsequence, this can only
happen along a density $0$ subsequence.\<close>

lemma upper_bound_L:
  fixes a::real and L::real and alpha::real
  assumes "a > 0" "alpha > 0" "L > 3"
          "PZ.prob {x. abs (x) > 2 * a} > 3 * alpha"
          "PZ.prob {x. abs (x) \<ge> (L-1) * a} < alpha"
  shows "\<exists>A. lower_asymptotic_density A = 1 \<and> (\<forall>n\<in>A. B (Suc n) \<le> L * Max {B i|i. i \<le> n})"
proof -
  define m where "m = (\<lambda>n. Max {B i|i. i \<le> n})"
  define K where "K = (\<lambda>n::nat. {x \<in> space M. abs(f x) \<in> {a * L * m n <..< a * L * m (Suc n)}})"
  have [measurable]: "K n \<in> sets M" for n
    unfolding K_def by auto
  have *: "m n \<le> m p" if "n \<le> p" for n p
    unfolding m_def K_def using that by (auto intro!: Max_mono)
  have "K n \<inter> K p = {}" if "n < p" for n p
  proof (auto simp add: K_def)
    fix x assume "\<bar>f x\<bar> < a * L * m (Suc n)" "a * L * m p < \<bar>f x\<bar>"
    moreover have "a * L * m (Suc n) \<le> a * L * m p"
      using *[of "Suc n" p] that \<open>a > 0\<close> \<open>L > 3\<close> by auto
    ultimately show False by auto
  qed
  then have "disjoint_family K"
    unfolding disjoint_family_on_def using nat_neq_iff by auto

  have "\<exists>A0. lower_asymptotic_density A0 = 1 \<and>
            (\<lambda>n. measure P (space M \<inter> (T^^n)-`(K n)) * indicator A0 n) \<longlonglongrightarrow> 0"
    apply (rule disjoint_sets_measure_density_one_tendsto_zero) apply fact+
    using PabsM by auto
  then obtain A0 where A0: "lower_asymptotic_density A0 = 1" "(\<lambda>n. measure P (space M \<inter> (T^^n)-`(K n)) * indicator A0 n) \<longlonglongrightarrow> 0"
    by blast
  obtain N0 where N0: "\<And>n. n \<ge> N0 \<Longrightarrow> measure P (space M \<inter> (T^^n)-`(K n)) * indicator A0 n < alpha"
    using order_tendstoD(2)[OF A0(2) \<open>alpha > 0\<close>] unfolding eventually_sequentially by blast

  have A: "eventually (\<lambda>n. measure (distr P borel (\<lambda>x. (g x + birkhoff_sum f n x) / B n)) {x. abs (x) > 2 * a} > 3 * alpha) sequentially"
    apply (rule open_set_weak_conv_lsc[of _ Z])
    by (auto simp add: PZ.real_distribution_axioms conv assms)
  have B: "eventually (\<lambda>n. measure (distr P borel (\<lambda>x. (g x + birkhoff_sum f n x) / B n)) {x. abs (x) \<ge> (L- 1) * a} < alpha) sequentially"
    apply (rule closed_set_weak_conv_usc[of _ Z])
    by (auto simp add: PZ.real_distribution_axioms conv assms)
  obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> measure (distr P borel (\<lambda>x. (g x + birkhoff_sum f n x) / B n)) {x. abs (x) > 2 * a} > 3 * alpha"
                    "\<And>n. n \<ge> N \<Longrightarrow> measure (distr P borel (\<lambda>x. (g x + birkhoff_sum f n x) / B n)) {x. abs (x) \<ge> (L-1) * a} < alpha"
    using eventually_conj[OF A B] unfolding eventually_sequentially by blast

  have I: "PS.prob {x \<in> space M. abs((g x + birkhoff_sum f n x) / B n) < (L-1) * a} > 1 - alpha" if "n \<ge> N" for n
  proof -
    let ?h = "(\<lambda>x. (g x + birkhoff_sum f n x) / B n)"
    have "measure (distr P borel ?h) {x. abs (x) \<ge> (L-1) * a}
              = measure P (?h-` {x. abs (x) \<ge> (L-1) * a} \<inter> space P)"
      by (rule measure_distr, auto)
    also have "... = measure P {x \<in> space M. abs(?h x) \<ge> (L-1) * a}"
      by (rule HOL.cong[of "measure P"], auto)
    finally have A: "PS.prob {x \<in> space M. abs(?h x) \<ge> (L-1) * a} < alpha"
      using N(2)[OF that] by auto
    have *: "{x \<in> space M. abs(?h x) < (L-1) * a} = space M - {x \<in> space M. abs(?h x) \<ge> (L-1) * a}"
      by auto
    show ?thesis
      unfolding * using A PS.prob_compl by auto
  qed

  have Main: "PS.prob (space M \<inter> (T^^n)-`(K n)) > alpha" if "n \<ge> N" "B (Suc n) > L * m n" for n
  proof -
    have "Suc n \<ge> N" using that by auto
    let ?h = "(\<lambda>x. (g x + birkhoff_sum f (Suc n) x) / B (Suc n))"
    have "measure (distr P borel ?h) {x. abs (x) > 2 * a}
              = measure P (?h-` {x. abs (x) > 2 * a} \<inter> space P)"
      by (rule measure_distr, auto)
    also have "... = measure P {x \<in> space M. abs(?h x) > 2 * a}"
      by (rule HOL.cong[of "measure P"], auto)
    finally have A: "PS.prob {x \<in> space M. abs(?h x) > 2 * a} > 3 * alpha"
      using N(1)[OF \<open>Suc n \<ge> N\<close>] by auto

    define X where "X = {x \<in> space M. abs((g x + birkhoff_sum f n x) / B n) < (L-1) * a}
                          \<inter> {x \<in> space M. abs((g x + birkhoff_sum f (Suc n) x) / B (Suc n)) < (L-1) * a}
                          \<inter> {x \<in> space M. abs((g x + birkhoff_sum f (Suc n) x) / B (Suc n)) > 2 * a}"
    have "(1 - alpha) + (1 - alpha) + 3 * alpha <
            PS.prob {x \<in> space M. abs((g x + birkhoff_sum f n x) / B n) < (L-1) * a}
          + PS.prob {x \<in> space M. abs((g x + birkhoff_sum f (Suc n) x) / B (Suc n)) < (L-1) * a}
          + PS.prob {x \<in> space M. abs((g x + birkhoff_sum f (Suc n) x) / B (Suc n)) > 2 * a}"
      using A I[OF \<open>n \<ge> N\<close>] I[OF \<open>Suc n \<ge> N\<close>] by auto
    also have "... \<le> 2 + PS.prob X"
      unfolding X_def by (rule PS.sum_measure_le_measure_inter3, auto)
    finally have "PS.prob X > alpha" by auto

    have "X \<subseteq> space M \<inter> (T^^n)-`(K n)"
    proof
      have *: "B i \<le> m n" if "i \<le> n" for i
        unfolding m_def by (rule Max_ge, auto simp add: that)
      have **: "B i \<le> B (Suc n)" if "i \<le> Suc n" for i
      proof (cases "i \<le> n")
        case True
        have "m n \<le> B (Suc n) / L"
          using \<open>L * m n < B (Suc n)\<close> \<open>L > 3\<close> by (simp add: divide_simps algebra_simps)
        also have "... \<le> B (Suc n)"
          using Bpos[of "Suc n"] \<open>L > 3\<close> by (simp add: divide_simps algebra_simps)
        finally show ?thesis using *[OF True] by simp
      next
        case False
        then show ?thesis
          using \<open>i \<le> Suc n\<close> le_SucE by blast
      qed
      have "m (Suc n) = B (Suc n)"
        unfolding m_def by (rule Max_eqI, auto simp add: **)

      fix x assume "x \<in> X"
      then have "abs (g x + birkhoff_sum f n x) < (L-1) * a * B n"
        unfolding X_def using Bpos[of n] by (auto simp add: algebra_simps divide_simps)
      also have "... \<le> L * a * m n"
        using *[of n] \<open>L > 3\<close> \<open>a > 0\<close> Bpos[of n] by (auto intro!: mult_mono)
      also have "... \<le> a * B (Suc n)"
        using \<open>B (Suc n) > L * m n\<close> less_imp_le \<open>a > 0\<close> by auto
      finally have A: "abs (g x + birkhoff_sum f n x) < a * B (Suc n)"
        by simp

      have B: "abs(g x + birkhoff_sum f (Suc n) x) < (L-1) * a * B (Suc n)"
        using \<open>x \<in> X\<close> unfolding X_def using Bpos[of "Suc n"] by (auto simp add: algebra_simps divide_simps)
      have *: "f((T^^n) x) = (g x + birkhoff_sum f (Suc n) x) - (g x + birkhoff_sum f n x)"
        apply (auto simp add: algebra_simps)
        by (metis add.commute birkhoff_sum_1(2) birkhoff_sum_cocycle plus_1_eq_Suc)
      have "abs(f((T^^n) x)) \<le> abs (g x + birkhoff_sum f (Suc n) x) + abs(g x + birkhoff_sum f n x)"
        unfolding * by simp
      also have "... < (L-1) * a * B (Suc n) + a * B (Suc n)"
        using A B by auto
      also have "... = L * a * m (Suc n)"
        using \<open>m (Suc n) = B (Suc n)\<close> by (simp add: algebra_simps)
      finally have Z1: "abs(f((T^^n) x)) < L * a * m (Suc n)"
        by simp

      have "2 * a * B (Suc n) < abs (g x + birkhoff_sum f (Suc n) x)"
        using \<open>x \<in> X\<close> unfolding X_def using Bpos[of "Suc n"] by (auto simp add: algebra_simps divide_simps)
      also have "... = abs(f((T^^n) x) + (g x + birkhoff_sum f n x))"
        unfolding * by auto
      also have "... \<le> abs(f((T^^n) x)) + abs (g x + birkhoff_sum f n x)"
        by auto
      also have "... < abs(f((T^^n) x)) + a * B (Suc n)"
        using A by auto
      finally have "abs(f((T^^n) x)) > a * B (Suc n)"
        by simp
      then have Z2: "abs(f((T^^n) x)) > a * L * m n"
        using mult_strict_left_mono[OF \<open>B (Suc n) > L * m n\<close> \<open>a > 0\<close>] by auto

      show "x \<in> space M \<inter> (T ^^ n) -` K n"
        using Z1 Z2 \<open>x \<in> X\<close> unfolding K_def X_def by (auto simp add: algebra_simps)
    qed
    have "PS.prob X \<le> PS.prob (space M \<inter> (T^^n)-`(K n))"
      by (rule PS.finite_measure_mono, fact, auto)
    then show "alpha < PS.prob (space M \<inter> (T ^^ n) -` K n)"
      using \<open>alpha < PS.prob X\<close> by simp
  qed
  define A where "A = A0 \<inter> {N + N0..}"
  have "lower_asymptotic_density A = 1"
    unfolding A_def by (rule lower_asymptotic_density_one_intersection, fact, simp)
  moreover have "B (Suc n) \<le> L * m n" if "n \<in> A" for n
  proof (rule ccontr)
    assume "\<not>(B (Suc n) \<le> L * m n)"
    then have "L * m n < B (Suc n)" "n \<ge> N" "n \<ge> N0"
      using \<open>n \<in> A\<close> unfolding A_def by auto
    then have "PS.prob (space M \<inter> (T^^n)-`(K n)) > alpha"
      using Main by auto
    moreover have "PS.prob (space M \<inter> (T^^n)-`(K n)) * indicator A0 n < alpha"
      using N0[OF \<open>n \<ge> N0\<close>] by simp
    moreover have "indicator A0 n = (1::real)"
      using \<open>n \<in> A\<close> unfolding A_def indicator_def by auto
    ultimately show False
      by simp
  qed
  ultimately show ?thesis
    unfolding m_def by blast
qed

text \<open>Now, we combine the two previous statements to prove the main theorem.\<close>

theorem subexponential_growth:
  "(\<lambda>n. max 0 (ln (B n) /n)) \<longlonglongrightarrow> 0"
proof -
  obtain a0 where a0: "a0 > 0" "PZ.prob {x. abs (x) > a0} > 0"
    using PZ.not_Dirac_0_imp_positive_mass_away_0[OF non_trivial] by blast
  define a where "a = a0/2"
  have "a > 0" using \<open>a0 > 0\<close> unfolding a_def by auto
  define alpha where "alpha = PZ.prob {x. abs (x) > a0}/4"
  have "alpha > 0" unfolding alpha_def using a0 by auto
  have "PZ.prob {x. abs (x) > 2 * a} > 3 * alpha"
    using a0 unfolding a_def alpha_def by auto

  obtain C0 where C0: "PZ.prob {x. abs(x) \<ge> C0} < alpha" "C0 \<ge> 3 * a"
    using PZ.random_variable_small_tails[OF \<open>alpha > 0\<close>, of "\<lambda>x. x"] by auto
  define L where "L = C0/a + 1"
  have "PZ.prob {x. abs(x) \<ge> (L-1) * a} < alpha"
    unfolding L_def using C0 \<open>a>0\<close> by auto
  have "L > 3"
    unfolding L_def using C0 \<open>a > 0\<close> by (auto simp add: divide_simps)

  obtain C where C: "\<And>n. B (Suc n) \<le> C * Max {B i|i. i \<le> n}" "C \<ge> 1"
    using upper_bound_C by blast
  have C2: "B n \<le> C * Max {B i|i. i < n}" if "n > 0" for n
  proof -
    obtain m where m: "n = Suc m"
      using \<open>0 < n\<close> gr0_implies_Suc by auto
    have *: "i \<le> m \<longleftrightarrow> i < Suc m" for i by auto
    show ?thesis using C(1)[of m] unfolding m * by auto
  qed

  have Mainj: "eventually (\<lambda>n. ln (B n) / n \<le> (1+ln L)/j) sequentially" if "j > 0" for j::nat
  proof -
    have *: "\<exists>A. lower_asymptotic_density A = 1 \<and> (\<forall>n\<in>A. B (j * Suc n + k) \<le> L * Max {B (j * i + k) |i. i \<le> n})" for k
    proof -
      interpret Tj0: conservative M "(T^^j)" using conservative_power[of j] by auto
      have *: "g x + birkhoff_sum f k x + Tj0.birkhoff_sum (\<lambda>x. birkhoff_sum f j ((T ^^ k) x)) n x = g x + birkhoff_sum f (j * n + k) x" for x n
      proof -
        have "birkhoff_sum f (j * n + k) x = (\<Sum>i \<in> {..<k} \<union> {k..<j * n + k}. f ((T ^^ i) x))"
          unfolding birkhoff_sum_def by (rule sum.cong, auto)
        also have "... = (\<Sum>i \<in> {..<k}. f ((T ^^ i) x)) + (\<Sum>i \<in> {k..<j * n + k}. f ((T ^^ i) x))"
          by (auto intro!: sum.union_disjoint)
        also have "... = birkhoff_sum f k x + (\<Sum>s<j. \<Sum>i<n. f ((T ^^ (i * j + s)) ((T^^k) x)))"
          apply (subst sum_arith_progression)
          unfolding birkhoff_sum_def Tj0.birkhoff_sum_def funpow_mult funpow_add'[symmetric]
          by (auto simp add: algebra_simps intro!: sum.reindex_bij_betw[symmetric] bij_betw_byWitness[of _ "\<lambda>a. a-k"])
        also have "... = birkhoff_sum f k x + Tj0.birkhoff_sum (\<lambda>x. birkhoff_sum f j ((T ^^ k) x)) n x"
          unfolding birkhoff_sum_def Tj0.birkhoff_sum_def funpow_mult funpow_add'[symmetric]
          by (auto simp add: algebra_simps intro!: sum.swap)
        finally show ?thesis by simp
      qed
      interpret Tj: conservative_limit "T^^j" M P Z "\<lambda>x. birkhoff_sum f j ((T^^k) x)" "\<lambda>x. g x + birkhoff_sum f k x" "\<lambda>n. B (j * n + k)"
        apply standard
        using PabsM Bpos non_trivial conv \<open>j>0\<close> unfolding * by (auto intro!: weak_conv_m_subseq strict_monoI)
      show ?thesis
        apply (rule Tj.upper_bound_L[OF \<open>a > 0\<close> \<open>alpha > 0\<close>]) by fact+
    qed
    have "\<exists>A. \<forall>k. lower_asymptotic_density (A k) = 1 \<and> (\<forall>n\<in>A k. B (j * Suc n + k) \<le> L * Max {B (j * i + k) |i. i \<le> n})"
      apply (rule choice) using * by auto
    then obtain A where A: "\<And>k. lower_asymptotic_density (A k) = 1" "\<And>k n. n \<in> A k \<Longrightarrow> B (j * Suc n + k) \<le> L * Max {B (j * i + k) |i. i \<le> n}"
      by blast
    define Aj where "Aj = (\<Inter>k<j. A k)"
    have "lower_asymptotic_density Aj = 1"
      unfolding Aj_def using A(1) by (simp add: lower_asymptotic_density_one_finite_Intersection)
    define Bj where "Bj = UNIV - Aj"
    have "upper_asymptotic_density Bj = 0"
      using \<open>lower_asymptotic_density Aj = 1\<close>
      unfolding Bj_def lower_upper_asymptotic_density_complement by simp

    define M where "M = (\<lambda>n. Max {B p |p. p < (n+1) * j})"
    have "B 0 \<le> M n" for n
      unfolding M_def apply (rule Max_ge, auto, rule exI[of _ 0]) using \<open>j > 0\<close> by auto
    then have Mpos: "M n > 0" for n
      by (metis Bpos not_le not_less_iff_gr_or_eq order.strict_trans)
    have M_L: "M (Suc n) \<le> L * M n" if "n \<in> Aj" for n
    proof -
      have *: "B s \<le> L * M n" if "s < (n+2) * j" for s
      proof (cases "s < (n+1) * j")
        case True
        have "B s \<le> M n"
          unfolding M_def apply (rule Max_ge) using True by auto
        also have "... \<le> L * M n" using \<open>L > 3\<close> \<open>M n > 0\<close> by auto
        finally show ?thesis by simp
      next
        case False
        then obtain k where "k < j" "s = (n+1) * j + k" using \<open>s < (n+2) * j\<close> le_Suc_ex by force
        then have "B s = B (j * Suc n + k)" by (auto simp add: algebra_simps)
        also have "... \<le> L * Max {B (j * i + k) |i. i \<le> n}"
          using A(2)[of n k] \<open>n \<in> Aj\<close> unfolding Aj_def using \<open>k < j\<close> by auto
        also have "... \<le> L * Max {B a|a. a < (n+1) * j}"
          apply (rule mult_left_mono, rule Max_mono) using \<open>L>3\<close> proof (auto)
          fix i assume "i \<le> n" show "\<exists>a. B (j * i + k) = B a \<and> a < j + n * j"
            apply (rule exI[of _ "j * i + k"]) using \<open>k < j\<close> \<open>i \<le> n\<close>
            by (auto simp add: add_mono_thms_linordered_field(3) algebra_simps)
        qed
        finally show ?thesis unfolding M_def by auto
      qed
      show ?thesis
        unfolding M_def apply (rule Max.boundedI)
        using * unfolding M_def using \<open>j > 0\<close> by auto
    qed
    have M_C: "M (Suc n) \<le> C^j * M n" for n
    proof -
      have I: "Max {B s|s. s < (n+1) * j + k} \<le> C^k * M n" for k
      proof (induction k)
        case 0
        show ?case
          apply (rule Max.boundedI) unfolding M_def using \<open>j > 0\<close> by auto
      next
        case (Suc k)
        have *: "B s \<le> C * C ^ k * M n" if "s < Suc (j + n * j + k)" for s
        proof (cases "s < j + n * j + k")
          case True
          then have "B s \<le> C^k * M n" using iffD1[OF Max_le_iff, OF _ _ Suc.IH] by auto
          also have "... \<le> C * C^k * M n" using \<open>C \<ge> 1\<close> \<open>M n > 0\<close> by auto
          finally show ?thesis by simp
        next
          case False
          then have "s = j + n * j + k" using that by auto
          then have "B s \<le> C * Max {B s|s. s < (n+1) * j + k}" using C2[of s] using \<open>j > 0\<close> by auto
          also have "... \<le> C * C^k * M n" using Suc.IH \<open>C \<ge> 1\<close> by auto
          finally show ?thesis by simp
        qed
        show ?case
          apply (rule Max.boundedI) using \<open>j > 0\<close> * by auto
      qed
      show ?thesis using I[of j] unfolding M_def by (auto simp add: algebra_simps)
    qed
    have I: "ln (M n) \<le> ln (M 0) + n * ln L + card (Bj \<inter> {..<n}) * ln (C^j)" for n
    proof (induction n)
      case 0
      show ?case by auto
    next
      case (Suc n)
      show ?case
      proof (cases "n \<in> Bj")
        case True
        then have *: "Bj \<inter> {..<Suc n} = Bj \<inter> {..<n} \<union> {n}" by auto
        have **: "card (Bj \<inter> {..<Suc n}) = card (Bj \<inter> {..<n}) + card {n}"
          unfolding * by (rule card_Un_disjoint, auto)

        have "ln (M (Suc n)) \<le> ln (C^j * M n)"
          using M_C \<open>\<And>n. 0 < M n\<close> less_le_trans ln_le_cancel_iff by blast
        also have "... = ln (M n) + ln (C^j)"
          using \<open>C \<ge> 1\<close> \<open>0 < M n\<close> ln_mult by auto
        also have "... \<le> ln (M 0) + n * ln L + card (Bj \<inter> {..<n}) * ln (C^j) + ln (C^j)"
          using Suc.IH by auto
        also have "... = ln (M 0) + n * ln L + card (Bj \<inter> {..<Suc n}) * ln (C^j)"
          using ** by (auto simp add: algebra_simps)
        also have "... \<le> ln (M 0) + (Suc n) * ln L + card (Bj \<inter> {..<Suc n}) * ln (C^j)"
          using \<open>L > 3\<close> by auto
        finally show ?thesis by auto
      next
        case False
        have "M (Suc n) \<le> L * M n"
          apply (rule M_L) using False unfolding Bj_def by auto
        then have "ln (M (Suc n)) \<le> ln (L * M n)"
          using \<open>\<And>n. 0 < M n\<close> less_le_trans ln_le_cancel_iff by blast
        also have "... = ln (M n) + ln L"
          using \<open>L > 3\<close> \<open>0 < M n\<close> ln_mult by auto
        also have "... \<le> ln (M 0) + Suc n * ln L + card (Bj \<inter> {..<n}) * ln (C^j)"
          using Suc.IH by (auto simp add: algebra_simps)
        also have "... \<le> ln (M 0) + Suc n * ln L + card (Bj \<inter> {..<Suc n}) * ln (C^j)"
          using \<open>C \<ge> 1\<close> by (auto intro!: mult_right_mono card_mono)
        finally show ?thesis by auto
      qed
    qed
    have "ln (M n)/n \<le> ln (M 0)* (1/n) + ln L + (card (Bj \<inter> {..<n})/n) * ln (C^j)" if "n\<ge>1" for n
      using that apply (auto simp add: algebra_simps divide_simps)
      by (metis (no_types, hide_lams) I add.assoc mult.commute mult_left_mono of_nat_0_le_iff semiring_normalization_rules(34))
    then have A: "eventually (\<lambda>n. ln (M n)/n \<le> ln (M 0)* (1/n) + ln L + (card (Bj \<inter> {..<n})/n) * ln (C^j)) sequentially"
      unfolding eventually_sequentially by blast

    have *: "(\<lambda>n. ln (M 0)*(1/n) + ln L + (card (Bj \<inter> {..<n})/n) * ln (C^j)) \<longlonglongrightarrow> ln (M 0) * 0 + ln L + 0 *ln (C^j)"
      by (intro tendsto_intros upper_asymptotic_density_zero_lim, fact)
    have B: "eventually (\<lambda>n. ln (M 0)*(1/n) + ln L + (card (Bj \<inter> {..<n})/n) * ln (C^j) < 1 + ln L) sequentially"
      by (rule order_tendstoD[OF *], auto)
    have "eventually (\<lambda>n. ln (M n)/n < 1 + ln L) sequentially"
      using eventually_conj[OF A B] by (simp add: eventually_mono)
    then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> ln (M n)/n < 1 + ln L"
      unfolding eventually_sequentially by blast
    have "ln (B p) / p \<le> (1+ln L) / j" if "p \<ge> (N+1) * j" for p
    proof -
      define n where "n = p div j"
      have "n \<ge> N+1" unfolding n_def using that
        by (metis \<open>0 < j\<close> div_le_mono div_mult_self_is_m)
      then have "n \<ge> N" "n \<ge> 1" by auto
      have *: "p < (n+1) * j" "n * j \<le> p"
        unfolding n_def using \<open>j > 0\<close> dividend_less_div_times by auto
      have "B p \<le> M n"
        unfolding M_def apply (rule Max_ge) using * by auto
      then have "ln (B p) \<le> ln (M n)"
        using Bpos Mpos ln_le_cancel_iff by blast
      also have "... \<le> n * (1+ln L)"
        using N[OF \<open>n \<ge> N\<close>] \<open>n \<ge> 1\<close> by (auto simp add: divide_simps algebra_simps)
      also have "... \<le> (p/j) * (1+ln L)"
        apply (rule mult_right_mono) using *(2) \<open>j > 0\<close> \<open>L > 3\<close>
        apply (auto simp add: divide_simps algebra_simps)
        using of_nat_mono by fastforce
      finally show ?thesis
        using \<open>j > 0\<close> that by (simp add: algebra_simps divide_simps)
    qed
    then show "eventually (\<lambda>p. ln (B p) / p \<le> (1+ln L)/j) sequentially"
      unfolding eventually_sequentially by auto
  qed
  show "(\<lambda>n. max 0 (ln (B n) / real n)) \<longlonglongrightarrow> 0"
  proof (rule order_tendstoI)
    fix e::real assume "e > 0"
    have *: "(\<lambda>j. (1+ln L) * (1/j)) \<longlonglongrightarrow> (1+ln L) * 0"
      by (intro tendsto_intros)
    have "eventually (\<lambda>j. (1+ln L) * (1/j) < e) sequentially"
      apply (rule order_tendstoD[OF *]) using \<open>e > 0\<close> by auto
    then obtain j::nat where j: "j > 0" "(1+ln L) * (1/j) < e"
      unfolding eventually_sequentially using add.right_neutral le_eq_less_or_eq by fastforce
    show "eventually (\<lambda>n. max 0 (ln (B n) / real n) < e) sequentially"
      using Mainj[OF \<open>j > 0\<close>] j(2) \<open>e > 0\<close> by (simp add: eventually_mono)
  qed (simp add: max.strict_coboundedI1)
qed


end (*of locale conservative_limit*)

subsection \<open>Normalizing sequences grow at most polynomially in probability preserving systems\<close>

text \<open>In probability preserving systems, normalizing sequences grow at most polynomially.
The proof, also given in~\cite{gouezel_normalizing_sequences}, is considerably easier than
the conservative case. We prove that $B_{n+1} \leq C B_n$ (more precisely, this only holds if
$B_{n+1}$ is large enough), by arguing that $S_{n+1} f = S_n f + f \circ T^n$, where $f\circ T^n$
is negligible if $B_{n+1}$ is large thanks to the measure preservation. We also prove that
$B_{2n} \leq E B_n$, by writing $S_{2n} f = S_n f+ S_n f \circ T^n$ and arguing that the two terms
on the right have the same distribution. Finally, combining these two estimates, the polynomial
growth follows readily.\<close>

locale pmpt_limit =
  pmpt M + PZ: real_distribution Z
    for M::"'a measure" and Z::"real measure" +
  fixes f::"'a \<Rightarrow> real" and B::"nat \<Rightarrow> real"
  assumes Bpos: "\<And>n. B n > 0"
      and M [measurable]: "f \<in> borel_measurable M"
      and non_trivial: "PZ.prob {0} < 1"
      and conv: "weak_conv_m (\<lambda>n. distr P borel (\<lambda>x. (birkhoff_sum f n x) / B n)) Z"
begin

text \<open>First, we prove that $B_{n+1} \leq C B_n$ if $B_{n+1}$ is large enough.\<close>

lemma upper_bound_CD:
  "\<exists>C D. (\<forall>n. B (Suc n) \<le> D \<or> B (Suc n) \<le> C * B n) \<and> C \<ge> 1"
proof -
  obtain a where a: "a > 0" "PZ.prob {x. abs (x) > a} > 0"
    using PZ.not_Dirac_0_imp_positive_mass_away_0[OF non_trivial] by blast
  define alpha where "alpha = PZ.prob {x. abs (x) > a}/4"
  have "alpha > 0" unfolding alpha_def using a by auto
  have A: "PZ.prob {x. abs (x) > a} > 3 * alpha"
    using a unfolding alpha_def by auto

  obtain C0 where C0: "PZ.prob {x. abs(x) \<ge> C0} < alpha" "C0 \<ge> a"
    using PZ.random_variable_small_tails[OF \<open>alpha > 0\<close>, of "\<lambda>x. x"] by auto

  have A: "eventually (\<lambda>n. measure (distr M borel (\<lambda>x. (birkhoff_sum f n x) / B n)) {x. abs (x) > a} > 3 * alpha) sequentially"
    apply (rule open_set_weak_conv_lsc[of _ Z])
    by (auto simp add: PZ.real_distribution_axioms conv A)
  have B: "eventually (\<lambda>n. measure (distr M borel (\<lambda>x. (birkhoff_sum f n x) / B n)) {x. abs (x) \<ge> C0} < alpha) sequentially"
    apply (rule closed_set_weak_conv_usc[of _ Z])
    by (auto simp add: PZ.real_distribution_axioms conv C0)
  obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> measure (distr M borel (\<lambda>x. (birkhoff_sum f n x) / B n)) {x. abs x > a} > 3 * alpha"
                    "\<And>n. n \<ge> N \<Longrightarrow> measure (distr M borel (\<lambda>x. (birkhoff_sum f n x) / B n)) {x. abs x \<ge> C0} < alpha"
    using eventually_conj[OF A B] unfolding eventually_sequentially by blast

  obtain Cf where Cf: "prob {x \<in> space M. abs(f x) \<ge> Cf} < alpha" "Cf \<ge> 1"
    using random_variable_small_tails[OF \<open>alpha > 0\<close> M] by auto
  have Main: "B (Suc n) \<le> (2*C0/a) * B n" if "n \<ge> N" "B (Suc n) \<ge> 2 * Cf/a" for n
  proof -
    have "Suc n \<ge> N" using that by auto
    let ?h = "(\<lambda>x. (birkhoff_sum f (Suc n) x) / B (Suc n))"
    have "measure (distr M borel ?h) {x. abs (x) > a}
              = measure M (?h-` {x. abs (x) > a} \<inter> space M)"
      by (rule measure_distr, auto)
    also have "... = prob {x \<in> space M. abs(?h x) > a}"
      by (rule HOL.cong[of "measure M"], auto)
    finally have A: "prob {x \<in> space M. abs(?h x) > a} > 3 * alpha"
      using N(1)[OF \<open>Suc n \<ge> N\<close>] by auto

    let ?h = "(\<lambda>x. (birkhoff_sum f n x) / B n)"
    have "measure (distr M borel ?h) {x. abs (x) \<ge> C0}
              = measure M (?h-` {x. abs (x) \<ge> C0} \<inter> space M)"
      by (rule measure_distr, auto)
    also have "... = measure M {x \<in> space M. abs(?h x) \<ge> C0}"
      by (rule HOL.cong[of "measure M"], auto)
    finally have B0: "prob {x \<in> space M. abs(?h x) \<ge> C0} < alpha"
      using N(2)[OF \<open>n \<ge> N\<close>] by auto
    have *: "{x \<in> space M. abs(?h x) < C0} = space M - {x \<in> space M. abs(?h x) \<ge> C0}"
      by auto
    have B: "prob {x \<in> space M. abs(?h x) < C0} > 1- alpha"
      unfolding * using B0 prob_compl by auto

    have "prob {x \<in> space M. abs(f ((T^^n) x)) \<ge> Cf} = prob ((T^^n)-`{x \<in> space M. abs(f x) \<ge> Cf} \<inter> space M)"
      by (rule HOL.cong[of "prob"], auto)
    also have "... = prob {x \<in> space M. abs(f x) \<ge> Cf}"
      using T_vrestr_same_measure(2)[of "{x \<in> space M. abs(f x) \<ge> Cf}" n]
      unfolding vimage_restr_def by auto
    finally have C0: "prob {x \<in> space M. abs(f ((T^^n) x)) \<ge> Cf} < alpha"
      using Cf by simp
    have *: "{x \<in> space M. abs(f ((T^^n) x)) < Cf} = space M - {x \<in> space M. abs(f ((T^^n) x)) \<ge> Cf}"
      by auto
    have C: "prob {x \<in> space M. abs(f ((T^^n) x)) < Cf} > 1- alpha"
      unfolding * using C0 prob_compl by auto

    define X where "X = {x \<in> space M. abs((birkhoff_sum f n x) / B n) < C0}
                          \<inter> {x \<in> space M. abs((birkhoff_sum f (Suc n) x) / B (Suc n)) > a}
                          \<inter> {x \<in> space M. abs(f ((T^^n) x)) < Cf}"
    have "(1 - alpha) + 3 * alpha + (1 - alpha) <
            prob {x \<in> space M. abs((birkhoff_sum f n x) / B n) < C0}
          + prob {x \<in> space M. abs((birkhoff_sum f (Suc n) x) / B (Suc n)) > a}
          + prob {x \<in> space M. abs(f ((T^^n) x)) < Cf}"
      using A B C by auto
    also have "... \<le> 2 + prob X"
      unfolding X_def by (rule sum_measure_le_measure_inter3, auto)
    finally have "prob X > alpha" by auto
    then have "X \<noteq> {}" using \<open>alpha > 0\<close> by auto
    then obtain x where "x \<in> X" by auto
    have *: "abs(birkhoff_sum f n x) \<le> C0 * B n"
            "abs(birkhoff_sum f (Suc n) x) \<ge> a * B (Suc n)"
            "abs(f((T^^n) x)) \<le> Cf"
      using \<open>x \<in> X\<close> Bpos[of n] Bpos[of "Suc n"] unfolding X_def by (auto simp add: divide_simps)
    have "a * B (Suc n) \<le> abs(birkhoff_sum f (Suc n) x)"
      using * by simp
    also have "... = abs(birkhoff_sum f n x + f ((T^^n) x))"
      by (metis Groups.add_ac(2) One_nat_def birkhoff_sum_1(3) birkhoff_sum_cocycle plus_1_eq_Suc)
    also have "... \<le> C0 * B n + Cf"
      using * by auto
    also have "... \<le> C0 * B n + (a/2) * B (Suc n)"
      using \<open>B (Suc n) \<ge> 2 * Cf/a\<close> \<open>a > 0\<close> by (auto simp add: divide_simps algebra_simps)
    finally show "B (Suc n) \<le> (2 * C0/a) * B n"
      using \<open>a > 0\<close> by (auto simp add: divide_simps algebra_simps)
  qed
  define C1 where "C1 = Max {B(Suc n)/B n |n. n \<le> N}"
  have *: "B (Suc n) \<le> max ((2 * C0/a)) C1 * B n" if "B (Suc n) > 2 * Cf/a" for n
  proof (cases "n > N")
    case True
    then show ?thesis
      using Main[OF less_imp_le[OF \<open>n > N\<close>] less_imp_le[OF that]] Bpos[of n]
      by (meson max.cobounded1 order_trans real_mult_le_cancel_iff1)
  next
    case False
    then have "n \<le> N" by simp
    have "B(Suc n)/B n \<le> C1"
      unfolding C1_def apply (rule Max_ge) using \<open>n \<le> N\<close> by auto
    then have "B (Suc n) \<le> C1 * B n"
      using Bpos[of n] by (simp add: divide_simps)
    then show ?thesis
      using Bpos[of n] by (meson max.cobounded2 order_trans real_mult_le_cancel_iff1)
  qed
  show ?thesis
    apply (rule exI[of _ "max ((2 * C0/a)) C1"], rule exI[of _ "2 * Cf/a"])
    using * linorder_not_less \<open>C0 \<ge> a\<close> \<open>a > 0\<close> by (auto intro!: max.coboundedI1)
qed

text \<open>Second, we prove that $B_{2n} \leq E B_n$.\<close>

lemma upper_bound_E:
  "\<exists>E. \<forall>n. B (2 * n) \<le> E * B n"
proof -
  obtain a where a: "a > 0" "PZ.prob {x. abs (x) > a} > 0"
    using PZ.not_Dirac_0_imp_positive_mass_away_0[OF non_trivial] by blast
  define alpha where "alpha = PZ.prob {x. abs (x) > a}/4"
  have "alpha > 0" unfolding alpha_def using a by auto
  have A: "PZ.prob {x. abs (x) > a} > 3 * alpha"
    using a unfolding alpha_def by auto

  obtain C0 where C0: "PZ.prob {x. abs(x) \<ge> C0} < alpha" "C0 \<ge> a"
    using PZ.random_variable_small_tails[OF \<open>alpha > 0\<close>, of "\<lambda>x. x"] by auto

  have A: "eventually (\<lambda>n. measure (distr M borel (\<lambda>x. (birkhoff_sum f n x) / B n)) {x. abs (x) > a} > 3 * alpha) sequentially"
    apply (rule open_set_weak_conv_lsc[of _ Z])
    by (auto simp add: PZ.real_distribution_axioms conv A)
  have B: "eventually (\<lambda>n. measure (distr M borel (\<lambda>x. (birkhoff_sum f n x) / B n)) {x. abs (x) \<ge> C0} < alpha) sequentially"
    apply (rule closed_set_weak_conv_usc[of _ Z])
    by (auto simp add: PZ.real_distribution_axioms conv C0)
  obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> measure (distr M borel (\<lambda>x. (birkhoff_sum f n x) / B n)) {x. abs x > a} > 3 * alpha"
                    "\<And>n. n \<ge> N \<Longrightarrow> measure (distr M borel (\<lambda>x. (birkhoff_sum f n x) / B n)) {x. abs x \<ge> C0} < alpha"
    using eventually_conj[OF A B] unfolding eventually_sequentially by blast

  have Main: "B (2 * n) \<le> (2*C0/a) * B n" if "n \<ge> N" for n
  proof -
    have "2 * n \<ge> N" using that by auto
    let ?h = "(\<lambda>x. (birkhoff_sum f (2 * n) x) / B (2 * n))"
    have "measure (distr M borel ?h) {x. abs (x) > a}
              = measure M (?h-` {x. abs (x) > a} \<inter> space M)"
      by (rule measure_distr, auto)
    also have "... = prob {x \<in> space M. abs(?h x) > a}"
      by (rule HOL.cong[of "measure M"], auto)
    finally have A: "prob {x \<in> space M. abs((birkhoff_sum f (2 * n) x) / B (2 * n)) > a} > 3 * alpha"
      using N(1)[OF \<open>2 * n \<ge> N\<close>] by auto

    let ?h = "(\<lambda>x. (birkhoff_sum f n x) / B n)"
    have "measure (distr M borel ?h) {x. abs (x) \<ge> C0}
              = measure M (?h-` {x. abs (x) \<ge> C0} \<inter> space M)"
      by (rule measure_distr, auto)
    also have "... = measure M {x \<in> space M. abs(?h x) \<ge> C0}"
      by (rule HOL.cong[of "measure M"], auto)
    finally have B0: "prob {x \<in> space M. abs(?h x) \<ge> C0} < alpha"
      using N(2)[OF \<open>n \<ge> N\<close>] by auto
    have *: "{x \<in> space M. abs(?h x) < C0} = space M - {x \<in> space M. abs(?h x) \<ge> C0}"
      by auto
    have B: "prob {x \<in> space M. abs((birkhoff_sum f n x) / B n) < C0} > 1- alpha"
      unfolding * using B0 prob_compl by auto

    have "prob {x \<in> space M. abs(?h ((T^^n) x)) < C0} = prob ((T^^n)-`{x \<in> space M. abs(?h x) < C0} \<inter> space M)"
      by (rule HOL.cong[of "prob"], auto)
    also have "... = prob {x \<in> space M. abs(?h x) < C0}"
      using T_vrestr_same_measure(2)[of "{x \<in> space M. abs(?h x) < C0}" n]
      unfolding vimage_restr_def by auto
    finally have C: "prob {x \<in> space M. abs((birkhoff_sum f n ((T^^n) x)) / B n) < C0} > 1- alpha"
      using B by simp

    define X where "X = {x \<in> space M. abs((birkhoff_sum f n x) / B n) < C0}
                          \<inter> {x \<in> space M. abs((birkhoff_sum f (2* n) x) / B (2* n)) > a}
                          \<inter> {x \<in> space M. abs((birkhoff_sum f n ((T^^n) x)) / B n) < C0}"
    have "(1 - alpha) + 3 * alpha + (1 - alpha) <
            prob {x \<in> space M. abs((birkhoff_sum f n x) / B n) < C0}
          + prob {x \<in> space M. abs((birkhoff_sum f (2* n) x) / B (2* n)) > a}
          + prob {x \<in> space M. abs((birkhoff_sum f n ((T^^n) x)) / B n) < C0}"
      using A B C by auto
    also have "... \<le> 2 + prob X"
      unfolding X_def by (rule sum_measure_le_measure_inter3, auto)
    finally have "prob X > alpha" by auto
    then have "X \<noteq> {}" using \<open>alpha > 0\<close> by auto
    then obtain x where "x \<in> X" by auto
    have *: "abs(birkhoff_sum f n x) \<le> C0 * B n"
            "abs((birkhoff_sum f (2 * n) x)) \<ge> a * B (2 * n)"
            "abs((birkhoff_sum f n ((T^^n) x))) \<le> C0 * B n"
      using \<open>x \<in> X\<close> Bpos[of n] Bpos[of "2* n"] unfolding X_def by (auto simp add: divide_simps)
    have "a * B (2 * n) \<le> abs(birkhoff_sum f (2 * n) x)"
      using * by simp
    also have "... = abs(birkhoff_sum f n x + birkhoff_sum f n ((T^^n) x))"
      unfolding birkhoff_sum_cocycle[of f n n x, symmetric] by (simp add: mult_2)
    also have "... \<le> 2 * C0 * B n"
      using * by auto
    finally show "B (2 * n) \<le> (2 * C0/a) * B n"
      using \<open>a > 0\<close> by (auto simp add: divide_simps algebra_simps)
  qed
  define C1 where "C1 = Max {B(2 * n)/B n |n. n \<le> N}"
  have *: "B (2*n) \<le> max ((2 * C0/a)) C1 * B n" for n
  proof (cases "n > N")
    case True
    then show ?thesis
      using Main[OF less_imp_le[OF \<open>n > N\<close>]] Bpos[of n]
      by (meson max.cobounded1 order_trans real_mult_le_cancel_iff1)
  next
    case False
    then have "n \<le> N" by simp
    have "B(2*n)/B n \<le> C1"
      unfolding C1_def apply (rule Max_ge) using \<open>n \<le> N\<close> by auto
    then have "B (2*n) \<le> C1 * B n"
      using Bpos[of n] by (simp add: divide_simps)
    then show ?thesis
      using Bpos[of n] by (meson max.cobounded2 order_trans real_mult_le_cancel_iff1)
  qed
  show ?thesis
    apply (rule exI[of _ "max ((2 * C0/a)) C1"])
    using * by auto
qed

text \<open>Finally, we combine the estimates in the two lemmas above to show that $B_n$ grows
at most polynomially.\<close>

theorem polynomial_growth:
  "\<exists>C K. \<forall>n>0. B n \<le> C * (real n)^K"
proof -
  obtain C D where C: "C \<ge> 1" "\<And>n. B (Suc n) \<le> D \<or> B (Suc n) \<le> C * B n"
    using upper_bound_CD by blast
  obtain E where E: "\<And>n. B (2 * n) \<le> E * B n"
    using upper_bound_E by blast
  have "E \<ge> 1" using E[of 0] Bpos[of 0] by auto

  obtain k::nat where "log 2 (max C E) \<le> k"
    using real_arch_simple[of "log 2 (max C E)"] by blast
  then have "max C E \<le> 2^k"
    by (meson less_log_of_power not_less one_less_numeral_iff semiring_norm(76))
  then have "C \<le> 2^k" "E \<le> 2^k"
    by auto

  define P where "P = max D (B 0)"
  have "P > 0" unfolding P_def using Bpos[of 0] by auto
  have Main: "\<And>n. n < 2^r \<Longrightarrow> B n \<le> P * 2^(2 * k * r)" for r
  proof (induction r)
    case 0
    fix n::nat assume "n < 2^0"
    then show "B n \<le> P * 2 ^ (2 * k * 0)"
      unfolding P_def by auto
  next
    case (Suc r)
    fix n::nat assume "n < 2^(Suc r)"
    consider "even n" | "B n \<le> D" | "odd n \<and> B n > D" by linarith
    then show "B n \<le> P * 2 ^ (2 * k * Suc r)"
    proof (cases)
      case 1
      then obtain m where m: "n = 2 * m" by (rule evenE)
      have "m < 2^r"
        using \<open>n < 2^(Suc r)\<close> unfolding m by auto
      then have *: "B m \<le> P * 2^(2 * k * r)"
        using Suc.IH by auto
      have "B n \<le> E * B m"
        unfolding m using E by simp
      also have "... \<le> 2^k * B m"
        apply (rule mult_right_mono[OF _ less_imp_le[OF Bpos[of m]]])
        using \<open>E \<le> 2^k\<close> by simp
      also have "... \<le> 2^k * (P * 2^(2 * k * r))"
        apply (rule mult_left_mono[OF *]) by auto
      also have "... = P * 2^(2 * k * r + k)"
        by (auto simp add: algebra_simps power_add)
      also have "... \<le> P * 2^(2 * k * Suc r)"
        apply (rule mult_left_mono) using \<open>P > 0\<close> by auto
      finally show ?thesis by simp
    next
      case 2
      have "D \<le> P * 1"
        unfolding P_def by auto
      also have "... \<le> P * 2^(2 * k * Suc r)"
        by (rule mult_left_mono[OF _ less_imp_le[OF \<open>P > 0\<close>]], auto)
      finally show ?thesis using 2 by simp
    next
      case 3
      then obtain m where m: "n = 2 * m + 1"
        using oddE by blast
      have "m < 2^r"
        using \<open>n < 2^(Suc r)\<close> unfolding m by auto
      then have *: "B m \<le> P * 2^(2 * k * r)"
        using Suc.IH by auto
      have "B n > D" using 3 by auto
      then have "B n \<le> C * B (2 * m)"
        unfolding m using C(2)[of "2 * m"] by auto
      also have "... \<le> C * (E * B m)"
        apply (rule mult_left_mono) using \<open>C \<ge> 1\<close> E[of m] by auto
      also have "... \<le> 2^k * (2^k * B m)"
        apply (intro mult_mono) using \<open>C \<le> 2^k\<close> \<open>C \<ge> 1\<close> \<open>E \<ge> 1\<close> \<open>E \<le> 2^k\<close> Bpos[of m] by auto
      also have "... \<le> 2^k * (2^k * (P * 2^(2 * k * r)))"
        apply (intro mult_left_mono) using * by auto
      also have "... = P * 2^(2 * k * Suc r)"
        using \<open>P > 0\<close> by (simp add: algebra_simps divide_simps mult_2_right power_add)
      finally show ?thesis by simp
    qed
  qed
  have I: "B n \<le> (P * 2^(2 * k)) * n^(2 * k)" if "n > 0" for n
  proof -
    define r::nat where "r = nat(floor(log 2 (real n)))"
    have *: "int r = floor(log 2 (real n))"
      unfolding r_def using \<open>0 < n\<close> by auto
    have I: "2^r \<le> n \<and> n < 2^(r+1)"
      using floor_log_nat_eq_powr_iff[OF _ \<open>n > 0\<close>, of 2 r] * by auto
    then have "B n \<le> P * 2^(2 * k * (r+1))"
      using Main[of n "r+1"] by auto
    also have "... = (P * 2^(2 * k)) * ((2^r)^(2*k))"
      by (simp add: power_add power_mult[symmetric])
    also have "... \<le> (P * 2^(2 * k)) * n^(2 * k)"
      apply (rule mult_left_mono) using I \<open>P > 0\<close> by (auto simp add: power_mono)
    finally show ?thesis by simp
  qed
  show ?thesis
    apply (rule exI[of _ "P * 2^(2 * k)"], rule exI[of _ "2 * k"])
    using I by auto
qed

end (*of locale locale pmpt_limit*)

end (*of Normalizing_Sequences.thy*)
