(*
  File:    PNT_Consequences.thy
  Author:  Manuel Eberl, TU München

  Some alternative forms and consequences of the Prime Number Theorem,
  including the asymptotics of the divisor function and Euler's totient function.
*)
section \<open>Consequences of the Prime Number Theorem\<close>
theory PNT_Consequences
imports
  Elementary_Prime_Bounds
  Prime_Number_Theorem.Mertens_Theorems
  Prime_Number_Theorem.Prime_Counting_Functions
  Moebius_Mu_Sum
  Lcm_Nat_Upto
  Primorial
  Primes_Omega
begin

text \<open>
  In this section, we will define a locale that assumes the Prime Number Theorem in order to
  explore some of its elementary consequences.
\<close>

(*<*)
unbundle prime_counting_notation
(*>*)

subsection \<open>Statement and alternative forms of the PNT\<close>

(*<*)
(* TODO: copied from afp-devel; delete in AFP 2019 *)
lemma PNT1_imp_PNT1':
  assumes "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)"
  shows   "(\<lambda>x. ln (\<pi> x)) \<sim>[at_top] ln"
proof -
  (* TODO: Tedious Landau sum reasoning *)
  from assms have "((\<lambda>x. \<pi> x / (x / ln x)) \<longlongrightarrow> 1) at_top"
    by (rule asymp_equivD_strong[OF _ eventually_mono[OF eventually_gt_at_top[of 1]]]) auto
  hence "((\<lambda>x. ln (\<pi> x / (x / ln x))) \<longlongrightarrow> ln 1) at_top"
    by (rule tendsto_ln) auto
  also have "?this \<longleftrightarrow> ((\<lambda>x. ln (\<pi> x) - ln x + ln (ln x)) \<longlongrightarrow> 0) at_top"
    by (intro filterlim_cong eventually_mono[OF eventually_gt_at_top[of 2]])
       (auto simp: ln_div field_simps ln_mult \<pi>_pos)
  finally have "(\<lambda>x. ln (\<pi> x) - ln x + ln (ln x)) \<in> o(\<lambda>_. 1)"
    by (intro smalloI_tendsto) auto
  also have "(\<lambda>_::real. 1 :: real) \<in> o(\<lambda>x. ln x)"
    by real_asymp
  finally have "(\<lambda>x. ln (\<pi> x) - ln x + ln (ln x) - ln (ln x)) \<in> o(\<lambda>x. ln x)"
    by (rule sum_in_smallo) real_asymp+
  thus *: "(\<lambda>x. ln (\<pi> x)) \<sim>[at_top] ln"
    by (simp add: asymp_equiv_altdef)
qed

lemma PNT1_imp_PNT2:
  assumes "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)"
  shows   "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x)"
proof -
  have "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x / ln x * ln x)"
    by (intro asymp_equiv_intros assms PNT1_imp_PNT1')
  also have "\<dots> \<sim>[at_top] (\<lambda>x. x)"
    by (intro asymp_equiv_refl_ev eventually_mono[OF eventually_gt_at_top[of 1]])
       (auto simp: field_simps)
  finally show "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x)"
    by simp
qed

lemma PNT2_imp_PNT3:
  assumes "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x)"
  shows   "nth_prime \<sim>[at_top] (\<lambda>n. n * ln n)"
proof -
  have "(\<lambda>n. nth_prime n) \<sim>[at_top] (\<lambda>n. \<pi> (nth_prime n) * ln (\<pi> (nth_prime n)))"
    using assms
    by (rule asymp_equiv_symI [OF asymp_equiv_compose'])
       (auto intro!: filterlim_compose[OF filterlim_real_sequentially nth_prime_at_top])
  also have "\<dots> = (\<lambda>n. real (Suc n) * ln (real (Suc n)))"
    by (simp add: add_ac)
  also have "\<dots> \<sim>[at_top] (\<lambda>n. real n * ln (real n))"
    by real_asymp
  finally show "nth_prime \<sim>[at_top] (\<lambda>n. n * ln n)" .
qed

lemma PNT3_imp_PNT2:
  assumes "nth_prime \<sim>[at_top] (\<lambda>n. n * ln n)"
  shows   "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x)"
proof (rule asymp_equiv_symI, rule asymp_equiv_sandwich_real)
  show "eventually (\<lambda>x. x \<in> {real (nth_prime (nat \<lfloor>\<pi> x\<rfloor> - 1))..real (nth_prime (nat \<lfloor>\<pi> x\<rfloor>))})
          at_top"
    using eventually_ge_at_top[of 2]
  proof eventually_elim
    case (elim x)
    with nth_prime_partition''[of x] show ?case by auto
  qed
next
  have "(\<lambda>x. real (nth_prime (nat \<lfloor>\<pi> x\<rfloor> - 1))) \<sim>[at_top]
           (\<lambda>x. real (nat \<lfloor>\<pi> x\<rfloor> - 1) * ln (real (nat \<lfloor>\<pi> x\<rfloor> - 1)))"
    by (rule asymp_equiv_compose'[OF _ \<pi>_at_top], rule asymp_equiv_compose'[OF assms]) real_asymp
  also have "\<dots> \<sim>[at_top] (\<lambda>x. \<pi> x * ln (\<pi> x))"
    by (rule asymp_equiv_compose'[OF _ \<pi>_at_top]) real_asymp
  finally show "(\<lambda>x. real (nth_prime (nat \<lfloor>\<pi> x\<rfloor> - 1))) \<sim>[at_top] (\<lambda>x. \<pi> x * ln (\<pi> x))" .
next
  have "(\<lambda>x. real (nth_prime (nat \<lfloor>\<pi> x\<rfloor>))) \<sim>[at_top]
           (\<lambda>x. real (nat \<lfloor>\<pi> x\<rfloor>) * ln (real (nat \<lfloor>\<pi> x\<rfloor>)))"
    by (rule asymp_equiv_compose'[OF _ \<pi>_at_top], rule asymp_equiv_compose'[OF assms]) real_asymp
  also have "\<dots> \<sim>[at_top] (\<lambda>x. \<pi> x * ln (\<pi> x))"
    by (rule asymp_equiv_compose'[OF _ \<pi>_at_top]) real_asymp
  finally show "(\<lambda>x. real (nth_prime (nat \<lfloor>\<pi> x\<rfloor>))) \<sim>[at_top] (\<lambda>x. \<pi> x * ln (\<pi> x))" .
qed

lemma PNT2_imp_PNT1:
  assumes "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x)"
  shows   "(\<lambda>x. ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. ln x)"
    and   "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)"
proof -
   have ev: "eventually (\<lambda>x. \<pi> x > 0) at_top"
            "eventually (\<lambda>x. ln (\<pi> x) > 0) at_top"
            "eventually (\<lambda>x. ln (ln (\<pi> x)) > 0) at_top"
    by (rule eventually_compose_filterlim[OF _ \<pi>_at_top], real_asymp)+

  from assms have "((\<lambda>x. \<pi> x * ln (\<pi> x) / x) \<longlongrightarrow> 1) at_top"
    by (rule asymp_equivD_strong[OF _ eventually_mono[OF eventually_gt_at_top[of 1]]]) auto
  hence "((\<lambda>x. ln (\<pi> x * ln (\<pi> x) / x)) \<longlongrightarrow> ln 1) at_top"
    by (rule tendsto_ln) auto
  moreover have "eventually (\<lambda>x. ln (\<pi> x * ln (\<pi> x) / x) =
                   ln (\<pi> x) * (1 + ln (ln (\<pi> x)) / ln (\<pi> x) - ln x / ln (\<pi> x))) at_top"
      (is "eventually (\<lambda>x. _ = _ * ?f x) _")
    using eventually_gt_at_top[of 0] ev
    by eventually_elim (simp add: field_simps ln_mult ln_div)
  ultimately have "((\<lambda>x. ln (\<pi> x) * ?f x) \<longlongrightarrow> ln 1) at_top"
    by (rule Lim_transform_eventually)

  moreover have "((\<lambda>x. 1 / ln (\<pi> x)) \<longlongrightarrow> 0) at_top"
    by (rule filterlim_compose[OF _ \<pi>_at_top]) real_asymp
  ultimately have "((\<lambda>x. ln (\<pi> x) * ?f x * (1 / ln (\<pi> x))) \<longlongrightarrow> ln 1 * 0) at_top"
    by (rule tendsto_mult)
  moreover have "eventually (\<lambda>x. ln (\<pi> x) * ?f x * (1 / ln (\<pi> x)) = ?f x) at_top"
    using ev by eventually_elim auto
  ultimately have "(?f \<longlongrightarrow> ln 1 * 0) at_top"
    by (rule Lim_transform_eventually)
  hence "((\<lambda>x. 1 + ln (ln (\<pi> x)) / ln (\<pi> x) - ?f x) \<longlongrightarrow> 1 + 0 - ln 1 * 0) at_top"
    by (intro tendsto_intros filterlim_compose[OF _ \<pi>_at_top]) (real_asymp | simp)+
  hence "((\<lambda>x. ln x / ln (\<pi> x)) \<longlongrightarrow> 1) at_top"
    by simp
  thus *: "(\<lambda>x. ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. ln x)"
    by (rule asymp_equiv_symI[OF asymp_equivI'])

  have "eventually (\<lambda>x. \<pi> x = \<pi> x * ln (\<pi> x) / ln (\<pi> x)) at_top"
    using ev by eventually_elim auto
  hence "\<pi> \<sim>[at_top] (\<lambda>x. \<pi> x * ln (\<pi> x) / ln (\<pi> x))"
    by (rule asymp_equiv_refl_ev)
  also from assms and * have "(\<lambda>x. \<pi> x * ln (\<pi> x) / ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x / ln x)"
    by (rule asymp_equiv_intros)
  finally show "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)" .
qed

lemma PNT4_imp_PNT5:
  assumes "\<theta> \<sim>[at_top] (\<lambda>x. x)"
  shows   "\<psi> \<sim>[at_top] (\<lambda>x. x)"
proof -
  define r where "r = (\<lambda>x. \<psi> x - \<theta> x)"
  have "r \<in> O(\<lambda>x. ln x * sqrt x)"
    unfolding r_def by (fact \<psi>_minus_\<theta>_bigo)
  also have "(\<lambda>x::real. ln x * sqrt x) \<in> o(\<lambda>x. x)"
    by real_asymp
  finally have r: "r \<in> o(\<lambda>x. x)" .

  have "(\<lambda>x. \<theta> x + r x) \<sim>[at_top] (\<lambda>x. x)"
    using assms r by (subst asymp_equiv_add_right) auto
  thus ?thesis by (simp add: r_def)
qed

lemma PNT4_imp_PNT1:
  assumes "\<theta> \<sim>[at_top] (\<lambda>x. x)"
  shows   "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)"
proof -
  have "(\<lambda>x. (\<pi> x - \<theta> x / ln x) + ((\<theta> x - x) / ln x)) \<in> o(\<lambda>x. x / ln x)"
  proof (rule sum_in_smallo)
    have "(\<lambda>x. \<pi> x - \<theta> x / ln x) \<in> O(\<lambda>x. x / ln x ^ 2)"
      by (rule \<pi>_\<theta>_bigo)
    also have "(\<lambda>x. x / ln x ^ 2) \<in> o(\<lambda>x. x / ln x :: real)"
      by real_asymp
    finally show "(\<lambda>x. \<pi> x - \<theta> x / ln x) \<in> o(\<lambda>x. x / ln x)" .
  next
    have "eventually (\<lambda>x::real. ln x > 0) at_top" by real_asymp
    hence "eventually (\<lambda>x::real. ln x \<noteq> 0) at_top" by eventually_elim auto
    thus "(\<lambda>x. (\<theta> x - x) / ln x) \<in> o(\<lambda>x. x / ln x)"
      by (intro landau_o.small.divide_right asymp_equiv_imp_diff_smallo assms)
  qed
  thus ?thesis by (simp add: diff_divide_distrib asymp_equiv_altdef)
qed

lemma PNT1_imp_PNT4:
  assumes "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)"
  shows   "\<theta> \<sim>[at_top] (\<lambda>x. x)"
proof -
  have "\<theta> \<sim>[at_top] (\<lambda>x. \<pi> x * ln x)"
  proof (rule smallo_imp_asymp_equiv)
    have "(\<lambda>x. \<theta> x - \<pi> x * ln x) \<in> \<Theta>(\<lambda>x. - ((\<pi> x - \<theta> x / ln x) * ln x))"
      by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 1]])
         (auto simp: field_simps)
    also have "(\<lambda>x. - ((\<pi> x - \<theta> x / ln x) * ln x)) \<in> O(\<lambda>x. x / (ln x)\<^sup>2 * ln x)"
      unfolding landau_o.big.uminus_in_iff by (intro landau_o.big.mult_right \<pi>_\<theta>_bigo)
    also have "(\<lambda>x::real. x / (ln x)\<^sup>2 * ln x) \<in> o(\<lambda>x. x / ln x * ln x)"
      by real_asymp
    also have "(\<lambda>x. x / ln x * ln x) \<in> \<Theta>(\<lambda>x. \<pi> x * ln x)"
      by (intro asymp_equiv_imp_bigtheta asymp_equiv_intros asymp_equiv_symI[OF assms])
    finally show "(\<lambda>x. \<theta> x - \<pi> x * ln x) \<in> o(\<lambda>x. \<pi> x * ln x)" .
  qed
  also have "\<dots> \<sim>[at_top] (\<lambda>x. x / ln x * ln x)"
    by (intro asymp_equiv_intros assms)
  also have "\<dots> \<sim>[at_top] (\<lambda>x. x)"
    by real_asymp
  finally show ?thesis .
qed

lemma PNT5_imp_PNT4:
  assumes "\<psi> \<sim>[at_top] (\<lambda>x. x)"
  shows   "\<theta> \<sim>[at_top] (\<lambda>x. x)"
proof -
  define r where "r = (\<lambda>x. \<theta> x - \<psi> x)"
  have "(\<lambda>x. \<psi> x - \<theta> x) \<in> O(\<lambda>x. ln x * sqrt x)"
    by (fact \<psi>_minus_\<theta>_bigo)
  also have "(\<lambda>x. \<psi> x - \<theta> x) = (\<lambda>x. -r x)"
    by (simp add: r_def)
  finally have "r \<in> O(\<lambda>x. ln x * sqrt x)"
    by simp
  also have "(\<lambda>x::real. ln x * sqrt x) \<in> o(\<lambda>x. x)"
    by real_asymp
  finally have r: "r \<in> o(\<lambda>x. x)" .

  have "(\<lambda>x. \<psi> x + r x) \<sim>[at_top] (\<lambda>x. x)"
    using assms r by (subst asymp_equiv_add_right) auto
  thus ?thesis by (simp add: r_def)
qed
(* END TODO *)
(*>*)

locale prime_number_theorem =
  assumes prime_number_theorem [asymp_equiv_intros]: "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)"
begin

corollary \<theta>_asymptotics [asymp_equiv_intros]: "\<theta> \<sim>[at_top] (\<lambda>x. x)"
  using prime_number_theorem by (rule PNT1_imp_PNT4)

corollary \<psi>_asymptotics [asymp_equiv_intros]: "\<psi> \<sim>[at_top] (\<lambda>x. x)"
  using \<theta>_asymptotics PNT4_imp_PNT5 by simp
  
corollary ln_\<pi>_asymptotics [asymp_equiv_intros]: "(\<lambda>x. ln (\<pi> x)) \<sim>[at_top] ln"
  using prime_number_theorem PNT1_imp_PNT1' by simp

corollary \<pi>_ln_\<pi>_asymptotics: "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x)"
  using prime_number_theorem PNT1_imp_PNT2 by simp

corollary nth_prime_asymptotics [asymp_equiv_intros]:
  "(\<lambda>n. real (nth_prime n)) \<sim>[at_top] (\<lambda>n. real n * ln (real n))"
  using \<pi>_ln_\<pi>_asymptotics PNT2_imp_PNT3 by simp

corollary moebius_mu_smallo: "sum_upto moebius_mu \<in> o(\<lambda>x. x)"
  using PNT_implies_sum_moebius_mu_sublinear \<psi>_asymptotics by simp

lemma ln_\<theta>_asymptotics:
  includes prime_counting_notation
  shows "(\<lambda>x. ln (\<theta> x) - ln x) \<in> o(\<lambda>_. 1)"
proof -
  have [simp]: "\<theta> 2 = ln 2"
    by (simp add: eval_\<theta>)
  have \<theta>_pos: "\<theta> x > 0" if "x \<ge> 2" for x
  proof -
    have "0 < ln (2 :: real)" by simp
    also have "\<dots> \<le> \<theta> x"
      using \<theta>_mono[OF that] by simp
    finally show ?thesis .
  qed

  have nz: "eventually (\<lambda>x. \<theta> x \<noteq> 0 \<or> x \<noteq> 0) at_top"
    using eventually_gt_at_top[of 0] by eventually_elim auto
  have "filterlim (\<lambda>x. \<theta> x / x) (nhds 1) at_top"
    using asymp_equivD_strong[OF \<theta>_asymptotics nz] .
  hence "filterlim (\<lambda>x. ln (\<theta> x / x)) (nhds (ln 1)) at_top"
    by (rule tendsto_ln) auto
  also have "?this \<longleftrightarrow> filterlim (\<lambda>x. ln (\<theta> x) - ln x) (nhds 0) at_top"
    by (intro filterlim_cong eventually_mono[OF eventually_ge_at_top[of 2]])
       (auto simp: ln_div \<theta>_pos)
  finally show "(\<lambda>x. ln (\<theta> x) - ln x) \<in> o(\<lambda>x. 1)"
    by (intro smalloI_tendsto) auto
qed

lemma ln_\<theta>_asymp_equiv [asymp_equiv_intros]:
  includes prime_counting_notation
  shows "(\<lambda>x. ln (\<theta> x)) \<sim>[at_top] ln"
proof (rule smallo_imp_asymp_equiv)
  have "(\<lambda>x. ln (\<theta> x) - ln x) \<in> o(\<lambda>_. 1)" by (rule ln_\<theta>_asymptotics)
  also have "(\<lambda>_. 1) \<in> O(\<lambda>x::real. ln x)" by real_asymp
  finally show "(\<lambda>x. ln (\<theta> x) - ln x) \<in> o(ln)" .
qed

lemma ln_nth_prime_asymptotics:
  "(\<lambda>n. ln (nth_prime n) - (ln n + ln (ln n))) \<in> o(\<lambda>_. 1)"
proof -
  have "filterlim (\<lambda>n. ln (nth_prime n / (n * ln n))) (nhds (ln 1)) at_top"
    by (intro tendsto_ln asymp_equivD_strong[OF nth_prime_asymptotics])
       (auto intro!: eventually_mono[OF eventually_gt_at_top[of 1]])
  also have "?this \<longleftrightarrow> filterlim (\<lambda>n. ln (nth_prime n) - (ln n + ln (ln n))) (nhds 0) at_top"
    using prime_gt_0_nat[OF prime_nth_prime]
    by (intro filterlim_cong refl eventually_mono[OF eventually_gt_at_top[of 1]])
       (auto simp: field_simps ln_mult ln_div)
  finally show ?thesis by (intro smalloI_tendsto) auto
qed

lemma ln_nth_prime_asymp_equiv [asymp_equiv_intros]:
  "(\<lambda>n. ln (nth_prime n)) \<sim>[at_top] ln"
proof -
  have "(\<lambda>n. ln (nth_prime n) - (ln n + ln (ln n))) \<in> o(ln)"
    using ln_nth_prime_asymptotics by (rule landau_o.small.trans) real_asymp
  hence "(\<lambda>n. ln (nth_prime n) - (ln n + ln (ln n)) + ln (ln n)) \<in> o(ln)"
    by (rule sum_in_smallo) real_asymp
  thus ?thesis by (intro smallo_imp_asymp_equiv) auto
qed


text \<open>
  The following versions use a little less notation.
\<close>
corollary prime_number_theorem': "((\<lambda>x. \<pi> x / (x / ln x)) \<longlongrightarrow> 1) at_top"
  using prime_number_theorem
  by (rule asymp_equivD_strong[OF _ eventually_mono[OF eventually_gt_at_top[of 1]]]) auto

corollary prime_number_theorem'':
  "(\<lambda>x. card {p. prime p \<and> real p \<le> x}) \<sim>[at_top] (\<lambda>x. x / ln x)"
proof -
  have "\<pi> = (\<lambda>x. card {p. prime p \<and> real p \<le> x})"
    by (intro ext) (simp add: \<pi>_def prime_sum_upto_def)
  with prime_number_theorem show ?thesis by simp
qed

corollary prime_number_theorem''':
  "(\<lambda>n. card {p. prime p \<and> p \<le> n}) \<sim>[at_top] (\<lambda>n. real n / ln (real n))"
proof -
  have "(\<lambda>n. card {p. prime p \<and> real p \<le> real n}) \<sim>[at_top] (\<lambda>n. real n / ln (real n))"
    using prime_number_theorem''
    by (rule asymp_equiv_compose') (simp add: filterlim_real_sequentially)
  thus ?thesis by simp
qed

end


subsection \<open>Existence of primes in intervals\<close>

text \<open>
  For fixed \<open>\<epsilon>\<close>, The interval $(x; \varepsilon x]$ contains a prime number for any sufficiently
  large \<open>x\<close>. This proof was taken from A.\,J. Hildebrand's lecture notes~\cite{hildebrand_ant}.
\<close>
lemma (in prime_number_theorem) prime_in_interval_exists:
  fixes c :: real
  assumes "c > 1"
  shows   "eventually (\<lambda>x. \<exists>p. prime p \<and> real p \<in> {x<..c*x}) at_top"
proof -
  from \<open>c > 1\<close> have "(\<lambda>x. \<pi> (c * x) / \<pi> x) \<sim>[at_top] (\<lambda>x. ((c * x) / ln (c * x)) / (x / ln x))"
    by (intro asymp_equiv_intros asymp_equiv_compose'[OF prime_number_theorem]) real_asymp+
  also have "\<dots> \<sim>[at_top] (\<lambda>x. c)"
    using \<open>c > 1\<close> by real_asymp
  finally have "(\<lambda>x. \<pi> (c * x) / \<pi> x) \<sim>[at_top] (\<lambda>a. c)" by simp
  hence "((\<lambda>x. \<pi> (c * x) / \<pi> x) \<longlongrightarrow> c) at_top"
    by (rule asymp_equivD_const)
  from this and \<open>c > 1\<close> have "eventually (\<lambda>x. \<pi> (c * x) / \<pi> x > 1) at_top"
    by (rule order_tendstoD)
  moreover have "eventually (\<lambda>x. \<pi> x > 0) at_top"
    using \<pi>_at_top by (auto simp: filterlim_at_top_dense)
  ultimately show ?thesis using eventually_gt_at_top[of 1]
  proof eventually_elim
    case (elim x)
    define P where "P = {p. prime p \<and> real p \<in> {x<..c*x}}"
    from elim and \<open>c > 1\<close> have "1 * x < c * x" by (intro mult_strict_right_mono) auto
    hence "x < c * x" by simp
    have "P = {p. prime p \<and> real p \<le> c * x} - {p. prime p \<and> real p \<le> x}"
      by (auto simp: P_def)
    also have "card \<dots> = card {p. prime p \<and> real p \<le> c * x} - card {p. prime p \<and> real p \<le> x}"
      using \<open>x < c * x\<close> by (subst card_Diff_subset) (auto intro: finite_primes_le)
    also have "real \<dots> = \<pi> (c * x) - \<pi> x"
      using \<pi>_mono[of x "c * x"] \<open>x < c * x\<close>
      by (subst of_nat_diff) (auto simp: primes_pi_def prime_sum_upto_def)
    finally have "real (card P) = \<pi> (c * x) - \<pi> x" by simp
    moreover have "\<pi> (c * x) - \<pi> x > 0"
      using elim by (auto simp: field_simps)
    ultimately have "real (card P) > 0" by linarith
    hence "card P > 0" by simp
    hence "P \<noteq> {}" by (intro notI) simp
    thus ?case by (auto simp: P_def)
  qed
qed

text \<open>
  The set of rationals whose numerator and denominator are primes is
  dense in $\mathbb{R}_{{}>0}$.
\<close>
lemma (in prime_number_theorem) prime_fractions_dense:
  fixes \<alpha> \<epsilon> :: real
  assumes "\<alpha> > 0" and "\<epsilon> > 0"
  obtains p q :: nat where "prime p" and "prime q" and "dist (real p / real q) \<alpha> < \<epsilon>"
proof -
  define \<epsilon>' where "\<epsilon>' = \<epsilon> / 2"
  from assms have "\<epsilon>' > 0" by (simp add: \<epsilon>'_def)
  have "eventually (\<lambda>x. \<exists>p. prime p \<and> real p \<in> {x<..(1 + \<epsilon>' / \<alpha>) * x}) at_top"
    using assms \<open>\<epsilon>' > 0\<close> by (intro prime_in_interval_exists) (auto simp: field_simps)
  then obtain x0 where x0: "\<And>x. x \<ge> x0 \<Longrightarrow> \<exists>p. prime p \<and> real p \<in> {x<..(1 + \<epsilon>' / \<alpha>) * x}"
    by (auto simp: eventually_at_top_linorder)

  have "\<exists>q. prime q \<and> q > nat \<lfloor>x0 / \<alpha>\<rfloor>" by (rule bigger_prime)
  then obtain q where "prime q" "q > nat \<lfloor>x0 / \<alpha>\<rfloor>" by blast
  hence "real q \<ge> x0 / \<alpha>" by linarith
  with \<open>\<alpha> > 0\<close> have "\<alpha> * real q \<ge> x0" by (simp add: field_simps)
  hence "\<exists>p. prime p \<and> real p \<in> {\<alpha> * real q<..(1 + \<epsilon>' / \<alpha>) * (\<alpha> * real q)}"
    by (intro x0)
  then obtain p where p: "prime p" "real p > \<alpha> * real q" "real p \<le> (1 + \<epsilon>' / \<alpha>) * (\<alpha> * real q)"
    using assms by auto

  from p \<open>prime q\<close> have "real p / real q \<le> (1 + \<epsilon>' / \<alpha>) * \<alpha>"
    using assms by (auto simp: field_simps dest: prime_gt_0_nat)
  also have "\<dots> = \<alpha> + \<epsilon>'"
    using assms by (simp add: field_simps)
  finally have "real p / real q \<le> \<alpha> + \<epsilon>'" .
  moreover from p \<open>prime q\<close> have "real p / real q > \<alpha>" "real p / real q \<le> (1 + \<epsilon>' / \<alpha>) * \<alpha>"
    using assms by (auto simp: field_simps dest: prime_gt_0_nat)
  ultimately have "dist (real p / real q) \<alpha> \<le> \<epsilon>'"
    by (simp add: dist_norm)
  also have "\<dots> < \<epsilon>"
    using \<open>\<epsilon> > 0\<close> by (simp add: \<epsilon>'_def)
  finally show ?thesis using \<open>prime p\<close> \<open>prime q\<close> that[of p q] by blast
qed


subsection \<open>The logarithm of the primorial\<close>

text \<open>
  The PNT directly implies the asymptotics of the logarithm of the primorial function:
\<close>

context prime_number_theorem
begin

lemma ln_primorial_asymp_equiv [asymp_equiv_intros]:
  "(\<lambda>x. ln (primorial x)) \<sim>[at_top] (\<lambda>x. x)"
  by (auto simp: ln_primorial \<theta>_asymptotics)

lemma ln_ln_primorial_asymp_equiv [asymp_equiv_intros]:
  "(\<lambda>x. ln (ln (primorial x))) \<sim>[at_top] (\<lambda>x. ln x)"
  by (auto simp: ln_primorial ln_\<theta>_asymp_equiv)

lemma ln_primorial'_asymp_equiv [asymp_equiv_intros]:
        "(\<lambda>k. ln (primorial' k)) \<sim>[at_top] (\<lambda>k. k * ln k)"
  and ln_ln_primorial'_asymp_equiv [asymp_equiv_intros]:
        "(\<lambda>k. ln (ln (primorial' k))) \<sim>[at_top] (\<lambda>k. ln k)"
  and ln_over_ln_ln_primorial'_asymp_equiv:
        "(\<lambda>k. ln (primorial' k) / ln (ln (primorial' k))) \<sim>[at_top] (\<lambda>k. k)"
proof -
  have lim1: "filterlim (\<lambda>k. real (nth_prime (k - 1))) at_top at_top"
    by (rule filterlim_compose[OF filterlim_real_sequentially]
             filterlim_compose[OF nth_prime_at_top])+ real_asymp
  have lim2: "filterlim (\<lambda>k::nat. k - 1) at_top at_top"
    by real_asymp

  have "(\<lambda>k. ln (primorial' k)) \<sim>[at_top] (\<lambda>n. ln (primorial (nth_prime (n - 1))))"
    by (intro asymp_equiv_refl_ev eventually_mono[OF eventually_gt_at_top[of 0]])
       (auto simp: primorial'_conv_primorial)
  also have "\<dots> \<sim>[at_top] (\<lambda>n. nth_prime (n - 1))"
    by (intro asymp_equiv_compose'[OF _ lim1] asymp_equiv_intros)
  also have "\<dots> \<sim>[at_top] (\<lambda>n. real (n - 1) * ln (real (n - 1)))"
    by (intro asymp_equiv_compose'[OF _ lim2] asymp_equiv_intros)
  also have "\<dots> \<sim>[at_top] (\<lambda>n. n * ln n)" by real_asymp
  finally show 1: "(\<lambda>k. ln (primorial' k)) \<sim>[at_top] (\<lambda>k. k * ln k)" .

  have "(\<lambda>k. ln (ln (primorial' k))) \<sim>[at_top] (\<lambda>n. ln (ln (primorial (nth_prime (n - 1)))))"
    by (intro asymp_equiv_refl_ev eventually_mono[OF eventually_gt_at_top[of 0]])
       (auto simp: primorial'_conv_primorial)
  also have "\<dots> \<sim>[at_top] (\<lambda>n. ln (nth_prime (n - 1)))"
    by (intro asymp_equiv_compose'[OF _ lim1] asymp_equiv_intros)
  also have "\<dots> \<sim>[at_top] (\<lambda>n. ln (real (n - 1)))"
    by (intro asymp_equiv_compose'[OF _ lim2] asymp_equiv_intros)
  also have "\<dots> \<sim>[at_top] (\<lambda>n. ln n)" by real_asymp
  finally show 2: "(\<lambda>k. ln (ln (primorial' k))) \<sim>[at_top] (\<lambda>k. ln k)" .
    
  have "(\<lambda>k. ln (primorial' k) / ln (ln (primorial' k))) \<sim>[at_top] (\<lambda>k. (k * ln k) / ln k)"
    by (intro asymp_equiv_intros 1 2)
  also have "\<dots> \<sim>[at_top] (\<lambda>k. k)" by real_asymp
  finally show "(\<lambda>k. ln (primorial' k) / ln (ln (primorial' k))) \<sim>[at_top] (\<lambda>k. k)" .
qed

end


subsection \<open>Consequences of the asymptotics of \<open>\<psi>\<close> and \<open>\<theta>\<close>\<close>

text \<open>
  Next, we will show some consequences of $\psi(x)\sim x$ and $\vartheta(x)\sim x$. To this
  end, we first show generically that any function $g = e^{x + o(x)}$ is $o(c^n)$ if $c > e$ and
  $\omega(c^n)$ if $c < e$.
\<close>
locale exp_asymp_equiv_linear =
  fixes f g :: "real \<Rightarrow> real"
  assumes f_asymp_equiv: "f \<sim>[at_top] (\<lambda>x. x)"
  assumes g: "eventually (\<lambda>x. g x = exp (f x)) F"
begin

lemma
  fixes \<epsilon> :: real assumes "\<epsilon> > 0"
  shows smallo:     "g \<in> o(\<lambda>x. exp ((1 + \<epsilon>) * x))"
    and smallomega: "g \<in> \<omega>(\<lambda>x. exp ((1 - \<epsilon>) * x))"
proof -
  have "(\<lambda>x. exp (f x) / exp ((1 + \<epsilon>) * x)) \<in> \<Theta>(\<lambda>x. exp (((f x - x) / x - \<epsilon>) * x))"
    by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 1]])
       (simp_all add: divide_simps ring_distribs flip: exp_add exp_diff)
  also have "((\<lambda>x. exp (((f x - x) / x - \<epsilon>) * x)) \<longlongrightarrow> 0) at_top"
  proof (intro filterlim_compose[OF exp_at_bot] filterlim_tendsto_neg_mult_at_bot)
    have smallo: "(\<lambda>x. f x - x) \<in> o(\<lambda>x. x)"
      using f_asymp_equiv by (rule asymp_equiv_imp_diff_smallo)
    show "((\<lambda>x. (f x - x) / x - \<epsilon>) \<longlongrightarrow> 0 - \<epsilon>) at_top"
      by (intro tendsto_diff smalloD_tendsto[OF smallo] tendsto_const)
  qed (use \<open>\<epsilon> > 0\<close> in \<open>auto simp: filterlim_ident\<close>)
  hence "(\<lambda>x. exp (((f x - x) / x - \<epsilon>) * x)) \<in> o(\<lambda>_. 1)"
    by (intro smalloI_tendsto) auto
  finally have "(\<lambda>x. exp (f x)) \<in> o(\<lambda>x. exp ((1 + \<epsilon>) * x))"
    by (simp add: landau_divide_simps)
  also have "?this \<longleftrightarrow> g \<in> o(\<lambda>x. exp ((1 + \<epsilon>) * x))"
    using g by (intro landau_o.small.in_cong) (simp add: eq_commute)
  finally show "g \<in> o(\<lambda>x. exp ((1 + \<epsilon>) * x))" .
next
  have "(\<lambda>x. exp (f x) / exp ((1 - \<epsilon>) * x)) \<in> \<Theta>(\<lambda>x. exp (((f x - x) / x + \<epsilon>) * x))"
    by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 1]])
       (simp add: ring_distribs flip: exp_add exp_diff)
  also have "filterlim (\<lambda>x. exp (((f x - x) / x + \<epsilon>) * x)) at_top at_top"
  proof (intro filterlim_compose[OF exp_at_top] filterlim_tendsto_pos_mult_at_top)
    have smallo: "(\<lambda>x. f x - x) \<in> o(\<lambda>x. x)"
      using f_asymp_equiv by (rule asymp_equiv_imp_diff_smallo)
    show "((\<lambda>x. (f x - x) / x + \<epsilon>) \<longlongrightarrow> 0 + \<epsilon>) at_top"
      by (intro tendsto_add smalloD_tendsto[OF smallo] tendsto_const)
  qed (use \<open>\<epsilon> > 0\<close> in \<open>auto simp: filterlim_ident\<close>)
  hence "(\<lambda>x. exp (((f x - x) / x + \<epsilon>) * x)) \<in> \<omega>(\<lambda>_. 1)"
    by (simp add: filterlim_at_top_iff_smallomega)
  finally have "(\<lambda>x. exp (f x)) \<in> \<omega>(\<lambda>x. exp ((1 - \<epsilon>) * x))"
    by (simp add: landau_divide_simps)
  also have "?this \<longleftrightarrow> g \<in> \<omega>(\<lambda>x. exp ((1 - \<epsilon>) * x))"
    using g by (intro landau_omega.small.in_cong) (simp add: eq_commute)
  finally show "g \<in> \<omega>(\<lambda>x. exp ((1 - \<epsilon>) * x))" .
qed

lemma smallo':
  fixes c :: real assumes "c > exp 1"
  shows "g \<in> o(\<lambda>x. c powr x)"
proof -
  have "c > 0" by (rule le_less_trans[OF _ assms]) auto
  from \<open>c > 0\<close> assms have "exp 1 < exp (ln c)"
    by (subst exp_ln) auto
  hence "ln c > 1" by (subst (asm) exp_less_cancel_iff)
  hence "g \<in> o(\<lambda>x. exp ((1 + (ln c - 1)) * x))"
    using assms by (intro smallo) auto
  also have "(\<lambda>x. exp ((1 + (ln c - 1)) * x)) = (\<lambda>x. c powr x)"
    using \<open>c > 0\<close> by (simp add: powr_def mult_ac)
  finally show ?thesis .
qed

lemma smallomega':
  fixes c :: real assumes "c \<in> {0<..<exp 1}"
  shows "g \<in> \<omega>(\<lambda>x. c powr x)"
proof -
  from assms have "exp 1 > exp (ln c)"
    by (subst exp_ln) auto
  hence "ln c < 1" by (subst (asm) exp_less_cancel_iff)
  hence "g \<in> \<omega>(\<lambda>x. exp ((1 - (1 - ln c)) * x))"
    using assms by (intro smallomega) auto
  also have "(\<lambda>x. exp ((1 - (1 - ln c)) * x)) = (\<lambda>x. c powr x)"
    using assms by (simp add: powr_def mult_ac)
  finally show ?thesis .
qed

end


text \<open>
  The primorial fulfils $x\# = e^{\vartheta(x)}$ and is therefore one example of this.
\<close>

context prime_number_theorem
begin

sublocale primorial: exp_asymp_equiv_linear \<theta> "\<lambda>x. real (primorial x)"
  using \<theta>_asymptotics by unfold_locales (simp_all add: ln_primorial [symmetric])

end


text \<open>
  The LCM of the first \<open>n\<close> natural numbers is equal to $e^{\psi(n)}$ and is
  therefore another example.
\<close>

context prime_number_theorem
begin

sublocale Lcm_upto: exp_asymp_equiv_linear \<psi> "\<lambda>x. real (Lcm {1..nat \<lfloor>x\<rfloor>})"
  using \<psi>_asymptotics by unfold_locales (simp_all flip: Lcm_upto_real_conv_\<psi>)

end


subsection \<open>Bounds on the prime \<open>\<omega>\<close> function\<close>

text \<open>
  Next, we will examine the asymptotic behaviour of the prime \<open>\<omega>\<close> function $\omega(n)$,
  i.\,e.\ the number of distinct prime factors of \<open>n\<close>. These proofs are again taken from
  A.\,J. Hildebrand's lecture notes~\cite{hildebrand_ant}.
\<close>

lemma ln_gt_1:
  assumes "x > (3 :: real)"
  shows   "ln x > 1"
proof -
  have "x > exp 1"
    using exp_le assms by linarith
  hence "ln x > ln (exp 1)" using assms by (subst ln_less_cancel_iff) auto
  thus ?thesis by simp
qed

lemma (in prime_number_theorem) primes_omega_primorial'_asymp_equiv:
  "(\<lambda>k. primes_omega (primorial' k)) \<sim>[at_top]
     (\<lambda>k. ln (primorial' k) / ln (ln (primorial' k)))"
  using ln_over_ln_ln_primorial'_asymp_equiv by (simp add: asymp_equiv_sym)

text \<open>
  The number of distinct prime factors of \<open>n\<close> has maximal order $\ln n / \ln\ln n$:
\<close>
theorem (in prime_number_theorem)
  limsup_primes_omega: "limsup (\<lambda>n. primes_omega n / (ln n / ln (ln n))) = 1"
proof (intro antisym)
  have "(\<lambda>k. primes_omega (primorial' k) / (ln (primorial' k) / ln (ln (primorial' k)))) \<longlonglongrightarrow> 1"
    using primes_omega_primorial'_asymp_equiv
    by (intro asymp_equivD_strong eventually_mono[OF eventually_gt_at_top[of 1]]) auto
  hence "limsup ((\<lambda>n. primes_omega n / (ln n / ln (ln n))) \<circ> primorial') = ereal 1"
    by (intro lim_imp_Limsup tendsto_ereal) simp_all
  hence "1 = limsup ((\<lambda>n. ereal (primes_omega n / (ln n / ln (ln n)))) \<circ> primorial')"
    by (simp add: o_def)
  also have "\<dots> \<le> limsup (\<lambda>n. primes_omega n / (ln n / ln (ln n)))"
    using strict_mono_primorial' by (rule limsup_subseq_mono)
  finally show "limsup (\<lambda>n. primes_omega n / (ln n / ln (ln n))) \<ge> 1" .
next
  show "limsup (\<lambda>n. primes_omega n / (ln n / ln (ln n))) \<le> 1"
    unfolding Limsup_le_iff
  proof safe
    fix C' :: ereal assume C': "C' > 1"
    from ereal_dense2[OF this] obtain C where C: "C > 1" "ereal C < C'" by auto

    have "(\<lambda>k. primes_omega (primorial' k) / (ln (primorial' k) / ln (ln (primorial' k)))) \<longlonglongrightarrow> 1"
      (is "filterlim ?f _ _") using primes_omega_primorial'_asymp_equiv
      by (intro asymp_equivD_strong eventually_mono[OF eventually_gt_at_top[of 1]]) auto
    from order_tendstoD(2)[OF this C(1)]
    have "eventually (\<lambda>k. ?f k < C) at_top" .
    then obtain k0 where k0: "\<And>k. k \<ge> k0 \<Longrightarrow> ?f k < C" by (auto simp: eventually_at_top_linorder) 
    
    have "eventually (\<lambda>n::nat. max 3 k0 / (ln n / ln (ln n)) < C) at_top"
      using \<open>C > 1\<close> by real_asymp
    hence "eventually (\<lambda>n. primes_omega n / (ln n / ln (ln n)) \<le> C) at_top"
      using eventually_gt_at_top[of "primorial' (max k0 3)"]
    proof eventually_elim
      case (elim n)
      define k where "k = primes_omega n"
      define m where "m = primorial' k"
      have "primorial' 3 \<le> primorial' (max k0 3)"
        by (subst strict_mono_less_eq[OF strict_mono_primorial']) auto
      also have "\<dots> < n" by fact
      finally have "n > 30" by simp

      show ?case
      proof (cases "k \<ge> max 3 k0")
        case True
        hence "m \<ge> 30"
          using strict_mono_less_eq[OF strict_mono_primorial', of 3 k] by (simp add: m_def k_def)
        have "exp 1 ^ 3 \<le> (3 ^ 3 :: real)"
          using exp_le by (intro power_mono) auto
        also have "\<dots> < m" using \<open>m \<ge> 30\<close> by simp
        finally have "ln (exp 1 ^ 3) < ln m"
          using \<open>m \<ge> 30\<close> by (subst ln_less_cancel_iff) auto
        hence "ln m > 3" by (subst (asm) ln_realpow) auto

        have "primorial' (primes_omega n) \<le> n"
          using \<open>n > 30\<close> by (intro primorial'_primes_omega_le) auto
        hence "m \<le> n" unfolding m_def k_def using elim
          by (auto simp: max_def)
        hence "primes_omega n / (ln n / ln (ln n)) \<le> k / (ln m / ln (ln m))"
          unfolding k_def using elim \<open>m \<ge> 30\<close> ln_gt_1[of n] \<open>ln m > 3\<close>
          by (intro frac_le[of "primes_omega n"] divide_ln_mono mult_pos_pos divide_pos_pos) auto
        also have "\<dots> = ?f k"
          by (simp add: k_def m_def)
        also have "\<dots> < C"
          by (intro k0) (use True in \<open>auto simp: k_def\<close>)
        finally show ?thesis by simp
      next
        case False
        hence "primes_omega n / (ln n / ln (ln n)) \<le> max 3 k0 / (ln n / ln (ln n))"
          using elim ln_gt_1[of n] \<open>n > 30\<close>
          by (intro divide_right_mono divide_nonneg_pos) (auto simp: k_def)
        also have "\<dots> < C"
          using elim by simp
        finally show ?thesis by simp
      qed
    qed
    thus "eventually (\<lambda>n. ereal (primes_omega n / (ln n / ln (ln n))) < C') at_top"
      by eventually_elim (rule le_less_trans[OF _ C(2)], auto)
  qed
qed


subsection \<open>Bounds on the divisor function\<close>

text \<open>
  In this section, we shall examine the growth of the divisor function $\sigma_0(n)$.
  In particular, we will show that $\sigma_0(n) < 2^{c\ln n / \ln\ln n}$ for all sufficiently
  large \<open>n\<close> if $c > 1$ and $\sigma_0(n) > 2^{c\ln n / \ln\ln n}$ for infinitely many \<open>n\<close>
  if $c < 1$.

  An equivalent statement is that $\ln(\sigma_0(n))$ has maximal order
  $\ln 2 \cdot \ln n / \ln\ln n$.

  Following Apostol's somewhat didactic approach, we first show a generic bounding lemma for
  $\sigma_0$ that depends on some function \<open>f\<close> that we will specify later.
\<close>
lemma divisor_count_bound_gen:
  fixes f :: "nat \<Rightarrow> real"
  assumes "eventually (\<lambda>n. f n \<ge> 2) at_top"
  defines "c \<equiv> (8 / ln 2 :: real)"
  defines "g \<equiv> (\<lambda>n. (ln n + c * f n * ln (ln n)) / (ln (f n)))"
  shows "eventually (\<lambda>n. divisor_count n < 2 powr g n) at_top"
proof -
  include prime_counting_notation
  have "eventually (\<lambda>n::nat. 1 + log 2 n \<le> ln n ^ 2) at_top"  by real_asymp
  thus "eventually (\<lambda>n. divisor_count n < 2 powr g n) at_top"
    using eventually_gt_at_top[of 2] assms(1)
  proof eventually_elim
    fix n :: nat
    assume n: "n > 2" and "f n \<ge> 2" and "1 + log 2 n \<le> ln n ^ 2"

    define Pr where [simp]: "Pr = prime_factors n"
    define Pr1 where [simp]: "Pr1 = {p\<in>Pr. p < f n}"
    define Pr2 where [simp]: "Pr2 = {p\<in>Pr. p \<ge> f n}"
  
    have "exp 1 < real n"
      using e_less_272 \<open>n > 2\<close> by linarith
    hence "ln (exp 1) < ln (real n)"
      using \<open>n > 2\<close> by (subst ln_less_cancel_iff) auto
    hence "ln (ln n) > ln (ln (exp 1))"
      by (subst ln_less_cancel_iff) auto
    hence "ln (ln n) > 0" by simp
  
    define S2 where "S2 = (\<Sum>p\<in>Pr2. multiplicity p n)"
    have "f n ^ S2 = (\<Prod>p\<in>Pr2. f n ^ multiplicity p n)"
      by (simp add: S2_def power_sum)
    also have "\<dots> \<le> (\<Prod>p\<in>Pr2. real p ^ multiplicity p n)"
      using \<open>f n \<ge> 2\<close> by (intro prod_mono conjI power_mono) auto
    also from \<open>n > 2\<close> have "\<dots> \<le> (\<Prod>p\<in>Pr. real p ^ multiplicity p n)"
      by (intro prod_mono2 one_le_power) (auto simp: in_prime_factors_iff dest: prime_gt_0_nat)
    also have "\<dots> = n"
      using \<open>n > 2\<close> by (subst prime_factorization_nat[of n])  auto
    finally have "f n ^ S2 \<le> n" .
    hence "ln (f n ^ S2) \<le> ln n"
      using n \<open>f n \<ge> 2\<close> by (subst ln_le_cancel_iff) auto
    hence "S2 \<le> ln n / ln (f n)"
      using \<open>f n \<ge> 2\<close> by (simp add: field_simps ln_realpow)
  
    have le_twopow: "Suc a \<le> 2 ^ a" for a :: nat by (induction a) auto
    have "(\<Prod>p\<in>Pr2. Suc (multiplicity p n)) \<le> (\<Prod>p\<in>Pr2. 2 ^ multiplicity p n)"
      by (intro prod_mono conjI le_twopow) auto
    also have "\<dots> = 2 ^ S2"
      by (simp add: S2_def power_sum)
    also have "\<dots> = 2 powr real S2"
      by (subst powr_realpow) auto
    also have "\<dots> \<le> 2 powr (ln n / ln (f n))"
      by (intro powr_mono \<open>S2 \<le> ln n / ln (f n)\<close>) auto
    finally have bound2: "real (\<Prod>p\<in>Pr2. Suc (multiplicity p n)) \<le> 2 powr (ln n / ln (f n))"
      by simp
  
    have multiplicity_le: "multiplicity p n \<le> log 2 n" if p: "p \<in> Pr" for p
    proof -
      from p have "2 ^ multiplicity p n \<le> p ^ multiplicity p n"
        by (intro power_mono) (auto simp: in_prime_factors_iff dest: prime_gt_1_nat)
      also have "\<dots> = (\<Prod>p\<in>{p}. p ^ multiplicity p n)" by simp
      also from p have "(\<Prod>p\<in>{p}. p ^ multiplicity p n) \<le> (\<Prod>p\<in>Pr. p ^ multiplicity p n)"
        by (intro dvd_imp_le prod_dvd_prod_subset)
           (auto simp: in_prime_factors_iff dest: prime_gt_0_nat)
      also have "\<dots> = n"
        using n by (subst prime_factorization_nat[of n]) auto
      finally have "2 ^ multiplicity p n \<le> n" .
      hence "log 2 (2 ^ multiplicity p n) \<le> log 2 n"
        using n by (subst log_le_cancel_iff) auto
      thus "multiplicity p n \<le> log 2 n"
        by (subst (asm) log_nat_power) auto    
    qed
  
    have "(\<Prod>p\<in>Pr1. Suc (multiplicity p n)) = exp (\<Sum>p\<in>Pr1. ln (multiplicity p n + 1))"
      by (simp add: exp_sum)
    also have "(\<Sum>p\<in>Pr1. ln (multiplicity p n + 1)) \<le> (\<Sum>p\<in>Pr1. 2 * ln (ln n))"
    proof (intro sum_mono)
      fix p assume p: "p \<in> Pr1"
      have "ln (multiplicity p n + 1) \<le> ln (1 + log 2 n)"
        using p multiplicity_le[of p] by (subst ln_le_cancel_iff) auto
      also have "\<dots> \<le> ln (ln n ^ 2)"
        using \<open>n > 2\<close> \<open>1 + log 2 n \<le> ln n ^ 2\<close>
        by (subst ln_le_cancel_iff) (auto intro: add_pos_nonneg)
      also have "\<dots> = 2 * ln (ln n)"
        using \<open>n > 2\<close> by (simp add: ln_realpow)
      finally show "ln (multiplicity p n + 1) \<le> 2 * ln (ln n)" .
    qed
    also have "\<dots> = 2 * ln (ln n) * card Pr1"
      by simp
    also have "finite {p. prime p \<and> real p \<le> f n}"
      by (rule finite_subset[of _ "{..nat \<lfloor>f n\<rfloor>}"]) (auto simp: le_nat_iff le_floor_iff)
    hence "card Pr1 \<le> card {p. prime p \<and> real p \<le> f n}"
      by (intro card_mono) auto
    also have "real \<dots> = \<pi> (f n)"
      by (simp add: primes_pi_def prime_sum_upto_def)
    also have "\<dots> < 4 * (f n / ln (f n))"
      using \<open>f n \<ge> 2\<close> by (intro \<pi>_upper_bound'') auto
    also have "exp (2 * ln (ln (real n)) * (4 * (f n / ln (f n)))) =
                 2 powr (c * f n * ln (ln n) / ln (f n))"
      by (simp add: powr_def c_def)
    finally have bound1: "(\<Prod>p\<in>Pr1. Suc (multiplicity p n)) <
                             2 powr (c * f n * ln (ln (real n)) / ln (f n))"
      using \<open>ln (ln n) > 0\<close> by (simp add: mult_strict_left_mono)
  
    
    have "divisor_count n = (\<Prod>p\<in>Pr. Suc (multiplicity p n))"
      using n by (subst divisor_count.prod_prime_factors') auto
    also have "Pr = Pr1 \<union> Pr2" by auto
    also have "real (\<Prod>p\<in>\<dots>. Suc (multiplicity p n)) =
                 real ((\<Prod>p\<in>Pr1. Suc (multiplicity p n)) * (\<Prod>p\<in>Pr2. Suc (multiplicity p n)))"
      by (subst prod.union_disjoint) auto
    also have "\<dots> < 2 powr (c * f n * ln (ln (real n)) / ln (f n)) * 2 powr (ln n / ln (f n))"
      unfolding of_nat_mult
      by (intro mult_less_le_imp_less bound1 bound2) (auto intro!: prod_nonneg prod_pos)
    also have "\<dots> = 2 powr g n"
      by (simp add: g_def add_divide_distrib powr_add)
    finally show "real (divisor_count n) < 2 powr g n" .
  qed
qed

text \<open>
  Now, Apostol explains that one can choose $f(n) := \ln n / (\ln\ln n) ^ 2$ to obtain
  the desired bound.
\<close>
proposition divisor_count_upper_bound:
  fixes \<epsilon> :: real
  assumes "\<epsilon> > 0"
  shows   "eventually (\<lambda>n. divisor_count n < 2 powr ((1 + \<epsilon>) * ln n / ln (ln n))) at_top"
proof -
  define c :: real where "c = 8 / ln 2"
  define f :: "nat \<Rightarrow> real" where "f = (\<lambda>n. ln n / (ln (ln n)) ^ 2)"
  define g where "g = (\<lambda>n. (ln n + c * f n * ln (ln n)) / (ln (f n)))"

  have "eventually (\<lambda>n. divisor_count n < 2 powr g n) at_top"
    unfolding g_def c_def f_def by (rule divisor_count_bound_gen) real_asymp+
  moreover have "eventually (\<lambda>n. 2 powr g n < 2 powr ((1 + \<epsilon>) * ln n / ln (ln n))) at_top"
    using \<open>\<epsilon> > 0\<close> unfolding g_def c_def f_def by real_asymp
  ultimately show "eventually (\<lambda>n. divisor_count n < 2 powr ((1 + \<epsilon>) * ln n / ln (ln n))) at_top"
    by eventually_elim (rule less_trans)
qed

text \<open>
  Next, we will examine the `worst case'. Since any prime factor of \<open>n\<close> with multiplicity
  \<open>k\<close> contributes a factor of $k + 1$, it is intuitively clear that $\sigma_0(n)$ is
  largest w.\,r.\,t.\ \<open>n\<close> if it is a product of small distinct primes.

  We show that indeed, if $n := x\#$ (where $x\#$ denotes the primorial), we have
  $\sigma_0(n) = 2^{\pi(x)}$, which, by the Prime Number Theorem, indeed
  exceeds $c \ln n / \ln\ln n$.
\<close>
theorem (in prime_number_theorem) divisor_count_primorial_gt:
  assumes "\<epsilon> > 0"
  defines "h \<equiv> primorial"
  shows "eventually (\<lambda>x. divisor_count (h x) > 2 powr ((1 - \<epsilon>) * ln (h x) / ln (ln (h x)))) at_top"
proof -
  have "(\<lambda>x. (1 - \<epsilon>) * ln (h x) / ln (ln (h x))) \<sim>[at_top] (\<lambda>x. (1 - \<epsilon>) * \<theta> x / ln (\<theta> x))"
    by (simp add: h_def ln_primorial)
  also have "\<dots> \<sim>[at_top] (\<lambda>x. (1 - \<epsilon>) * x / ln x)"
    by (intro asymp_equiv_intros \<theta>_asymptotics ln_\<theta>_asymp_equiv)
  finally have *: "(\<lambda>x. (1 - \<epsilon>) * ln (h x) / ln (ln (h x))) \<sim>[at_top] (\<lambda>x. (1 - \<epsilon>) * x / ln x)"
    by simp
  have "(\<lambda>x. (1 - \<epsilon>) * ln (h x) / (ln (ln (h x))) - (1 - \<epsilon>) * x / ln x) \<in> o(\<lambda>x. (1 - \<epsilon>) * x / ln x)"
    using asymp_equiv_imp_diff_smallo[OF *] by simp
  also have "?this \<longleftrightarrow> (\<lambda>x. (1 - \<epsilon>) * ln (h x) / (ln (ln (h x))) - x / ln x + \<epsilon> * x / ln x)
                \<in> o(\<lambda>x. (1 - \<epsilon>) * x / ln x)"
    by (intro landau_o.small.in_cong eventually_mono[OF eventually_gt_at_top[of 1]])
       (auto simp: field_simps)
  also have "(\<lambda>x. (1 - \<epsilon>) * x / ln x) \<in> O(\<lambda>x. x / ln x)"
    by real_asymp
  finally have "(\<lambda>x. (1 - \<epsilon>) * ln (h x) / (ln (ln (h x))) - x / ln x + \<epsilon> * x / ln x)
                   \<in> o(\<lambda>x. x / ln x)" .
  hence "(\<lambda>x. (1 - \<epsilon>) * ln (h x) / (ln (ln (h x))) - x / ln x + \<epsilon> * x / ln x - (\<pi> x - x / ln x))
           \<in> o(\<lambda>x. x / ln x)"
    by (intro sum_in_smallo[OF _ asymp_equiv_imp_diff_smallo] prime_number_theorem)
  hence "(\<lambda>x. (1 - \<epsilon>) * ln (h x) / (ln (ln (h x))) - \<pi> x + \<epsilon> * (x / ln x)) \<in> o(\<lambda>x. \<epsilon> * (x / ln x))"
    using \<open>\<epsilon> > 0\<close> by (subst landau_o.small.cmult) (simp_all add: algebra_simps)
  hence "(\<lambda>x. (1 - \<epsilon>) * ln (h x) / (ln (ln (h x))) - \<pi> x) \<sim>[at_top] (\<lambda>x. -\<epsilon> * (x / ln x))"
    by (intro smallo_imp_asymp_equiv) auto
  hence "eventually (\<lambda>x. (1 - \<epsilon>) * ln (h x) / (ln (ln (h x))) - \<pi> x < 0 \<longleftrightarrow>
                         -\<epsilon> * (x / ln x) < 0) at_top"
    by (rule asymp_equiv_eventually_neg_iff)
  moreover have "eventually (\<lambda>x. -\<epsilon> * (x / ln x) < 0) at_top"
    using \<open>\<epsilon> > 0\<close> by real_asymp
  ultimately have "eventually (\<lambda>x. (1 - \<epsilon>) * ln (h x) / ln (ln (h x)) < \<pi> x) at_top"
    by eventually_elim simp
  thus "eventually (\<lambda>x. divisor_count (h x) > 2 powr ((1 - \<epsilon>) * ln (h x) / ln (ln (h x)))) at_top"
  proof eventually_elim
    case (elim x)
    hence "2 powr ((1 - \<epsilon>) * ln (h x) / ln (ln (h x))) < 2 powr \<pi> x"
      by (intro powr_less_mono) auto
    thus ?case by (simp add: divisor_count_primorial h_def)
  qed
qed

text \<open>
  Since $h(x)\longrightarrow\infty$, this gives us our infinitely many values of \<open>n\<close>
  that exceed the bound.
\<close>
corollary (in prime_number_theorem) divisor_count_lower_bound:
  assumes "\<epsilon> > 0"
  shows   "frequently (\<lambda>n. divisor_count n > 2 powr ((1 - \<epsilon>) * ln n / ln (ln n))) at_top"
proof -
  define h where "h = primorial"
  have "eventually (\<lambda>n. divisor_count n > 2 powr ((1 - \<epsilon>) * ln n / ln (ln n)))
          (filtermap h at_top)"
    using divisor_count_primorial_gt[OF assms] by (simp add: eventually_filtermap h_def)
  hence "frequently (\<lambda>n. divisor_count n > 2 powr ((1 - \<epsilon>) * ln n / ln (ln n)))
           (filtermap h at_top)"
    by (intro eventually_frequently) (auto simp: filtermap_bot_iff)
  moreover from this and primorial_at_top
    have "filtermap h at_top \<le> at_top" by (simp add: filterlim_def h_def)
  ultimately show ?thesis
    by (rule frequently_mono_filter)
qed

text \<open>
  A different formulation that is not quite as tedious to prove is this one:
\<close>
lemma (in prime_number_theorem) ln_divisor_count_primorial'_asymp_equiv:
  "(\<lambda>k. ln (divisor_count (primorial' k))) \<sim>[at_top]
     (\<lambda>k. ln 2 * ln (primorial' k) / ln (ln (primorial' k)))"
proof -
  have "(\<lambda>k. ln 2 * (ln (primorial' k) / ln (ln (primorial' k)))) \<sim>[at_top] (\<lambda>k. ln 2 * k)"
    by (intro asymp_equiv_intros ln_over_ln_ln_primorial'_asymp_equiv)
  also have "\<dots> \<sim>[at_top] (\<lambda>k. ln (divisor_count (primorial' k)))"
    by (simp add: ln_realpow mult_ac)
  finally show ?thesis by (simp add: asymp_equiv_sym mult_ac)
qed

text \<open>
  It follows that the maximal order of the divisor function is $\ln 2 \cdot \ln n /\ln \ln n$.
\<close>
theorem (in prime_number_theorem) limsup_divisor_count:
  "limsup (\<lambda>n. ln (divisor_count n) * ln (ln n) / ln n) = ln 2"
proof (intro antisym)
  let ?h = "primorial'"
  have "2 ^ k = (1 :: real) \<longleftrightarrow> k = 0" for k :: nat
    using power_eq_1_iff[of "2::real" k] by auto
  hence "(\<lambda>k. ln (divisor_count (?h k)) / (ln 2 * ln (?h k) / ln (ln (?h k)))) \<longlonglongrightarrow> 1"
    using ln_divisor_count_primorial'_asymp_equiv
    by (intro asymp_equivD_strong eventually_mono[OF eventually_gt_at_top[of 1]])
       (auto simp: power_eq_1_iff)
  hence "(\<lambda>k. ln (divisor_count (?h k)) / (ln 2 * ln (?h k) / ln (ln (?h k))) * ln 2) \<longlonglongrightarrow> 1 * ln 2"
    by (rule tendsto_mult) auto
  hence "(\<lambda>k. ln (divisor_count (?h k)) / (ln (?h k) / ln (ln (?h k)))) \<longlonglongrightarrow> ln 2"
    by simp
  hence "limsup ((\<lambda>n. ln (divisor_count n) * ln (ln n) / ln n) \<circ> primorial') = ereal (ln 2)"
    by (intro lim_imp_Limsup tendsto_ereal) simp_all
  hence "ln 2 = limsup ((\<lambda>n. ereal (ln (divisor_count n) * ln (ln n) / ln n)) \<circ> primorial')"
    by (simp add: o_def)
  also have "\<dots> \<le> limsup (\<lambda>n. ln (divisor_count n) * ln (ln n) / ln n)"
    using strict_mono_primorial' by (rule limsup_subseq_mono)
  finally show "limsup (\<lambda>n. ln (divisor_count n) * ln (ln n) / ln n) \<ge> ln 2" .
next
  show "limsup (\<lambda>n. ln (divisor_count n) * ln (ln n) / ln n) \<le> ln 2"
    unfolding Limsup_le_iff
  proof safe
    fix C' assume "C' > ereal (ln 2)"
    from ereal_dense2[OF this] obtain C where C: "C > ln 2" "ereal C < C'" by auto
    define \<epsilon> where "\<epsilon> = (C / ln 2) - 1"
    from C have "\<epsilon> > 0" by (simp add: \<epsilon>_def)

    have "eventually (\<lambda>n::nat. ln (ln n) > 0) at_top" by real_asymp
    hence "eventually (\<lambda>n. ln (divisor_count n) * ln (ln n) / ln n < C) at_top"
      using divisor_count_upper_bound[OF \<open>\<epsilon> > 0\<close>] eventually_gt_at_top[of 1]
    proof eventually_elim
      case (elim n)
      hence "ln (divisor_count n) < ln (2 powr ((1 + \<epsilon>) * ln n / ln (ln n)))"
        by (subst ln_less_cancel_iff) auto
      also have "\<dots> = (1 + \<epsilon>) * ln 2 * ln n / ln (ln n)"
        by (simp add: ln_powr)
      finally have "ln (divisor_count n) * ln (ln n) / ln n < (1 + \<epsilon>) * ln 2"
        using elim by (simp add: field_simps)
      also have "\<dots> = C" by (simp add: \<epsilon>_def)
      finally show ?case .
    qed
    thus "eventually (\<lambda>n. ereal (ln (divisor_count n) * ln (ln n) / ln n) < C') at_top"
      by eventually_elim (rule less_trans[OF _ C(2)], auto)
  qed
qed
    

subsection \<open>Mertens' Third Theorem\<close>

text \<open>
  In this section, we will show that
  \[\prod_{p\leq x} \left(1 - \frac{1}{p}\right) =
      \frac{C}{\ln x} + O\left(\frac{1}{\ln^2 x}\right)\]
  with explicit bounds for the factor in the `Big-O'. Here, \<open>C\<close> is the following constant:
\<close>
definition third_mertens_const :: real where
  "third_mertens_const =
     exp (-(\<Sum>p::nat. if prime p then -ln (1 - 1 / real p) - 1 / real p else 0) - meissel_mertens)"

text \<open>
  This constant is actually equal to $e^{-\gamma}$ where $\gamma$ is the Euler--Mascheroni
   constant, but showing this is quite a bit of work, which we shall not do here.
\<close>

lemma third_mertens_const_pos: "third_mertens_const > 0"
  by (simp add: third_mertens_const_def)

theorem
  defines "C \<equiv> third_mertens_const" 
  shows   mertens_third_theorem_strong:
            "eventually (\<lambda>x. \<bar>(\<Prod>p | prime p \<and> real p \<le> x. 1 - 1 / p) - C / ln x\<bar> \<le>
                                10 * C / ln x ^ 2) at_top"
  and     mertens_third_theorem:
            "(\<lambda>x. (\<Prod>p | prime p \<and> real p \<le> x. 1 - 1 / p) - C / ln x) \<in> O(\<lambda>x. 1 / ln x ^ 2)"
proof -
  define Pr where "Pr = (\<lambda>x. {p. prime p \<and> real p \<le> x})"
  define a :: "nat \<Rightarrow> real"
    where "a = (\<lambda>p. if prime p then -ln (1 - 1 / real p) - 1 / real p else 0)"
  define B where "B = suminf a"
  have C_eq: "C = exp (-B - meissel_mertens)"
    by (simp add: B_def a_def third_mertens_const_def C_def)
  have fin: "finite (Pr x)" for x
    by (rule finite_subset[of _ "{..nat \<lfloor>x\<rfloor>}"]) (auto simp: Pr_def le_nat_iff le_floor_iff)

  define S where "S = (\<lambda>x. (\<Sum>p\<in>Pr x. ln (1 - 1 / p)))"
  define R where "R = (\<lambda>x. S x + ln (ln x) + (B + meissel_mertens))"

  have exp_S: "exp (S x) = (\<Prod>p\<in>Pr x. (1 - 1 / p))" for x
  proof -
    have "exp (S x) = (\<Prod>p\<in>Pr x. exp (ln (1 - 1 / p)))"
      by (simp add: S_def exp_sum fin)
    also have "\<dots> = (\<Prod>p\<in>Pr x. (1 - 1 / p))"
      by (intro prod.cong) (auto simp: Pr_def dest: prime_gt_1_nat)
    finally show ?thesis .
  qed

  have a_nonneg: "a n \<ge> 0" for n
  proof (cases "prime n")
    case True
    hence "ln (1 - 1 / n) \<le> -(1 / n)"
      by (intro ln_one_minus_pos_upper_bound) (auto dest: prime_gt_1_nat)
    thus ?thesis by (auto simp: a_def)
  qed (auto simp: a_def)

  have "summable a"
  proof (rule summable_comparison_test_bigo)
    have "a \<in> O(\<lambda>n. -ln (1 - 1 / n) - 1 / n)"
      by (intro bigoI[of _ 1]) (auto simp: a_def)
    also have "(\<lambda>n::nat. -ln (1 - 1 / n) - 1 / n) \<in> O(\<lambda>n. 1 / n ^ 2)"
      by real_asymp
    finally show "a \<in> O(\<lambda>n. 1 / real n ^ 2)" .
  next
    show "summable (\<lambda>n. norm (1 / real n ^ 2))"
      using inverse_power_summable[of 2] by (simp add: field_simps)
  qed

  have "eventually (\<lambda>n. a n \<le> 1 / n - 1 / Suc n) at_top"
  proof -
    have "eventually (\<lambda>n::nat. -ln (1 - 1 / n) - 1 / n \<le> 1 / n - 1 / Suc n) at_top"
      by real_asymp
    thus ?thesis using eventually_gt_at_top[of 1]
      by eventually_elim (auto simp: a_def of_nat_diff field_simps)
  qed
  hence "eventually (\<lambda>m. \<forall>n\<ge>m. a n \<le> 1 / n - 1 / Suc n) at_top"
    by (rule eventually_all_ge_at_top)
  hence "eventually (\<lambda>x. \<forall>n\<ge>nat \<lfloor>x\<rfloor>. a n \<le> 1 / n - 1 / Suc n) at_top"
    by (rule eventually_compose_filterlim)
       (intro filterlim_compose[OF filterlim_nat_sequentially] filterlim_floor_sequentially)
  hence "eventually (\<lambda>x. B - sum_upto a x \<le> 1 / x) at_top"
    using eventually_ge_at_top[of "1::real"]
  proof eventually_elim
    case (elim x)
    have a_le: "a n \<le> 1 / real n - 1 / real (Suc n)" if "real n \<ge> x" for n
    proof -
      from that and \<open>x \<ge> 1\<close> have "n \<ge> nat \<lfloor>x\<rfloor>" by linarith
      with elim and that show ?thesis by auto
    qed
    define m where "m = Suc (nat \<lfloor>x\<rfloor>)"
    have telescope: "(\<lambda>n. 1 / (n + m) - 1 / (Suc n + m)) sums (1 / real (0 + m) - 0)"
      by (intro telescope_sums') real_asymp

    have "B - (\<Sum>n<m. a n) = (\<Sum>n. a (n + m))"
      unfolding B_def sum_upto_altdef m_def using \<open>summable a\<close>
      by (subst suminf_split_initial_segment[of _ "Suc (nat \<lfloor>x\<rfloor>)"]) auto
    also have "(\<Sum>n<m. a n) = sum_upto a x"
      unfolding m_def sum_upto_altdef by (intro sum.mono_neutral_right) (auto simp: a_def)
    also have "(\<Sum>n. a (n + m)) \<le> (\<Sum>n. 1 / (n + m) - 1 / (Suc n + m))"
    proof (intro suminf_le allI)
      show "summable (\<lambda>n. a (n + m))"
        by (rule summable_ignore_initial_segment) fact+
    next
      show "summable (\<lambda>n. 1 / (n + m) - 1 / (Suc n + m))"
        using telescope by (rule sums_summable)
    next
      fix n :: nat
      have "x \<le> n + m" unfolding m_def using \<open>x \<ge> 1\<close> by linarith
      thus "a (n + m) \<le> 1 / (n + m) - 1 / (Suc n + m)"
        using a_le[of "n + m"] \<open>x \<ge> 1\<close> by simp
    qed
    also have "\<dots> = 1 / m"
      using telescope by (simp add: sums_iff)
    also have "x \<le> m" "m > 0"
      unfolding m_def using \<open>x \<ge> 1\<close> by linarith+
    hence "1 / m \<le> 1 / x"
      using \<open>x \<ge> 1\<close> by (intro divide_left_mono) (auto simp: m_def)
    finally show ?case .
  qed

  moreover have "eventually (\<lambda>x::real. 1 / x \<le> 1 / ln x) at_top" by real_asymp
  ultimately have "eventually (\<lambda>x. B - sum_upto a x \<le> 1 / ln x) at_top"
    by eventually_elim (rule order.trans)

  hence "eventually (\<lambda>x. \<bar>R x\<bar> \<le> 5 / ln x) at_top"
    using eventually_ge_at_top[of 2]
  proof eventually_elim
    case (elim x)
    have "\<bar>(B - sum_upto a x) - (prime_sum_upto (\<lambda>p. 1 / p) x - ln (ln x) - meissel_mertens)\<bar> \<le>
             1 / ln x + 4 / ln x"
    proof (intro order.trans[OF abs_triangle_ineq4 add_mono])
      show "\<bar>prime_sum_upto (\<lambda>p. 1 / real p) x - ln (ln x) - meissel_mertens\<bar> \<le> 4 / ln x"
        by (intro mertens_second_theorem \<open>x \<ge> 2\<close>)
      have "sum_upto a x \<le> B"
        unfolding B_def sum_upto_def by (intro sum_le_suminf \<open>summable a\<close> a_nonneg ballI) auto
      thus "\<bar>B - sum_upto a x\<bar> \<le> 1 / ln x"
        using elim by linarith
    qed
    also have "sum_upto a x = prime_sum_upto (\<lambda>p. -ln (1 - 1 / p) - 1 / p) x"
      unfolding sum_upto_def prime_sum_upto_altdef1 a_def by (intro sum.cong allI) auto
    also have "\<dots> = -S x - prime_sum_upto (\<lambda>p. 1 / p) x"
      by (simp add: a_def S_def Pr_def prime_sum_upto_def sum_subtractf sum_negf)
    finally show "\<bar>R x\<bar> \<le> 5 / ln x"
      by (simp add: R_def)
  qed

  moreover have "eventually (\<lambda>x::real. \<bar>5 / ln x\<bar> < 1 / 2) at_top" by real_asymp
  ultimately have "eventually (\<lambda>x. exp (R x) - 1 \<in> {-5 / ln x..10 / ln x}) at_top"
    using eventually_gt_at_top[of 1]
  proof eventually_elim
    case (elim x)
    have "exp (R x) \<le> exp (5 / ln x)"
      using elim by simp
    also have "\<dots> \<le> 1 + 10 / ln x"
      using real_exp_bound_lemma[of "5 / ln x"] elim by (simp add: abs_if split: if_splits)
    finally have le: "exp (R x) \<le> 1 + 10 / ln x" .

    have "1 + (-5 / ln x) \<le> exp (-5 / ln x)"
      by (rule exp_ge_add_one_self)
    also have "exp (-5 / ln x) \<le> exp (R x)"
      using elim by simp
    finally have "exp (R x) \<ge> 1 - 5 / ln x" by simp
    with le show ?case by simp
  qed

  thus "eventually (\<lambda>x. \<bar>(\<Prod>p\<in>Pr x. 1 - 1 / real p) - C / ln x\<bar> \<le> 10 * C / ln x ^ 2) at_top"
    using eventually_gt_at_top[of "exp 1"] eventually_gt_at_top[of 1]
  proof eventually_elim
    case (elim x)
    have "\<bar>exp (R x) - 1\<bar> \<le> 10 / ln x"
      using elim by (simp add: abs_if)
    from elim have "\<bar>exp (S x) - C / ln x\<bar> = C / ln x * \<bar>exp (R x) - 1\<bar>"
      by (simp add: R_def exp_add C_eq exp_diff exp_minus field_simps)
    also have "\<dots> \<le> C / ln x * (10 / ln x)"
      using elim by (intro mult_left_mono) (auto simp: C_eq)
    finally show ?case by (simp add: exp_S power2_eq_square mult_ac)
  qed

  thus "(\<lambda>x. (\<Prod>p\<in>Pr x. 1 - 1 / real p) - C / ln x) \<in> O(\<lambda>x. 1 / ln x ^ 2)"
    by (intro bigoI[of _ "10  * C"]) auto
qed

lemma mertens_third_theorem_asymp_equiv:
  "(\<lambda>x. (\<Prod>p | prime p \<and> real p \<le> x. 1 - 1 / real p)) \<sim>[at_top]
     (\<lambda>x. third_mertens_const / ln x)"
  by (rule smallo_imp_asymp_equiv[OF landau_o.big_small_trans[OF mertens_third_theorem]])
     (use third_mertens_const_pos in real_asymp)

text \<open>
  We now show an equivalent version where $\prod_{p\leq x} (1 - 1 / p)$ is replaced
  by $\prod_{i=1}^k (1 - 1 / p_i)$:
\<close>
lemma mertens_third_convert:
  assumes "n > 0"
  shows "(\<Prod>k<n. 1 - 1 / real (nth_prime k)) =
           (\<Prod>p | prime p \<and> p \<le> nth_prime (n - 1). 1 - 1 / p)"
proof -
  have "primorial' n = primorial (nth_prime (n - 1))"
    using assms by (simp add: primorial'_conv_primorial)
  also have "real (totient \<dots>) =
               primorial' n * (\<Prod>p | prime p \<and> p \<le> nth_prime (n - 1). 1 - 1 / p)"
    using assms by (subst totient_primorial) (auto simp: primorial'_conv_primorial)
  finally show ?thesis
    by (simp add: totient_primorial')
qed

lemma (in prime_number_theorem) mertens_third_theorem_asymp_equiv':
  "(\<lambda>n. (\<Prod>k<n. 1 - 1 / nth_prime k)) \<sim>[at_top] (\<lambda>x. third_mertens_const / ln x)"
proof -
  have lim: "filterlim (\<lambda>n. real (nth_prime (n - 1))) at_top at_top"
    by (intro filterlim_compose[OF filterlim_real_sequentially]
              filterlim_compose[OF nth_prime_at_top]) real_asymp
  have "(\<lambda>n. (\<Prod>k<n. 1 - 1 / nth_prime k)) \<sim>[at_top]
          (\<lambda>n. (\<Prod>p | prime p \<and> real p \<le> real (nth_prime (n - 1)). 1 - 1 / p))"
    by (intro asymp_equiv_refl_ev eventually_mono[OF eventually_gt_at_top[of 0]])
       (subst mertens_third_convert, auto)
  also have "\<dots> \<sim>[at_top] (\<lambda>n. third_mertens_const / ln (real (nth_prime (n - 1))))"
    by (intro asymp_equiv_compose'[OF mertens_third_theorem_asymp_equiv lim])
  also have "\<dots> \<sim>[at_top] (\<lambda>n. third_mertens_const / ln (real (n - 1)))"
    by (intro asymp_equiv_intros asymp_equiv_compose'[OF ln_nth_prime_asymp_equiv]) real_asymp
  also have "\<dots> \<sim>[at_top] (\<lambda>n. third_mertens_const / ln (real n))"
    using third_mertens_const_pos by real_asymp
  finally show ?thesis .
qed


subsection \<open>Bounds on Euler's totient function\<close>

text \<open>
  Similarly to the divisor function, we will show that $\varphi(n)$ has minimal order
  $C n / \ln\ln n$.

  The first part is to show the lower bound:
\<close>
theorem totient_lower_bound:
  fixes \<epsilon> :: real
  assumes "\<epsilon> > 0"
  defines "C \<equiv> third_mertens_const"
  shows "eventually (\<lambda>n. totient n > (1 - \<epsilon>) * C * n / ln (ln n)) at_top"
proof -
  include prime_counting_notation
  define f :: "nat \<Rightarrow> nat" where "f = (\<lambda>n. card {p\<in>prime_factors n. p > ln n})"

  define lb1 where "lb1 = (\<lambda>n::nat. (\<Prod>p | prime p \<and> real p \<le> ln n. 1 - 1 / p))"
  define lb2 where "lb2 = (\<lambda>n::nat. (1 - 1 / ln n) powr (ln n / ln (ln n)))"
  define lb1' where "lb1' = (\<lambda>n::nat. C / ln (ln n) - 10 * C / ln (ln n) ^ 2)"

  have "eventually (\<lambda>n::nat. 1 + log 2 n \<le> ln n ^ 2) at_top"  by real_asymp
  hence "eventually (\<lambda>n. totient n / n \<ge> lb1 n * lb2 n) at_top"
    using eventually_gt_at_top[of 2]
  proof eventually_elim
    fix n :: nat
    assume n: "n > 2" and "1 + log 2 n \<le> ln n ^ 2"

    define Pr where [simp]: "Pr = prime_factors n"
    define Pr1 where [simp]: "Pr1 = {p\<in>Pr. p \<le> ln n}"
    define Pr2 where [simp]: "Pr2 = {p\<in>Pr. p > ln n}"
  
    have "exp 1 < real n"
      using e_less_272 \<open>n > 2\<close> by linarith
    hence "ln (exp 1) < ln (real n)"
      using \<open>n > 2\<close> by (subst ln_less_cancel_iff) auto
    hence "1 < ln n" by simp
    hence "ln (ln n) > ln (ln (exp 1))"
      by (subst ln_less_cancel_iff) auto
    hence "ln (ln n) > 0" by simp
  
    have "ln n ^ f n \<le> (\<Prod>p\<in>Pr2. ln n)"
      by (simp add: f_def)
    also have "\<dots> \<le> real (\<Prod>p\<in>Pr2. p)" unfolding of_nat_prod
      by (intro prod_mono) (auto dest: prime_gt_1_nat simp: in_prime_factors_iff)
    also {
      have "(\<Prod>p\<in>Pr2. p) dvd (\<Prod>p\<in>Pr2. p ^ multiplicity p n)"
        by (intro prod_dvd_prod dvd_power) (auto simp: prime_factors_multiplicity)
      also have "\<dots> dvd (\<Prod>p\<in>Pr. p ^ multiplicity p n)"
        by (intro prod_dvd_prod_subset2) auto
      also have "\<dots> = n"
        using \<open>n > 2\<close> by (subst (2) prime_factorization_nat[of n]) auto
      finally have "(\<Prod>p\<in>Pr2. p) \<le> n"
        using \<open>n > 2\<close> by (intro dvd_imp_le) auto
    }
    finally have "ln (ln n ^ f n) \<le> ln n"
      using \<open>n > 2\<close> by (subst ln_le_cancel_iff) auto
    also have "ln (ln n ^ f n) = f n * ln (ln n)"
      using \<open>n > 2\<close> by (subst ln_realpow) auto
    finally have f_le: "f n \<le> ln n / ln (ln n)"
      using \<open>ln (ln n) > 0\<close> by (simp add: field_simps)

    have "(1 - 1 / ln n) powr (ln n / ln (ln n)) \<le> (1 - 1 / ln n) powr (real (f n))"
      using \<open>n > 2\<close> and \<open>ln n > 1\<close> by (intro powr_mono' f_le) auto
    also have "\<dots> = (\<Prod>p\<in>Pr2. 1 - 1 / ln n)"
      using \<open>n > 2\<close> and \<open>ln n > 1\<close> by (subst powr_realpow) (auto simp: f_def)
    also have "\<dots> \<le> (\<Prod>p\<in>Pr2. 1 - 1 / p)"
      using \<open>n > 2\<close> and \<open>ln n > 1\<close>
      by (intro prod_mono conjI diff_mono divide_left_mono) (auto dest: prime_gt_1_nat)
    finally have bound2: "(\<Prod>p\<in>Pr2. 1 - 1 / p) \<ge> lb2 n" unfolding lb2_def .

    have "(\<Prod>p | prime p \<and> real p \<le> ln n. inverse (1 - 1 / p)) \<ge> (\<Prod>p\<in>Pr1. inverse (1 - 1 / p))"
      using \<open>n > 2\<close> by (intro prod_mono2) (auto intro: finite_primes_le  dest: prime_gt_1_nat                                                simp: in_prime_factors_iff field_simps)
    hence "inverse (\<Prod>p | prime p \<and> real p \<le> ln n. 1 - 1 / p) \<ge> inverse (\<Prod>p\<in>Pr1. 1 - 1 / p)"
      by (subst (1 2) prod_inversef [symmetric]) auto
    hence bound1: "(\<Prod>p\<in>Pr1. 1 - 1 / p) \<ge> lb1 n" unfolding lb1_def
      by (rule inverse_le_imp_le)
         (auto intro!: prod_pos simp: in_prime_factors_iff dest: prime_gt_1_nat)

    have "lb1 n * lb2 n \<le> (\<Prod>p\<in>Pr1. 1 - 1 / p) * (\<Prod>p\<in>Pr2. 1 - 1 / p)"
      by (intro mult_mono bound1 bound2 prod_nonneg ballI)
         (auto simp: in_prime_factors_iff lb1_def lb2_def dest: prime_gt_1_nat)
    also have "\<dots> = (\<Prod>p\<in>Pr1 \<union> Pr2. 1 - 1 / p)"
      by (subst prod.union_disjoint) auto
    also have "Pr1 \<union> Pr2 = Pr" by auto
    also have "(\<Prod>p\<in>Pr. 1 - 1 / p) = totient n / n"
      using n by (subst totient_formula2) auto
    finally show "real (totient n) / real n \<ge> lb1 n * lb2 n"
      by (simp add: lb1_def lb2_def)
  qed

  moreover have "eventually (\<lambda>n. \<bar>lb1 n - C / ln (ln n)\<bar> \<le> 10 * C / ln (ln n) ^ 2) at_top"
    unfolding lb1_def C_def using mertens_third_theorem_strong
    by (rule eventually_compose_filterlim) real_asymp

  moreover have "eventually (\<lambda>n. (1 - \<epsilon>) * C / ln (ln n) < lb1' n * lb2 n) at_top"
    unfolding lb1'_def lb2_def C_def using third_mertens_const_pos \<open>\<epsilon> > 0\<close> by real_asymp

  ultimately show "eventually (\<lambda>n. totient n > (1 - \<epsilon>) * C * n / ln (ln n)) at_top"
    using eventually_gt_at_top[of 0]
  proof eventually_elim
    case (elim n)
    have "(1 - \<epsilon>) * C / ln (ln n) < lb1' n * lb2 n" by fact
    also have "lb1' n \<le> lb1 n"
      unfolding lb1'_def using elim by linarith
    hence "lb1' n * lb2 n \<le> lb1 n * lb2 n"
      by (intro mult_right_mono) (auto simp: lb2_def)
    also have "\<dots> \<le> totient n / n" by fact
    finally show "totient n > (1 - \<epsilon>) * C * n / (ln (ln n))"
      using \<open>n > 0\<close> by (simp add: field_simps)
  qed
qed

text \<open>
  Next, we examine the `worst case' of $\varphi(n)$ where \<open>n\<close> is the primorial of $x$.
  In this case, we have $\varphi(n) < c n / \ln\ln n$ for any $c > C$ for all sufficiently
  large $n$.
\<close>
theorem (in prime_number_theorem) totient_primorial_less:
  fixes \<epsilon> :: real
  defines "C \<equiv> third_mertens_const" and "h \<equiv> primorial"
  assumes "\<epsilon> > 0"
  shows   "eventually (\<lambda>x. totient (h x) < (1 + \<epsilon>) * C * h x / ln (ln (h x))) at_top"
proof -
  have "C > 0" by (simp add: C_def third_mertens_const_pos)

  have "(\<lambda>x. (1 + \<epsilon>) * C / ln (ln (h x))) \<sim>[at_top] (\<lambda>x. (1 + \<epsilon>) * C / ln (\<theta> x))"
    by (simp add: ln_primorial h_def)
  also have "\<dots> \<sim>[at_top] (\<lambda>x. (1 + \<epsilon>) * C / ln x)"
    by (intro asymp_equiv_intros ln_\<theta>_asymp_equiv)
  finally have "(\<lambda>x. (1 + \<epsilon>) * C / ln (ln (h x)) - (1 + \<epsilon>) * C / ln x) \<in> o(\<lambda>x. (1 + \<epsilon>) * C / ln x)"
    by (rule asymp_equiv_imp_diff_smallo)
  also have "(\<lambda>x. (1 + \<epsilon>) * C / ln x) \<in> O(\<lambda>x. 1 / ln x)"
    by real_asymp
  also have "(\<lambda>x. (1 + \<epsilon>) * C / ln (ln (h x)) - (1 + \<epsilon>) * C / ln x) =
               (\<lambda>x. (1 + \<epsilon>) * C / ln (ln (h x)) - C / ln x - \<epsilon> * C / ln x)"
    by (simp add: algebra_simps fun_eq_iff add_divide_distrib)
  finally have "(\<lambda>x. (1 + \<epsilon>) * C / ln (ln (h x)) - C / ln x - \<epsilon> * C / ln x) \<in> o(\<lambda>x. 1 / ln x)" .
  hence "(\<lambda>x. (1 + \<epsilon>) * C / ln (ln (h x)) - C / ln x - \<epsilon> * C / ln x - 
           ((\<Prod>p\<in>{p. prime p \<and> real p \<le> x}. 1 - 1 / real p) - C / ln x)) \<in> o(\<lambda>x. 1 / ln x)"
    unfolding C_def
    by (rule sum_in_smallo[OF _ landau_o.big_small_trans[OF mertens_third_theorem]]) real_asymp+
  hence "(\<lambda>x. ((1 + \<epsilon>) * C / ln (ln (h x)) - (\<Prod>p\<in>{p. prime p \<and> real p \<le> x}. 1 - 1 / real p)) -
                 (\<epsilon> * C / ln x)) \<in> o(\<lambda>x. 1 / ln x)"
    by (simp add: algebra_simps)
  also have "(\<lambda>x. 1 / ln x) \<in> O(\<lambda>x. \<epsilon> * C / ln x)"
    using \<open>\<epsilon> > 0\<close> by (simp add: landau_divide_simps C_def third_mertens_const_def)
  finally have "(\<lambda>x. (1 + \<epsilon>) * C / ln (ln (h x)) - (\<Prod>p | prime p \<and> real p \<le> x. 1 - 1 / p))
                  \<sim>[at_top] (\<lambda>x. \<epsilon> * C / ln x)"
    by (rule smallo_imp_asymp_equiv)

  hence "eventually (\<lambda>x. (1 + \<epsilon>) * C / ln (ln (h x)) - (\<Prod>p | prime p \<and> real p \<le> x. 1 - 1 / p) > 0
                          \<longleftrightarrow> \<epsilon> * C / ln x > 0) at_top"
    by (rule asymp_equiv_eventually_pos_iff)
  moreover have "eventually (\<lambda>x. \<epsilon> * C / ln x > 0) at_top"
    using \<open>\<epsilon> > 0\<close> \<open>C > 0\<close> by real_asymp
  ultimately have "eventually (\<lambda>x. (1 + \<epsilon>) * C / ln (ln (h x)) >
                      (\<Prod>p | prime p \<and> real p \<le> x. 1 - 1 / p)) at_top"
    by eventually_elim auto
  thus ?thesis
  proof eventually_elim
    case (elim x)
    have "h x > 0" by (auto simp: h_def primorial_def intro!: prod_pos dest: prime_gt_0_nat)
    have "h x * ((1 + \<epsilon>) * C / ln (ln (h x))) > totient (h x)"
      using elim primorial_pos[of x] unfolding h_def totient_primorial
      by (intro mult_strict_left_mono) auto
    thus ?case by (simp add: mult_ac)
  qed
qed

text \<open>
  It follows that infinitely many values of \<open>n\<close> exceed $c n / \ln (\ln n)$ when \<open>c\<close> is chosen
  larger than \<open>C\<close>.
\<close>
corollary (in prime_number_theorem) totient_upper_bound:
  assumes "\<epsilon> > 0"
  defines "C \<equiv> third_mertens_const"
  shows   "frequently (\<lambda>n. totient n < (1 + \<epsilon>) * C * n / ln (ln n)) at_top"
proof -
  define h where "h = primorial"
  have "eventually (\<lambda>n. totient n < (1 + \<epsilon>) * C * n / ln (ln n)) (filtermap h at_top)"
    using totient_primorial_less[OF assms(1)] by (simp add: eventually_filtermap C_def h_def)
  hence "frequently (\<lambda>n. totient n < (1 + \<epsilon>) * C * n / ln (ln n)) (filtermap h at_top)"
    by (intro eventually_frequently) (auto simp: filtermap_bot_iff)
  moreover from this and primorial_at_top
    have "filtermap h at_top \<le> at_top" by (simp add: filterlim_def h_def)
  ultimately show ?thesis
    by (rule frequently_mono_filter)
qed

text \<open>
  Again, the following alternative formulation is somewhat nicer to prove:
\<close>
lemma (in prime_number_theorem) totient_primorial'_asymp_equiv:
  "(\<lambda>k. totient (primorial' k)) \<sim>[at_top] (\<lambda>k. third_mertens_const * primorial' k / ln k)"
proof -
  let ?C = third_mertens_const
  have "(\<lambda>k. totient (primorial' k)) \<sim>[at_top] (\<lambda>k. primorial' k * (\<Prod>i<k. 1 - 1 / nth_prime i))"
    by (subst totient_primorial') auto
  also have "\<dots> \<sim>[at_top] (\<lambda>k. primorial' k * (?C / ln k))"
    by (intro asymp_equiv_intros mertens_third_theorem_asymp_equiv')
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma (in prime_number_theorem) totient_primorial'_asymp_equiv':
  "(\<lambda>k. totient (primorial' k)) \<sim>[at_top]
      (\<lambda>k. third_mertens_const * primorial' k / ln (ln (primorial' k)))"
proof -
  let ?C = third_mertens_const
  have "(\<lambda>k. totient (primorial' k)) \<sim>[at_top] (\<lambda>k. third_mertens_const * primorial' k / ln k)"
    by (rule totient_primorial'_asymp_equiv)
  also have "\<dots> \<sim>[at_top] (\<lambda>k. third_mertens_const * primorial' k / ln (ln (primorial' k)))"
    by (intro asymp_equiv_intros asymp_equiv_symI[OF ln_ln_primorial'_asymp_equiv])
  finally show ?thesis .
qed

text \<open>
  All in all, $\varphi(n)$ has minimal order $cn / \ln\ln n$:
\<close>
theorem (in prime_number_theorem)
  liminf_totient: "liminf (\<lambda>n. totient n * ln (ln n) / n) = third_mertens_const"
    (is "_ = ereal ?c")
proof (intro antisym)
  have "(\<lambda>k. totient (primorial' k) / (?c * primorial' k / ln (ln (primorial' k)))) \<longlonglongrightarrow> 1"
    using totient_primorial'_asymp_equiv'
    by (intro asymp_equivD_strong eventually_mono[OF eventually_gt_at_top[of 1]]) auto
  hence "(\<lambda>k. totient (primorial' k) / (?c * primorial' k / ln (ln (primorial' k))) * ?c)
             \<longlonglongrightarrow> 1 * ?c" by (intro tendsto_mult) auto
  hence "(\<lambda>k. totient (primorial' k) / (primorial' k / ln (ln (primorial' k)))) \<longlonglongrightarrow> ?c"
    using third_mertens_const_pos by simp
  hence "liminf ((\<lambda>n. totient n * ln (ln n) / n) \<circ> primorial') = ereal ?c"
    by (intro lim_imp_Liminf tendsto_ereal) simp_all
  hence "?c = liminf ((\<lambda>n. ereal (totient n * ln (ln n) / n)) \<circ> primorial')"
    by (simp add: o_def)
  also have "\<dots> \<ge> liminf (\<lambda>n. totient n * ln (ln n) / n)"
    using strict_mono_primorial' by (rule liminf_subseq_mono)
  finally show "liminf (\<lambda>n. totient n * ln (ln n) / n) \<le> ?c" .
next
  show "liminf (\<lambda>n. totient n * ln (ln n) / n) \<ge> ?c"
    unfolding le_Liminf_iff
  proof safe
    fix C' assume "C' < ereal ?c"
    from ereal_dense2[OF this] obtain C where C: "C < ?c" "ereal C > C'" by auto
    define \<epsilon> where "\<epsilon> = 1 - C / ?c"
    from C have "\<epsilon> > 0" using third_mertens_const_pos by (simp add: \<epsilon>_def)

    have "eventually (\<lambda>n::nat. ln (ln n) > 0) at_top" by real_asymp
    hence "eventually (\<lambda>n. totient n * ln (ln n) / n > C) at_top"
      using totient_lower_bound[OF \<open>\<epsilon> > 0\<close>] eventually_gt_at_top[of 1]
    proof eventually_elim
      case (elim n)
      hence "totient n * ln (ln n) / n > (1 - \<epsilon>) * ?c"
        by (simp add: field_simps)
      also have "(1 - \<epsilon>) * ?c = C"
        using third_mertens_const_pos by (simp add: field_simps \<epsilon>_def)
      finally show ?case .
    qed
    thus "eventually (\<lambda>n. ereal (totient n * ln (ln n) / n) > C') at_top"
      by eventually_elim (rule less_trans[OF C(2)], auto)
  qed
qed

(*<*)
unbundle no_prime_counting_notation
(*>*)

end
