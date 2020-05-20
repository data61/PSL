section \<open>Uniqueness of Laplace Transform\<close>
theory Uniqueness
  imports
    "Existence"
    "Lerch_Lemma"
begin

text \<open>We show uniqueness of the Laplace transform for continuous functions.\<close>

lemma laplace_transform_zero:\<comment> \<open>should also work for piecewise continuous\<close>
  assumes cont_f: "continuous_on {0..} f"
  assumes eo: "exponential_order M a f"
  assumes laplace: "\<And>s. Re s > a \<Longrightarrow> (f has_laplace 0) s"
  assumes "t \<ge> 0"
  shows "f t = 0"
proof -
  define I where "I \<equiv> \<lambda>s k. integral {0..k} (laplace_integrand f s)"
  have bounded_image: "bounded (f ` {0..b})" for b
    by (auto intro!: compact_imp_bounded compact_continuous_image cont_f intro: continuous_on_subset)
  obtain B where B: "\<forall>x\<in>{0..b}. cmod (f x) \<le> B b" for b
    apply atomize_elim
    apply (rule choice)
    using bounded_image[unfolded bounded_iff]
    by auto
  have fi: "f integrable_on {0..b}" for b
    by (auto intro!: integrable_continuous_interval intro: continuous_on_subset cont_f)
  have aint: "complex_set_integrable lebesgue {0..b} (laplace_integrand f s)" for b s
    by (rule laplace_integrand_absolutely_integrable_on_Icc[OF
          AE_BallI[OF bounded_le_Sup[OF bounded_image]] fi])
  have int: "((\<lambda>t. exp (t *\<^sub>R - s) * f t) has_integral I s b) {0 .. b}" for s b
    using aint[of b s]
    unfolding laplace_integrand_def[symmetric] I_def absolutely_integrable_on_def
    by blast
  have I_integral: "Re s > a \<Longrightarrow> (I s \<longlongrightarrow> integral {0..} (laplace_integrand f s)) at_top" for s
    unfolding I_def
    by (metis aint eo improper_integral_at_top laplace_integrand_absolutely_integrable_on_Ici_iff)
  have imp: "(I s \<longlongrightarrow> 0) at_top" if s: "Re s > a" for s
    using I_integral[of s] laplace[unfolded has_laplace_def, rule_format, OF s] s
    unfolding has_laplace_def I_def laplace_integrand_def
    by (simp add: integral_unique)

  define s0 where "s0 = a + 1"
  then have "s0 > a" by auto
  have "\<forall>\<^sub>F x in at_right (0::real). 0 < x \<and> x < 1"
    by (auto intro!: eventually_at_rightI)
  moreover
  from exponential_orderD(2)[OF eo]
  have "\<forall>\<^sub>F t in at_right 0. cmod (f (- ln t)) \<le> M * exp (a * (- ln t))"
    unfolding at_top_mirror filtermap_ln_at_right[symmetric] eventually_filtermap .
  ultimately have "\<forall>\<^sub>F x in at_right 0. cmod ((x powr s0) * f (- ln x)) \<le> M * x powr (s0 - a)"
    (is "\<forall>\<^sub>F x in _. ?l x \<le> ?r x")
  proof eventually_elim
    case x: (elim x)
    then have "cmod ((x powr s0) * f (- ln x)) \<le> x powr s0 * (M * exp (a * (- ln x)))"
      by (intro norm_mult_ineq[THEN order_trans]) (auto intro!: x(2)[THEN order_trans])
    also have "\<dots> = M * x powr (s0 - a)"
      by (simp add: exp_minus ln_inverse divide_simps powr_def mult_exp_exp algebra_simps)
    finally show ?case .
  qed
  then have "((\<lambda>x. x powr s0 * f (- ln x)) \<longlongrightarrow> 0) (at_right 0)"
    by (rule Lim_null_comparison)
      (auto intro!: tendsto_eq_intros \<open>a < s0\<close> eventually_at_rightI zero_less_one)
  moreover have "\<forall>\<^sub>F x in at x. ln x \<le> 0" if "0 < x" "x < 1" for x::real
    using order_tendstoD(1)[OF tendsto_ident_at \<open>0 < x\<close>, of UNIV]
      order_tendstoD(2)[OF tendsto_ident_at \<open>x < 1\<close>, of UNIV]
    by eventually_elim simp
  ultimately have [continuous_intros]:
    "continuous_on {0..1} (\<lambda>x. x powr s0 * f (- ln x))"
    by (intro continuous_on_IccI;
        force intro!: continuous_on_tendsto_compose[OF cont_f] tendsto_eq_intros eventually_at_leftI
        zero_less_one)
  {
    fix n::nat
    let ?i = "(\<lambda>u. u ^ n *\<^sub>R (u powr s0 * f (- ln u)))"
    let ?I = "\<lambda>n b. integral {exp (- b).. 1} ?i"
    have "\<forall>\<^sub>F (b::real) in at_top. b > 0"
      by (simp add: eventually_gt_at_top)
    then have "\<forall>\<^sub>F b in at_top. I (s0 + Suc n) b = ?I n b"
    proof eventually_elim
      case (elim b)
      have eq: "exp (t *\<^sub>R - complex_of_real (s0 + real (Suc n))) * f t =
        complex_of_real (exp (- (real n * t)) * exp (- t) * exp (- (s0 * t))) * f t"
        for t
        by (auto simp: Euler mult_exp_exp algebra_simps simp del: of_real_mult)
      from int[of "s0 + Suc n" b]
      have int': "((\<lambda>t. exp (- (n * t)) * exp (-t) * exp (- (s0 * t)) * f t)
          has_integral I (s0 + Suc n) b) {0..b}"
        (is "(?fe has_integral _) _")
        unfolding eq .
      have "((\<lambda>x. - exp (- x) *\<^sub>R exp (- x) ^ n *\<^sub>R (exp (- x) powr s0 * f (- ln (exp (- x)))))
          has_integral
            integral {exp (- 0)..exp (- b)} ?i - integral {exp (- b)..exp (- 0)} ?i) {0..b}"
        by (rule has_integral_substitution_general[of "{}" 0 b "\<lambda>t. exp(-t)" 0 1 ?i "\<lambda>x. -exp(-x)"])
           (auto intro!: less_imp_le[OF \<open>b > 0\<close>] continuous_intros integrable_continuous_real
             derivative_eq_intros)
      then have "(?fe has_integral ?I n b) {0..b}"
        using \<open>b > 0\<close>
        by (auto simp: algebra_simps mult_exp_exp exp_of_nat_mult[symmetric] scaleR_conv_of_real
            exp_add powr_def of_real_exp has_integral_neg_iff)
      with int' show ?case
        by (rule has_integral_unique)
    qed
    moreover have "(I (s0 + Suc n) \<longlongrightarrow> 0) at_top"
      by (rule imp) (use \<open>s0 > a\<close> in auto)
    ultimately have "(?I n \<longlongrightarrow> 0) at_top"
      by (rule Lim_transform_eventually[rotated])
    then have 1: "((\<lambda>x. integral {exp (ln x)..1} ?i) \<longlongrightarrow> 0) (at_right 0)"
      unfolding at_top_mirror filtermap_ln_at_right[symmetric] filtermap_filtermap filterlim_filtermap
      by simp
    have "\<forall>\<^sub>F x in at_right 0. x > 0"
      by (simp add: eventually_at_filter)
    then have "\<forall>\<^sub>F x in at_right 0. integral {exp (ln x)..1} ?i = integral {x .. 1} ?i"
      by eventually_elim (auto simp:)
    from Lim_transform_eventually[OF 1 this]
    have "((\<lambda>x. integral {x..1} ?i) \<longlongrightarrow> 0) (at_right 0)"
      by simp
    moreover
    have "?i integrable_on {0..1}"
      by (force intro: continuous_intros integrable_continuous_real)
    from continuous_on_Icc_at_rightD[OF indefinite_integral_continuous_1'[OF this] zero_less_one]
    have "((\<lambda>x. integral {x..1} ?i) \<longlongrightarrow> integral {0 .. 1} ?i) (at_right 0)"
      by simp
    ultimately have "integral {0 .. 1} ?i = 0"
      by (rule tendsto_unique[symmetric, rotated]) simp
    then have "(?i has_integral 0) {0 .. 1}"
      using integrable_integral \<open>?i integrable_on {0..1}\<close>
      by (metis (full_types))
  } from lerch_lemma[OF _ this, of "exp (- t)"]
  show "f t = 0" using \<open>t \<ge> 0\<close>
    by (auto intro!: continuous_intros)
qed

lemma exponential_order_eventually_eq: "exponential_order M a f"
  if "exponential_order M a g" "\<And>t. t \<ge> k \<Longrightarrow> f t = g t"
proof -
  have "\<forall>\<^sub>F t in at_top. f t = g t"
    using that
    unfolding eventually_at_top_linorder
    by blast
  with exponential_orderD(2)[OF that(1)]
  have "(\<forall>\<^sub>F t in at_top. norm (f t) \<le> M * exp (a * t))"
    by eventually_elim auto
  with exponential_orderD(1)[OF that(1)]
  show ?thesis
    by (rule exponential_orderI)
qed

lemma exponential_order_mono:
  assumes eo: "exponential_order M a f"
  assumes "a \<le> b" "M \<le> N"
  shows "exponential_order N b f"
proof (rule exponential_orderI)
  from exponential_orderD[OF eo] assms(3)
  show "0 < N" by simp
  have "\<forall>\<^sub>F t in at_top. (t::real) > 0"
    by (simp add: eventually_gt_at_top)
  then have "\<forall>\<^sub>F t in at_top. M * exp (a * t) \<le> N * exp (b * t)"
    by eventually_elim
      (use \<open>0 < N\<close> in \<open>force intro: mult_mono assms\<close>)
  with exponential_orderD(2)[OF eo]
  show "\<forall>\<^sub>F t in at_top. norm (f t) \<le> N * exp (b * t)"
    by (eventually_elim) simp
qed

lemma exponential_order_uminus_iff:
  "exponential_order M a (\<lambda>x. - f x) = exponential_order M a f"
  by (auto simp: exponential_order_def)

lemma exponential_order_add:
  assumes "exponential_order M a f" "exponential_order M a g"
  shows "exponential_order (2 * M) a (\<lambda>x. f x + g x)"
  using assms
  apply (auto simp: exponential_order_def)
  subgoal premises prems
    using prems(1,3)
    apply (eventually_elim)
    apply (rule norm_triangle_le)
    by linarith
  done

theorem laplace_transform_unique:
  assumes f: "\<And>s. Re s > a \<Longrightarrow> (f has_laplace F) s"
  assumes g: "\<And>s. Re s > b \<Longrightarrow> (g has_laplace F) s"
  assumes [continuous_intros]: "continuous_on {0..} f"
  assumes [continuous_intros]: "continuous_on {0..} g"
  assumes eof: "exponential_order M a f"
  assumes eog: "exponential_order N b g"
  assumes "t \<ge> 0"
  shows "f t = g t"
proof -
  define c where "c = max a b"
  define L where "L = max M N"
  from eof have eof: "exponential_order L c f"
    by (rule exponential_order_mono) (auto simp: L_def c_def)
  from eog have eog: "exponential_order L c (\<lambda>x. - g x)"
    unfolding exponential_order_uminus_iff
    by (rule exponential_order_mono) (auto simp: L_def c_def)
  from exponential_order_add[OF eof eog]
  have eom: "exponential_order (2 * L) c (\<lambda>x. f x - g x)"
    by simp
  have l0: "((\<lambda>x. f x - g x) has_laplace 0) s" if "Re s > c" for s
    using has_laplace_minus[OF f g, of s] that by (simp add: c_def max_def split: if_splits)
  have "f t - g t = 0"
    by (rule laplace_transform_zero[OF _ eom l0 \<open>t \<ge> 0\<close>])
      (auto intro!: continuous_intros)
  then show ?thesis by simp
qed

end