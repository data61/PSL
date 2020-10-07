(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

theory Lp
imports Functional_Spaces
begin

text \<open>The material in this file is essentially of analytic nature. However, one of the central
proofs (the proof of Holder inequality below) uses a probability space, and Jensen's inequality
there. Hence, we need to import \verb+Probability+. Moreover, we use several lemmas from
\verb+SG_Library_Complement+.\<close>


section \<open>Conjugate exponents\<close>

text \<open>Two numbers $p$ and $q$ are \emph{conjugate} if $1/p + 1/q = 1$. This relation keeps
appearing in the theory of $L^p$ spaces, as the dual of $L^p$ is $L^q$ where $q$ is the conjugate
of $p$. This relation makes sense for real numbers, but also for ennreals
(where the case $p=1$ and $q=\infty$ is most important). Unfortunately, manipulating the
previous relation with ennreals is tedious as there is no good simproc involving addition and
division there. To mitigate this difficulty, we prove once and for all most useful properties
of such conjugates exponents in this paragraph.\<close>

lemma Lp_cases_1_PInf:
  assumes "p \<ge> (1::ennreal)"
  obtains (gr) p2 where "p = ennreal p2" "p2 > 1" "p > 1"
    | (one) "p = 1"
    | (PInf) "p = \<infinity>"
using assms by (metis (full_types) antisym_conv ennreal_cases ennreal_le_1 infinity_ennreal_def not_le)

lemma Lp_cases:
  obtains (real_pos) p2 where "p = ennreal p2" "p2 > 0" "p > 0"
    | (zero) "p = 0"
    | (PInf) "p = \<infinity>"
by (metis enn2real_positive_iff ennreal_enn2real_if infinity_ennreal_def not_gr_zero top.not_eq_extremum)

definition
  "conjugate_exponent p = 1 + 1/(p-1)"

lemma conjugate_exponent_real:
  assumes "p > (1::real)"
  shows "1/p + 1/(conjugate_exponent p) = 1"
        "conjugate_exponent p > 1"
        "conjugate_exponent(conjugate_exponent p) = p"
        "(p-1) * conjugate_exponent p = p"
        "p - p / conjugate_exponent p = 1"
unfolding conjugate_exponent_def using assms by (auto simp add: algebra_simps divide_simps)

lemma conjugate_exponent_real_iff:
  assumes "p > (1::real)"
  shows "q = conjugate_exponent p \<longleftrightarrow> (1/p + 1/q = 1)"
unfolding conjugate_exponent_def using assms by (auto simp add: algebra_simps divide_simps)

lemma conjugate_exponent_real_2 [simp]:
  "conjugate_exponent (2::real) = 2"
  unfolding conjugate_exponent_def by (auto simp add: algebra_simps divide_simps)

lemma conjugate_exponent_realI:
  assumes "p > (0::real)" "q > 0" "1/p + 1/q = 1"
  shows "p > 1" "q = conjugate_exponent p" "q > 1" "p = conjugate_exponent q"
unfolding conjugate_exponent_def using assms apply (auto simp add: algebra_simps divide_simps)
apply (metis assms(3) divide_less_eq_1_pos less_add_same_cancel1 zero_less_divide_1_iff)
using mult_less_cancel_left_pos by fastforce


lemma conjugate_exponent_real_ennreal:
  assumes "p> (1::real)"
  shows "conjugate_exponent(ennreal p) = ennreal(conjugate_exponent p)"
unfolding conjugate_exponent_def using assms
by (auto, metis diff_gt_0_iff_gt divide_ennreal ennreal_1 ennreal_minus zero_le_one)

lemma conjugate_exponent_ennreal_1_2_PInf [simp]:
  "conjugate_exponent (1::ennreal) = \<infinity>"
  "conjugate_exponent (\<infinity>::ennreal) = 1"
  "conjugate_exponent (\<top>::ennreal) = 1"
  "conjugate_exponent (2::ennreal) = 2"
using conjugate_exponent_real_ennreal[of 2] by (auto simp add: conjugate_exponent_def)

lemma conjugate_exponent_ennreal:
  assumes "p \<ge> (1::ennreal)"
  shows "1/p + 1/(conjugate_exponent p) = 1"
        "conjugate_exponent p \<ge> 1"
        "conjugate_exponent(conjugate_exponent p) = p"
proof -
  have "(1/p + 1/(conjugate_exponent p) = 1) \<and> (conjugate_exponent p \<ge> 1) \<and> conjugate_exponent(conjugate_exponent p) = p"
  using \<open>p \<ge> 1\<close> proof (cases rule: Lp_cases_1_PInf)
    case (gr p2)
    then have *: "conjugate_exponent p = ennreal (conjugate_exponent p2)" using conjugate_exponent_real_ennreal[OF \<open>p2 > 1\<close>] by auto
    have a: "conjugate_exponent p \<ge> 1" using * conjugate_exponent_real[OF \<open>p2 > 1\<close>] by auto
    have b: "conjugate_exponent(conjugate_exponent p) = p"
      using conjugate_exponent_real(3)[OF \<open>p2 > 1\<close>] conjugate_exponent_real_ennreal[OF \<open>p2 > 1\<close>]
      conjugate_exponent_real_ennreal[OF conjugate_exponent_real(2)[OF \<open>p2 > 1\<close>]] unfolding * \<open>p = ennreal p2\<close> by auto
    have "1 / p + 1 / conjugate_exponent p = ennreal(1/p2 + 1/(conjugate_exponent p2))" unfolding * unfolding \<open>p = ennreal p2\<close>
      using conjugate_exponent_real(2)[OF \<open>p2 > 1\<close>] \<open>p2 > 1\<close>
      apply (subst ennreal_plus, auto) apply (subst divide_ennreal[symmetric], auto)
      using divide_ennreal_def inverse_ennreal inverse_eq_divide by auto
    then have c: "1 / p + 1 / conjugate_exponent p = 1" using conjugate_exponent_real[OF \<open>p2 > 1\<close>] by auto
    show ?thesis using a b c by simp
  qed (auto)
  then show "1/p + 1/(conjugate_exponent p) = 1"
            "conjugate_exponent p \<ge> 1"
            "conjugate_exponent(conjugate_exponent p) = p"
    by auto
qed

lemma conjugate_exponent_ennreal_iff:
  assumes "p \<ge> (1::ennreal)"
  shows "q = conjugate_exponent p \<longleftrightarrow> (1/p + 1/q = 1)"
using conjugate_exponent_ennreal[OF assms]
by (auto, metis ennreal_add_diff_cancel_left ennreal_add_eq_top ennreal_top_neq_one one_divide_one_divide_ennreal)

lemma conjugate_exponent_ennrealI:
  assumes "1/p + 1/q = (1::ennreal)"
  shows "p \<ge> 1" "q \<ge> 1" "p = conjugate_exponent q" "q = conjugate_exponent p"
proof -
  have "1/p \<le> 1" using assms using le_iff_add by fastforce
  then show "p \<ge> 1"
    by (metis assms divide_ennreal_def ennreal_add_eq_top ennreal_divide_self ennreal_divide_zero ennreal_le_epsilon ennreal_one_neq_top mult.left_neutral mult_left_le zero_le)
  then show "q = conjugate_exponent p" using conjugate_exponent_ennreal_iff assms by auto
  then show "q \<ge> 1" using conjugate_exponent_ennreal[OF \<open>p \<ge> 1\<close>] by auto
  show "p = conjugate_exponent q"
    using conjugate_exponent_ennreal_iff[OF \<open>q\<ge>1\<close>, of p] assms by (simp add: add.commute)
qed


section \<open>Convexity inequalities and integration\<close>

text \<open>In this paragraph, we describe the basic inequalities relating the integral of a function
and of its $p$-th power, for $p > 0$. These inequalities imply in particular that the $L^p$ norm
satisfies the triangular inequality, a feature we will need when defining the $L^p$ spaces below.
In particular, we prove the Hölder and Minkowski inequalities. The Hölder inequality,
especially, is the basis of all further inequalities for $L^p$ spaces.
\<close>

lemma (in prob_space) bound_L1_Lp:
  assumes "p \<ge> (1::real)"
          "f \<in> borel_measurable M"
          "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "integrable M f"
        "abs(\<integral>x. f x \<partial>M) powr p \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M)"
        "abs(\<integral>x. f x \<partial>M) \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
proof -
  have *: "norm x \<le> 1 + (norm x) powr p" for x::real
    apply (cases "norm x \<le> 1")
    apply (meson le_add_same_cancel1 order.trans powr_ge_pzero)
    apply (metis add_le_same_cancel2 assms(1) less_le_trans linear not_less not_one_le_zero powr_le_cancel_iff powr_one_gt_zero_iff)
    done
  show *: "integrable M f"
    apply (rule Bochner_Integration.integrable_bound[of _ "\<lambda>x. 1 + \<bar>f x\<bar> powr p"], auto simp add: assms) using * by auto
  show "abs(\<integral>x. f x \<partial>M) powr p \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M)"
    by (rule jensens_inequality[OF * _ _ assms(3) convex_abs_powr[OF \<open>p \<ge> 1\<close>]], auto)
  then have "(abs(\<integral>x. f x \<partial>M) powr p) powr (1/p) \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
    using assms(1) powr_mono2 by auto
  then show "abs(\<integral>x. f x \<partial>M) \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
    using \<open>p \<ge> 1\<close> by (auto simp add: powr_powr)
qed


theorem Holder_inequality:
  assumes "p > (0::real)" "q > 0" "1/p + 1/q = 1"
      and [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
          "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
          "integrable M (\<lambda>x. \<bar>g x\<bar> powr q)"
  shows "integrable M (\<lambda>x. f x * g x)"
        "(\<integral>x. \<bar>f x * g x\<bar> \<partial>M) \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) * (\<integral>x. \<bar>g x\<bar> powr q \<partial>M) powr (1/q)"
        "abs(\<integral>x. f x * g x \<partial>M) \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) * (\<integral>x. \<bar>g x\<bar> powr q \<partial>M) powr (1/q)"
proof -
  have "p > 1" using conjugate_exponent_realI(1)[OF \<open>p>0\<close> \<open>q>0\<close> \<open>1/p+1/q=1\<close>].

  have *: "x * y \<le> x powr p + y powr q" if "x \<ge> 0" "y \<ge> 0" for x y
  proof -
    have "x * y = (x powr p) powr (1/p) * (y powr q) powr (1/q)"
      using \<open>p > 0\<close> \<open>q > 0\<close> powr_powr that(1) that(2) by auto
    also have "... \<le> (max (x powr p) (y powr q)) powr (1/p) * (max (x powr p) (y powr q)) powr (1/q)"
      apply (rule mult_mono, auto) using assms(1) assms(2) powr_mono2 by auto
    also have "... = max (x powr p) (y powr q)"
      by (metis max_def mult.right_neutral powr_add powr_powr assms(3))
    also have "... \<le> x powr p + y powr q"
      by auto
    finally show ?thesis by simp
  qed
  show [simp]: "integrable M (\<lambda>x. f x * g x)"
    apply (rule Bochner_Integration.integrable_bound[of _ "\<lambda>x. \<bar>f x\<bar> powr p + \<bar>g x\<bar> powr q"], auto)
    by (rule Bochner_Integration.integrable_add, auto simp add: assms * abs_mult)

  text \<open>The proof of the main inequality is done by applying the inequality
        $(\int |h| d\mu \leq \int |h|^p d\mu)^{1/p}$ to the right function $h$ in the right
        probability space. One should take $h = f \cdot |g|^{1-q}$, and $d\mu = |g|^q dM / I$,
        where $I = \int |g|^q$. This readily gives the result.\<close>

  show *: "(\<integral>x. \<bar>f x * g x\<bar> \<partial>M) \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) * (\<integral>x. \<bar>g x\<bar> powr q \<partial>M) powr (1/q)"
  proof (cases "(\<integral>x. \<bar>g x\<bar> powr q \<partial>M) = 0")
    case True
    then have "AE x in M. \<bar>g x\<bar> powr q = 0"
      by (subst integral_nonneg_eq_0_iff_AE[symmetric], auto simp add: assms)
    then have *: "AE x in M. f x * g x = 0"
      using \<open>q > 0\<close> by auto
    have "(\<integral>x. \<bar>f x * g x\<bar> \<partial>M) = (\<integral>x. 0 \<partial>M)"
      apply (rule integral_cong_AE) using * by auto
    then show ?thesis by auto
  next
    case False
    moreover have "(\<integral>x. \<bar>g x\<bar> powr q \<partial>M) \<ge> (\<integral>x. 0 \<partial>M)" by (rule integral_mono, auto simp add: assms)
    ultimately have *: "(\<integral>x. \<bar>g x\<bar> powr q \<partial>M) > 0" by (simp add: le_less)
    define I where "I = (\<integral>x. \<bar>g x\<bar> powr q \<partial>M)"
    have [simp]: "I > 0" unfolding I_def using * by auto
    define M2 where "M2 = density M (\<lambda>x. \<bar>g x\<bar> powr q / I)"
    interpret prob_space M2
      apply (standard, unfold M2_def, auto, subst emeasure_density, auto)
      apply (subst divide_ennreal[symmetric], auto, subst nn_integral_divide, auto)
      apply (subst nn_integral_eq_integral, auto simp add: assms, unfold I_def)
      using * by auto

    have [simp]: "p \<ge> 1" "p \<ge> 0" using \<open>p > 1\<close> by auto
    have A: "q + (1 - q) * p = 0" using assms by (auto simp add: divide_simps algebra_simps)
    have B: "1 - 1/p = 1/q" using \<open>1/p + 1/q = 1\<close> by auto
    define f2 where "f2 = (\<lambda>x. f x * indicator {y\<in> space M. g y \<noteq> 0} x)"
    have [measurable]: "f2 \<in> borel_measurable M" unfolding f2_def by auto
    define h where "h = (\<lambda>x. \<bar>f2 x\<bar> * \<bar>g x\<bar> powr (1-q))"
    have [measurable]: "h \<in> borel_measurable M" unfolding h_def by auto
    have [measurable]: "h \<in> borel_measurable M2" unfolding M2_def by auto

    have Eq: "(\<bar>g x\<bar> powr q / I) *\<^sub>R \<bar>h x\<bar> powr p = \<bar>f2 x\<bar> powr p / I" for x
      apply (insert \<open>I>0\<close>, auto simp add: divide_simps, unfold h_def)
      apply (auto simp add: divide_nonneg_pos divide_simps powr_mult powr_powr powr_add[symmetric] A)
      unfolding f2_def by auto
    have "integrable M2 (\<lambda>x. \<bar>h x\<bar> powr p)"
      unfolding M2_def apply (subst integrable_density, simp, simp, simp add: divide_simps)
      apply (subst Eq, rule integrable_divide, rule Bochner_Integration.integrable_bound[of _ "\<lambda>x. \<bar>f x\<bar> powr p"], unfold f2_def)
      by (unfold indicator_def, auto simp add: \<open>integrable M (\<lambda>x. \<bar>f x\<bar> powr p)\<close>)
    then have "integrable M2 (\<lambda>x. \<bar>h x\<bar>)"
      by (metis bound_L1_Lp(1) \<open>random_variable borel h\<close> \<open>p > 1\<close> integrable_abs le_less)

    have "(\<integral>x. \<bar>h x\<bar> powr p \<partial>M2) = (\<integral>x. (\<bar>g x\<bar> powr q / I) *\<^sub>R (\<bar>h x\<bar> powr p) \<partial>M)"
      unfolding M2_def by (rule integral_density[of "\<lambda>x. \<bar>h x\<bar> powr p" M "\<lambda>x. \<bar>g x\<bar> powr q / I"], auto simp add: divide_simps)
    also have "... = (\<integral>x. \<bar>f2 x\<bar> powr p / I \<partial>M)"
      apply (rule Bochner_Integration.integral_cong) using Eq by auto
    also have "... \<le> (\<integral>x. \<bar>f x\<bar> powr p / I \<partial>M)"
      apply (rule integral_mono', rule integrable_divide[OF \<open>integrable M (\<lambda>x. \<bar>f x\<bar> powr p)\<close>])
      unfolding f2_def indicator_def using \<open>I > 0\<close> by (auto simp add: divide_simps)
    finally have C: "(\<integral>x. \<bar>h x\<bar> powr p \<partial>M2) \<le> (\<integral>x. \<bar>f x\<bar> powr p / I \<partial>M)" by simp

    have "(\<integral>x. \<bar>f x * g x\<bar> \<partial>M) / I = (\<integral>x. \<bar>f x * g x\<bar> / I \<partial>M)"
      by auto
    also have "... = (\<integral>x. \<bar>f2 x * g x\<bar> / I \<partial>M)"
      by (auto simp add: divide_simps, rule Bochner_Integration.integral_cong, unfold f2_def indicator_def, auto)
    also have "... = (\<integral>x. \<bar>h x\<bar> \<partial>M2)"
      apply (unfold M2_def, subst integral_density, simp, simp, simp add: divide_simps)
      by (rule Bochner_Integration.integral_cong, unfold h_def, auto simp add: divide_simps algebra_simps powr_add[symmetric] abs_mult)
    also have "... \<le> abs (\<integral>x. \<bar>h x\<bar> \<partial>M2)"
      by auto
    also have "... \<le> (\<integral>x. abs(\<bar>h x\<bar>) powr p \<partial>M2) powr (1/p)"
      apply (rule bound_L1_Lp(3)[of p "\<lambda>x. \<bar>h x\<bar>"])
      by (auto simp add: \<open>integrable M2 (\<lambda>x. \<bar>h x\<bar> powr p)\<close>)
    also have "... \<le> (\<integral>x. \<bar>f x\<bar> powr p / I \<partial>M) powr (1/p)"
      by (rule powr_mono2, insert C, auto)
    also have "... \<le> ((\<integral>x. \<bar>f x\<bar> powr p \<partial>M) / I) powr (1/p)"
      apply (rule powr_mono2, auto simp add: divide_simps) using \<open>p \<ge> 0\<close> by auto
    also have "... = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) * I powr(-1/p)"
      by (auto simp add: less_imp_le powr_divide powr_minus_divide)
    finally have "(\<integral>x. \<bar>f x * g x\<bar> \<partial>M) \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) * I * I powr(-1/p)"
      by (auto simp add: divide_simps algebra_simps)
    also have "... = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) * I powr (1-1/p)"
      by (auto simp add: powr_mult_base less_imp_le)
    also have "... = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) * (\<integral>x. \<bar>g x\<bar> powr q \<partial>M) powr (1/q)"
      unfolding I_def using B by auto
    finally show ?thesis
      by simp
  qed
  have "abs(\<integral>x. f x * g x \<partial>M) \<le> (\<integral>x. \<bar>f x * g x\<bar> \<partial>M)" by auto
  then show "abs(\<integral>x. f x * g x \<partial>M) \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) * (\<integral>x. \<bar>g x\<bar> powr q \<partial>M) powr (1/q)"
    using * by linarith
qed

theorem Minkowski_inequality:
  assumes "p \<ge> (1::real)"
      and [measurable, simp]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
          "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
          "integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
  shows "integrable M (\<lambda>x. \<bar>f x + g x\<bar> powr p)"
        "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1/p)
          \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) + (\<integral>x. \<bar>g x\<bar> powr p \<partial>M) powr (1/p)"
proof -
  have *: "\<bar>x + y\<bar> powr p \<le> 2 powr p * (\<bar>x\<bar> powr p + \<bar>y\<bar> powr p)" for x y::real
  proof -
    have "\<bar>x + y\<bar> \<le> \<bar>x\<bar> + \<bar>y\<bar>" by auto
    also have "... \<le> (max \<bar>x\<bar> \<bar>y\<bar>) + max \<bar>x\<bar> \<bar>y\<bar>" by auto
    also have "... = 2 * max \<bar>x\<bar> \<bar>y\<bar>" by auto
    finally have "\<bar>x + y\<bar> powr p \<le> (2 * max \<bar>x\<bar> \<bar>y\<bar>) powr p"
      using powr_mono2 \<open>p \<ge> 1\<close> by auto
    also have "... = 2 powr p * (max \<bar>x\<bar> \<bar>y\<bar>) powr p"
      using powr_mult by auto
    also have "... \<le> 2 powr p * (\<bar>x\<bar> powr p + \<bar>y\<bar> powr p)"
      unfolding max_def by auto
    finally show ?thesis by simp
  qed
  show [simp]: "integrable M (\<lambda>x. \<bar>f x + g x\<bar> powr p)"
    by (rule Bochner_Integration.integrable_bound[of _ "\<lambda>x. 2 powr p * (\<bar>f x\<bar> powr p + \<bar>g x\<bar> powr p)"], auto simp add: *)

  show "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1/p) \<le> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) + (\<integral>x. \<bar>g x\<bar> powr p \<partial>M) powr (1/p)"
  proof (cases "p=1")
    case True
    then show ?thesis
      apply (auto, subst Bochner_Integration.integral_add[symmetric], insert assms(4) assms(5), simp, simp)
      by (rule integral_mono', auto)
  next
    case False
    then have [simp]: "p > 1" "p \<ge> 1" "p > 0" "p \<noteq> 0" using assms(1) by auto
    define q where "q = conjugate_exponent p"
    have [simp]: "q > 1" "q > 0" "1/p + 1/q = 1" "(p-1) * q = p"
      unfolding q_def using conjugate_exponent_real[OF \<open>p>1\<close>] by auto
    then have [simp]: "(z powr (p-1)) powr q = z powr p" for z
      by (simp add: powr_powr)
    have "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) = (\<integral>x. \<bar>f x + g x\<bar> * \<bar>f x + g x\<bar> powr (p-1) \<partial>M)"
      by (subst powr_mult_base, auto)
    also have "... \<le> (\<integral>x. \<bar>f x\<bar> * \<bar>f x + g x\<bar> powr (p-1) + \<bar>g x\<bar> * \<bar>f x + g x\<bar> powr (p-1) \<partial>M)"
      apply (rule integral_mono', rule Bochner_Integration.integrable_add)
      apply (rule Holder_inequality(1)[of p q], auto)
      apply (rule Holder_inequality(1)[of p q], auto)
      by (metis abs_ge_zero abs_triangle_ineq comm_semiring_class.distrib le_less mult_mono' powr_ge_pzero)
    also have "... = (\<integral>x. \<bar>f x\<bar> * \<bar>f x + g x\<bar> powr (p-1) \<partial>M) + (\<integral>x. \<bar>g x\<bar> * \<bar>f x + g x\<bar> powr (p-1) \<partial>M)"
      apply (rule Bochner_Integration.integral_add) by (rule Holder_inequality(1)[of p q], auto)+
    also have "... \<le> abs (\<integral>x. \<bar>f x\<bar> * \<bar>f x + g x\<bar> powr (p-1) \<partial>M) + abs (\<integral>x. \<bar>g x\<bar> * \<bar>f x + g x\<bar> powr (p-1) \<partial>M)"
      by auto
    also have "... \<le> (\<integral>x. abs(\<bar>f x\<bar>) powr p \<partial>M) powr (1/p) * (\<integral>x. abs(\<bar>f x + g x\<bar> powr (p-1)) powr q \<partial>M) powr (1/q)
                      + (\<integral>x. abs(\<bar>g x\<bar>) powr p \<partial>M) powr (1/p) * (\<integral>x. abs(\<bar>f x + g x\<bar> powr (p-1)) powr q \<partial>M) powr (1/q)"
      apply (rule add_mono)
      apply (rule Holder_inequality(3)[of p q], simp, simp, simp, simp, simp, simp, simp)
      apply (rule Holder_inequality(3)[of p q], simp, simp, simp, simp, simp, simp, simp)
      done
    also have "... = (\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1/q) *
            ((\<integral>x. abs(\<bar>f x\<bar>) powr p \<partial>M) powr (1/p) + (\<integral>x. abs(\<bar>g x\<bar>) powr p \<partial>M) powr (1/p))"
      by (auto simp add: algebra_simps)
    finally have *: "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) \<le> (\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1/q) *
        ((\<integral>x. abs(\<bar>f x\<bar>) powr p \<partial>M) powr (1/p) + (\<integral>x. abs(\<bar>g x\<bar>) powr p \<partial>M) powr (1/p))"
      by simp
    show ?thesis
    proof (cases "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) = 0")
      case True
      then show ?thesis by auto
    next
      case False
      then have **: "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1/q) > 0"
        by auto
      have "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1/q) * (\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1/p)
              = (\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M)"
        by (auto simp add: powr_add[symmetric] add.commute)
      then have "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1/q) * (\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1/p) \<le>
              (\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1/q) *
              ((\<integral>x. abs(\<bar>f x\<bar>) powr p \<partial>M) powr (1/p) + (\<integral>x. abs(\<bar>g x\<bar>) powr p \<partial>M) powr (1/p))"
        using * by auto
      then show ?thesis using ** by auto
    qed
  qed
qed

text \<open>When $p<1$, the function $x \mapsto |x|^p$ is not convex any more. Hence, the $L^p$ ``norm''
is not a norm any more, but a quasinorm. This is proved using a different convexity argument, as
follows.\<close>

theorem Minkowski_inequality_le_1:
  assumes "p > (0::real)" "p \<le> 1"
      and [measurable, simp]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
          "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
          "integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
  shows "integrable M (\<lambda>x. \<bar>f x + g x\<bar> powr p)"
        "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1/p)
          \<le> 2 powr (1/p-1) * (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) + 2 powr (1/p-1) * (\<integral>x. \<bar>g x\<bar> powr p \<partial>M) powr (1/p)"
proof -
  have *: "\<bar>a + b\<bar> powr p \<le> \<bar>a\<bar> powr p + \<bar>b\<bar> powr p" for a b
    using x_plus_y_p_le_xp_plus_yp[OF \<open>p > 0\<close> \<open>p \<le> 1\<close>, of "\<bar>a\<bar>" "\<bar>b\<bar>"]
    by (auto, meson abs_ge_zero abs_triangle_ineq assms(1) le_less order.trans powr_mono2)
  show "integrable M (\<lambda>x. \<bar>f x + g x\<bar> powr p)"
    by (rule Bochner_Integration.integrable_bound[of _ "\<lambda>x. \<bar>f x\<bar> powr p + \<bar>g x\<bar> powr p"], auto simp add: *)

  have "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1/p) \<le> (\<integral>x. \<bar>f x\<bar> powr p + \<bar>g x\<bar> powr p \<partial>M) powr (1/p)"
    by (rule powr_mono2, simp add: \<open>p > 0\<close> less_imp_le, simp, rule integral_mono', auto simp add: *)
  also have "... = 2 powr (1/p) * (((\<integral>x. \<bar>f x\<bar> powr p \<partial>M) + (\<integral>x. \<bar>g x\<bar> powr p \<partial>M)) / 2) powr (1/p)"
    by (auto simp add: powr_mult[symmetric] add_divide_distrib)
  also have "... \<le> 2 powr (1/p) * (((\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) + (\<integral>x. \<bar>g x\<bar> powr p \<partial>M) powr (1/p)) / 2)"
    apply (rule mult_mono, simp, rule convex_on_mean_ineq[OF convex_powr[of "1/p"]])
    using \<open>p \<le> 1\<close> \<open>p > 0\<close> by auto
  also have "... = 2 powr (1/p - 1) * ((\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) + (\<integral>x. \<bar>g x\<bar> powr p \<partial>M) powr (1/p))"
    by (simp add: powr_diff)
  finally show "(\<integral>x. \<bar>f x + g x\<bar> powr p \<partial>M) powr (1/p)
      \<le> 2 powr (1/p-1) * (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) + 2 powr (1/p-1) * (\<integral>x. \<bar>g x\<bar> powr p \<partial>M) powr (1/p)"
    by (auto simp add: algebra_simps)
qed


section \<open>$L^p$ spaces\<close>

text \<open>We define $L^p$ spaces by giving their defining quasinorm. It is a norm for $p\in [1, \infty]$,
and a quasinorm for $p \in (0,1)$. The construction of a quasinorm from a formula only makes sense
if this formula is indeed a quasinorm, i.e., it is homogeneous and satisfies the triangular
inequality with the given multiplicative defect. Thus, we have to show that this is indeed
the case to be able to use the definition.\<close>

definition Lp_space::"ennreal \<Rightarrow> 'a measure \<Rightarrow> ('a \<Rightarrow> real) quasinorm"
  where "Lp_space p M = (
    if p = 0 then quasinorm_of (1, (\<lambda>f. if (f \<in> borel_measurable M) then 0 else \<infinity>))
    else if p < \<infinity> then quasinorm_of (
        if p < 1 then 2 powr (1/enn2real p - 1) else 1,
        (\<lambda>f. if (f \<in> borel_measurable M \<and> integrable M (\<lambda>x. \<bar>f x\<bar> powr (enn2real p)))
              then (\<integral>x. \<bar>f x\<bar> powr (enn2real p) \<partial>M) powr (1/(enn2real p))
              else (\<infinity>::ennreal)))
    else quasinorm_of (1, (\<lambda>f. if f \<in> borel_measurable M then esssup M (\<lambda>x. ereal \<bar>f x\<bar>) else (\<infinity>::ennreal))))"

abbreviation "\<LL> == Lp_space"


subsection \<open>$L^\infty$\<close>

text \<open>Let us check that, for $L^\infty$, the above definition makes sense.\<close>

lemma L_infinity:
  "eNorm (\<LL> \<infinity> M) f = (if f \<in> borel_measurable M then esssup M (\<lambda>x. ereal \<bar>f x\<bar>) else (\<infinity>::ennreal))"
  "defect (\<LL> \<infinity> M) = 1"
proof -
  have T: "esssup M (\<lambda>x. ereal \<bar>(f + g) x\<bar>) \<le> e2ennreal (esssup M (\<lambda>x. ereal \<bar>f x\<bar>)) + esssup M (\<lambda>x. ereal \<bar>g x\<bar>)"
    if [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M" for f g
  proof (cases "emeasure M (space M) = 0")
    case True
    then have "e2ennreal (esssup M (\<lambda>x. ereal \<bar>(f + g) x\<bar>)) = 0"
      using esssup_zero_space[OF True] by (simp add: e2ennreal_neg)
    then show ?thesis by simp
  next
    case False
    have *: "esssup M (\<lambda>x. \<bar>h x\<bar>) \<ge> 0" for h::"'a \<Rightarrow> real"
    proof -
      have "esssup M (\<lambda>x. 0) \<le> esssup M (\<lambda>x. \<bar>h x\<bar>)" by (rule esssup_mono, auto)
      then show ?thesis using esssup_const[OF False, of "0::ereal"] by simp
    qed
    have "esssup M (\<lambda>x. ereal \<bar>(f + g) x\<bar>) \<le> esssup M (\<lambda>x. ereal \<bar>f x\<bar> + ereal \<bar>g x\<bar>)"
      by (rule esssup_mono, auto simp add: plus_fun_def)
    also have "... \<le> esssup M (\<lambda>x. ereal \<bar>f x\<bar>) + esssup M (\<lambda>x. ereal \<bar>g x\<bar>)"
      by (rule esssup_add)
    finally show ?thesis
      using * by (simp add: e2ennreal_mono eq_onp_def plus_ennreal.abs_eq)
  qed

  have H: "esssup M (\<lambda>x. ereal \<bar>(c *\<^sub>R f) x\<bar>) \<le> ennreal \<bar>c\<bar> * esssup M (\<lambda>x. ereal \<bar>f x\<bar>)" if "c \<noteq> 0" for f c
  proof -
    have "abs c > 0" "ereal \<bar>c\<bar> \<ge> 0" using that by auto
    have *: "esssup M (\<lambda>x. abs(c *\<^sub>R f x)) = abs c * esssup M (\<lambda>x. \<bar>f x\<bar>)"
      apply (subst esssup_cmult[OF \<open>abs c > 0\<close>, of M "\<lambda>x. ereal \<bar>f x\<bar>", symmetric])
      using times_ereal.simps(1) by (auto simp add: abs_mult)
    show ?thesis
      unfolding e2ennreal_mult[OF \<open>ereal \<bar>c\<bar> \<ge> 0\<close>] * scaleR_fun_def
      using ennreal.abs_eq ennreal.rep_eq by auto
  qed

  have "esssup M (\<lambda>x. ereal 0) \<le> 0" using esssup_I by auto
  then have Z: "e2ennreal (esssup M (\<lambda>x. ereal 0)) = 0" using e2ennreal_neg by auto

  have *: "quasinorm_on (borel_measurable M) 1 (\<lambda>(f::'a\<Rightarrow>real). e2ennreal(esssup M (\<lambda>x. ereal \<bar>f x\<bar>)))"
    apply (rule quasinorm_onI) using T H Z by auto
  have **: "quasinorm_on UNIV 1 (\<lambda>(f::'a\<Rightarrow>real). if f \<in> borel_measurable M then e2ennreal(esssup M (\<lambda>x. ereal \<bar>f x\<bar>)) else \<infinity>)"
    by (rule extend_quasinorm[OF *])
  show "eNorm (\<LL> \<infinity> M) f = (if f \<in> borel_measurable M then e2ennreal(esssup M (\<lambda>x. \<bar>f x\<bar>)) else \<infinity>)"
       "defect (\<LL> \<infinity> M) = 1"
    unfolding Lp_space_def using quasinorm_of[OF **] by auto
qed

lemma L_infinity_space:
  "space\<^sub>N (\<LL> \<infinity> M) = {f \<in> borel_measurable M. \<exists>C. AE x in M. \<bar>f x\<bar> \<le> C}"
proof (auto simp del: infinity_ennreal_def)
  fix f assume H: "f \<in> space\<^sub>N (\<LL> \<infinity> M)"
  then show "f \<in> borel_measurable M"
    unfolding space\<^sub>N_def using L_infinity(1)[of M] top.not_eq_extremum by fastforce
  then have *: "esssup M (\<lambda>x. \<bar>f x\<bar>) < \<infinity>"
    using H unfolding space\<^sub>N_def L_infinity(1)[of M] by (auto simp add: e2ennreal_infty)
  define C where "C = real_of_ereal(esssup M (\<lambda>x. \<bar>f x\<bar>))"
  have "AE x in M. ereal \<bar>f x\<bar> \<le> ereal C"
  proof (cases "emeasure M (space M) = 0")
    case True
    then show ?thesis using emeasure_0_AE by simp
  next
    case False
    then have "esssup M (\<lambda>x. \<bar>f x\<bar>) \<ge> 0"
      using esssup_mono[of "\<lambda>x. 0" M "(\<lambda>x. \<bar>f x\<bar>)"] esssup_const[OF False, of "0::ereal"] by auto
    then have "esssup M (\<lambda>x. \<bar>f x\<bar>) = ereal C" unfolding C_def using * ereal_real by auto
    then show ?thesis using esssup_AE[of "(\<lambda>x. ereal \<bar>f x\<bar>)" M] by simp
  qed
  then have "AE x in M. \<bar>f x\<bar> \<le> C" by auto
  then show "\<exists>C. AE x in M. \<bar>f x\<bar> \<le> C" by blast
next
  fix f::"'a \<Rightarrow> real" and C::real
  assume H: "f \<in> borel_measurable M" "AE x in M. \<bar>f x\<bar> \<le> C"
  then have "esssup M (\<lambda>x. \<bar>f x\<bar>) \<le> C" using esssup_I by auto
  then have "eNorm (\<LL> \<infinity> M) f \<le> C" unfolding L_infinity(1) using H(1)
    by (auto, metis antisym e2ennreal_mono enn2ereal_ennreal ennreal.abs_eq ennreal.rep_eq ennreal_eq_0_iff ereal_less_eq(4) linear order.trans zero_ereal_def)
  then show "f \<in> space\<^sub>N (\<LL> \<infinity> M)"
    using spaceN_iff le_less_trans by fastforce
qed

lemma L_infinity_zero_space:
  "zero_space\<^sub>N (\<LL> \<infinity> M) = {f \<in> borel_measurable M. AE x in M. f x = 0}"
proof (auto simp del: infinity_ennreal_def)
  fix f assume H: "f \<in> zero_space\<^sub>N (\<LL> \<infinity> M)"
  then show "f \<in> borel_measurable M"
    unfolding zero_space\<^sub>N_def using L_infinity(1)[of M] top.not_eq_extremum by fastforce
  then have *: "e2ennreal(esssup M (\<lambda>x. \<bar>f x\<bar>)) = 0"
    using H unfolding zero_space\<^sub>N_def using L_infinity(1)[of M] e2ennreal_infty by auto
  then have "esssup M (\<lambda>x. \<bar>f x\<bar>) \<le> 0"
    by (metis e2ennreal_infty e2ennreal_mult ennreal_top_neq_zero ereal_mult_infty leI linear mult_zero_left)
  then have "f x = 0" if "ereal \<bar>f x\<bar> \<le> esssup M (\<lambda>x. \<bar>f x\<bar>)" for x
    using that order.trans by fastforce
  then show "AE x in M. f x = 0" using esssup_AE[of "\<lambda>x. ereal \<bar>f x\<bar>" M] by auto
next
  fix f::"'a \<Rightarrow> real"
  assume H: "f \<in> borel_measurable M" "AE x in M. f x = 0"
  then have "esssup M (\<lambda>x. \<bar>f x\<bar>) \<le> 0" using esssup_I by auto
  then have "eNorm (\<LL> \<infinity> M) f = 0" unfolding L_infinity(1) using H(1)
    by (simp add: e2ennreal_neg)
  then show "f \<in> zero_space\<^sub>N (\<LL> \<infinity> M)"
    using zero_spaceN_iff by auto
qed

lemma L_infinity_AE_ebound:
  "AE x in M. ennreal \<bar>f x\<bar> \<le> eNorm (\<LL> \<infinity> M) f"
proof (cases "f \<in> borel_measurable M")
  case False
  then have "eNorm (\<LL> \<infinity> M) f = \<infinity>"
    unfolding L_infinity(1) by auto
  then show ?thesis by simp
next
  case True
  then have "ennreal \<bar>f x\<bar> \<le> eNorm (\<LL> \<infinity> M) f" if "\<bar>f x\<bar> \<le> esssup M (\<lambda>x. \<bar>f x\<bar>)" for x
    unfolding L_infinity(1) using that e2ennreal_mono ennreal.abs_eq ennreal.rep_eq by fastforce
  then show ?thesis using esssup_AE[of "\<lambda>x. ereal \<bar>f x\<bar>"] by force
qed

lemma L_infinity_AE_bound:
  assumes "f \<in> space\<^sub>N (\<LL> \<infinity> M)"
  shows "AE x in M. \<bar>f x\<bar> \<le> Norm (\<LL> \<infinity> M) f"
using L_infinity_AE_ebound[of f M] unfolding eNorm_Norm[OF assms] by (simp)

text \<open>In the next lemma, the assumption $C \geq 0$ that might seem useless is in fact
necessary for the second statement when the space has zero measure. Indeed, any function is
then almost surely bounded by any constant!\<close>

lemma L_infinity_I:
  assumes "f \<in> borel_measurable M"
          "AE x in M. \<bar>f x\<bar> \<le> C"
          "C \<ge> 0"
  shows "f \<in> space\<^sub>N (\<LL> \<infinity> M)"
        "Norm (\<LL> \<infinity> M) f \<le> C"
proof -
  show "f \<in> space\<^sub>N (\<LL> \<infinity> M)"
    using L_infinity_space assms(1) assms(2) by force
  have "esssup M (\<lambda>x. \<bar>f x\<bar>) \<le> C" using assms(1) assms(2) esssup_I by auto
  then have "eNorm (\<LL> \<infinity> M) f \<le> ereal C"
    unfolding L_infinity(1) using assms(1) e2ennreal_mono by force
  then have "ennreal (Norm (\<LL> \<infinity> M) f) \<le> ennreal C"
    using eNorm_Norm[OF \<open>f \<in> space\<^sub>N (\<LL> \<infinity> M)\<close>] assms(3) ennreal.abs_eq ennreal.rep_eq by auto
  then show "Norm (\<LL> \<infinity> M) f \<le> C" using assms(3) by auto
qed

lemma L_infinity_I':
  assumes [measurable]: "f \<in> borel_measurable M"
      and "AE x in M. ennreal \<bar>f x\<bar> \<le> C"
  shows "eNorm (\<LL> \<infinity> M) f \<le> C"
proof -
  have "esssup M (\<lambda>x. \<bar>f x\<bar>) \<le> enn2ereal C"
    apply (rule esssup_I, auto) using assms(2) less_eq_ennreal.rep_eq by auto
  then show ?thesis unfolding L_infinity using assms apply auto
    using e2ennreal_mono by fastforce
qed

lemma L_infinity_pos_measure:
  assumes [measurable]: "f \<in> borel_measurable M"
      and "eNorm (\<LL> \<infinity> M) f > (C::real)"
  shows "emeasure M {x \<in> space M. \<bar>f x\<bar> > C} > 0"
proof -
  have *: "esssup M (\<lambda>x. ereal(\<bar>f x\<bar>)) > ereal C" using \<open>eNorm (\<LL> \<infinity> M) f > C\<close> unfolding L_infinity
  proof (auto)
    assume a1: "ennreal C < e2ennreal (esssup M (\<lambda>x. ereal \<bar>f x\<bar>))"
    have "\<not> e2ennreal (esssup M (\<lambda>a. ereal \<bar>f a\<bar>)) \<le> e2ennreal (ereal C)" if "\<not> C < 0"
      using a1 that by (metis (no_types) e2ennreal_enn2ereal enn2ereal_ennreal leD leI)
    then have "e2ennreal (esssup M (\<lambda>a. ereal \<bar>f a\<bar>)) \<le> e2ennreal (ereal C) \<longrightarrow> (\<exists>e\<le>esssup M (\<lambda>a. ereal \<bar>f a\<bar>). ereal C < e)"
      using a1 e2ennreal_neg by fastforce
    then show ?thesis
      by (meson e2ennreal_mono leI less_le_trans)
  qed
  have "emeasure M {x \<in> space M. ereal(\<bar>f x\<bar>) > C} > 0"
    by (rule esssup_pos_measure[OF _ *], auto)
  then show ?thesis by auto
qed

lemma L_infinity_tendsto_AE:
  assumes "tendsto_in\<^sub>N (\<LL> \<infinity> M) f g"
          "\<And>n. f n \<in> space\<^sub>N (\<LL> \<infinity> M)"
          "g \<in> space\<^sub>N (\<LL> \<infinity> M)"
  shows "AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> g x"
proof -
  have *: "AE x in M. \<bar>(f n - g) x\<bar> \<le> Norm (\<LL> \<infinity> M) (f n - g)" for n
    apply (rule L_infinity_AE_bound) using assms spaceN_diff by blast
  have "AE x in M. \<forall>n. \<bar>(f n - g) x\<bar> \<le> Norm (\<LL> \<infinity> M) (f n - g)"
    apply (subst AE_all_countable) using * by auto
  moreover have "(\<lambda>n. f n x) \<longlonglongrightarrow> g x" if "\<forall>n. \<bar>(f n - g) x\<bar> \<le> Norm (\<LL> \<infinity> M) (f n - g)" for x
  proof -
    have "(\<lambda>n. \<bar>(f n - g) x\<bar>) \<longlonglongrightarrow> 0"
      apply (rule tendsto_sandwich[of "\<lambda>n. 0" _ _ "\<lambda>n. Norm (\<LL> \<infinity> M) (f n - g)"])
      using that \<open>tendsto_in\<^sub>N (\<LL> \<infinity> M) f g\<close> unfolding tendsto_in\<^sub>N_def by auto
    then have "(\<lambda>n. \<bar>f n x - g x\<bar>) \<longlonglongrightarrow> 0" by auto
    then show ?thesis
      by (simp add: \<open>(\<lambda>n. \<bar>f n x - g x\<bar>) \<longlonglongrightarrow> 0\<close> LIM_zero_cancel tendsto_rabs_zero_cancel)
  qed
  ultimately show ?thesis by auto
qed

text \<open>As an illustration of the mechanism of spaces inclusion, let us show that bounded
continuous functions belong to $L^\infty$.\<close>

lemma bcontfun_subset_L_infinity:
  assumes "sets M = sets borel"
  shows "space\<^sub>N bcontfun\<^sub>N \<subseteq> space\<^sub>N (\<LL> \<infinity> M)"
        "\<And>f. f \<in> space\<^sub>N bcontfun\<^sub>N \<Longrightarrow> Norm (\<LL> \<infinity> M) f \<le> Norm bcontfun\<^sub>N f"
        "\<And>f. eNorm (\<LL> \<infinity> M) f \<le> eNorm bcontfun\<^sub>N f"
        "bcontfun\<^sub>N \<subseteq>\<^sub>N \<LL> \<infinity> M"
proof -
  have *: "f \<in> space\<^sub>N (\<LL> \<infinity> M) \<and> Norm (\<LL> \<infinity> M) f \<le> Norm bcontfun\<^sub>N f" if "f \<in> space\<^sub>N bcontfun\<^sub>N" for f
  proof -
    have H: "continuous_on UNIV f" "\<And>x. abs(f x) \<le> Norm bcontfun\<^sub>N f"
      using bcontfun\<^sub>ND[OF \<open>f \<in> space\<^sub>N bcontfun\<^sub>N\<close>] by auto
    then have "f \<in> borel_measurable borel" using borel_measurable_continuous_on1 by simp
    then have "f \<in> borel_measurable M" using assms by auto
    have *: "AE x in M. \<bar>f x\<bar> \<le> Norm bcontfun\<^sub>N f" using H(2) by auto
    show ?thesis using L_infinity_I[OF \<open>f \<in> borel_measurable M\<close> * Norm_nonneg] by auto
  qed
  show "space\<^sub>N bcontfun\<^sub>N \<subseteq> space\<^sub>N (\<LL> \<infinity> M)"
       "\<And>f. f \<in> space\<^sub>N bcontfun\<^sub>N \<Longrightarrow> Norm (\<LL> \<infinity> M) f \<le> Norm bcontfun\<^sub>N f"
    using * by auto
  show **: "bcontfun\<^sub>N \<subseteq>\<^sub>N \<LL> \<infinity> M"
    apply (rule quasinorm_subsetI'[of _ _ 1]) using * by auto
  have "eNorm (\<LL> \<infinity> M) f \<le> ennreal 1 * eNorm bcontfun\<^sub>N f" for f
    apply (rule quasinorm_subset_Norm_eNorm) using * ** by auto
  then show "eNorm (\<LL> \<infinity> M) f \<le> eNorm bcontfun\<^sub>N f" for f by simp
qed


subsection \<open>$L^p$ for $0 < p < \infty$\<close>

lemma Lp:
  assumes "p \<ge> (1::real)"
  shows "eNorm (\<LL> p M) f = (if (f \<in> borel_measurable M \<and> integrable M (\<lambda>x. \<bar>f x\<bar> powr p))
                            then (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)
                            else (\<infinity>::ennreal))"
        "defect (\<LL> p M) = 1"
proof -
  define F where "F = {f \<in> borel_measurable M. integrable M (\<lambda>x. \<bar>f x\<bar> powr p)}"
  have *: "quasinorm_on F 1 (\<lambda>(f::'a\<Rightarrow>real). (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p))"
  proof (rule quasinorm_onI)
    fix f g assume "f \<in> F" "g \<in> F"
    then show "f + g \<in> F"
      unfolding F_def plus_fun_def apply (auto) by (rule Minkowski_inequality(1), auto simp add: \<open>p \<ge> 1\<close>)
    show "ennreal ((\<integral>x. \<bar>(f + g) x\<bar> powr p \<partial>M) powr (1/p))
          \<le> ennreal 1 * (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) + ennreal 1 * (\<integral>x. \<bar>g x\<bar> powr p \<partial>M) powr (1/p)"
      apply (auto, subst ennreal_plus[symmetric], simp, simp, rule ennreal_leI)
      unfolding plus_fun_def apply (rule Minkowski_inequality(2)[of p f M g], auto simp add: \<open>p \<ge> 1\<close>)
      using \<open>f \<in> F\<close> \<open>g \<in> F\<close> unfolding F_def by auto
  next
    fix f and c::real assume "f \<in> F"
    show "c *\<^sub>R f \<in> F" using \<open>f \<in> F\<close> unfolding scaleR_fun_def F_def by (auto simp add: abs_mult powr_mult)
    show "(\<integral>x. \<bar>(c *\<^sub>R f) x\<bar> powr p \<partial>M) powr (1/p) \<le> ennreal(abs(c)) * (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
      apply (rule eq_refl, subst ennreal_mult[symmetric], simp, simp, rule ennreal_cong)
      apply (unfold scaleR_fun_def, simp add: abs_mult powr_mult powr_powr) using \<open>p \<ge> 1\<close> by auto
  next
    show "0 \<in> F" unfolding zero_fun_def F_def by auto
  qed (auto)

  have "p \<ge> 0" using \<open>p \<ge> 1\<close> by auto
  have **: "\<LL> p M = quasinorm_of (1,
              (\<lambda>f. if (f \<in> borel_measurable M \<and> integrable M (\<lambda>x. \<bar>f x\<bar> powr p))
              then (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)
              else (\<infinity>::ennreal)))"
    unfolding Lp_space_def using enn2real_ennreal[OF \<open>p \<ge> 0\<close>] \<open>p \<ge> 1\<close> apply auto
    using enn2real_ennreal[OF \<open>p \<ge> 0\<close>] by presburger
  show "eNorm (\<LL> p M) f = (if (f \<in> borel_measurable M \<and> integrable M (\<lambda>x. \<bar>f x\<bar> powr p))
                            then (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)
                            else (\<infinity>::ennreal))"
      "defect (\<LL> p M) = 1"
    unfolding ** using quasinorm_of[OF extend_quasinorm[OF *]] unfolding F_def by auto
qed

lemma Lp_le_1:
  assumes "p > 0" "p \<le> (1::real)"
  shows "eNorm (\<LL> p M) f = (if (f \<in> borel_measurable M \<and> integrable M (\<lambda>x. \<bar>f x\<bar> powr p))
                            then (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)
                            else (\<infinity>::ennreal))"
        "defect (\<LL> p M) = 2 powr (1/p - 1)"
proof -
  define F where "F = {f \<in> borel_measurable M. integrable M (\<lambda>x. \<bar>f x\<bar> powr p)}"
  have *: "quasinorm_on F (2 powr (1/p-1)) (\<lambda>(f::'a\<Rightarrow>real). (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p))"
  proof (rule quasinorm_onI)
    fix f g assume "f \<in> F" "g \<in> F"
    then show "f + g \<in> F"
      unfolding F_def plus_fun_def apply (auto) by (rule Minkowski_inequality_le_1(1), auto simp add: \<open>p > 0\<close> \<open>p \<le> 1\<close>)
    show "ennreal ((\<integral>x. \<bar>(f + g) x\<bar> powr p \<partial>M) powr (1/p))
          \<le> ennreal (2 powr (1/p-1)) * (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) + ennreal (2 powr (1/p-1)) * (\<integral>x. \<bar>g x\<bar> powr p \<partial>M) powr (1/p)"
      apply (subst ennreal_mult[symmetric], auto)+
      apply (subst ennreal_plus[symmetric], simp, simp)
      apply (rule ennreal_leI)
      unfolding plus_fun_def apply (rule Minkowski_inequality_le_1(2)[of p f M g], auto simp add: \<open>p > 0\<close> \<open>p \<le> 1\<close>)
      using \<open>f \<in> F\<close> \<open>g \<in> F\<close> unfolding F_def by auto
  next
    fix f and c::real assume "f \<in> F"
    show "c *\<^sub>R f \<in> F" using \<open>f \<in> F\<close> unfolding scaleR_fun_def F_def by (auto simp add: abs_mult powr_mult)
    show "(\<integral>x. \<bar>(c *\<^sub>R f) x\<bar> powr p \<partial>M) powr (1/p) \<le> ennreal(abs(c)) * (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
      apply (rule eq_refl, subst ennreal_mult[symmetric], simp, simp, rule ennreal_cong)
      apply (unfold scaleR_fun_def, simp add: abs_mult powr_mult powr_powr) using \<open>p > 0\<close> by auto
  next
    show "0 \<in> F" unfolding zero_fun_def F_def by auto
    show "1 \<le> 2 powr (1 / p - 1)" using \<open>p > 0\<close> \<open>p \<le> 1\<close> by (auto simp add: ge_one_powr_ge_zero)
  qed (auto)

  have "p \<ge> 0" using \<open>p > 0\<close> by auto
  have **: "\<LL> p M = quasinorm_of (2 powr (1/p-1),
              (\<lambda>f. if (f \<in> borel_measurable M \<and> integrable M (\<lambda>x. \<bar>f x\<bar> powr p))
              then (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)
              else (\<infinity>::ennreal)))"
    unfolding Lp_space_def using \<open>p > 0\<close> \<open>p \<le> 1\<close> using enn2real_ennreal[OF \<open>p \<ge> 0\<close>] apply auto
    by (insert enn2real_ennreal[OF \<open>p \<ge> 0\<close>], presburger)+
  show "eNorm (\<LL> p M) f = (if (f \<in> borel_measurable M \<and> integrable M (\<lambda>x. \<bar>f x\<bar> powr p))
                            then (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)
                            else (\<infinity>::ennreal))"
      "defect (\<LL> p M) = 2 powr (1/p-1)"
    unfolding ** using quasinorm_of[OF extend_quasinorm[OF *]] unfolding F_def by auto
qed

lemma Lp_space:
  assumes "p > (0::real)"
  shows "space\<^sub>N (\<LL> p M) = {f \<in> borel_measurable M. integrable M (\<lambda>x. \<bar>f x\<bar> powr p)}"
apply (auto simp add: spaceN_iff)
using Lp(1) Lp_le_1(1) \<open>p > 0\<close> apply (metis infinity_ennreal_def less_le not_less)
using Lp(1) Lp_le_1(1) \<open>p > 0\<close> apply (metis infinity_ennreal_def less_le not_less)
using Lp(1) Lp_le_1(1) \<open>p > 0\<close> by (metis ennreal_neq_top linear top.not_eq_extremum)

lemma Lp_I:
  assumes "p > (0::real)"
          "f \<in> borel_measurable M" "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "f \<in> space\<^sub>N (\<LL> p M)"
        "Norm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
        "eNorm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
proof -
  have *: "eNorm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
    by (cases "p \<le> 1", insert assms, auto simp add: Lp_le_1(1) Lp(1))
  then show **: "f \<in> space\<^sub>N (\<LL> p M)" unfolding space\<^sub>N_def by auto
  show "Norm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)" using * unfolding Norm_def by auto
  then show "eNorm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)" using eNorm_Norm[OF **] by auto
qed

lemma Lp_D:
  assumes "p>0" "f \<in> space\<^sub>N (\<LL> p M)"
  shows "f \<in> borel_measurable M"
        "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
        "Norm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
        "eNorm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
proof -
  show *: "f \<in> borel_measurable M"
          "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
    using Lp_space[OF \<open>p > 0\<close>] assms(2) by auto
  then show "Norm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
            "eNorm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
    using Lp_I[OF \<open>p > 0\<close>] by auto
qed

lemma Lp_Norm:
  assumes "p > (0::real)"
          "f \<in> borel_measurable M"
  shows "Norm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
        "(Norm (\<LL> p M) f) powr p = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M)"
proof -
  show *: "Norm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
  proof (cases "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)")
    case True
    then show ?thesis using Lp_I[OF assms True] by auto
  next
    case False
    then have "f \<notin> space\<^sub>N (\<LL> p M)" using Lp_space[OF \<open>p > 0\<close>, of M] by auto
    then have *: "Norm (\<LL> p M) f = 0" using eNorm_Norm' by auto
    have "(\<integral>x. \<bar>f x\<bar> powr p \<partial>M) = 0" using False by (simp add: not_integrable_integral_eq)
    then have "(\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p) = 0" by auto
    then show ?thesis using * by auto
  qed
  then show "(Norm (\<LL> p M) f) powr p = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M)"
    unfolding * using powr_powr \<open>p > 0\<close> by auto
qed

lemma Lp_zero_space:
  assumes "p > (0::real)"
  shows "zero_space\<^sub>N (\<LL> p M) = {f \<in> borel_measurable M. AE x in M. f x = 0}"
proof (auto)
  fix f assume H: "f \<in> zero_space\<^sub>N (\<LL> p M)"
  then have *: "f \<in> {f \<in> borel_measurable M. integrable M (\<lambda>x. \<bar>f x\<bar> powr p)}"
    using Lp_space[OF assms] zero_spaceN_subset_spaceN by auto
  then show "f \<in> borel_measurable M" by auto
  have "eNorm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
    by (cases "p \<le> 1", insert * \<open>p > 0\<close>, auto simp add: Lp_le_1(1) Lp(1))
  then have "(\<integral>x. \<bar>f x\<bar> powr p \<partial>M) = 0" using H unfolding zero_space\<^sub>N_def by auto
  then have "AE x in M. \<bar>f x\<bar> powr p = 0"
    by (subst integral_nonneg_eq_0_iff_AE[symmetric], insert *, auto)
  then show "AE x in M. f x = 0" by auto
next
  fix f::"'a \<Rightarrow> real"
  assume H [measurable]: "f \<in> borel_measurable M" "AE x in M. f x = 0"
  then have *: "AE x in M. \<bar>f x\<bar> powr p = 0" by auto
  have "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
    using integrable_cong_AE[OF _ _ *] by auto
  have **: "(\<integral>x. \<bar>f x\<bar> powr p \<partial>M) = 0"
    using integral_cong_AE[OF _ _ *] by auto
  have "eNorm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"
    by (cases "p \<le> 1", insert H(1) \<open>integrable M (\<lambda>x. \<bar>f x\<bar> powr p)\<close> \<open>p > 0\<close>, auto simp add: Lp_le_1(1) Lp(1))
  then have "eNorm (\<LL> p M) f = 0" using ** by simp
  then show "f \<in> zero_space\<^sub>N (\<LL> p M)"
    using zero_spaceN_iff by auto
qed

lemma Lp_tendsto_AE_subseq:
  assumes "p>(0::real)"
          "tendsto_in\<^sub>N (\<LL> p M) f g"
          "\<And>n. f n \<in> space\<^sub>N (\<LL> p M)"
          "g \<in> space\<^sub>N (\<LL> p M)"
  shows "\<exists>r. strict_mono r \<and> (AE x in M. (\<lambda>n. f (r n) x) \<longlonglongrightarrow> g x)"
proof -
  have "f n - g \<in> space\<^sub>N (\<LL> p M)" for n
    using spaceN_diff[OF \<open>\<And>n. f n \<in> space\<^sub>N (\<LL> p M)\<close> \<open>g \<in> space\<^sub>N (\<LL> p M)\<close>] by simp
  have int: "integrable M (\<lambda>x. \<bar>f n x - g x\<bar> powr p)" for n
    using Lp_D(2)[OF \<open>p > 0\<close> \<open>f n - g \<in> space\<^sub>N (\<LL> p M)\<close>] by auto

  have "(\<lambda>n. Norm (\<LL> p M) (f n - g)) \<longlonglongrightarrow> 0"
    using \<open>tendsto_in\<^sub>N (\<LL> p M) f g\<close> unfolding tendsto_in\<^sub>N_def by auto
  then have *: "(\<lambda>n. (\<integral>x. \<bar>f n x - g x\<bar> powr p \<partial>M) powr (1/p)) \<longlonglongrightarrow> 0"
    using Lp_D(3)[OF \<open>p > 0\<close> \<open>\<And>n. f n - g \<in> space\<^sub>N (\<LL> p M)\<close>] by auto
  have "(\<lambda>n. ((\<integral>x. \<bar>f n x - g x\<bar> powr p \<partial>M) powr (1/p)) powr p) \<longlonglongrightarrow> 0"
    apply (rule tendsto_zero_powrI[of _ _ _ p]) using \<open>p > 0\<close> * by auto
  then have **: "(\<lambda>n. (\<integral>x. \<bar>f n x - g x\<bar> powr p \<partial>M)) \<longlonglongrightarrow> 0"
    using powr_powr \<open>p > 0\<close> by auto
  have "\<exists>r. strict_mono r \<and> (AE x in M. (\<lambda>n. \<bar>f (r n) x - g x\<bar> powr p) \<longlonglongrightarrow> 0)"
    apply (rule tendsto_L1_AE_subseq) using int ** by auto
  then obtain r where "strict_mono r" "AE x in M. (\<lambda>n. \<bar>f (r n) x - g x\<bar> powr p) \<longlonglongrightarrow> 0"
    by blast
  moreover have "(\<lambda>n. f (r n) x) \<longlonglongrightarrow> g x" if "(\<lambda>n. \<bar>f (r n) x - g x\<bar> powr p) \<longlonglongrightarrow> 0" for x
  proof -
    have "(\<lambda>n. (\<bar>f (r n) x - g x\<bar> powr p) powr (1/p)) \<longlonglongrightarrow> 0"
      apply (rule tendsto_zero_powrI[of _ _ _ "1/p"]) using \<open>p > 0\<close> that by auto
    then have "(\<lambda>n. \<bar>f (r n) x - g x\<bar>) \<longlonglongrightarrow> 0"
      using powr_powr \<open>p > 0\<close> by auto
    show ?thesis
      by (simp add: \<open>(\<lambda>n. \<bar>f (r n) x - g x\<bar>) \<longlonglongrightarrow> 0\<close> Limits.LIM_zero_cancel tendsto_rabs_zero_cancel)
  qed
  ultimately have "AE x in M. (\<lambda>n. f (r n) x) \<longlonglongrightarrow> g x" by auto
  then show ?thesis using \<open>strict_mono r\<close> by auto
qed

subsection \<open>Specialization to $L^1$\<close>

lemma L1_space:
  "space\<^sub>N (\<LL> 1 M) = {f. integrable M f}"
unfolding one_ereal_def using Lp_space[of 1 M] integrable_abs_iff by auto

lemma L1_I:
  assumes "integrable M f"
  shows "f \<in> space\<^sub>N (\<LL> 1 M)"
        "Norm (\<LL> 1 M) f = (\<integral>x. \<bar>f x\<bar> \<partial>M)"
        "eNorm (\<LL> 1 M) f = (\<integral>x. \<bar>f x\<bar> \<partial>M)"
unfolding one_ereal_def using Lp_I[of 1, OF _ borel_measurable_integrable[OF assms]] assms powr_to_1 by auto

lemma L1_D:
  assumes "f \<in> space\<^sub>N (\<LL> 1 M)"
  shows "f \<in> borel_measurable M"
        "integrable M f"
        "Norm (\<LL> 1 M) f = (\<integral>x. \<bar>f x\<bar> \<partial>M)"
        "eNorm (\<LL> 1 M) f = (\<integral>x. \<bar>f x\<bar> \<partial>M)"
  using assms by (auto simp add: L1_space L1_I)

lemma L1_int_ineq:
  "abs(\<integral>x. f x \<partial>M) \<le> Norm (\<LL> 1 M) f"
proof (cases "integrable M f")
  case True
  then show ?thesis using L1_I(2)[OF True] by auto
next
  case False
  then have "(\<integral>x. f x \<partial>M) = 0" by (simp add: not_integrable_integral_eq)
  then show ?thesis using Norm_nonneg by auto
qed

text \<open>In $L^1$, one can give a direct formula for the eNorm of a measurable function, using a
nonnegative integral. The same formula holds in $L^p$ for $p > 0$, with additional powers $p$ and
$1/p$, but one can not write it down since \verb+powr+ is not defined on \verb+ennreal+.\<close>

lemma L1_Norm:
  assumes [measurable]: "f \<in> borel_measurable M"
  shows "Norm (\<LL> 1 M) f = (\<integral>x. \<bar>f x\<bar> \<partial>M)"
        "eNorm (\<LL> 1 M) f = (\<integral>\<^sup>+x. \<bar>f x\<bar> \<partial>M)"
proof -
  show *: "Norm (\<LL> 1 M) f = (\<integral>x. \<bar>f x\<bar> \<partial>M)"
    using Lp_Norm[of 1, OF _ assms] unfolding one_ereal_def by auto
  show "eNorm (\<LL> 1 M) f = (\<integral>\<^sup>+x. \<bar>f x\<bar> \<partial>M)"
  proof (cases "integrable M f")
    case True
    then have "f \<in> space\<^sub>N (\<LL> 1 M)" using L1_space by auto
    then have "eNorm (\<LL> 1 M) f = ennreal (Norm (\<LL> 1 M) f)"
      using eNorm_Norm by auto
    then show ?thesis
      by (metis (mono_tags) * AE_I2 True abs_ge_zero integrable_abs nn_integral_eq_integral)
  next
    case False
    then have "eNorm (\<LL> 1 M) f = \<infinity>" using L1_space space\<^sub>N_def
      by (metis ennreal_add_eq_top infinity_ennreal_def le_iff_add le_less_linear mem_Collect_eq)
    moreover have "(\<integral>\<^sup>+x. \<bar>f x\<bar> \<partial>M) = \<infinity>"
      apply (rule nn_integral_nonneg_infinite) using False by (auto simp add: integrable_abs_iff)
    ultimately show ?thesis by simp
  qed
qed

lemma L1_indicator:
  assumes [measurable]: "A \<in> sets M"
  shows "eNorm (\<LL> 1 M) (indicator A) = emeasure M A"
by (subst L1_Norm, auto, metis assms ennreal_indicator nn_integral_cong nn_integral_indicator)

lemma L1_indicator':
  assumes [measurable]: "A \<in> sets M"
      and "emeasure M A \<noteq> \<infinity>"
  shows "indicator A \<in> space\<^sub>N (\<LL> 1 M)"
        "Norm (\<LL> 1 M) (indicator A) = measure M A"
unfolding space\<^sub>N_def Norm_def using L1_indicator[OF \<open>A \<in> sets M\<close>] \<open>emeasure M A \<noteq> \<infinity>\<close>
by (auto simp add: top.not_eq_extremum Sigma_Algebra.measure_def)


subsection \<open>$L^0$\<close>

text \<open>We have defined $L^p$ for all exponents $p$, although it does not really make sense for $p = 0$.
We have chosen a definition in this case (the space of all measurable functions) so that many
statements are true for all exponents. In this paragraph, we show the consistency of this definition.\<close>

lemma L_zero:
  "eNorm (\<LL> 0 M) f = (if f \<in> borel_measurable M then 0 else \<infinity>)"
  "defect (\<LL> 0 M) = 1"
proof -
  have *: "quasinorm_on UNIV 1 (\<lambda>(f::'a\<Rightarrow>real). (if f \<in> borel_measurable M then 0 else \<infinity>))"
    by (rule extend_quasinorm, rule quasinorm_onI, auto)
  show "eNorm (\<LL> 0 M) f = (if f \<in> borel_measurable M then 0 else \<infinity>)"
       "defect (\<LL> 0 M) = 1"
    using quasinorm_of[OF *] unfolding Lp_space_def by auto
qed

lemma L_zero_space:
  "space\<^sub>N (\<LL> 0 M) = borel_measurable M"
  "zero_space\<^sub>N (\<LL> 0 M) = borel_measurable M"
apply (auto simp add: spaceN_iff zero_spaceN_iff L_zero(1))
using top.not_eq_extremum by force+

subsection \<open>Basic results on $L^p$ for general $p$\<close>

lemma Lp_measurable_subset:
  "space\<^sub>N (\<LL> p M) \<subseteq> borel_measurable M"
proof (cases rule: Lp_cases[of p])
  case zero
  then show ?thesis using L_zero_space by auto
next
  case (real_pos p2)
  then show ?thesis using Lp_space[OF \<open>p2 > 0\<close>] by auto
next
  case PInf
  then show ?thesis using L_infinity_space by auto
qed

lemma Lp_measurable:
  assumes "f \<in> space\<^sub>N (\<LL> p M)"
  shows "f \<in> borel_measurable M"
using assms Lp_measurable_subset by auto

lemma Lp_infinity_zero_space:
  assumes "p > (0::ennreal)"
  shows "zero_space\<^sub>N (\<LL> p M) = {f \<in> borel_measurable M. AE x in M. f x = 0}"
proof (cases rule: Lp_cases[of p])
  case PInf
  then show ?thesis using L_infinity_zero_space by auto
next
  case (real_pos p2)
  then show ?thesis using Lp_zero_space[OF \<open>p2 > 0\<close>] unfolding \<open>p = ennreal p2\<close> by auto
next
  case zero
  then have False using assms by auto
  then show ?thesis by simp
qed

lemma (in prob_space) Lp_subset_Lq:
  assumes "p \<le> q"
  shows "\<And>f. eNorm (\<LL> p M) f \<le> eNorm (\<LL> q M) f"
        "\<LL> q M \<subseteq>\<^sub>N \<LL> p M"
        "space\<^sub>N (\<LL> q M) \<subseteq> space\<^sub>N (\<LL> p M)"
        "\<And>f. f \<in> space\<^sub>N (\<LL> q M) \<Longrightarrow> Norm (\<LL> p M) f \<le> Norm (\<LL> q M) f"
proof -
  show "eNorm (\<LL> p M) f \<le> eNorm (\<LL> q M) f" for f
  proof (cases "eNorm (\<LL> q M) f < \<infinity>")
    case True
    then have "f \<in> space\<^sub>N (\<LL> q M)" using spaceN_iff by auto
    then have f_meas [measurable]: "f \<in> borel_measurable M" using Lp_measurable by auto
    consider "p = 0" | "p = q" | "p > 0 \<and> p < \<infinity> \<and> q = \<infinity>" | "p > 0 \<and> p < q \<and> q < \<infinity>"
      using \<open>p \<le> q\<close> apply (simp add: top.not_eq_extremum)
      using not_less_iff_gr_or_eq order.order_iff_strict by fastforce
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis by (simp add: L_zero(1))
    next
      case 2
      then show ?thesis by auto
    next
      case 3
      then have "q = \<infinity>" by simp
      obtain p2 where "p = ennreal p2" "p2 > 0"
        using 3 enn2real_positive_iff[of p] by (cases p) auto
      have *: "AE x in M. \<bar>f x\<bar> \<le> Norm (\<LL> \<infinity> M) f"
        using L_infinity_AE_bound \<open>f \<in> space\<^sub>N (\<LL> q M)\<close> \<open>q = \<infinity>\<close> by auto
      have **: "integrable M (\<lambda>x. \<bar>f x\<bar> powr p2)"
        apply (rule Bochner_Integration.integrable_bound[of _ "\<lambda>x. (Norm (\<LL> \<infinity> M) f) powr p2"], auto)
        using * powr_mono2 \<open>p2 > 0\<close> by force
      then have "eNorm (\<LL> p2 M) f = (\<integral>x. \<bar>f x\<bar> powr p2 \<partial>M) powr (1/p2)"
        using Lp_I(3)[OF \<open>p2 > 0\<close> f_meas] by simp
      also have "... \<le> (\<integral>x. (Norm (\<LL> \<infinity> M) f) powr p2 \<partial>M) powr (1/p2)"
        apply (rule ennreal_leI, rule powr_mono2, simp add: \<open>p2 > 0\<close> less_imp_le, simp)
        apply (rule integral_mono_AE, auto simp add: **)
        using * powr_mono2 \<open>p2 > 0\<close> by force
      also have "... = Norm (\<LL> \<infinity> M) f"
        using \<open>p2 > 0\<close> by (auto simp add: prob_space powr_powr)
      finally show ?thesis
        using \<open>p = ennreal p2\<close> \<open>q = \<infinity>\<close> eNorm_Norm[OF \<open>f \<in> space\<^sub>N (\<LL> q M)\<close>] by auto
    next
      case 4
      then have "0 < p" "p < \<infinity>" by auto
      then obtain p2 where "p = ennreal p2" "p2 > 0"
        using enn2real_positive_iff[of p] by (cases p) auto
      have "0 < q" "q < \<infinity>" using 4 by auto
      then obtain q2 where "q = ennreal q2" "q2 > 0"
        using enn2real_positive_iff[of q] by (cases q) auto
      have "p2 < q2" using 4 \<open>p = ennreal p2\<close> \<open>q = ennreal q2\<close>
        using ennreal_less_iff by auto
      define r2 where "r2 = q2 / p2"
      have "r2 \<ge> 1" unfolding r2_def using \<open>p2 < q2\<close> \<open>p2 > 0\<close> by auto
      have *: "abs (\<bar>z\<bar> powr p2) powr r2 = \<bar>z\<bar> powr q2" for z::real
        unfolding r2_def using \<open>p2 > 0\<close> by (simp add: powr_powr)
      have I: "integrable M (\<lambda>x. abs(\<bar>f x\<bar> powr p2) powr r2)"
        unfolding * using \<open>f \<in> space\<^sub>N (\<LL> q M)\<close> \<open>q = ennreal q2\<close> Lp_D(2)[OF \<open>q2 > 0\<close>] by auto
      have J: "integrable M (\<lambda>x. \<bar>f x\<bar> powr p2)"
        by (rule bound_L1_Lp(1)[OF \<open>r2 \<ge> 1\<close> _ I], auto)
      have "f \<in> space\<^sub>N (\<LL> p2 M)"
        by (rule Lp_I(1)[OF \<open>p2 > 0\<close> _ J], simp)
      have "(\<integral>x. \<bar>f x\<bar> powr p2 \<partial>M) powr (1/p2) = abs(\<integral>x. \<bar>f x\<bar> powr p2 \<partial>M) powr (1/p2)"
        by auto
      also have "... \<le> ((\<integral>x. abs (\<bar>f x\<bar> powr p2) powr r2 \<partial>M) powr (1/r2)) powr (1/p2)"
        apply (subst powr_mono2, simp add: \<open>p2 > 0\<close> less_imp_le, simp)
        apply (rule bound_L1_Lp, simp add: \<open>r2 \<ge> 1\<close>, simp)
        unfolding * using \<open>f \<in> space\<^sub>N (\<LL> q M)\<close> \<open>q = ennreal q2\<close> Lp_D(2)[OF \<open>q2 > 0\<close>] by auto
      also have "... = (\<integral>x. \<bar>f x\<bar> powr q2 \<partial>M) powr (1/q2)"
        unfolding * using \<open>p2 > 0\<close> by (simp add: powr_powr r2_def)
      finally show ?thesis
        using \<open>f \<in> space\<^sub>N (\<LL> q M)\<close> Lp_D(4)[OF \<open>q2 > 0\<close>] ennreal_leI
        unfolding \<open>p = ennreal p2\<close> \<open>q = ennreal q2\<close> Lp_D(4)[OF \<open>p2 > 0\<close> \<open>f \<in> space\<^sub>N (\<LL> p2 M)\<close>] by force
    qed
  next
    case False
    then have "eNorm (\<LL> q M) f = \<infinity>"
      using top.not_eq_extremum by fastforce
    then show ?thesis by auto
  qed
  then show "\<LL> q M \<subseteq>\<^sub>N \<LL> p M" using quasinorm_subsetI[of _ _ 1] by auto
  then show "space\<^sub>N (\<LL> q M) \<subseteq> space\<^sub>N (\<LL> p M)" using quasinorm_subset_space by auto
  then show "Norm (\<LL> p M) f \<le> Norm (\<LL> q M) f" if "f \<in> space\<^sub>N (\<LL> q M)" for f
    using eNorm_Norm that \<open>eNorm (\<LL> p M) f \<le> eNorm (\<LL> q M) f\<close> ennreal_le_iff Norm_nonneg
    by (metis rev_subsetD)
qed

proposition Lp_domination:
  assumes [measurable]: "g \<in> borel_measurable M"
      and "f \<in> space\<^sub>N (\<LL> p M)"
          "AE x in M. \<bar>g x\<bar> \<le> \<bar>f x\<bar>"
  shows "g \<in> space\<^sub>N (\<LL> p M)"
        "Norm (\<LL> p M) g \<le> Norm (\<LL> p M) f"
proof -
  have [measurable]: "f \<in> borel_measurable M" using Lp_measurable[OF assms(2)] by simp
  have "g \<in> space\<^sub>N (\<LL> p M) \<and> Norm (\<LL> p M) g \<le> Norm (\<LL> p M) f"
  proof (cases rule: Lp_cases[of p])
    case zero
    then have "Norm (\<LL> p M) g = 0"
      unfolding Norm_def using L_zero(1)[of M] by auto
    then have "Norm (\<LL> p M) g \<le> Norm (\<LL> p M) f" using Norm_nonneg by auto
    then show ?thesis unfolding \<open>p = 0\<close> L_zero_space by auto
  next
    case (real_pos p2)
    have *: "integrable M (\<lambda>x. \<bar>f x\<bar> powr p2)"
      using \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> unfolding \<open>p = ennreal p2\<close> using Lp_D(2) \<open>p2 > 0\<close> by auto
    have **: "integrable M (\<lambda>x. \<bar>g x\<bar> powr p2)"
      apply (rule Bochner_Integration.integrable_bound[of _ "\<lambda>x. \<bar>f x\<bar> powr p2"]) using * apply auto
      using assms(3) powr_mono2 \<open>p2 > 0\<close> by (auto simp add: less_imp_le)
    then have "g \<in> space\<^sub>N (\<LL> p M)"
      unfolding \<open>p = ennreal p2\<close> using Lp_space[OF \<open>p2 > 0\<close>, of M] by auto
    have "Norm (\<LL> p M) g = (\<integral>x. \<bar>g x\<bar> powr p2 \<partial>M) powr (1/p2)"
      unfolding \<open>p = ennreal p2\<close> by (rule Lp_I(2)[OF \<open>p2 > 0\<close> _ **], simp)
    also have "... \<le> (\<integral>x. \<bar>f x\<bar> powr p2 \<partial>M) powr (1/p2)"
      apply (rule powr_mono2, simp add: \<open>p2 > 0\<close> less_imp_le, simp)
      apply (rule integral_mono_AE, auto simp add: * **)
      using \<open>p2 > 0\<close> less_imp_le powr_mono2 assms(3) by auto
    also have "... = Norm (\<LL> p M) f"
      unfolding \<open>p = ennreal p2\<close> by (rule Lp_I(2)[OF \<open>p2 > 0\<close> _ *, symmetric], simp)
    finally show ?thesis using \<open>g \<in> space\<^sub>N (\<LL> p M)\<close> by auto
  next
    case PInf
    have "AE x in M. \<bar>f x\<bar> \<le> Norm (\<LL> p M) f"
      using \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> L_infinity_AE_bound unfolding \<open>p = \<infinity>\<close> by auto
    then have *: "AE x in M. \<bar>g x\<bar> \<le> Norm (\<LL> p M) f"
      using assms(3) by auto
    show ?thesis
      using L_infinity_I[OF assms(1) *] Norm_nonneg \<open>p = \<infinity>\<close> by auto
  qed
  then show "g \<in> space\<^sub>N (\<LL> p M)" "Norm (\<LL> p M) g \<le> Norm (\<LL> p M) f"
    by auto
qed

lemma Lp_Banach_lattice:
  assumes "f \<in> space\<^sub>N (\<LL> p M)"
  shows "(\<lambda>x. \<bar>f x\<bar>) \<in> space\<^sub>N (\<LL> p M)"
        "Norm (\<LL> p M) (\<lambda>x. \<bar>f x\<bar>) = Norm (\<LL> p M) f"
proof -
  have [measurable]: "f \<in> borel_measurable M" using Lp_measurable[OF assms] by simp
  show "(\<lambda>x. \<bar>f x\<bar>) \<in> space\<^sub>N (\<LL> p M)"
    by (rule Lp_domination(1)[OF _ assms], auto)
  have "Norm (\<LL> p M) (\<lambda>x. \<bar>f x\<bar>) \<le> Norm (\<LL> p M) f"
    by (rule Lp_domination[OF _ assms], auto)
  moreover have "Norm (\<LL> p M) f \<le> Norm (\<LL> p M) (\<lambda>x. \<bar>f x\<bar>)"
    by (rule Lp_domination[OF _ \<open>(\<lambda>x. \<bar>f x\<bar>) \<in> space\<^sub>N (\<LL> p M)\<close>], auto)
  finally show "Norm (\<LL> p M) (\<lambda>x. \<bar>f x\<bar>) = Norm (\<LL> p M) f" by auto
qed

lemma Lp_bounded_bounded_support:
  assumes [measurable]: "f \<in> borel_measurable M"
      and "AE x in M. \<bar>f x\<bar> \<le> C"
          "emeasure M {x \<in> space M. f x \<noteq> 0} \<noteq> \<infinity>"
  shows "f \<in> space\<^sub>N(\<LL> p M)"
proof (cases rule: Lp_cases[of p])
  case zero
  then show ?thesis using L_zero_space assms by blast
next
  case PInf
  then show ?thesis using L_infinity_space assms by blast
next
  case (real_pos p2)
  have *: "integrable M (\<lambda>x. \<bar>f x\<bar> powr p2)"
    apply (rule integrableI_bounded_set[of "{x \<in> space M. f x \<noteq> 0}" _ _ "C powr p2"])
    using assms powr_mono2[OF less_imp_le[OF \<open>p2 > 0\<close>]] by (auto simp add: top.not_eq_extremum)
  show ?thesis
    unfolding \<open>p = ennreal p2\<close> apply (rule Lp_I[OF \<open>p2 > 0\<close>]) using * by auto
qed


subsection \<open>$L^p$ versions of the main theorems in integration theory\<close>

text \<open>The space $L^p$ is stable under almost sure convergence, for sequence with bounded norm.
This is a version of Fatou's lemma (and it indeed follows from this lemma in the only
nontrivial situation where $p \in (0, +\infty)$.\<close>

proposition Lp_AE_limit:
  assumes [measurable]: "g \<in> borel_measurable M"
      and "AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> g x"
  shows "eNorm (\<LL> p M) g \<le> liminf (\<lambda>n. eNorm (\<LL> p M) (f n))"
proof (cases "liminf (\<lambda>n. eNorm (\<LL> p M) (f n)) = \<infinity>")
  case True
  then show ?thesis by auto
next
  case False
  define le where "le = liminf (\<lambda>n. eNorm (\<LL> p M) (f n))"
  then have "le < \<infinity>" using False by (simp add: top.not_eq_extremum)
  obtain r0 where r0: "strict_mono r0" "(\<lambda>n. eNorm (\<LL> p M) (f (r0 n))) \<longlonglongrightarrow> le"
    using liminf_subseq_lim unfolding comp_def le_def by force
  then have "eventually (\<lambda>n. eNorm (\<LL> p M) (f (r0 n)) < \<infinity>) sequentially"
    using False unfolding order_tendsto_iff le_def by (simp add: top.not_eq_extremum)
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> eNorm (\<LL> p M) (f (r0 n)) < \<infinity>"
    unfolding eventually_sequentially by blast
  define r where "r = (\<lambda>n. r0 (n + N))"
  have "strict_mono r" unfolding r_def using \<open>strict_mono r0\<close> 
    by (simp add: strict_mono_Suc_iff)
  have *: "(\<lambda>n. eNorm (\<LL> p M) (f (r n))) \<longlonglongrightarrow> le"
    unfolding r_def using LIMSEQ_ignore_initial_segment[OF r0(2), of N].
  have "f (r n) \<in> space\<^sub>N (\<LL> p M)" for n
    using N spaceN_iff unfolding r_def by force
  then have [measurable]: "f (r n) \<in> borel_measurable M" for n
    using Lp_measurable by auto
  define l where "l = enn2real le"
  have "l \<ge> 0" unfolding l_def by auto
  have "le = ennreal l" using \<open>le < \<infinity>\<close> unfolding l_def by auto
  have [tendsto_intros]: "(\<lambda>n. Norm (\<LL> p M) (f (r n))) \<longlonglongrightarrow> l"
    apply (rule tendsto_ennrealD)
    using * \<open>le < \<infinity>\<close> unfolding eNorm_Norm[OF \<open>\<And>n. f (r n) \<in> space\<^sub>N (\<LL> p M)\<close>] l_def by auto

  show ?thesis
  proof (cases rule: Lp_cases[of p])
    case zero
    then have "eNorm (\<LL> p M) g = 0"
      using assms(1) by (simp add: L_zero(1))
    then show ?thesis by auto
  next
    case (real_pos p2)
    then have "f (r n) \<in> space\<^sub>N (\<LL> p2 M)" for n
      using \<open>\<And>n. f (r n) \<in> space\<^sub>N(\<LL> p M)\<close> by auto
    have "liminf (\<lambda>n. ennreal(\<bar>f (r n) x\<bar> powr p2)) = \<bar>g x\<bar> powr p2" if "(\<lambda>n. f n x) \<longlonglongrightarrow> g x" for x
      apply (rule lim_imp_Liminf, auto intro!: tendsto_intros simp add: \<open>p2 > 0\<close>)
      using LIMSEQ_subseq_LIMSEQ[OF that \<open>strict_mono r\<close>] unfolding comp_def by auto
    then have *: "AE x in M. liminf (\<lambda>n. ennreal(\<bar>f (r n) x\<bar> powr p2)) = \<bar>g x\<bar> powr p2"
      using \<open>AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> g x\<close> by auto

    have "(\<integral>\<^sup>+x. ennreal(\<bar>f (r n) x\<bar> powr p2) \<partial>M) = ennreal((Norm (\<LL> p M) (f (r n))) powr p2)" for n
    proof -
      have "(\<integral>\<^sup>+x. ennreal(\<bar>f (r n) x\<bar> powr p2) \<partial>M) = ennreal (\<integral>x. \<bar>f (r n) x\<bar> powr p2 \<partial>M)"
        by (rule nn_integral_eq_integral, auto simp add: Lp_D(2)[OF \<open>p2 > 0\<close> \<open>f (r n) \<in> space\<^sub>N (\<LL> p2 M)\<close>])
      also have "... = ennreal((Norm (\<LL> p2 M) (f (r n))) powr p2)"
        unfolding Lp_D(3)[OF \<open>p2 > 0\<close> \<open>f (r n) \<in> space\<^sub>N (\<LL> p2 M)\<close>] using powr_powr \<open>p2 > 0\<close> by auto
      finally show ?thesis using \<open>p = ennreal p2\<close> by simp
    qed
    moreover have "(\<lambda>n. ennreal((Norm (\<LL> p M) (f (r n))) powr p2)) \<longlonglongrightarrow> ennreal(l powr p2)"
      by (auto intro!:tendsto_intros simp add: \<open>p2 > 0\<close>)
    ultimately have **: "liminf (\<lambda>n. (\<integral>\<^sup>+x. ennreal(\<bar>f (r n) x\<bar> powr p2) \<partial>M)) = ennreal(l powr p2)"
      using lim_imp_Liminf by force

    have "(\<integral>\<^sup>+x. \<bar>g x\<bar> powr p2 \<partial>M) = (\<integral>\<^sup>+x. liminf (\<lambda>n. ennreal(\<bar>f (r n) x\<bar> powr p2)) \<partial>M)"
      apply (rule nn_integral_cong_AE) using * by auto
    also have "... \<le> liminf (\<lambda>n. \<integral>\<^sup>+x. ennreal(\<bar>f (r n) x\<bar> powr p2) \<partial>M)"
      by (rule nn_integral_liminf, auto)
    finally have "(\<integral>\<^sup>+x. \<bar>g x\<bar> powr p2 \<partial>M) \<le> ennreal(l powr p2)" using ** by auto
    then have "(\<integral>\<^sup>+x. \<bar>g x\<bar> powr p2 \<partial>M) < \<infinity>" using le_less_trans by fastforce
    then have intg: "integrable M (\<lambda>x. \<bar>g x\<bar> powr p2)"
      apply (intro integrableI_nonneg) by auto
    then have "g \<in> space\<^sub>N (\<LL> p2 M)" using Lp_I(1)[OF \<open>p2 > 0\<close>, of _ M] by fastforce
    have "ennreal((Norm (\<LL> p2 M) g) powr p2) = ennreal(\<integral>x. \<bar>g x\<bar> powr p2 \<partial>M)"
      unfolding Lp_D(3)[OF \<open>p2 > 0\<close> \<open>g \<in> space\<^sub>N (\<LL> p2 M)\<close>] using powr_powr \<open>p2 > 0\<close> by auto
    also have "... = (\<integral>\<^sup>+x. \<bar>g x\<bar> powr p2 \<partial>M)"
      by (rule nn_integral_eq_integral[symmetric], auto simp add: intg)
    finally have "ennreal((Norm (\<LL> p2 M) g) powr p2) \<le> ennreal(l powr p2)"
      using \<open>(\<integral>\<^sup>+x. \<bar>g x\<bar> powr p2 \<partial>M) \<le> ennreal(l powr p2)\<close> by auto
    then have "((Norm (\<LL> p2 M) g) powr p2) powr (1/p2) \<le> (l powr p2) powr (1/p2)"
      using ennreal_le_iff \<open>l \<ge> 0\<close> \<open>p2 > 0\<close> powr_mono2 by auto
    then have "Norm (\<LL> p2 M) g \<le> l"
      using \<open>p2 > 0\<close> \<open>l \<ge> 0\<close> by (auto simp add: powr_powr)
    then have "eNorm (\<LL> p2 M) g \<le> le"
      unfolding eNorm_Norm[OF \<open>g \<in> space\<^sub>N (\<LL> p2 M)\<close>] \<open>le = ennreal l\<close> using ennreal_leI by auto
    then show ?thesis unfolding le_def \<open>p = ennreal p2\<close> by simp
  next
    case PInf
    then have "AE x in M. \<forall>n. \<bar>f (r n) x\<bar> \<le> Norm (\<LL> \<infinity> M) (f (r n))"
      apply (subst AE_all_countable) using L_infinity_AE_bound \<open>\<And>n. f (r n) \<in> space\<^sub>N (\<LL> p M)\<close> by blast
    moreover have "\<bar>g x\<bar> \<le> l" if "\<forall>n. \<bar>f (r n) x\<bar> \<le> Norm (\<LL> \<infinity> M) (f (r n))" "(\<lambda>n. f n x) \<longlonglongrightarrow> g x" for x
    proof -
      have "(\<lambda>n. f (r n) x) \<longlonglongrightarrow> g x"
        using that LIMSEQ_subseq_LIMSEQ[OF _ \<open>strict_mono r\<close>] unfolding comp_def by auto
      then have *: "(\<lambda>n. \<bar>f (r n) x\<bar>) \<longlonglongrightarrow> \<bar>g x\<bar>"
        by (auto intro!:tendsto_intros)
      show ?thesis
        apply (rule LIMSEQ_le[OF *]) using that(1) \<open>(\<lambda>n. Norm (\<LL> p M) (f (r n))) \<longlonglongrightarrow> l\<close> unfolding PInf by auto
    qed
    ultimately have "AE x in M. \<bar>g x\<bar> \<le> l" using \<open>AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> g x\<close> by auto
    then have "g \<in> space\<^sub>N (\<LL> \<infinity> M)" "Norm (\<LL> \<infinity> M) g \<le> l"
      using L_infinity_I[OF \<open>g \<in> borel_measurable M\<close> _ \<open>l \<ge> 0\<close>] by auto
    then have "eNorm (\<LL> \<infinity> M) g \<le> le"
      unfolding eNorm_Norm[OF \<open>g \<in> space\<^sub>N (\<LL> \<infinity> M)\<close>] \<open>le = ennreal l\<close> using ennreal_leI by auto
    then show ?thesis unfolding le_def \<open>p = \<infinity>\<close> by simp
  qed
qed

lemma Lp_AE_limit':
  assumes "g \<in> borel_measurable M"
          "\<And>n. f n \<in> space\<^sub>N (\<LL> p M)"
          "AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> g x"
          "(\<lambda>n. Norm (\<LL> p M) (f n)) \<longlonglongrightarrow> l"
  shows "g \<in> space\<^sub>N (\<LL> p M)"
        "Norm (\<LL> p M) g \<le> l"
proof -
  have "l \<ge> 0" by (rule LIMSEQ_le_const[OF \<open>(\<lambda>n. Norm (\<LL> p M) (f n)) \<longlonglongrightarrow> l\<close>], auto)
  have "(\<lambda>n. eNorm (\<LL> p M) (f n)) \<longlonglongrightarrow> ennreal l"
    unfolding eNorm_Norm[OF \<open>\<And>n. f n \<in> space\<^sub>N (\<LL> p M)\<close>] using \<open>(\<lambda>n. Norm (\<LL> p M) (f n)) \<longlonglongrightarrow> l\<close> by auto
  then have *: "ennreal l = liminf (\<lambda>n. eNorm (\<LL> p M) (f n))"
    using lim_imp_Liminf[symmetric] trivial_limit_sequentially by blast
  have "eNorm (\<LL> p M) g \<le> ennreal l"
    unfolding * apply (rule Lp_AE_limit) using assms by auto
  then have "eNorm (\<LL> p M) g < \<infinity>" using le_less_trans by fastforce
  then show "g \<in> space\<^sub>N (\<LL> p M)" using spaceN_iff by auto
  show "Norm (\<LL> p M) g \<le> l"
    using \<open>eNorm (\<LL> p M) g \<le> ennreal l\<close> ennreal_le_iff[OF \<open>l \<ge> 0\<close>]
    unfolding eNorm_Norm[OF \<open>g \<in> space\<^sub>N (\<LL> p M)\<close>] by auto
qed

lemma Lp_AE_limit'':
  assumes "g \<in> borel_measurable M"
          "\<And>n. f n \<in> space\<^sub>N (\<LL> p M)"
          "AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> g x"
          "\<And>n. Norm (\<LL> p M) (f n) \<le> C"
  shows "g \<in> space\<^sub>N (\<LL> p M)"
        "Norm (\<LL> p M) g \<le> C"
proof -
  have "C \<ge> 0" by (rule order_trans[OF Norm_nonneg[of "\<LL> p M" "f 0"] \<open>Norm (\<LL> p M) (f 0) \<le> C\<close>])
  have *: "liminf (\<lambda>n. ennreal C) = ennreal C"
    using Liminf_const trivial_limit_at_top_linorder by blast
  have "eNorm (\<LL> p M) (f n) \<le> ennreal C" for n
    unfolding eNorm_Norm[OF \<open>f n \<in> space\<^sub>N (\<LL> p M)\<close>]
    using \<open>Norm (\<LL> p M) (f n) \<le> C\<close> by (auto simp add: ennreal_leI)
  then have "liminf (\<lambda>n. eNorm (\<LL> p M) (f n)) \<le> ennreal C"
    using Liminf_mono[of "(\<lambda>n. eNorm (\<LL> p M) (f n))" "\<lambda>_. C" sequentially] * by auto
  then have "eNorm (\<LL> p M) g \<le> ennreal C" using
    Lp_AE_limit[OF \<open>g \<in> borel_measurable M\<close> \<open>AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> g x\<close>, of p] by auto
  then have "eNorm (\<LL> p M) g < \<infinity>" using le_less_trans by fastforce
  then show "g \<in> space\<^sub>N (\<LL> p M)" using spaceN_iff by auto
  show "Norm (\<LL> p M) g \<le> C"
    using \<open>eNorm (\<LL> p M) g \<le> ennreal C\<close> ennreal_le_iff[OF \<open>C \<ge> 0\<close>]
    unfolding eNorm_Norm[OF \<open>g \<in> space\<^sub>N (\<LL> p M)\<close>] by auto
qed

text \<open>We give the version of Lebesgue dominated convergence theorem in the setting of
$L^p$ spaces.\<close>

proposition Lp_domination_limit:
  fixes p::real
  assumes [measurable]: "g \<in> borel_measurable M"
          "\<And>n. f n \<in> borel_measurable M"
      and "m \<in> space\<^sub>N (\<LL> p M)"
          "AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> g x"
          "\<And>n. AE x in M. \<bar>f n x\<bar> \<le> m x"
  shows "g \<in> space\<^sub>N (\<LL> p M)"
        "tendsto_in\<^sub>N (\<LL> p M) f g"
proof -
  have [measurable]: "m \<in> borel_measurable M" using Lp_measurable[OF \<open>m \<in> space\<^sub>N (\<LL> p M)\<close>] by auto
  have "f n \<in> space\<^sub>N(\<LL> p M)" for n
    apply (rule Lp_domination[OF _ \<open>m \<in> space\<^sub>N (\<LL> p M)\<close>]) using \<open>AE x in M. \<bar>f n x\<bar> \<le> m x\<close> by auto

  have "AE x in M. \<forall>n. \<bar>f n x\<bar> \<le> m x"
    apply (subst AE_all_countable) using \<open>\<And>n. AE x in M. \<bar>f n x\<bar> \<le> m x\<close> by auto
  moreover have "\<bar>g x\<bar> \<le> m x" if "\<forall>n. \<bar>f n x\<bar> \<le> m x" "(\<lambda>n. f n x) \<longlonglongrightarrow> g x" for x
    apply (rule LIMSEQ_le_const2[of "\<lambda>n. \<bar>f n x\<bar>"]) using that by (auto intro!:tendsto_intros)
  ultimately have *: "AE x in M. \<bar>g x\<bar> \<le> m x" using \<open>AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> g x\<close> by auto
  show "g \<in> space\<^sub>N(\<LL> p M)"
    apply (rule Lp_domination[OF _ \<open>m \<in> space\<^sub>N (\<LL> p M)\<close>]) using * by auto

  have "(\<lambda>n. Norm (\<LL> p M) (f n - g)) \<longlonglongrightarrow> 0"
  proof (cases "p \<le> 0")
    case True
    then have "ennreal p = 0" by (simp add: ennreal_eq_0_iff)
    then show ?thesis unfolding Norm_def by (auto simp add: L_zero(1))
  next
    case False
    then have "p > 0" by auto
    have "(\<lambda>n. (\<integral>x. \<bar>f n x - g x\<bar> powr p \<partial>M)) \<longlonglongrightarrow> (\<integral>x. \<bar>0\<bar> powr p \<partial>M)"
    proof (rule integral_dominated_convergence[of _ _ _ "(\<lambda>x. \<bar>2 * m x\<bar> powr p)"], auto)
      show "integrable M (\<lambda>x. \<bar>2 * m x\<bar> powr p)"
        unfolding abs_mult apply (subst powr_mult)
        using Lp_D(2)[OF \<open>p > 0\<close> \<open>m \<in> space\<^sub>N (\<LL> p M)\<close>] by auto
      have "(\<lambda>n. \<bar>f n x - g x\<bar> powr p) \<longlonglongrightarrow> \<bar>0\<bar> powr p" if "(\<lambda>n. f n x) \<longlonglongrightarrow> g x" for x
        apply (rule tendsto_powr') using \<open>p > 0\<close> that apply (auto)
        using Lim_null tendsto_rabs_zero_iff by fastforce
      then show "AE x in M. (\<lambda>n. \<bar>f n x - g x\<bar> powr p) \<longlonglongrightarrow> 0"
        using \<open>AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> g x\<close> by auto
      have "\<bar>f n x - g x\<bar> powr p \<le> \<bar>2 * m x\<bar> powr p" if "\<bar>f n x\<bar> \<le> m x" "\<bar>g x\<bar> \<le> m x" for n x
        using powr_mono2 \<open>p > 0\<close> that by auto
      then show "AE x in M. \<bar>f n x - g x\<bar> powr p \<le> \<bar>2 * m x\<bar> powr p" for n
        using \<open>AE x in M. \<bar>f n x\<bar> \<le> m x\<close> \<open>AE x in M. \<bar>g x\<bar> \<le> m x\<close> by auto
    qed
    then have "(\<lambda>n. (Norm (\<LL> p M) (f n - g)) powr p) \<longlonglongrightarrow> (Norm (\<LL> p M) 0) powr p"
      unfolding Lp_D[OF \<open>p > 0\<close> spaceN_diff[OF \<open>\<And>n. f n \<in> space\<^sub>N(\<LL> p M)\<close> \<open>g \<in> space\<^sub>N(\<LL> p M)\<close>]]
      using \<open>p > 0\<close> by (auto simp add: powr_powr)
    then have "(\<lambda>n. ((Norm (\<LL> p M) (f n - g)) powr p) powr (1/p)) \<longlonglongrightarrow> ((Norm (\<LL> p M) 0) powr p) powr (1/p)"
      by (rule tendsto_powr', auto simp add: \<open>p > 0\<close>)
    then show ?thesis using powr_powr \<open>p > 0\<close> by auto
  qed
  then show "tendsto_in\<^sub>N (\<LL> p M) f g"
    unfolding tendsto_in\<^sub>N_def by auto
qed

text \<open>We give the version of the monotone convergence theorem in the setting of
$L^p$ spaces.\<close>

proposition Lp_monotone_limit:
  fixes f::"nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "p > (0::ennreal)"
          "AE x in M. incseq (\<lambda>n. f n x)"
          "\<And>n. Norm (\<LL> p M) (f n) \<le> C"
          "\<And>n. f n \<in> space\<^sub>N (\<LL> p M)"
  shows "AE x in M. convergent (\<lambda>n. f n x)"
        "(\<lambda>x. lim (\<lambda>n. f n x)) \<in> space\<^sub>N (\<LL> p M)"
        "Norm (\<LL> p M) (\<lambda>x. lim (\<lambda>n. f n x)) \<le> C"
proof -
  have [measurable]: "f n \<in> borel_measurable M" for n using Lp_measurable[OF assms(4)].
  show "AE x in M. convergent (\<lambda>n. f n x)"
  proof (cases rule: Lp_cases[of p])
    case PInf
    have "AE x in M. \<bar>f n x\<bar> \<le> C" for n
      using L_infinity_AE_bound[of "f n" M] \<open>Norm (\<LL> p M) (f n) \<le> C\<close> \<open>f n \<in> space\<^sub>N (\<LL> p M)\<close>
      unfolding \<open>p=\<infinity>\<close> by auto
    then have *: "AE x in M. \<forall>n. \<bar>f n x\<bar> \<le> C"
      by (subst AE_all_countable, auto)
    have "(\<lambda>n. f n x) \<longlonglongrightarrow> (SUP n. f n x)" if "incseq (\<lambda>n. f n x)" "\<And>n. \<bar>f n x\<bar> \<le> C" for x
      apply (rule LIMSEQ_incseq_SUP[OF _ \<open>incseq (\<lambda>n. f n x)\<close>]) using that(2) abs_le_D1 by fastforce
    then have "convergent (\<lambda>n. f n x)" if "incseq (\<lambda>n. f n x)" "\<And>n. \<bar>f n x\<bar> \<le> C" for x
      unfolding convergent_def using that by auto
    then show ?thesis using \<open>AE x in M. incseq (\<lambda>n. f n x)\<close> * by auto
  next
    case (real_pos p2)
    define g where "g = (\<lambda>n. f n - f 0)"
    have "AE x in M. incseq (\<lambda>n. g n x)"
      unfolding g_def using \<open>AE x in M. incseq (\<lambda>n. f n x)\<close> by (simp add: incseq_def)
    have "g n \<in> space\<^sub>N (\<LL> p2 M)" for n
      unfolding g_def using \<open>\<And>n. f n \<in> space\<^sub>N (\<LL> p M)\<close> unfolding \<open>p = ennreal p2\<close> by auto
    then have [measurable]: "g n \<in> borel_measurable M" for n using Lp_measurable by auto
    define D where "D = defect (\<LL> p2 M) * C + defect (\<LL> p2 M) * C"
    have "Norm (\<LL> p2 M) (g n) \<le> D" for n
    proof -
      have "f n \<in> space\<^sub>N (\<LL> p2 M)" using \<open>f n \<in> space\<^sub>N (\<LL> p M)\<close> unfolding \<open>p = ennreal p2\<close> by auto
      have "Norm (\<LL> p2 M) (g n) \<le> defect (\<LL> p2 M) * Norm (\<LL> p2 M) (f n) + defect (\<LL> p2 M) * Norm (\<LL> p2 M) (f 0)"
        unfolding g_def using Norm_triangular_ineq_diff[OF \<open>f n \<in> space\<^sub>N (\<LL> p2 M)\<close>] by auto
      also have "... \<le> D"
        unfolding D_def apply(rule add_mono)
        using mult_left_mono defect_ge_1[of "\<LL> p2 M"] \<open>\<And>n. Norm (\<LL> p M) (f n) \<le> C\<close> unfolding \<open>p = ennreal p2\<close> by auto
      finally show ?thesis by simp
    qed
    have g_bound: "(\<integral>\<^sup>+x. \<bar>g n x\<bar> powr p2 \<partial>M) \<le> ennreal(D powr p2)" for n
    proof -
      have "(\<integral>\<^sup>+x. \<bar>g n x\<bar> powr p2 \<partial>M) = ennreal(\<integral>x. \<bar>g n x\<bar> powr p2 \<partial>M)"
        apply (rule nn_integral_eq_integral) using Lp_D(2)[OF \<open>p2 > 0\<close> \<open>g n \<in> space\<^sub>N (\<LL> p2 M)\<close>] by auto
      also have "... = ennreal((Norm (\<LL> p2 M) (g n)) powr p2)"
        apply (subst Lp_Norm(2)[OF \<open>p2 > 0\<close>, of "g n", symmetric]) by auto
      also have "... \<le> ennreal(D powr p2)"
        by (auto intro!: powr_mono2 simp add: less_imp_le[OF \<open>p2 > 0\<close>] \<open>Norm (\<LL> p2 M) (g n) \<le> D\<close>)
      finally show ?thesis by simp
    qed
    have "\<forall>n. g n x \<ge> 0" if "incseq (\<lambda>n. f n x)" for x
      unfolding g_def using that by (auto simp add: incseq_def)
    then have "AE x in M. \<forall>n. g n x \<ge> 0" using \<open>AE x in M. incseq (\<lambda>n. f n x)\<close> by auto

    define h where "h = (\<lambda>n x. ennreal(\<bar>g n x\<bar> powr p2))"
    have [measurable]: "h n \<in> borel_measurable M" for n unfolding h_def by auto
    define H where "H = (\<lambda>x. (SUP n. h n x))"
    have [measurable]: "H \<in> borel_measurable M" unfolding H_def by auto
    have "\<And>n. h n x \<le> h (Suc n) x" if "\<forall>n. g n x \<ge> 0" "incseq (\<lambda>n. g n x)" for x
      unfolding h_def apply (auto intro!:powr_mono2)
      apply (auto simp add: less_imp_le[OF \<open>p2 > 0\<close>]) using that incseq_SucD by auto
    then have *: "AE x in M. h n x \<le> h (Suc n) x" for n
      using \<open>AE x in M. \<forall>n. g n x \<ge> 0\<close> \<open>AE x in M. incseq (\<lambda>n. g n x)\<close> by auto
    have "(\<integral>\<^sup>+x. H x \<partial>M) = (SUP n. \<integral>\<^sup>+x. h n x \<partial>M)"
      unfolding H_def by (rule nn_integral_monotone_convergence_SUP_AE, auto simp add: *)
    also have "... \<le> ennreal(D powr p2)"
      unfolding H_def h_def using g_bound by (simp add: SUP_least)
    finally have "(\<integral>\<^sup>+x. H x \<partial>M) < \<infinity>" by (simp add: le_less_trans)
    then have "AE x in M. H x \<noteq> \<infinity>"
      by (metis (mono_tags, lifting) \<open>H \<in> borel_measurable M\<close> infinity_ennreal_def nn_integral_noteq_infinite top.not_eq_extremum)

    have "convergent (\<lambda>n. f n x)" if "H x \<noteq> \<infinity>" "incseq (\<lambda>n. f n x)" for x
    proof -
      define A where "A = enn2real(H x)"
      then have "H x = ennreal A" using \<open>H x \<noteq> \<infinity>\<close> by (simp add: ennreal_enn2real_if)
      have "f n x \<le> f 0 x + A powr (1/p2)" for n
      proof -
        have "ennreal(\<bar>g n x\<bar> powr p2) \<le> ennreal A"
          unfolding \<open>H x = ennreal A\<close>[symmetric] H_def h_def by (meson SUP_upper2 UNIV_I order_refl)
        then have "\<bar>g n x\<bar> powr p2 \<le> A"
          by (subst ennreal_le_iff[symmetric], auto simp add: A_def)
        have "\<bar>g n x\<bar> = (\<bar>g n x\<bar> powr p2) powr (1/p2)"
          using \<open>p2 > 0\<close> by (simp add: powr_powr)
        also have "... \<le> A powr (1/p2)"
          apply (rule powr_mono2) using \<open>p2 > 0\<close> \<open>\<bar>g n x\<bar> powr p2 \<le> A\<close> by auto
        finally have "\<bar>g n x\<bar> \<le> A powr (1/p2)" by simp
        then show ?thesis unfolding g_def by auto
      qed
      then show "convergent (\<lambda>n. f n x)"
        using LIMSEQ_incseq_SUP[OF _ \<open>incseq (\<lambda>n. f n x)\<close>] convergent_def by (metis bdd_aboveI2)
    qed
    then show "AE x in M. convergent (\<lambda>n. f n x)"
      using \<open>AE x in M. H x \<noteq> \<infinity>\<close> \<open>AE x in M. incseq (\<lambda>n. f n x)\<close> by auto
  qed (insert \<open>p>0\<close>, simp)
  then have lim: "AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> lim (\<lambda>n. f n x)"
    using convergent_LIMSEQ_iff by auto
  show "(\<lambda>x. lim (\<lambda>n. f n x)) \<in> space\<^sub>N (\<LL> p M)"
    apply (rule Lp_AE_limit''[of _ _ f, OF _ \<open>\<And>n. f n \<in> space\<^sub>N (\<LL> p M)\<close> lim \<open>\<And>n. Norm (\<LL> p M) (f n) \<le> C\<close>])
    by auto
  show "Norm (\<LL> p M) (\<lambda>x. lim (\<lambda>n. f n x)) \<le> C"
    apply (rule Lp_AE_limit''[of _ _ f, OF _ \<open>\<And>n. f n \<in> space\<^sub>N (\<LL> p M)\<close> lim \<open>\<And>n. Norm (\<LL> p M) (f n) \<le> C\<close>])
    by auto
qed


subsection \<open>Completeness of $L^p$\<close>

text \<open>We prove the completeness of $L^p$.\<close>

theorem Lp_complete:
  "complete\<^sub>N (\<LL> p M)"
proof (cases rule: Lp_cases[of p])
  case zero
  show ?thesis
  proof (rule complete\<^sub>N_I)
    fix u assume "\<forall>(n::nat). u n \<in> space\<^sub>N (\<LL> p M)"
    then have "tendsto_in\<^sub>N (\<LL> p M) u 0"
      unfolding tendsto_in\<^sub>N_def Norm_def \<open>p = 0\<close> L_zero(1) L_zero_space by auto
    then show "\<exists>x\<in>space\<^sub>N (\<LL> p M). tendsto_in\<^sub>N (\<LL> p M) u x"
      by auto
  qed
next
  case (real_pos p2)
  show ?thesis
  proof (rule complete\<^sub>N_I'[of "\<lambda>n. (1/2)^n * (1/(defect (\<LL> p M))^(Suc n))"], unfold \<open>p = ennreal p2\<close>)
    show "0 < (1 / 2) ^ n * (1 / defect (\<LL> (ennreal p2) M) ^ Suc n)" for n
      using defect_ge_1[of "\<LL> (ennreal p2) M"] by (auto simp add: divide_simps)

    fix u assume "\<forall>(n::nat). u n \<in> space\<^sub>N (\<LL> p2 M)" "\<forall>n. Norm (\<LL> p2 M) (u n) \<le> (1/2)^n * (1/(defect (\<LL> p2 M))^(Suc n))"
    then have H: "\<And>n. u n \<in> space\<^sub>N (\<LL> p2 M)"
                 "\<And>n. Norm (\<LL> p2 M) (u n) \<le> (1 / 2) ^ n * (1/(defect (\<LL> p2 M))^(Suc n))"
      unfolding \<open>p = ennreal p2\<close> by auto
    have [measurable]: "u n \<in> borel_measurable M" for n using Lp_measurable[OF H(1)].

    define w where "w = (\<lambda>N x. (\<Sum>n\<in>{..<N}. \<bar>u n x\<bar>))"
    have w2: "w = (\<lambda>N. sum (\<lambda>n x. \<bar>u n x\<bar>) {..<N})" unfolding w_def apply (rule ext)+
      by (metis (mono_tags, lifting) sum.cong fun_sum_apply)
    have "incseq (\<lambda>N. w N x)" for x unfolding w2 by (rule incseq_SucI, auto)
    then have wN_inc: "AE x in M. incseq (\<lambda>N. w N x)" by simp

    have abs_u_space: "(\<lambda>x. \<bar>u n x\<bar>) \<in> space\<^sub>N (\<LL> p2 M)" for n
      by (rule Lp_Banach_lattice[OF \<open>u n \<in> space\<^sub>N (\<LL> p2 M)\<close>])
    then have wN_space: "w N \<in> space\<^sub>N (\<LL> p2 M)" for N unfolding w2 using H(1) by auto
    have abs_u_Norm: "Norm (\<LL> p2 M) (\<lambda>x. \<bar>u n x\<bar>) \<le> (1 / 2) ^ n * (1/(defect (\<LL> p2 M))^(Suc n))" for n
      using Lp_Banach_lattice(2)[OF \<open>u n \<in> space\<^sub>N (\<LL> p2 M)\<close>] H(2) by auto

    have wN_Norm: "Norm (\<LL> p2 M) (w N) \<le> 2" for N
    proof -
      have *: "(defect (\<LL> p2 M))^(Suc n) \<ge> 0" "(defect (\<LL> p2 M))^(Suc n) > 0" for n
        using defect_ge_1[of "\<LL> p2 M"] by auto
      have "Norm (\<LL> p2 M) (w N) \<le> (\<Sum>n<N. (defect (\<LL> p2 M))^(Suc n) * Norm (\<LL> p2 M) (\<lambda>x. \<bar>u n x\<bar>))"
        unfolding w2 lessThan_Suc_atMost[symmetric] by (rule Norm_sum, simp add: abs_u_space)
      also have "... \<le> (\<Sum>n<N. (defect (\<LL> p2 M))^(Suc n) * ((1 / 2) ^ n * (1/(defect (\<LL> p2 M))^(Suc n))))"
        apply (rule sum_mono, rule mult_left_mono) using abs_u_Norm * by auto
      also have "... = (\<Sum>n<N. (1 / 2) ^ n)"
        using *(2) defect_ge_1[of "\<LL> p2 M"] by (auto simp add: algebra_simps)
      also have "... \<le> (\<Sum>n. (1 / 2) ^ n)"
        unfolding lessThan_Suc_atMost[symmetric] by (rule sum_le_suminf, rule summable_geometric[of "1/2"], auto)
      also have "... = 2" using suminf_geometric[of "1/2"] by auto
      finally show ?thesis by simp
    qed

    have "AE x in M. convergent (\<lambda>N. w N x)"
      apply (rule Lp_monotone_limit[OF \<open>p > 0\<close>, of _ _ 2], unfold \<open>p = ennreal p2\<close>)
      using wN_inc wN_Norm wN_space by auto
    define m where "m = (\<lambda>x. lim (\<lambda>N. w N x))"
    have m_space: "m \<in> space\<^sub>N (\<LL> p2 M)"
      unfolding m_def \<open>p = ennreal p2\<close>[symmetric] apply (rule Lp_monotone_limit[OF \<open>p > 0\<close>, of _ _ 2], unfold \<open>p = ennreal p2\<close>)
      using wN_inc wN_Norm wN_space by auto

    define v where "v = (\<lambda>x. (\<Sum>n. u n x))"
    have v_meas: "v \<in> borel_measurable M" unfolding v_def by auto
    have u_meas: "\<And>n. (sum u {0..<n}) \<in> borel_measurable M" by auto
    {
      fix x assume "convergent (\<lambda>N. w N x)"
      then have S: "summable (\<lambda>n. \<bar>u n x\<bar>)" unfolding w_def using summable_iff_convergent by auto
      then have "m x = (\<Sum>n. \<bar>u n x\<bar>)" unfolding m_def w_def by (metis suminf_eq_lim)

      have "summable (\<lambda>n. u n x)" using S by (rule summable_rabs_cancel)
      then have *: "(\<lambda>n. (sum u {..<n}) x) \<longlonglongrightarrow> v x"
        unfolding v_def fun_sum_apply by (metis convergent_LIMSEQ_iff suminf_eq_lim summable_iff_convergent)
      have "\<bar>(sum u {..<n}) x\<bar> \<le> m x" for n
      proof -
        have "\<bar>(sum u {..<n}) x\<bar> \<le> (\<Sum>i\<in>{..<n}. \<bar>u i x\<bar>)"
          unfolding fun_sum_apply by auto
        also have "... \<le> (\<Sum>i. \<bar>u i x\<bar>)"
          apply (rule sum_le_suminf) using S by auto
        finally show ?thesis using \<open>m x = (\<Sum>n. \<bar>u n x\<bar>)\<close> by simp
      qed
      then have "(\<forall>n. \<bar>(sum u {0..<n}) x\<bar> \<le> m x) \<and> (\<lambda>n. (sum u {0..<n}) x) \<longlonglongrightarrow> v x"
        unfolding atLeast0LessThan using * by auto
    }
    then have m_bound: "\<And>n. AE x in M. \<bar>(sum u {0..<n}) x\<bar> \<le> m x"
          and u_conv: "AE x in M. (\<lambda>n. (sum u {0..<n}) x) \<longlonglongrightarrow> v x"
      using \<open>AE x in M. convergent (\<lambda>N. w N x)\<close> by auto

    have "tendsto_in\<^sub>N (\<LL> p2 M) (\<lambda>n. sum u {0..<n}) v"
      by (rule Lp_domination_limit[OF v_meas u_meas m_space u_conv m_bound])
    moreover have "v \<in> space\<^sub>N (\<LL> p2 M)"
      by (rule Lp_domination_limit[OF v_meas u_meas m_space u_conv m_bound])
    ultimately show "\<exists>v \<in> space\<^sub>N (\<LL> p2 M). tendsto_in\<^sub>N (\<LL> p2 M) (\<lambda>n. sum u {0..<n}) v"
      by auto
  qed
next
  case PInf
  show ?thesis
  proof (rule complete\<^sub>N_I'[of "\<lambda>n. (1/2)^n"])
    fix u assume "\<forall>(n::nat). u n \<in> space\<^sub>N (\<LL> p M)" "\<forall>n. Norm (\<LL> p M) (u n) \<le> (1 / 2) ^ n"
    then have H: "\<And>n. u n \<in> space\<^sub>N (\<LL> \<infinity> M)" "\<And>n. Norm (\<LL> \<infinity> M) (u n) \<le> (1 / 2) ^ n" using PInf by auto
    have [measurable]: "u n \<in> borel_measurable M" for n using Lp_measurable[OF H(1)] by auto
    define v where "v = (\<lambda>x. \<Sum>n. u n x)"
    have [measurable]: "v \<in> borel_measurable M" unfolding v_def by auto
    define w where "w = (\<lambda>N x. (\<Sum>n\<in>{0..<N}. u n x))"
    have [measurable]: "w N \<in> borel_measurable M" for N unfolding w_def by auto

    have "AE x in M. \<bar>u n x\<bar> \<le> (1/2)^n" for n
      using L_infinity_AE_bound[OF H(1), of n] H(2)[of n] by auto
    then have "AE x in M. \<forall>n. \<bar>u n x\<bar> \<le> (1/2)^n"
      by (subst AE_all_countable, auto)
    moreover have "\<bar>w N x - v x\<bar> \<le> (1/2)^N * 2" if "\<forall>n. \<bar>u n x\<bar> \<le> (1/2)^n" for N x
    proof -
      have *: "\<And>n. \<bar>u n x\<bar> \<le> (1/2)^n" using that by auto
      have **: "summable (\<lambda>n. \<bar>u n x\<bar>)"
        apply (rule summable_norm_cancel, rule summable_comparison_test'[OF summable_geometric[of "1/2"]])
        using * by auto
      have "\<bar>w N x - v x\<bar> = \<bar>(\<Sum>n. u (n + N) x)\<bar>"
        unfolding v_def w_def
        apply (subst suminf_split_initial_segment[OF summable_rabs_cancel[OF \<open>summable (\<lambda>n. \<bar>u n x\<bar>)\<close>], of "N"])
        by (simp add: lessThan_atLeast0)
      also have "... \<le> (\<Sum>n. \<bar>u (n + N) x\<bar>)"
        apply (rule summable_rabs, subst summable_iff_shift) using ** by auto
      also have "... \<le> (\<Sum>n. (1/2)^(n + N))"
        apply (rule suminf_le)
        apply (intro allI) using *[of "_ + N"] apply simp
        apply (subst summable_iff_shift) using ** apply simp
        apply (subst summable_iff_shift) using summable_geometric[of "1/2"] by auto
      also have "... = (1/2)^N * (\<Sum>n. (1/2)^n)"
        by (subst power_add, subst suminf_mult2[symmetric], auto simp add: summable_geometric[of "1/2"])
      also have "... = (1/2)^N * 2"
        by (subst suminf_geometric, auto)
      finally show ?thesis by simp
    qed
    ultimately have *: "AE x in M. \<bar>w N x - v x\<bar> \<le> (1/2)^N * 2" for N by auto

    have **: "w N - v \<in> space\<^sub>N (\<LL> \<infinity> M)" "Norm (\<LL> \<infinity> M) (w N - v) \<le> (1/2)^N * 2" for N
      unfolding fun_diff_def using L_infinity_I[OF _ *] by auto
    have l: "(\<lambda>N. ((1/2)^N) * (2::real)) \<longlonglongrightarrow> 0 * 2"
      by (rule tendsto_mult, auto simp add: LIMSEQ_realpow_zero[of "1/2"])
    have "tendsto_in\<^sub>N (\<LL> \<infinity> M) w v" unfolding tendsto_in\<^sub>N_def
      apply (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. (1/2)^n * 2"]) using l **(2) by auto
    have "v = - (w 0 - v)" unfolding w_def by auto
    then have "v \<in> space\<^sub>N (\<LL> \<infinity> M)" using **(1)[of 0] spaceN_add spaceN_diff by fastforce
    then show "\<exists>v \<in> space\<^sub>N (\<LL> p M). tendsto_in\<^sub>N (\<LL> p M) (\<lambda>n. sum u {0..<n}) v"
      using \<open>tendsto_in\<^sub>N (\<LL> \<infinity> M) w v\<close> unfolding \<open>p = \<infinity>\<close> w_def fun_sum_apply[symmetric] by auto
  qed (simp)
qed


subsection \<open>Multiplication of functions, duality\<close>

text \<open>The next theorem asserts that the multiplication of two functions in $L^p$ and $L^q$ belongs to
$L^r$, where $r$ is determined by the equality $1/r = 1/p + 1/q$. This is essentially a case by case
analysis, depending on the kind of $L^p$ space we are considering. The only nontrivial case is
when $p$, $q$ (and $r$) are finite and nonzero. In this case, it reduces to H\"older inequality.\<close>

theorem Lp_Lq_mult:
  fixes p q r::ennreal
  assumes "1/p + 1/q = 1/r"
      and "f \<in> space\<^sub>N (\<LL> p M)" "g \<in> space\<^sub>N (\<LL> q M)"
  shows "(\<lambda>x. f x * g x) \<in> space\<^sub>N (\<LL> r M)"
        "Norm (\<LL> r M) (\<lambda>x. f x * g x) \<le> Norm (\<LL> p M) f * Norm (\<LL> q M) g"
proof -
  have [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M" using Lp_measurable assms by auto
  have "(\<lambda>x. f x * g x) \<in> space\<^sub>N (\<LL> r M) \<and> Norm (\<LL> r M) (\<lambda>x. f x * g x) \<le> Norm (\<LL> p M) f * Norm (\<LL> q M) g"
  proof (cases rule: Lp_cases[of r])
    case zero
    have *: "(\<lambda>x. f x * g x) \<in> borel_measurable M" by auto
    then have "Norm (\<LL> r M) (\<lambda>x. f x * g x) = 0" using L_zero[of M] unfolding Norm_def zero by auto
    then have "Norm (\<LL> r M) (\<lambda>x. f x * g x) \<le> Norm (\<LL> p M) f * Norm (\<LL> q M) g"
      using Norm_nonneg by auto
    then show ?thesis unfolding zero using * L_zero_space[of M] by auto
  next
    case (real_pos r2)
    have "p > 0" "q > 0" using \<open>1/p + 1/q = 1/r\<close> \<open>r > 0\<close>
      by (metis ennreal_add_eq_top ennreal_divide_eq_top_iff ennreal_top_neq_one gr_zeroI zero_neq_one)+
    consider "p = \<infinity>" | "q = \<infinity>" | "p < \<infinity> \<and> q < \<infinity>" using top.not_eq_extremum by force
    then show ?thesis
    proof (cases)
      case 1
      then have "q = r" using \<open>1/p + 1/q = 1/r\<close>
        by (metis ennreal_divide_top infinity_ennreal_def one_divide_one_divide_ennreal semiring_normalization_rules(5))
      have "AE x in M. \<bar>f x\<bar> \<le> Norm (\<LL> p M) f"
        using \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> L_infinity_AE_bound unfolding \<open>p = \<infinity>\<close> by auto
      then have *: "AE x in M. \<bar>f x * g x\<bar> \<le> \<bar>Norm (\<LL> p M) f * g x\<bar>"
        unfolding abs_mult using Norm_nonneg[of "\<LL> p M" f] mult_right_mono by fastforce
      have **: "(\<lambda>x. Norm (\<LL> p M) f * g x) \<in> space\<^sub>N (\<LL> r M)"
        using spaceN_cmult[OF \<open>g \<in> space\<^sub>N (\<LL> q M)\<close>] unfolding \<open>q = r\<close> scaleR_fun_def by simp
      have ***: "Norm (\<LL> r M) (\<lambda>x. Norm (\<LL> p M) f * g x) = Norm (\<LL> p M) f * Norm (\<LL> q M) g"
        using Norm_cmult[of "\<LL> r M"] unfolding \<open>q = r\<close> scaleR_fun_def by auto
      then show ?thesis
        using Lp_domination[of "\<lambda>x. f x * g x" M "\<lambda>x. Norm (\<LL> p M) f * g x" r] unfolding \<open>q = r\<close>
        using * ** *** by auto
    next
      case 2
      then have "p = r" using \<open>1/p + 1/q = 1/r\<close>
        by (metis add.right_neutral ennreal_divide_top infinity_ennreal_def one_divide_one_divide_ennreal)
      have "AE x in M. \<bar>g x\<bar> \<le> Norm (\<LL> q M) g"
        using \<open>g \<in> space\<^sub>N (\<LL> q M)\<close> L_infinity_AE_bound unfolding \<open>q = \<infinity>\<close> by auto
      then have *: "AE x in M. \<bar>f x * g x\<bar> \<le> \<bar>Norm (\<LL> q M) g * f x\<bar>"
        apply (simp only: mult.commute[of "Norm (\<LL> q M) g" _])
        unfolding abs_mult using mult_left_mono Norm_nonneg[of "\<LL> q M" g] by fastforce
      have **: "(\<lambda>x. Norm (\<LL> q M) g * f x) \<in> space\<^sub>N (\<LL> r M)"
        using spaceN_cmult[OF \<open>f \<in> space\<^sub>N (\<LL> p M)\<close>] unfolding \<open>p = r\<close> scaleR_fun_def by simp
      have ***: "Norm (\<LL> r M) (\<lambda>x. Norm (\<LL> q M) g * f x) = Norm (\<LL> p M) f * Norm (\<LL> q M) g"
        using Norm_cmult[of "\<LL> r M"] unfolding \<open>p = r\<close> scaleR_fun_def by auto
      then show ?thesis
        using Lp_domination[of "\<lambda>x. f x * g x" M "\<lambda>x. Norm (\<LL> q M) g * f x" r] unfolding \<open>p = r\<close>
        using * ** *** by auto
    next
      case 3
      obtain p2 where "p = ennreal p2" "p2 > 0"
        using enn2real_positive_iff[of p] 3 \<open>p > 0\<close> by (cases p) auto
      obtain q2 where "q = ennreal q2" "q2 > 0"
        using enn2real_positive_iff[of q] 3 \<open>q > 0\<close> by (cases q) auto

      have "ennreal(1/r2) = 1/r"
        using \<open>r = ennreal r2\<close> \<open>r2 > 0\<close> divide_ennreal zero_le_one by fastforce
      also have "... = 1/p + 1/q" using assms by auto
      also have "... = ennreal(1/p2 + 1/q2)" using \<open>p = ennreal p2\<close> \<open>p2 > 0\<close> \<open>q = ennreal q2\<close> \<open>q2 > 0\<close>
        apply (simp only: divide_ennreal ennreal_1[symmetric]) using ennreal_plus[of "1/p2" "1/q2", symmetric] by auto
      finally have *: "1/r2 = 1/p2 + 1/q2"
        using ennreal_inj \<open>p2 > 0\<close> \<open>q2 > 0\<close> \<open>r2 > 0\<close> by (metis divide_pos_pos ennreal_less_zero_iff le_less zero_less_one)

      define P where "P = p2 / r2"
      define Q where "Q = q2 / r2"
      have [simp]: "P > 0" "Q > 0" and "1/P + 1/Q = 1"
        using \<open>p2 > 0\<close> \<open>q2 > 0\<close> \<open>r2 > 0\<close> * unfolding P_def Q_def by (auto simp add: divide_simps algebra_simps)
      have Pa: "(\<bar>z\<bar> powr r2) powr P = \<bar>z\<bar> powr p2" for z
        unfolding P_def powr_powr using \<open>r2 > 0\<close> by auto
      have Qa: "(\<bar>z\<bar> powr r2) powr Q = \<bar>z\<bar> powr q2" for z
        unfolding Q_def powr_powr using \<open>r2 > 0\<close> by auto

      have *: "integrable M (\<lambda>x. \<bar>f x\<bar> powr r2 * \<bar>g x\<bar> powr r2)"
        apply (rule Holder_inequality[OF \<open>P>0\<close> \<open>Q>0\<close> \<open>1/P + 1/Q = 1\<close>], auto simp add: Pa Qa)
        using \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> unfolding \<open>p = ennreal p2\<close> using Lp_space[OF \<open>p2 > 0\<close>] apply auto
        using \<open>g \<in> space\<^sub>N (\<LL> q M)\<close> unfolding \<open>q = ennreal q2\<close> using Lp_space[OF \<open>q2 > 0\<close>] by auto
      have "(\<lambda>x. f x * g x) \<in> space\<^sub>N (\<LL> r M)"
        unfolding \<open>r = ennreal r2\<close> using Lp_space[OF \<open>r2 > 0\<close>, of M] by (auto simp add: * abs_mult powr_mult)
      have "Norm (\<LL> r M) (\<lambda>x. f x * g x) = (\<integral>x. \<bar>f x * g x\<bar> powr r2 \<partial>M) powr (1/r2)"
        unfolding \<open>r = ennreal r2\<close> using Lp_Norm[OF \<open>r2 > 0\<close>, of _ M] by auto
      also have "... = abs (\<integral>x. \<bar>f x\<bar> powr r2 * \<bar>g x\<bar> powr r2 \<partial>M) powr (1/r2)"
        by (auto simp add: powr_mult abs_mult)
      also have "... \<le> ((\<integral>x. \<bar> \<bar>f x\<bar> powr r2 \<bar> powr P \<partial>M) powr (1/P) * (\<integral>x. \<bar> \<bar>g x\<bar> powr r2 \<bar> powr Q \<partial>M) powr (1/Q)) powr (1/r2)"
        apply (rule powr_mono2, simp add: \<open>r2 > 0\<close> less_imp_le, simp)
        apply (rule Holder_inequality[OF \<open>P>0\<close> \<open>Q>0\<close> \<open>1/P + 1/Q = 1\<close>], auto simp add: Pa Qa)
        using \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> unfolding \<open>p = ennreal p2\<close> using Lp_space[OF \<open>p2 > 0\<close>] apply auto
        using \<open>g \<in> space\<^sub>N (\<LL> q M)\<close> unfolding \<open>q = ennreal q2\<close> using Lp_space[OF \<open>q2 > 0\<close>] by auto
      also have "... = (\<integral>x. \<bar>f x\<bar> powr p2 \<partial>M) powr (1/p2) * (\<integral>x. \<bar>g x\<bar> powr q2 \<partial>M) powr (1/q2)"
        apply (auto simp add: powr_mult powr_powr) unfolding P_def Q_def using \<open>r2 > 0\<close> by auto
      also have "... = Norm (\<LL> p M) f * Norm (\<LL> q M) g"
        unfolding \<open>p = ennreal p2\<close> \<open>q = ennreal q2\<close>
        using Lp_Norm[OF \<open>p2 > 0\<close>, of _ M] Lp_Norm[OF \<open>q2 > 0\<close>, of _ M] by auto
      finally show ?thesis using \<open>(\<lambda>x. f x * g x) \<in> space\<^sub>N (\<LL> r M)\<close> by auto
    qed
  next
    case PInf
    then have "p = \<infinity>" "q = r" using \<open>1/p + 1/q = 1/r\<close>
      by (metis add_eq_0_iff_both_eq_0 ennreal_divide_eq_0_iff infinity_ennreal_def not_one_le_zero order.order_iff_strict)+
    have "AE x in M. \<bar>f x\<bar> \<le> Norm (\<LL> p M) f"
      using \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> L_infinity_AE_bound unfolding \<open>p = \<infinity>\<close> by auto
    then have *: "AE x in M. \<bar>f x * g x\<bar> \<le> \<bar>Norm (\<LL> p M) f * g x\<bar>"
      unfolding abs_mult using Norm_nonneg[of "\<LL> p M" f] mult_right_mono by fastforce
    have **: "(\<lambda>x. Norm (\<LL> p M) f * g x) \<in> space\<^sub>N (\<LL> r M)"
      using spaceN_cmult[OF \<open>g \<in> space\<^sub>N (\<LL> q M)\<close>] unfolding \<open>q = r\<close> scaleR_fun_def by simp
    have ***: "Norm (\<LL> r M) (\<lambda>x. Norm (\<LL> p M) f * g x) = Norm (\<LL> p M) f * Norm (\<LL> q M) g"
      using Norm_cmult[of "\<LL> r M"] unfolding \<open>q = r\<close> scaleR_fun_def by auto
    then show ?thesis
      using Lp_domination[of "\<lambda>x. f x * g x" M "\<lambda>x. Norm (\<LL> p M) f * g x" r] unfolding \<open>q = r\<close>
      using * ** *** by auto
  qed
  then show "(\<lambda>x. f x * g x) \<in> space\<^sub>N (\<LL> r M)"
            "Norm (\<LL> r M) (\<lambda>x. f x * g x) \<le> Norm (\<LL> p M) f * Norm (\<LL> q M) g"
    by auto
qed

text \<open>The previous theorem admits an eNorm version in which one does not assume a priori
that the functions under consideration belong to $L^p$ or $L^q$.\<close>

theorem Lp_Lq_emult:
  fixes p q r::ennreal
  assumes "1/p + 1/q = 1/r"
          "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "eNorm (\<LL> r M) (\<lambda>x. f x * g x) \<le> eNorm (\<LL> p M) f * eNorm (\<LL> q M) g"
proof (cases "r = 0")
  case True
  then have "eNorm (\<LL> r M) (\<lambda>x. f x * g x) = 0"
    using assms by (simp add: L_zero(1))
  then show ?thesis by auto
next
  case False
  then have "r > 0" using not_gr_zero by blast
  then have "p > 0" "q > 0" using \<open>1/p + 1/q = 1/r\<close>
    by (metis ennreal_add_eq_top ennreal_divide_eq_top_iff ennreal_top_neq_one gr_zeroI zero_neq_one)+
  then have Z: "zero_space\<^sub>N (\<LL> p M) = {f \<in> borel_measurable M. AE x in M. f x = 0}"
               "zero_space\<^sub>N (\<LL> q M) = {f \<in> borel_measurable M. AE x in M. f x = 0}"
               "zero_space\<^sub>N (\<LL> r M) = {f \<in> borel_measurable M. AE x in M. f x = 0}"
    using \<open>r > 0\<close> Lp_infinity_zero_space by auto
  have [measurable]: "(\<lambda>x. f x * g x) \<in> borel_measurable M" using assms by auto
  consider "eNorm (\<LL> p M) f = 0 \<or> eNorm (\<LL> q M) g = 0"
         | "(eNorm (\<LL> p M) f > 0 \<and> eNorm (\<LL> q M) g = \<infinity>) \<or> (eNorm (\<LL> p M) f = \<infinity> \<and> eNorm (\<LL> q M) g > 0)"
         | "eNorm (\<LL> p M) f < \<infinity> \<and> eNorm (\<LL> q M) g < \<infinity>"
    using less_top by fastforce
  then show ?thesis
  proof (cases)
    case 1
    then have "(AE x in M. f x = 0) \<or> (AE x in M. g x = 0)" using Z unfolding zero_space\<^sub>N_def by auto
    then have "AE x in M. f x * g x = 0" by auto
    then have "eNorm (\<LL> r M) (\<lambda>x. f x * g x) = 0" using Z unfolding zero_space\<^sub>N_def by auto
    then show ?thesis by simp
  next
    case 2
    then have "eNorm (\<LL> p M) f * eNorm (\<LL> q M) g = \<infinity>" using ennreal_mult_eq_top_iff by force
    then show ?thesis by auto
  next
    case 3
    then have *: "f \<in> space\<^sub>N (\<LL> p M)" "g \<in> space\<^sub>N (\<LL> q M)" unfolding space\<^sub>N_def by auto
    then have "(\<lambda>x. f x * g x) \<in> space\<^sub>N (\<LL> r M)" using Lp_Lq_mult(1)[OF assms(1)] by auto
    then show ?thesis
      using Lp_Lq_mult(2)[OF assms(1) *] by (simp add: eNorm_Norm * ennreal_mult'[symmetric])
  qed
qed

lemma Lp_Lq_duality_bound:
  fixes p q::ennreal
  assumes "1/p + 1/q = 1"
          "f \<in> space\<^sub>N (\<LL> p M)"
          "g \<in> space\<^sub>N (\<LL> q M)"
  shows "integrable M (\<lambda>x. f x * g x)"
        "abs(\<integral>x. f x * g x \<partial>M) \<le> Norm (\<LL> p M) f * Norm (\<LL> q M) g"
proof -
  have "(\<lambda>x. f x * g x) \<in> space\<^sub>N (\<LL> 1 M)"
    apply (rule Lp_Lq_mult[OF _ \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> \<open>g \<in> space\<^sub>N (\<LL> q M)\<close>])
    using \<open>1/p + 1/q = 1\<close> by auto
  then show "integrable M (\<lambda>x. f x * g x)" using L1_space by auto

  have "abs(\<integral>x. f x * g x \<partial>M) \<le> Norm (\<LL> 1 M) (\<lambda>x. f x * g x)" using L1_int_ineq by auto
  also have "... \<le> Norm (\<LL> p M) f * Norm (\<LL> q M) g"
    apply (rule Lp_Lq_mult[OF _ \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> \<open>g \<in> space\<^sub>N (\<LL> q M)\<close>])
    using \<open>1/p + 1/q = 1\<close> by auto
  finally show "abs(\<integral>x. f x * g x \<partial>M) \<le> Norm (\<LL> p M) f * Norm (\<LL> q M) g" by simp
qed

text \<open>The next theorem asserts that the norm of an $L^p$ function $f$ can be obtained by estimating
the integrals of $fg$ over all $L^q$ functions $g$, where $1/p + 1/q = 1$. When $p = \infty$, it is
necessary to assume that the space is sigma-finite: for instance, if the space is one single atom
of infinite mass, then there is no nonzero $L^1$ function, so taking for $f$ the constant function
equal to $1$, it has $L^\infty$ norm equal to $1$, but $\int fg = 0$ for all $L^1$ function $g$.\<close>

theorem Lp_Lq_duality:
  fixes p q::ennreal
  assumes "f \<in> space\<^sub>N (\<LL> p M)"
          "1/p + 1/q = 1"
          "p = \<infinity> \<Longrightarrow> sigma_finite_measure M"
  shows "bdd_above ((\<lambda>g. (\<integral>x. f x * g x \<partial>M))`{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1})"
        "Norm (\<LL> p M) f = (SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. (\<integral>x. f x * g x \<partial>M))"
proof -
  have [measurable]: "f \<in> borel_measurable M" using Lp_measurable[OF assms(1)] by auto
  have B: "(\<integral>x. f x * g x \<partial>M) \<le> Norm (\<LL> p M) f" if "g \<in> {g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}" for g
  proof -
    have g: "g \<in> space\<^sub>N (\<LL> q M)" "Norm (\<LL> q M) g \<le> 1" using that by auto
    have "(\<integral>x. f x * g x \<partial>M) \<le> abs(\<integral>x. f x * g x \<partial>M)" by auto
    also have "... \<le> Norm (\<LL> p M) f * Norm (\<LL> q M) g"
      using Lp_Lq_duality_bound(2)[OF \<open>1/p + 1/q = 1\<close> \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> g(1)] by auto
    also have "... \<le> Norm (\<LL> p M) f"
      using g(2) Norm_nonneg[of "\<LL> p M" f] mult_left_le by blast
    finally show "(\<integral>x. f x * g x \<partial>M) \<le> Norm (\<LL> p M) f" by simp
  qed
  then show "bdd_above ((\<lambda>g. (\<integral>x. f x * g x \<partial>M))`{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1})"
    by (meson bdd_aboveI2)

  show "Norm (\<LL> p M) f = (SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. (\<integral>x. f x * g x \<partial>M))"
  proof (rule antisym)
    show "(SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. \<integral>x. f x * g x \<partial>M) \<le> Norm (\<LL> p M) f"
      by (rule cSUP_least, auto, rule exI[of _ 0], auto simp add: B)

    have "p \<ge> 1" using conjugate_exponent_ennrealI(1)[OF \<open>1/p + 1/q = 1\<close>] by simp
    show "Norm (\<LL> p M) f \<le> (SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. (\<integral>x. f x * g x \<partial>M))"
    using \<open>p \<ge> 1\<close> proof (cases rule: Lp_cases_1_PInf)
      case PInf
      then have "f \<in> space\<^sub>N (\<LL> \<infinity> M)"
        using \<open>f \<in> space\<^sub>N(\<LL> p M)\<close> by simp
      have "q = 1" using \<open>1/p + 1/q = 1\<close> \<open>p = \<infinity>\<close> by (simp add: divide_eq_1_ennreal)
      have "c \<le> (SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. (\<integral>x. f x * g x \<partial>M))" if "c < Norm (\<LL> p M) f" for c
      proof (cases "c < 0")
        case True
        then have "c \<le> (\<integral>x. f x * 0 x \<partial>M)" by auto
        also have "... \<le> (SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. (\<integral>x. f x * g x \<partial>M))"
          apply (rule cSUP_upper, auto simp add: zero_fun_def[symmetric]) using B by (meson bdd_aboveI2)
        finally show ?thesis by simp
      next
        case False
        then have "ennreal c < eNorm (\<LL> \<infinity> M) f"
          using eNorm_Norm[OF \<open>f \<in> space\<^sub>N (\<LL> p M)\<close>] that ennreal_less_iff unfolding \<open>p = \<infinity>\<close> by auto
        then have *: "emeasure M {x \<in> space M. \<bar>f x\<bar> > c} > 0" using L_infinity_pos_measure[of f M c] by auto
        obtain A where [measurable]: "\<And>(n::nat). A n \<in> sets M" and "(\<Union>i. A i) = space M" "\<And>i. emeasure M (A i) \<noteq> \<infinity>"
          using sigma_finite_measure.sigma_finite[OF \<open>p = \<infinity> \<Longrightarrow> sigma_finite_measure M\<close>[OF \<open>p = \<infinity>\<close>]] by (metis UNIV_I sets_range)
        define Y where "Y = (\<lambda>n::nat. {x \<in> A n. \<bar>f x\<bar> > c})"
        have [measurable]: "Y n \<in> sets M" for n unfolding Y_def by auto
        have "{x \<in> space M. \<bar>f x\<bar> > c} = (\<Union>n. Y n)" unfolding Y_def using \<open>(\<Union>i. A i) = space M\<close> by auto
        then have "emeasure M (\<Union>n. Y n) > 0" using * by auto
        then obtain n where "emeasure M (Y n) > 0"
          using emeasure_pos_unionE[of Y, OF \<open>\<And>n. Y n \<in> sets M\<close>] by auto
        have "emeasure M (Y n) \<le> emeasure M (A n)" apply (rule emeasure_mono) unfolding Y_def by auto
        then have "emeasure M (Y n) \<noteq> \<infinity>" using \<open>emeasure M (A n) \<noteq> \<infinity>\<close>
          by (metis infinity_ennreal_def neq_top_trans)
        then have "measure M (Y n) > 0" using \<open>emeasure M (Y n) > 0\<close> unfolding measure_def
          by (simp add: enn2real_positive_iff top.not_eq_extremum)
        have "\<bar>f x\<bar> \<ge> c" if "x \<in> Y n" for x using that less_imp_le unfolding Y_def by auto

        define g where "g = (\<lambda>x. indicator (Y n) x * sgn(f x)) /\<^sub>R measure M (Y n)"
        have "g \<in> space\<^sub>N (\<LL> 1 M)"
          apply (rule Lp_domination[of _ _ "indicator (Y n) /\<^sub>R measure M (Y n)"]) unfolding g_def
          using L1_indicator'[OF \<open>Y n \<in> sets M\<close> \<open>emeasure M (Y n) \<noteq> \<infinity>\<close>] by (auto simp add: abs_mult indicator_def abs_sgn_eq)
        have "Norm (\<LL> 1 M) g = Norm (\<LL> 1 M) (\<lambda>x. indicator (Y n) x * sgn(f x)) / abs(measure M (Y n))"
          unfolding g_def Norm_cmult by (simp add: divide_inverse)
        also have "... \<le> Norm (\<LL> 1 M) (indicator (Y n)) / abs(measure M (Y n))"
          using \<open>measure M (Y n) > 0\<close> apply (auto simp add: divide_simps) apply (rule Lp_domination)
          using L1_indicator'[OF \<open>Y n \<in> sets M\<close> \<open>emeasure M (Y n) \<noteq> \<infinity>\<close>] by (auto simp add: abs_mult indicator_def abs_sgn_eq)
        also have "... = measure M (Y n) / abs(measure M (Y n))"
          using L1_indicator'[OF \<open>Y n \<in> sets M\<close> \<open>emeasure M (Y n) \<noteq> \<infinity>\<close>] by (auto simp add: abs_mult indicator_def abs_sgn_eq)
        also have "... = 1" using \<open>measure M (Y n) > 0\<close> by auto
        finally have "Norm (\<LL> 1 M) g \<le> 1" by simp

        have "c * measure M (Y n) = (\<integral>x. c * indicator (Y n) x \<partial>M)"
          using \<open>measure M (Y n) > 0\<close> \<open>emeasure M (Y n) \<noteq> \<infinity>\<close> by auto
        also have "... \<le> (\<integral>x. \<bar>f x\<bar> * indicator (Y n) x \<partial>M)"
          apply (rule integral_mono)
          using \<open>emeasure M (Y n) \<noteq> \<infinity>\<close> \<open>0 < Sigma_Algebra.measure M (Y n)\<close> not_integrable_integral_eq apply fastforce
          apply (rule Bochner_Integration.integrable_bound[of _ "\<lambda>x. Norm (\<LL> \<infinity> M) f * indicator (Y n) x"])
          using \<open>emeasure M (Y n) \<noteq> \<infinity>\<close> \<open>0 < Sigma_Algebra.measure M (Y n)\<close> not_integrable_integral_eq apply fastforce
          using L_infinity_AE_bound[OF \<open>f \<in> space\<^sub>N (\<LL> \<infinity> M)\<close>] by (auto simp add: indicator_def Y_def)
        finally have "c \<le> (\<integral>x. \<bar>f x\<bar> * indicator (Y n) x \<partial>M) / measure M (Y n)"
          using \<open>measure M (Y n) > 0\<close> by (auto simp add: divide_simps)
        also have "... = (\<integral>x. f x * indicator (Y n) x * sgn(f x) / measure M (Y n) \<partial>M)"
          using \<open>measure M (Y n) > 0\<close> by (simp add: abs_sgn mult.commute mult.left_commute)
        also have "... = (\<integral>x. f x * g x \<partial>M)"
          unfolding divide_inverse g_def divideR_apply by (auto simp add: algebra_simps)
        also have "... \<le> (SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. (\<integral>x. f x * g x \<partial>M))"
          unfolding \<open>q = 1\<close> apply (rule cSUP_upper, auto)
          using \<open>g \<in> space\<^sub>N (\<LL> 1 M)\<close> \<open>Norm (\<LL> 1 M) g \<le> 1\<close> apply auto using B \<open>p = \<infinity>\<close> \<open>q = 1\<close> by (meson bdd_aboveI2)
        finally show ?thesis by simp
      qed
      then show ?thesis using dense_le by auto
    next
      case one
      then have "q = \<infinity>" using \<open>1/p + 1/q = 1\<close> by simp
      define g where "g = (\<lambda>x. sgn (f x))"
      have [measurable]: "g \<in> space\<^sub>N (\<LL> \<infinity> M)"
        apply (rule L_infinity_I[of g M 1]) unfolding g_def by (auto simp add: abs_sgn_eq)
      have "Norm (\<LL> \<infinity> M) g \<le> 1"
        apply (rule L_infinity_I[of g M 1]) unfolding g_def by (auto simp add: abs_sgn_eq)
      have "Norm (\<LL> p M) f = (\<integral>x. \<bar>f x\<bar> \<partial>M)"
        unfolding \<open>p = 1\<close> apply (rule L1_D(3)) using \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> unfolding \<open>p = 1\<close> by auto
      also have "... = (\<integral>x. f x * g x \<partial>M)"
        unfolding g_def by (simp add: abs_sgn)
      also have "... \<le> (SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. (\<integral>x. f x * g x \<partial>M))"
        unfolding \<open>q = \<infinity>\<close> apply (rule cSUP_upper, auto)
        using \<open>g \<in> space\<^sub>N (\<LL> \<infinity> M)\<close> \<open>Norm (\<LL> \<infinity> M) g \<le> 1\<close> apply auto
        using B \<open>q = \<infinity>\<close> by fastforce
      finally show ?thesis by simp
    next
      case (gr p2)
      then have "p2 > 0" by simp
      have "f \<in> space\<^sub>N (\<LL> p2 M)" using \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> \<open>p = ennreal p2\<close> by auto
      define q2 where "q2 = conjugate_exponent p2"
      have "q2 > 1" "q2 > 0" using conjugate_exponent_real(2)[OF \<open>p2 > 1\<close>] unfolding q2_def by auto
      have "q = ennreal q2"
        unfolding q2_def conjugate_exponent_real_ennreal[OF \<open>p2 > 1\<close>, symmetric] \<open>p = ennreal p2\<close>[symmetric]
        using conjugate_exponent_ennreal_iff[OF \<open>p \<ge> 1\<close>] \<open>1/p + 1/q = 1\<close> by auto

      show ?thesis
      proof (cases "Norm (\<LL> p M) f = 0")
        case True
        then have "Norm (\<LL> p M) f \<le> (\<integral>x. f x * 0 x \<partial>M)" by auto
        also have "... \<le> (SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. (\<integral>x. f x * g x \<partial>M))"
          apply (rule cSUP_upper, auto simp add: zero_fun_def[symmetric]) using B by (meson bdd_aboveI2)
        finally show ?thesis by simp
      next
        case False
        then have "Norm (\<LL> p2 M) f > 0"
          unfolding \<open>p = ennreal p2\<close> using Norm_nonneg[of "\<LL> p2 M" f] by linarith

        define h where "h = (\<lambda>x. sgn(f x) * \<bar>f x\<bar> powr (p2 - 1))"
        have [measurable]: "h \<in> borel_measurable M" unfolding h_def by auto
        have "(\<integral>\<^sup>+x. \<bar>h x\<bar> powr q2 \<partial>M) = (\<integral>\<^sup>+x. (\<bar>f x\<bar> powr (p2 - 1)) powr q2 \<partial>M)"
          unfolding h_def by (rule nn_integral_cong, auto simp add: abs_mult abs_sgn_eq)
        also have "... = (\<integral>\<^sup>+x. \<bar>f x\<bar> powr p2 \<partial>M)"
          unfolding powr_powr q2_def using conjugate_exponent_real(4)[OF \<open>p2 > 1\<close>] by auto
        also have "... = (Norm (\<LL> p2 M) f) powr p2"
          apply (subst Lp_Norm(2), auto simp add: \<open>p2 > 0\<close>)
          by (rule nn_integral_eq_integral, auto simp add: Lp_D(2)[OF \<open>p2 > 0\<close> \<open>f \<in> space\<^sub>N (\<LL> p2 M)\<close>])
        finally have *: "(\<integral>\<^sup>+x. \<bar>h x\<bar> powr q2 \<partial>M) = (Norm (\<LL> p2 M) f) powr p2" by simp
        have "integrable M (\<lambda>x. \<bar>h x\<bar> powr q2)"
          apply (rule integrableI_bounded, auto) using * by auto
        then have "(\<integral>x. \<bar>h x\<bar> powr q2 \<partial>M) = (\<integral>\<^sup>+x. \<bar>h x\<bar> powr q2 \<partial>M)"
          by (rule nn_integral_eq_integral[symmetric], auto)
        then have **: "(\<integral>x. \<bar>h x\<bar> powr q2 \<partial>M) = (Norm (\<LL> p2 M) f) powr p2" using * by auto

        define g where "g = (\<lambda>x. h x / (Norm (\<LL> p2 M) f) powr (p2 / q2))"
        have [measurable]: "g \<in> borel_measurable M" unfolding g_def by auto
        have intg: "integrable M (\<lambda>x. \<bar>g x\<bar> powr q2)"
          unfolding g_def using \<open>Norm (\<LL> p2 M) f > 0\<close> \<open>q2 > 1\<close> apply (simp add: abs_mult powr_divide powr_powr)
          using \<open>integrable M (\<lambda>x. \<bar>h x\<bar> powr q2)\<close> integrable_divide_zero by blast
        have "g \<in> space\<^sub>N (\<LL> q2 M)" by (rule Lp_I(1)[OF \<open>q2 > 0\<close> _ intg], auto)
        have "(\<integral>x. \<bar>g x\<bar> powr q2 \<partial>M) = 1"
          unfolding g_def using \<open>Norm (\<LL> p2 M) f > 0\<close> \<open>q2 > 1\<close> by (simp add: abs_mult powr_divide powr_powr **)
        then have "Norm (\<LL> q2 M) g = 1"
          apply (subst Lp_D[OF \<open>q2 > 0\<close>]) using \<open>g \<in> space\<^sub>N (\<LL> q2 M)\<close> by auto

        have "(\<integral>x. f x * g x \<partial>M) = (\<integral>x. f x * sgn(f x) * \<bar>f x\<bar> powr (p2 - 1) / (Norm (\<LL> p2 M) f) powr (p2 / q2) \<partial>M)"
          unfolding g_def h_def by (simp add: mult.assoc)
        also have "... = (\<integral>x. \<bar>f x\<bar> * \<bar>f x\<bar> powr (p2-1) \<partial>M) / (Norm (\<LL> p2 M) f) powr (p2 / q2)"
          by (auto simp add: abs_sgn)
        also have "... = (\<integral>x. \<bar>f x\<bar> powr p2 \<partial>M) / (Norm (\<LL> p2 M) f) powr (p2 / q2)"
          by (subst powr_mult_base, auto)
        also have "... = (Norm (\<LL> p2 M) f) powr p2 / (Norm (\<LL> p2 M) f) powr (p2 / q2)"
          by (subst Lp_Norm(2)[OF \<open>p2 > 0\<close>], auto)
        also have "... = (Norm (\<LL> p2 M) f) powr (p2 - p2/q2)"
          by (simp add: powr_diff [symmetric] )
        also have "... = Norm (\<LL> p2 M) f"
          unfolding q2_def using conjugate_exponent_real(5)[OF \<open>p2 > 1\<close>] by auto
        finally have "Norm (\<LL> p M) f = (\<integral>x. f x * g x \<partial>M)"
          unfolding \<open>p = ennreal p2\<close> by simp
        also have "... \<le> (SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. (\<integral>x. f x * g x \<partial>M))"
          unfolding \<open>q = ennreal q2\<close> apply (rule cSUP_upper, auto)
          using \<open>g \<in> space\<^sub>N (\<LL> q2 M)\<close> \<open>Norm (\<LL> q2 M) g = 1\<close> apply auto
          using B \<open>q = ennreal q2\<close> by fastforce
        finally show ?thesis by simp
      qed
    qed
  qed
qed

text \<open>The previous theorem admits a version in which one does not assume a priori that the
function under consideration belongs to $L^p$. This gives an efficient criterion to check
if a function is indeed in $L^p$. In this case, it is always necessary to assume that the
measure is sigma-finite.

Note that, in the statement, the Bochner integral $\int fg$ vanishes by definition if
$fg$ is not integrable. Hence, the statement really says that the eNorm can be estimated
using functions $g$ for which $fg$ is integrable. It is precisely the construction of such
functions $g$ that requires the space to be sigma-finite.\<close>

theorem Lp_Lq_duality':
  fixes p q::ennreal
  assumes "1/p + 1/q = 1"
          "sigma_finite_measure M"
      and [measurable]: "f \<in> borel_measurable M"
  shows "eNorm (\<LL> p M) f = (SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. ennreal(\<integral>x. f x * g x \<partial>M))"
proof (cases "eNorm (\<LL> p M) f \<noteq> \<infinity>")
  case True
  then have "f \<in> space\<^sub>N (\<LL> p M)" unfolding space\<^sub>N_def by (simp add: top.not_eq_extremum)
  show ?thesis
    unfolding eNorm_Norm[OF \<open>f \<in> space\<^sub>N (\<LL> p M)\<close>] Lp_Lq_duality[OF \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> \<open>1/p + 1/q = 1\<close> \<open>sigma_finite_measure M\<close>]
    apply (rule SUP_real_ennreal[symmetric], auto, rule exI[of _ 0], auto)
    by (rule Lp_Lq_duality[OF \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> \<open>1/p + 1/q = 1\<close> \<open>sigma_finite_measure M\<close>])
next
  case False
  have B: "\<exists>g \<in> {g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. (\<integral>x. f x * g x \<partial>M) \<ge> C" if "C < \<infinity>" for C::ennreal
  proof -
    obtain Cr where "C = ennreal Cr" "Cr \<ge> 0" using \<open>C < \<infinity>\<close> ennreal_cases less_irrefl by auto
    obtain A where A: "\<And>n::nat. A n \<in> sets M" "incseq A" "(\<Union>n. A n) = space M"
            "\<And>n. emeasure M (A n) \<noteq> \<infinity>"
      using sigma_finite_measure.sigma_finite_incseq[OF \<open>sigma_finite_measure M\<close>] by (metis range_subsetD)
    define Y where "Y = (\<lambda>n. {x \<in> A n. \<bar>f x\<bar> \<le> n})"
    have [measurable]: "\<And>n. Y n \<in> sets M" unfolding Y_def using \<open>\<And>n::nat. A n \<in> sets M\<close> by auto
    have "incseq Y"
      apply (rule incseq_SucI) unfolding Y_def using incseq_SucD[OF \<open>incseq A\<close>] by auto
    have *: "\<exists>N. \<forall>n \<ge> N. f x * indicator (Y n) x = f x" if "x \<in> space M" for x
    proof -
      obtain n0 where n0: "x \<in> A n0" using \<open>x \<in> space M\<close> \<open>(\<Union>n. A n) = space M\<close> by auto
      obtain n1::nat where n1: "\<bar>f x\<bar> \<le> n1" using real_arch_simple by blast
      have "x \<in> Y (max n0 n1)"
        unfolding Y_def using n1 apply auto
        using n0 \<open>incseq A\<close> incseq_def max.cobounded1 by blast
      then have *: "x \<in> Y n" if "n \<ge> max n0 n1" for n
        using \<open>incseq Y\<close> that incseq_def by blast
      show ?thesis by (rule exI[of _ "max n0 n1"], auto simp add: *)
    qed
    have *: "(\<lambda>n. f x * indicator (Y n) x) \<longlonglongrightarrow> f x" if "x \<in> space M" for x
      using *[OF that] unfolding eventually_sequentially[symmetric] by (simp add: Lim_eventually)
    have "liminf (\<lambda>n. eNorm (\<LL> p M) (\<lambda>x. f x * indicator (Y n) x)) \<ge> eNorm (\<LL> p M) f"
      apply (rule Lp_AE_limit) using * by auto
    then have "liminf (\<lambda>n. eNorm (\<LL> p M) (\<lambda>x. f x * indicator (Y n) x)) > Cr" using False neq_top_trans by force
    then have "limsup (\<lambda>n. eNorm (\<LL> p M) (\<lambda>x. f x * indicator (Y n) x)) > Cr"
      using Liminf_le_Limsup less_le_trans trivial_limit_sequentially by blast
    then obtain n where n: "eNorm (\<LL> p M) (\<lambda>x. f x * indicator (Y n) x) > Cr"
      using Limsup_obtain by blast

    have "(\<lambda>x. f x * indicator (Y n) x) \<in> space\<^sub>N (\<LL> p M)"
      apply (rule Lp_bounded_bounded_support[of _ _ n], auto)
      unfolding Y_def indicator_def apply auto
      by (metis (mono_tags, lifting) A(1) A(4) emeasure_mono infinity_ennreal_def mem_Collect_eq neq_top_trans subsetI)
    have "Norm (\<LL> p M) (\<lambda>x. f x * indicator (Y n) x) > Cr"
      using n unfolding eNorm_Norm[OF \<open>(\<lambda>x. f x * indicator (Y n) x) \<in> space\<^sub>N (\<LL> p M)\<close>]
      by (meson ennreal_leI not_le)
    then have "(SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. (\<integral>x. f x * indicator (Y n) x * g x \<partial>M)) > Cr"
      using Lp_Lq_duality(2)[OF \<open>(\<lambda>x. f x * indicator (Y n) x) \<in> space\<^sub>N (\<LL> p M)\<close> \<open>1/p + 1/q = 1\<close> \<open>sigma_finite_measure M\<close>]
      by auto
    then have "\<exists>g \<in> {g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. (\<integral>x. f x * indicator (Y n) x * g x \<partial>M) > Cr"
      apply (subst less_cSUP_iff[symmetric])
      using Lp_Lq_duality(1)[OF \<open>(\<lambda>x. f x * indicator (Y n) x) \<in> space\<^sub>N (\<LL> p M)\<close> \<open>1/p + 1/q = 1\<close> \<open>sigma_finite_measure M\<close>] apply auto
      by (rule exI[of _ 0], auto)
    then obtain g where g: "g \<in> space\<^sub>N (\<LL> q M)" "Norm (\<LL> q M) g \<le> 1" "(\<integral>x. f x * indicator (Y n) x * g x \<partial>M) > Cr"
      by auto
    then have [measurable]: "g \<in> borel_measurable M" using Lp_measurable by auto
    define h where "h = (\<lambda>x. indicator (Y n) x * g x)"
    have "Norm (\<LL> q M) h \<le> Norm (\<LL> q M) g"
      apply (rule Lp_domination[of _ _ g]) unfolding h_def indicator_def using \<open>g \<in> space\<^sub>N (\<LL> q M)\<close> by auto
    then have a: "Norm (\<LL> q M) h \<le> 1" using \<open>Norm (\<LL> q M) g \<le> 1\<close> by auto
    have b: "h \<in> space\<^sub>N (\<LL> q M)"
      apply (rule Lp_domination[of _ _ g]) unfolding h_def indicator_def using \<open>g \<in> space\<^sub>N (\<LL> q M)\<close> by auto
    have "(\<integral>x. f x * h x \<partial>M) > Cr" unfolding h_def using g(3) by (auto simp add: mult.assoc)
    then have "(\<integral>x. f x * h x \<partial>M) > C"
      unfolding \<open>C = ennreal Cr\<close> using \<open>Cr \<ge> 0\<close> by (simp add: ennreal_less_iff)
    then show ?thesis using a b by auto
  qed
  have "(SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. ennreal(\<integral>x. f x * g x \<partial>M)) \<ge> \<infinity>"
    apply (rule dense_le) using B by (meson SUP_upper2)
  then show ?thesis using False neq_top_trans by force
qed


subsection \<open>Conditional expectations and $L^p$\<close>

text \<open>The $L^p$ space with respect to a subalgebra is included in the whole $L^p$ space.\<close>

lemma Lp_subalgebra:
  assumes "subalgebra M F"
  shows "\<And>f. eNorm (\<LL> p M) f \<le> eNorm (\<LL> p (restr_to_subalg M F)) f"
        "(\<LL> p (restr_to_subalg M F)) \<subseteq>\<^sub>N \<LL> p M"
        "space\<^sub>N ((\<LL> p (restr_to_subalg M F))) \<subseteq> space\<^sub>N (\<LL> p M)"
        "\<And>f. f \<in> space\<^sub>N ((\<LL> p (restr_to_subalg M F))) \<Longrightarrow> Norm (\<LL> p M) f = Norm (\<LL> p (restr_to_subalg M F)) f"
proof -
  have *: "f \<in> space\<^sub>N (\<LL> p M) \<and> Norm (\<LL> p M) f = Norm (\<LL> p (restr_to_subalg M F)) f"
       if "f \<in> space\<^sub>N (\<LL> p (restr_to_subalg M F))" for f
  proof -
    have [measurable]: "f \<in> borel_measurable (restr_to_subalg M F)" using that Lp_measurable by auto
    then have [measurable]: "f \<in> borel_measurable M"
      using assms measurable_from_subalg measurable_in_subalg' by blast
    show ?thesis
    proof (cases rule: Lp_cases[of p])
      case zero
      then show ?thesis using that unfolding \<open>p = 0\<close> L_zero_space Norm_def L_zero by auto
    next
      case PInf
      have [measurable]: "f \<in> borel_measurable (restr_to_subalg M F)" using that Lp_measurable by auto
      then have [measurable]: "f \<in> borel_measurable F" using assms measurable_in_subalg' by blast
      then have [measurable]: "f \<in> borel_measurable M" using assms measurable_from_subalg by blast
      have "AE x in (restr_to_subalg M F). \<bar>f x\<bar> \<le> Norm (\<LL> \<infinity> (restr_to_subalg M F)) f"
        using L_infinity_AE_bound that unfolding \<open>p = \<infinity>\<close> by auto
      then have a: "AE x in M. \<bar>f x\<bar> \<le> Norm (\<LL> \<infinity> (restr_to_subalg M F)) f"
        using assms AE_restr_to_subalg by blast
      have *: "f \<in> space\<^sub>N (\<LL> \<infinity> M)" "Norm (\<LL> \<infinity> M) f \<le> Norm (\<LL> \<infinity> (restr_to_subalg M F)) f"
        using L_infinity_I[OF \<open>f \<in> borel_measurable M\<close> a] by auto
      then have b: "AE x in M. \<bar>f x\<bar> \<le> Norm (\<LL> \<infinity> M) f"
        using L_infinity_AE_bound by auto
      have c: "AE x in (restr_to_subalg M F). \<bar>f x\<bar> \<le> Norm (\<LL> \<infinity> M) f"
        apply (rule AE_restr_to_subalg2[OF assms]) using b by auto
      have "Norm (\<LL> \<infinity> (restr_to_subalg M F)) f \<le> Norm (\<LL> \<infinity> M) f"
        using L_infinity_I[OF \<open>f \<in> borel_measurable (restr_to_subalg M F)\<close> c] by auto
      then show ?thesis using * unfolding \<open>p = \<infinity>\<close> by auto
    next
      case (real_pos p2)
      then have a [measurable]: "f \<in> space\<^sub>N (\<LL> p2 (restr_to_subalg M F))"
        using that unfolding \<open>p = ennreal p2\<close> by auto
      then have b [measurable]: "f \<in> space\<^sub>N (\<LL> p2 M)"
        unfolding Lp_space[OF \<open>p2 > 0\<close>] using integrable_from_subalg[OF assms] by auto
      show ?thesis
        unfolding \<open>p = ennreal p2\<close> Lp_D[OF \<open>p2 > 0\<close> a] Lp_D[OF \<open>p2 > 0\<close> b]
        using integral_subalgebra2[OF assms, symmetric, of f] apply (auto simp add: b)
        by (metis (mono_tags, lifting) \<open>integrable (restr_to_subalg M F) (\<lambda>x. \<bar>f x\<bar> powr p2)\<close> assms integrableD(1) integral_subalgebra2 measurable_in_subalg')
    qed
  qed
  show "space\<^sub>N ((\<LL> p (restr_to_subalg M F))) \<subseteq> space\<^sub>N (\<LL> p M)" using * by auto
  show "Norm (\<LL> p M) f = Norm (\<LL> p (restr_to_subalg M F)) f" if "f \<in> space\<^sub>N ((\<LL> p (restr_to_subalg M F)))" for f
    using * that by auto
  show "eNorm (\<LL> p M) f \<le> eNorm (\<LL> p (restr_to_subalg M F)) f" for f
    by (metis "*" eNorm_Norm eq_iff infinity_ennreal_def less_imp_le spaceN_iff top.not_eq_extremum)
  then show "(\<LL> p (restr_to_subalg M F)) \<subseteq>\<^sub>N \<LL> p M"
    by (metis ennreal_1 mult.left_neutral quasinorm_subsetI)
qed

text \<open>For $p \geq 1$, the conditional expectation of an $L^p$ function still belongs to $L^p$,
with an $L^p$ norm which is bounded by the norm of the original function. This is wrong for
$p < 1$. One can prove this separating the cases and using the conditional version of Jensen's
inequality, but it is much more efficient to do it with duality arguments, as follows.\<close>

proposition Lp_real_cond_exp:
  assumes [simp]: "subalgebra M F"
      and "p \<ge> (1::ennreal)"
          "sigma_finite_measure (restr_to_subalg M F)"
          "f \<in> space\<^sub>N (\<LL> p M)"
  shows "real_cond_exp M F f \<in> space\<^sub>N (\<LL> p (restr_to_subalg M F))"
        "Norm (\<LL> p (restr_to_subalg M F)) (real_cond_exp M F f) \<le> Norm (\<LL> p M) f"
proof -
  have [measurable]: "f \<in> borel_measurable M" using Lp_measurable assms by auto
  define q where "q = conjugate_exponent p"
  have "1/p + 1/q = 1" unfolding q_def using conjugate_exponent_ennreal[OF \<open>p \<ge> 1\<close>] by simp
  have "eNorm (\<LL> p (restr_to_subalg M F)) (real_cond_exp M F f)
    = (SUP g\<in>{g \<in> space\<^sub>N (\<LL> q (restr_to_subalg M F)). Norm (\<LL> q (restr_to_subalg M F)) g \<le> 1}. ennreal(\<integral>x. (real_cond_exp M F f) x * g x \<partial>(restr_to_subalg M F)))"
    by (rule Lp_Lq_duality'[OF \<open>1/p + 1/q = 1\<close> \<open>sigma_finite_measure (restr_to_subalg M F)\<close>], simp)
  also have "... \<le> (SUP g\<in>{g \<in> space\<^sub>N (\<LL> q M). Norm (\<LL> q M) g \<le> 1}. ennreal(\<integral>x. f x * g x \<partial>M))"
  proof (rule SUP_mono, auto)
    fix g assume H: "g \<in> space\<^sub>N (\<LL> q (restr_to_subalg M F))"
                    "Norm (\<LL> q (restr_to_subalg M F)) g \<le> 1"
    then have H2: "g \<in> space\<^sub>N (\<LL> q M)" "Norm (\<LL> q M) g \<le> 1"
      using Lp_subalgebra[OF \<open>subalgebra M F\<close>] by (auto simp add: subset_iff)
    have [measurable]: "g \<in> borel_measurable M" "g \<in> borel_measurable F"
      using Lp_measurable[OF H(1)] Lp_measurable[OF H2(1)] by auto
    have int: "integrable M (\<lambda>x. f x * g x)"
      using Lp_Lq_duality_bound(1)[OF \<open>1/p + 1/q = 1\<close> \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> H2(1)].
    have "(\<integral>x. (real_cond_exp M F f) x * g x \<partial>(restr_to_subalg M F)) = (\<integral>x. g x * (real_cond_exp M F f) x \<partial>M)"
      by (subst mult.commute, rule integral_subalgebra2[OF \<open>subalgebra M F\<close>], auto)
    also have "... = (\<integral>x. g x * f x \<partial>M)"
      apply (rule sigma_finite_subalgebra.real_cond_exp_intg, auto simp add: int mult.commute)
      unfolding sigma_finite_subalgebra_def using assms by auto
    finally have "ennreal (\<integral>x. (real_cond_exp M F f) x * g x \<partial>(restr_to_subalg M F)) \<le> ennreal (\<integral>x. f x * g x \<partial>M)"
      by (auto intro!: ennreal_leI simp add: mult.commute)
    then show "\<exists>m. m \<in> space\<^sub>N (\<LL> q M) \<and> Norm (\<LL> q M) m \<le> 1
        \<and> ennreal (LINT x|restr_to_subalg M F. real_cond_exp M F f x * g x) \<le> ennreal (LINT x|M. f x * m x)"
      using H2 by blast
  qed
  also have "... = eNorm (\<LL> p M) f"
    apply (rule Lp_Lq_duality'[OF \<open>1/p + 1/q = 1\<close>, symmetric], auto intro!: sigma_finite_subalgebra_is_sigma_finite[of _ F])
    unfolding sigma_finite_subalgebra_def using assms by auto
  finally have *: "eNorm (\<LL> p (restr_to_subalg M F)) (real_cond_exp M F f) \<le> eNorm (\<LL> p M) f"
    by simp
  then show a: "real_cond_exp M F f \<in> space\<^sub>N (\<LL> p (restr_to_subalg M F))"
    apply (subst spaceN_iff) using \<open>f \<in> space\<^sub>N (\<LL> p M)\<close> by (simp add: space\<^sub>N_def)
  show "Norm (\<LL> p (restr_to_subalg M F)) (real_cond_exp M F f) \<le> Norm (\<LL> p M) f"
    using * unfolding eNorm_Norm[OF \<open>f \<in> space\<^sub>N (\<LL> p M)\<close>] eNorm_Norm[OF a] by simp
qed

lemma Lp_real_cond_exp_eNorm:
  assumes [simp]: "subalgebra M F"
      and "p \<ge> (1::ennreal)"
          "sigma_finite_measure (restr_to_subalg M F)"
  shows "eNorm (\<LL> p (restr_to_subalg M F)) (real_cond_exp M F f) \<le> eNorm (\<LL> p M) f"
proof (cases "eNorm (\<LL> p M) f = \<infinity>")
  case False
  then have *: "f \<in> space\<^sub>N (\<LL> p M)"
    unfolding spaceN_iff by (simp add: top.not_eq_extremum)
  show ?thesis
    using Lp_real_cond_exp[OF assms \<open>f \<in> space\<^sub>N (\<LL> p M)\<close>] by (subst eNorm_Norm, auto simp: \<open>f \<in> space\<^sub>N (\<LL> p M)\<close>)+
qed (simp)

end
