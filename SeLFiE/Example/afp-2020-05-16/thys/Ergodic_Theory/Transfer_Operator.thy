(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>Transfer Operator\<close>

theory Transfer_Operator
  imports Recurrence
begin

context qmpt begin

text \<open>The map $T$ acts on measures by push-forward. In particular, if $f d\mu$ is absolutely continuous
with respect to the reference measure $\mu$, then its push-forward $T_*(f d\mu)$ is absolutely
continuous with respect to $\mu$, and can therefore be written as $g d\mu$ for some function $g$.
The map $f \mapsto g$, representing the action of $T$ on the level of densities, is called the
transfer operator associated to $T$ and often denoted by $\hat T$.

We first define it on nonnegative functions, using Radon-Nikodym derivatives. Then, we extend it
to general real-valued functions by separating it into positive and negative parts.

The theory presents many similarities with the theory of conditional expectations. Indeed, it is
possible to make a theory encompassing the two. When the map is measure preserving,
there is also a direct relationship: $(\hat T f) \circ T$ is the conditional expectation of $f$
with respect to $T^{-1}B$ where $B$ is the sigma-algebra. Instead of building a general theory,
we copy the proofs for conditional expectations and adapt them where needed.\<close>

subsection \<open>The transfer operator on nonnegative functions\<close>

definition nn_transfer_operator :: "('a \<Rightarrow> ennreal) \<Rightarrow> ('a \<Rightarrow> ennreal)"
where
  "nn_transfer_operator f = (if f \<in> borel_measurable M then RN_deriv M (distr (density M f) M T)
                              else (\<lambda>_. 0))"

lemma borel_measurable_nn_transfer_operator [measurable]:
  "nn_transfer_operator f \<in> borel_measurable M"
unfolding nn_transfer_operator_def by auto

lemma borel_measurable_nn_transfer_operator_iterates [measurable]:
  assumes [measurable]: "f \<in> borel_measurable M"
  shows "(nn_transfer_operator^^n) f \<in> borel_measurable M"
by (cases n, auto)

text \<open>The next lemma is arguably the most fundamental property of the transfer operator: it is the
adjoint of the composition by $T$. If one defined it as an abstract adjoint, it would be defined
on the dual of $L^\infty$, which is a large unwieldy space. The point is that it can be defined
on genuine functions, using the push-forward point of view above. However, once we have this
property, we can forget completely about the definition, since this property characterizes
the transfer operator, as the second lemma below shows.
From this point on, we will only work with it, and forget completely about
the definition using Radon-Nikodym derivatives.
\<close>

lemma nn_transfer_operator_intg:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ x. f x * nn_transfer_operator g x \<partial>M) = (\<integral>\<^sup>+ x. f (T x) * g x \<partial>M)"
proof -
  have *: "density M (RN_deriv M (distr (density M g) M T)) = distr (density M g) M T"
    by (rule density_RN_deriv) (auto intro!: quasi_measure_preserving_absolutely_continuous simp add: Tqm)
  have "(\<integral>\<^sup>+ x. f x * nn_transfer_operator g x \<partial>M) = (\<integral>\<^sup>+ x. f x \<partial>(density M (RN_deriv M (distr (density M g) M T))))"
    unfolding nn_transfer_operator_def by (simp add: nn_integral_densityR)
  also have "... = (\<integral>\<^sup>+ x. f x \<partial>(distr (density M g) M T))"
    unfolding * by simp
  also have "... = (\<integral>\<^sup>+ x. f (T x) \<partial>(density M g))"
    by (rule nn_integral_distr, auto)
  also have "... = (\<integral>\<^sup>+ x. f (T x) * g x \<partial>M)"
    by (simp add: nn_integral_densityR)
  finally show ?thesis by auto
qed

lemma nn_transfer_operator_intTn_g:
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ x. f x * (nn_transfer_operator^^n) g x \<partial>M) = (\<integral>\<^sup>+ x. f ((T^^n) x) * g x \<partial>M)"
proof -
  have "\<And>f g. f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<integral>\<^sup>+ x. f x * (nn_transfer_operator^^n) g x \<partial>M) = (\<integral>\<^sup>+ x. f ((T^^n) x) * g x \<partial>M)" for n
  proof (induction n)
    case (Suc n)
    have [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M" by fact+
    have "(\<integral>\<^sup>+ x. f x * (nn_transfer_operator ^^ Suc n) g x \<partial>M) = (\<integral>\<^sup>+ x. f x * (nn_transfer_operator ((nn_transfer_operator^^n) g)) x \<partial>M)"
      apply (rule nn_integral_cong) using funpow.simps(2) unfolding comp_def by auto
    also have "... = (\<integral>\<^sup>+ x. f (T x) * (nn_transfer_operator^^n) g x \<partial>M)"
      by (rule nn_transfer_operator_intg, auto)
    also have "... = (\<integral>\<^sup>+ x. (\<lambda>x. f (T x)) ((T^^n) x) * g x \<partial>M)"
      by (rule Suc.IH, auto)
    also have "... = (\<integral>\<^sup>+ x. f ((T^^(Suc n)) x) * g x \<partial>M)"
      apply (rule nn_integral_cong) using funpow.simps(2) unfolding comp_def by auto
    finally show ?case by auto
  qed (simp)
  then show ?thesis using assms by auto
qed

lemma nn_transfer_operator_intg_Tn:
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ x. (nn_transfer_operator^^n) g x * f x \<partial>M) = (\<integral>\<^sup>+ x. g x * f ((T^^n) x) \<partial>M)"
using nn_transfer_operator_intTn_g[OF assms, of n] by (simp add: algebra_simps)

lemma nn_transfer_operator_charact:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>\<^sup>+ x. indicator A x * g x \<partial>M) = (\<integral>\<^sup>+ x. indicator A (T x) * f x \<partial>M)" and
          [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "AE x in M. nn_transfer_operator f x = g x"
proof -
  have *:"set_nn_integral M A g = set_nn_integral M A (nn_transfer_operator f)" if [measurable]: "A \<in> sets M" for A
  proof -
    have "set_nn_integral M A g = (\<integral>\<^sup>+ x. indicator A x * g x \<partial>M)"
      using mult.commute by metis
    also have "... = (\<integral>\<^sup>+ x. indicator A (T x) * f x \<partial>M)"
      using assms(1) by auto
    also have "... = (\<integral>\<^sup>+ x. indicator A x * nn_transfer_operator f x \<partial>M)"
      by (rule nn_transfer_operator_intg[symmetric], auto)
    finally show ?thesis
      using mult.commute by (metis (no_types, lifting) nn_integral_cong)
  qed
  show ?thesis
    by (rule sigma_finite_measure.density_unique2, auto simp add: sigma_finite_measure_axioms *)
qed

text \<open>When $T$ is measure-preserving, $\hat T(f \circ T) = f$.\<close>

lemma (in mpt) nn_transfer_operator_foT:
  assumes [measurable]: "f \<in> borel_measurable M"
  shows "AE x in M. nn_transfer_operator (f o T) x = f x"
proof -
  have *: "(\<integral>\<^sup>+ x. indicator A x * f x \<partial>M) = (\<integral>\<^sup>+ x. indicator A (T x) * f (T x) \<partial>M)" if [measurable]: "A \<in> sets M" for A
    by (subst T_nn_integral_preserving[symmetric]) auto
  show ?thesis
    by (rule nn_transfer_operator_charact) (auto simp add: assms *)
qed

text \<open>In general, one only has $\hat T(f\circ T \cdot g) = f \cdot \hat T g$.\<close>
lemma nn_transfer_operator_foT_g:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "AE x in M. nn_transfer_operator (\<lambda>x. f (T x) * g x) x = f x * nn_transfer_operator g x"
proof -
  have *: "(\<integral>\<^sup>+ x. indicator A x * (f x * nn_transfer_operator g x) \<partial>M) = (\<integral>\<^sup>+ x. indicator A (T x) * (f (T x) * g x) \<partial>M)"
    if [measurable]: "A \<in> sets M" for A
    by (simp add: mult.assoc[symmetric] nn_transfer_operator_intg)
  show ?thesis
    by (rule nn_transfer_operator_charact) (auto simp add: assms *)
qed

lemma nn_transfer_operator_cmult:
  assumes [measurable]: "g \<in> borel_measurable M"
  shows "AE x in M. nn_transfer_operator (\<lambda>x. c * g x) x = c * nn_transfer_operator g x"
apply (rule nn_transfer_operator_foT_g) using assms by auto

lemma nn_transfer_operator_zero:
  "AE x in M. nn_transfer_operator (\<lambda>x. 0) x = 0"
using nn_transfer_operator_cmult[of "\<lambda>x. 0" 0] by auto

lemma nn_transfer_operator_sum:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "AE x in M. nn_transfer_operator (\<lambda>x. f x + g x) x = nn_transfer_operator f x + nn_transfer_operator g x"
proof (rule nn_transfer_operator_charact)
  fix A assume [measurable]: "A \<in> sets M"
  have "(\<integral>\<^sup>+ x. indicator A x * (nn_transfer_operator f x + nn_transfer_operator g x) \<partial>M) =
        (\<integral>\<^sup>+ x. indicator A x * nn_transfer_operator f x + indicator A x * nn_transfer_operator g x \<partial>M)"
    by (auto simp add: algebra_simps)
  also have "... = (\<integral>\<^sup>+x. indicator A x * nn_transfer_operator f x \<partial>M) + (\<integral>\<^sup>+x. indicator A x * nn_transfer_operator g x \<partial>M)"
    by (rule nn_integral_add, auto)
  also have "... = (\<integral>\<^sup>+x. indicator A (T x) * f x \<partial>M) + (\<integral>\<^sup>+x. indicator A (T x) * g x \<partial>M)"
    by (simp add: nn_transfer_operator_intg)
  also have "... = (\<integral>\<^sup>+x. indicator A (T x) * f x + indicator A (T x) * g x \<partial>M)"
    by (rule nn_integral_add[symmetric], auto)
  also have "... = (\<integral>\<^sup>+x. indicator A (T x) * (f x + g x) \<partial>M)"
    by (auto simp add: algebra_simps)
  finally show "(\<integral>\<^sup>+ x. indicator A x * (nn_transfer_operator f x + nn_transfer_operator g x) \<partial>M) = (\<integral>\<^sup>+x. indicator A (T x) * (f x + g x) \<partial>M)"
    by simp
qed (auto simp add: assms)

lemma nn_transfer_operator_cong:
  assumes "AE x in M. f x = g x"
      and [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "AE x in M. nn_transfer_operator f x = nn_transfer_operator g x"
apply (rule nn_transfer_operator_charact)
apply (auto simp add: nn_transfer_operator_intg assms intro!: nn_integral_cong_AE)
using assms by auto

lemma nn_transfer_operator_mono:
  assumes "AE x in M. f x \<le> g x"
      and [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "AE x in M. nn_transfer_operator f x \<le> nn_transfer_operator g x"
proof -
  define h where "h = (\<lambda>x. g x - f x)"
  have [measurable]: "h \<in> borel_measurable M" unfolding h_def by simp
  have *: "AE x in M. g x = f x + h x" unfolding h_def using assms(1) by (auto simp: ennreal_ineq_diff_add)
  have "AE x in M. nn_transfer_operator g x = nn_transfer_operator (\<lambda>x. f x + h x) x"
    by (rule nn_transfer_operator_cong) (auto simp add: * assms)
  moreover have "AE x in M. nn_transfer_operator (\<lambda>x. f x + h x) x = nn_transfer_operator f x + nn_transfer_operator h x"
    by (rule nn_transfer_operator_sum) (auto simp add: assms)
  ultimately have "AE x in M. nn_transfer_operator g x = nn_transfer_operator f x + nn_transfer_operator h x" by auto
  then show ?thesis by force
qed

subsection \<open>The transfer operator on real functions\<close>

text \<open>Once the transfer operator of positive functions is defined, the definition for real-valued
functions follows readily, by taking the difference of positive and negative parts.
\<close>

definition real_transfer_operator :: "('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)" where
  "real_transfer_operator f =
    (\<lambda>x. enn2real(nn_transfer_operator (\<lambda>x. ennreal (f x)) x) - enn2real(nn_transfer_operator (\<lambda>x. ennreal (-f x)) x))"

lemma borel_measurable_transfer_operator [measurable]:
  "real_transfer_operator f \<in> borel_measurable M"
unfolding real_transfer_operator_def by auto

lemma borel_measurable_transfer_operator_iterates [measurable]:
  assumes [measurable]: "f \<in> borel_measurable M"
  shows "(real_transfer_operator^^n) f \<in> borel_measurable M"
by (cases n, auto)

lemma real_transfer_operator_abs:
  assumes [measurable]: "f \<in> borel_measurable M"
  shows "AE x in M. abs (real_transfer_operator f x) \<le> nn_transfer_operator (\<lambda>x. ennreal (abs(f x))) x"
proof -
  define fp where "fp = (\<lambda>x. ennreal (f x))"
  define fm where "fm = (\<lambda>x. ennreal (- f x))"
  have [measurable]: "fp \<in> borel_measurable M" "fm \<in> borel_measurable M" unfolding fp_def fm_def by auto
  have eq: "\<And>x. ennreal \<bar>f x\<bar> = fp x + fm x" unfolding fp_def fm_def by (simp add: abs_real_def ennreal_neg)

  {
    fix x assume H: "nn_transfer_operator (\<lambda>x. fp x + fm x) x = nn_transfer_operator fp x + nn_transfer_operator fm x"
    have "\<bar>real_transfer_operator f x\<bar> \<le> \<bar>enn2real(nn_transfer_operator fp x)\<bar> + \<bar>enn2real(nn_transfer_operator fm x)\<bar>"
      unfolding real_transfer_operator_def fp_def fm_def by (auto intro: abs_triangle_ineq4 simp del: enn2real_nonneg)
    from ennreal_leI[OF this]
    have "abs(real_transfer_operator f x) \<le> nn_transfer_operator fp x + nn_transfer_operator fm x"
      by simp (metis add.commute ennreal_enn2real le_iff_add not_le top_unique)
    also have "... = nn_transfer_operator (\<lambda>x. fp x + fm x) x" using H by simp
    finally have "abs(real_transfer_operator f x) \<le> nn_transfer_operator (\<lambda>x. fp x + fm x) x" by simp
  }
  moreover have "AE x in M. nn_transfer_operator (\<lambda>x. fp x + fm x) x = nn_transfer_operator fp x + nn_transfer_operator fm x"
    by (rule nn_transfer_operator_sum) (auto simp add: fp_def fm_def)
  ultimately have "AE x in M. abs(real_transfer_operator f x) \<le> nn_transfer_operator (\<lambda>x. fp x + fm x) x"
    by auto
  then show ?thesis using eq by simp
qed

text \<open>The next lemma shows that the transfer operator as we have defined it satisfies the basic
duality relation $\int \hat T f \cdot g = \int f \cdot g \circ T$. It follows from the same relation
for nonnegative functions, and splitting into positive and negative parts.

Moreover, this relation characterizes the transfer operator. Hence, once this lemma is proved, we
will never come back to the original definition of the transfer operator.\<close>

lemma real_transfer_operator_intg_fpos:
  assumes "integrable M (\<lambda>x. f (T x) * g x)" and f_pos[simp]: "\<And>x. f x \<ge> 0" and
          [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "integrable M (\<lambda>x. f x * real_transfer_operator g x)"
        "(\<integral> x. f x * real_transfer_operator g x \<partial>M) = (\<integral> x. f (T x) * g x \<partial>M)"
proof -
  define gp where "gp = (\<lambda>x. ennreal (g x))"
  define gm where "gm = (\<lambda>x. ennreal (- g x))"
  have [measurable]: "gp \<in> borel_measurable M" "gm \<in> borel_measurable M" unfolding gp_def gm_def by auto
  define h where "h = (\<lambda>x. ennreal(abs(g x)))"
  have hgpgm: "\<And>x. h x = gp x + gm x" unfolding gp_def gm_def h_def by (simp add: abs_real_def ennreal_neg)
  have [measurable]: "h \<in> borel_measurable M" unfolding h_def by simp
  have pos[simp]: "\<And>x. h x \<ge> 0" "\<And>x. gp x \<ge> 0" "\<And>x. gm x \<ge> 0" unfolding h_def gp_def gm_def by simp_all
  have gp_real: "\<And>x. enn2real(gp x) = max (g x) 0"
    unfolding gp_def by (simp add: max_def ennreal_neg)
  have gm_real: "\<And>x. enn2real(gm x) = max (-g x) 0"
    unfolding gm_def by (simp add: max_def ennreal_neg)

  have "(\<integral>\<^sup>+ x. norm(f (T x) * max (g x) 0) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f (T x) * g x) \<partial>M)"
    by (simp add: nn_integral_mono)
  also have "... < \<infinity>" using assms(1) by (simp add: integrable_iff_bounded)
  finally have "(\<integral>\<^sup>+ x. norm(f (T x) * max (g x) 0) \<partial>M) < \<infinity>" by simp
  then have int1: "integrable M (\<lambda>x. f (T x) * max (g x) 0)" by (simp add: integrableI_bounded)

  have "(\<integral>\<^sup>+ x. norm(f (T x) * max (-g x) 0) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f (T x) * g x) \<partial>M)"
    by (simp add: nn_integral_mono)
  also have "... < \<infinity>" using assms(1) by (simp add: integrable_iff_bounded)
  finally have "(\<integral>\<^sup>+ x. norm(f (T x) * max (-g x) 0) \<partial>M) < \<infinity>" by simp
  then have int2: "integrable M (\<lambda>x. f (T x) * max (-g x) 0)" by (simp add: integrableI_bounded)

  have "(\<integral>\<^sup>+x. f x * nn_transfer_operator h x \<partial>M) = (\<integral>\<^sup>+x. f (T x) * h x \<partial>M)"
    by (rule nn_transfer_operator_intg) auto
  also have "\<dots> = \<integral>\<^sup>+ x. ennreal (f (T x) * max (g x) 0 + f (T x) * max (- g x) 0) \<partial>M"
    unfolding h_def
    by (intro nn_integral_cong)(auto simp: ennreal_mult[symmetric] abs_mult split: split_max)
  also have "... < \<infinity>"
    using Bochner_Integration.integrable_add[OF int1 int2, THEN integrableD(2)] by (auto simp add: less_top)
  finally have *: "(\<integral>\<^sup>+x. f x * nn_transfer_operator h x \<partial>M) < \<infinity>" by simp

  have "(\<integral>\<^sup>+x. norm(f x * real_transfer_operator g x) \<partial>M) = (\<integral>\<^sup>+x. f x * abs(real_transfer_operator g x) \<partial>M)"
    by (simp add: abs_mult)
  also have "... \<le> (\<integral>\<^sup>+x. f x * nn_transfer_operator h x \<partial>M)"
  proof (rule nn_integral_mono_AE)
    {
      fix x assume *: "abs(real_transfer_operator g x) \<le> nn_transfer_operator h x"
      have "ennreal (f x * \<bar>real_transfer_operator g x\<bar>) = f x * ennreal(\<bar>real_transfer_operator g x\<bar>)"
        by (simp add: ennreal_mult)
      also have "... \<le> f x * nn_transfer_operator h x"
        using * by (auto intro!: mult_left_mono)
      finally have "ennreal (f x * \<bar>real_transfer_operator g x\<bar>) \<le> f x * nn_transfer_operator h x"
        by simp
    }
    then show "AE x in M. ennreal (f x * \<bar>real_transfer_operator g x\<bar>) \<le> f x * nn_transfer_operator h x"
      using real_transfer_operator_abs[OF assms(4)] h_def by auto
  qed
  finally have **: "(\<integral>\<^sup>+x. norm(f x * real_transfer_operator g x) \<partial>M) < \<infinity>" using * by auto
  show "integrable M (\<lambda>x. f x * real_transfer_operator g x)"
    using ** by (intro integrableI_bounded) auto

  have "(\<integral>\<^sup>+x. f x * nn_transfer_operator gp x \<partial>M) \<le> (\<integral>\<^sup>+x. f x * nn_transfer_operator h x \<partial>M)"
  proof (rule nn_integral_mono_AE)
    have "AE x in M. nn_transfer_operator gp x \<le> nn_transfer_operator h x"
      by (rule nn_transfer_operator_mono) (auto simp add: hgpgm)
    then show "AE x in M. f x * nn_transfer_operator gp x \<le> f x * nn_transfer_operator h x"
      by (auto simp: mult_left_mono)
  qed
  then have a: "(\<integral>\<^sup>+x. f x * nn_transfer_operator gp x \<partial>M) < \<infinity>"
    using * by auto
  have "ennreal(norm(f x * enn2real(nn_transfer_operator gp x))) \<le> f x * nn_transfer_operator gp x" for x
    by (auto simp add: ennreal_mult intro!: mult_left_mono)
       (metis enn2real_ennreal enn2real_nonneg le_cases le_ennreal_iff)
  then have "(\<integral>\<^sup>+x. norm(f x * enn2real(nn_transfer_operator gp x)) \<partial>M) \<le> (\<integral>\<^sup>+x. f x * nn_transfer_operator gp x \<partial>M)"
    by (simp add: nn_integral_mono)
  then have "(\<integral>\<^sup>+x. norm(f x * enn2real(nn_transfer_operator gp x)) \<partial>M) < \<infinity>" using a by auto
  then have gp_int: "integrable M (\<lambda>x. f x * enn2real(nn_transfer_operator gp x))" by (simp add: integrableI_bounded)
  have gp_fin: "AE x in M. f x * nn_transfer_operator gp x \<noteq> \<infinity>"
    apply (rule nn_integral_PInf_AE) using a by auto

  have "(\<integral> x. f x * enn2real(nn_transfer_operator gp x) \<partial>M) = enn2real (\<integral>\<^sup>+ x. f x * enn2real(nn_transfer_operator gp x) \<partial>M)"
    by (rule integral_eq_nn_integral) auto
  also have "... = enn2real(\<integral>\<^sup>+ x. ennreal(f (T x) * enn2real(gp x)) \<partial>M)"
  proof -
    {
      fix x assume "f x * nn_transfer_operator gp x \<noteq> \<infinity>"
      then have "ennreal (f x * enn2real (nn_transfer_operator gp x)) = ennreal (f x) * nn_transfer_operator gp x"
        by (auto simp add: ennreal_mult ennreal_mult_eq_top_iff less_top intro!: ennreal_mult_left_cong)
    }
    then have "AE x in M. ennreal (f x * enn2real (nn_transfer_operator gp x)) = ennreal (f x) * nn_transfer_operator gp x"
      using gp_fin by auto
    then have "(\<integral>\<^sup>+ x. f x * enn2real(nn_transfer_operator gp x) \<partial>M) = (\<integral>\<^sup>+ x. f x * nn_transfer_operator gp x \<partial>M)"
      by (rule nn_integral_cong_AE)
    also have "... = (\<integral>\<^sup>+ x. f (T x) * gp x \<partial>M)"
      by (rule nn_transfer_operator_intg) (auto simp add: gp_def)
    also have "... = (\<integral>\<^sup>+ x. ennreal(f (T x) * enn2real(gp x)) \<partial>M)"
      by (rule nn_integral_cong_AE) (auto simp: ennreal_mult gp_def)
    finally have "(\<integral>\<^sup>+ x. f x * enn2real(nn_transfer_operator gp x) \<partial>M) = (\<integral>\<^sup>+ x. ennreal(f (T x) * enn2real(gp x)) \<partial>M)" by simp
    then show ?thesis by simp
  qed
  also have "... = (\<integral> x. f (T x) * enn2real(gp x) \<partial>M)"
    by (rule integral_eq_nn_integral[symmetric]) (auto simp add: gp_def)
  finally have gp_expr: "(\<integral> x. f x * enn2real(nn_transfer_operator gp x) \<partial>M) = (\<integral> x. f (T x) * enn2real(gp x) \<partial>M)" by simp

  have "(\<integral>\<^sup>+x. f x * nn_transfer_operator gm x \<partial>M) \<le> (\<integral>\<^sup>+x. f x * nn_transfer_operator h x \<partial>M)"
  proof (rule nn_integral_mono_AE)
    have "AE x in M. nn_transfer_operator gm x \<le> nn_transfer_operator h x"
      by (rule nn_transfer_operator_mono) (auto simp add: hgpgm)
    then show "AE x in M. f x * nn_transfer_operator gm x \<le> f x * nn_transfer_operator h x"
      by (auto simp: mult_left_mono)
  qed
  then have a: "(\<integral>\<^sup>+x. f x * nn_transfer_operator gm x \<partial>M) < \<infinity>"
    using * by auto
  have "\<And>x. ennreal(norm(f x * enn2real(nn_transfer_operator gm x))) \<le> f x * nn_transfer_operator gm x"
    by (auto simp add: ennreal_mult intro!: mult_left_mono)
       (metis enn2real_ennreal enn2real_nonneg le_cases le_ennreal_iff)
  then have "(\<integral>\<^sup>+x. norm(f x * enn2real(nn_transfer_operator gm x)) \<partial>M) \<le> (\<integral>\<^sup>+x. f x * nn_transfer_operator gm x \<partial>M)"
    by (simp add: nn_integral_mono)
  then have "(\<integral>\<^sup>+x. norm(f x * enn2real(nn_transfer_operator gm x)) \<partial>M) < \<infinity>" using a by auto
  then have gm_int: "integrable M (\<lambda>x. f x * enn2real(nn_transfer_operator gm x))" by (simp add: integrableI_bounded)
  have gm_fin: "AE x in M. f x * nn_transfer_operator gm x \<noteq> \<infinity>"
    apply (rule nn_integral_PInf_AE) using a by auto

  have "(\<integral> x. f x * enn2real(nn_transfer_operator gm x) \<partial>M) = enn2real (\<integral>\<^sup>+ x. f x * enn2real(nn_transfer_operator gm x) \<partial>M)"
    by (rule integral_eq_nn_integral) auto
  also have "... = enn2real(\<integral>\<^sup>+ x. ennreal(f (T x) * enn2real(gm x)) \<partial>M)"
  proof -
    {
      fix x assume "f x * nn_transfer_operator gm x \<noteq> \<infinity>"
      then have "ennreal (f x * enn2real (nn_transfer_operator gm x)) = ennreal (f x) * nn_transfer_operator gm x"
        by (auto simp add: ennreal_mult ennreal_mult_eq_top_iff less_top intro!: ennreal_mult_left_cong)
    }
    then have "AE x in M. ennreal (f x * enn2real (nn_transfer_operator gm x)) = ennreal (f x) * nn_transfer_operator gm x"
      using gm_fin by auto
    then have "(\<integral>\<^sup>+ x. f x * enn2real(nn_transfer_operator gm x) \<partial>M) = (\<integral>\<^sup>+ x. f x * nn_transfer_operator gm x \<partial>M)"
      by (rule nn_integral_cong_AE)
    also have "... = (\<integral>\<^sup>+ x. f (T x) * gm x \<partial>M)"
      by (rule nn_transfer_operator_intg) (auto simp add: gm_def)
    also have "... = (\<integral>\<^sup>+ x. ennreal(f (T x) * enn2real(gm x)) \<partial>M)"
      by (rule nn_integral_cong_AE) (auto simp: ennreal_mult gm_def)
    finally have "(\<integral>\<^sup>+ x. f x * enn2real(nn_transfer_operator gm x) \<partial>M) = (\<integral>\<^sup>+ x. ennreal(f (T x) * enn2real(gm x)) \<partial>M)" by simp
    then show ?thesis by simp
  qed
  also have "... = (\<integral> x. f (T x) * enn2real(gm x) \<partial>M)"
    by (rule integral_eq_nn_integral[symmetric]) (auto simp add: gm_def)
  finally have gm_expr: "(\<integral> x. f x * enn2real(nn_transfer_operator gm x) \<partial>M) = (\<integral> x. f (T x) * enn2real(gm x) \<partial>M)" by simp

  have "(\<integral> x. f x * real_transfer_operator g x \<partial>M) = (\<integral> x. f x * enn2real(nn_transfer_operator gp x) - f x * enn2real(nn_transfer_operator gm x) \<partial>M)"
    unfolding real_transfer_operator_def gp_def gm_def by (simp add: right_diff_distrib)
  also have "... = (\<integral> x. f x * enn2real(nn_transfer_operator gp x) \<partial>M) - (\<integral> x. f x * enn2real(nn_transfer_operator gm x) \<partial>M)"
    by (rule Bochner_Integration.integral_diff) (simp_all add: gp_int gm_int)
  also have "... = (\<integral> x. f (T x) * enn2real(gp x) \<partial>M) - (\<integral> x. f (T x) * enn2real(gm x) \<partial>M)"
    using gp_expr gm_expr by simp
  also have "... = (\<integral> x. f (T x) * max (g x) 0 \<partial>M) - (\<integral> x. f (T x) * max (-g x) 0 \<partial>M)"
    using gp_real gm_real by simp
  also have "... = (\<integral> x. f (T x) * max (g x) 0 - f (T x) * max (-g x) 0 \<partial>M)"
    by (rule Bochner_Integration.integral_diff[symmetric]) (simp_all add: int1 int2)
  also have "... = (\<integral>x. f (T x) * g x \<partial>M)"
    by (metis (mono_tags, hide_lams) diff_0 diff_zero eq_iff max.cobounded2 max_def minus_minus neg_le_0_iff_le right_diff_distrib)
  finally show "(\<integral> x. f x * real_transfer_operator g x \<partial>M) = (\<integral>x. f (T x) * g x \<partial>M)"
    by simp
qed

lemma real_transfer_operator_intg:
  assumes "integrable M (\<lambda>x. f (T x) * g x)" and
          [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "integrable M (\<lambda>x. f x * real_transfer_operator g x)"
        "(\<integral> x. f x * real_transfer_operator g x \<partial>M) = (\<integral> x. f (T x) * g x \<partial>M)"
proof -
  define fp where "fp = (\<lambda>x. max (f x) 0)"
  define fm where "fm = (\<lambda>x. max (-f x) 0)"
  have [measurable]: "fp \<in> borel_measurable M" "fm \<in> borel_measurable M"
    unfolding fp_def fm_def by simp_all

  have "(\<integral>\<^sup>+ x. norm(fp (T x) * g x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f (T x) * g x) \<partial>M)"
    by (simp add: fp_def nn_integral_mono)
  also have "... < \<infinity>" using assms(1) by (simp add: integrable_iff_bounded)
  finally have "(\<integral>\<^sup>+ x. norm(fp (T x) * g x) \<partial>M) < \<infinity>" by simp
  then have intp: "integrable M (\<lambda>x. fp (T x) * g x)" by (simp add: integrableI_bounded)
  moreover have "\<And>x. fp x \<ge> 0" unfolding fp_def by simp
  ultimately have Rp: "integrable M (\<lambda>x. fp x * real_transfer_operator g x)"
    "(\<integral> x. fp x * real_transfer_operator g x \<partial>M) = (\<integral> x. fp (T x) * g x \<partial>M)"
  using real_transfer_operator_intg_fpos by auto

  have "(\<integral>\<^sup>+ x. norm(fm (T x) * g x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f (T x) * g x) \<partial>M)"
    by (simp add: fm_def nn_integral_mono)
  also have "... < \<infinity>" using assms(1) by (simp add: integrable_iff_bounded)
  finally have "(\<integral>\<^sup>+ x. norm(fm (T x) * g x) \<partial>M) < \<infinity>" by simp
  then have intm: "integrable M (\<lambda>x. fm (T x) * g x)" by (simp add: integrableI_bounded)
  moreover have "\<And>x. fm x \<ge> 0" unfolding fm_def by simp
  ultimately have Rm: "integrable M (\<lambda>x. fm x * real_transfer_operator g x)"
    "(\<integral> x. fm x * real_transfer_operator g x \<partial>M) = (\<integral> x. fm (T x) * g x \<partial>M)"
  using real_transfer_operator_intg_fpos by auto

  have "integrable M (\<lambda>x. fp x * real_transfer_operator g x - fm x * real_transfer_operator g x)"
    using Rp(1) Rm(1) integrable_diff by simp
  moreover have *: "\<And>x. f x * real_transfer_operator g x = fp x * real_transfer_operator g x - fm x * real_transfer_operator g x"
    unfolding fp_def fm_def by (simp add: max_def)
  ultimately show "integrable M (\<lambda>x. f x * real_transfer_operator g x)"
    by simp

  have "(\<integral> x. f x * real_transfer_operator g x \<partial>M) = (\<integral> x. fp x * real_transfer_operator g x - fm x * real_transfer_operator g x \<partial>M)"
    using * by simp
  also have "... = (\<integral> x. fp x * real_transfer_operator g x \<partial>M) - (\<integral> x. fm x * real_transfer_operator g x \<partial>M)"
    using Rp(1) Rm(1) by simp
  also have "... = (\<integral> x. fp (T x) * g x \<partial>M) - (\<integral> x. fm (T x) * g x \<partial>M)"
    using Rp(2) Rm(2) by simp
  also have "... = (\<integral> x. fp (T x) * g x - fm (T x) * g x \<partial>M)"
    using intm intp by simp
  also have "... = (\<integral> x. f (T x) * g x \<partial>M)"
    unfolding fp_def fm_def by (metis (no_types, hide_lams) diff_0 diff_zero max.commute
    max_def minus_minus mult.commute neg_le_iff_le right_diff_distrib)
  finally show "(\<integral> x. f x * real_transfer_operator g x \<partial>M) = (\<integral> x. f (T x) * g x \<partial>M)" by simp
qed

lemma real_transfer_operator_int [intro]:
  assumes "integrable M f"
  shows "integrable M (real_transfer_operator f)"
        "(\<integral>x. real_transfer_operator f x \<partial>M) = (\<integral>x. f x \<partial>M)"
using real_transfer_operator_intg[where ?f = "\<lambda>x. 1" and ?g = f] assms by auto

lemma real_transfer_operator_charact:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>x. indicator A x * g x \<partial>M) = (\<integral>x. indicator A (T x) * f x \<partial>M)"
      and [measurable]: "integrable M f" "integrable M g"
  shows "AE x in M. real_transfer_operator f x = g x"
proof (rule AE_symmetric[OF density_unique_real])
  fix A assume [measurable]: "A \<in> sets M"
  have "set_lebesgue_integral M A (real_transfer_operator f) = (\<integral>x. indicator A x * real_transfer_operator f x \<partial>M)"
    unfolding set_lebesgue_integral_def by auto
  also have "... = (\<integral>x. indicator A (T x) * f x \<partial>M)"
    apply (rule real_transfer_operator_intg, auto)
    by (rule Bochner_Integration.integrable_bound[of _ "\<lambda>x. abs(f x)"], auto simp add: assms indicator_def)
  also have "... = set_lebesgue_integral M A g"
    unfolding set_lebesgue_integral_def using assms(1)[OF \<open>A \<in> sets M\<close>] by auto
  finally show "set_lebesgue_integral M A g = set_lebesgue_integral M A (real_transfer_operator f)"
    by simp
qed (auto simp add: assms real_transfer_operator_int)

lemma (in mpt) real_transfer_operator_foT:
  assumes "integrable M f"
  shows "AE x in M. real_transfer_operator (f o T) x = f x"
proof -
  have *: "(\<integral> x. indicator A x * f x \<partial>M) = (\<integral>x. indicator A (T x) * f (T x) \<partial>M)" if [measurable]: "A \<in> sets M" for A
    apply (subst T_integral_preserving)
    using integrable_real_mult_indicator[OF that assms] by (auto simp add: mult.commute)
  show ?thesis
    apply (rule real_transfer_operator_charact)
    using assms * by (auto simp add: comp_def T_integral_preserving)
qed

lemma real_transfer_operator_foT_g:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M" "integrable M (\<lambda>x. f (T x) * g x)"
  shows "AE x in M. real_transfer_operator (\<lambda>x. f (T x) * g x) x = f x * real_transfer_operator g x"
proof -
  have *: "(\<integral>x. indicator A x * (f x * real_transfer_operator g x) \<partial>M) = (\<integral>x. indicator A (T x) * (f (T x) * g x) \<partial>M)"
    if [measurable]: "A \<in> sets M" for A
    apply (simp add: mult.assoc[symmetric])
    apply (subst real_transfer_operator_intg)
    apply (rule Bochner_Integration.integrable_bound[of _ "(\<lambda>x. f (T x) * g x)"])
    by (auto simp add: assms indicator_def)
  show ?thesis
    by (rule real_transfer_operator_charact) (auto simp add: assms * intro!: real_transfer_operator_intg)
qed

lemma real_transfer_operator_add [intro]:
  assumes [measurable]: "integrable M f" "integrable M g"
  shows "AE x in M. real_transfer_operator (\<lambda>x. f x + g x) x = real_transfer_operator f x + real_transfer_operator g x"
proof (rule real_transfer_operator_charact)
  have "integrable M (real_transfer_operator f)" "integrable M (real_transfer_operator g)"
    using real_transfer_operator_int(1) assms by auto
  then show "integrable M (\<lambda>x. real_transfer_operator f x + real_transfer_operator g x)"
    by auto

  fix A assume [measurable]: "A \<in> sets M"
  have intAf: "integrable M (\<lambda>x. indicator A (T x) * f x)"
    apply (rule Bochner_Integration.integrable_bound[OF assms(1)]) unfolding indicator_def by auto
  have intAg: "integrable M (\<lambda>x. indicator A (T x) * g x)"
    apply (rule Bochner_Integration.integrable_bound[OF assms(2)]) unfolding indicator_def by auto

  have "(\<integral>x. indicator A x * (real_transfer_operator f x + real_transfer_operator g x)\<partial>M)
      = (\<integral>x. indicator A x * real_transfer_operator f x + indicator A x* real_transfer_operator g x \<partial>M)"
    by (simp add: algebra_simps)
  also have "... = (\<integral>x. indicator A x * real_transfer_operator f x \<partial>M) + (\<integral>x. indicator A x * real_transfer_operator g x \<partial>M)"
    apply (rule Bochner_Integration.integral_add)
    using integrable_real_mult_indicator[OF \<open>A \<in> sets M\<close> real_transfer_operator_int(1)[OF assms(1)]]
          integrable_real_mult_indicator[OF \<open>A \<in> sets M\<close> real_transfer_operator_int(1)[OF assms(2)]]
    by (auto simp add: mult.commute)
  also have "... = (\<integral>x. indicator A (T x) * f x \<partial>M) + (\<integral>x. indicator A (T x) * g x \<partial>M)"
    using real_transfer_operator_intg(2) assms \<open>A \<in> sets M\<close> intAf intAg by auto
  also have "... = (\<integral>x. indicator A (T x) * f x + indicator A (T x) * g x \<partial>M)"
    by (rule Bochner_Integration.integral_add[symmetric]) (auto simp add: assms \<open>A \<in> sets M\<close> intAf intAg)
  also have "... = \<integral>x. indicator A (T x) * (f x + g x)\<partial>M"
    by (simp add: algebra_simps)
  finally show "(\<integral>x. indicator A x * (real_transfer_operator f x + real_transfer_operator g x)\<partial>M) = \<integral>x. indicator A (T x) * (f x + g x)\<partial>M"
    by simp
qed (auto simp add: assms)

lemma real_transfer_operator_cong:
  assumes ae: "AE x in M. f x = g x" and [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "AE x in M. real_transfer_operator f x = real_transfer_operator g x"
proof -
  have "AE x in M. nn_transfer_operator (\<lambda>x. ennreal (f x)) x = nn_transfer_operator (\<lambda>x. ennreal (g x)) x"
    apply (rule nn_transfer_operator_cong) using assms by auto
  moreover have "AE x in M. nn_transfer_operator (\<lambda>x. ennreal (-f x)) x = nn_transfer_operator (\<lambda>x. ennreal(-g x)) x"
    apply (rule nn_transfer_operator_cong) using assms by auto
  ultimately show "AE x in M. real_transfer_operator f x = real_transfer_operator g x"
    unfolding real_transfer_operator_def by auto
qed

lemma real_transfer_operator_cmult [intro, simp]:
  fixes c::real
  assumes "integrable M f"
  shows "AE x in M. real_transfer_operator (\<lambda>x. c * f x) x = c * real_transfer_operator f x"
by (rule real_transfer_operator_foT_g) (auto simp add: assms borel_measurable_integrable)

lemma real_transfer_operator_cdiv [intro, simp]:
  fixes c::real
  assumes "integrable M f"
  shows "AE x in M. real_transfer_operator (\<lambda>x. f x / c) x = real_transfer_operator f x / c"
using real_transfer_operator_cmult[of _ "1/c", OF assms] by (auto simp add: divide_simps)

lemma real_transfer_operator_diff [intro, simp]:
  assumes [measurable]: "integrable M f" "integrable M g"
  shows "AE x in M. real_transfer_operator (\<lambda>x. f x - g x) x = real_transfer_operator f x - real_transfer_operator g x"
proof -
  have "AE x in M. real_transfer_operator (\<lambda>x. f x + (- g x)) x = real_transfer_operator f x + real_transfer_operator (\<lambda>x. -g x) x"
    using real_transfer_operator_add[where ?f = f and ?g = "\<lambda>x. - g x"] assms by auto
  moreover have "AE x in M. real_transfer_operator (\<lambda>x. -g x) x = - real_transfer_operator g x"
    using real_transfer_operator_cmult[where ?f = g and ?c = "-1"] assms(2) by auto
  ultimately show ?thesis by auto
qed

lemma real_transfer_operator_pos [intro]:
  assumes "AE x in M. f x \<ge> 0" and [measurable]: "f \<in> borel_measurable M"
  shows "AE x in M. real_transfer_operator f x \<ge> 0"
proof -
  define g where "g = (\<lambda>x. max (f x) 0)"
  have "AE x in M. f x = g x" using assms g_def by auto
  then have *: "AE x in M. real_transfer_operator f x = real_transfer_operator g x" using real_transfer_operator_cong g_def by auto

  have "\<And>x. g x \<ge> 0" unfolding g_def by simp
  then have "(\<lambda>x. ennreal(-g x)) = (\<lambda>x. 0)"
    by (simp add: ennreal_neg)
  then have "AE x in M. nn_transfer_operator (\<lambda>x. ennreal(-g x)) x = 0"
    using nn_transfer_operator_zero by simp
  then have "AE x in M. real_transfer_operator g x = enn2real(nn_transfer_operator (\<lambda>x. ennreal (g x)) x)"
    unfolding real_transfer_operator_def by auto
  then have "AE x in M. real_transfer_operator g x \<ge> 0" by auto
  then show ?thesis using * by auto
qed

lemma real_transfer_operator_mono:
  assumes "AE x in M. f x \<le> g x" and [measurable]: "integrable M f" "integrable M g"
  shows "AE x in M. real_transfer_operator f x \<le> real_transfer_operator g x"
proof -
  have "AE x in M. real_transfer_operator g x - real_transfer_operator f x = real_transfer_operator (\<lambda>x. g x - f x) x"
    by (rule AE_symmetric[OF real_transfer_operator_diff], auto simp add: assms)
  moreover have "AE x in M. real_transfer_operator (\<lambda>x. g x - f x) x \<ge> 0"
    by (rule real_transfer_operator_pos, auto simp add: assms(1))
  ultimately have "AE x in M. real_transfer_operator g x - real_transfer_operator f x \<ge> 0" by auto
  then show ?thesis by auto
qed

lemma real_transfer_operator_sum [intro, simp]:
  fixes f::"'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes [measurable]: "\<And>i. integrable M (f i)"
  shows "AE x in M. real_transfer_operator (\<lambda>x. \<Sum>i\<in>I. f i x) x = (\<Sum>i\<in>I. real_transfer_operator (f i) x)"
proof (rule real_transfer_operator_charact)
  fix A assume [measurable]: "A \<in> sets M"
  have *: "integrable M (\<lambda>x. indicator A (T x) * f i x)" for i
    apply (rule Bochner_Integration.integrable_bound[of _ "f i"]) by (auto simp add: assms indicator_def)
  have **: "integrable M (\<lambda>x. indicator A x * real_transfer_operator (f i) x)" for i
    apply (rule Bochner_Integration.integrable_bound[of _ "real_transfer_operator (f i)"]) by (auto simp add: assms indicator_def)
  have inti: "(\<integral>x. indicator A (T x) * f i x \<partial>M) = (\<integral>x. indicator A x * real_transfer_operator (f i) x \<partial>M)" for i
    by (rule real_transfer_operator_intg(2)[symmetric], auto simp add: *)

  have "(\<integral>x. indicator A (T x) * (\<Sum>i\<in>I. f i x)\<partial>M) = (\<integral>x. (\<Sum>i\<in>I. indicator A (T x) * f i x)\<partial>M)"
    by (simp add: sum_distrib_left)
  also have "... = (\<Sum>i\<in>I. (\<integral>x. indicator A (T x) * f i x \<partial>M))"
    by (rule Bochner_Integration.integral_sum, simp add: *)
  also have "... = (\<Sum>i\<in>I. (\<integral>x. indicator A x * real_transfer_operator (f i) x \<partial>M))"
    using inti by auto
  also have "... = (\<integral>x. (\<Sum>i\<in>I. indicator A x * real_transfer_operator (f i) x)\<partial>M)"
    by (rule Bochner_Integration.integral_sum[symmetric], simp add: **)
  also have "... = (\<integral>x. indicator A x * (\<Sum>i\<in>I. real_transfer_operator (f i) x)\<partial>M)"
    by (simp add: sum_distrib_left)
  finally show "(\<integral>x. indicator A x * (\<Sum>i\<in>I. real_transfer_operator (f i) x)\<partial>M) = (\<integral>x. indicator A (T x) * (\<Sum>i\<in>I. f i x)\<partial>M)" by auto
qed (auto simp add: assms real_transfer_operator_int(1)[OF assms(1)])
end (*of context qmpt*)



subsection \<open>Conservativity in terms of transfer operators\<close>

text \<open>Conservativity amounts to the fact that $\sum f(T^n x) = \infty$ for almost every $x$
such that $f(x)>0$, if $f$ is nonnegative (see Lemma \verb+recurrent_series_infinite+).
There is a dual formulation, in terms of transfer
operators, asserting that $\sum \hat T^n f(x) = \infty$ for almost every $x$ such that $f(x)>0$.
It is proved by duality, reducing to the previous statement.\<close>

theorem (in conservative) recurrence_series_infinite_transfer_operator:
  assumes [measurable]: "f \<in> borel_measurable M"
  shows "AE x in M. f x > 0 \<longrightarrow> (\<Sum>n. (nn_transfer_operator^^n) f x) = \<infinity>"
proof -
  define A where "A = {x \<in> space M. f x > 0}"
  have [measurable]: "A \<in> sets M"
    unfolding A_def by auto
  have K: "emeasure M {x \<in> A. (\<Sum>n. (nn_transfer_operator^^n) f x) \<le> K} = 0" if "K < \<infinity>" for K
  proof (rule ccontr)
    assume "emeasure M {x \<in> A. (\<Sum>n. (nn_transfer_operator^^n) f x) \<le> K} \<noteq> 0"
    then have *: "emeasure M {x \<in> A. (\<Sum>n. (nn_transfer_operator^^n) f x) \<le> K} > 0"
      using not_gr_zero by blast
    obtain B where B [measurable]: "B \<in> sets M" "B \<subseteq> {x \<in> A. (\<Sum>n. (nn_transfer_operator^^n) f x) \<le> K}" "emeasure M B < \<infinity>" "emeasure M B > 0"
      using approx_with_finite_emeasure[OF _ *] by auto
    have "f x > 0" if "x \<in> B" for x
      using B(2) that unfolding A_def by auto
    moreover have "AE x\<in>B in M. (\<Sum>n. indicator B ((T^^n) x)) = (\<infinity>::ennreal)"
      using recurrence_series_infinite[of "indicator B"] by (auto simp add: indicator_def)
    ultimately have PInf: "AE x\<in>B in M. (\<Sum>n. indicator B ((T^^n) x)) * f x = \<top>"
      unfolding ennreal_mult_eq_top_iff by fastforce

    have "(\<integral>\<^sup>+x. indicator B x * (\<Sum>n. (nn_transfer_operator^^n) f x) \<partial>M) \<le> (\<integral>\<^sup>+x. indicator B x * K \<partial>M)"
      apply (rule nn_integral_mono) using B(2) unfolding indicator_def by auto
    also have "... = K * emeasure M B"
      by (simp add: mult.commute nn_integral_cmult_indicator)
    also have "... < \<infinity>" using \<open>K < \<infinity>\<close> B(3)
      using ennreal_mult_eq_top_iff top.not_eq_extremum by auto
    finally have *: "(\<integral>\<^sup>+x. indicator B x * (\<Sum>n. (nn_transfer_operator^^n) f x) \<partial>M) < \<infinity>" by auto

    have "(\<integral>\<^sup>+x. indicator B x * (\<Sum>n. (nn_transfer_operator^^n) f x) \<partial>M)
            = (\<integral>\<^sup>+x. (\<Sum>n. indicator B x * (nn_transfer_operator^^n) f x) \<partial>M)"
      by auto
    also have "... = (\<Sum>n. (\<integral>\<^sup>+x. indicator B x * (nn_transfer_operator^^n) f x \<partial>M))"
      by (rule nn_integral_suminf, auto)
    also have "... = (\<Sum>n. (\<integral>\<^sup>+x. indicator B ((T^^n) x) * f x \<partial>M))"
      using nn_transfer_operator_intTn_g by auto
    also have "... = (\<integral>\<^sup>+x. (\<Sum>n. indicator B ((T^^n) x) * f x) \<partial>M)"
      by (rule nn_integral_suminf[symmetric], auto)
    also have "... = (\<integral>\<^sup>+x. (\<Sum>n. indicator B ((T^^n) x)) * f x \<partial>M)"
      by auto
    finally have **: "(\<integral>\<^sup>+x. (\<Sum>n. indicator B ((T^^n) x)) * f x \<partial>M) \<noteq> \<infinity>"
      using * by simp
    have "AE x in M. (\<Sum>n. indicator B ((T^^n) x)) * f x \<noteq> \<infinity>"
      by (rule nn_integral_noteq_infinite[OF _ **], auto)
    then have "AE x\<in>B in M. False"
      using PInf by auto
    then have "emeasure M B = 0"
      by (smt AE_E B(1) Collect_mem_eq Collect_mono_iff dual_order.trans emeasure_eq_0 subsetD sets.sets_into_space)
    then show False
      using B by auto
  qed
  have L: "{x \<in> A. (\<Sum>n. (nn_transfer_operator^^n) f x) \<le> K} \<in> null_sets M" if "K < \<infinity>" for K
    using K[OF that] by auto
  have P: "AE x in M. x \<in> A \<longrightarrow> (\<Sum>n. (nn_transfer_operator^^n) f x) \<ge> K" if "K < \<infinity>" for K
    using AE_not_in[OF L[OF that]] by auto
  have "AE x in M. \<forall>N::nat. (x \<in> A \<longrightarrow> (\<Sum>n. (nn_transfer_operator^^n) f x) \<ge> of_nat N)"
    unfolding AE_all_countable by (auto simp add: of_nat_less_top intro!: P)
  then have "AE x in M. f x > 0 \<longrightarrow> (\<forall>N::nat. (\<Sum>n. (nn_transfer_operator^^n) f x) \<ge> of_nat N)"
    unfolding A_def by auto
  then show "AE x in M. 0 < f x \<longrightarrow> (\<Sum>n. (nn_transfer_operator ^^ n) f x) = \<infinity>"
    using ennreal_ge_nat_imp_PInf by auto
qed


end (*of Transfer_Operator.thy*)
