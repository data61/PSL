theory Laplace_Transform_Library
  imports
    "HOL-Analysis.Analysis"
begin

section \<open>References\<close>

text \<open>
Much of this formalization is based on Schiff's textbook @{cite "Schiff2013"}.
Parts of this formalization are inspired by the HOL-Light formalization
(@{cite "Taqdees2013"}, @{cite "Rashid2017"}, @{cite "Rashid2018"}), but stated more generally for
piecewise continuous (instead of piecewise continuously differentiable) functions.
\<close>

section \<open>Library Additions\<close>

subsection \<open>Derivatives\<close>

lemma DERIV_compose_FDERIV:\<comment>\<open>TODO: generalize and move from HOL-ODE\<close>
  assumes "DERIV f (g x) :> f'"
  assumes "(g has_derivative g') (at x within s)"
  shows "((\<lambda>x. f (g x)) has_derivative (\<lambda>x. g' x * f')) (at x within s)"
  using assms has_derivative_compose[of g g' x s f "(*) f'"]
  by (auto simp: has_field_derivative_def ac_simps)

lemmas has_derivative_sin[derivative_intros] = DERIV_sin[THEN DERIV_compose_FDERIV]
  and  has_derivative_cos[derivative_intros] = DERIV_cos[THEN DERIV_compose_FDERIV]
  and  has_derivative_exp[derivative_intros] = DERIV_exp[THEN DERIV_compose_FDERIV]


subsection \<open>Integrals\<close>

lemma negligible_real_ivlI:
  fixes a b::real
  assumes "a \<ge> b"
  shows "negligible {a .. b}"
proof -
  from assms have "{a .. b} = {a} \<or> {a .. b} = {}"
    by auto
  then show ?thesis
    by auto
qed

lemma absolutely_integrable_on_combine:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "f absolutely_integrable_on {a..c}"
    and "f absolutely_integrable_on {c..b}"
    and "a \<le> c"
    and "c \<le> b"
  shows "f absolutely_integrable_on {a..b}"
  using assms
  unfolding absolutely_integrable_on_def integrable_on_def
  by (auto intro!: has_integral_combine)

lemma dominated_convergence_at_top:
  fixes f :: "real \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes f: "\<And>k. (f k) integrable_on s" and h: "h integrable_on s"
    and le: "\<And>k x. x \<in> s \<Longrightarrow> norm (f k x) \<le> h x"
    and conv: "\<forall>x \<in> s. ((\<lambda>k. f k x) \<longlongrightarrow> g x) at_top"
  shows "g integrable_on s" "((\<lambda>k. integral s (f k)) \<longlongrightarrow> integral s g) at_top"
proof -
  have 3: "set_integrable lebesgue s h"
    unfolding absolutely_integrable_on_def
  proof
    show "(\<lambda>x. norm (h x)) integrable_on s"
    proof (intro integrable_spike_finite[OF _ _ h, where S="{}"] ballI)
      fix x assume "x \<in> s - {}" then show "norm (h x) = h x"
        using order_trans[OF norm_ge_zero le[of x]] by auto
    qed auto
  qed fact
  have 2: "set_borel_measurable lebesgue s (f k)" for k
    using f[of k]
    using has_integral_implies_lebesgue_measurable[of "f k"]
    by (auto intro:  simp: integrable_on_def set_borel_measurable_def)
  have conv': "\<forall>x \<in> s. ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
    using conv filterlim_filtermap filterlim_compose filterlim_real_sequentially by blast
  from 2 have 1: "set_borel_measurable lebesgue s g"
    unfolding set_borel_measurable_def
    by (rule borel_measurable_LIMSEQ_metric) (use conv' in \<open>auto split: split_indicator\<close>)
  have 4: "AE x in lebesgue. ((\<lambda>i. indicator s x *\<^sub>R f i x) \<longlongrightarrow> indicator s x *\<^sub>R g x) at_top"
    "\<forall>\<^sub>F i in at_top. AE x in lebesgue. norm (indicator s x *\<^sub>R f i x) \<le> indicator s x *\<^sub>R h x"
    using conv le by (auto intro!: always_eventually split: split_indicator)

  note 1 2 3 4
  note * = this[unfolded set_borel_measurable_def set_integrable_def]
  have g: "g absolutely_integrable_on s"
    unfolding set_integrable_def
    by (rule integrable_dominated_convergence_at_top[OF *])
  then show "g integrable_on s"
    by (auto simp: absolutely_integrable_on_def)
  have "((\<lambda>k. (LINT x:s|lebesgue. f k x)) \<longlongrightarrow> (LINT x:s|lebesgue. g x)) at_top"
    unfolding set_lebesgue_integral_def
    using *
    by (rule integral_dominated_convergence_at_top)
  then show "((\<lambda>k. integral s (f k)) \<longlongrightarrow> integral s g) at_top"
    using g absolutely_integrable_integrable_bound[OF le f h]
    by (subst (asm) (1 2) set_lebesgue_integral_eq_integral) auto
qed

lemma has_integral_dominated_convergence_at_top:
  fixes f :: "real \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "\<And>k. (f k has_integral y k) s" "h integrable_on s"
    "\<And>k x. x\<in>s \<Longrightarrow> norm (f k x) \<le> h x" "\<forall>x\<in>s. ((\<lambda>k. f k x) \<longlongrightarrow> g x) at_top"
    and x: "(y \<longlongrightarrow> x) at_top"
  shows "(g has_integral x) s"
proof -
  have int_f: "\<And>k. (f k) integrable_on s"
    using assms by (auto simp: integrable_on_def)
  have "(g has_integral (integral s g)) s"
    by (intro integrable_integral dominated_convergence_at_top[OF int_f assms(2)]) fact+
  moreover have "integral s g = x"
  proof (rule tendsto_unique)
    show "((\<lambda>i. integral s (f i)) \<longlongrightarrow> x) at_top"
      using integral_unique[OF assms(1)] x by simp
    show "((\<lambda>i. integral s (f i)) \<longlongrightarrow> integral s g) at_top"
      by (intro dominated_convergence_at_top[OF int_f assms(2)]) fact+
  qed simp
  ultimately show ?thesis
    by simp
qed

lemma integral_indicator_eq_restriction:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes f: "f integrable_on R"
    and "R \<subseteq> S"
  shows "integral S (\<lambda>x. indicator R x *\<^sub>R f x) = integral R f"
proof -
  let ?f = "\<lambda>x. indicator R x *\<^sub>R f x"
  have "?f integrable_on R"
    using f negligible_empty
    by (rule integrable_spike) auto
  from integrable_integral[OF this]
  have "(?f has_integral integral R ?f) S"
    by (rule has_integral_on_superset) (use \<open>R \<subseteq> S\<close> in \<open>auto simp: indicator_def\<close>)
  also have "integral R ?f = integral R f"
    using negligible_empty
    by (rule integral_spike) auto
  finally show ?thesis
    by blast
qed

lemma
  improper_integral_at_top:
  fixes f::"real \<Rightarrow> 'a::euclidean_space"
  assumes "f absolutely_integrable_on {a..}"
  shows "((\<lambda>x. integral {a..x} f) \<longlongrightarrow> integral {a..} f) at_top"
proof -
  let ?f = "\<lambda>(k::real) (t::real). indicator {a..k} t *\<^sub>R f t"
  have f: "f integrable_on {a..k}" for k
    using set_lebesgue_integral_eq_integral(1)[OF assms]
    by (rule integrable_on_subinterval) simp
  from this negligible_empty have "?f k integrable_on {a..k}" for k
    by (rule integrable_spike) auto
  from this have "?f k integrable_on {a..}" for k
    by (rule integrable_on_superset) auto
  moreover
  have "(\<lambda>x. norm (f x)) integrable_on {a..}"
    using assms by (simp add: absolutely_integrable_on_def)
  moreover
  note _
  moreover
  have "\<forall>\<^sub>F k in at_top. k \<ge> x" for x::real
    by (simp add: eventually_ge_at_top)
  then have "\<forall>x\<in>{a..}. ((\<lambda>k. ?f k x) \<longlongrightarrow> f x) at_top"
    by (auto intro!: Lim_transform_eventually[OF tendsto_const] simp: indicator_def eventually_at_top_linorder)
  ultimately
  have "((\<lambda>k. integral {a..} (?f k)) \<longlongrightarrow> integral {a ..} f) at_top"
    by (rule dominated_convergence_at_top) (auto simp: indicator_def)
  also have "(\<lambda>k. integral {a..} (?f k)) = (\<lambda>k. integral {a..k} f)"
    by (auto intro!: ext integral_indicator_eq_restriction f)
  finally show ?thesis .
qed

lemma norm_integrable_onI: "(\<lambda>x. norm (f x)) integrable_on S"
  if "f absolutely_integrable_on S"
  for f::"'a::euclidean_space\<Rightarrow>'b::euclidean_space"
  using that by (auto simp: absolutely_integrable_on_def)

lemma
  has_integral_improper_at_topI:
  fixes f::"real \<Rightarrow> 'a::banach"
  assumes I: "\<forall>\<^sub>F k in at_top. (f has_integral I k) {a..k}"
  assumes J: "(I \<longlongrightarrow> J) at_top"
  shows "(f has_integral J) {a..}"
  apply (subst has_integral')
proof (auto, goal_cases)
  case (1 e)
  from tendstoD[OF J \<open>0 < e\<close>]
  have "\<forall>\<^sub>F x in at_top. dist (I x) J < e" .
  moreover have "\<forall>\<^sub>F x in at_top. (x::real) > 0" by simp
  moreover have "\<forall>\<^sub>F x in at_top. (x::real) > - a"\<comment>\<open>TODO: this seems to be strange?\<close>
    by simp
  moreover note I
  ultimately have "\<forall>\<^sub>F x in at_top. x > 0 \<and> x > - a \<and> dist (I x) J < e \<and>
    (f has_integral I x) {a..x}" by eventually_elim auto
  then obtain k where k: "\<forall>b\<ge>k. norm (I b - J) < e" "k > 0" "k > - a"
    and I: "\<And>c. c \<ge> k \<Longrightarrow> (f has_integral I c) {a..c}"
    by (auto simp: eventually_at_top_linorder dist_norm)
  show ?case
    apply (rule exI[where x=k])
    apply (auto simp: \<open>0 < k\<close>)
    subgoal premises prems for b c
    proof -
      have ball_eq: "ball 0 k = {-k <..< k}" by (auto simp: abs_real_def split: if_splits)
      from prems \<open>0 < k\<close> have "c \<ge> 0" "b \<le> 0"
        by (auto simp: subset_iff)
      with prems \<open>0 < k\<close> have "c \<ge> k"
        apply (auto simp: ball_eq)
        apply (auto simp: subset_iff)
        apply (drule spec[where x="(c + k)/2"])
        apply (auto simp: algebra_split_simps not_less)
        using \<open>0 \<le> c\<close> by linarith
      then have "norm (I c - J) < e" using k by auto
      moreover
      from prems \<open>0 < k\<close> \<open>c \<ge> 0\<close> \<open>b \<le> 0\<close> \<open>c \<ge> k\<close> \<open>k > - a\<close> have "a \<ge> b"
        apply (auto simp: ball_eq)
        apply (auto simp: subset_iff)
        by (meson \<open>b \<le> 0\<close> less_eq_real_def minus_less_iff not_le order_trans)
      have "((\<lambda>x. if x \<in> cbox a c then f x else 0) has_integral I c) (cbox b c)"
        apply (subst has_integral_restrict_closed_subintervals_eq)
        using I[of c] prems \<open>a \<ge> b\<close> \<open>k \<le> c\<close>
        by (auto )
      from negligible_empty _ this have "((\<lambda>x. if a \<le> x then f x else 0) has_integral I c) (cbox b c)"
        by (rule has_integral_spike) auto
      ultimately
      show ?thesis
        by (intro exI[where x="I c"]) auto
    qed
    done
qed

lemma has_integral_improperE:
  fixes f::"real \<Rightarrow> 'a::euclidean_space"
  assumes I: "(f has_integral I) {a..}"
  assumes ai: "f absolutely_integrable_on {a..}"
  obtains J where
    "\<And>k. (f has_integral J k) {a..k}"
    "(J \<longlongrightarrow> I) at_top"
proof -
  define J where "J k = integral {a .. k} f" for k
  have "(f has_integral J k) {a..k}" for k
    unfolding J_def
    by (force intro: integrable_on_subinterval has_integral_integrable[OF I])
  moreover
  have I_def[symmetric]: "integral {a..} f = I"
    using I by auto
  from improper_integral_at_top[OF ai]
  have "(J \<longlongrightarrow> I) at_top"
    unfolding J_def I_def .
  ultimately show ?thesis ..
qed


subsection \<open>Miscellaneous\<close>

lemma AE_BallI: "AE x\<in>X in F. P x" if "\<forall>x \<in> X. P x"
  using that by (intro always_eventually) auto

lemma bounded_le_Sup:
  assumes "bounded (f ` S)"
  shows "\<forall>x\<in>S. norm (f x) \<le> Sup (norm ` f ` S)"
  by (auto intro!: cSup_upper bounded_imp_bdd_above simp: bounded_norm_comp assms)

end