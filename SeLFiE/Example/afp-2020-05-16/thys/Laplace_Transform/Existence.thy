section \<open>Existence\<close>
theory Existence imports
  Piecewise_Continuous
begin

subsection \<open>Definition\<close>

definition has_laplace :: "(real \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> bool"
  (infixr "has'_laplace" 46)
  where "(f has_laplace L) s \<longleftrightarrow> ((\<lambda>t. exp (t *\<^sub>R - s) * f t) has_integral L) {0..}"

lemma has_laplaceI:
  assumes "((\<lambda>t. exp (t *\<^sub>R - s) * f t) has_integral L) {0..}"
  shows "(f has_laplace L) s"
  using assms
  by (auto simp: has_laplace_def)

lemma has_laplaceD:
  assumes "(f has_laplace L) s"
  shows "((\<lambda>t. exp (t *\<^sub>R - s) * f t) has_integral L) {0..}"
  using assms
  by (auto simp: has_laplace_def)

lemma has_laplace_unique:
  "L = M" if
  "(f has_laplace L) s"
  "(f has_laplace M) s"
  using that
  by (auto simp: has_laplace_def has_integral_unique)


subsection \<open>Condition for Existence: Exponential Order\<close>

definition "exponential_order M c f \<longleftrightarrow> 0 < M \<and> (\<forall>\<^sub>F t in at_top. norm (f t) \<le> M * exp (c * t))"

lemma exponential_orderI:
  assumes "0 < M" and eo: "\<forall>\<^sub>F t in at_top. norm (f t) \<le> M * exp (c * t)"
  shows "exponential_order M c f"
  by (auto intro!: assms simp: exponential_order_def)

lemma exponential_orderD:
  assumes "exponential_order M c f"
  shows "0 < M" "\<forall>\<^sub>F t in at_top. norm (f t) \<le> M * exp (c * t)"
  using assms by (auto simp: exponential_order_def)

context
  fixes f::"real \<Rightarrow> complex"
begin

definition laplace_integrand::"complex \<Rightarrow> real \<Rightarrow> complex"
  where "laplace_integrand s t = exp (t *\<^sub>R - s) * f t"

lemma laplace_integrand_absolutely_integrable_on_Icc:
  "laplace_integrand s absolutely_integrable_on {a..b}"
  if "AE x\<in>{a..b} in lebesgue. cmod (f x) \<le> B" "f integrable_on {a..b}"
  apply (cases "b \<le> a")
  subgoal by (auto intro!: absolutely_integrable_onI integrable_negligible[OF negligible_real_ivlI])
proof goal_cases
  case 1
  have "compact ((\<lambda>x. exp (- (x *\<^sub>R s))) ` {a .. b})"
    by (rule compact_continuous_image) (auto intro!: continuous_intros)
  then obtain C where C: "0 \<le> C" "a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> cmod (exp (- (x *\<^sub>R s))) \<le> C" for x
    using 1
    apply (auto simp: bounded_iff dest!: compact_imp_bounded)
    by (metis atLeastAtMost_iff exp_ge_zero order_refl order_trans scaleR_complex.sel(1))

  have m: "(\<lambda>x. indicator {a..b} x *\<^sub>R f x) \<in> borel_measurable lebesgue"
    apply (rule has_integral_implies_lebesgue_measurable)
    apply (rule integrable_integral)
    apply (rule that)
    done
  have "complex_set_integrable lebesgue {a..b} (\<lambda>x. exp (- (x *\<^sub>R s)) * (indicator {a .. b} x *\<^sub>R f x))"
    unfolding set_integrable_def
    apply (rule integrableI_bounded_set_indicator[where B="C * B"])
       apply (simp; fail)
      apply (rule borel_measurable_times)
       apply measurable
        apply (simp add: measurable_completion)
       apply (simp add: measurable_completion)
      apply (rule m)
    apply (simp add: emeasure_lborel_Icc_eq)
    using that(1)
    apply eventually_elim
    apply (auto simp: norm_mult)
    apply (rule mult_mono)
    using C
    by auto
  then show ?case
    unfolding set_integrable_def
    by (simp add: laplace_integrand_def[abs_def] indicator_inter_arith[symmetric])
qed

lemma laplace_integrand_integrable_on_Icc:
  "laplace_integrand s integrable_on {a..b}"
  if "AE x\<in>{a..b} in lebesgue. cmod (f x) \<le> B" "f integrable_on {a..b}"
  using laplace_integrand_absolutely_integrable_on_Icc[OF that]
  using set_lebesgue_integral_eq_integral(1) by blast

lemma eventually_laplace_integrand_le:
  "\<forall>\<^sub>F t in at_top. cmod (laplace_integrand s t) \<le> M * exp (- (Re s - c) * t)"
  if "exponential_order M c f"
  using exponential_orderD(2)[OF that]
proof (eventually_elim)
  case (elim t)
  show ?case
    unfolding laplace_integrand_def
    apply (rule norm_mult_ineq[THEN order_trans])
    apply (auto intro!: mult_left_mono[THEN order_trans, OF elim])
    apply (auto simp: exp_minus divide_simps algebra_simps exp_add[symmetric])
    done
qed

lemma
  assumes eo: "exponential_order M c f"
    and cs: "c < Re s"
  shows laplace_integrand_integrable_on_Ici_iff:
    "laplace_integrand s integrable_on {a..} \<longleftrightarrow>
      (\<forall>k>a. laplace_integrand s integrable_on {a..k})"
    (is ?th1)
  and laplace_integrand_absolutely_integrable_on_Ici_iff:
    "laplace_integrand s absolutely_integrable_on {a..} \<longleftrightarrow>
      (\<forall>k>a. laplace_integrand s absolutely_integrable_on {a..k})"
    (is ?th2)
proof -
  have "\<forall>\<^sub>F t in at_top. a < (t::real)"
    using eventually_gt_at_top by blast
  then have "\<forall>\<^sub>F t in at_top. t > a \<and> cmod (laplace_integrand s t) \<le> M * exp (- (Re s - c) * t)"
    using eventually_laplace_integrand_le[OF eo]
    by eventually_elim (auto)
  then obtain A where A: "A > a" and le: "t \<ge> A \<Longrightarrow> cmod (laplace_integrand s t) \<le> M * exp (- (Re s - c) * t)" for t
    unfolding eventually_at_top_linorder
    by blast

  let ?f = "\<lambda>(k::real) (t::real). indicat_real {A..k} t *\<^sub>R laplace_integrand s t"

  from exponential_orderD[OF eo] have "M \<noteq> 0" by simp
  have 2: "(\<lambda>t. M * exp (- (Re s - c) * t)) integrable_on {A..}"
    unfolding integrable_on_cmult_iff[OF \<open>M \<noteq> 0\<close>] norm_exp_eq_Re
    by (rule integrable_on_exp_minus_to_infinity) (simp add: cs)

  have 3: "t\<in>{A..} \<Longrightarrow> cmod (?f k t) \<le> M * exp (- (Re s - c) * t)"
    (is "t\<in>_\<Longrightarrow> ?lhs t \<le> ?rhs t")
    for t k
  proof safe
    fix t assume "A \<le> t"
    have "?lhs t \<le> cmod (laplace_integrand s t)"
      by (auto simp: indicator_def)
    also have "\<dots> \<le> ?rhs t" using \<open>A \<le> t\<close> le by (simp add: laplace_integrand_def)
    finally show "?lhs t \<le> ?rhs t" .
  qed

  have 4: "\<forall>t\<in>{A..}. ((\<lambda>k. ?f k t) \<longlongrightarrow> laplace_integrand s t) at_top"
  proof safe
    fix t assume t: "t \<ge> A"
    have "\<forall>\<^sub>F k in at_top. k \<ge> t"
      by (simp add: eventually_ge_at_top)
    then have "\<forall>\<^sub>F k in at_top. laplace_integrand s t = ?f k t"
      by eventually_elim (use t in \<open>auto simp: indicator_def\<close>)
    then show "((\<lambda>k. ?f k t) \<longlongrightarrow> laplace_integrand s t) at_top" using tendsto_const
      by (rule Lim_transform_eventually[rotated])
  qed

  show th1: ?th1
  proof safe
    assume "\<forall>k>a. laplace_integrand s integrable_on {a..k}"
    note li = this[rule_format]
    have liA: "laplace_integrand s integrable_on {A..k}" for k
    proof cases
      assume "k \<le> A"
      then have "{A..k} = (if A = k then {k} else {})" by auto
      then show ?thesis by (auto intro!: integrable_negligible)
    next
      assume n: "\<not> k \<le> A"
      show ?thesis
        by (rule integrable_on_subinterval[OF li[of k]]) (use A n in auto)
    qed
    have "?f k integrable_on {A..k}" for k
      using liA[of k] negligible_empty
      by (rule integrable_spike) auto
    then have 1: "?f k integrable_on {A..}" for k
      by (rule integrable_on_superset) auto
    note 1 2 3 4
    note * = this[unfolded set_integrable_def]
    from li[of A] dominated_convergence_at_top(1)[OF *]
    show "laplace_integrand s integrable_on {a..}"
      by (rule integrable_Un') (use \<open>a < A\<close> in \<open>auto simp: max_def li\<close>)
  qed (rule integrable_on_subinterval, assumption, auto)

  show ?th2
  proof safe
    assume ai: "\<forall>k>a. laplace_integrand s absolutely_integrable_on {a..k}"
    then have "laplace_integrand s absolutely_integrable_on {a..A}"
      using A by auto
    moreover
    from ai have "\<forall>k>a. laplace_integrand s integrable_on {a..k}"
      using set_lebesgue_integral_eq_integral(1) by blast
    with th1 have i: "laplace_integrand s integrable_on {a..}" by auto
    have 1: "?f k integrable_on {A..}" for k
      apply (rule integrable_on_superset[where S="{A..k}"])
      using _ negligible_empty
        apply (rule integrable_spike[where f="laplace_integrand s"])
        apply (rule integrable_on_subinterval)
         apply (rule i)
      by (use \<open>a < A\<close> in auto)
    have "laplace_integrand s absolutely_integrable_on {A..}"
      using _ dominated_convergence_at_top(1)[OF 1 2 3 4] 2
      by (rule absolutely_integrable_integrable_bound) (use le in auto)
    ultimately
    have "laplace_integrand s absolutely_integrable_on ({a..A} \<union> {A..})"
      by (rule set_integrable_Un) auto
    also have "{a..A} \<union> {A..} = {a..}" using \<open>a < A\<close> by auto
    finally show "local.laplace_integrand s absolutely_integrable_on {a..}" .
  qed (rule set_integrable_subset, assumption, auto)
qed

theorem laplace_exists_laplace_integrandI:
  assumes "laplace_integrand s integrable_on {0..}"
  obtains F where "(f has_laplace F) s"
proof -
  from assms
  have "(f has_laplace integral {0..} (laplace_integrand s)) s"
    unfolding has_laplace_def laplace_integrand_def by blast
  thus ?thesis ..
qed

lemma
  assumes eo: "exponential_order M c f"
    and pc: "\<And>k. AE x\<in>{0..k} in lebesgue. cmod (f x) \<le> B k" "\<And>k. f integrable_on {0..k}"
    and s: "Re s > c"
  shows laplace_integrand_integrable: "laplace_integrand s integrable_on {0..}" (is ?th1)
    and laplace_integrand_absolutely_integrable:
      "laplace_integrand s absolutely_integrable_on {0..}" (is ?th2)
  using eo laplace_integrand_absolutely_integrable_on_Icc[OF pc] s
  by (auto simp: laplace_integrand_integrable_on_Ici_iff
      laplace_integrand_absolutely_integrable_on_Ici_iff
      set_lebesgue_integral_eq_integral)

lemma piecewise_continuous_on_AE_boundedE:
  assumes pc: "\<And>k. piecewise_continuous_on a k (I k) f"
  obtains B where "\<And>k. AE x\<in>{a..k} in lebesgue. cmod (f x) \<le> B k"
  apply atomize_elim
  apply (rule choice)
  apply (rule allI)
  subgoal for k
    using bounded_piecewise_continuous_image[OF pc[of k]]
    by (force simp: bounded_iff)
  done

theorem piecewise_continuous_on_has_laplace:
  assumes eo: "exponential_order M c f"
    and pc: "\<And>k. piecewise_continuous_on 0 k (I k) f"
    and s: "Re s > c"
  obtains F where "(f has_laplace F) s"
proof -
  from piecewise_continuous_on_AE_boundedE[OF pc]
  obtain B where AE: "AE x\<in>{0..k} in lebesgue. cmod (f x) \<le> B k" for k by force
  have int: "f integrable_on {0..k}" for k
    using pc
    by (rule piecewise_continuous_on_integrable)
  show ?thesis
    using pc
    apply (rule piecewise_continuous_on_AE_boundedE)
    apply (rule laplace_exists_laplace_integrandI)
     apply (rule laplace_integrand_integrable)
        apply (rule eo)
       apply assumption
      apply (rule int)
     apply (rule s)
    by (rule that)
qed

end


subsection \<open>Concrete Laplace Transforms\<close>

lemma exp_scaleR_has_vector_derivative_left'[derivative_intros]:
  "((\<lambda>t. exp (t *\<^sub>R A)) has_vector_derivative A * exp (t *\<^sub>R A)) (at t within S)"
  by (metis exp_scaleR_has_vector_derivative_right exp_times_scaleR_commute)

lemma
  fixes a::complex\<comment>\<open>TODO: generalize\<close>
  assumes a: "0 < Re a"
  shows integrable_on_cexp_minus_to_infinity: "(\<lambda>x. exp (x *\<^sub>R - a)) integrable_on {c..}"
    and integral_cexp_minus_to_infinity:  "integral {c..} (\<lambda>x. exp (x *\<^sub>R - a)) = exp (c *\<^sub>R - a) / a"
proof -
  from a have "a \<noteq> 0" by auto
  define f where "f = (\<lambda>k x. if x \<in> {c..real k} then exp (x *\<^sub>R -a) else 0)"
  {
    fix k :: nat assume k: "of_nat k \<ge> c"
    from \<open>a \<noteq> 0\<close> k
      have "((\<lambda>x. exp (x *\<^sub>R -a)) has_integral (-exp (k *\<^sub>R -a)/a - (-exp (c *\<^sub>R -a)/a))) {c..real k}"
      by (intro fundamental_theorem_of_calculus)
         (auto intro!: derivative_eq_intros exp_scaleR_has_vector_derivative_left
            simp: divide_inverse_commute
               simp del: scaleR_minus_left scaleR_minus_right)
    hence "(f k has_integral (exp (c *\<^sub>R -a)/a - exp (k *\<^sub>R -a)/a)) {c..}" unfolding f_def
      by (subst has_integral_restrict) simp_all
  } note has_integral_f = this

  have integrable_fk: "f k integrable_on {c..}" for k
  proof -
    have "(\<lambda>x. exp (x *\<^sub>R -a)) integrable_on {c..of_real k}" (is ?P)
      unfolding f_def by (auto intro!: continuous_intros integrable_continuous_real)
    then have int: "(f k) integrable_on {c..of_real k}"
      by (rule integrable_eq) (simp add: f_def)
    show ?thesis
      by (rule integrable_on_superset[OF int]) (auto simp: f_def)
  qed
  have limseq: "\<And>x. x \<in>{c..} \<Longrightarrow> (\<lambda>k. f k x) \<longlonglongrightarrow> exp (x *\<^sub>R - a)"
    apply (auto intro!: Lim_transform_eventually[OF tendsto_const] simp: f_def)
    by (meson eventually_sequentiallyI nat_ceiling_le_eq)
  have bnd: "\<And>x. x \<in> {c..} \<Longrightarrow> cmod (f k x) \<le> exp (- Re a * x)" for k
    by (auto simp: f_def)

  have [simp]: "f k = (\<lambda>_. 0)" if "of_nat k < c" for k using that by (auto simp: fun_eq_iff f_def)
  have integral_f: "integral {c..} (f k) =
                      (if real k \<ge> c then exp (c *\<^sub>R -a)/a - exp (k *\<^sub>R -a)/a else 0)"
    for k using integral_unique[OF has_integral_f[of k]] by simp

  have "(\<lambda>k. exp (c *\<^sub>R -a)/a - exp (k *\<^sub>R -a)/a) \<longlonglongrightarrow> exp (c*\<^sub>R-a)/a - 0/a"
    apply (intro tendsto_intros filterlim_compose[OF exp_at_bot]
          filterlim_tendsto_neg_mult_at_bot[OF tendsto_const] filterlim_real_sequentially)+
     apply (rule tendsto_norm_zero_cancel)
    by (auto intro!: assms \<open>a \<noteq> 0\<close> filterlim_real_sequentially
        filterlim_compose[OF exp_at_bot] filterlim_compose[OF filterlim_uminus_at_bot_at_top]
        filterlim_at_top_mult_tendsto_pos[OF tendsto_const])
  moreover
  note A = dominated_convergence[where g="\<lambda>x. exp (x *\<^sub>R -a)",
    OF integrable_fk integrable_on_exp_minus_to_infinity[where a="Re a" and c=c, OF \<open>0 < Re a\<close>]
      bnd limseq]
  from A(1) show "(\<lambda>x. exp (x *\<^sub>R - a)) integrable_on {c..}" .
  from eventually_gt_at_top[of "nat \<lceil>c\<rceil>"] have "eventually (\<lambda>k. of_nat k > c) sequentially"
    by eventually_elim linarith
  hence "eventually (\<lambda>k. exp (c *\<^sub>R -a)/a - exp (k *\<^sub>R -a)/a = integral {c..} (f k)) sequentially"
    by eventually_elim (simp add: integral_f)
  ultimately have "(\<lambda>k. integral {c..} (f k)) \<longlonglongrightarrow> exp (c *\<^sub>R -a)/a - 0/a"
    by (rule Lim_transform_eventually)
  from LIMSEQ_unique[OF A(2) this]
  show "integral {c..} (\<lambda>x. exp (x *\<^sub>R -a)) = exp (c *\<^sub>R -a)/a" by simp
qed

lemma has_integral_cexp_minus_to_infinity:
  fixes a::complex\<comment>\<open>TODO: generalize\<close>
  assumes a: "0 < Re a"
  shows "((\<lambda>x. exp (x *\<^sub>R - a)) has_integral exp (c *\<^sub>R - a) / a) {c..}"
  using integral_cexp_minus_to_infinity[OF assms]
    integrable_on_cexp_minus_to_infinity[OF assms]
  using has_integral_integrable_integral by blast

lemma has_laplace_one:
  "((\<lambda>_. 1) has_laplace inverse s) s" if "Re s > 0"
proof (safe intro!: has_laplaceI)
  from that have "((\<lambda>t. exp (t *\<^sub>R - s)) has_integral inverse s) {0..}"
    by (rule has_integral_cexp_minus_to_infinity[THEN has_integral_eq_rhs])
       (auto simp: inverse_eq_divide)
  then show "((\<lambda>t. exp (t *\<^sub>R - s) * 1) has_integral inverse s) {0..}" by simp
qed

lemma has_laplace_add:
  assumes f: "(f has_laplace F) S"
  assumes g: "(g has_laplace G) S"
  shows "((\<lambda>x. f x + g x) has_laplace F + G) S"
  apply (rule has_laplaceI)
  using has_integral_add[OF has_laplaceD[OF f ] has_laplaceD[OF g]]
  by (auto simp: algebra_simps)

lemma has_laplace_cmul:
  assumes "(f has_laplace F) S"
  shows "((\<lambda>x. r *\<^sub>R f x) has_laplace r *\<^sub>R F) S"
  apply (rule has_laplaceI)
  using has_laplaceD[OF assms, THEN has_integral_cmul[where c=r]]
  by auto

lemma has_laplace_uminus:
  assumes "(f has_laplace F) S"
  shows "((\<lambda>x. - f x) has_laplace - F) S"
  using has_laplace_cmul[OF assms, of "-1"]
  by auto

lemma has_laplace_minus:
  assumes f: "(f has_laplace F) S"
  assumes g: "(g has_laplace G) S"
  shows "((\<lambda>x. f x - g x) has_laplace F - G) S"
  using has_laplace_add[OF f has_laplace_uminus[OF g]]
  by simp

lemma has_laplace_spike:
  "(f has_laplace L) s"
  if L: "(g has_laplace L) s"
    and "negligible T"
    and "\<And>t. t \<notin> T \<Longrightarrow> t \<ge> 0 \<Longrightarrow> f t = g t"
  by (auto intro!: has_laplaceI has_integral_spike[where S="T", OF _ _ has_laplaceD[OF L]] that)


lemma has_laplace_frequency_shift:\<comment>\<open>First Translation Theorem in Schiff\<close>
  "((\<lambda>t. exp (t *\<^sub>R b) * f t) has_laplace L) s"
  if "(f has_laplace L) (s - b)"
  using that
  by (auto intro!: has_laplaceI dest!: has_laplaceD
      simp: mult_exp_exp algebra_simps)

theorem has_laplace_derivative_time_domain:
  "(f' has_laplace s * L - f0) s"
  if L: "(f has_laplace L) s"
    and f': "\<And>t. t > 0 \<Longrightarrow> (f has_vector_derivative f' t) (at t)"
    and f0: "(f \<longlongrightarrow> f0) (at_right 0)"
    and eo: "exponential_order M c f"
    and cs: "c < Re s"
    \<comment>\<open>Proof and statement follow "The Laplace Transform: Theory and Applications" by Joel L. Schiff.\<close>
proof (rule has_laplaceI)
  have ce: "continuous_on S (\<lambda>t. exp (t *\<^sub>R - s))" for S
    by (auto intro!: continuous_intros)
  have de: "((\<lambda>t. exp (t *\<^sub>R - s)) has_vector_derivative (- s * exp (- (t *\<^sub>R s)))) (at t)" for t
    by (auto simp: has_vector_derivative_def intro!: derivative_eq_intros ext)
  have "((\<lambda>x. -s * (f x * exp (- (x *\<^sub>R s)))) has_integral - s * L) {0..}"
    apply (rule has_integral_mult_right)
    using has_laplaceD[OF L]
    by (auto simp: ac_simps)

  define g where "g x = (if x \<le> 0 then f0 else f x)" for x

  have eog: "exponential_order M c g"
  proof -
    from exponential_orderD[OF eo] have "0 < M"
      and ev: "\<forall>\<^sub>F t in at_top. cmod (f t) \<le> M * exp (c * t)" .
    have "\<forall>\<^sub>F t::real in at_top. t > 0" by simp
    with ev have "\<forall>\<^sub>F t in at_top. cmod (g t) \<le> M * exp (c * t)"
      by eventually_elim (auto simp: g_def)
    with \<open>0 < M\<close> show ?thesis
      by (rule exponential_orderI)
  qed
  have Lg: "(g has_laplace L) s"
    using L
    by (rule has_laplace_spike[where T="{0}"]) (auto simp: g_def)
  have g': "\<And>t. 0 < t \<Longrightarrow> (g has_vector_derivative f' t) (at t)"
    using f'
    by (rule has_vector_derivative_transform_within_open[where S="{0<..}"]) (auto simp: g_def)
  have cg: "continuous_on {0..k} g" for k
    apply (auto simp: g_def continuous_on_def)
     apply (rule filterlim_at_within_If)
    subgoal by (rule tendsto_intros)
    subgoal
      apply (rule tendsto_within_subset)
       apply (rule f0)
      by auto
    subgoal premises prems for x
    proof -
      from prems have "0 < x" by auto
      from order_tendstoD[OF tendsto_ident_at this]
      have "eventually ((<) 0) (at x within {0..k})" by auto
      then have "\<forall>\<^sub>F x in at x within {0..k}. f x = (if x \<le> 0 then f0 else f x)"
        by eventually_elim auto
      moreover
      note [simp] = at_within_open[where S="{0<..}"]
      have "continuous_on {0<..} f"
        by (rule continuous_on_vector_derivative)
          (auto simp add: intro!: f')
      then have "(f \<longlongrightarrow> f x) (at x within {0..k})"
        using \<open>0 < x\<close>
        by (auto simp: continuous_on_def intro: Lim_at_imp_Lim_at_within)
      ultimately show ?thesis
        by (rule Lim_transform_eventually[rotated])
    qed
    done
  then have pcg: "piecewise_continuous_on 0 k {} g" for k
    by (auto simp: piecewise_continuous_on_def)
  from piecewise_continuous_on_AE_boundedE[OF this]
  obtain B where B: "AE x\<in>{0..k} in lebesgue. cmod (g x) \<le> B k" for k by auto
  have 1: "laplace_integrand g s absolutely_integrable_on {0..}"
    apply (rule laplace_integrand_absolutely_integrable[OF eog])
      apply (rule B)
     apply (rule piecewise_continuous_on_integrable)
     apply (rule pcg)
    apply (rule cs)
    done
  then have csi: "complex_set_integrable lebesgue {0..} (\<lambda>x. exp (x *\<^sub>R - s) * g x)"
    by (auto simp: laplace_integrand_def[abs_def])
  from has_laplaceD[OF Lg, THEN has_integral_improperE, OF csi]
  obtain J where J: "\<And>k. ((\<lambda>t. exp (t *\<^sub>R - s) * g t) has_integral J k) {0..k}"
    and [tendsto_intros]: "(J \<longlongrightarrow> L) at_top"
    by auto
  have "((\<lambda>x. -s * (exp (x *\<^sub>R - s) * g x)) has_integral -s * J k) {0..k}" for k
    by (rule has_integral_mult_right) (rule J)
  then have *: "((\<lambda>x. g x * (- s * exp (- (x *\<^sub>R s)))) has_integral -s * J k) {0..k}" for k
    by (auto simp: algebra_simps)
  have "\<forall>\<^sub>F k::real in at_top. k \<ge> 0"
    using eventually_ge_at_top by blast
  then have evI: "\<forall>\<^sub>F k in at_top. ((\<lambda>t. exp (t *\<^sub>R - s) * f' t) has_integral
    g k * exp (k *\<^sub>R - s) + s * J k - g 0) {0..k}"
  proof eventually_elim
    case (elim k)
    show ?case
      apply (subst mult.commute)
      apply (rule integration_by_parts_interior[OF bounded_bilinear_mult], fact)
      apply (rule cg) apply (rule ce) apply (rule g') apply force apply (rule de)
      apply (rule has_integral_eq_rhs)
       apply (rule *)
      by (auto simp: )
  qed
  have t1: "((\<lambda>x. g x * exp (x *\<^sub>R - s)) \<longlongrightarrow> 0) at_top"
    apply (subst mult.commute)
    unfolding laplace_integrand_def[symmetric]
    apply (rule Lim_null_comparison)
    apply (rule eventually_laplace_integrand_le[OF eog])
    apply (rule tendsto_mult_right_zero)
    apply (rule filterlim_compose[OF exp_at_bot])
    apply (rule filterlim_tendsto_neg_mult_at_bot)
      apply (rule tendsto_intros)
    using cs apply simp
    apply (rule filterlim_ident)
    done
  show "((\<lambda>t. exp (t *\<^sub>R - s) * f' t) has_integral s * L - f0) {0..}"
    apply (rule has_integral_improper_at_topI[OF evI])
    subgoal
      apply (rule tendsto_eq_intros)
       apply (rule tendsto_intros)
        apply (rule t1)
       apply (rule tendsto_intros)
        apply (rule tendsto_intros)
       apply (rule tendsto_intros)
       apply (rule tendsto_intros)
      by (simp add: g_def)
    done
qed

lemma exp_times_has_integral:
  "((\<lambda>t. exp (c * t)) has_integral (if c = 0 then t else exp (c * t) / c) - (if c = 0 then t0 else exp (c * t0) / c)) {t0 .. t}"
  if "t0 \<le> t"
  for c t::real
  apply (cases "c = 0")
  subgoal
    using that
    apply auto
    apply (rule has_integral_eq_rhs)
     apply (rule has_integral_const_real)
    by auto
  subgoal
    apply (rule fundamental_theorem_of_calculus)
    using that
    by (auto simp: has_vector_derivative_def intro!: derivative_eq_intros)
  done

lemma integral_exp_times:
  "integral {t0 .. t} (\<lambda>t. exp (c * t)) = (if c = 0 then t - t0 else exp (c * t) / c - exp (c * t0) / c)"
  if "t0 \<le> t"
  for c t::real
  using exp_times_has_integral[OF that, of c] that
  by (auto split: if_splits)

lemma filtermap_times_pos_at_top: "filtermap ((*) e) at_top = at_top"
  if "e > 0"
  for e::real
  apply (rule filtermap_fun_inverse[of "(*) (inverse e)"])
    apply (rule filterlim_tendsto_pos_mult_at_top)
      apply (rule tendsto_intros)
  subgoal using that by simp
    apply (rule filterlim_ident)
    apply (rule filterlim_tendsto_pos_mult_at_top)
      apply (rule tendsto_intros)
  subgoal using that by simp
   apply (rule filterlim_ident)
  using that by auto

lemma exponential_order_additiveI:
  assumes "0 < M" and eo: "\<forall>\<^sub>F t in at_top. norm (f t) \<le> K + M * exp (c * t)" and "c \<ge> 0"
  obtains M' where "exponential_order M' c f"
proof -
  consider "c = 0" | "c > 0" using \<open>c \<ge> 0\<close> by arith
  then show ?thesis
  proof cases
    assume "c = 0"
    have "exponential_order (max K 0 + M) c f"
      using eo
       apply (auto intro!: exponential_orderI add_nonneg_pos \<open>0 < M\<close> simp: \<open>c = 0\<close>)
      apply (auto simp: max_def)
      using eventually_elim2 by force
    then show ?thesis ..
  next
    assume "c > 0"
    have "\<forall>\<^sub>F t in at_top. norm (f t) \<le> K + M * exp (c * t)"
      by fact
    moreover
    have "\<forall>\<^sub>F t in (filtermap exp (filtermap ((*) c) at_top)). K < t"
      by (simp add: filtermap_times_pos_at_top \<open>c > 0\<close> filtermap_exp_at_top)
    then have "\<forall>\<^sub>F t in at_top. K < exp (c * t)"
      by (simp add: eventually_filtermap)
    ultimately
    have "\<forall>\<^sub>F t in at_top. norm (f t) \<le> (1 + M) * exp (c * t)"
      by eventually_elim (auto simp: algebra_simps)
    with add_nonneg_pos[OF zero_le_one \<open>0 < M\<close>]
    have "exponential_order (1 + M) c f"
      by (rule exponential_orderI)
    then show ?thesis ..
  qed
qed

lemma exponential_order_integral:
  fixes f::"real \<Rightarrow> 'a::banach"
  assumes I: "\<And>t. t \<ge> a \<Longrightarrow> (f has_integral I t) {a .. t}"
    and eo: "exponential_order M c f"
    and "c > 0"
  obtains M' where "exponential_order M' c I"
proof -
  from exponential_orderD[OF eo] have "0 < M"
    and bound: "\<forall>\<^sub>F t in at_top. norm (f t) \<le> M * exp (c * t)"
    by auto
  have "\<forall>\<^sub>F t in at_top. t > a"
    by simp
  from bound this
  have "\<forall>\<^sub>F t in at_top. norm (f t) \<le> M * exp (c * t) \<and> t > a"
    by eventually_elim auto
  then obtain t0 where t0: "\<And>t. t \<ge> t0 \<Longrightarrow> norm (f t) \<le> M * exp (c * t)" "t0 > a"
    by (auto simp: eventually_at_top_linorder)
  have "\<forall>\<^sub>F t in at_top. t > t0" by simp
  then have "\<forall>\<^sub>F t in at_top. norm (I t) \<le> norm (integral {a..t0} f) - M * exp (c * t0) / c + (M / c) * exp (c * t)"
  proof eventually_elim
    case (elim t) then have that: "t \<ge> t0" by simp
    from t0 have "a \<le> t0" by simp
    have "f integrable_on {a .. t0}" "f integrable_on {t0 .. t}"
      subgoal by (rule has_integral_integrable[OF I[OF \<open>a \<le> t0\<close>]])
      subgoal
        apply (rule integrable_on_subinterval[OF has_integral_integrable[OF I[where t=t]]])
        using \<open>t0 > a\<close> that by auto
      done
    have "I t = integral {a .. t0} f + integral {t0 .. t} f"
      by (smt I \<open>a \<le> t0\<close> \<open>f integrable_on {t0..t}\<close> has_integral_combine has_integral_integrable_integral that)
    also have "norm \<dots> \<le> norm (integral {a .. t0} f) + norm (integral {t0 .. t} f)" by norm
    also
    have "norm (integral {t0 .. t} f) \<le> integral {t0 .. t} (\<lambda>t. M * exp (c * t))"
      apply (rule integral_norm_bound_integral)
        apply fact
      by (auto intro!: integrable_continuous_interval continuous_intros t0)
    also have "\<dots> = M * integral {t0 .. t} (\<lambda>t. exp (c * t))"
      by simp
    also have "integral {t0 .. t} (\<lambda>t. exp (c * t)) = exp (c * t) / c - exp (c * t0) / c"
      using \<open>c > 0\<close> \<open>t0 \<le> t\<close>
      by (subst integral_exp_times) auto
    finally show ?case
      using \<open>c > 0\<close>
      by (auto simp: algebra_simps)
  qed
  from exponential_order_additiveI[OF divide_pos_pos[OF \<open>0 < M\<close> \<open>0 < c\<close>] this less_imp_le[OF \<open>0 < c\<close>]]
  obtain M' where "exponential_order M' c I" .
  then show ?thesis ..
qed

lemma integral_has_vector_derivative_piecewise_continuous:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"\<comment>\<open>TODO: generalize?\<close>
  assumes "piecewise_continuous_on a b D f"
  shows "\<And>x. x \<in> {a .. b} - D \<Longrightarrow>
    ((\<lambda>u. integral {a..u} f) has_vector_derivative f(x)) (at x within {a..b} - D)"
  using assms
proof (induction a b D f rule: piecewise_continuous_on_induct)
  case (empty a b f)
  then show ?case
    by (auto intro: integral_has_vector_derivative)
next
  case (combine a i b I f1 f2 f)
  then consider "x < i" | "i < x" by auto arith

  then show ?case
  proof cases\<comment>\<open>TODO: this is very explicit...\<close>
    case 1
    have evless: "\<forall>\<^sub>F xa in nhds x. xa < i"
      apply (rule order_tendstoD[OF _ \<open>x < i\<close>])
      by (simp add: filterlim_ident)
    have eq: "at x within {a..b} - insert i I = at x within {a .. i} - I"
      unfolding filter_eq_iff
    proof safe
      fix P
      assume "eventually P (at x within {a..i} - I)"
      with evless show "eventually P (at x within {a..b} - insert i I)"
        unfolding eventually_at_filter
        by eventually_elim auto
    next
      fix P
      assume "eventually P (at x within {a..b} - insert i I)"
      with evless show "eventually P (at x within {a..i} - I)"
        unfolding eventually_at_filter
        apply eventually_elim
        using 1 combine
        by auto
    qed
    have "f x = f1 x" using combine 1 by auto
    have i_eq: "integral {a..y} f = integral {a..y} f1" if "y < i" for y
      using negligible_empty
      apply (rule integral_spike)
      using combine 1 that
      by auto
    from evless have ev_eq: "\<forall>\<^sub>F x in nhds x. x \<in> {a..i} - I \<longrightarrow> integral {a..x} f = integral {a..x} f1"
      by eventually_elim (auto simp: i_eq)
    show ?thesis unfolding eq \<open>f x = f1 x\<close>
      apply (subst has_vector_derivative_cong_ev[OF ev_eq])
      using combine.IH[of x]
      using combine.hyps combine.prems 1
      by (auto simp: i_eq)
  next
    case 2
    have evless: "\<forall>\<^sub>F xa in nhds x. xa > i"
      apply (rule order_tendstoD[OF _ \<open>x > i\<close>])
      by (simp add: filterlim_ident)
    have eq: "at x within {a..b} - insert i I = at x within {i .. b} - I"
      unfolding filter_eq_iff
    proof safe
      fix P
      assume "eventually P (at x within {i..b} - I)"
      with evless show "eventually P (at x within {a..b} - insert i I)"
        unfolding eventually_at_filter
        by eventually_elim auto
    next
      fix P
      assume "eventually P (at x within {a..b} - insert i I)"
      with evless show "eventually P (at x within {i..b} - I)"
        unfolding eventually_at_filter
        apply eventually_elim
        using 2 combine
        by auto
    qed
    have "f x = f2 x" using combine 2 by auto
    have i_eq: "integral {a..y} f = integral {a..i} f + integral {i..y} f2" if "i < y" "y \<le> b" for y
    proof -
      have "integral {a..y} f = integral {a..i} f + integral {i..y} f"
        apply (cases "i = y")
        subgoal by auto
        subgoal
          apply (rule Henstock_Kurzweil_Integration.integral_combine[symmetric])
          using combine that apply auto
          apply (rule integrable_Un'[where A="{a .. i}" and B="{i..y}"])
          subgoal
            by (rule integrable_spike[where S="{i}" and f="f1"])
              (auto intro: piecewise_continuous_on_integrable)
          subgoal
            apply (rule integrable_on_subinterval[where S="{i..b}"])
            by (rule integrable_spike[where S="{i}" and f="f2"])
              (auto intro: piecewise_continuous_on_integrable)
          subgoal by (auto simp: max_def min_def)
          subgoal by auto
          done
        done
      also have "integral {i..y} f = integral {i..y} f2"
        apply (rule integral_spike[where S="{i}"])
        using combine 2 that
        by auto
      finally show ?thesis .
    qed
    from evless have ev_eq: "\<forall>\<^sub>F y in nhds x. y \<in> {i..b} - I \<longrightarrow> integral {a..y} f = integral {a..i} f + integral {i..y} f2"
      by eventually_elim (auto simp: i_eq)
    show ?thesis unfolding eq
      apply (subst has_vector_derivative_cong_ev[OF ev_eq])
      using combine.IH[of x] combine.prems combine.hyps 2
      by (auto simp: i_eq intro!: derivative_eq_intros)
  qed
qed (auto intro: has_vector_derivative_within_subset)

lemma has_derivative_at_split:
  "(f has_derivative f') (at x) \<longleftrightarrow> (f has_derivative f') (at_left x) \<and> (f has_derivative f') (at_right x)"
  for x::"'a::{linorder_topology, real_normed_vector}"
  by (auto simp: has_derivative_at_within filterlim_at_split)

lemma has_vector_derivative_at_split:
  "(f has_vector_derivative f') (at x) \<longleftrightarrow>
   (f has_vector_derivative f') (at_left x) \<and>
   (f has_vector_derivative f') (at_right x)"
  using has_derivative_at_split[of f "\<lambda>h. h *\<^sub>R f'" x]
  by (simp add: has_vector_derivative_def)

lemmas differentiableI_vector[intro]

lemma differentiable_at_splitD:
  "f differentiable at_left x"
  "f differentiable at_right x"
  if "f differentiable (at x)"
  for x::real
  using that[unfolded vector_derivative_works has_vector_derivative_at_split]
  by auto

lemma integral_differentiable:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a..b} f"
    and "x \<in> {a..b}"
  shows "(\<lambda>u. integral {a..u} f) differentiable at x within {a..b}"
  using integral_has_vector_derivative[OF assms]
  by blast

theorem integral_has_vector_derivative_piecewise_continuous':
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"\<comment>\<open>TODO: generalize?\<close>
  assumes "piecewise_continuous_on a b D f" "a < b"
  shows
    "(\<forall>x. a < x \<longrightarrow> x < b \<longrightarrow> x \<notin> D \<longrightarrow> (\<lambda>u. integral {a..u} f) differentiable at x) \<and>
    (\<forall>x. a \<le> x \<longrightarrow> x < b \<longrightarrow> (\<lambda>t. integral {a..t} f) differentiable at_right x) \<and>
    (\<forall>x. a < x \<longrightarrow> x \<le> b \<longrightarrow> (\<lambda>t. integral {a..t} f) differentiable at_left x)"
  using assms
proof (induction a b D f rule: piecewise_continuous_on_induct)
  case (empty a b f)
  have "a < x \<Longrightarrow> x < b \<Longrightarrow> (\<lambda>u. integral {a..u} f) differentiable (at x)" for x
    using integral_differentiable[OF empty(1), of x]
    by (auto simp: at_within_interior)
  then show ?case
    using integral_differentiable[OF empty(1), of a]
      integral_differentiable[OF empty(1), of b]
      \<open>a < b\<close>
    by (auto simp: at_within_Icc_at_right at_within_Icc_at_left le_less
        intro: differentiable_at_withinI)
next
  case (combine a i b I f1 f2 f)
  from \<open>piecewise_continuous_on a i I f1\<close> have "finite I"
    by (auto elim!: piecewise_continuous_onE)

  from combine(4) have "piecewise_continuous_on a i (insert i I) f1"
    by (rule piecewise_continuous_on_insert_rightI)
  then have "piecewise_continuous_on a i (insert i I) f"
    by (rule piecewise_continuous_on_congI) (auto simp: combine)
  moreover
  from combine(5) have "piecewise_continuous_on i b (insert i I) f2"
    by (rule piecewise_continuous_on_insert_leftI)
  then have "piecewise_continuous_on i b (insert i I) f"
    by (rule piecewise_continuous_on_congI) (auto simp: combine)
  ultimately have "piecewise_continuous_on a b (insert i I) f"
    by (rule piecewise_continuous_on_combine)
  then have f_int: "f integrable_on {a .. b}"
    by (rule piecewise_continuous_on_integrable)

  from combine.IH
  have f1: "x>a \<Longrightarrow> x < i \<Longrightarrow> x \<notin> I \<Longrightarrow> (\<lambda>u. integral {a..u} f1) differentiable (at x)"
    "x\<ge>a \<Longrightarrow> x < i \<Longrightarrow> (\<lambda>t. integral {a..t} f1) differentiable (at_right x)"
    "x>a \<Longrightarrow> x \<le> i \<Longrightarrow> (\<lambda>t. integral {a..t} f1) differentiable (at_left x)"
   and f2: "x>i \<Longrightarrow> x < b \<Longrightarrow> x \<notin> I \<Longrightarrow> (\<lambda>u. integral {i..u} f2) differentiable (at x)"
    "x\<ge>i \<Longrightarrow> x < b \<Longrightarrow> (\<lambda>t. integral {i..t} f2) differentiable (at_right x)"
    "x>i \<Longrightarrow> x \<le> b \<Longrightarrow> (\<lambda>t. integral {i..t} f2) differentiable (at_left x)"
    for x
    by auto

  have "(\<lambda>u. integral {a..u} f) differentiable at x" if "a < x" "x < b" "x \<noteq> i" "x \<notin> I" for x
  proof -
    from that consider "x < i" |"i < x" by arith
    then show ?thesis
    proof cases
      case 1
      have at: "at x within {a<..<i} - I = at x"
        using that 1
        by (intro at_within_open) (auto intro!: open_Diff finite_imp_closed \<open>finite I\<close>)
      then have "(\<lambda>u. integral {a..u} f1) differentiable at x within {a<..<i} - I"
        using that 1 f1 by auto
      then have "(\<lambda>u. integral {a..u} f) differentiable at x within {a<..<i} - I"
        apply (rule differentiable_transform_within[OF _ zero_less_one])
        using that combine.hyps 1 by (auto intro!: integral_cong)
      then show ?thesis by (simp add: at)
    next
      case 2
      have at: "at x within {i<..<b} - I = at x"
        using that 2
        by (intro at_within_open) (auto intro!: open_Diff finite_imp_closed \<open>finite I\<close>)
      then have "(\<lambda>u. integral {a..i} f + integral {i..u} f2) differentiable at x within {i<..<b} - I"
        using that 2 f2 by auto
      then have "(\<lambda>u. integral {a..i} f + integral {i..u} f) differentiable at x within {i<..<b} - I"
        apply (rule differentiable_transform_within[OF _ zero_less_one])
        using that combine.hyps 2 by (auto intro!: integral_spike[where S="{i,x}"])
      then have "(\<lambda>u. integral {a..u} f) differentiable at x within {i<..<b} - I"
        apply (rule differentiable_transform_within[OF _ zero_less_one])
        subgoal using that 2 by auto
        apply (auto simp: )
        apply (subst Henstock_Kurzweil_Integration.integral_combine)
        using that 2 \<open>a \<le> i\<close>
        apply auto
        by (auto intro: integrable_on_subinterval f_int)
      then show ?thesis by (simp add: at)
    qed
  qed
  moreover
  have "(\<lambda>t. integral {a..t} f) differentiable at_right x" if "a \<le> x" "x < b" for x
  proof -
    from that consider "x < i" |"i \<le> x" by arith
    then show ?thesis
    proof cases
      case 1
      have at: "at x within {x..i} = at_right x"
        using \<open>x < i\<close> by (rule at_within_Icc_at_right)
      then have "(\<lambda>u. integral {a..u} f1) differentiable at x within {x..i}"
        using that 1 f1 by auto
      then have "(\<lambda>u. integral {a..u} f) differentiable at x within {x..i}"
        apply (rule differentiable_transform_within[OF _ zero_less_one])
        using that combine.hyps 1 by (auto intro!: integral_spike[where S="{i,x}"])
      then show ?thesis by (simp add: at)
    next
      case 2
      have at: "at x within {x..b} = at_right x"
        using \<open>x < b\<close> by (rule at_within_Icc_at_right)
      then have "(\<lambda>u. integral {a..i} f + integral {i..u} f2) differentiable at x within {x..b}"
        using that 2 f2 by auto
      then have "(\<lambda>u. integral {a..i} f + integral {i..u} f) differentiable at x within {x..b}"
        apply (rule differentiable_transform_within[OF _ zero_less_one])
        using that combine.hyps 2 by (auto intro!: integral_spike[where S="{i,x}"])
      then have "(\<lambda>u. integral {a..u} f) differentiable at x within {x..b}"
        apply (rule differentiable_transform_within[OF _ zero_less_one])
        subgoal using that 2 by auto
        apply (auto simp: )
        apply (subst Henstock_Kurzweil_Integration.integral_combine)
        using that 2 \<open>a \<le> i\<close>
        apply auto
        by (auto intro: integrable_on_subinterval f_int)
      then show ?thesis by (simp add: at)
    qed
  qed
  moreover
  have "(\<lambda>t. integral {a..t} f) differentiable at_left x" if "a < x" "x \<le> b" for x
  proof -
    from that consider "x \<le> i" |"i < x" by arith
    then show ?thesis
    proof cases
      case 1
      have at: "at x within {a..x} = at_left x"
        using \<open>a < x\<close> by (rule at_within_Icc_at_left)
      then have "(\<lambda>u. integral {a..u} f1) differentiable at x within {a..x}"
        using that 1 f1 by auto
      then have "(\<lambda>u. integral {a..u} f) differentiable at x within {a..x}"
        apply (rule differentiable_transform_within[OF _ zero_less_one])
        using that combine.hyps 1 by (auto intro!: integral_spike[where S="{i,x}"])
      then show ?thesis by (simp add: at)
    next
      case 2
      have at: "at x within {i..x} = at_left x"
        using \<open>i < x\<close> by (rule at_within_Icc_at_left)
      then have "(\<lambda>u. integral {a..i} f + integral {i..u} f2) differentiable at x within {i..x}"
        using that 2 f2 by auto
      then have "(\<lambda>u. integral {a..i} f + integral {i..u} f) differentiable at x within {i..x}"
        apply (rule differentiable_transform_within[OF _ zero_less_one])
        using that combine.hyps 2 by (auto intro!: integral_spike[where S="{i,x}"])
      then have "(\<lambda>u. integral {a..u} f) differentiable at x within {i..x}"
        apply (rule differentiable_transform_within[OF _ zero_less_one])
        subgoal using that 2 by auto
        apply (auto simp: )
        apply (subst Henstock_Kurzweil_Integration.integral_combine)
        using that 2 \<open>a \<le> i\<close>
        apply auto
        by (auto intro: integrable_on_subinterval f_int)
      then show ?thesis by (simp add: at)
    qed
  qed
  ultimately
  show ?case
    by auto
next
  case (weaken a b i I f)
  from weaken.IH[OF \<open>a < b\<close>]
  obtain l u where IH:
    "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> x \<notin> I \<Longrightarrow> (\<lambda>u. integral {a..u} f) differentiable (at x)"
    "\<And>x. a \<le> x \<Longrightarrow> x < b \<Longrightarrow> (\<lambda>t. integral {a..t} f) differentiable (at_right x)"
    "\<And>x. a < x \<Longrightarrow> x \<le> b \<Longrightarrow> (\<lambda>t. integral {a..t} f) differentiable (at_left x)"
    by metis
  then show ?case by auto
qed

lemma "closure (-S) \<inter> closure S = frontier S"
  by (auto simp add: frontier_def closure_complement)

theorem integral_time_domain_has_laplace:
  "((\<lambda>t. integral {0 .. t} f) has_laplace L / s) s"
  if pc: "\<And>k. piecewise_continuous_on 0 k D f"
    and eo: "exponential_order M c f"
    and L: "(f has_laplace L) s"
    and s: "Re s > c"
    and c: "c > 0"
    and TODO: "D = {}" \<comment> \<open>TODO: generalize to actual \<open>piecewise_continuous_on\<close>\<close>
  for f::"real \<Rightarrow> complex"
proof -
  define I where "I = (\<lambda>t. integral {0 .. t} f)"
  have I': "(I has_vector_derivative f t) (at t within {0..x} - D)"
    if "t \<in> {0 .. x} - D"
    for x t
    unfolding I_def
    by (rule integral_has_vector_derivative_piecewise_continuous; fact)
  have fi: "f integrable_on {0..t}" for t
    by (rule piecewise_continuous_on_integrable) fact
  have Ic: "continuous_on {0 .. t} I" for t
    unfolding I_def using fi
    by (rule indefinite_integral_continuous_1)
  have Ipc: "piecewise_continuous_on 0 t {} I" for t
    by (rule piecewise_continuous_onI) (auto intro!: Ic)
  have I: "(f has_integral I t) {0 .. t}" for t
    unfolding I_def
    using fi
    by (rule integrable_integral)
  from exponential_order_integral[OF I eo \<open>0 < c\<close>] obtain M'
    where Ieo: "exponential_order M' c I" .
  have Ili: "laplace_integrand I s integrable_on {0..}"
    using Ipc
    apply (rule piecewise_continuous_on_AE_boundedE)
    apply (rule laplace_integrand_integrable)
    apply (rule Ieo)
      apply assumption
     apply (rule integrable_continuous_interval)
     apply (rule Ic)
    apply (rule s)
    done
  then obtain LI where LI: "(I has_laplace LI) s"
    by (rule laplace_exists_laplace_integrandI)

  from piecewise_continuous_onE[OF pc] have \<open>finite D\<close> by auto
  have I'2: "(I has_vector_derivative f t) (at t)" if "t > 0" "t \<notin> D" for t
    apply (subst at_within_open[symmetric, where S="{0<..<t+1} - D"])
    subgoal using that by auto
    subgoal by (auto intro!:open_Diff finite_imp_closed \<open>finite D\<close>)
    subgoal using I'[where x="t + 1"]
      apply (rule has_vector_derivative_within_subset)
      using that
      by auto
    done
  have I_tndsto: "(I \<longlongrightarrow> 0) (at_right 0)"
    apply (rule tendsto_eq_rhs)
     apply (rule continuous_on_Icc_at_rightD)
      apply (rule Ic)
    apply (rule zero_less_one)
    by (auto simp: I_def)
  have "(f has_laplace s * LI - 0) s"
    by (rule has_laplace_derivative_time_domain[OF LI I'2 I_tndsto Ieo s])
      (auto simp: TODO)
  from has_laplace_unique[OF this L] have "LI = L / s"
    using s c by auto
  with LI show "(I has_laplace L / s) s" by simp
qed

subsection \<open>higher derivatives\<close>

definition "nderiv i f X = ((\<lambda>f. (\<lambda>x. vector_derivative f (at x within X)))^^i) f"

definition "ndiff n f X \<longleftrightarrow> (\<forall>i<n. \<forall>x \<in> X. nderiv i f X differentiable at x within X)"

lemma nderiv_zero[simp]: "nderiv 0 f X = f"
  by (auto simp: nderiv_def)

lemma nderiv_Suc[simp]:
  "nderiv (Suc i) f X x = vector_derivative (nderiv i f X) (at x within X)"
  by (auto simp: nderiv_def)

lemma ndiff_zero[simp]: "ndiff 0 f X"
  by (auto simp: ndiff_def)

lemma ndiff_Sucs[simp]:
  "ndiff (Suc i) f X \<longleftrightarrow>
    (ndiff i f X) \<and>
    (\<forall>x \<in> X. (nderiv i f X) differentiable (at x within X))"
  apply (auto simp: ndiff_def )
  using less_antisym by blast

theorem has_laplace_vector_derivative:
  "((\<lambda>t. vector_derivative f (at t)) has_laplace s * L - f0) s"
  if L: "(f has_laplace L) s"
    and f': "\<And>t. t > 0 \<Longrightarrow> f differentiable (at t)"
    and f0: "(f \<longlongrightarrow> f0) (at_right 0)"
    and eo: "exponential_order M c f"
    and cs: "c < Re s"
proof -
  have f': "(\<And>t. 0 < t \<Longrightarrow> (f has_vector_derivative vector_derivative f (at t)) (at t))"
    using f'
    by (subst vector_derivative_works[symmetric])
  show ?thesis
    by (rule has_laplace_derivative_time_domain[OF L f' f0 eo cs])
qed

lemma has_laplace_nderiv:
  "(nderiv n f {0<..} has_laplace s^n * L - (\<Sum>i<n. s^(n - Suc i) * f0 i)) s"
  if L: "(f has_laplace L) s"
    and f': "ndiff n f {0<..}"
    and f0: "\<And>i. i < n \<Longrightarrow> (nderiv i f {0<..} \<longlongrightarrow> f0 i) (at_right 0)"
    and eo: "\<And>i. i < n \<Longrightarrow> exponential_order M c (nderiv i f {0<..})"
    and cs: "c < Re s"
  using f' f0 eo
proof (induction n)
  case 0
  then show ?case
    by (auto simp: L)
next
  case (Suc n)
  have awo: "at t within {0<..} = at t" if "t > 0" for t::real
    using that
    by (subst at_within_open) auto
  have "((\<lambda>a. vector_derivative (nderiv n f {0<..}) (at a)) has_laplace
    s * ( s ^ n * L - (\<Sum>i<n. s^(n - Suc i) * f0 i)) - f0 n) s"
    (is "(_ has_laplace ?L) _")
    apply (rule has_laplace_vector_derivative)
        apply (rule Suc.IH)
    subgoal using Suc.prems by auto
    subgoal using Suc.prems by auto
    subgoal using Suc.prems by auto
    subgoal using Suc.prems by (auto simp: awo)
    subgoal using Suc.prems by auto
     apply (rule Suc.prems; force)
    apply (rule cs)
    done
  also have "?L = s ^ Suc n * L - (\<Sum>i<Suc n. s ^ (Suc n - Suc i) * f0 i)"
    by (auto simp: algebra_simps sum_distrib_left diff_Suc Suc_diff_le
        split: nat.splits
        intro!: sum.cong)
  finally show ?case
    by (rule has_laplace_spike[where T="{0}"]) (auto simp: awo)
qed

end