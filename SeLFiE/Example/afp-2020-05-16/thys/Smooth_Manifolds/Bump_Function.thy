section \<open>Bump Functions\<close>
theory Bump_Function
  imports Smooth
    "HOL-Analysis.Weierstrass_Theorems"
begin

subsection \<open>Construction\<close>

context begin

qualified definition f :: "real \<Rightarrow> real" where
  "f t = (if t > 0 then exp(-inverse t) else 0)"

lemma f_nonpos[simp]: "x \<le> 0 \<Longrightarrow> f x = 0"
  by (auto simp: f_def)

lemma exp_inv_limit_0_right:
  "((\<lambda>(t::real). exp(-inverse t)) \<longlongrightarrow> 0) (at_right 0)"
  apply (rule filterlim_compose[where g = exp])
   apply (rule exp_at_bot)
  apply (rule filterlim_compose[where g = uminus])
   apply (rule filterlim_uminus_at_bot_at_top)
  by (rule filterlim_inverse_at_top_right)

lemma "\<forall>\<^sub>F t in at_right 0. ((\<lambda>x. inverse (x ^ Suc k)) has_real_derivative
  - (inverse (t ^ Suc k) * ((1 + real k) * t ^ k) * inverse (t ^ Suc k))) (at t)"
  unfolding eventually_at_filter
  by (auto simp del: power_Suc intro!: derivative_eq_intros eventuallyI)

lemma exp_inv_limit_0_right_gen':
  "((\<lambda>(t::real). inverse (t ^ k) / exp(inverse t)) \<longlongrightarrow> 0) (at_right 0)"
proof (induct k)
  case 0
  then show ?case
    using exp_inv_limit_0_right
    by (auto simp: exp_minus inverse_eq_divide)
next
  case (Suc k)
  have df: "\<forall>\<^sub>F t in at_right 0. ((\<lambda>x. inverse (x ^ Suc k)) has_real_derivative 
    - (inverse (t ^ k) * ((1 + real k)) * (inverse t ^ 2))) (at t)"
    unfolding eventually_at_filter
    apply (auto simp del: power_Suc intro!: derivative_eq_intros eventuallyI)
    by (auto simp: power2_eq_square)
  have dg: "\<forall>\<^sub>F t in at_right 0. ((\<lambda>x. exp (inverse x)) has_real_derivative
    - (exp (inverse t) * (inverse t ^ 2))) (at t)"
    unfolding eventually_at_filter
    by (auto simp del: power_Suc intro!: derivative_eq_intros eventuallyI simp: power2_eq_square)
  show ?case
    apply (rule lhopital_right_0_at_top [OF _ _ df dg])
      apply (rule filterlim_compose[where g = exp])
       apply (rule exp_at_top)
      apply (rule filterlim_inverse_at_top_right)
    subgoal by (auto simp: eventually_at_filter)
    subgoal
      apply (rule Lim_transform_eventually[where f = "\<lambda>x. (1 + real k) * (inverse (x ^ k) / exp (inverse x))"])
      using Suc.hyps tendsto_mult_right_zero apply blast
      by (auto simp: eventually_at_filter)
    done
qed

lemma exp_inv_limit_0_right_gen:
  "((\<lambda>(t::real). exp(-inverse t) / t ^ k) \<longlongrightarrow> 0) (at_right 0)"
  using exp_inv_limit_0_right_gen'[of k]
  by (metis (no_types, lifting) Groups.mult_ac(2) Lim_cong_within divide_inverse exp_minus)  

lemma f_limit_0_right: "(f \<longlongrightarrow> 0) (at_right 0)"
proof -
  have "\<forall>\<^sub>F t in at_right 0. (t::real) > 0"
    by (rule eventually_at_right_less)
  then have "\<forall>\<^sub>F t in at_right 0. exp(-inverse t) = f t"
    by (eventually_elim) (auto simp: f_def)
  moreover have "((\<lambda>(t::real). exp(-inverse t)) \<longlongrightarrow> 0) (at_right 0)"
    by (rule exp_inv_limit_0_right)
  ultimately show ?thesis
    by (blast intro: Lim_transform_eventually)
qed

lemma f_limit_0: "(f \<longlongrightarrow> 0) (at 0)"
  using _ f_limit_0_right
proof (rule filterlim_split_at_real)
  have "\<forall>\<^sub>F t in at_left 0. 0 = f t"
    by (auto simp: f_def eventually_at_filter)
  then show "(f \<longlongrightarrow> 0) (at_left 0)"
    by (blast intro: Lim_transform_eventually) 
qed

lemma f_tendsto: "(f \<longlongrightarrow> f x) (at x)"
proof -
  consider "x = 0" | "x < 0" | "x > 0" by arith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (auto simp: f_limit_0 f_def)
  next
    case 2
    have "\<forall>\<^sub>F t in at x. t < 0"
      apply (rule order_tendstoD)
      by (rule tendsto_intros) fact
    then have "\<forall>\<^sub>F t in at x. 0 = f t"
      by (eventually_elim) (auto simp: f_def)
    then show ?thesis
      using \<open>x < 0\<close> by (auto simp: f_def intro: Lim_transform_eventually)
  next
    case 3
    have "\<forall>\<^sub>F t in at x. t > 0"
      apply (rule order_tendstoD)
      by (rule tendsto_intros) fact
    then have "\<forall>\<^sub>F t in at x. exp(-inverse t) = f t"
      by (eventually_elim) (auto simp: f_def)
    moreover have "(\<lambda>t. exp (- inverse t)) \<midarrow>x\<rightarrow> f x"
      using \<open>x > 0\<close> by (auto simp: f_def tendsto_intros )
    ultimately show ?thesis
      by (blast intro: Lim_transform_eventually)
  qed
qed

lemma f_continuous: "continuous_on S f"
  using f_tendsto continuous_on continuous_on_subset subset_UNIV by metis

lemma continuous_on_real_polynomial_function:
  "continuous_on S p" if "real_polynomial_function p"
  using that
  by induction (auto intro: continuous_intros linear_continuous_on)

lemma f_nth_derivative_is_poly:
  "higher_differentiable_on {0<..} f k \<and>
   (\<exists>p. real_polynomial_function p \<and> (\<forall>t>0. nth_derivative k f t 1 = p t / (t ^ (2 * k)) * exp(-inverse t)))"
proof (induction k)
  case 0
  then show ?case
    apply (auto simp: higher_differentiable_on.simps f_continuous)
    by (auto simp: f_def)
next
  case (Suc k)
  obtain p where fk: "higher_differentiable_on {0<..} f k"
    and p1: "real_polynomial_function p"
    and p2: "\<forall>t>0. nth_derivative k f t 1 = p t / t ^ (2 * k) * exp (- inverse t)"
    using Suc by auto
  obtain p' where p'1: "real_polynomial_function p'"
    and p'2: "\<forall>t. (p has_real_derivative (p' t)) (at t)"
    using has_real_derivative_polynomial_function[of p] p1 by auto

  define rp where "rp t = (t\<^sup>2 * p' t - 2 * real k * t * p t + p t)" for t
  have rp: "real_polynomial_function rp"
    unfolding rp_def
    by (auto intro!: real_polynomial_function.intros(2-) real_polynomial_function_diff
        p1 p'1 simp: power2_eq_square)
  moreover
  have fk': "(\<lambda>x. nth_derivative k f x 1) differentiable at t" (is ?a)
    "frechet_derivative (\<lambda>x. nth_derivative k f x 1) (at t) 1 =
        rp t * (exp (-inverse t) / t^(2*k+2))" (is ?b)
    if "0 < t" for t
  proof -
    from p'2 that have dp: "(p has_derivative ((*) (p' t))) (at t within {0<..})"
      by (auto simp: at_within_open[of _ "{0<..}"] has_field_derivative_def ac_simps)
    have "((\<lambda>t. p t / t ^ (2 * k) * exp (- inverse t)) has_derivative
      (\<lambda>v. v * rp t * (exp (-inverse t) / t^(2*k+2)))) (at t within {0<..})"
      using that
      apply (auto intro!: derivative_eq_intros dp ext)
      apply (simp add: divide_simps algebra_simps rp_def power2_eq_square)
      by (metis Suc_pred mult_is_0 neq0_conv power_Suc zero_neq_numeral)
    then have "((\<lambda>x. nth_derivative k f x 1) has_derivative
      (\<lambda>v. v * rp t * (exp (-inverse t) / t^(2*k+2)))) (at t within {0<..})"
      apply (rule has_derivative_transform_within[OF _ zero_less_one])
      using that p2 by (auto simp: )
    then have "((\<lambda>x. nth_derivative k f x 1) has_derivative
      (\<lambda>v. v * rp t * (exp (-inverse t) / t^(2*k+2)))) (at t)"
      using that
      by (auto simp: at_within_open[of _ "{0<..}"])
    from frechet_derivative_at'[OF this] this
    show ?a ?b
      by (auto simp: differentiable_def)
  qed
  have hdS: "higher_differentiable_on {0<..} f (Suc k)"
    apply (subst higher_differentiable_on_real_Suc')
     apply (auto simp: fk fk' frechet_derivative_nth_derivative_commute[symmetric])
    apply (subst continuous_on_cong[OF refl])
     apply (rule fk')
    by (auto intro!: continuous_intros p'1 p1 rp
        intro: continuous_on_real_polynomial_function)
  moreover
  have "nth_derivative (Suc k) f t 1 = rp t / t ^ (2 * (Suc k)) * exp (- inverse t)"
    if "t > 0" for t
  proof -
    have "nth_derivative (Suc k) f t 1 = frechet_derivative (\<lambda>x. nth_derivative k f x 1) (at t) 1"
      by (simp add: frechet_derivative_nth_derivative_commute)

    also have "\<dots> = rp t / t^(2*k+2) * (exp (-inverse t))"
      using fk'[OF \<open>t > 0\<close>] by simp
    finally  show ?thesis by simp
  qed
  ultimately show ?case by blast
qed

lemma f_has_derivative_at_neg:
  " x < 0 \<Longrightarrow> (f has_derivative (\<lambda>x. 0)) (at x)"
  by (rule has_derivative_transform_within_open[where f="\<lambda>x. 0" and s="{..<0}"])
    (auto simp: f_def)

lemma f_differentiable_at_neg:
  "x < 0 \<Longrightarrow> f differentiable at x"
  using f_has_derivative_at_neg
  by (auto simp: differentiable_def)

lemma frechet_derivative_f_at_neg:
  "x \<in> {..<0} \<Longrightarrow> frechet_derivative f (at x) = (\<lambda>x. 0)"
  by (rule frechet_derivative_at') (rule f_has_derivative_at_neg, simp)

lemma f_nth_derivative_lt_0:
  "higher_differentiable_on {..<0} f k \<and> (\<forall>t<0. nth_derivative k f t 1 = 0)"
proof (induction k)
  case 0
  have rewr: "a \<in> {..<0} \<Longrightarrow> \<not>0 < a" for a::real by simp
  show ?case
    by (auto simp: higher_differentiable_on.simps f_def rewr
        simp del: lessThan_iff
        cong: continuous_on_cong)
next
  case (Suc k)
  have "t < 0 \<Longrightarrow> (\<lambda>x. nth_derivative k f x 1) differentiable at t" for t
    by (rule differentiable_eqI[where g=0 and X="{..<0}"])
      (auto simp: zero_fun_def frechet_derivative_const Suc.IH)
  then have "frechet_derivative (\<lambda>x. nth_derivative k f x 1) (at t) 1 = 0" if "t < 0" for t
    using that Suc.IH
    by (subst frechet_derivative_transform_within_open[where X="{..<0}" and g =0])
      (auto simp: frechet_derivative_zero_fun)
  with Suc show ?case
    by (auto simp: higher_differentiable_on.simps f_differentiable_at_neg
        frechet_derivative_f_at_neg zero_fun_def
        simp flip: frechet_derivative_nth_derivative_commute
        simp del: lessThan_iff
        intro!: higher_differentiable_on_const
        cong: higher_differentiable_on_cong)
qed

lemma netlimit_at_left: "netlimit (at_left x) = x" for x::real
  by (rule Lim_ident_at) simp

lemma netlimit_at_right: "netlimit (at_right x) = x" for x::real
  by (rule Lim_ident_at) simp


lemma has_derivative_split_at:
  "(g has_derivative g') (at x)"
  if
    "(g has_derivative g') (at_left x)"
    "(g has_derivative g') (at_right x)"
  for x::real
  using that
  unfolding has_derivative_def netlimit_at netlimit_at_right netlimit_at_left
  by (auto intro: filterlim_split_at)

lemma has_derivative_at_left_at_right':
  "(g has_derivative g') (at x)"
  if
    "(g has_derivative g') (at x within {..x})"
    "(g has_derivative g') (at x within {x..})"
  for x::real
  apply (rule has_derivative_split_at)
  subgoal by (rule has_derivative_within_subset) (fact, auto)
  subgoal by (rule has_derivative_within_subset) (fact, auto)
  done

lemma real_polynomial_function_tendsto:
  "(p \<longlongrightarrow> p x) (at x within X)" if "real_polynomial_function p"
  using that
  by (induction p) (auto intro!: tendsto_eq_intros intro: bounded_linear.tendsto)

lemma f_nth_derivative_cases:
  "higher_differentiable_on UNIV f k \<and>
   (\<forall>t\<le>0. nth_derivative k f t 1 = 0) \<and>
   (\<exists>p. real_polynomial_function p \<and>
      (\<forall>t>0. nth_derivative k f t 1 = p t / (t ^ (2 * k)) * exp(-inverse t)))"
proof (induction k)
  case 0
  then show ?case
    apply (auto simp: higher_differentiable_on.simps f_continuous)
    by (auto simp: f_def)
next
  case (Suc k)
  from Suc.IH obtain pk where IH:
    "higher_differentiable_on UNIV f k"
    "\<And>t. t \<le> 0 \<Longrightarrow> nth_derivative k f t 1 = 0"
    "real_polynomial_function pk"
    "\<And>t. t > 0 \<Longrightarrow> nth_derivative k f t 1 = pk t / t ^ (2 * k) * exp (- inverse t)"
    by auto
  from f_nth_derivative_lt_0[of "Suc k"]
    local.f_nth_derivative_is_poly[of "Suc k"]
  obtain p where neg: "higher_differentiable_on {..<0} f (Suc k)"
    and neg0: "(\<forall>t<0. nth_derivative (Suc k) f t 1 = 0)"
    and pos: "higher_differentiable_on {0<..} f (Suc k)"
    and p: "real_polynomial_function p"
    "\<And>t. t > 0 \<Longrightarrow> nth_derivative (Suc k) f t 1 = p t / t ^ (2 * Suc k) * exp (- inverse t)"
    by auto
  moreover
  have at_within_eq_at_right: "(at 0 within {0..}) = at_right (0::real)"
    apply (auto simp: filter_eq_iff eventually_at_filter )
     apply (simp add: eventually_mono)
    apply (simp add: eventually_mono)
    done
  have [simp]: "{0..} - {0} = {0::real<..}" by auto
  have [simp]: "(at (0::real) within {0..}) \<noteq> bot"
    by (auto simp: at_within_eq_bot_iff)
  have k_th_has_derivative_at_left:
    "((\<lambda>x. nth_derivative k f x 1) has_derivative (\<lambda>x. 0)) (at 0 within {..0})"
    apply (rule has_derivative_transform_within[OF _ zero_less_one])
      prefer 2
      apply force
     prefer 2
     apply (simp add: IH)
    by (rule derivative_intros)
  have k_th_has_derivative_at_right:
    "((\<lambda>x. nth_derivative k f x 1) has_derivative (\<lambda>x. 0)) (at 0 within {0..})"
    apply (rule has_derivative_transform_within[where
          f="\<lambda>x'. if x' = 0 then 0 else pk x' / x' ^ (2 * k) * exp (- inverse x')", OF _ zero_less_one])
    subgoal
      unfolding has_derivative_def
      apply (auto simp: Lim_ident_at)
      apply (rule Lim_transform_eventually[where f="\<lambda>x. (pk x * (exp (- inverse x) / x ^ (2 * k + 1)))"])
       apply (rule tendsto_eq_intros)
         apply (rule real_polynomial_function_tendsto[THEN tendsto_eq_rhs])
          apply fact
         apply (rule refl)
        apply (subst at_within_eq_at_right)
        apply (rule exp_inv_limit_0_right_gen)
      apply (auto simp add: eventually_at_filter divide_simps)
      done
    subgoal by force
    subgoal by (auto simp: IH(2) IH(4))
    done
  have k_th_has_derivative: "((\<lambda>x. nth_derivative k f x 1) has_derivative (\<lambda>x. 0)) (at 0)"
    apply (rule has_derivative_at_left_at_right')
     apply (rule k_th_has_derivative_at_left)
    apply (rule k_th_has_derivative_at_right)
    done
  have nth_Suc_zero: "nth_derivative (Suc k) f 0 1 = 0"
    apply (auto simp: frechet_derivative_nth_derivative_commute[symmetric])
    apply (subst frechet_derivative_at')
     apply (rule k_th_has_derivative)
    by simp
  moreover have "higher_differentiable_on UNIV f (Suc k)"
  proof -
    have "continuous_on UNIV (\<lambda>x. nth_derivative (Suc k) f x 1)"
      unfolding continuous_on_eq_continuous_within
    proof
      fix x::real
      consider "x < 0" | "x > 0" | "x = 0" by arith
      then show "isCont (\<lambda>x. nth_derivative (Suc k) f x 1) x"
      proof cases
        case 1
        then have at_eq: "at x = at x within {..<0}"
          using at_within_open[of x "{..<0}"] by auto
        show ?thesis
          unfolding at_eq
          apply (rule continuous_transform_within[OF _ zero_less_one])
          using neg0 1 by (auto simp: at_eq)
      next
        case 2
        then have at_eq: "at x = at x within {0<..}"
          using at_within_open[of x "{0<..}"] by auto
        show ?thesis
          unfolding at_eq
          apply (rule continuous_transform_within[OF _ zero_less_one])
          using p 2 by (auto intro!: continuous_intros
              intro: continuous_real_polymonial_function continuous_at_imp_continuous_within)
      next
        case 3
        have "((\<lambda>x. nth_derivative (Suc k) f x 1) \<longlongrightarrow> 0) (at_left 0)"
        proof -
          have "\<forall>\<^sub>F x in at_left 0. 0 = nth_derivative (Suc k) f x 1"
            using neg0
            by (auto simp: eventually_at_filter)
          then show ?thesis
            by (blast intro: Lim_transform_eventually) 
        qed
        moreover have "((\<lambda>x. nth_derivative (Suc k) f x 1) \<longlongrightarrow> 0) (at_right 0)"
        proof -
          have "((\<lambda>x. p x * (exp (- inverse x) / x ^ (2 * Suc k))) \<longlongrightarrow> 0) (at_right 0)"
            apply (rule tendsto_eq_intros)
              apply (rule real_polynomial_function_tendsto)
              apply fact
             apply (rule exp_inv_limit_0_right_gen)
            by simp
          moreover
          have "\<forall>\<^sub>F x in at_right 0. p x * (exp (- inverse x) / x ^ (2 * Suc k)) =
            nth_derivative (Suc k) f x 1"
            using p
            by (auto simp: eventually_at_filter)
          ultimately show ?thesis
            by (rule Lim_transform_eventually)
        qed
        ultimately show ?thesis
          by (auto simp: continuous_def nth_Suc_zero 3 filterlim_split_at
              simp del: nth_derivative.simps)
      qed
    qed
    moreover have "(\<lambda>x. nth_derivative k f x 1) differentiable at x" for x
    proof -
      consider  "x = 0" | "x < 0" | "x > 0"by arith
      then show ?thesis
      proof cases
        case 1
        then show ?thesis
          using k_th_has_derivative by (auto simp: differentiable_def)
      next
        case 2
        with neg show ?thesis
          by (subst (asm) higher_differentiable_on_real_Suc') (auto simp: )
      next
        case 3
        with pos show ?thesis
          by (subst (asm) higher_differentiable_on_real_Suc') (auto simp: )
      qed
    qed
    moreover have "higher_differentiable_on UNIV f k" by fact
    ultimately
    show ?thesis
      by (subst higher_differentiable_on_real_Suc'[OF open_UNIV]) auto
  qed
  ultimately
  show ?case
    by (auto simp: less_eq_real_def)
qed

lemma f_smooth_on: "k-smooth_on S f"
  and f_higher_differentiable_on: "higher_differentiable_on S f n"
  using f_nth_derivative_cases
  by (auto simp: smooth_on_def higher_differentiable_on_subset[OF _ subset_UNIV])

lemma f_compose_smooth_on: "k-smooth_on S (\<lambda>x. f (g x))"
  if "k-smooth_on S g" "open S"
  using smooth_on_compose[OF f_smooth_on that open_UNIV subset_UNIV]
  by (auto simp: o_def)

lemma f_nonneg: "f x \<ge> 0"
  by (auto simp: f_def)

lemma f_pos_iff: "f x > 0 \<longleftrightarrow> x > 0"
  by (auto simp: f_def)

lemma f_eq_zero_iff: "f x = 0 \<longleftrightarrow> x \<le> 0"
  by (auto simp: f_def)


subsection \<open>Cutoff function\<close>

definition "h t = f (2 - t) / (f (2 - t) + f (t - 1))"

lemma denominator_pos: "f (2 - t) + f (t - 1) > 0"
  by (auto simp: f_def add_pos_pos)

lemma denominator_nonzero: "f (2 - t) + f (t - 1) = 0 \<longleftrightarrow> False"
  using denominator_pos[of t] by auto

lemma h_range: "0 \<le> h t" "h t \<le> 1"
  by (auto simp: h_def f_nonneg denominator_pos)

lemma h_pos: "t < 2 \<Longrightarrow> 0 < h t"
  and h_less_one: "1 < t \<Longrightarrow> h t < 1"
  by (auto simp: h_def f_pos_iff denominator_pos)

lemma h_eq_0: "h t = 0" if "t \<ge> 2"
  using that
  by (auto simp: h_def)

lemma h_eq_1: "h t = 1" if "t \<le> 1"
  using that
  by (auto simp: h_def f_eq_zero_iff)

lemma h_compose_smooth_on: "k-smooth_on S (\<lambda>x. h (g x))"
  if "k-smooth_on S g" "open S"
  by (auto simp: h_def[abs_def] denominator_nonzero
      intro!: smooth_on_divide f_compose_smooth_on smooth_on_minus smooth_on_add
      that)


subsection \<open>Bump function\<close>

definition H::"_::real_inner \<Rightarrow> real" where "H x = h (norm x)"

lemma H_range: "0 \<le> H x" "H x \<le> 1"
  by (auto simp: H_def h_range)

lemma H_eq_one: "H x = 1" if "x \<in> cball 0 1"
  using that
  by (auto simp: H_def h_eq_1)

lemma H_pos: "H x > 0" if "x \<in> ball 0 2"
  using that
  by (auto simp: H_def h_pos)

lemma H_eq_zero: "H x = 0" if "x \<notin> ball 0 2"
  using that
  by (auto simp: H_def h_eq_0)

lemma H_neq_zeroD: "H x \<noteq> 0 \<Longrightarrow> x \<in> ball 0 2"
  using H_eq_zero by blast

lemma H_smooth_on: "k-smooth_on UNIV H"
proof -
  have 1: "k-smooth_on (ball 0 1) H"
    by (rule smooth_on_cong[where g="\<lambda>x. 1"]) (auto simp: H_eq_one)
  have 2: "k-smooth_on (UNIV - cball 0 (1/2)) H"
    by (auto simp: H_def[abs_def]
        intro!: h_compose_smooth_on smooth_on_norm)
  have O: "open (ball 0 1)" "open (UNIV - cball 0 (1 / 2))"
    by auto
  have *: "ball 0 1 \<union> (UNIV - cball 0 (1 / 2)) = UNIV" by (auto simp: mem_ball)
  from smooth_on_open_Un[OF 1 2 O, unfolded *]
  show ?thesis
    by (rule smooth_on_subset) auto
qed

lemma H_compose_smooth_on: "k-smooth_on S (\<lambda>x. H (g x))" if "k-smooth_on S g" "open S"
  for g :: "_ \<Rightarrow> _::euclidean_space"
  using smooth_on_compose[OF H_smooth_on that]
  by (auto simp: o_def)

end

end