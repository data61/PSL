(*
  File:     Error_Function.thy
  Author:   Manuel Eberl, TU München

  The complex and real error function (most results are on the real error function though)
*)
section \<open>The complex and real error function\<close>
theory Error_Function
  imports "HOL-Analysis.Analysis" "HOL-Library.Landau_Symbols"
begin

subsection \<open>Auxiliary Facts\<close>

lemma tendsto_sandwich_mono:
  assumes "(\<lambda>n. f (real n)) \<longlonglongrightarrow> (c::real)"
  assumes "eventually (\<lambda>x. \<forall>y z. x \<le> y \<and> y \<le> z \<longrightarrow> f y \<le> f z) at_top"
  shows   "(f \<longlongrightarrow> c) at_top"
proof (rule tendsto_sandwich)
  from assms(2) obtain C where C: "\<And>x y. C \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
    by (auto simp: eventually_at_top_linorder)
  show "eventually (\<lambda>x. f (real (nat \<lfloor>x\<rfloor>)) \<le> f x) at_top"
    using eventually_gt_at_top[of "0::real"] eventually_gt_at_top[of "C+1::real"]
    by eventually_elim (rule C, linarith+)
  show "eventually (\<lambda>x. f (real (Suc (nat \<lfloor>x\<rfloor>))) \<ge> f x) at_top"
    using eventually_gt_at_top[of "0::real"] eventually_gt_at_top[of "C+1::real"]
    by eventually_elim (rule C, linarith+)
qed (auto intro!: filterlim_compose[OF assms(1)]
                  filterlim_compose[OF filterlim_nat_sequentially]
                  filterlim_compose[OF filterlim_Suc] filterlim_floor_sequentially
          simp del: of_nat_Suc)

lemma tendsto_sandwich_antimono:
  assumes "(\<lambda>n. f (real n)) \<longlonglongrightarrow> (c::real)"
  assumes "eventually (\<lambda>x. \<forall>y z. x \<le> y \<and> y \<le> z \<longrightarrow> f y \<ge> f z) at_top"
  shows   "(f \<longlongrightarrow> c) at_top"
proof (rule tendsto_sandwich)
  from assms(2) obtain C where C: "\<And>x y. C \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<ge> f y"
    by (auto simp: eventually_at_top_linorder)
  show "eventually (\<lambda>x. f (real (nat \<lfloor>x\<rfloor>)) \<ge> f x) at_top"
    using eventually_gt_at_top[of "0::real"] eventually_gt_at_top[of "C+1::real"]
    by eventually_elim (rule C, linarith+)
  show "eventually (\<lambda>x. f (real (Suc (nat \<lfloor>x\<rfloor>))) \<le> f x) at_top"
    using eventually_gt_at_top[of "0::real"] eventually_gt_at_top[of "C+1::real"]
    by eventually_elim (rule C, linarith+)
qed (auto intro!: filterlim_compose[OF assms(1)]
                  filterlim_compose[OF filterlim_nat_sequentially]
                  filterlim_compose[OF filterlim_Suc] filterlim_floor_sequentially
          simp del: of_nat_Suc)

lemma has_bochner_integral_completion [intro]:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "has_bochner_integral M f I \<Longrightarrow> has_bochner_integral (completion M) f I"
  by (auto simp: has_bochner_integral_iff integrable_completion integral_completion 
                 borel_measurable_integrable)

lemma has_bochner_integral_imp_has_integral:
  "has_bochner_integral lebesgue (\<lambda>x. indicator S x *\<^sub>R f x) I \<Longrightarrow> 
     (f has_integral (I :: 'b :: euclidean_space)) S"
  using has_integral_set_lebesgue[of S f] 
  by (simp add: has_bochner_integral_iff set_integrable_def set_lebesgue_integral_def) 
    
lemma has_bochner_integral_imp_has_integral':
  "has_bochner_integral lborel (\<lambda>x. indicator S x *\<^sub>R f x) I \<Longrightarrow> 
     (f has_integral (I :: 'b :: euclidean_space)) S"
  by (intro has_bochner_integral_imp_has_integral has_bochner_integral_completion)

lemma has_bochner_integral_erf_aux:
  "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R exp (- x\<^sup>2)) (sqrt pi / 2)"
proof -
  let ?pI = "\<lambda>f. (\<integral>\<^sup>+s. f (s::real) * indicator {0..} s \<partial>lborel)"
  let ?gauss = "\<lambda>x. exp (- x\<^sup>2)"
  let ?I = "indicator {0<..} :: real \<Rightarrow> real"
  let ?ff= "\<lambda>x s. x * exp (- x\<^sup>2 * (1 + s\<^sup>2)) :: real"
  have *: "?pI ?gauss = (\<integral>\<^sup>+x. ?gauss x * ?I x \<partial>lborel)"
    by (intro nn_integral_cong_AE AE_I[where N="{0}"]) (auto split: split_indicator)

  have "?pI ?gauss * ?pI ?gauss = (\<integral>\<^sup>+x. \<integral>\<^sup>+s. ?gauss x * ?gauss s * ?I s * ?I x \<partial>lborel \<partial>lborel)"
    by (auto simp: nn_integral_cmult[symmetric] nn_integral_multc[symmetric] * 
                   ennreal_mult[symmetric] intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+x. \<integral>\<^sup>+s. ?ff x s * ?I s * ?I x \<partial>lborel \<partial>lborel)"
  proof (rule nn_integral_cong, cases)
    fix x :: real assume "x \<noteq> 0"
    then show "(\<integral>\<^sup>+s. ?gauss x * ?gauss s * ?I s * ?I x \<partial>lborel) =
                 (\<integral>\<^sup>+s. ?ff x s * ?I s * ?I x \<partial>lborel)"
      by (subst nn_integral_real_affine[where t="0" and c="x"])
         (auto simp: mult_exp_exp nn_integral_cmult[symmetric] field_simps zero_less_mult_iff ennreal_mult[symmetric]
               intro!: nn_integral_cong split: split_indicator)
  qed simp
  also have "... = \<integral>\<^sup>+s. \<integral>\<^sup>+x. ?ff x s * ?I s * ?I x \<partial>lborel \<partial>lborel"
    by (rule lborel_pair.Fubini'[symmetric]) auto
  also have "... = ?pI (\<lambda>s. ?pI (\<lambda>x. ?ff x s))"
    by (rule nn_integral_cong_AE)
       (auto intro!: nn_integral_cong_AE AE_I[where N="{0}"] split: split_indicator_asm)
  also have "\<dots> = ?pI (\<lambda>s. ennreal (1 / (2 * (1 + s\<^sup>2))))"
  proof (intro nn_integral_cong ennreal_mult_right_cong)
    fix s :: real show "?pI (\<lambda>x. ?ff x s) = ennreal (1 / (2 * (1 + s\<^sup>2)))"
    proof (subst nn_integral_FTC_atLeast)
      have "((\<lambda>a. - (exp (- ((1 + s\<^sup>2) * a\<^sup>2)) / (2 + 2 * s\<^sup>2))) \<longlongrightarrow> (- (0 / (2 + 2 * s\<^sup>2)))) at_top"
        by (intro tendsto_intros filterlim_compose[OF exp_at_bot]
                  filterlim_compose[OF filterlim_uminus_at_bot_at_top]
                  filterlim_tendsto_pos_mult_at_top)
           (auto intro!: filterlim_at_top_mult_at_top[OF filterlim_ident filterlim_ident]
                 simp: add_pos_nonneg  power2_eq_square add_nonneg_eq_0_iff)
      then show "((\<lambda>a. - (exp (- a\<^sup>2 - s\<^sup>2 * a\<^sup>2) / (2 + 2 * s\<^sup>2))) \<longlongrightarrow> 0) at_top"
        by (simp add: field_simps)
    qed (auto intro!: derivative_eq_intros simp: field_simps add_nonneg_eq_0_iff)
  qed
  also have "... = ennreal (pi / 4)"
  proof (subst nn_integral_FTC_atLeast)
    show "((\<lambda>a. arctan a / 2) \<longlongrightarrow> (pi / 2) / 2 ) at_top"
      by (intro tendsto_intros) (simp_all add: tendsto_arctan_at_top)
  qed (auto intro!: derivative_eq_intros simp: add_nonneg_eq_0_iff field_simps power2_eq_square)
  finally have "?pI ?gauss^2 = pi / 4"
    by (simp add: power2_eq_square)
  then have "?pI ?gauss = sqrt (pi / 4)"
    using power_eq_iff_eq_base[of 2 "enn2real (?pI ?gauss)" "sqrt (pi / 4)"]
    by (cases "?pI ?gauss") (auto simp: power2_eq_square ennreal_mult[symmetric] ennreal_top_mult)
  also have "?pI ?gauss = (\<integral>\<^sup>+x. indicator {0..} x *\<^sub>R exp (- x\<^sup>2) \<partial>lborel)"
    by (intro nn_integral_cong) (simp split: split_indicator)
  also have "sqrt (pi / 4) = sqrt pi / 2"
    by (simp add: real_sqrt_divide)
  finally show ?thesis
    by (rule has_bochner_integral_nn_integral[rotated 3])
       auto
qed

lemma has_integral_erf_aux: "((\<lambda>t::real. exp (-t\<^sup>2)) has_integral (sqrt pi / 2)) {0..}"
  by (intro has_bochner_integral_imp_has_integral' has_bochner_integral_erf_aux)

lemma contour_integrable_on_linepath_neg_exp_squared [simp, intro]:
  "(\<lambda>t. exp (-(t^2))) contour_integrable_on linepath 0 z"
  by (auto intro!: contour_integrable_continuous_linepath continuous_intros)

lemma holomorphic_on_chain:
  "g holomorphic_on t \<Longrightarrow> f holomorphic_on s \<Longrightarrow> f ` s \<subseteq> t \<Longrightarrow> 
    (\<lambda>x. g (f x)) holomorphic_on s"
  using holomorphic_on_compose_gen[of f s g t] by (simp add: o_def)
    
lemma holomorphic_on_chain_UNIV:
  "g holomorphic_on UNIV \<Longrightarrow> f holomorphic_on s\<Longrightarrow> 
    (\<lambda>x. g (f x)) holomorphic_on s"
  using holomorphic_on_compose_gen[of f s g UNIV] by (simp add: o_def)

lemmas holomorphic_on_exp' [holomorphic_intros] = 
  holomorphic_on_exp [THEN holomorphic_on_chain_UNIV]

lemma leibniz_rule_field_derivative_real:
  fixes f::"'a::{real_normed_field, banach} \<Rightarrow> real \<Rightarrow> 'a"
  assumes fx: "\<And>x t. x \<in> U \<Longrightarrow> t \<in> {a..b} \<Longrightarrow> ((\<lambda>x. f x t) has_field_derivative fx x t) (at x within U)"
  assumes integrable_f2: "\<And>x. x \<in> U \<Longrightarrow> (f x) integrable_on {a..b}"
  assumes cont_fx: "continuous_on (U \<times> {a..b}) (\<lambda>(x, t). fx x t)"
  assumes U: "x0 \<in> U" "convex U"
  shows "((\<lambda>x. integral {a..b} (f x)) has_field_derivative integral {a..b} (fx x0)) (at x0 within U)"    
  using leibniz_rule_field_derivative[of U a b f fx x0] assms by simp

lemma has_vector_derivative_linepath_within [derivative_intros]:
  assumes [derivative_intros]: 
    "(f has_vector_derivative f') (at x within S)" "(g has_vector_derivative g') (at x within S)"
    "(h has_real_derivative h') (at x within S)"
  shows "((\<lambda>x. linepath (f x) (g x) (h x)) has_vector_derivative 
           (1 - h x) *\<^sub>R f' + h x *\<^sub>R g' - h' *\<^sub>R (f x - g x)) (at x within S)"
  unfolding linepath_def [abs_def]
  by (auto intro!: derivative_eq_intros simp: field_simps scaleR_diff_right)
    
lemma has_field_derivative_linepath_within [derivative_intros]:
  assumes [derivative_intros]: 
    "(f has_field_derivative f') (at x within S)" "(g has_field_derivative g') (at x within S)"
    "(h has_real_derivative h') (at x within S)"
  shows "((\<lambda>x. linepath (f x) (g x) (h x)) has_field_derivative 
           (1 - h x) *\<^sub>R f' + h x *\<^sub>R g' - h' *\<^sub>R (f x - g x)) (at x within S)"
  unfolding linepath_def [abs_def]
  by (auto intro!: derivative_eq_intros simp: field_simps scaleR_diff_right)

lemma continuous_on_linepath' [continuous_intros]:
  assumes [continuous_intros]: "continuous_on A f" "continuous_on A g" "continuous_on A h"
  shows   "continuous_on A (\<lambda>x. linepath (f x) (g x) (h x))"
  using assms unfolding linepath_def by (auto intro!: continuous_intros)
    
lemma contour_integral_has_field_derivative:
  assumes A: "open A" "convex A" "a \<in> A" "z \<in> A"
  assumes integrable: "\<And>z. z \<in> A \<Longrightarrow> f contour_integrable_on linepath a z"
  assumes holo: "f holomorphic_on A"
  shows   "((\<lambda>z. contour_integral (linepath a z) f) has_field_derivative f z) (at z within B)"
proof -
  have "(f has_field_derivative deriv f z) (at z)" if "z \<in> A" for z
    using that assms by (auto intro!: holomorphic_derivI)
  note [derivative_intros] = DERIV_chain2[OF this]
  note [continuous_intros] = 
    continuous_on_compose2[OF holomorphic_on_imp_continuous_on [OF holo]]
    continuous_on_compose2[OF holomorphic_on_imp_continuous_on [OF holomorphic_deriv[OF holo]]]
  have [derivative_intros]:
      "((\<lambda>x. linepath a x t) has_field_derivative of_real t) (at x within A)" for t x
    by (auto simp: linepath_def scaleR_conv_of_real intro!: derivative_eq_intros)
 
  have *: "linepath a b t \<in> A" if "a \<in> A" "b \<in> A" "t \<in> {0..1}" for a b t
    using that linepath_in_convex_hull[of a A b t] \<open>convex A\<close> by (simp add: hull_same)
    
  have "((\<lambda>z. integral {0..1} (\<lambda>x. f (linepath a z x)) * (z - a)) has_field_derivative 
      integral {0..1} (\<lambda>t. deriv f (linepath a z t) * of_real t) * (z - a) +
      integral {0..1} (\<lambda>x. f (linepath a z x))) (at z within A)" 
      (is "(_ has_field_derivative ?I) _")
    by (rule derivative_eq_intros leibniz_rule_field_derivative_real)+
       (insert assms,
        auto intro!: derivative_eq_intros leibniz_rule_field_derivative_real
                     integrable_continuous_real continuous_intros 
             simp:   split_beta scaleR_conv_of_real *)
  also have "(\<lambda>z. integral {0..1} (\<lambda>x. f (linepath a z x)) * (z - a)) = 
               (\<lambda>z. contour_integral (linepath a z) f)"
    by (simp add: contour_integral_integral)
  also have "?I = integral {0..1} (\<lambda>x. deriv f (linepath a z x) * of_real x * (z - a) + 
                     f (linepath a z x))" (is "_ = integral _ ?g")
    by (subst integral_mult_left [symmetric], subst integral_add [symmetric])
       (insert assms, auto intro!: integrable_continuous_real continuous_intros simp: *)
  also have "(?g has_integral of_real 1 * f (linepath a z 1) - of_real 0 * f (linepath a z 0)) {0..1}"
    using * A
    by (intro fundamental_theorem_of_calculus)
       (auto intro!: derivative_eq_intros has_vector_derivative_real_complex 
             simp: linepath_def scaleR_conv_of_real)
  hence "integral {0..1} ?g = f (linepath a z 1)" by (simp add: has_integral_iff)
  also have "linepath a z 1 = z" by (simp add: linepath_def)
  also from \<open>z \<in> A\<close> and \<open>open A\<close> have "at z within A = at z" by (rule at_within_open)
  finally show ?thesis by (rule DERIV_subset) simp_all
qed


subsection \<open>Definition of the error function\<close>

definition erf_coeffs :: "nat \<Rightarrow> real" where
  "erf_coeffs n = 
     (if odd n then 2 / sqrt pi * (-1) ^ (n div 2) / (of_nat n * fact (n div 2)) 
      else 0)"

lemma summable_erf:
  fixes z :: "'a :: {real_normed_div_algebra, banach}"
  shows "summable (\<lambda>n. of_real (erf_coeffs n) * z ^ n)"
proof -
  define b where "b = (\<lambda>n. 2 / sqrt pi * (if odd n then inverse (fact (n div 2)) else 0))"
  show ?thesis
  proof (rule summable_comparison_test[OF exI[of _ 1]], clarify)
    fix n :: nat assume n: "n \<ge> 1"
    hence "norm (of_real (erf_coeffs n) * z ^ n) \<le> b n * norm z ^ n"
      unfolding norm_mult norm_power erf_coeffs_def b_def
      by (intro mult_right_mono) (auto simp: field_simps norm_divide abs_mult)
    thus "norm (of_real (erf_coeffs n) * z ^ n) \<le> b n * norm z ^ n"
      by (simp add: mult_ac)
  next
    have "summable (\<lambda>n. (norm z * 2 / sqrt pi) * (inverse (fact n) * norm z ^ (2*n)))" 
      (is "summable ?c") unfolding power_mult by (intro summable_mult summable_exp)
    also have "?c = (\<lambda>n. b (2*n+1) * norm z ^ (2*n+1))"
      unfolding b_def by (auto simp: fun_eq_iff b_def)
    also have "summable \<dots> \<longleftrightarrow> summable (\<lambda>n. b n * norm z ^ n)"
      using summable_mono_reindex [of "\<lambda>n. 2*n+1"]
      by (intro summable_mono_reindex [of "\<lambda>n. 2*n+1"]) 
         (auto elim!: oddE simp: strict_mono_def b_def)
    finally show \<dots> .
  qed
qed
  
definition erf :: "('a :: {real_normed_field, banach}) \<Rightarrow> 'a" where
  "erf z = (\<Sum>n. of_real (erf_coeffs n) * z ^ n)"

lemma erf_converges: "(\<lambda>n. of_real (erf_coeffs n) * z ^ n) sums erf z"
  using summable_erf by (simp add: sums_iff erf_def)

lemma erf_0 [simp]: "erf 0 = 0"
  unfolding erf_def powser_zero by (simp add: erf_coeffs_def)

lemma erf_minus [simp]: "erf (-z) = - erf z"
  unfolding erf_def
  by (subst suminf_minus [OF summable_erf, symmetric], rule suminf_cong)
     (simp_all add: erf_coeffs_def)

lemma erf_of_real [simp]: "erf (of_real x) = of_real (erf x)"
  unfolding erf_def using summable_erf[of x]
  by (subst suminf_of_real) (simp_all add: summable_erf)
    
lemma of_real_erf_numeral [simp]: "of_real (erf (numeral n)) = erf (numeral n)"
  by (simp only: erf_of_real [symmetric] of_real_numeral)

lemma of_real_erf_1 [simp]: "of_real (erf 1) = erf 1"
  by (simp only: erf_of_real [symmetric] of_real_1)


lemma erf_has_field_derivative:
  "(erf has_field_derivative of_real (2 / sqrt pi) * exp (-(z^2))) (at z within A)"
proof -
    define a' where "a' = (\<lambda>n. 2 / sqrt pi *
     (if even n then (- 1) ^ (n div 2) / fact (n div 2) else 0))"

  have "(erf has_field_derivative
           (\<Sum>n. diffs (\<lambda>n. of_real (erf_coeffs n)) n * z ^ n)) (at z)"
    using summable_erf unfolding erf_def by (rule termdiffs_strong_converges_everywhere)
  also have "diffs (\<lambda>n. of_real (erf_coeffs n)) = (\<lambda>n. of_real (a' n) :: 'a)"
    by (simp add: erf_coeffs_def a'_def diffs_def fun_eq_iff del: of_nat_Suc)
  hence "(\<Sum>n. diffs (\<lambda>n. of_real (erf_coeffs n)) n * z ^ n) = 
           (\<Sum>n. of_real (a' n) * z ^ n)" by simp
  also have "\<dots> = (\<Sum>n. of_real (a' (2*n)) * z ^ (2*n))"
    by (intro suminf_mono_reindex [symmetric]) (auto simp: strict_mono_def a'_def elim!: evenE)
  also have "(\<lambda>n. of_real (a' (2*n)) * z ^ (2*n)) = 
               (\<lambda>n. of_real (2 / sqrt pi) * (inverse (fact n) * (-(z^2))^n))"
    by (simp add: fun_eq_iff power_mult [symmetric] a'_def field_simps power_minus')
  also have "suminf \<dots> = of_real (2 / sqrt pi) * exp (-(z^2))"
    by (subst suminf_mult, intro summable_exp) 
       (auto simp: field_simps scaleR_conv_of_real exp_def)
  finally show ?thesis by (rule DERIV_subset) simp_all
qed

lemmas erf_has_field_derivative' [derivative_intros] =
  erf_has_field_derivative [THEN DERIV_chain2]
  
lemma erf_continuous_on: "continuous_on A erf"
  by (rule DERIV_continuous_on erf_has_field_derivative)+

lemma continuous_on_compose2_UNIV:
  "continuous_on UNIV g \<Longrightarrow> continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. g (f x))"
  by (rule continuous_on_compose2[of UNIV g s f]) simp_all
    
lemmas erf_continuous_on' [continuous_intros] = 
  erf_continuous_on [THEN continuous_on_compose2_UNIV]

lemma erf_continuous [continuous_intros]: "continuous (at x within A) erf"
  by (rule continuous_within_subset[OF _ subset_UNIV])
     (insert erf_continuous_on[of UNIV], auto simp: continuous_on_eq_continuous_at)

lemmas erf_continuous' [continuous_intros] = 
  continuous_within_compose2[OF _ erf_continuous]
  
lemmas tendsto_erf [tendsto_intros] = isCont_tendsto_compose[OF erf_continuous]

lemma erf_cnj [simp]: "erf (cnj z) = cnj (erf z)"
proof -
  interpret bounded_linear cnj by (rule bounded_linear_cnj)
  from suminf[OF summable_erf] show ?thesis by (simp add: erf_def erf_coeffs_def)
qed


lemma integral_exp_minus_squared_real:
  assumes "a \<le> b"
  shows   "((\<lambda>t. exp (-(t^2))) has_integral (sqrt pi / 2 * (erf b - erf a))) {a..b}"
proof -
  have "((\<lambda>t. exp (-(t^2))) has_integral (sqrt pi / 2 * erf b - sqrt pi / 2 * erf a)) {a..b}"
    using assms
    by (intro fundamental_theorem_of_calculus)
       (auto intro!: derivative_eq_intros 
             simp: has_field_derivative_iff_has_vector_derivative [symmetric])
  thus ?thesis by (simp add: field_simps)
qed

lemma erf_real_altdef_nonneg:
  "x \<ge> 0 \<Longrightarrow> erf (x::real) = 2 / sqrt pi * integral {0..x} (\<lambda>t. exp (-(t^2)))"
  using integral_exp_minus_squared_real[of 0 x]
  by (simp add: has_integral_iff field_simps)
    
lemma erf_real_altdef_nonpos:
  "x \<le> 0 \<Longrightarrow> erf (x::real) = -2 / sqrt pi * integral {0..-x} (\<lambda>t. exp (-(t^2)))"
  using erf_real_altdef_nonneg[of "-x"] by simp

lemma less_imp_erf_real_less:
  assumes "a < (b::real)"
  shows   "erf a < erf b"
proof -
  from assms have "\<exists>z. z > a \<and> z < b \<and> erf b - erf a = (b - a) * (2 / sqrt pi * exp (- z\<^sup>2))"
    by (intro MVT2) (auto intro!: derivative_eq_intros simp: field_simps)
  then guess z by (elim exE conjE) note z = this
  note z(3)
  also from assms have "(b - a) * (2 / sqrt pi * exp (- z\<^sup>2)) > 0"
    by (intro mult_pos_pos divide_pos_pos) simp_all
  finally show ?thesis by simp
qed
  
lemma le_imp_erf_real_le: "a \<le> (b::real) \<Longrightarrow> erf a \<le> erf b"
  by (cases "a < b") (auto dest: less_imp_erf_real_less)
  
lemma erf_real_less_cancel [simp]: "(erf (a :: real) < erf b) \<longleftrightarrow> a < b"
  using less_imp_erf_real_less[of a b] less_imp_erf_real_less[of b a]
  by (cases a b rule: linorder_cases) simp_all

lemma erf_real_eq_iff [simp]: "erf (a::real) = erf b \<longleftrightarrow> a = b"
  by (cases a b rule: linorder_cases) (auto dest: less_imp_erf_real_less)
    
lemma erf_real_le_cancel [simp]: "(erf (a :: real) \<le> erf b) \<longleftrightarrow> a \<le> b"
  by (cases a b rule: linorder_cases) (auto simp: less_eq_real_def)
    
lemma inj_on_erf_real [intro]: "inj_on (erf :: real \<Rightarrow> real) A"
  by (auto simp: inj_on_def)
    
lemma strict_mono_erf_real [intro]: "strict_mono (erf :: real \<Rightarrow> real)"
  by (auto simp: strict_mono_def)
    
lemma mono_erf_real [intro]: "mono (erf :: real \<Rightarrow> real)"
  by (auto simp: mono_def)

lemma erf_real_ge_0_iff [simp]: "erf (x::real) \<ge> 0 \<longleftrightarrow> x \<ge> 0"
  using erf_real_le_cancel[of 0 x] unfolding erf_0 .

lemma erf_real_le_0_iff [simp]: "erf (x::real) \<le> 0 \<longleftrightarrow> x \<le> 0"
  using erf_real_le_cancel[of x 0] unfolding erf_0 .
    
lemma erf_real_gt_0_iff [simp]: "erf (x::real) > 0 \<longleftrightarrow> x > 0"
  using erf_real_less_cancel[of 0 x] unfolding erf_0 .

lemma erf_real_less_0_iff [simp]: "erf (x::real) < 0 \<longleftrightarrow> x < 0"
  using erf_real_less_cancel[of x 0] unfolding erf_0 .
    


lemma erf_at_top [tendsto_intros]: "((erf :: real \<Rightarrow> real) \<longlongrightarrow> 1) at_top"
proof -
  have *: "(\<Union>n. {0..real n}) = {0..}" by (auto intro!: real_nat_ceiling_ge)
  let ?f = "\<lambda>t::real. exp (-t\<^sup>2)"
  have "(\<lambda>n. set_lebesgue_integral lborel {0..real n} ?f)
          \<longlonglongrightarrow> set_lebesgue_integral lborel (\<Union>n. {0..real n}) ?f"
    using has_bochner_integral_erf_aux     
    by (intro set_integral_cont_up )
       (insert *, auto simp: incseq_def has_bochner_integral_iff set_integrable_def)
  also note *
  also have "(\<lambda>n. set_lebesgue_integral lborel {0..real n} ?f) = (\<lambda>n. integral {0..real n} ?f)"
  proof -
    have "\<And>n. set_integrable lborel {0..real n} (\<lambda>x. exp (- x\<^sup>2))"
      unfolding set_integrable_def
      by (intro borel_integrable_compact) (auto intro!: continuous_intros)
    then show ?thesis
      by (intro set_borel_integral_eq_integral ext)
  qed
  also have "\<dots> = (\<lambda>n. sqrt pi / 2 * erf (real n))" by (simp add: erf_real_altdef_nonneg)
  also have "set_lebesgue_integral lborel {0..} ?f = sqrt pi / 2"
    using has_bochner_integral_erf_aux by (simp add: has_bochner_integral_iff set_lebesgue_integral_def)
  finally have "(\<lambda>n. 2 / sqrt pi * (sqrt pi / 2 * erf (real n))) \<longlonglongrightarrow> 
                  (2 / sqrt pi) * (sqrt pi / 2)" by (intro tendsto_intros)
  hence "(\<lambda>n. erf (real n)) \<longlonglongrightarrow> 1" by simp
  thus ?thesis by (rule tendsto_sandwich_mono) auto
qed
  
lemma erf_at_bot [tendsto_intros]: "((erf :: real \<Rightarrow> real) \<longlongrightarrow> -1) at_bot"
  by (simp add: filterlim_at_bot_mirror tendsto_minus_cancel_left erf_at_top)

lemmas tendsto_erf_at_top [tendsto_intros] = filterlim_compose[OF erf_at_top]
lemmas tendsto_erf_at_bot [tendsto_intros] = filterlim_compose[OF erf_at_bot]


subsection \<open>The complimentary error function\<close>  
  
definition erfc where "erfc z = 1 - erf z"
  
lemma erf_conv_erfc: "erf z = 1 - erfc z" by (simp add: erfc_def)

lemma erfc_0 [simp]: "erfc 0 = 1"
  by (simp add: erfc_def)

lemma erfc_minus: "erfc (-z) = 2 - erfc z"
  by (simp add: erfc_def)

lemma erfc_of_real [simp]: "erfc (of_real x) = of_real (erfc x)"
  by (simp add: erfc_def)
    
lemma of_real_erfc_numeral [simp]: "of_real (erfc (numeral n)) = erfc (numeral n)"
  by (simp add: erfc_def)

lemma of_real_erfc_1 [simp]: "of_real (erfc 1) = erfc 1"
  by (simp add: erfc_def)
    

lemma less_imp_erfc_real_less: "a < (b::real) \<Longrightarrow> erfc a > erfc b"
  by (simp add: erfc_def)
  
lemma le_imp_erfc_real_le: "a \<le> (b::real) \<Longrightarrow> erfc a \<ge> erfc b"
  by (simp add: erfc_def)
  
lemma erfc_real_less_cancel [simp]: "(erfc (a :: real) < erfc b) \<longleftrightarrow> a > b"
  by (simp add: erfc_def)

lemma erfc_real_eq_iff [simp]: "erfc (a::real) = erfc b \<longleftrightarrow> a = b"
  by (simp add: erfc_def)
    
lemma erfc_real_le_cancel [simp]: "(erfc (a :: real) \<le> erfc b) \<longleftrightarrow> a \<ge> b"
  by (simp add: erfc_def)
    
lemma inj_on_erfc_real [intro]: "inj_on (erfc :: real \<Rightarrow> real) A"
  by (auto simp: inj_on_def)

lemma antimono_erfc_real [intro]: "antimono (erfc :: real \<Rightarrow> real)"
  by (auto simp: antimono_def)

lemma erfc_real_ge_0_iff [simp]: "erfc (x::real) \<ge> 1 \<longleftrightarrow> x \<le> 0"
  by (simp add: erfc_def)

lemma erfc_real_le_0_iff [simp]: "erfc (x::real) \<le> 1 \<longleftrightarrow> x \<ge> 0"
  by (simp add: erfc_def)
    
lemma erfc_real_gt_0_iff [simp]: "erfc (x::real) > 1 \<longleftrightarrow> x < 0"
  by (simp add: erfc_def)

lemma erfc_real_less_0_iff [simp]: "erfc (x::real) < 1 \<longleftrightarrow> x > 0"
  by (simp add: erfc_def)


lemma erfc_has_field_derivative:
  "(erfc has_field_derivative -of_real (2 / sqrt pi) * exp (-(z^2))) (at z within A)"
  unfolding erfc_def [abs_def] by (auto intro!: derivative_eq_intros)

lemmas erfc_has_field_derivative' [derivative_intros] =
  erfc_has_field_derivative [THEN DERIV_chain2]
  
lemma erfc_continuous_on: "continuous_on A erfc"
  by (rule DERIV_continuous_on erfc_has_field_derivative)+

lemmas erfc_continuous_on' [continuous_intros] = 
  erfc_continuous_on [THEN continuous_on_compose2_UNIV]

lemma erfc_continuous [continuous_intros]: "continuous (at x within A) erfc"
  by (rule continuous_within_subset[OF _ subset_UNIV])
     (insert erfc_continuous_on[of UNIV], auto simp: continuous_on_eq_continuous_at)

lemmas erfc_continuous' [continuous_intros] = 
  continuous_within_compose2[OF _ erfc_continuous]
  
lemmas tendsto_erfc [tendsto_intros] = isCont_tendsto_compose[OF erfc_continuous]

  
lemma erfc_at_top [tendsto_intros]: "((erfc :: real \<Rightarrow> real) \<longlongrightarrow> 0) at_top"
  unfolding erfc_def [abs_def] by (auto intro!: tendsto_eq_intros)
  
lemma erfc_at_bot [tendsto_intros]: "((erfc :: real \<Rightarrow> real) \<longlongrightarrow> 2) at_bot"
  unfolding erfc_def [abs_def] by (auto intro!: tendsto_eq_intros)

lemmas tendsto_erfc_at_top [tendsto_intros] = filterlim_compose[OF erfc_at_top]
lemmas tendsto_erfc_at_bot [tendsto_intros] = filterlim_compose[OF erfc_at_bot]  

lemma integrable_exp_minus_squared:
  assumes "A \<subseteq> {0..}" "A \<in> sets lborel"
  shows   "set_integrable lborel A (\<lambda>t::real. exp (-t\<^sup>2))" (is ?thesis1)
    and   "(\<lambda>t::real. exp (-t\<^sup>2)) integrable_on A" (is ?thesis2)
proof -
  show ?thesis1 
    by (rule set_integrable_subset[of _ "{0..}"]) 
       (insert assms has_bochner_integral_erf_aux, auto simp: has_bochner_integral_iff set_integrable_def)
  thus ?thesis2 by (rule set_borel_integral_eq_integral)
qed

lemma
  assumes "x \<ge> 0"
  shows   erfc_real_altdef_nonneg: "erfc x = 2 / sqrt pi * integral {x..} (\<lambda>t. exp (-t\<^sup>2))"
    and   has_integral_erfc:       "((\<lambda>t. exp (-t\<^sup>2)) has_integral (sqrt pi / 2 * erfc x)) {x..}"
proof -
  let ?f = "\<lambda>t::real. exp (-t\<^sup>2)"
  have int: "set_integrable lborel {0..} ?f"
    using has_bochner_integral_erf_aux by (simp add: has_bochner_integral_iff set_integrable_def)
  from assms have *: "{(0::real)..} = {0..x} \<union> {x..}" by auto
  have "set_lebesgue_integral lborel ({0..x} \<union> {x..}) ?f = 
               set_lebesgue_integral lborel {0..x} ?f + set_lebesgue_integral lborel {x..} ?f"
    by (subst set_integral_Un_AE; (rule set_integrable_subset[OF int])?)
       (insert assms AE_lborel_singleton[of x], auto elim!: eventually_mono)
  also note * [symmetric]
  also have "set_lebesgue_integral lborel {0..} ?f = sqrt pi / 2"
    using has_bochner_integral_erf_aux by (simp add: has_bochner_integral_iff set_lebesgue_integral_def)
  also have "set_lebesgue_integral lborel {0..x} ?f = sqrt pi / 2 * erf x"
    by (subst set_borel_integral_eq_integral(2)[OF set_integrable_subset[OF int]])
       (insert assms, auto simp: erf_real_altdef_nonneg)
  also have "set_lebesgue_integral lborel {x..} ?f = integral {x..} ?f"
    by (subst set_borel_integral_eq_integral(2)[OF set_integrable_subset[OF int]])
       (insert assms, auto) 
  finally show "erfc x = 2 / sqrt pi * integral {x..} ?f" by (simp add: field_simps erfc_def)
  with integrable_exp_minus_squared(2)[of "{x..}"] assms
  show "(?f has_integral (sqrt pi / 2 * erfc x)) {x..}"
    by (simp add: has_integral_iff)
qed


lemma erfc_real_gt_0 [simp, intro]: "erfc (x::real) > 0"
proof (cases "x \<ge> 0")
  case True
  have "0 < integral {x..x+1} (\<lambda>t. exp (-(x+1)\<^sup>2))" by simp
  also from True have "\<dots> \<le> integral {x..x+1} (\<lambda>t. exp (-t\<^sup>2))"
    by (intro integral_le) 
       (auto intro!: integrable_continuous_real continuous_intros power_mono)
  also have "\<dots> \<le> sqrt pi / 2 * erfc x"
    by (rule has_integral_subset_le[OF _ integrable_integral has_integral_erfc])
       (auto intro!: integrable_continuous_real continuous_intros True)
  finally have "sqrt pi / 2 * erfc x > 0" .
  hence "\<dots> * (2 / sqrt pi) > 0" by (rule mult_pos_pos) simp_all
  thus "erfc x > 0" by simp
next
  case False
  have "0 \<le> (1::real)" by simp
  also from False have "\<dots> < erfc x" by simp
  finally show ?thesis .
qed

lemma erfc_real_less_2 [intro]: "erfc (x::real) < 2"
  using erfc_real_gt_0[of "-x"] unfolding erfc_minus by simp
    
lemma erf_real_gt_neg1 [intro]: "erf (x::real) > -1"
  using erfc_real_less_2[of x] unfolding erfc_def by simp
    
lemma erf_real_less_1 [intro]: "erf (x::real) < 1"
  using erfc_real_gt_0[of x] unfolding erfc_def by simp

lemma erfc_cnj [simp]: "erfc (cnj z) = cnj (erfc z)"
  by (simp add: erfc_def)


subsection \<open>Specific facts about the complex case\<close>  
  
lemma erf_complex_altdef:
  "erf z = of_real (2 / sqrt pi) * contour_integral (linepath 0 z) (\<lambda>t. exp (-(t^2)))"
proof -
  define A where "A = (\<lambda>z. contour_integral (linepath 0 z) (\<lambda>t. exp (-(t^2))))"
  have [derivative_intros]: "(A has_field_derivative exp (-(z^2))) (at z)" for z :: complex
    unfolding A_def
    by (rule contour_integral_has_field_derivative[where A = UNIV])
       (auto intro!: holomorphic_intros)
  have "erf z - 2 / sqrt pi * A z = erf 0 - 2 / sqrt pi * A 0"
    by (intro DERIV_zero_UNIV_unique[of "\<lambda>z. erf z - 2 / sqrt pi * A z"]) 
       (auto intro!: derivative_eq_intros)
  also have "A 0 = 0" by (simp only: A_def contour_integral_trivial)
  finally show ?thesis unfolding A_def by (simp add: algebra_simps)
qed

lemma erf_holomorphic_on: "erf holomorphic_on A"
  by (auto simp: holomorphic_on_def field_differentiable_def intro!: erf_has_field_derivative)

lemmas erf_holomorphic_on' [holomorphic_intros] = 
  erf_holomorphic_on [THEN holomorphic_on_chain_UNIV]
  
lemma erf_analytic_on: "erf analytic_on A"
  by (auto simp: analytic_on_def) (auto intro!: exI[of _ 1] holomorphic_intros)

lemma erf_analytic_on'  [analytic_intros]:
  assumes "f analytic_on A"
  shows   "(\<lambda>x. erf (f x)) analytic_on A"
proof -
  from assms and erf_analytic_on have "erf \<circ> f analytic_on A"
    by (rule analytic_on_compose_gen) auto
  thus ?thesis by (simp add: o_def)
qed

lemma erfc_holomorphic_on: "erfc holomorphic_on A"
  by (auto simp: holomorphic_on_def field_differentiable_def intro!: erfc_has_field_derivative)

lemmas erfc_holomorphic_on' [holomorphic_intros] = 
  erfc_holomorphic_on [THEN holomorphic_on_chain_UNIV]

lemma erfc_analytic_on: "erfc analytic_on A"
  by (auto simp: analytic_on_def) (auto intro!: exI[of _ 1] holomorphic_intros)

lemma erfc_analytic_on' [analytic_intros]:
  assumes "f analytic_on A"
  shows   "(\<lambda>x. erfc (f x)) analytic_on A"
proof -
  from assms and erfc_analytic_on have "erfc \<circ> f analytic_on A"
    by (rule analytic_on_compose_gen) auto
  thus ?thesis by (simp add: o_def)
qed
   
end
