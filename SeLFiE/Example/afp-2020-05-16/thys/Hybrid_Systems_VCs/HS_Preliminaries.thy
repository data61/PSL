(*  Title:       Preliminaries for hybrid systems verification
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Hybrid Systems Preliminaries \<close>

text \<open>Hybrid systems combine continuous dynamics with discrete control. This section contains
auxiliary lemmas for verification of hybrid systems.\<close>

theory HS_Preliminaries
  imports "Ordinary_Differential_Equations.Picard_Lindeloef_Qualitative"
begin


subsection \<open> Real numbers \<close>

lemma abs_le_eq:
  shows "(r::real) > 0 \<Longrightarrow> (\<bar>x\<bar> < r) = (-r < x \<and> x < r)"
    and "(r::real) > 0 \<Longrightarrow> (\<bar>x\<bar> \<le> r) = (-r \<le> x \<and> x \<le> r)"
  by linarith+

lemma real_ivl_eqs:
  assumes "0 < r"
  shows "ball x r = {x-r<--< x+r}"         and "{x-r<--< x+r} = {x-r<..< x+r}"
    and "ball (r / 2) (r / 2) = {0<--<r}"  and "{0<--<r} = {0<..<r}"
    and "ball 0 r = {-r<--<r}"             and "{-r<--<r} = {-r<..<r}"
    and "cball x r = {x-r--x+r}"           and "{x-r--x+r} = {x-r..x+r}"
    and "cball (r / 2) (r / 2) = {0--r}"   and "{0--r} = {0..r}"
    and "cball 0 r = {-r--r}"              and "{-r--r} = {-r..r}"
  unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl
  using assms by (auto simp: cball_def ball_def dist_norm field_simps)

lemma norm_rotate_eq[simp]:
  fixes x :: "'a:: {banach,real_normed_field}"
  shows "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    and "(x * cos t + y * sin t)\<^sup>2 + (y * cos t - x * sin t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
proof-
  have "(x * cos t - y * sin t)\<^sup>2 = x\<^sup>2 * (cos t)\<^sup>2 + y\<^sup>2 * (sin t)\<^sup>2 - 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_diff power_mult_distrib)
  also have "(x * sin t + y * cos t)\<^sup>2 = y\<^sup>2 * (cos t)\<^sup>2 + x\<^sup>2 * (sin t)\<^sup>2 + 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_sum power_mult_distrib)
  ultimately show "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    by (simp add: Groups.mult_ac(2) Groups.mult_ac(3) right_diff_distrib sin_squared_eq)
  thus "(x * cos t + y * sin t)\<^sup>2 + (y * cos t - x * sin t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    by (simp add: add.commute add.left_commute power2_diff power2_sum)
qed


subsection \<open> Single variable derivatives \<close>

notation has_derivative ("(1(D _ \<mapsto> (_))/ _)" [65,65] 61)
notation has_vderiv_on ("(1 D _ = (_)/ on _)" [65,65] 61)
notation norm ("(1\<parallel>_\<parallel>)" [65] 61)

thy_deps

named_theorems poly_derivatives "compilation of optimised miscellaneous derivative rules."

declare has_vderiv_on_const [poly_derivatives]
    and has_vderiv_on_id [poly_derivatives]
    and has_vderiv_on_add[THEN has_vderiv_on_eq_rhs, poly_derivatives]
    and has_vderiv_on_diff[THEN has_vderiv_on_eq_rhs, poly_derivatives]
    and has_vderiv_on_mult[THEN has_vderiv_on_eq_rhs, poly_derivatives]

lemma has_vderiv_on_compose_eq:
  assumes "D f = f' on g ` T"
    and " D g = g' on T"
    and "h = (\<lambda>x. g' x *\<^sub>R f' (g x))"
  shows "D (\<lambda>t. f (g t)) = h on T"
  apply(subst ssubst[of h], simp)
  using assms has_vderiv_on_compose by auto

lemma vderiv_on_compose_add [derivative_intros]:
  assumes "D x = x' on (\<lambda>\<tau>. \<tau> + t) ` T"
  shows "D (\<lambda>\<tau>. x (\<tau> + t)) = (\<lambda>\<tau>. x' (\<tau> + t)) on T"
  apply(rule has_vderiv_on_compose_eq[OF assms])
  by(auto intro: derivative_intros)

lemma has_vderiv_on_divide_cnst: "a \<noteq> 0 \<Longrightarrow> D (\<lambda>t. t/a) = (\<lambda>t. 1/a) on T"
  unfolding has_vderiv_on_def has_vector_derivative_def
  apply clarify
  apply(rule_tac f'1="\<lambda>t. t" and g'1="\<lambda> x. 0" in has_derivative_divide[THEN has_derivative_eq_rhs])
  by(auto intro: derivative_eq_intros)

lemma has_vderiv_on_power: "n \<ge> 1 \<Longrightarrow> D (\<lambda>t. t ^ n) = (\<lambda>t. n * (t ^ (n - 1))) on T"
  unfolding has_vderiv_on_def has_vector_derivative_def
  by (auto intro!: derivative_eq_intros)

lemma has_vderiv_on_exp: "D (\<lambda>t. exp t) = (\<lambda>t. exp t) on T"
  unfolding has_vderiv_on_def has_vector_derivative_def by (auto intro: derivative_intros)

lemma has_vderiv_on_cos_comp:
  "D (f::real \<Rightarrow> real) = f' on T \<Longrightarrow> D (\<lambda>t. cos (f t)) = (\<lambda>t. - (f' t) * sin (f t)) on T"
  apply(rule has_vderiv_on_compose_eq[of "\<lambda>t. cos t"])
  unfolding has_vderiv_on_def has_vector_derivative_def
    apply clarify
  by(auto intro!: derivative_eq_intros simp: fun_eq_iff)

lemma has_vderiv_on_sin_comp:
  "D (f::real \<Rightarrow> real) = f' on T \<Longrightarrow> D (\<lambda>t. sin (f t)) = (\<lambda>t. (f' t) * cos (f t)) on T"
  apply(rule has_vderiv_on_compose_eq[of "\<lambda>t. sin t"])
  unfolding has_vderiv_on_def has_vector_derivative_def
    apply clarify
  by(auto intro!: derivative_eq_intros simp: fun_eq_iff)

lemma has_vderiv_on_exp_comp:
  "D (f::real \<Rightarrow> real) = f' on T \<Longrightarrow> D (\<lambda>t. exp (f t)) = (\<lambda>t. (f' t) * exp (f t)) on T"
  apply(rule has_vderiv_on_compose_eq[of "\<lambda>t. exp t"])
  by (rule has_vderiv_on_exp, simp_all add: mult.commute)

lemma vderiv_uminus_intro [poly_derivatives]:
  "D f = f' on T \<Longrightarrow> g = (\<lambda>t. - f' t) \<Longrightarrow> D (\<lambda>t. - f t) = g on T"
  using has_vderiv_on_uminus by auto

lemma vderiv_div_cnst_intro [poly_derivatives]:
  assumes "(a::real) \<noteq> 0" and "D f = f' on T" and "g = (\<lambda>t. (f' t)/a)"
  shows "D (\<lambda>t. (f t)/a) = g on T"
  apply(rule has_vderiv_on_compose_eq[of "\<lambda>t. t/a" "\<lambda>t. 1/a"])
  using assms by(auto intro: has_vderiv_on_divide_cnst)

lemma vderiv_npow_intro [poly_derivatives]:
  fixes f::"real \<Rightarrow> real"
  assumes "n \<ge> 1" and "D f = f' on T" and "g = (\<lambda>t. n * (f' t) * (f t)^(n-1))"
  shows "D (\<lambda>t. (f t)^n) = g on T"
  apply(rule has_vderiv_on_compose_eq[of "\<lambda>t. t^n"])
  using assms(1)
    apply(rule has_vderiv_on_power)
  using assms by auto

lemma vderiv_cos_intro [poly_derivatives]:
  assumes "D (f::real \<Rightarrow> real) = f' on T" and "g = (\<lambda>t. - (f' t) * sin (f t))"
  shows "D (\<lambda>t. cos (f t)) = g on T"
  using assms and has_vderiv_on_cos_comp by auto

lemma vderiv_sin_intro [poly_derivatives]:
  assumes "D (f::real \<Rightarrow> real) = f' on T" and "g = (\<lambda>t. (f' t) * cos (f t))"
  shows "D (\<lambda>t. sin (f t)) = g on T"
  using assms and has_vderiv_on_sin_comp by auto

lemma vderiv_exp_intro [poly_derivatives]:
  assumes "D (f::real \<Rightarrow> real) = f' on T" and "g = (\<lambda>t. (f' t) * exp (f t))"
  shows "D (\<lambda>t. exp (f t)) = g on T"
  using assms and has_vderiv_on_exp_comp by auto

\<comment> \<open>Examples for checking derivatives\<close>

lemma "D (\<lambda>t. a * t\<^sup>2 / 2 + v * t + x) = (\<lambda>t. a * t + v) on T"
  by(auto intro!: poly_derivatives)

lemma "D (\<lambda>t. v * t - a * t\<^sup>2 / 2 + x) = (\<lambda>x. v - a * x) on T"
  by(auto intro!: poly_derivatives)

lemma "c \<noteq> 0 \<Longrightarrow> D (\<lambda>t. a5 * t^5 + a3 * (t^3 / c) - a2 * exp (t^2) + a1 * cos t + a0) =
  (\<lambda>t. 5 * a5 * t^4 + 3 * a3 * (t^2 / c) - 2 * a2 * t * exp (t^2) - a1 * sin t) on T"
  by(auto intro!: poly_derivatives)

lemma "c \<noteq> 0 \<Longrightarrow> D (\<lambda>t. - a3 * exp (t^3 / c) + a1 * sin t + a2 * t^2) =
  (\<lambda>t. a1 * cos t + 2 * a2 * t - 3 * a3 * t^2 / c * exp (t^3 / c)) on T"
  apply(intro poly_derivatives)
  using poly_derivatives(1,2) by force+

lemma "c \<noteq> 0 \<Longrightarrow> D (\<lambda>t. exp (a * sin (cos (t^4) / c))) =
(\<lambda>t. - 4 * a * t^3 * sin (t^4) / c * cos (cos (t^4) / c) * exp (a * sin (cos (t^4) / c))) on T"
  apply(intro poly_derivatives)
  using poly_derivatives(1,2) by force+


subsection \<open> Intermediate Value Theorem \<close>

lemma IVT_two_functions:
  fixes f :: "('a::{linear_continuum_topology, real_vector}) \<Rightarrow> 
  ('b::{linorder_topology,real_normed_vector,ordered_ab_group_add})"
  assumes conts: "continuous_on {a..b} f" "continuous_on {a..b} g"
      and ahyp: "f a < g a" and bhyp: "g b < f b " and "a \<le> b"
    shows "\<exists>x\<in>{a..b}. f x = g x"
proof-
  let "?h x" = "f x - g x"
  have "?h a \<le> 0" and "?h b \<ge> 0"
    using ahyp bhyp by simp_all
  also have "continuous_on {a..b} ?h"
    using conts continuous_on_diff by blast 
  ultimately obtain x where "a \<le> x" "x \<le> b" and "?h x = 0"
    using IVT'[of "?h"] \<open>a \<le> b\<close> by blast
  thus ?thesis
    using \<open>a \<le> b\<close> by auto
qed

lemma IVT_two_functions_real_ivl:
  fixes f :: "real \<Rightarrow> real"
  assumes conts: "continuous_on {a--b} f" "continuous_on {a--b} g"
      and ahyp: "f a < g a" and bhyp: "g b < f b "
    shows "\<exists>x\<in>{a--b}. f x = g x"
proof(cases "a \<le> b")
  case True
  then show ?thesis 
    using IVT_two_functions assms 
    unfolding closed_segment_eq_real_ivl by auto
next
  case False
  hence "a \<ge> b"
    by auto
  hence "continuous_on {b..a} f" "continuous_on {b..a} g"
    using conts False unfolding closed_segment_eq_real_ivl by auto
  hence "\<exists>x\<in>{b..a}. g x = f x"
    using IVT_two_functions[of b a g f] assms(3,4) False by auto
  then show ?thesis  
    using \<open>a \<ge> b\<close> unfolding closed_segment_eq_real_ivl by auto force
qed


subsection \<open> Filters \<close>

lemma eventually_at_within_mono:
  assumes "t \<in> interior T" and "T \<subseteq> S"
    and "eventually P (at t within T)"
  shows "eventually P (at t within S)"
  by (meson assms eventually_within_interior interior_mono subsetD)

lemma netlimit_at_within_mono:
  fixes t::"'a::{perfect_space,t2_space}"
  assumes "t \<in> interior T" and "T \<subseteq> S"
  shows "netlimit (at t within S) = t"
  using assms(1) interior_mono[OF \<open>T \<subseteq> S\<close>] netlimit_within_interior by auto

lemma has_derivative_at_within_mono:
  assumes "(t::real) \<in> interior T" and "T \<subseteq> S"
    and "D f \<mapsto> f' at t within T"
  shows "D f \<mapsto> f' at t within S"
  using assms(3) apply(unfold has_derivative_def tendsto_iff, safe)
  unfolding netlimit_at_within_mono[OF assms(1,2)] netlimit_within_interior[OF assms(1)]
  by (rule eventually_at_within_mono[OF assms(1,2)]) simp

lemma eventually_all_finite2:
  fixes P :: "('a::finite) \<Rightarrow> 'b \<Rightarrow> bool"
  assumes h:"\<forall>i. eventually (P i) F"
  shows "eventually (\<lambda>x. \<forall>i. P i x) F"
proof(unfold eventually_def)
  let ?F = "Rep_filter F"
  have obs: "\<forall>i. ?F (P i)"
    using h by auto
  have "?F (\<lambda>x. \<forall>i \<in> UNIV. P i x)"
    apply(rule finite_induct)
    by(auto intro: eventually_conj simp: obs h)
  thus "?F (\<lambda>x. \<forall>i. P i x)"
    by simp
qed

lemma eventually_all_finite_mono:
  fixes P :: "('a::finite) \<Rightarrow> 'b \<Rightarrow> bool"
  assumes h1: "\<forall>i. eventually (P i) F"
      and h2: "\<forall>x. (\<forall>i. (P i x)) \<longrightarrow> Q x"
  shows "eventually Q F"
proof-
  have "eventually (\<lambda>x. \<forall>i. P i x) F"
    using h1 eventually_all_finite2 by blast
  thus "eventually Q F"
    unfolding eventually_def
    using h2 eventually_mono by auto
qed


subsection \<open> Multivariable derivatives \<close>

lemma frechet_vec_lambda:
  fixes f::"real \<Rightarrow> ('a::banach)^('m::finite)" and x::real and T::"real set"
  defines "x\<^sub>0 \<equiv> netlimit (at x within T)" and "m \<equiv> real CARD('m)"
  assumes "\<forall>i. ((\<lambda>y. (f y $ i - f x\<^sub>0 $ i - (y - x\<^sub>0) *\<^sub>R f' x $ i) /\<^sub>R (\<parallel>y - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at x within T)"
  shows "((\<lambda>y. (f y - f x\<^sub>0 - (y - x\<^sub>0) *\<^sub>R f' x) /\<^sub>R (\<parallel>y - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at x within T)"
proof(simp add: tendsto_iff, clarify)
  fix \<epsilon>::real assume "0 < \<epsilon>"
  let "?\<Delta>" = "\<lambda>y. y - x\<^sub>0" and "?\<Delta>f" = "\<lambda>y. f y - f x\<^sub>0"
  let "?P" = "\<lambda>i e y. inverse \<bar>?\<Delta> y\<bar> * (\<parallel>f y $ i - f x\<^sub>0 $ i - ?\<Delta> y *\<^sub>R f' x $ i\<parallel>) < e"
    and "?Q" = "\<lambda>y. inverse \<bar>?\<Delta> y\<bar> * (\<parallel>?\<Delta>f y - ?\<Delta> y *\<^sub>R f' x\<parallel>) < \<epsilon>"
  have "0 < \<epsilon> / sqrt m"
    using \<open>0 < \<epsilon>\<close> by (auto simp: assms)
  hence "\<forall>i. eventually (\<lambda>y. ?P i (\<epsilon> / sqrt m) y) (at x within T)"
    using assms unfolding tendsto_iff by simp
  thus "eventually ?Q (at x within T)"
  proof(rule eventually_all_finite_mono, simp add: norm_vec_def L2_set_def, clarify)
    fix t::real
    let ?c = "inverse \<bar>t - x\<^sub>0\<bar>" and "?u t" = "\<lambda>i. f t $ i - f x\<^sub>0 $ i - ?\<Delta> t *\<^sub>R f' x $ i"
    assume hyp:"\<forall>i. ?c * (\<parallel>?u t i\<parallel>) < \<epsilon> / sqrt m"
    hence "\<forall>i. (?c *\<^sub>R (\<parallel>?u t i\<parallel>))\<^sup>2 < (\<epsilon> / sqrt m)\<^sup>2"
      by (simp add: power_strict_mono)
    hence "\<forall>i. ?c\<^sup>2 * ((\<parallel>?u t i\<parallel>))\<^sup>2 < \<epsilon>\<^sup>2 / m"
      by (simp add: power_mult_distrib power_divide assms)
    hence "\<forall>i. ?c\<^sup>2 * ((\<parallel>?u t i\<parallel>))\<^sup>2 < \<epsilon>\<^sup>2 / m"
      by (auto simp: assms)
    also have "({}::'m set) \<noteq> UNIV \<and> finite (UNIV :: 'm set)"
      by simp
    ultimately have "(\<Sum>i\<in>UNIV. ?c\<^sup>2 * ((\<parallel>?u t i\<parallel>))\<^sup>2) < (\<Sum>(i::'m)\<in>UNIV. \<epsilon>\<^sup>2 / m)"
      by (metis (lifting) sum_strict_mono)
    moreover have "?c\<^sup>2 * (\<Sum>i\<in>UNIV. (\<parallel>?u t i\<parallel>)\<^sup>2) = (\<Sum>i\<in>UNIV. ?c\<^sup>2 *  (\<parallel>?u t i\<parallel>)\<^sup>2)"
      using sum_distrib_left by blast
    ultimately have "?c\<^sup>2 * (\<Sum>i\<in>UNIV. (\<parallel>?u t i\<parallel>)\<^sup>2) < \<epsilon>\<^sup>2"
      by (simp add: assms)
    hence "sqrt (?c\<^sup>2 * (\<Sum>i\<in>UNIV. (\<parallel>?u t i\<parallel>)\<^sup>2)) < sqrt (\<epsilon>\<^sup>2)"
      using real_sqrt_less_iff by blast
    also have "... = \<epsilon>"
      using \<open>0 < \<epsilon>\<close> by auto
    moreover have "?c * sqrt (\<Sum>i\<in>UNIV. (\<parallel>?u t i\<parallel>)\<^sup>2) = sqrt (?c\<^sup>2 * (\<Sum>i\<in>UNIV. (\<parallel>?u t i\<parallel>)\<^sup>2))"
      by (simp add: real_sqrt_mult)
    ultimately show "?c * sqrt (\<Sum>i\<in>UNIV. (\<parallel>?u t i\<parallel>)\<^sup>2) < \<epsilon>"
      by simp
  qed
qed

lemma tendsto_norm_bound:
  "\<forall>x. \<parallel>G x - L\<parallel> \<le> \<parallel>F x - L\<parallel> \<Longrightarrow> (F \<longlongrightarrow> L) net \<Longrightarrow> (G \<longlongrightarrow> L) net"
  apply(unfold tendsto_iff dist_norm, clarsimp)
  apply(rule_tac P="\<lambda>x. \<parallel>F x - L\<parallel> < e" in eventually_mono, simp)
  by (rename_tac e z) (erule_tac x=z in allE, simp)

lemma tendsto_zero_norm_bound:
  "\<forall>x. \<parallel>G x\<parallel> \<le> \<parallel>F x\<parallel> \<Longrightarrow> (F \<longlongrightarrow> 0) net \<Longrightarrow> (G \<longlongrightarrow> 0) net"
  apply(unfold tendsto_iff dist_norm, clarsimp)
  apply(rule_tac P="\<lambda>x. \<parallel>F x\<parallel> < e" in eventually_mono, simp)
  by (rename_tac e z) (erule_tac x=z in allE, simp)

lemma frechet_vec_nth:
  fixes f::"real \<Rightarrow> ('a::real_normed_vector)^'m"
  assumes "((\<lambda>x. (f x - f x\<^sub>0 - (x - x\<^sub>0) *\<^sub>R f' t) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at t within T)"
  shows "((\<lambda>x. (f x $ i - f x\<^sub>0 $ i - (x - x\<^sub>0) *\<^sub>R f' t $ i) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at t within T)"
  apply(rule_tac F="(\<lambda>x. (f x - f x\<^sub>0 - (x - x\<^sub>0) *\<^sub>R f' t) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>))" in tendsto_zero_norm_bound)
   apply(clarsimp, rule mult_left_mono)
    apply (metis Finite_Cartesian_Product.norm_nth_le vector_minus_component vector_scaleR_component)
  using assms by simp_all

lemma has_derivative_vec_lambda:
  fixes f::"real \<Rightarrow> ('a::banach)^('n::finite)"
  assumes "\<forall>i. D (\<lambda>t. f t $ i) \<mapsto> (\<lambda> h. h *\<^sub>R f' x $ i) (at x within T)"
  shows "D f \<mapsto> (\<lambda>h. h *\<^sub>R f' x) at x within T"
  apply(unfold has_derivative_def, safe)
   apply(force simp: bounded_linear_def bounded_linear_axioms_def)
  using assms frechet_vec_lambda[of x T ] unfolding has_derivative_def by auto

lemma has_derivative_vec_nth:
  assumes "D f \<mapsto> (\<lambda>h. h *\<^sub>R f' x) at x within T"
  shows "D (\<lambda>t. f t $ i) \<mapsto> (\<lambda>h. h *\<^sub>R f' x $ i) at x within T"
  apply(unfold has_derivative_def, safe)
   apply(force simp: bounded_linear_def bounded_linear_axioms_def)
  using frechet_vec_nth assms unfolding has_derivative_def by auto

lemma has_vderiv_on_vec_eq[simp]:
  fixes x::"real \<Rightarrow> ('a::banach)^('n::finite)"
  shows "(D x = x' on T) = (\<forall>i. D (\<lambda>t. x t $ i) = (\<lambda>t. x' t $ i) on T)"
  unfolding has_vderiv_on_def has_vector_derivative_def apply safe
  using has_derivative_vec_nth has_derivative_vec_lambda by blast+

end