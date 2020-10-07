section \<open>Linear ODE\<close>
theory Linear_ODE
imports
  "../IVP/Flow"
  Bounded_Linear_Operator
  Multivariate_Taylor
begin

lemma
  exp_scaleR_has_derivative_right[derivative_intros]:
  fixes f::"real \<Rightarrow> real"
  assumes "(f has_derivative f') (at x within s)"
  shows "((\<lambda>x. exp (f x *\<^sub>R A)) has_derivative (\<lambda>h. f' h *\<^sub>R (exp (f x *\<^sub>R A) * A))) (at x within s)"
proof -
  from assms have "bounded_linear f'" by auto
  with real_bounded_linear obtain m where f': "f' = (\<lambda>h. h * m)" by blast
  show ?thesis
    using vector_diff_chain_within[OF _ exp_scaleR_has_vector_derivative_right, of f m x s A] assms f'
    by (auto simp: has_vector_derivative_def o_def)
qed

context
fixes A::"'a::{banach,perfect_space} blinop"
begin

definition "linode_solution t0 x0 = (\<lambda>t. exp ((t - t0) *\<^sub>R A) x0)"

lemma linode_solution_solves_ode:
  "(linode_solution t0 x0 solves_ode (\<lambda>_. A)) UNIV UNIV" "linode_solution t0 x0 t0 = x0"
  by (auto intro!: solves_odeI derivative_eq_intros
    simp: has_vector_derivative_def blinop.bilinear_simps exp_times_scaleR_commute
      has_vderiv_on_def linode_solution_def)

lemma "(linode_solution t0 x0 usolves_ode (\<lambda>_. A) from t0) UNIV UNIV"
  using linode_solution_solves_ode(1)
proof (rule usolves_odeI)
  fix s t1
  assume s0: "s t0 = linode_solution t0 x0 t0"
  assume sol: "(s solves_ode (\<lambda>x. blinop_apply A)) {t0--t1} UNIV"

  then have [derivative_intros]:
    "(s has_derivative (\<lambda>h. h *\<^sub>R A (s t))) (at t within {t0 -- t1})" if "t \<in> {t0 -- t1}" for t
    using that
    by (auto dest!: solves_odeD(1) simp: has_vector_derivative_def has_vderiv_on_def)
  have "((\<lambda>t. exp (-(t - t0) *\<^sub>R A) (s t)) has_derivative (\<lambda>_. 0)) (at t within {t0 -- t1})"
    (is "(?es has_derivative _) _")
    if "t \<in> {t0 -- t1}" for t
    by (auto intro!: derivative_eq_intros that simp: has_vector_derivative_def
      blinop.bilinear_simps)
  from has_derivative_zero_constant[OF convex_closed_segment this]
  obtain c where c: "\<And>t. t \<in> {t0 -- t1} \<Longrightarrow> ?es t = c" by auto
  hence "(exp ((t - t0) *\<^sub>R A) * (exp (-((t - t0) *\<^sub>R A)))) (s t) = exp ((t - t0) *\<^sub>R A) c"
    if "t \<in> {t0 -- t1}" for t
    by (metis (no_types, hide_lams) blinop_apply_times_blinop real_vector.scale_minus_left that)
  then have s_def: "s t = exp ((t - t0) *\<^sub>R A) c" if "t \<in> {t0 -- t1}" for t
    by (simp add: exp_minus_inverse that)
  from s0 s_def
  have "exp ((t0 - t0) *\<^sub>R A) c = x0"
    by (simp add: linode_solution_solves_ode(2))
  hence "c = x0" by (simp add: )
  then show "s t1 = linode_solution t0 x0 t1"
    using s_def[of t1] by (simp add: linode_solution_def)
qed auto

end

end
