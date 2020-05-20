(*  Title:       Examples of hybrid systems verifications
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

subsection \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our
recently described verification components.\<close>

theory HS_VC_PT_Examples
  imports HS_VC_PT

begin


subsubsection \<open> Pendulum \<close>

text \<open> The ODEs @{text "x' t = y t"} and {text "y' t = - x t"} describe the circular motion of
a mass attached to a string looked from above. We use @{text "s$1"} to represent the x-coordinate
and @{text "s$2"} for the y-coordinate. We prove that this motion remains circular. \<close>

abbreviation fpend :: "real^2 \<Rightarrow> real^2" ("f")
  where "f s \<equiv> (\<chi> i. if i = 1 then s$2 else -s$1)"

abbreviation pend_flow :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>")
  where "\<phi> t s \<equiv> (\<chi> i. if i = 1 then s$1 * cos t + s$2 * sin t else - s$1 * sin t + s$2 * cos t)"

\<comment> \<open>Verified by providing the dynamics\<close>

lemma pendulum_dyn: "{s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2} \<le> fb\<^sub>\<F> (EVOL \<phi> G T) {s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2}"
  by force

\<comment> \<open>Verified with differential invariants. \<close>

lemma pendulum_inv: "{s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2} \<le> fb\<^sub>\<F> (x\<acute>= f & G) {s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2}"
  by (auto intro!: diff_invariant_rules poly_derivatives)

\<comment> \<open>Verified with the flow. \<close>

lemma local_flow_pend: "local_flow f UNIV UNIV \<phi>"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
    apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def power2_commute UNIV_2)
  by (auto simp: forall_2 intro!: poly_derivatives)

lemma pendulum_flow: "{s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2} \<le> fb\<^sub>\<F> (x\<acute>= f & G) {s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2}"
  by (force simp: local_flow.ffb_g_ode[OF local_flow_pend])

no_notation fpend ("f")
        and pend_flow ("\<phi>")


subsubsection \<open> Bouncing Ball \<close>

text \<open> A ball is dropped from rest at an initial height @{text "h"}. The motion is described with
the free-fall equations @{text "x' t = v t"} and @{text "v' t = g"} where @{text "g"} is the
constant acceleration due to gravity. The bounce is modelled with a variable assigntment that
flips the velocity, thus it is a completely elastic collision with the ground. We use @{text "s$1"}
to ball's height and @{text "s$2"} for its velocity. We prove that the ball remains above ground
and below its initial resting position. \<close>

abbreviation fball :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("f")
  where "f g s \<equiv> (\<chi> i. if i = 1 then s$2 else g)"

abbreviation ball_flow :: "real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>")
  where "\<phi> g t s \<equiv> (\<chi> i. if i = 1 then g * t ^ 2/2 + s$2 * t + s$1 else g * t + s$2)"

\<comment> \<open>Verified with differential invariants. \<close>

named_theorems bb_real_arith "real arithmetic properties for the bouncing ball."

lemma inv_imp_pos_le[bb_real_arith]:
  assumes "0 > g" and inv: "2 * g * x - 2 * g * h = v * v"
  shows "(x::real) \<le> h"
proof-
  have "v * v = 2 * g * x - 2 * g * h \<and> 0 > g"
    using inv and \<open>0 > g\<close> by auto
  hence obs:"v * v = 2 * g * (x - h) \<and> 0 > g \<and> v * v \<ge> 0"
    using left_diff_distrib mult.commute by (metis zero_le_square)
  hence "(v * v)/(2 * g) = (x - h)"
    by auto
  also from obs have "(v * v)/(2 * g) \<le> 0"
    using divide_nonneg_neg by fastforce
  ultimately have "h - x \<ge> 0"
    by linarith
  thus ?thesis by auto
qed

lemma bouncing_ball_inv: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow>
  {s. s$1 = h \<and> s$2 = 0} \<le> fb\<^sub>\<F>
  (LOOP (
    (x\<acute>=(f g) & (\<lambda> s. s$1 \<ge> 0) DINV (\<lambda>s. 2 * g * s$1 - 2 * g * h - s$2 * s$2 = 0)) ;
    (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip))
  INV (\<lambda>s. 0 \<le> s$1 \<and>2 * g * s$1 - 2 * g * h - s$2 * s$2 = 0))
  {s. 0 \<le> s$1 \<and> s$1 \<le> h}"
  apply(rule ffb_loopI, simp_all)
    apply(force, force simp: bb_real_arith)
  apply(rule ffb_g_odei)
  by (auto intro!: diff_invariant_rules poly_derivatives simp: bb_real_arith)

\<comment> \<open>Verified by providing the dynamics\<close>

lemma inv_conserv_at_ground[bb_real_arith]:
  assumes invar: "2 * g * x = 2 * g * h + v * v"
    and pos: "g * \<tau>\<^sup>2 / 2 + v * \<tau> + (x::real) = 0"
  shows "2 * g * h + (g * \<tau> * (g * \<tau> + v) + v * (g * \<tau> + v)) = 0"
proof-
  from pos have "g * \<tau>\<^sup>2  + 2 * v * \<tau> + 2 * x = 0" by auto
  then have "g\<^sup>2 * \<tau>\<^sup>2  + 2 * g * v * \<tau> + 2 * g * x = 0"
    by (metis (mono_tags, hide_lams) Groups.mult_ac(1,3) mult_zero_right
        monoid_mult_class.power2_eq_square semiring_class.distrib_left)
  hence "g\<^sup>2 * \<tau>\<^sup>2 + 2 * g * v * \<tau> + v\<^sup>2 + 2 * g * h = 0"
    using invar by (simp add: monoid_mult_class.power2_eq_square)
  hence obs: "(g * \<tau> + v)\<^sup>2 + 2 * g * h = 0"
    apply(subst power2_sum) by (metis (no_types, hide_lams) Groups.add_ac(2, 3)
        Groups.mult_ac(2, 3) monoid_mult_class.power2_eq_square nat_distrib(2))
  thus "2 * g * h + (g * \<tau> * (g * \<tau> + v) + v * (g * \<tau> + v)) = 0"
    by (simp add: add.commute distrib_right power2_eq_square)
qed

lemma inv_conserv_at_air[bb_real_arith]:
  assumes invar: "2 * g * x = 2 * g * h + v * v"
  shows "2 * g * (g * \<tau>\<^sup>2 / 2 + v * \<tau> + (x::real)) =
  2 * g * h + (g * \<tau> + v) * (g * \<tau> + v)" (is "?lhs = ?rhs")
proof-
  have "?lhs = g\<^sup>2 * \<tau>\<^sup>2 + 2 * g * v * \<tau> + 2 * g * x"
    by(auto simp: algebra_simps semiring_normalization_rules(29))
  also have "... = g\<^sup>2 * \<tau>\<^sup>2 + 2 * g * v * \<tau> + 2 * g * h + v * v" (is "... = ?middle")
    by(subst invar, simp)
  finally have "?lhs = ?middle".
  moreover
  {have "?rhs = g * g * (\<tau> * \<tau>) + 2 * g * v * \<tau> + 2 * g * h + v * v"
    by (simp add: Groups.mult_ac(2,3) semiring_class.distrib_left)
  also have "... = ?middle"
    by (simp add: semiring_normalization_rules(29))
  finally have "?rhs = ?middle".}
  ultimately show ?thesis by auto
qed

lemma bouncing_ball_dyn: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow>
  {s. s$1 = h \<and> s$2 = 0} \<le> fb\<^sub>\<F>
  (LOOP (
    (EVOL (\<phi> g) (\<lambda> s. s$1 \<ge> 0) T) ;
    (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip))
  INV (\<lambda>s. 0 \<le> s$1 \<and> 2 * g * s$1 = 2 * g * h + s$2 * s$2))
  {s. 0 \<le> s$1 \<and> s$1 \<le> h}"
  by (rule ffb_loopI) (auto simp: bb_real_arith)

\<comment> \<open>Verified with the flow. \<close>

lemma local_flow_ball: "local_flow (f g) UNIV UNIV (\<phi> g)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
    apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def UNIV_2)
  by (auto simp: forall_2 intro!: poly_derivatives)

lemma bouncing_ball_flow: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow>
  {s. s$1 = h \<and> s$2 = 0} \<le> fb\<^sub>\<F>
  (LOOP (
    (x\<acute>=(f g) & (\<lambda> s. s$1 \<ge> 0)) ;
    (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip))
  INV (\<lambda>s. 0 \<le> s$1 \<and> 2 * g * s$1 = 2 * g * h + s$2 * s$2))
  {s. 0 \<le> s$1 \<and> s$1 \<le> h}"
  by (rule ffb_loopI) (auto simp: bb_real_arith local_flow.ffb_g_ode[OF local_flow_ball])

no_notation fball ("f")
        and ball_flow ("\<phi>")


subsubsection \<open> Thermostat \<close>

text \<open> A thermostat has a chronometer, a thermometer and a switch to turn on and off a heater.
At most every @{text "t"} minutes, it sets its chronometer to @{term "0::real"}, it registers
the room temperature, and it turns the heater on (or off) based on this reading. The temperature
follows the ODE @{text "T' = - a * (T - U)"} where @{text "U"} is @{text "L \<ge> 0"} when the heater
is on, and @{text "0"} when it is off. We use @{term "1::4"} to denote the room's temperature,
@{term "2::4"} is time as measured by the thermostat's chronometer, @{term "3::4"} is the
temperature detected by the thermometer, and @{term "4::4"} states whether the heater is on
(@{text "s$4 = 1"}) or off (@{text "s$4 = 0"}). We prove that the thermostat keeps the room's
temperature between @{text "Tmin"} and @{text "Tmax"}. \<close>

abbreviation temp_vec_field :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f a L s \<equiv> (\<chi> i. if i = 2 then 1 else (if i = 1 then - a * (s$1 - L) else 0))"

abbreviation temp_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("\<phi>")
  where "\<phi> a L t s \<equiv> (\<chi> i. if i = 1 then - exp(-a * t) * (L - s$1) + L else
  (if i = 2 then t + s$2 else s$i))"

\<comment> \<open>Verified with the flow. \<close>

lemma norm_diff_temp_dyn: "0 < a \<Longrightarrow> \<parallel>f a L s\<^sub>1 - f a L s\<^sub>2\<parallel> = \<bar>a\<bar> * \<bar>s\<^sub>1$1 - s\<^sub>2$1\<bar>"
proof(simp add: norm_vec_def L2_set_def, unfold UNIV_4, simp)
  assume a1: "0 < a"
  have f2: "\<And>r ra. \<bar>(r::real) + - ra\<bar> = \<bar>ra + - r\<bar>"
    by (metis abs_minus_commute minus_real_def)
  have "\<And>r ra rb. (r::real) * ra + - (r * rb) = r * (ra + - rb)"
    by (metis minus_real_def right_diff_distrib)
  hence "\<bar>a * (s\<^sub>1$1 + - L) + - (a * (s\<^sub>2$1 + - L))\<bar> = a * \<bar>s\<^sub>1$1 + - s\<^sub>2$1\<bar>"
    using a1 by (simp add: abs_mult)
  thus "\<bar>a * (s\<^sub>2$1 - L) - a * (s\<^sub>1$1 - L)\<bar> = a * \<bar>s\<^sub>1$1 - s\<^sub>2$1\<bar>"
    using f2 minus_real_def by presburger
qed

lemma local_lipschitz_temp_dyn:
  assumes "0 < (a::real)"
  shows "local_lipschitz UNIV UNIV (\<lambda>t::real. f a L)"
  apply(unfold local_lipschitz_def lipschitz_on_def dist_norm)
  apply(clarsimp, rule_tac x=1 in exI, clarsimp, rule_tac x=a in exI)
  using assms
  apply(simp_all add: norm_diff_temp_dyn)
  apply(simp add: norm_vec_def L2_set_def, unfold UNIV_4, clarsimp)
  unfolding real_sqrt_abs[symmetric] by (rule real_le_lsqrt) auto

lemma local_flow_temp: "a > 0 \<Longrightarrow> local_flow (f a L) UNIV UNIV (\<phi> a L)"
  by (unfold_locales, auto intro!: poly_derivatives local_lipschitz_temp_dyn simp: forall_4 vec_eq_iff)

lemma temp_dyn_down_real_arith:
  assumes "a > 0" and Thyps: "0 < Tmin" "Tmin \<le> T" "T \<le> Tmax"
    and thyps: "0 \<le> (t::real)" "\<forall>\<tau>\<in>{0..t}. \<tau> \<le> - (ln (Tmin / T) / a) "
  shows "Tmin \<le> exp (-a * t) * T" and "exp (-a * t) * T \<le> Tmax"
proof-
  have "0 \<le> t \<and> t \<le> - (ln (Tmin / T) / a)"
    using thyps by auto
  hence "ln (Tmin / T) \<le> - a * t \<and> - a * t \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "Tmin / T > 0"
    using Thyps by auto
  ultimately have obs: "Tmin / T \<le> exp (-a * t)" "exp (-a * t) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less, simp)
  thus "Tmin \<le> exp (-a * t) * T"
    using Thyps by (simp add: pos_divide_le_eq)
  show "exp (-a * t) * T \<le> Tmax"
    using Thyps mult_left_le_one_le[OF _ exp_ge_zero obs(2), of T]
      less_eq_real_def order_trans_rules(23) by blast
qed

lemma temp_dyn_up_real_arith:
  assumes "a > 0" and Thyps: "Tmin \<le> T" "T \<le> Tmax" "Tmax < (L::real)"
    and thyps: "0 \<le> t" "\<forall>\<tau>\<in>{0..t}. \<tau> \<le> - (ln ((L - Tmax) / (L - T)) / a) "
  shows "L - Tmax \<le> exp (-(a * t)) * (L - T)"
    and "L - exp (-(a * t)) * (L - T) \<le> Tmax"
    and "Tmin \<le> L - exp (-(a * t)) * (L - T)"
proof-
  have "0 \<le> t \<and> t \<le> - (ln ((L - Tmax) / (L - T)) / a)"
    using thyps by auto
  hence "ln ((L - Tmax) / (L - T)) \<le> - a * t \<and> - a * t \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "(L - Tmax) / (L - T) > 0"
    using Thyps by auto
  ultimately have "(L - Tmax) / (L - T) \<le> exp (-a * t) \<and> exp (-a * t) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less)
  moreover have "L - T > 0"
    using Thyps by auto
  ultimately have obs: "(L - Tmax) \<le> exp (-a * t) * (L - T) \<and> exp (-a * t) * (L - T) \<le> (L - T)"
    by (simp add: pos_divide_le_eq)
  thus "(L - Tmax) \<le> exp (-(a * t)) * (L - T)"
    by auto
  thus "L - exp (-(a * t)) * (L - T) \<le> Tmax"
    by auto
  show "Tmin \<le> L - exp (-(a * t)) * (L - T)"
    using Thyps and obs by auto
qed

lemmas ffb_temp_dyn = local_flow.ffb_g_ode_ivl[OF local_flow_temp _ UNIV_I]

lemma thermostat:
  assumes "a > 0" and "0 \<le> t" and "0 < Tmin" and "Tmax < L"
  shows "{s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$4 = 0} \<le> fb\<^sub>\<F>
  (LOOP
    \<comment> \<open>control\<close>
    ((2 ::= (\<lambda>s. 0));(3 ::= (\<lambda>s. s$1));
    (IF (\<lambda>s. s$4 = 0 \<and> s$3 \<le> Tmin + 1) THEN (4 ::= (\<lambda>s.1)) ELSE
    (IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> Tmax - 1) THEN (4 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$4 = 0) THEN (x\<acute>=(f a 0) & (\<lambda>s. s$2 \<le> - (ln (Tmin/s$3))/a) on {0..t} UNIV @ 0)
    ELSE (x\<acute>=(f a L) & (\<lambda>s. s$2 \<le> - (ln ((L-Tmax)/(L-s$3)))/a) on {0..t} UNIV @ 0)) )
  INV (\<lambda>s. Tmin \<le>s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1)))
  {s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax}"
  apply(rule ffb_loopI, simp_all add: ffb_temp_dyn[OF assms(1,2)] le_fun_def, safe)
  using temp_dyn_up_real_arith[OF assms(1) _ _ assms(4), of Tmin]
    and temp_dyn_down_real_arith[OF assms(1,3), of _ Tmax] by auto

no_notation temp_vec_field ("f")
        and temp_flow ("\<phi>")

end