theory Examples_One_Step_Method
imports
  "HOL-ODE-Numerics.ODE_Numerics"
begin

subsection \<open>Example 1\<close>
experiment begin

schematic_goal e1_fas:
  "[1, (X!1)\<^sup>2 - X!0] = interpret_floatariths ?fas X"
  unfolding power2_eq_square\<comment> \<open>TODO: proper affine implementation of power\<close>
  by (reify_floatariths)

concrete_definition e1_fas uses e1_fas

interpretation e1: ode_interpretation true_form UNIV e1_fas "\<lambda>(x, y). (1, y\<^sup>2 - x)::real*real"
  "d::2" for d
  by unfold_locales (auto simp: e1_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def
      mk_ode_ops_def eucl_of_list_prod power2_eq_square intro!: isFDERIV_I)

lemma e1_0: "t \<in> {4 .. 4} \<longrightarrow> (x, y) \<in> {(0, 0) .. (0, 0.71875)} \<longrightarrow>
   t \<in> e1.existence_ivl0 (x, y) \<and> e1.flow0 (x, y) t \<in> {(3.999, -1.96)..(4, -1.9)}"
  by (tactic \<open>ode_bnds_tac @{thms e1_fas_def} 30 20 7 12 [(0, 1, "0x000000")] (* "out_e1_0.out" *) "" @{context} 1\<close>)

lemma e1_1: "t \<in> {4 .. 4} \<longrightarrow> (x, y) \<in> {(0, 0.71875) .. (0, 0.71875)} \<longrightarrow>
   t \<in> e1.existence_ivl0 (x, y) \<and> e1.flow0 (x, y) t \<in> {(3.999, -1.921)..(4, -1.919)}"
  by (tactic \<open>ode_bnds_tac @{thms e1_fas_def} 30 20 7 12 [(0, 1, "0xff0000")] (* "out_e1_1.out" *) "" @{context} 1\<close>)

end


subsection \<open>Example Exponential\<close>
experiment begin

schematic_goal exp_fas:
  "[1, (X!1)] = interpret_floatariths ?fas X"
  by (reify_floatariths)
concrete_definition exp_fas uses exp_fas

interpretation exp_ivp: ode_interpretation true_form UNIV exp_fas
  "\<lambda>(t::real, x). (1, x::real)" "one::2"
  by standard
    (auto simp: exp_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def
      mk_ode_ops_def eucl_of_list_prod power2_eq_square intro!: isFDERIV_I)

subsubsection \<open>connection to exponential function\<close>

lemma exp_ivp_existence_ivl0:
  "exp_ivp.existence_ivl0 p = UNIV"
  by (rule exp_ivp.existence_ivl_eq_domain)
     (auto intro!: exI[where x=1] order_trans[OF norm_Pair_le] order_trans[OF _ norm_snd_le])

lemma exp_eq_exp_ivp_aux:
  "exp_ivp.flow0 (0, 1) x = (x, exp x)"
  apply (rule exp_ivp.flow_unique[where phi="\<lambda>x. (x, exp x)"])
  unfolding exp_ivp_existence_ivl0
  by (auto simp: has_vector_derivative_def intro!: derivative_eq_intros)

lemma ex_eq_exp_ivp: "exp x = snd (exp_ivp.flow0 (0, 1) x)"
  unfolding exp_eq_exp_ivp_aux by simp

text \<open>concrete example\<close>

lemma exp_ode_result:
  "t \<in> {1 .. 1} \<longrightarrow> (s, x) \<in> {(0, 1) .. (0, 1)} \<longrightarrow>
  t \<in> exp_ivp.existence_ivl0 (s, x) \<and>
  exp_ivp.flow0 (s, x) t \<in> {(0.99, 2.718281) .. (1, 2.718284)}"
  by (tactic \<open>ode_bnds_tac @{thms exp_fas_def} 30 20 7 20 [(0, 1, "0x000000")] (* "out_exp.out" *) "" @{context} 1\<close>)

lemma exp1: "exp 1 \<in> {2.718281 .. 2.718284::real}"
  using exp_ode_result[of 1 0 1]
  by (auto simp: exp_eq_exp_ivp_aux)

end


subsection \<open>Van der Pol\<close>
experiment begin

schematic_goal vdp_fas:
  "[X!1, X!1 * (1 - (X!0)\<^sup>2) - X!0] = interpret_floatariths ?fas X"
  unfolding power2_eq_square\<comment> \<open>TODO: proper affine implementation of power\<close>
  by (reify_floatariths)

concrete_definition vdp_fas uses vdp_fas

interpretation vdp: ode_interpretation true_form UNIV vdp_fas "\<lambda>(x, y). (y, y * (1 - x\<^sup>2) - x)::real*real"
  "n::2" for n
  by standard
    (auto simp: vdp_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def
      mk_ode_ops_def eucl_of_list_prod power2_eq_square intro!: isFDERIV_I)

lemma vdp_c0: "t \<in> point_ivl 7 \<longrightarrow> (x, y) \<in> point_ivl (1.4, 2.4) \<longrightarrow>
   t \<in> vdp.existence_ivl0 (x, y) \<and> vdp.flow0 (x, y) t \<in> {(1.870, 0.9887) .. (1.875, 1.001)}"
  by (tactic \<open>ode_bnds_tac @{thms vdp_fas_def} 30 35 9 14 [(0, 1, "0x000000")] (* "out_vdp_c0.out" *) "" @{context} 1\<close>)

lemma vdp_c1: "t \<in> point_ivl 7 \<longrightarrow> (x, y) \<in> point_ivl (1.4, 2.4) \<longrightarrow>
   t \<in> vdp.existence_ivl0 (x, y) \<and>
   vdp.flow0 (x, y) t \<in> {(1.870, 0.9887) .. (1.875, 1.001)} \<and>
    vdp.Dflow (x, y) t o\<^sub>L blinfun_of_list [1,0, 0,1] \<in>
      vdp.blinfuns_of_lvivl ([-0.197,-0.399, 0.835, 1.71],
                             [-0.189, -0.387, 0.858, 1.75])"
  by (tactic \<open>ode'_bnds_tac @{thms vdp_fas_def} 30 80 40 14
    [(0, 1, "0x000000", [0,1])] ["0x7f0000", "0x00007f"] (* "out_vdp_c1.out" *) "" @{context} 1\<close>)
end

subsection \<open>Example Classical Lorenz Equations\<close>
experiment begin

schematic_goal
  lorenz_fas:
  "[10 * (X!1 - X!0),
    X!0 * (28 - X!2) - X!1,
    X!0 * X!1 - 8 /3 * X!2] =
  interpret_floatariths ?fas X"
  by (reify_floatariths)
concrete_definition lorenz_fas uses lorenz_fas

interpretation lorenz: ode_interpretation true_form UNIV lorenz_fas
  "\<lambda>(x, y, z). (10 * (y - x), x * (28 - z) - y, x * y - 8 / 3 * z)
    ::real*real*real"
  "three::3"
  by standard
    (auto simp: lorenz_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def
      mk_ode_ops_def eucl_of_list_prod power2_eq_square intro!: isFDERIV_I)

text \<open>Taken from "A database of rigorous and high-precision periodic orbits of the Lorenz model" (2015)
  by Barrio, Dena, Tucker\<close>
lemma lorenz_c0: "t \<in> point_ivl 1.558652210 \<longrightarrow> (x, y, z) \<in> point_ivl ( -2.147367631, 2.078048211, 27) \<longrightarrow>
   t \<in> lorenz.existence_ivl0 (x, y, z) \<and> lorenz.flow0 (x, y, z) t \<in> {(-2.1515, 2.0738, 26.992) .. (-2.1434, 2.0824, 27.009)}"
  by (tactic \<open>ode_bnds_tac @{thms lorenz_fas_def} 30 35 9 16
    [(0, 1, "0x7f0000"), (0, 2, "0x00007f")] (* "out_lorenz_c0.out" *) "" @{context} 1\<close>)

lemma lorenz_c1: "t \<in> point_ivl (FloatR 52299689 (- 25) \<comment> \<open>for C1-info, the target time needs to be a float\<close>) \<longrightarrow>
  (x, y, z) \<in> point_ivl ( -2.147367631, 2.078048211, 27) \<longrightarrow>
   t \<in> lorenz.existence_ivl0 (x, y, z) \<and>
   lorenz.flow0 (x, y, z) t \<in> {(-2.158, 2.064, 26.98) .. (-2.137, 2.092, 27.02)} \<and>
    lorenz.Dflow (x, y, z) t o\<^sub>L blinfun_of_list [1,0,0, 0,1,0, 0,0,1] \<in>
      lorenz.blinfuns_of_lvivl ([-0.535,-1.15,-0.794, 1.49,4.01,0.651, 2.71,6.85,2.11],
                                [-0.479,-1.03,-0.751, 1.58,4.14,0.703, 2.82,7.00,2.19])"
  by (tactic \<open>ode'_bnds_tac @{thms lorenz_fas_def} 30 80 40 16
    [(0, 1, "0x000000", [0,1,2]), (0, 2, "0x7f7f7f", [0,1,2])] ["0x7f0000", "0x007f00", "0x00007f"]
      (* "out_lorenz_c1.out" *) "" @{context} 1\<close>)
end


subsection \<open>Bessel Function inspired example\<close>
text \<open>\label{sec:bessel}\<close>
experiment begin

unbundle floatarith_notation

text \<open>encoding a constant parameter and higher derivatives in the ode...\<close>

schematic_goal bessel_fas:
  "[0, -1, -(X!3), (((X!1)\<^sup>2 - (X!0)\<^sup>2) * X!2 + (X!1) * (X!3)) / (X!1)\<^sup>2] = interpret_floatariths ?fas X"
  unfolding power2_eq_square\<comment> \<open>TODO: proper affine implementation of power\<close>
  by (reify_floatariths)
concrete_definition bessel_fas uses bessel_fas

interpretation bessel: ode_interpretation "Less (Var 1) (Num 0)" "{(mu, s, _, _). s < 0}"
  bessel_fas
  "\<lambda>(mu::real, s::real, x::real, x'::real).
  (0::real,
  -1::real,
  -x'::real,
  (((s\<^sup>2 - mu\<^sup>2) * x + s * x') / s\<^sup>2))"
  "four::4"
  by standard
    (auto simp: bessel_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def inverse_eq_divide
      mk_ode_ops_def eucl_of_list_prod power2_eq_square intro!: isFDERIV_I)

definition "J0 = 0.765197686557966551449717526103"
definition "J0' = 0.440050585744933515959682203719"

lemma bessel_result:
  "t \<in> {10 .. 10} \<longrightarrow>
   (x, y, j0, j0') \<in> {(0, -1, 0.765197686557966551449717526103, 0.440050585744933515959682203719) ..
      (0, -1, 0.765197686557966551449717526103, 0.440050585744933515959682203719)} \<longrightarrow>
   t \<in> bessel.existence_ivl0 (x, y, j0, j0') \<and>
                bessel.flow0 (x, y, j0, j0') t \<in> {(0, -11.01, -0.18, -0.185) .. (0, -11, -0.165, -0.169)}"
  by (tactic \<open>ode_bnds_tac @{thms bessel_fas_def} 30 20 7 12
    [(1, 2, "0x007f00"), (1, 3, "0x00007f")] (* "out_bessel.out" *) "" @{context} 1\<close>)
end

subsection \<open> Oil reservoir in Affine arithmetic \<close>
text \<open>\label{sec:exampleoil}\<close>
experiment begin

schematic_goal oil_fas:
  "[X!1, (X!1)\<^sup>2 - 3 / (0.001 + (X!0)\<^sup>2)] = interpret_floatariths ?fas X"
  unfolding power2_eq_square\<comment> \<open>TODO: proper affine implementation of power\<close>
  by (reify_floatariths)

concrete_definition oil_fas uses oil_fas

lemma oil_deriv_ok: fixes y::real
shows "1 / 1000 + y*y = 0 \<longleftrightarrow> False"
proof -
  have "1 / 1000 + y*y > 0"
    by (auto intro!: add_pos_nonneg)
  thus ?thesis by auto
qed

interpretation oil: ode_interpretation true_form UNIV oil_fas
  "\<lambda>(y, z). (z, z\<^sup>2 - 3 / (0.001 + y\<^sup>2))::real*real" "two::2"
  by standard
    (auto simp: oil_fas_def oil_deriv_ok less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def inverse_eq_divide
      mk_ode_ops_def eucl_of_list_prod isDERIV_Power_iff power2_eq_square intro!: isFDERIV_I)

theorem oil_20:
  "t \<in> {50 .. 50} \<longrightarrow> (x, y) \<in> {(10, 0) .. (10, 0)} \<longrightarrow>
   t \<in> oil.existence_ivl0 (x, y) \<and> oil.flow0 (x, y) t \<in> {(-8.310, -0.2252) .. (-8.257, -0.2236)}"
  by (tactic \<open>ode_bnds_tac @{thms oil_fas_def} 30 20 7 20 [(0, 1, "0x000000")] (* "out_oil_20.out" *) "" @{context} 1\<close>)

theorem oil_30:
  "t \<in> {50 .. 50} \<longrightarrow> (x, y) \<in> {(10, 0) .. (10, 0)} \<longrightarrow>
   t \<in> oil.existence_ivl0 (x, y) \<and> oil.flow0 (x, y) t \<in> {(-8.279, -0.2246) .. (-8.276, -0.2245)}"
  by (tactic \<open>ode_bnds_tac @{thms oil_fas_def} 30 20 7 30 [(0, 1, "0xff0000")] (* "out_oil_30.out" *) "" @{context} 1\<close>)
end

subsection \<open>Example V in Walter's textbook~\cite{walter}\<close>
experiment begin

schematic_goal e3_fas:
  "[1, (X!1)\<^sup>2 + (X!0)\<^sup>2] = interpret_floatariths ?fas X"
  unfolding power2_eq_square\<comment> \<open>TODO: proper affine implementation of power\<close>
  by (reify_floatariths)
concrete_definition e3_fas uses e3_fas

interpretation e3: ode_interpretation true_form UNIV e3_fas "\<lambda>(t, x). (1, x\<^sup>2 + t\<^sup>2)::real*real"
  "d::2" for d
  by standard
    (auto simp: e3_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def
      mk_ode_ops_def eucl_of_list_prod power2_eq_square intro!: isFDERIV_I)

lemma e3_flow_mem:
  "t \<in> {0.125 .. 0.125} \<longrightarrow> (s, x) \<in> {(0, 1) .. (0, 1)} \<longrightarrow>
  t \<in> e3.existence_ivl0 (s, x) \<and> (e3.flow0 (s, x) t \<in> {(0.124, 1.14347) .. (0.126, 1.14376)})"
  by (tactic \<open>ode_bnds_tac @{thms e3_fas_def} 30 20 7 11 [(0, 1, "0x000000")] (* "out_e2.out" *) "" @{context} 1\<close>)

subsubsection \<open>Walter's analytical obtained by in section 9, Example V.\<close>

lemma cos_neq_zeroI:
  assumes "-pi / 2 < x" "x < pi / 2"
  shows "cos x \<noteq> 0"
  using assms div2_less_self
  by (fastforce simp: cos_zero_iff)

lemma quadratic_real_max_eq:
  fixes a b c x::real
  defines "xm \<equiv> -b / (2 * a)"
  shows "a < 0 \<Longrightarrow> a * x\<^sup>2 + b * x + c \<le> a * xm\<^sup>2 + b * xm + c"
  unfolding xm_def
  by (sos "(((((A<0 * (A<1 * A<2)) * R<1) + ((A<2 * R<1) * (R<1 * [a^2]^2)))) &
    ((((A<0 * (A<1 * A<2)) * R<1) + ((R<1 * (R<1/2 * [2*a^4*x + a^3*b]^2)) +
    ((A<0 * (A<1 * R<1)) * (R<1/2 * [2*a^2*x + a*b]^2))))))")

definition "f = (\<lambda>t x. t\<^sup>2 + x\<^sup>2::real)"

lemma ll: "local_lipschitz UNIV UNIV f"
  by (rule c1_implies_local_lipschitz[where f'="\<lambda>(t, x). blinfun_scaleR_left (blinfun_scaleR_left id_blinfun 2) x"])
    (auto intro!: continuous_intros derivative_eq_intros ext simp: f_def split_beta' blinfun.bilinear_simps)

lemma cont: "continuous_on UNIV (\<lambda>t. f t x)"
  by (auto intro!: continuous_intros simp: f_def)

interpretation ll_on_open_real UNIV f UNIV by unfold_locales (auto intro!: ll cont)

definition f1::"real \<Rightarrow> real \<Rightarrow> real" where "f1 t x \<equiv> x\<^sup>2"
definition v::"real \<Rightarrow> real" where "v t = 1 / (1 - t)"

lemma v: "(v solves_ode f1) {0..<1} UNIV" and "v 0 = 1"
  by (auto intro!: solves_odeI derivative_eq_intros ext
    simp: v_def has_vderiv_on_def f1_def has_vector_derivative_def divide_simps power2_eq_square)

lemma
  lower_bound:
  assumes y: "(y solves_ode f) {0 ..< t1} UNIV"
    and iv: "y 0 = 1"
    and t: "t1 < 1" "t \<in> {0 ..< t1}"
  shows "v t \<le> y t"
  using y[THEN solves_ode_on_subset] solves_odeD(1)[OF v, THEN has_vderiv_on_subset]
  apply (rule lower_solution[where ?t0.0 = 0])
  using t
  by (auto simp: f1_def f_def v_def iv)

definition f2::"real \<Rightarrow> real \<Rightarrow> real" where "f2 t x \<equiv> 1 + x\<^sup>2"
definition w::"real \<Rightarrow> real" where "w t = tan (t + pi / 4)"

lemma w: "(w solves_ode f2) {0..<pi/4} UNIV" and "w 0 = 1"
  by (auto intro!: solves_odeI derivative_eq_intros ext
    simp: w_def has_vderiv_on_def f2_def has_vector_derivative_def cos_neq_zeroI
      tan_45 tan_sec divide_simps)

lemma upper_bound:
  assumes y: "(y solves_ode f) {0 ..< t1} UNIV"
    and iv: "y 0 = 1"
    and t: "t1 < pi / 4" "t \<in> {0 ..< t1}"
  shows "y t \<le> w t"
  using y[THEN solves_ode_on_subset] solves_odeD(1)[OF w,THEN has_vderiv_on_subset]
  apply (rule upper_solution[where ?t0.0 = 0])
  using t pi_less_4
  by (auto simp: f2_def f_def w_def iv abs_square_less_1 tan_45)

context
  fixes a::real
  assumes a: "a > 1"
  assumes cond: "1 < 16 * a\<^sup>2 * (a - 1)"
begin

definition w1::"real \<Rightarrow> real" where "w1 t = 1 / (1 - a * t)"
definition w1'::"real \<Rightarrow> real" where "w1' t = a / ((1 - a * t)\<^sup>2)"

lemma w1_lower:
  assumes s: "s < 1 / a" "0 < s"
  shows "f s (w1 s) < w1' s"
proof -
  define smax where "smax \<equiv> 1 / (2 * a)"
  have "a - 1 > (1 - a * s)\<^sup>2 * s\<^sup>2"
  proof -
    have "sqrt ((1 - a * s)\<^sup>2 * s\<^sup>2) = (1 - a * s) * s"
      using a s
      by (auto simp: power_mult_distrib[symmetric] algebra_simps divide_simps
        split: if_split_asm)
    also have "\<dots> = (- a) * s\<^sup>2 + 1 * s + 0" by (simp add: algebra_simps power2_eq_square)
    also have "\<dots> \<le> (1 - a * smax) * smax"
      apply (rule order_trans[OF quadratic_real_max_eq])
      using a s
      by (auto simp: smax_def divide_simps algebra_simps power2_eq_square)
    finally have "((1 - a * s)\<^sup>2 * s\<^sup>2) \<le> (1 - a * smax)\<^sup>2 * smax\<^sup>2"
      unfolding power_mult_distrib[symmetric]
      by (simp add: sqrt_le_D)
    also have "\<dots> < a - 1"
      using a s cond
      by (auto simp add: smax_def power2_eq_square algebra_simps  divide_simps split: if_splits)
    finally show ?thesis .
  qed
  then have "s\<^sup>2 < (a - 1) / (1 - a * s)\<^sup>2"
    using a s
    by (auto simp: divide_simps algebra_simps)
  then have "s\<^sup>2 + (1 / (1 - a * s))\<^sup>2 < a / (1 - a * s)\<^sup>2"
    by (simp add: diff_divide_distrib algebra_simps power_one_over)
  then show ?thesis by (simp add: w1_def w1'_def f_def)
qed

lemma w1: "(w1 has_vderiv_on w1') {0..<1/a}"
  by (auto intro!: derivative_eq_intros split: if_splits
    simp: w1_def w1'_def has_vderiv_on_def has_vector_derivative_def
      algebra_simps divide_simps power2_eq_square)

lemma upper_bound1:
  assumes y: "(y solves_ode f) {0 ..< t1} UNIV"
    and iv: "y 0 = 1"
    and t: "t1 < 1 / a" "t \<in> {0 ..< t1}"
  shows "y t \<le> w1 t"
proof -
  have less_one: "s * a < 1" if a1: "s < t1" and a2: "t1 * a < 1" for s
  proof -
    have "0 < a"
      using a by linarith
    then have "a * s \<le> t1 * a"
      using a1 by (metis (no_types) less_eq_real_def mult.commute real_mult_le_cancel_iff2)
    then have "a * s < 1"
      using a2 by linarith
    then show ?thesis
      by (metis mult.commute)
  qed
  show ?thesis
    using y[THEN solves_ode_on_subset] w1[THEN has_vderiv_on_subset] w1_lower
    apply (rule upper_solution[where ?t0.0 = 0 and S = "{0 ..< t1}"])
    using t a
    by (auto simp: less_one w1_def f_def w1'_def iv divide_simps)
qed

end

definition w16::"real \<Rightarrow> real" where "w16 t = 16 / (16 - 17 * t)"

lemma upper_bound16:
  assumes y: "(y solves_ode f) {0 ..< t1} UNIV"
    and iv: "y 0 = 1"
    and t: "t1 < 16 / 17" "t \<in> {0 ..< t1}"
  shows "y t \<le> w16 t"
  using upper_bound1[of "17/16" y t1 t] assms
  by (simp add: divide_simps w1_def w16_def)

lemma approx_lower_bound:
  "1.142857139 \<le> v 0.125"
  unfolding v_def
  by (approximation 40)

lemma approx_upper_bound:
  "w 0.125 \<le> 1.287426955"
  unfolding w_def
  by (approximation 40)

lemma approx_upper_bound16:
  "w16 0.125 \<le> 1.153153155"
  unfolding w16_def
  by (approximation 40)

end

subsection \<open>Building\<close>
experiment begin

text \<open>Benchmark from the ARCH friendly competition: group AFF. This example is out of the scope of
the current ODE solver: dimension is very high, and without matrix exponential, the ODE solver is
too unstable.\<close>

definition "x1'  x == x ! 25"
definition "x2'  x == x ! 26"
definition "x3'  x == x ! 27"
definition "x4'  x == x ! 28"
definition "x5'  x == x ! 29"
definition "x6'  x == x ! 30"
definition "x7'  x == x ! 31"
definition "x8'  x == x ! 32"
definition "x9'  x == x ! 33"
definition "x10' x == x ! 34"
definition "x11' x == x ! 35"
definition "x12' x == x ! 36"
definition "x13' x == x ! 37"
definition "x14' x == x ! 38"
definition "x15' x == x ! 39"
definition "x16' x == x ! 40"
definition "x17' x == x ! 41"
definition "x18' x == x ! 42"
definition "x19' x == x ! 43"
definition "x20' x == x ! 44"
definition "x21' x == x ! 45"
definition "x22' x == x ! 46"
definition "x23' x == x ! 47"
definition "x24' x == x ! 48"
definition "x25' x == 0.013697*(x!49) - 606.16*x!1 + 34.67*x!2 - 5.0432*x!3 - 734.04*x!4 + 124.55*x!5 - 302.91*x!6 - 98.21*x!7 - 2.204*x!8 - 10.668*x!9 - 41.864*x!10 + 8.1784*x!11 + 51.36*x!12 - 10.956*x!13 - 2.3086*x!14 - 11.998*x!15 - 42.003*x!16 + 4.9418*x!17 - 1.5216*x!18 - 10.35*x!19 + 8.6969*x!20 + 14.96*x!21 + 37.885*x!22 - 24.546*x!23 - 19.3*x!24 - 1.1333*x!25 + 0.036523*x!26 - 0.0053128*x!27 - 0.77328*x!28 + 0.13121*x!29 - 0.3191*x!30 - 0.10346*x!31 - 0.0023218*x!32 - 0.011238*x!33 - 0.044102*x!34 + 0.0086155*x!35 + 0.054106*x!36 - 0.011541*x!37 - 0.002432*x!38 - 0.012639*x!39 - 0.044248*x!40 + 0.0052059*x!41 - 0.0016029*x!42 - 0.010904*x!43 + 0.0091618*x!44 + 0.01576*x!45 + 0.03991*x!46 - 0.025858*x!47 - 0.020331*x!48"
definition "x26' x == 33.51*x!1 - 664.52*x!2 + 79.773*x!3 + 207.45*x!4 + 829.03*x!5 + 94.055*x!6 - 4.3133*x!7 - 136.48*x!8 + 16.276*x!9 + 28.243*x!10 - 76.936*x!11 - 0.55452*x!12 + 30.931*x!13 + 51.904*x!14 + 11.87*x!15 + 9.6948*x!16 - 15.613*x!17 + 15.14*x!18 + 7.6133*x!19 - 5.7122*x!20 + 3.7841*x!21 - 21.172*x!22 - 29.014*x!23 + 10.245*x!24 + 0.035301*x!25 - 1.1948*x!26 + 0.084037*x!27 + 0.21854*x!28 + 0.87334*x!29 + 0.099082*x!30 - 0.0045438*x!31 - 0.14378*x!32 + 0.017146*x!33 + 0.029753*x!34 - 0.081048*x!35 - 0.00058416*x!36 + 0.032585*x!37 + 0.054679*x!38 + 0.012505*x!39 + 0.010213*x!40 - 0.016447*x!41 + 0.01595*x!42 + 0.0080202*x!43 - 0.0060176*x!44 + 0.0039864*x!45 - 0.022303*x!46 - 0.030565*x!47 + 0.010792*x!48"
definition "x27' x == 76.572*x!2 - 3.4577*x!1 - 799.41*x!3 - 347.78*x!4 - 142.59*x!5 + 867.7*x!6 - 165.08*x!7 + 36.992*x!8 + 91.256*x!9 - 66.266*x!10 + 26.434*x!11 + 39.519*x!12 + 67.373*x!13 - 32.177*x!14 + 17.164*x!15 + 133.45*x!16 + 34.378*x!17 + 6.5652*x!18 + 27.869*x!19 - 51.473*x!20 + 41.979*x!21 - 44.928*x!22 + 34.417*x!23 + 30.824*x!24 - 0.0036425*x!25 + 0.080665*x!26 - 1.3369*x!27 - 0.36637*x!28 - 0.15021*x!29 + 0.91408*x!30 - 0.17391*x!31 + 0.038969*x!32 + 0.096134*x!33 - 0.069808*x!34 + 0.027847*x!35 + 0.041632*x!36 + 0.070975*x!37 - 0.033897*x!38 + 0.018082*x!39 + 0.14058*x!40 + 0.036215*x!41 + 0.0069161*x!42 + 0.029358*x!43 - 0.054224*x!44 + 0.044223*x!45 - 0.04733*x!46 + 0.036257*x!47 + 0.032471*x!48"
definition "x28' x == 206.8*x!2 - 734.86*x!1 - 348.32*x!3 - 1910.4*x!4 - 135.41*x!5 - 218.05*x!6 - 1130.0*x!7 + 263.61*x!8 - 178.6*x!9 - 285.02*x!10 + 65.125*x!11 + 125.09*x!12 - 78.164*x!13 - 2.0288*x!14 + 11.414*x!15 - 54.481*x!16 - 17.625*x!17 - 14.273*x!18 - 13.334*x!19 + 11.514*x!20 + 88.076*x!21 + 56.304*x!22 - 12.53*x!23 + 19.497*x!24 - 0.77414*x!25 + 0.21785*x!26 - 0.36694*x!27 - 2.5072*x!28 - 0.14264*x!29 - 0.2297*x!30 - 1.1904*x!31 + 0.2777*x!32 - 0.18815*x!33 - 0.30026*x!34 + 0.068606*x!35 + 0.13177*x!36 - 0.082342*x!37 - 0.0021372*x!38 + 0.012024*x!39 - 0.057393*x!40 - 0.018567*x!41 - 0.015036*x!42 - 0.014047*x!43 + 0.012129*x!44 + 0.092784*x!45 + 0.059314*x!46 - 0.013199*x!47 + 0.020539*x!48"
definition "x29' x == 126.41*x!1 + 830.41*x!2 - 142.11*x!3 - 134.84*x!4 - 1968.7*x!5 + 54.561*x!6 + 141.8*x!7 + 1183.9*x!8 + 118.23*x!9 - 32.897*x!10 + 295.19*x!11 - 13.727*x!12 - 6.9809*x!13 - 150.49*x!14 - 16.631*x!15 + 76.503*x!16 + 25.453*x!17 + 26.848*x!18 + 8.696*x!19 - 20.18*x!20 - 16.511*x!21 + 8.533*x!22 + 112.09*x!23 + 9.1024*x!24 + 0.13317*x!25 + 0.8748*x!26 - 0.14971*x!27 - 0.14205*x!28 - 2.5687*x!29 + 0.057478*x!30 + 0.14938*x!31 + 1.2472*x!32 + 0.12455*x!33 - 0.034656*x!34 + 0.31097*x!35 - 0.014461*x!36 - 0.0073541*x!37 - 0.15853*x!38 - 0.01752*x!39 + 0.080592*x!40 + 0.026813*x!41 + 0.028283*x!42 + 0.0091609*x!43 - 0.021259*x!44 - 0.017394*x!45 + 0.0089891*x!46 + 0.11808*x!47 + 0.009589*x!48"
definition "x30' x == 89.14*x!2 - 308.62*x!1 + 845.85*x!3 - 220.15*x!4 + 49.494*x!5 - 2326.8*x!6 + 132.76*x!7 + 67.169*x!8 - 1400.6*x!9 + 24.168*x!10 + 24.278*x!11 - 85.266*x!12 - 294.4*x!13 + 127.92*x!14 - 24.456*x!15 - 379.06*x!16 - 100.16*x!17 - 46.537*x!18 - 67.411*x!19 + 169.3*x!20 - 100.19*x!21 + 200.07*x!22 - 126.91*x!23 - 44.045*x!24 - 0.32511*x!25 + 0.093904*x!26 + 0.89106*x!27 - 0.23192*x!28 + 0.052139*x!29 - 2.9459*x!30 + 0.13986*x!31 + 0.07076*x!32 - 1.4755*x!33 + 0.02546*x!34 + 0.025576*x!35 - 0.089824*x!36 - 0.31014*x!37 + 0.13476*x!38 - 0.025763*x!39 - 0.39932*x!40 - 0.10551*x!41 - 0.049024*x!42 - 0.071015*x!43 + 0.17835*x!44 - 0.10555*x!45 + 0.21077*x!46 - 0.13369*x!47 - 0.046399*x!48"
definition "x31' x == 140.17*x!5 - 3.2644*x!2 - 166.03*x!3 - 1130.1*x!4 - 97.135*x!1 + 149.9*x!6 - 2042.2*x!7 + 77.153*x!8 + 122.7*x!9 - 1223.6*x!10 - 66.505*x!11 + 249.18*x!12 - 16.632*x!13 + 2.6274*x!14 + 56.399*x!15 - 46.871*x!16 - 118.4*x!17 - 62.011*x!18 - 2.1658*x!19 - 30.269*x!20 + 130.25*x!21 + 5.2191*x!22 - 24.931*x!23 + 6.3303*x!24 - 0.10233*x!25 - 0.0034389*x!26 - 0.17491*x!27 - 1.1905*x!28 + 0.14767*x!29 + 0.15792*x!30 - 2.6461*x!31 + 0.081277*x!32 + 0.12926*x!33 - 1.289*x!34 - 0.07006*x!35 + 0.2625*x!36 - 0.01752*x!37 + 0.0027678*x!38 + 0.059414*x!39 - 0.049377*x!40 - 0.12472*x!41 - 0.065326*x!42 - 0.0022816*x!43 - 0.031887*x!44 + 0.13721*x!45 + 0.005498*x!46 - 0.026264*x!47 + 0.0066687*x!48"
definition "x32' x == 34.596*x!3 - 138.29*x!2 - 2.5435*x!1 + 264.02*x!4 + 1185.0*x!5 + 58.931*x!6 + 77.078*x!7 - 2124.4*x!8 - 54.178*x!9 + 240.2*x!10 - 1279.6*x!11 + 14.033*x!12 + 37.313*x!13 + 238.99*x!14 + 1.7648*x!15 - 96.468*x!16 + 33.324*x!17 - 103.99*x!18 - 129.69*x!19 + 35.961*x!20 + 34.916*x!21 - 10.09*x!22 - 99.84*x!23 - 13.713*x!24 - 0.0026795*x!25 - 0.14568*x!26 + 0.036445*x!27 + 0.27814*x!28 + 1.2484*x!29 + 0.062081*x!30 + 0.081198*x!31 - 2.7327*x!32 - 0.057074*x!33 + 0.25304*x!34 - 1.348*x!35 + 0.014783*x!36 + 0.039308*x!37 + 0.25177*x!38 + 0.0018592*x!39 - 0.10162*x!40 + 0.035106*x!41 - 0.10955*x!42 - 0.13662*x!43 + 0.037884*x!44 + 0.036783*x!45 - 0.010629*x!46 - 0.10518*x!47 - 0.014446*x!48"
definition "x33' x == 54.576*x!3 - 4.3846*x!2 - 11.068*x!1 - 167.43*x!4 + 119.06*x!5 - 1413.1*x!6 + 116.3*x!7 - 50.978*x!8 - 2668.8*x!9 + 58.12*x!10 + 61.221*x!11 - 299.51*x!12 - 1455.4*x!13 + 600.59*x!14 - 14.962*x!15 - 609.81*x!16 - 179.98*x!17 - 140.89*x!18 - 67.425*x!19 + 261.44*x!20 - 215.8*x!21 + 374.46*x!22 - 267.83*x!23 - 167.39*x!24 - 0.01166*x!25 - 0.004619*x!26 + 0.057493*x!27 - 0.17638*x!28 + 0.12543*x!29 - 1.4886*x!30 + 0.12251*x!31 - 0.053703*x!32 - 3.3062*x!33 + 0.061226*x!34 + 0.064493*x!35 - 0.31552*x!36 - 1.5332*x!37 + 0.63269*x!38 - 0.015762*x!39 - 0.6424*x!40 - 0.1896*x!41 - 0.14842*x!42 - 0.071029*x!43 + 0.27541*x!44 - 0.22734*x!45 + 0.39448*x!46 - 0.28215*x!47 - 0.17634*x!48"
definition "x34' x == 29.028*x!2 - 42.219*x!1 - 59.833*x!3 - 284.78*x!4 - 31.96*x!5 + 16.189*x!6 - 1220.6*x!7 + 238.17*x!8 + 45.965*x!9 - 2290.9*x!10 + 219.74*x!11 + 1329.3*x!12 - 104.55*x!13 - 231.45*x!14 + 196.73*x!15 - 91.293*x!16 - 418.1*x!17 - 203.17*x!18 + 77.147*x!19 - 64.407*x!20 + 127.6*x!21 - 66.422*x!22 + 17.647*x!23 + 14.772*x!24 - 0.044476*x!25 + 0.03058*x!26 - 0.063031*x!27 - 0.3*x!28 - 0.033668*x!29 + 0.017054*x!30 - 1.2858*x!31 + 0.2509*x!32 + 0.048422*x!33 - 2.9081*x!34 + 0.23149*x!35 + 1.4003*x!36 - 0.11014*x!37 - 0.24382*x!38 + 0.20725*x!39 - 0.096173*x!40 - 0.44045*x!41 - 0.21403*x!42 + 0.08127*x!43 - 0.06785*x!44 + 0.13442*x!45 - 0.069972*x!46 + 0.01859*x!47 + 0.015562*x!48"
definition "x35' x == 5.3147*x!1 - 77.32*x!2 + 33.098*x!3 + 62.873*x!4 + 295.95*x!5 + 11.239*x!6 - 66.808*x!7 - 1279.2*x!8 + 57.198*x!9 + 221.07*x!10 - 2387.6*x!11 + 120.01*x!12 + 572.58*x!13 + 1229.1*x!14 + 124.63*x!15 - 56.089*x!16 + 180.3*x!17 - 312.48*x!18 - 445.95*x!19 - 24.274*x!20 + 86.343*x!21 - 2.8317*x!22 - 45.574*x!23 - 33.346*x!24 + 0.0055988*x!25 - 0.081453*x!26 + 0.034867*x!27 + 0.066234*x!28 + 0.31177*x!29 + 0.011839*x!30 - 0.070379*x!31 - 1.3476*x!32 + 0.060255*x!33 + 0.23288*x!34 - 3.0099*x!35 + 0.12643*x!36 + 0.60318*x!37 + 1.2948*x!38 + 0.13129*x!39 - 0.059087*x!40 + 0.18994*x!41 - 0.32918*x!42 - 0.46979*x!43 - 0.025571*x!44 + 0.090958*x!45 - 0.002983*x!46 - 0.04801*x!47 - 0.035129*x!48"
definition "x36' x == 48.409*x!1 - 3.7335*x!2 + 32.385*x!3 + 123.4*x!4 - 10.509*x!5 - 100.46*x!6 + 251.0*x!7 + 15.115*x!8 - 306.96*x!9 + 1327.9*x!10 + 119.59*x!11 - 2059.6*x!12 - 316.77*x!13 + 309.66*x!14 - 870.95*x!15 - 176.05*x!16 + 612.8*x!17 + 311.81*x!18 - 23.027*x!19 + 201.61*x!20 - 171.24*x!21 + 169.57*x!22 - 91.873*x!23 - 44.001*x!24 + 0.050997*x!25 - 0.0039331*x!26 + 0.034116*x!27 + 0.13*x!28 - 0.011071*x!29 - 0.10583*x!30 + 0.26442*x!31 + 0.015922*x!32 - 0.32337*x!33 + 1.3989*x!34 + 0.12598*x!35 - 2.6645*x!36 - 0.3337*x!37 + 0.32621*x!38 - 0.9175*x!39 - 0.18546*x!40 + 0.64555*x!41 + 0.32848*x!42 - 0.024258*x!43 + 0.21239*x!44 - 0.18039*x!45 + 0.17864*x!46 - 0.096784*x!47 - 0.046353*x!48"
definition "x37' x == 16.772*x!2 - 18.711*x!1 + 31.337*x!3 - 86.799*x!4 - 1.8261*x!5 - 326.22*x!6 - 26.875*x!7 + 48.423*x!8 - 1444.1*x!9 - 111.75*x!10 + 580.84*x!11 - 316.97*x!12 - 2618.4*x!13 + 213.69*x!14 - 227.06*x!15 - 1560.3*x!16 - 475.12*x!17 + 287.08*x!18 + 62.345*x!19 + 349.71*x!20 - 307.69*x!21 + 551.86*x!22 - 413.54*x!23 - 278.79*x!24 - 0.019712*x!25 + 0.017669*x!26 + 0.033012*x!27 - 0.091439*x!28 - 0.0019237*x!29 - 0.34366*x!30 - 0.028311*x!31 + 0.051011*x!32 - 1.5212*x!33 - 0.11773*x!34 + 0.61189*x!35 - 0.33391*x!36 - 3.2531*x!37 + 0.22511*x!38 - 0.23919*x!39 - 1.6437*x!40 - 0.50052*x!41 + 0.30242*x!42 + 0.065677*x!43 + 0.36841*x!44 - 0.32414*x!45 + 0.58136*x!46 - 0.43564*x!47 - 0.29369*x!48"
definition "x38' x == 2.1605*x!1 + 59.152*x!2 - 19.397*x!3 + 2.4357*x!4 - 153.32*x!5 + 143.74*x!6 + 5.1672*x!7 + 235.26*x!8 + 606.81*x!9 - 229.22*x!10 + 1225.8*x!11 + 308.88*x!12 + 220.47*x!13 - 2060.7*x!14 - 41.024*x!15 + 847.46*x!16 - 549.36*x!17 + 704.76*x!18 + 575.93*x!19 - 182.76*x!20 + 62.77*x!21 - 246.62*x!22 + 238.45*x!23 + 159.35*x!24 + 0.002276*x!25 + 0.062314*x!26 - 0.020434*x!27 + 0.0025659*x!28 - 0.16151*x!29 + 0.15142*x!30 + 0.0054434*x!31 + 0.24784*x!32 + 0.63924*x!33 - 0.24147*x!34 + 1.2913*x!35 + 0.32539*x!36 + 0.23225*x!37 - 2.6656*x!38 - 0.043217*x!39 + 0.89276*x!40 - 0.57872*x!41 + 0.74243*x!42 + 0.60672*x!43 - 0.19253*x!44 + 0.066125*x!45 - 0.2598*x!46 + 0.25119*x!47 + 0.16786*x!48"
definition "x39' x == 11.65*x!2 - 11.108*x!1 + 6.8996*x!3 + 10.745*x!4 - 14.165*x!5 - 24.224*x!6 + 58.6*x!7 + 1.0473*x!8 - 23.411*x!9 + 194.71*x!10 + 124.74*x!11 - 874.49*x!12 - 232.17*x!13 - 36.538*x!14 - 982.44*x!15 - 164.62*x!16 + 658.46*x!17 + 612.29*x!18 + 81.858*x!19 + 340.63*x!20 - 202.91*x!21 + 81.196*x!22 - 56.024*x!23 - 15.279*x!24 - 0.011702*x!25 + 0.012273*x!26 + 0.0072684*x!27 + 0.01132*x!28 - 0.014922*x!29 - 0.025519*x!30 + 0.061732*x!31 + 0.0011033*x!32 - 0.024662*x!33 + 0.20512*x!34 + 0.1314*x!35 - 0.92123*x!36 - 0.24458*x!37 - 0.038491*x!38 - 1.5297*x!39 - 0.17342*x!40 + 0.69366*x!41 + 0.64502*x!42 + 0.086233*x!43 + 0.35883*x!44 - 0.21375*x!45 + 0.085536*x!46 - 0.059019*x!47 - 0.016096*x!48"
definition "x40' x == 0.34677*x!2 - 45.16*x!1 + 87.266*x!3 - 58.989*x!4 + 81.86*x!5 - 393.99*x!6 - 43.617*x!7 - 87.105*x!8 - 585.65*x!9 - 95.775*x!10 - 55.621*x!11 - 175.4*x!12 - 1550.2*x!13 + 849.01*x!14 - 150.24*x!15 - 2831.0*x!16 - 714.73*x!17 - 306.41*x!18 - 276.74*x!19 + 1235.6*x!20 - 213.26*x!21 + 900.37*x!22 - 708.02*x!23 - 408.51*x!24 - 0.047574*x!25 + 0.00036531*x!26 + 0.09193*x!27 - 0.062142*x!28 + 0.086236*x!29 - 0.41505*x!30 - 0.045948*x!31 - 0.091761*x!32 - 0.61696*x!33 - 0.10089*x!34 - 0.058594*x!35 - 0.18478*x!36 - 1.633*x!37 + 0.89439*x!38 - 0.15827*x!39 - 3.477*x!40 - 0.75293*x!41 - 0.32279*x!42 - 0.29153*x!43 + 1.3016*x!44 - 0.22465*x!45 + 0.94849*x!46 - 0.74586*x!47 - 0.43035*x!48"
definition "x41' x == 3.5059*x!1 - 19.002*x!2 + 24.585*x!3 - 17.341*x!4 + 25.7*x!5 - 100.44*x!6 - 121.83*x!7 + 37.286*x!8 - 153.78*x!9 - 417.65*x!10 + 181.1*x!11 + 615.65*x!12 - 480.91*x!13 - 550.2*x!14 + 663.43*x!15 - 703.07*x!16 - 2922.4*x!17 - 629.58*x!18 + 982.78*x!19 - 72.585*x!20 + 517.72*x!21 + 573.36*x!22 - 34.103*x!23 - 92.294*x!24 + 0.0036933*x!25 - 0.020017*x!26 + 0.025899*x!27 - 0.018268*x!28 + 0.027073*x!29 - 0.1058*x!30 - 0.12834*x!31 + 0.039279*x!32 - 0.162*x!33 - 0.43998*x!34 + 0.19078*x!35 + 0.64856*x!36 - 0.50662*x!37 - 0.57961*x!38 + 0.69889*x!39 - 0.74065*x!40 - 3.5734*x!41 - 0.66323*x!42 + 1.0353*x!43 - 0.076465*x!44 + 0.54539*x!45 + 0.60401*x!46 - 0.035926*x!47 - 0.097227*x!48"
definition "x42' x == 11.689*x!2 - 6.541*x!1 + 14.446*x!3 - 16.841*x!4 + 27.253*x!5 - 50.506*x!6 - 63.95*x!7 - 102.32*x!8 - 140.13*x!9 - 204.16*x!10 - 309.41*x!11 + 316.39*x!12 + 287.25*x!13 + 700.16*x!14 + 615.11*x!15 - 292.97*x!16 - 628.33*x!17 - 1965.7*x!18 - 1181.8*x!19 - 160.14*x!20 + 504.08*x!21 + 10.684*x!22 - 328.24*x!23 - 67.729*x!24 - 0.0068906*x!25 + 0.012313*x!26 + 0.015219*x!27 - 0.017741*x!28 + 0.028709*x!29 - 0.053205*x!30 - 0.067368*x!31 - 0.10779*x!32 - 0.14762*x!33 - 0.21507*x!34 - 0.32595*x!35 + 0.33331*x!36 + 0.3026*x!37 + 0.73758*x!38 + 0.64799*x!39 - 0.30863*x!40 - 0.66191*x!41 - 2.5655*x!42 - 1.245*x!43 - 0.16869*x!44 + 0.53103*x!45 + 0.011255*x!46 - 0.34578*x!47 - 0.071349*x!48"
definition "x43' x == 5.9383*x!2 - 11.411*x!1 + 26.834*x!3 - 15.359*x!4 + 6.1346*x!5 - 51.136*x!6 - 1.6072*x!7 - 127.63*x!8 - 64.662*x!9 + 76.069*x!10 - 444.22*x!11 - 20.062*x!12 + 77.799*x!13 + 570.73*x!14 + 84.558*x!15 - 263.82*x!16 + 983.07*x!17 - 1184.4*x!18 - 2653.4*x!19 + 240.05*x!20 + 17.029*x!21 - 433.29*x!22 - 721.56*x!23 - 85.171*x!24 - 0.012021*x!25 + 0.0062557*x!26 + 0.028268*x!27 - 0.01618*x!28 + 0.0064625*x!29 - 0.05387*x!30 - 0.0016931*x!31 - 0.13445*x!32 - 0.068118*x!33 + 0.080135*x!34 - 0.46796*x!35 - 0.021135*x!36 + 0.081958*x!37 + 0.60124*x!38 + 0.089078*x!39 - 0.27792*x!40 + 1.0356*x!41 - 1.2477*x!42 - 3.2899*x!43 + 0.25288*x!44 + 0.017939*x!45 - 0.45645*x!46 - 0.76013*x!47 - 0.089724*x!48"
definition "x44' x == 10.661*x!1 + 0.75629*x!2 - 31.37*x!3 + 18.757*x!4 - 29.414*x!5 + 193.91*x!6 - 34.395*x!7 + 32.908*x!8 + 271.89*x!9 - 54.429*x!10 - 33.158*x!11 + 199.94*x!12 + 354.88*x!13 - 181.87*x!14 + 333.88*x!15 + 1248.3*x!16 - 59.084*x!17 - 157.94*x!18 + 239.26*x!19 - 1528.9*x!20 + 772.83*x!21 - 858.92*x!22 + 734.27*x!23 + 372.63*x!24 + 0.011231*x!25 + 0.00079672*x!26 - 0.033047*x!27 + 0.01976*x!28 - 0.030986*x!29 + 0.20427*x!30 - 0.036234*x!31 + 0.034667*x!32 + 0.28643*x!33 - 0.057338*x!34 - 0.03493*x!35 + 0.21063*x!36 + 0.37385*x!37 - 0.19159*x!38 + 0.35173*x!39 + 1.315*x!40 - 0.062242*x!41 - 0.16638*x!42 + 0.25204*x!43 - 2.1053*x!44 + 0.81414*x!45 - 0.90483*x!46 + 0.77352*x!47 + 0.39255*x!48"
definition "x45' x == 21.145*x!1 - 0.67362*x!2 + 25.339*x!3 + 82.664*x!4 - 18.143*x!5 - 108.58*x!6 + 131.04*x!7 + 40.675*x!8 - 205.5*x!9 + 125.37*x!10 + 92.038*x!11 - 169.72*x!12 - 294.36*x!13 + 57.772*x!14 - 200.48*x!15 - 211.37*x!16 + 512.5*x!17 + 500.79*x!18 + 15.006*x!19 + 785.7*x!20 - 3685.6*x!21 + 248.17*x!22 - 125.37*x!23 - 428.07*x!24 + 0.022275*x!25 - 0.00070963*x!26 + 0.026694*x!27 + 0.087083*x!28 - 0.019113*x!29 - 0.11438*x!30 + 0.13805*x!31 + 0.04285*x!32 - 0.21648*x!33 + 0.13207*x!34 + 0.096957*x!35 - 0.17879*x!36 - 0.31009*x!37 + 0.06086*x!38 - 0.2112*x!39 - 0.22266*x!40 + 0.5399*x!41 + 0.52756*x!42 + 0.015808*x!43 + 0.8277*x!44 - 4.3773*x!45 + 0.26143*x!46 - 0.13208*x!47 - 0.45095*x!48"
definition "x46' x == 30.438*x!1 - 10.312*x!2 - 14.559*x!3 + 71.32*x!4 + 9.4074*x!5 + 217.12*x!6 + 3.4082*x!7 - 22.61*x!8 + 366.85*x!9 - 62.437*x!10 - 17.337*x!11 + 170.53*x!12 + 551.59*x!13 - 246.57*x!14 + 70.631*x!15 + 918.77*x!16 + 591.41*x!17 + 17.745*x!18 - 424.27*x!19 - 874.95*x!20 + 255.27*x!21 - 4294.4*x!22 + 510.73*x!23 + 1033.1*x!24 + 0.032064*x!25 - 0.010863*x!26 - 0.015337*x!27 + 0.075133*x!28 + 0.0099102*x!29 + 0.22872*x!30 + 0.0035904*x!31 - 0.023818*x!32 + 0.38646*x!33 - 0.065775*x!34 - 0.018263*x!35 + 0.17964*x!36 + 0.58107*x!37 - 0.25975*x!38 + 0.074406*x!39 + 0.96788*x!40 + 0.62302*x!41 + 0.018694*x!42 - 0.44695*x!43 - 0.92172*x!44 + 0.26891*x!45 - 5.0186*x!46 + 0.53803*x!47 + 1.0883*x!48"
definition "x47' x == 11.835*x!3 - 37.47*x!2 - 18.027*x!1 - 25.981*x!4 + 110.26*x!5 - 133.09*x!6 - 21.113*x!7 - 89.428*x!8 - 265.96*x!9 + 11.486*x!10 - 31.545*x!11 - 88.775*x!12 - 389.13*x!13 + 228.95*x!14 - 47.085*x!15 - 703.45*x!16 - 45.639*x!17 - 333.53*x!18 - 724.09*x!19 + 748.64*x!20 - 119.88*x!21 + 488.53*x!22 - 3962.5*x!23 - 875.81*x!24 - 0.01899*x!25 - 0.039473*x!26 + 0.012468*x!27 - 0.027369*x!28 + 0.11615*x!29 - 0.1402*x!30 - 0.022242*x!31 - 0.094208*x!32 - 0.28018*x!33 + 0.0121*x!34 - 0.033231*x!35 - 0.093521*x!36 - 0.40993*x!37 + 0.24119*x!38 - 0.049602*x!39 - 0.74105*x!40 - 0.048079*x!41 - 0.35136*x!42 - 0.7628*x!43 + 0.78865*x!44 - 0.12629*x!45 + 0.51464*x!46 - 4.669*x!47 - 0.92262*x!48"
definition "x48' x == 12.708*x!1 + 4.8669*x!2 - 6.4356*x!3 + 9.4963*x!4 + 3.5537*x!5 - 74.352*x!6 + 13.537*x!7 - 16.221*x!8 - 158.43*x!9 + 2.6078*x!10 - 31.934*x!11 - 48.095*x!12 - 252.14*x!13 + 158.72*x!14 - 25.236*x!15 - 416.39*x!16 - 103.09*x!17 - 75.108*x!18 - 90.118*x!19 + 375.82*x!20 - 425.25*x!21 + 1006.8*x!22 - 878.11*x!23 - 4455.6*x!24 + 0.013388*x!25 + 0.0051271*x!26 - 0.0067796*x!27 + 0.010004*x!28 + 0.0037436*x!29 - 0.078327*x!30 + 0.01426*x!31 - 0.017088*x!32 - 0.1669*x!33 + 0.0027471*x!34 - 0.033641*x!35 - 0.050665*x!36 - 0.26562*x!37 + 0.16721*x!38 - 0.026585*x!39 - 0.43865*x!40 - 0.1086*x!41 - 0.079123*x!42 - 0.094935*x!43 + 0.39591*x!44 - 0.44798*x!45 + 1.0606*x!46 - 0.92505*x!47 - 5.1884*x!48"
definition "t'   x == 1"
definition "u1   x == x ! 49"

schematic_goal building_fas:
  "[t' X,  x1' X,  x2' X,  x3' X,  x4' X,  x5' X,  x6' X,  x7' X,  x8' X,  x9' X,
  x10' X, x11' X, x12' X, x13' X, x14' X, x15' X, x16' X, x17' X, x18' X, x19' X,
  x20' X, x21' X, x22' X, x23' X, x24' X, x25' X, x26' X, x27' X, x28' X, x29' X,
  x30' X, x31' X, x32' X, x33' X, x34' X, x35' X, x36' X, x37' X, x38' X, x39' X,
  x40' X, x41' X, x42' X, x43' X, x44' X, x45' X, x46' X, x47' X, x48' X, u1 X] =
  interpret_floatariths ?fas X"
  unfolding t'_def x1'_def  x2'_def  x3'_def  x4'_def  x5'_def  x6'_def  x7'_def  x8'_def  x9'_def
    x10'_def x11'_def x12'_def x13'_def x14'_def x15'_def x16'_def x17'_def x18'_def x19'_def
    x20'_def x21'_def x22'_def x23'_def x24'_def x25'_def x26'_def x27'_def x28'_def x29'_def
    x30'_def x31'_def x32'_def x33'_def x34'_def x35'_def x36'_def x37'_def x38'_def x39'_def
    x40'_def x41'_def x42'_def x43'_def x44'_def x45'_def x46'_def x47'_def x48'_def u1_def
  by (reify_floatariths)

concrete_definition building_fas uses building_fas

end

end
