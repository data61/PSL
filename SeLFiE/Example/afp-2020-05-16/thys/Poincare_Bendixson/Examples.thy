section \<open>Examples\<close>
theory Examples
  imports Poincare_Bendixson
    "HOL-ODE-Numerics.ODE_Numerics"
    Affine_Arithmetic_Misc
begin

subsection \<open>Simple\<close>

context
begin

text \<open>coordinate functions\<close>
definition "cx x y = -y + x * (1 - x^2 - y^2)"
definition "cy x y = x + y * (1 - x^2 - y^2)"

lemmas c_defs = cx_def cy_def

text \<open>partial derivatives\<close>
definition C11::"real\<Rightarrow>real\<Rightarrow>real" where "C11 x y = 1 - 3 * x^2 - y^2"
definition C12::"real\<Rightarrow>real\<Rightarrow>real" where "C12 x y = -1 - 2 * x * y"
definition C21::"real\<Rightarrow>real\<Rightarrow>real" where "C21 x y = 1 - 2 * x * y"
definition C22::"real\<Rightarrow>real\<Rightarrow>real" where "C22 x y = 1 - x^2 - 3 * y^2"

lemmas C_partials = C11_def C12_def C21_def C22_def

text \<open>Jacobian as linear map\<close>
definition C :: "real \<Rightarrow> real \<Rightarrow> (real \<times> real) \<Rightarrow>\<^sub>L (real \<times> real)" where
  "C x y = blinfun_of_matrix
    ((\<lambda>_ _. 0)
      ((1,0) := (\<lambda>_. 0)((1, 0):=C11 x y, (0, 1):=C12 x y),
       (0, 1):= (\<lambda>_. 0)((1, 0):=C21 x y, (0, 1):=C22 x y)))"

lemma C_simp[simp]: "blinfun_apply (C x y) (dx, dy) =
  (dx * C11 x y + dy * C12 x y,
   dx * C21 x y + dy * C22 x y)"
  by (auto simp: C_def blinfun_of_matrix_apply Basis_prod_def)

lemma C_continuous[continuous_intros]:
  "continuous_on S (\<lambda>x. local.C (f x) (g x))"
  if "continuous_on S f" "continuous_on S g"
  unfolding C_def
  by (auto intro!: continuous_on_blinfun_of_matrix continuous_intros that
      simp: Basis_prod_def C_partials)

interpretation c: c1_on_open_R2 "\<lambda>(x::real, y::real). (cx x y, cy x y)::real*real"
  "\<lambda>(x, y). C x y" UNIV
  by unfold_locales
    (auto intro!: derivative_eq_intros ext continuous_intros simp: split_beta algebra_simps
      c_defs C_partials power2_eq_square)

definition "trapC = cball (0::real,0::real) 2 - ball (0::real,0::real) (1/2)"

lemma trapC_eq:
  shows "trapC = {p. (fst p)^2 + (snd p)^2 - 4 \<le> 0} \<inter> {p. 1/4 - ((fst p)^2 + (snd p)^2) \<le> 0}"
  unfolding trapC_def
  apply (auto simp add: dist_Pair_Pair)
  using real_sqrt_le_iff apply fastforce
    apply (smt four_x_squared one_le_power real_sqrt_ge_0_iff real_sqrt_pow2)
  using real_sqrt_le_mono apply fastforce
proof -
  fix a :: real and b :: real
  assume a1: "sqrt (a\<^sup>2 + b\<^sup>2) * 2 < 1"
  assume a2: "1 \<le> a\<^sup>2 * 4 + b\<^sup>2 * 4"
  have "\<forall>r. 1 \<le> sqrt r \<or> \<not> 1 \<le> r"
    by simp
  then show False
    using a2 a1 by (metis (no_types) Groups.mult_ac(2) distrib_left linorder_not_le real_sqrt_four real_sqrt_mult)
qed

lemma x_in_trapC:
  shows "(2,0) \<in> trapC"
  unfolding trapC_def
  by (auto simp add: dist_Pair_Pair)

lemma compact_trapC:
  shows "compact trapC"
  unfolding trapC_def
  using compact_cball compact_diff by blast

lemma nonempty_trapC:
  shows "trapC \<noteq> {}"
  using x_in_trapC by auto

lemma origin_fixpoint:
  assumes "(\<lambda>(x, y). (cx x y, cy x y)) (a,b) = 0"
  shows "a = (0::real)" "b = (0::real)"
  using assms unfolding cx_def cy_def zero_prod_def apply auto
  apply (sos "((((A<0 * R<1) + (([28859/65536*a + 5089/8192*b + ~1/2] * A=0) + (([~5089/8192*a + 17219/65536*b + ~1/2] * A=1) + (R<1 * ((R<11853/65536 * [~16384/11853*a^2 + ~11585/11853*b^2 + 302/1317*a*b + a + 1940/3951*b]^2) + ((R<73630271/776798208 * [a^2 + 64177444/73630271*b^2 + 44531712/73630271*a*b + ~131061126/73630271*b]^2) + ((R<70211653911/4825433440256 * [~77895776116/70211653911*b^2 + 5825642465/10030236273*a*b + b]^2) + ((R<48375415273/657341564387328 * [~36776393918/48375415273*b^2 + a*b]^2) + (R<18852430195/11096159253659648 * [b^2]^2)))))))))) & (((A<0 * (A<0 * R<1)) + (([b] * A=0) + (([~1*a] * A=1) + (R<1 * (R<1 * [b]^2)))))))")
proof -
  assume a1: "a * (1 - a\<^sup>2 - b\<^sup>2) = b"
  assume a2: "a + b * (1 - a\<^sup>2 - b\<^sup>2) = 0"
  have f3: "\<forall>r ra. - (ra::real) * r = ra * - r"
    by simp
  have "- b * (1 - a\<^sup>2 - b\<^sup>2) = a"
    using a2 by simp
  then have "\<exists>r ra. b * b - ra * (r * (ra * - r)) = 0"
    using f3 a1 by (metis (no_types) c.vec_simps(15) right_minus_eq)
  then have "\<exists>r. b * b - r * - r = 0"
    using f3 by (metis (no_types) c.vec_simps(14))
  then show "b = 0"
    by simp
qed

lemma origin_not_trapC:
  shows "0 \<notin> trapC"
  unfolding trapC_def zero_prod_def 
  by auto

lemma regular_trapC:
  shows "0 \<notin> (\<lambda>(x, y). (cx x y, cy x y)) ` trapC"
  using origin_fixpoint origin_not_trapC
  by (smt UNIV_I UNIV_I UNIV_def case_prodE2 imageE c.flow_initial_time_if
      c.rev.flow_initial_time_if mem_Collect_eq zero_prod_def)

lemma positively_invariant_outer:
  shows "c.positively_invariant  {p. (\<lambda>p. (fst p)\<^sup>2 + (snd p)\<^sup>2 - 4) p \<le> 0}"
  apply (rule c.positively_invariant_le[of "\<lambda>p.-2*((fst p)^2+(snd p)^2)" _  "\<lambda>x p. 2 * fst x * fst p + 2 * snd x * snd p" ])
    apply (auto intro!: continuous_intros derivative_eq_intros)
  unfolding cx_def cy_def
  by (sos "(((A<0 * R<1) + (R<1 * ((R<6 * [a]^2) + (R<6 * [b]^2)))))")


lemma positively_invariant_inner:
  shows "c.positively_invariant  {p. (\<lambda>p. 1/4 - ((fst p)\<^sup>2 + (snd p)\<^sup>2)) p \<le> 0}"
  apply (rule c.positively_invariant_le[of "\<lambda>p.-2*((fst p)^2+(snd p)^2)" _ "\<lambda>x p. - 2 * fst x * fst p - 2 * snd x * snd p"])
    apply (auto intro!: continuous_intros derivative_eq_intros)
  unfolding cx_def cy_def
  by (sos "(((A<0 * R<1) + (R<1 * ((R<3/2 * [a]^2) + (R<3/2 * [b]^2)))))")

lemma positively_invariant_trapC:
  shows "c.positively_invariant trapC"
  unfolding trapC_eq
  apply (rule c.positively_invariant_conj)
  using positively_invariant_outer
   apply (metis (no_types, lifting) Collect_cong case_prodE case_prodI2 case_prod_conv)
  using positively_invariant_inner
  by (metis (no_types, lifting) Collect_cong case_prodE case_prodI2 case_prod_conv)

theorem c_has_periodic_orbit:
  obtains y where "c.periodic_orbit y" "c.flow0 y ` UNIV \<subseteq> trapC"
proof -
  from c.poincare_bendixson_applied[OF compact_trapC _ nonempty_trapC positively_invariant_trapC regular_trapC]
  show ?thesis using that by blast
qed

text \<open>Real-Arithmetic\<close>
schematic_goal c_fas:
  "[-(-(X!1) + (X!0) * (1 - (X!0)^2 - (X!1)^2)), -((X!0) + (X!1) * (1 - (X!0)^2 - (X!1)^2))] = interpret_floatariths ?fas X"
  by (reify_floatariths)

concrete_definition c_fas uses c_fas

interpretation crev: ode_interpretation true_form UNIV c_fas
  "-(\<lambda>(x, y). (cx x y, cy x y)::real*real)"
  "d::2" for d
  by unfold_locales (auto simp: c_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def
      cx_def cy_def eval_nat_numeral
      mk_ode_ops_def eucl_of_list_prod power2_eq_square intro!: isFDERIV_I)

lemma crev: "t \<in> {1/8 .. 1/8} \<longrightarrow> (x, y) \<in> {(2, 0) .. (2, 0)} \<longrightarrow>
   t \<in> c.rev.existence_ivl0 (x, y) \<and> c.rev.flow0 (x, y) t \<in> {(5.15, -0.651)..(5.18, -0.647)}"
  by (tactic \<open>ode_bnds_tac @{thms c_fas_def} 30 20 7 12 [(0, 1, "0x000000")] (* "crev.out" *) "" @{context} 1\<close>)

theorem c_has_limit_cycle:
  obtains y where "c.limit_cycle y" "range (c.flow0 y) \<subseteq> trapC"
proof -
  define E where "E = {(5.15, -0.651)..(5.18, -0.647)::real*real}"
  from crev have "c.rev.flow0 (2, 0) (1/8) \<in> E"
    by (auto simp: E_def)
  moreover
  have "E \<inter> trapC = {}"
  proof -
    have "norm x > 2" if "x \<in> E" for x
      using that
      apply (auto simp: norm_prod_def less_eq_prod_def E_def)
      by (smt power2_less_eq_zero_iff real_less_rsqrt zero_compare_simps(9))
    moreover have "norm x \<le> 2" if "x \<in> trapC" for x
      using that
      by (auto simp: trapC_def dist_prod_def norm_prod_def)
    ultimately show ?thesis by force
  qed
  ultimately have "c.rev.flow0 (2, 0) (1 / 8) \<notin> trapC" by blast
  from c.poincare_bendixson_limit_cycle[OF compact_trapC subset_UNIV x_in_trapC positively_invariant_trapC regular_trapC this] that
  show ?thesis by blast
qed

end


subsection \<open>Glycolysis\<close>

text \<open>Strogatz, Example 7.3.2\<close>

context
begin

text \<open>coordinate functions\<close>
definition "gx x y = -x + 0.08 * y + x\<^sup>2 * y"
definition "gy x y = 0.6 - 0.08 * y - x\<^sup>2 * y"

lemmas g_defs = gx_def gy_def

text \<open>partial derivatives\<close>
definition A11::"real\<Rightarrow>real\<Rightarrow>real" where "A11 x y = -1 + 2 * x * y"
definition A12::"real\<Rightarrow>real\<Rightarrow>real" where "A12 x y = (0.08 + x\<^sup>2)"
definition A21::"real\<Rightarrow>real\<Rightarrow>real" where "A21 x y = -2*x*y"
definition A22::"real\<Rightarrow>real\<Rightarrow>real" where "A22 x y = -(0.08 + x\<^sup>2)"

lemmas A_partials = A11_def A12_def A21_def A22_def

text \<open>Jacobian as linear map\<close>
definition A :: "real \<Rightarrow> real \<Rightarrow> (real \<times> real) \<Rightarrow>\<^sub>L (real \<times> real)" where
  "A x y = blinfun_of_matrix
    ((\<lambda>_ _. 0)
      ((1,0) := (\<lambda>_. 0)((1, 0):=A11 x y, (0, 1):=A12 x y),
       (0, 1):= (\<lambda>_. 0)((1, 0):=A21 x y, (0, 1):=A22 x y)))"

lemma A_simp[simp]: "blinfun_apply (A x y) (dx, dy) =
  (dx * A11 x y + dy * A12 x y,
   dx * A21 x y + dy * A22 x y)"
  by (auto simp: A_def blinfun_of_matrix_apply Basis_prod_def)

lemma A_continuous[continuous_intros]:
  "continuous_on S (\<lambda>x. local.A (f x) (g x))"
  if "continuous_on S f" "continuous_on S g"
  unfolding A_def
  by (auto intro!: continuous_on_blinfun_of_matrix continuous_intros that
      simp: Basis_prod_def A_partials)

interpretation g: c1_on_open_R2 "\<lambda>(x::real, y::real). (gx x y, gy x y)::real*real"
  "\<lambda>(x, y). A x y" UNIV
  by unfold_locales
    (auto intro!: derivative_eq_intros ext continuous_intros simp: split_beta algebra_simps
      g_defs A_partials)

(*
  The outer invariant is the convex set formed by the axes, y \<le> 7.51, and x+y\<le>8.12
*)
definition "(pos_quad::(real \<times> real) set) =  {p . - snd p \<le> 0} \<inter> {p . - fst p \<le> 0}"

definition "(trapG1::(real \<times> real) set) = pos_quad \<inter> ({p. (snd p) - 751/100 \<le> 0} \<inter> {p. (fst p) + (snd p) - 812/100 \<le> 0})"

lemma positively_invariant_y:
  shows "g.positively_invariant {p . - snd p \<le> 0}"
  apply (rule g.positively_invariant_le[of "\<lambda>p. -(0.08 + (fst p)^2)" _ "\<lambda>x p. - snd p"])
    apply (auto intro!: continuous_intros derivative_eq_intros)
  unfolding gy_def
  by (sos "()")

lemma positively_invariant_pos_quad:
  shows "g.positively_invariant pos_quad"
  unfolding pos_quad_def
  apply (rule g.positively_invariant_le_domain[OF positively_invariant_y, of "\<lambda>p. fst p * snd p -1"])
    apply (auto intro!: continuous_intros derivative_eq_intros)
  unfolding gx_def
  by (sos "(((A<0 * R<1) + (((A<0 * R<1) * (R<11/14 * [1]^2)) + ((A<=0 * R<1) * (R<1/7 * [1]^2)))))")

lemma positively_invariant_y_upper:
  shows "g.positively_invariant {p. (snd p) - 751/100 \<le> 0}"
  apply (rule g.positively_invariant_barrier)
    apply (auto intro!: continuous_intros derivative_eq_intros)
  unfolding gy_def
  by (sos "((R<1 + ((R<1 * (R<18775/2 * [a]^2)) + ((A<=0 * R<1) * (R<1250 * [1]^2)))))")

lemma arith2:
  shows "(y::real) \<le> 751/100 \<and> x + (y::real) = 812/100 \<Longrightarrow> 3/5 - (x::real) < 0"
  by linarith

lemma positively_invariant_trapG1:
  shows "g.positively_invariant trapG1"
  unfolding trapG1_def
  apply (rule g.positively_invariant_conj[OF positively_invariant_pos_quad])
  apply (rule g.positively_invariant_barrier_domain[OF positively_invariant_y_upper])
  apply (auto intro!: continuous_intros derivative_eq_intros)
  unfolding gx_def gy_def by auto

(* Polynomial in invariant *)
definition "p1 (x::real) (y::real) = -(21/34) - (69*x)/38 + (19*x^2)/15 - (9*x^3)/28 - (6*x^4)/43 + ( 14*y)/29 + (31*x*y)/21 + (182*x^2*y)/47 - (35*x^3*y)/16 - ( 3*y^2)/17 - (2*x*y^2)/9 - (31*x^2*y^2)/20 +y^3/102 + (x*y^3)/59"

definition "p1d x xa = 38 * (fst xa * fst x) / 15 - 69 * fst xa / 38 -
          27 * (fst xa * (fst x)\<^sup>2) / 28 -
          24 * (fst xa * fst x ^ 3) / 43 +
          14 * snd xa / 29 +
          (651 * (fst x * snd xa) +
           651 * (fst xa * snd x)) /
          441 +
          (8554 * ((fst x)\<^sup>2 * snd xa) +
           17108 * (fst xa * (fst x * snd x))) /
          2209 -
          (560 * (fst x ^ 3 * snd xa) +
           1680 * (fst xa * ((fst x)\<^sup>2 * snd x))) /
          256 -
          6 * (snd xa * snd x) / 17 -
          (36 * (fst x * (snd xa * snd x)) +
           18 * (fst xa * (snd x)\<^sup>2)) /
          81 -
          (1240 * ((fst x)\<^sup>2 * (snd xa * snd x)) +
           1240 * (fst xa * (fst x * (snd x)\<^sup>2))) /
          400 +
          snd xa * (snd x)\<^sup>2 / 34 +
          (177 * (fst x * (snd xa * (snd x)\<^sup>2)) +
           fst xa * snd x ^ 3 * 59) /
          3481"

lemma p1_has_derivative:
  shows "((\<lambda>x. p1 (fst x) (snd x)) has_derivative p1d x) (at x)"
  unfolding p1_def p1d_def
  by (auto intro!: continuous_intros derivative_eq_intros)

(* p1 excludes equilibria for free *)
lemma p1_not_equil:
  shows " p1 x y \<le> 0 \<Longrightarrow> gx x y \<noteq> 0 \<or> gy x y \<noteq> 0"
  unfolding gx_def gy_def p1_def
  by (sos "()")

definition "trapG = trapG1 \<inter> {p. p1 (fst p) (snd p) \<le> 0}"

text \<open>Real-Arithmetic\<close>
definition "g_arith a b = (- (27 / 25) - a\<^sup>2 + 2 * a * b) * p1 a b - p1d (a, b) (gx a b, gy a b)"

schematic_goal g_arith_fas:
  "[g_arith (X!0) (X!1)] = interpret_floatariths ?fas X"
  unfolding g_arith_def p1_def p1d_def gx_def gy_def fst_conv snd_conv
  by (reify_floatariths)

concrete_definition g_arith_fas uses g_arith_fas

lemma list_interval2: "list_interval [a, b] [c, d] = {[x, y] | x y. x \<in> {a .. c} \<and> y \<in> {b .. d}}"
  apply (auto simp: list_interval_def)
  subgoal for x
    apply (cases x)
    apply auto
    subgoal for y zs
      apply (cases zs)
      by auto
    done
  done

lemma g_arith_nonneg: "g_arith a b \<ge> 0"
  if a: "0 \<le> a" "a \<le> 8.24" and b: "0 \<le> b" "b \<le> 7.51"
proof -
  have "prove_nonneg [(0, 1, ''0x000000'')] 1000000 30 (slp_of_fas [hd g_arith_fas]) [aforms_of_ivls [0, 0]
    [float_divr 30 824 100, float_divr 30 751 100]]"
    by eval\<comment> \<open>slow: 60s\<close>
  from prove_nonneg[OF this]
  have "0 \<le> interpret_floatarith (hd g_arith_fas) [a, b]"
    apply (auto simp: g_arith_fas)
    apply (subst (asm) Joints_aforms_of_ivls)
     apply (auto )
      apply (smt divide_nonneg_nonneg float_divr float_numeral rel_simps(27))
     apply (smt divide_nonneg_nonneg float_divr float_numeral rel_simps(27))
    apply (subst (asm) list_interval2)
    apply auto
    apply (drule spec[where x="[a, b]"])
    using a b
    apply auto
    subgoal by (rule order_trans[OF _ float_divr]) simp
    subgoal by (rule order_trans[OF _ float_divr]) simp
    done
  also have "\<dots> = g_arith a b"
    by (auto simp: g_arith_fas_def g_arith_def p1_def p1d_def gx_def gy_def)
  finally show ?thesis .
qed

lemma trap_arithmetic:
  "p1d (a, b) (gx a b, gy a b) \<le> (- (27 / 25) - a\<^sup>2 + 2 * a * b) * p1 a b" if "(a, b) \<in> trapG1"
proof -
  from that
  have b: "0 \<le> b" "b \<le> 7.51"
    and a: "0 \<le> a" "a \<le> 8.24"
    by (auto simp: trapG1_def pos_quad_def)
  from g_arith_nonneg[OF a b] show ?thesis
    by (simp add: g_arith_def)
qed

lemma positively_invariant_trapG:
  shows "g.positively_invariant trapG"
  unfolding trapG_def
  apply (rule g.positively_invariant_le_domain[OF positively_invariant_trapG1 _ p1_has_derivative,
        of "\<lambda>p. -1.08 - (fst p)^2 + 2 * fst p * snd p"])
  subgoal by (auto intro!: continuous_intros derivative_eq_intros simp add: pos_quad_def)
  apply auto
  by (rule trap_arithmetic)

lemma regular_trapG:
  shows "0 \<notin> (\<lambda>(x, y). (gx x y, gy x y)) ` trapG"
  unfolding trapG_def apply auto using p1_not_equil
  by force

lemma arith:
  "\<And>a b::real. 0 \<le> b \<Longrightarrow>
           0 \<le> a \<Longrightarrow>
           b * 100 \<le> 751 \<Longrightarrow>
           a * 25 + b * 25 \<le> 203 \<Longrightarrow> norm a + norm b \<le> 20"
  by auto

lemma trapG1_subset:
  shows "trapG1 \<subseteq> cball (0::real \<times> real) 20"
  unfolding trapG1_def pos_quad_def
  apply auto
  using arith norm_Pair_le
  by smt

lemma compact_subset_closed:
  assumes "compact S" "closed T"
  assumes "T \<subseteq> S"
  shows "compact T"
  using compact_Int_closed[OF assms(1-2)] assms(3)
  by (simp add: inf_absorb2)

lemma compact_trapG1:
  shows "compact trapG1"
  apply (auto intro!: compact_subset_closed[OF _ _ trapG1_subset])
  unfolding trapG1_def pos_quad_def
  by (auto intro!: closed_Collect_le continuous_intros)

lemma compact_trapG:
  shows "compact trapG"
  unfolding trapG_def
  by (auto intro!: compact_Int_closed compact_trapG1 closed_Collect_le continuous_intros simp add: p1_def)

lemma x_in_trapG:
  shows "(1,0) \<in> trapG"
  unfolding trapG_def trapG1_def pos_quad_def p1_def
  by (auto simp add: dist_Pair_Pair)

schematic_goal g_fas:
  "[- (- (X!0) + 8 / 100 * (X!1) + (X!0)^2 * (X!1)),-( 6 / 10 - 8 / 100 * (X!1) - (X!0)^2 * (X!1))] = interpret_floatariths ?fas X"
  by (reify_floatariths)

concrete_definition g_fas uses g_fas

interpretation grev: ode_interpretation true_form UNIV g_fas
  "-(\<lambda>(x, y). (gx x y, gy x y)::real*real)"
  "d::2" for d
  by unfold_locales (auto simp: g_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def
      gx_def gy_def eval_nat_numeral
      mk_ode_ops_def eucl_of_list_prod power2_eq_square intro!: isFDERIV_I)

lemma grev: "t \<in> {1/8 .. 1/8} \<longrightarrow> (x, y) \<in> {(1, 0) .. (1, 0)} \<longrightarrow>
   t \<in> g.rev.existence_ivl0 (x, y) \<and> g.rev.flow0 (x, y) t \<in>
    {(1.1, -0.09) .. (1.2, -0.08)}"
  by (tactic \<open>ode_bnds_tac @{thms g_fas_def} 30 20 7 12 [(0, 1, "0x000000")] (* "grev.out" *) "" @{context} 1\<close>)

theorem g_has_limit_cycle:
  obtains y where "g.limit_cycle y" "range (g.flow0 y) \<subseteq> trapG"
proof -
  define E::"(real*real) set" where "E = {(1.1, -0.09) .. (1.2, -0.08)}"
  from grev have "g.rev.flow0 (1, 0) (1/8) \<in> E"
    by (auto simp: E_def)
  moreover
  have "E \<inter> trapG = {}"
    by (auto simp: trapG_def E_def trapG1_def pos_quad_def)
  ultimately have "g.rev.flow0 (1, 0) (1 / 8) \<notin> trapG" by blast
  from g.poincare_bendixson_limit_cycle[OF compact_trapG subset_UNIV x_in_trapG positively_invariant_trapG regular_trapG this] that
  show ?thesis by blast
qed

end

end