theory Examples_Poincare_Map
imports
  "HOL-ODE-Numerics.ODE_Numerics"
begin

subsection \<open>Van der Pol oscillator\<close>
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
      mk_ode_ops_def eucl_of_list_prod power2_eq_square inverse_eq_divide intro!: isFDERIV_I)

lemma poincare_section_rep[poincare_tac_theorems]:
  "{(1, FloatR 9 (-2))..(2::real, FloatR 9 (-2))} = {eucl_of_list [1, FloatR 9 (-2)]..eucl_of_list [2, FloatR 9 (-2)]}"
  by (auto simp: eucl_of_list_prod)

lemma poincare_section_le[poincare_tac_theorems]:
  "{(x::real, y::real). y \<le> FloatR 9 (- 2)} =
    {x. if True then x \<bullet> Basis_list ! 1 \<le> [1, FloatR 9 (- 2)] ! 1
        else [1, FloatR 9 (- 2)] ! 1 \<le> x \<bullet> Basis_list ! 1}"
  by (auto simp: Basis_list_prod_def Basis_list_real_def)

abbreviation "vdp_ro \<equiv> ro 2 10 7 2 2 2"

lemma vdp_ro: "TAG_reach_optns vdp_ro" by simp

lemma vdp_start: "TAG_sctn True" by simp

lemma ninequarters: "2.25 = FloatR 9 (-2)"
  by auto

subsection \<open>No intermediate Poincare map\<close>

lemma vdp_pi_0: "vdp.guards_invar DIM(real \<times> real) []"
  by (auto simp: vdp.guards_invar_def)

lemma vanderpol_derivative_bounds:
  notes [poincare_tac_theorems] = vdp_pi_0 vdp_ro vdp_start
  defines "\<Sigma> \<equiv> {(1::real, 2.25::real) .. (2, 2.25)}"
  shows "\<forall>x\<in>{(1.41, 2.25) .. (1.42, 2.25)}.
  vdp.returns_to \<Sigma> x \<and>
  vdp.return_time \<Sigma> differentiable at x within {(x, y). y \<le> 2.25} \<and>
  (\<exists>D. (vdp.poincare_map \<Sigma> has_derivative blinfun_apply D) (at x within {(x, y). y \<le> 2.25}) \<and>
        vdp.poincare_map \<Sigma> x \<in> {(1.41, 2.25) .. (1.42, 2.25)} \<and>
        D o\<^sub>L blinfun_of_list [1, 0,
                             0, 1] \<in> vdp.blinfuns_of_lvivl ([-0.016, -0.024, 0, 0], [0.021, 0.031, 0, 0]))
  "
  unfolding ninequarters \<Sigma>_def
  by (tactic \<open>poincare'_bnds_tac @{thms vdp_fas_def} 30 50 20 14 [(0, 1, "0x000000")] "" (* "out_p0_vdp_0.out" *)  @{context} 1\<close>)

lemma blinfun_of_list_id2: "blinfun_of_list [1, 0, 0, 1] = (id_blinfun::(real*real)\<Rightarrow>\<^sub>L(real*real))"
  apply (auto intro!: blinfun_euclidean_eqI simp: Basis_prod_def)
  apply (auto simp: blinfun_of_list_def blinfun_of_matrix_apply)
   apply (auto simp: Basis_prod_def Basis_list_real_def)
  done

lemma norm_blinfun_of_list:
  "norm (blinfun_of_list xs::'a::executable_euclidean_space\<Rightarrow>\<^sub>L'a) \<le> (\<Sum>x\<leftarrow>xs. abs x)"
  if "length xs = DIM('a)*DIM('a)"\<comment> \<open>should work for all lists\<close>
  unfolding blinfun_of_list_def
  apply (rule norm_blinfun_of_matrix[le])
  apply (auto simp: sum_Basis_sum_nth_Basis_list)
  apply (subst add.commute)
  apply (subst sum_mult_product[symmetric])
  by (auto simp: sum_list_sum_nth that atLeast0LessThan)

lemma norm_blinfuns_of_ivl2:
  "norm x \<le> (\<Sum>i<DIM('a)*DIM('a). max (abs (xs!i)) (abs (ys!i)))"
  if "x \<in> vdp.blinfuns_of_lvivl (xs, ys)" "length xs = DIM('a)*DIM('a)" "length ys = DIM('a)*DIM('a)"
  for x::"'a::executable_euclidean_space\<Rightarrow>\<^sub>L'a"
proof -
  from that
  obtain es where xs: "x = blinfun_of_list es"
    "es \<in> list_interval xs ys"
    by (auto simp: vdp.blinfuns_of_lvivl_def)
  have [simp]: "length es = DIM('a)*DIM('a)"
    using xs that
    by (auto simp: list_interval_def dest!: list_all2_lengthD )
  note xs(1)
  also have "norm (blinfun_of_list es::'a\<Rightarrow>\<^sub>L'a) \<le> (\<Sum>x\<leftarrow>es. abs x)"
    by (rule norm_blinfun_of_list) simp
  also have "\<dots> \<le> (\<Sum>i<DIM('a)*DIM('a). max (abs (xs!i)) (abs (ys!i)))"
    using xs(2)
    by (auto simp: sum_list_sum_nth atLeast0LessThan list_interval_def
        list_all2_conv_all_nth max_def that dest!: spec
        intro!: sum_mono)
  finally show ?thesis .
qed

lemma unique_Poincare:
  defines "\<Sigma> \<equiv> {(1::real, 2.25::real) .. (2, 2.25)}"
  shows "\<exists>!x. x \<in> {(1.41::real, 2.25::real) .. (1.42, 2.25)} \<and> vdp.poincare_map \<Sigma> x = x"
proof -
  let ?S = "{(x, y). y \<le> 225 / 10\<^sup>2}"
  define S where "S \<equiv> {(1.41::real, 2.25::real) .. (1.42, 2.25)}"
  have "convex S" "complete S" "S \<noteq> {}"  "S \<subseteq> ?S"
    unfolding S_def
    by (auto intro!: compact_imp_complete)
  then show ?thesis
    unfolding S_def[symmetric]
  proof (rule vdp.Poincare_Banach_fixed_pointI)
    show "\<forall>x\<in>S. vdp.poincare_map \<Sigma> x \<in> S \<and>
           (\<exists>D. (vdp.poincare_map \<Sigma> has_derivative D) (at x within {(x, y). y \<le> 225 / 10\<^sup>2}) \<and>
                onorm D \<le> 0.06)"
    proof
      fix x
      assume "x \<in> S"
      from vanderpol_derivative_bounds[folded S_def \<Sigma>_def, rule_format, OF this]
      obtain D where D: "vdp.returns_to \<Sigma> x"
        "vdp.poincare_map \<Sigma> x \<in> S"
        "vdp.return_time \<Sigma> differentiable at x within ?S"
        "(vdp.poincare_map \<Sigma> has_derivative blinfun_apply D) (at x within ?S)"
        "D \<in> vdp.blinfuns_of_lvivl ([-0.016, -0.024, 0, 0], [0.021, 0.031, 0, 0])"
        by (auto simp: blinfun_of_list_id2)
      have "onorm D = norm D" by transfer simp
      also from norm_blinfuns_of_ivl2[OF D(5)]
      have "norm D \<le> 0.06" by (simp add: max_def)
      finally show "vdp.poincare_map \<Sigma> x \<in> S \<and>
        (\<exists>D. (vdp.poincare_map \<Sigma> has_derivative D) (at x within ?S) \<and> onorm D \<le> 0.06)"
        using D by auto
    qed
  qed simp
qed

lemma
  notes [poincare_tac_theorems] = vdp_pi_0 vdp_ro vdp_start
  shows "\<forall>x\<in>{(1.41, 2.25) .. (1.42, 2.25)}.
  vdp.returns_to   {(1, 2.25) .. (2, 2.25)} x \<and>
  vdp.poincare_map {(1, 2.25) .. (2, 2.25)} x \<in> {(1.41, 2.25) .. (1.42, 2.25)}"
  unfolding ninequarters
  by (tactic \<open>poincare_bnds_tac @{thms vdp_fas_def} 30 20 7 14 [(0, 1, "0x000000")] "" (* "out_p0_vdp_0.out" *)  @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = vdp_pi_0 vdp_ro vdp_start
  shows "\<forall>x\<in>{(1.35, 2.25) .. (1.45, 2.25)}.
  vdp.returns_to   {(1, 2.25) .. (2, 2.25)} x \<and>
  vdp.poincare_map {(1, 2.25) .. (2, 2.25)} x \<in> {(1.35, 2.25) .. (1.45, 2.25)}"
  unfolding ninequarters
  by (tactic \<open>poincare_bnds_tac @{thms vdp_fas_def} 30 20 7 14 [(0, 1, "0x000000")] "" (* "out_p0_vdp_1.out" *)  @{context} 1\<close>)


subsection \<open>One intermediate Poincare map\<close>

lemma vdp_pi_1: "vdp.guards_invar DIM(real \<times> real) [([xsec2' 1 (-2, 0)], vdp_ro)]"
  by (auto simp: vdp.guards_invar_def)


lemma
  notes [poincare_tac_theorems] = vdp_ro vdp_start vdp_pi_1
  shows "\<forall>x\<in>{(1.41, 2.25) .. (1.42, 2.25)}.
  vdp.returns_to   {(1, 2.25) .. (2, 2.25)} x \<and>
  vdp.poincare_map {(1, 2.25) .. (2, 2.25)} x \<in> {(1.41, 2.25) .. (1.42, 2.25)}"
  unfolding ninequarters
  by (tactic \<open>poincare_bnds_tac @{thms vdp_fas_def} 30 20 7 14 [(0, 1, "0x000000")] "" (* "out_p1_vdp_0.out" *)  @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = vdp_ro vdp_start vdp_pi_1
  shows "\<forall>x\<in>{(1.35, 2.25) .. (1.45, 2.25)}.
  vdp.returns_to   {(1, 2.25) .. (2, 2.25)} x \<and>
  vdp.poincare_map {(1, 2.25) .. (2, 2.25)} x \<in> {(1.35, 2.25) .. (1.45, 2.25)}"
  unfolding ninequarters
  by (tactic \<open>poincare_bnds_tac @{thms vdp_fas_def} 30 20 7 12 [(0, 1, "0x000000")] "" (* "out_p1_vdp_1.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = vdp_ro vdp_start vdp_pi_1
  shows "\<forall>x\<in>{(1.3, 2.25) .. (1.5, 2.25)}.
  vdp.returns_to   {(1, 2.25) .. (2, 2.25)} x \<and>
  vdp.poincare_map {(1, 2.25) .. (2, 2.25)} x \<in> {(1.3, 2.25) .. (1.5, 2.25)}"
  unfolding ninequarters
  by (tactic \<open>poincare_bnds_tac @{thms vdp_fas_def} 30 20 7 12 [(0, 1, "0x000000")] "" (* "out_p1_vdp_2.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = vdp_ro vdp_start vdp_pi_1
  shows "\<forall>x\<in>{(1.15, 2.25) .. (1.65, 2.25)}.
  vdp.returns_to   {(1, 2.25) .. (2, 2.25)} x \<and>
  vdp.poincare_map {(1, 2.25) .. (2, 2.25)} x \<in> {(1.15, 2.25) .. (1.65, 2.25)}"
  unfolding ninequarters
  by (tactic \<open>poincare_bnds_tac @{thms vdp_fas_def} 30 30 7 16 [(0, 1, "0x000000")] "" (* "out_p1_vdp_3.out" *) @{context} 1\<close>)

end


subsection \<open>Example Approximate JNF-Lorenz\<close>
experiment begin

schematic_goal
  lorenz_fas:
  "[11.8 * X!0 - 0.29 * (X!0 + X!1) * X!2,
    -22.8 * X!1 + 0.29*(X!0 + X!1) * X!2,
    -2.67*X!2 + (X!0 + X!1)*(2.2*X!0 - 1.3*X!1)] =
  interpret_floatariths ?fas X"
  by (reify_floatariths)
concrete_definition lorenz_fas uses lorenz_fas

interpretation lorenz: ode_interpretation true_form UNIV lorenz_fas
  "\<lambda>(x1, x2, x3).
    (11.8 * x1 - 0.29 * (x1 + x2) * x3,
    -22.8 * x2 + 0.29*(x1 + x2) * x3,
    -2.67*x3 + (x1 + x2)*(2.2*x1 - 1.3*x2))
    ::real*real*real"
  "three::3"
  by standard
    (auto simp: lorenz_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def isDERIV_Power_iff
      mk_ode_ops_def eucl_of_list_prod power2_eq_square inverse_eq_divide intro!: isFDERIV_I)

abbreviation "lorenz_ro \<equiv> ro 2 10 7 2 2 2"

lemma lorenz_ro: "TAG_reach_optns lorenz_ro" by simp

lemma lorenz_start: "TAG_sctn True" by simp

subsection \<open>No intermediate Poincare map\<close>

lemma lorenz_pi_0: "lorenz.guards_invar DIM(real \<times> real \<times> real) []"
  by (auto simp: lorenz.guards_invar_def)

abbreviation \<Sigma>::"(real * real * real) set"
  where "\<Sigma> \<equiv> {(-6, -6, 27) .. (6, 6, 27)}"

lemma poincare_section_rep[poincare_tac_theorems]:
  "\<Sigma> = {eucl_of_list [-6, -6, 27]..eucl_of_list [6, 6, 27]}"
  by (auto simp: eucl_of_list_prod)

abbreviation "lorenz_iv x y w \<equiv> {(x - w, y - w, 27)..(x + w, y + w, 27)::real*real*real}"

subsection \<open>With intermediate Poincare map\<close>

lemma lorenz_pi_1: "lorenz.guards_invar DIM(real \<times> real \<times> real) [([xsec 2 (-1, 1) (0, 10)], lorenz_ro)]"
  by (auto simp: lorenz.guards_invar_def)

lemma
  notes [poincare_tac_theorems] = lorenz_pi_1 lorenz_ro lorenz_start
  shows "\<forall>x\<in>lorenz_iv 0.84 2.21 0.005.
  lorenz.returns_to   \<Sigma> x \<and>
  lorenz.poincare_map \<Sigma> x \<in> lorenz_iv (-2.17) 0.98 0.3"
  by (tactic \<open>poincare_bnds_tac @{thms lorenz_fas_def} 30 30 9 14 [(0, 2, "0x000000"), (1, 2, "0xff0000")] "" (* "out_p1_lorenz_0.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = lorenz_pi_1 lorenz_ro lorenz_start
  shows "\<forall>x\<in>lorenz_iv 0.86 2.21 0.005.
  lorenz.returns_to   \<Sigma> x \<and>
  lorenz.poincare_map \<Sigma> x \<in> lorenz_iv (-1.8) 1.2 0.2"
  by (tactic \<open>poincare_bnds_tac @{thms lorenz_fas_def} 30 30 9 14 [(0, 2, "0x000000"), (1, 2, "0xff0000")] "" (* "out_p1_lorenz_1.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = lorenz_pi_1 lorenz_ro lorenz_start
  shows "\<forall>x\<in>lorenz_iv 0.88 2.21 0.005.
  lorenz.returns_to   \<Sigma> x \<and>
  lorenz.poincare_map \<Sigma> x \<in> lorenz_iv (-1.58) 1.3 0.1"
  by (tactic \<open>poincare_bnds_tac @{thms lorenz_fas_def} 30 30 9 14 [(0, 2, "0x000000"), (1, 2, "0xff0000")] "" (* "out_p1_lorenz_2.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = lorenz_pi_1 lorenz_ro lorenz_start
  shows "\<forall>x\<in>lorenz_iv 0.90 2.21 0.005.
  lorenz.returns_to   \<Sigma> x \<and>
  lorenz.poincare_map \<Sigma> x \<in> lorenz_iv (-1.4) 1.4 0.1"
  by (tactic \<open>poincare_bnds_tac @{thms lorenz_fas_def} 30 30 9 14 [(0, 2, "0x000000"), (1, 2, "0xff0000")] "" (* "out_p1_lorenz_3.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = lorenz_pi_1 lorenz_ro lorenz_start
  shows "\<forall>x\<in>lorenz_iv 0.92 2.21 0.005.
  lorenz.returns_to   \<Sigma> x \<and>
  lorenz.poincare_map \<Sigma> x \<in> lorenz_iv (-1.24) 1.45 0.1"
  by (tactic \<open>poincare_bnds_tac @{thms lorenz_fas_def} 30 30 9 14 [(0, 2, "0x000000"), (1, 2, "0xff0000")] "" (* "out_p1_lorenz_4.out" *) @{context} 1\<close>)

lemma
  notes [poincare_tac_theorems] = lorenz_pi_1 lorenz_ro lorenz_start
  shows "\<forall>x\<in>lorenz_iv 0.94 2.21 0.005.
  lorenz.returns_to   \<Sigma> x \<and>
  lorenz.poincare_map \<Sigma> x \<in> lorenz_iv (-1.11) 1.5 0.1"
  by (tactic \<open>poincare_bnds_tac @{thms lorenz_fas_def} 30 30 9 14 [(0, 2, "0x000000"), (1, 2, "0xff0000")] "" (* "out_p1_lorenz_5.out" *) @{context} 1\<close>)

end


subsection \<open>Controller 2D\<close>

text \<open>An example from @{cite "barriertubes"}\<close>

experiment begin

schematic_goal c2d:
  "[X!0 * X!1 + (X!1)^3 + 2, (X!0)\<^sup>2 + 2 * (X!0) - 3 * X!1] = interpret_floatariths ?fas X"
  unfolding power2_eq_square power3_eq_cube
  by (reify_floatariths)

concrete_definition c2d uses c2d

interpretation c2d: ode_interpretation true_form UNIV c2d "\<lambda>(x, y). (x*y + y^3 + 2, x\<^sup>2 + 2 * x - 3 * y)::real*real"
  "n::2" for n
  by standard
    (auto simp: c2d_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def power3_eq_cube
      mk_ode_ops_def eucl_of_list_prod power2_eq_square inverse_eq_divide intro!: isFDERIV_I)

abbreviation "options \<equiv> ro 2 10 7 2 2 2"

lemma c2d_pi_1: "c2d.guards_invar DIM(real \<times> real)
  [([ysec2 (-200, 0) 0], options), ([xsec2 0 (0, 100)], options), ([xsec2 75 (0, 100)], options),
    ([xsec2 150 (0, 300)], options), ([xsec2 250 (0, 300)], options)]"
  by (auto simp: c2d.guards_invar_def)

lemma c2d_poincare_section_rep[poincare_tac_theorems]:
  "{(300::real, 0::real)..(300, 300)} = {eucl_of_list [300, 0]..eucl_of_list [300, 300]}"
  by (auto simp: eucl_of_list_prod)

lemma c2d_ro: "TAG_reach_optns options" by simp

lemma c2d_start: "TAG_sctn False" by simp

lemma
  notes [poincare_tac_theorems] = c2d_ro c2d_start c2d_pi_1
  shows "\<forall>x\<in>{(29.9, -38) .. (30.1, -36)}.
  c2d.returns_to   {(300, 0) .. (300, 300)} x \<and>
  c2d.poincare_map_from_outside {(300, 0) .. (300, 300)} x \<in> {(300, 70) .. (300, 80)}"
  using [[ode_numerics_trace]]
  by (tactic \<open>poincare_bnds_tac_gen 20 @{thms c2d_def} 30 20 7 10 [(0, 1, "0x000000")] "-" (* "out_p1_vdp_0.out" *)  @{context} 1\<close>)

end

end
