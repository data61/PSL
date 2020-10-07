theory Refine_Reachability_Analysis_C1
  imports
    Abstract_Reachability_Analysis_C1
    Refine_Reachability_Analysis
begin

lemma fst_flow1_of_vec1[simp]: "fst (flow1_of_vec1 x) = fst x"
  by (auto simp: flow1_of_vec1_def)

lemma fst_vec1_of_flow[simp]: "fst (vec1_of_flow1 x) = fst x"
  by (auto simp: vec1_of_flow1_def)

context approximate_sets_ode'
begin

lemma poincare_mapsto_scaleR2I:
  "poincare_mapsto P (scaleR2 x1 x2 baa) UNIV x1b (scaleR2 x1 x2 aca)"
  if "poincare_mapsto P (baa) UNIV x1b (aca)"
  using that
  apply (auto simp: poincare_mapsto_def scaleR2_def image_def vimage_def)
  apply (drule bspec, assumption)
  apply auto
  apply (rule exI, rule conjI, assumption)
  apply (rule exI, rule conjI, assumption, rule conjI, assumption)
  apply (rule bexI) prefer 2 apply assumption
  apply (auto simp: scaleR_blinfun_compose_right)
  done

context includes ode_ops.lifting begin
lemma var_safe_form_eq[simp]: "var.safe_form = safe_form"
  unfolding var.safe_form_def
  by transfer (auto simp: var_ode_ops_def safe_form_def)

lemma var_ode_e: "var.ode_e = ode_e'"
  unfolding var.ode_e_def
  by transfer (auto simp: var_ode_ops_def)
end

lemma wd_imp_var_wd[refine_vcg, intro]: "wd (TYPE('n rvec)) \<Longrightarrow> var.wd (TYPE('n::enum vec1))"
  unfolding var.wd_def
  by (auto simp: wd_def length_concat o_def sum_list_distinct_conv_sum_set
      concat_map_map_index var_ode_e D_def ode_e'_def
      intro!: max_Var_floatariths_mmult_fa[le] max_Var_floatariths_mapI
      max_Var_floatarith_FDERIV_floatarith[le]
      max_Var_floatariths_fold_const_fa[le]
      max_Var_floatarith_le_max_Var_floatariths_nthI
      max_Var_floatariths_list_updateI max_Var_floatariths_replicateI)

lemma safe_eq:
  assumes "wd TYPE('n::enum rvec)"
  shows "var.Csafe = ((Csafe \<times> UNIV)::'n vec1 set)"
  using assms var.wdD[OF wd_imp_var_wd[OF assms]] wdD[OF assms]
  unfolding var.safe_def safe_def var.wd_def wd_def var.Csafe_def Csafe_def
  unfolding ode_e'_def var_ode_e
  apply (auto simp: D_def)
  subgoal
    apply (subst interpret_form_max_Var_cong) prefer 2 apply assumption
    by (auto simp: nth_Basis_list_prod)
  subgoal for a b
    apply (drule isFDERIV_appendD1)
        apply simp apply simp apply (auto intro!: max_Var_floatariths_fold_const_fa[le])[]
    apply (rule isFDERIV_max_Var_congI, assumption)
    by (auto simp: nth_Basis_list_prod)
  subgoal
    apply (subst interpret_form_max_Var_cong) prefer 2 apply assumption
    by (auto simp: nth_Basis_list_prod)
  subgoal for a b
    apply (rule isFDERIV_appendI1)
    apply (rule isFDERIV_max_Var_congI, assumption)
        apply (auto simp: nth_Basis_list_prod)
     apply (auto simp: isFDERIV_def FDERIV_floatariths_def in_set_conv_nth isDERIV_inner_iff
      length_concat o_def sum_list_distinct_conv_sum_set concat_map_map_index
        intro!: isDERIV_FDERIV_floatarith isDERIV_mmult_fa_nth)
     apply (rule isDERIV_max_Var_floatarithI[where ys="list_of_eucl a"])
    subgoal for i j k
      apply (cases "i < CARD('n)")
      subgoal by auto
      subgoal apply (rule isDERIV_max_VarI)
         apply (rule max_Var_floatarith_le_max_Var_floatariths_nthI)
          apply force
         apply auto
        done
      done
    subgoal for i j k l by (auto dest!: max_Var_floatariths_lessI simp: nth_Basis_list_prod)
    subgoal by (auto simp: nth_list_update)
    done
  done

lemma
  var_ode_eq:
  fixes x::"'n::enum vec1"
  assumes "wd TYPE('n rvec)" and [simp]: "(fst x) \<in> Csafe"
  shows "var.ode x = (ode (fst x), matrix (ode_d1 (fst x)) ** snd x)"
proof -
  have "interpret_floatariths ode_e (list_of_eucl x) =
    interpret_floatariths ode_e (list_of_eucl (fst x))"
    apply (rule interpret_floatariths_max_Var_cong)
    using wdD[OF \<open>wd _\<close>]
    by (auto simp: list_of_eucl_nth_if nth_Basis_list_prod inner_prod_def)
  moreover
  have "eucl_of_list
            (interpret_floatariths
              (mmult_fa D D D
       (concat (map (\<lambda>j. map (\<lambda>i. FDERIV_floatarith (ode_e ! j) [0..<D] ((replicate D 0)[i := 1])) [0..<D]) [0..<D]))
       (map floatarith.Var [D..<D + D * D])) (list_of_eucl x)) =
    matrix (blinfun_apply (ode_d 0 (fst x) 0)) ** snd x"
    unfolding matrix_eq
    apply auto
    apply (subst matrix_vector_mul_assoc[symmetric])
    apply (subst matrix_works)
    subgoal by (auto simp: linear_matrix_vector_mul_eq
          intro!: bounded_linear.linear blinfun.bounded_linear_right)
    apply (subst einterpret_mmult_fa[where 'n='n and 'm = 'n and 'l='n])
    subgoal by (simp add: wdD[OF \<open>wd _\<close>])
    subgoal by (simp add: length_concat o_def sum_list_distinct_conv_sum_set wdD[OF \<open>wd _\<close>])
    subgoal by (simp add: length_concat o_def sum_list_distinct_conv_sum_set wdD[OF \<open>wd _\<close>])
    subgoal for v
    proof -
      have v: "einterpret (map floatarith.Var [D..<D + D * D]) (list_of_eucl x) *v v = snd x *v v"
        apply (vector matrix_vector_mult_def)
        apply (simp add: vec_nth_eq_list_of_eucl2 wdD[OF \<open>wd _\<close>])
        apply (auto simp: vec_nth_eq_list_of_eucl1 sum_index_enum_eq)
        apply (subst sum_index_enum_eq)+
        apply (rule sum.cong)
        by (auto simp: nth_Basis_list_prod prod_eq_iff inner_prod_def)
      show ?thesis
        unfolding matrix_vector_mul_assoc[symmetric]
        apply (subst v)
        apply (auto simp: concat_map_map_index vec_nth_eq_list_of_eucl2)
        apply (subst  eucl_of_list_list_of_eucl[of "snd x *v v", symmetric])
        apply (subst (2) eucl_of_list_list_of_eucl[of "snd x *v v", symmetric])
        apply (subst eucl_of_list_matrix_vector_mult_eq_sum_nth_Basis_list)
        subgoal by (simp add: length_concat o_def sum_list_distinct_conv_sum_set wdD[OF \<open>wd _\<close>])
        subgoal by simp
        apply (subst blinfun_apply_eq_sum)
         apply (auto simp: vec_nth_eq_list_of_eucl1 sum_index_enum_eq)
        apply (auto simp: scaleR_sum_left ode_d.rep_eq intro!: sum.cong[OF refl])
        apply (auto simp: ode_d_raw_def wdD[OF \<open>wd _\<close>] eucl_of_list_inner )
        apply (auto simp: ode_d_expr_def FDERIV_floatariths_def wdD[OF \<open>wd _\<close>] )
        apply (rule interpret_floatarith_FDERIV_floatarith_cong)
        subgoal for x y i
          using wdD[OF \<open>wd _\<close>]
          by (auto simp add: nth_append inner_prod_def
              nth_Basis_list_prod dest!: max_Var_floatariths_lessI)
        subgoal by auto
        subgoal by auto
        subgoal
          apply (auto simp: wdD[OF \<open>wd _\<close>] nth_list_update inner_Basis intro!: nth_equalityI)
          by (metis \<open>length (list_of_eucl (snd x *v v)) = CARD('n)\<close> index_Basis_list_nth length_list_of_eucl)
        done
    qed
    done
  ultimately show ?thesis
    unfolding var.ode_def ode_def
    unfolding ode_e'_def var_ode_e
    by (auto simp: wdD[OF \<open>wd _\<close>] ode_d1_def intro!: euclidean_eqI[where 'a="'n vec1"])
qed

lemma var_existence_ivl_imp_existence_ivl:
  fixes x::"'n::enum vec1"
  assumes wd: "wd TYPE('n rvec)"
  assumes t: "t \<in> var.existence_ivl0 x"
  shows "t \<in> existence_ivl0 (fst x)"
proof (rule existence_ivl_maximal_segment)
  from var.flow_solves_ode[OF UNIV_I var.mem_existence_ivl_iv_defined(2), OF t]
  have D: "(var.flow0 x solves_ode (\<lambda>_. var.ode)) {0--t} (var.Csafe)"
    apply (rule solves_ode_on_subset)
     apply (rule var.closed_segment_subset_existence_ivl)
     apply (rule t)
    apply simp
    done
  show "((\<lambda>t. fst (var.flow0 x t)) solves_ode (\<lambda>_. ode)) {0--t} (Csafe)"
    using var.closed_segment_subset_existence_ivl[OF t]
    apply (auto simp: has_vderiv_on_def has_vector_derivative_def subset_iff
        intro!: solves_odeI derivative_eq_intros)
        apply (rule refl)
       apply (rule refl)
      apply (rule refl)
     apply (auto simp: var.flowderiv_def )
     apply (subst var_ode_eq[OF wd(1)])
      apply (auto simp: blinfun.bilinear_simps)
    subgoal for s
      using solves_odeD(2)[OF D, of s]
      by (subst(asm) (3) safe_eq[OF wd]) (auto )
    subgoal for s
      using solves_odeD(2)[OF D, of s]
      by (subst(asm) (3) safe_eq[OF wd]) (auto )
    done
next
  show "fst (var.flow0 x 0) = fst x"
    apply (subst var.flow_initial_time)
      apply simp
    apply (rule var.mem_existence_ivl_iv_defined[OF t])
    apply auto
    done
qed simp

lemma existence_ivl_imp_var_existence_ivl:
  fixes x::"'n::enum rvec"
  assumes wd: "wd TYPE('n rvec)"
  assumes t: "t \<in> existence_ivl0 x"
  shows "t \<in> var.existence_ivl0 ((x, W)::'n vec1)"
proof (rule var.existence_ivl_maximal_segment)
  from flow_solves_ode[OF UNIV_I mem_existence_ivl_iv_defined(2), OF t]
  have D: "(flow0 x solves_ode (\<lambda>_. ode)) {0--t} (Csafe)"
    apply (rule solves_ode_on_subset)
     apply (rule closed_segment_subset_existence_ivl)
     apply (rule t)
    apply simp
    done
  show "((\<lambda>t. (flow0 x t, matrix (Dflow x t) ** W)) solves_ode (\<lambda>_. var.ode)) {0--t} (var.Csafe)"
    using closed_segment_subset_existence_ivl[OF t]
    apply (auto simp: has_vderiv_on_def has_vector_derivative_def subset_iff
        intro!: solves_odeI derivative_eq_intros)
        apply (rule refl)
        apply (rule refl)
        apply (rule refl)
       apply (rule has_derivative_at_withinI)
       apply (rule Dflow_has_derivative)
       apply force
      apply (rule refl)
     apply (auto simp: flowderiv_def )
     apply (subst var_ode_eq)
     apply (auto simp: blinfun.bilinear_simps matrix_blinfun_compose wd
        intro!: ext)
    subgoal for s h
      unfolding matrix_scaleR matrix_blinfun_compose matrix_mul_assoc matrix_scaleR_right ..
    subgoal for s
      using solves_odeD(2)[OF D, of s] safe_eq[OF wd]
      by auto
    done
next
  have "x \<in> Csafe" by rule fact
  then show "(flow0 x 0, matrix (blinfun_apply (Dflow x 0)) ** W) = (x, W)"
    apply (auto )
    apply (vector matrix_def matrix_matrix_mult_def axis_def)
    by (auto simp:  if_distrib if_distribR cong: if_cong)
qed auto

theorem var_existence_ivl0_eq_existence_ivl0:
  fixes x::"'n::enum vec1"
  assumes wd: "wd TYPE('n rvec)"
  shows "var.existence_ivl0 (x::'n vec1) = existence_ivl0 (fst x)"
  apply safe
  subgoal by (rule var_existence_ivl_imp_existence_ivl[OF wd, of _ "x", simplified], simp)
  subgoal
    by (rule existence_ivl_imp_var_existence_ivl[OF wd, of _ "fst x" "snd x", unfolded prod.collapse])
  done

theorem var_flow_eq_flow_Dflow:
  fixes x::"'n::enum vec1"
  assumes wd: "wd TYPE('n rvec)"
  assumes t: "t \<in> var.existence_ivl0 x"
  shows "var.flow0 x t = vec1_of_flow1 (flow0 (fst x) t, Dflow (fst x) t o\<^sub>L blinfun_of_vmatrix (snd x)) "
proof -
  have x: "x \<in> var.Csafe"
    by (rule var.mem_existence_ivl_iv_defined[OF t])
  then have "fst x \<in> Csafe"
    by (subst (asm) safe_eq[OF wd]) auto
  then have sx[simp]: "(fst x) \<in> Csafe" by simp
  show ?thesis
  proof (rule var.flow_unique_on[OF t])
    show "vec1_of_flow1 (flow0 (fst x) 0, Dflow (fst x) 0 o\<^sub>L blinfun_of_vmatrix (snd x)) = x"
      by (auto simp: vec1_of_flow1_def x)
    show "((\<lambda>a. vec1_of_flow1 (flow0 (fst x) a, Dflow (fst x) a o\<^sub>L blinfun_of_vmatrix (snd x))) has_vderiv_on
     (\<lambda>t. var.ode (vec1_of_flow1 (flow0 (fst x) t, Dflow (fst x) t o\<^sub>L blinfun_of_vmatrix (snd x)))))
     (var.existence_ivl0 x)"
      apply (auto simp: has_vderiv_on_def has_vector_derivative_def vec1_of_flow1_def
          at_within_open[OF _ var.open_existence_ivl] flowderiv_def
          intro!: derivative_eq_intros var_existence_ivl_imp_existence_ivl[OF wd]
          Dflow_has_derivative ext)
      apply (subst var_ode_eq[OF wd(1)])
       apply (auto simp: blinfun.bilinear_simps)
      subgoal for t
        using flow_in_domain[of t "fst x"]
        by (simp add: var_existence_ivl_imp_existence_ivl[OF wd])
      subgoal for t h
        by (simp add: matrix_blinfun_compose matrix_scaleR matrix_mul_assoc matrix_scaleR_right)
      done
    fix t
    assume "t \<in> var.existence_ivl0 x"
    then show "vec1_of_flow1 (flow0 (fst x) t, Dflow (fst x) t o\<^sub>L blinfun_of_vmatrix (snd x)) \<in> var.Csafe"
      by (subst safe_eq[OF wd])
        (auto simp: vec1_of_flow1_def dest!: var_existence_ivl_imp_existence_ivl[OF wd]
          flow_in_domain)
  qed
qed

theorem flow_Dflow_eq_var_flow:
  fixes x::"'n::enum rvec"
  assumes wd: "wd TYPE('n rvec)"
  assumes t: "t \<in> existence_ivl0 x"
  shows "(flow0 x t, Dflow x t o\<^sub>L W) = flow1_of_vec1 (var.flow0 (x, matrix W) t::'n vec1)"
  using var_flow_eq_flow_Dflow[OF wd existence_ivl_imp_var_existence_ivl[OF wd t]]
  unfolding var_flow_eq_flow_Dflow[OF wd existence_ivl_imp_var_existence_ivl[OF wd t]]
  by (auto simp: flow1_of_vec1_def vec1_of_flow1_def)

context includes blinfun.lifting begin
lemma flow1_of_vec1_vec1_of_flow1[simp]:
  "flow1_of_vec1 (vec1_of_flow1 X) = X"
  unfolding vec1_of_flow1_def flow1_of_vec1_def
  by (transfer) auto
end

lemma
  var_flowpipe0_flowpipe:
  assumes wd: "wd TYPE('n::enum rvec)"
  assumes "var.flowpipe0 X0 hl hu (CX) X1"
  assumes "fst ` X0 \<subseteq> Csafe"
  assumes "fst ` CX \<subseteq> Csafe"
  assumes "fst ` X1 \<subseteq> Csafe"
  shows "flowpipe (flow1_of_vec1 ` X0) hl hu (flow1_of_vec1 ` (CX::'n vec1 set)) (flow1_of_vec1 ` X1)"
  using assms
  unfolding flowpipe_def var.flowpipe0_def
  apply safe
  subgoal by (auto simp add: flow1_of_vec1_def vec1_of_flow1_def safe_eq[OF wd])
  subgoal by (auto simp add: flow1_of_vec1_def vec1_of_flow1_def safe_eq[OF wd])
  subgoal by (auto simp add: flow1_of_vec1_def vec1_of_flow1_def safe_eq[OF wd])
  subgoal for x W y V h
    apply (drule bspec[where x="(y, V)"], force)
    apply (drule bspec, assumption)
    by (simp add: var_existence_ivl0_eq_existence_ivl0[OF wd] flow1_of_vec1_def)
  subgoal for x W y V h
    apply (drule bspec[where x="(y, V)"], force)
    apply (drule bspec, assumption)
    apply (subst flow_Dflow_eq_var_flow[OF wd],
        force simp: var_existence_ivl0_eq_existence_ivl0[OF wd] flow1_of_vec1_def)
    apply (rule imageI)
    by (simp add: vec1_of_flow1_def flow1_of_vec1_def)
  subgoal for x W y V h h'
    apply (drule bspec[where x="vec1_of_flow1 (x, W)"], force)
    apply (drule bspec, assumption)
    apply (subst flow_Dflow_eq_var_flow[OF wd])
     apply (subst (asm) var_existence_ivl0_eq_existence_ivl0[OF wd])
     apply (simp add: flow1_of_vec1_def)
    subgoal
      by (meson local.existence_ivl_initial_time local.mem_existence_ivl_iv_defined(1)
          local.mem_existence_ivl_iv_defined(2) mem_is_interval_1_I mvar.interval)
    subgoal
      apply (rule imageI)
      by (simp add: vec1_of_flow1_def flow1_of_vec1_def)
    done
  done

theorem einterpret_solve_poincare_fas:
  assumes wd: "wd TYPE('n rvec)"
  assumes "length CXs = D + D*D" "n < D"
  assumes nz: "ode (fst (eucl_of_list CXs::'n vec1)) \<bullet> Basis_list ! n \<noteq> 0"
  shows
  "flow1_of_vec1 (einterpret (solve_poincare_fas n) CXs::'n::enum vec1) =
  (let (x, d) = flow1_of_vec1 (eucl_of_list CXs::'n vec1) in (x,
     d - (blinfun_scaleR_left (ode (x)) o\<^sub>L
    (blinfun_scaleR_left (inverse (ode x \<bullet> Basis_list ! n)) o\<^sub>L (blinfun_inner_left (Basis_list ! n) o\<^sub>L d)))))"
  using assms
  apply (auto intro!: simp: flow1_of_vec1_def solve_poincare_fas_def)
  subgoal
    apply (auto intro!: euclidean_eqI[where 'a="'n rvec"])
    apply (subst eucl_of_list_prod)
    by (auto simp: eucl_of_list_prod length_concat o_def sum_list_distinct_conv_sum_set D_def Let_def
        wdD[OF wd] take_eq_map_nth)
  subgoal premises prems
  proof -
    have ode_e_eq: "interpret_floatarith (ode_e ! i) (map ((!) CXs) [0..<CARD('n)]) = interpret_floatarith (ode_e ! i) CXs"
      if "i < D"
      for i
      apply (rule interpret_floatarith_max_Var_cong)
      apply (drule max_Var_floatariths_lessI)
      using that apply (simp add: wdD[OF wd])
      apply (subst nth_map)
       apply auto
      using wdD[OF wd]
      apply (simp add: )
      using wdD[OF wd]
      apply (simp add: )
      done
    define z where "z = (0::float)"
    show ?thesis
      supply [simp] = snd_eucl_of_list_prod fst_eucl_of_list_prod
      supply [simp del] = eucl_of_list_take_DIM
      using prems unfolding z_def[symmetric] D_def Let_def
      including blinfun.lifting
      apply (transfer fixing: CXs n z)
      unfolding z_def
      apply (auto simp: o_def ode_def intro!: ext)
      apply (vector matrix_vector_mult_def )
      apply (auto intro!: blinfun_euclidean_eqI simp: inner_Basis_eq_vec_nth wdD[OF wd])
      apply (auto simp: length_concat o_def sum_list_distinct_conv_sum_set wdD[OF wd] take_eq_map_nth)
      apply (auto simp: concat_map_map_index)
      apply (vector )
      apply (subst vec_nth_eq_list_of_eucl2 vec_nth_eq_list_of_eucl1)+
      apply (subst (asm) vec_nth_eq_list_of_eucl2 vec_nth_eq_list_of_eucl1)+
      apply (simp add: less_imp_le wdD[OF wd] index_nth_id )
      apply (auto simp: algebra_simps ode_e_eq wdD[OF wd] divide_simps)
      done
  qed
  done

lemma choose_step'_flowpipe:
  assumes wd[refine_vcg]: "wd TYPE('n::enum rvec)"
  assumes safe: "fst ` X0 \<subseteq> Csafe"
  shows "var.choose_step (X0::'n vec1 set) h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES::'n vec1 set).
      0 < h' \<and> h' \<le> h \<and> flowpipe (flow1_of_vec1 ` X0) h' h' (flow1_of_vec1 ` RES_ivl) (flow1_of_vec1 ` RES))"
  apply refine_vcg
  apply (auto simp: )
  apply (frule var.flowpipe0_safeD)
  apply (drule var_flowpipe0_flowpipe[rotated])
  by (auto simp: safe_eq wd)

lemma max_Var_floatariths_solve_poincare_fas[le]:
  assumes wd: "wd (TYPE('n::enum rvec))"
  shows "i < D \<Longrightarrow> max_Var_floatariths (solve_poincare_fas i) \<le> D + D * D"
  by (auto simp: solve_poincare_fas_def concat_map_map_index Let_def
      intro!: max_Var_floatariths_leI Suc_leI)
   (auto intro!: max_Var_floatarith_le_max_Var_floatariths_nthI max_Var_floatariths_ode_e_wd[OF wd]
      simp: wdD[OF wd])

lemma length_solve_poincare_fas[simp]: "length (solve_poincare_fas n) = D + D * D"
  by (auto simp: solve_poincare_fas_def length_concat o_def sum_list_distinct_conv_sum_set D_def Let_def)

theorem interpret_floatariths_solve_poincare_fas:
  assumes wd: "wd TYPE('n::enum rvec)"
  assumes "length CXs = D + D*D" "n < D"
  assumes nz: "ode (fst (eucl_of_list CXs::'n vec1)) \<bullet> Basis_list ! n \<noteq> 0"
  shows
  "interpret_floatariths (solve_poincare_fas n) CXs =
    list_of_eucl (vec1_of_flow1 (let (x, d) = flow1_of_vec1 (eucl_of_list CXs::'n vec1) in (x,
       d - (blinfun_scaleR_left (ode (x)) o\<^sub>L
      (blinfun_scaleR_left (inverse (ode x \<bullet> Basis_list ! n)) o\<^sub>L (blinfun_inner_left (Basis_list ! n) o\<^sub>L d))))))"
  using arg_cong[where f="list_of_eucl::'n vec1 \<Rightarrow> _", OF arg_cong[where f=vec1_of_flow1, OF einterpret_solve_poincare_fas[OF assms]]]
  apply (auto simp: )
  apply (subst (asm) list_of_eucl_eucl_of_list)
   apply (auto simp: )
  apply (auto simp: wdD[OF wd])
  done

lemma length_solve_poincare_slp[simp]: "length solve_poincare_slp = D"
  by (auto simp: solve_poincare_slp_def)

lemma ne_zero_lemma:
  assumes
    "ode ` fst ` CX \<subseteq> FC"
   "\<forall>b\<in>FC. b \<bullet> n \<noteq> 0"
   "(a, b) \<in> CX"
   "ode a \<bullet> n = 0"
 shows "False"
proof -
  have "(a, b) \<in> CX" by fact
  then have "ode (fst (a, b)) \<in> ode ` fst ` CX" by blast
  also have "\<dots> \<subseteq> FC"
    by fact
  finally have "ode a \<in> FC" by simp
  with assms show False
    by auto
qed

lemma ne_zero_lemma2:
  assumes
   "ode ` fst ` flow1_of_vec1 ` env \<subseteq> F"
   "\<forall>x\<in>F. x \<bullet> n \<noteq> 0"
   "(a, b) \<in> env"
   "flow1_of_vec1 (a, b) = (a', b')"
   "ode a' \<bullet> n = 0"
 shows False
proof -
  have "(a', b') \<in> flow1_of_vec1 ` env"
    apply (rule image_eqI)
    using assms by auto
  then have "ode (fst (a', b')) \<in> ode ` fst ` \<dots>" by blast
  also from assms have "\<dots> \<subseteq> F" by simp
  finally have "ode a' \<in> F" by simp
  with assms have "ode a' \<bullet> n \<noteq> 0" by auto
  with assms show False by simp
qed

lemma solve_poincare_plane[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  assumes "n \<in> Basis"
  shows "solve_poincare_plane (n::'n::enum rvec) CX \<le> SPEC (\<lambda>PDP.
    fst ` PDP \<subseteq> Csafe \<and>
    (\<forall>(x, d) \<in> CX. (x, d - (blinfun_scaleR_left (ode x) o\<^sub>L
      (blinfun_scaleR_left (inverse (ode x \<bullet> n)) o\<^sub>L (blinfun_inner_left n o\<^sub>L d)))) \<in> PDP) \<and>
    (\<forall>(x, d) \<in> PDP. ode x \<bullet> n \<noteq> 0))"
  unfolding solve_poincare_plane_def
  apply (refine_vcg)
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by (auto simp: solve_poincare_slp_def)
  subgoal using assms by auto
  subgoal for C1 FC _ CX' CX'' P P1 FP _
    apply auto
    apply (drule bspec, assumption)
    apply (rule image_eqI)
     prefer 2 apply assumption
    apply (subst einterpret_solve_poincare_fas)
    subgoal using wd by auto
    subgoal using wd by auto
    subgoal using wd by auto
    subgoal using wd assms by (auto elim!: ne_zero_lemma)
    subgoal using wd assms by (auto simp: )
    done
  subgoal by (auto elim!: ne_zero_lemma2)
  done

lemma choose_step1_flowpipe[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd TYPE('n::enum rvec)"
  shows "choose_step1 (X0::'n eucl1 set) h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES::'n eucl1 set).
      0 < h' \<and> h' \<le> h \<and> flowpipe X0 h' h' RES_ivl RES)"
  using assms
  unfolding choose_step1_def
  by (refine_vcg choose_step'_flowpipe[le] wd)
    (auto simp: image_image,
      auto simp: safe_eq vec1_of_flow1_def flowpipe0_imp_flowpipe env_len_def)

lemma image_flow1_of_vec1I:
  "vec1_of_flow1 x \<in> X \<Longrightarrow> x \<in> flow1_of_vec1 ` X"
  by (rule image_eqI) (rule flow1_of_vec1_vec1_of_flow1[symmetric])

lemma inter_sctn1_spec[le, refine_vcg]:
  "inter_sctn1_spec X sctn \<le> SPEC (\<lambda>(R, S). X \<inter> plane_of sctn \<times> UNIV \<subseteq> R \<and> fst ` R \<subseteq> plane_of sctn
  \<and> X \<inter> plane_of sctn \<times> UNIV \<subseteq> S \<and> fst ` S \<subseteq> plane_of sctn)"
  unfolding inter_sctn1_spec_def
  apply (refine_vcg, auto)
  subgoal by (rule image_flow1_of_vec1I) (auto simp: plane_of_def inner_prod_def)
  subgoal by (auto simp: plane_of_def inner_prod_def)
  subgoal by (rule image_flow1_of_vec1I)
         (force simp: set_plus_def plane_of_def inner_prod_def vec1_of_flow1_def)
  subgoal by (force simp: set_plus_def)
  done

lemma fst_safe_coll[le, refine_vcg]:
  "wd TYPE('a) \<Longrightarrow>
      fst_safe_coll (X::('a::executable_euclidean_space*'c) set) \<le> SPEC (\<lambda>R. R = fst ` X \<and> fst ` X \<subseteq> Csafe)"
  unfolding fst_safe_coll_def
  by refine_vcg

lemma vec1reps[THEN order_trans, refine_vcg]: "vec1reps CX \<le> SPEC (\<lambda>R. case R of None \<Rightarrow> True | Some X \<Rightarrow> X = vec1_of_flow1 ` CX)"
  unfolding vec1reps_def
  apply (refine_vcg FORWEAK_mono_rule[where
        I="\<lambda>XS R. case R of None \<Rightarrow> True | Some R \<Rightarrow> vec1_of_flow1 ` (\<Union>XS) \<subseteq> R \<and> R \<subseteq> vec1_of_flow1 ` CX"])
  by (auto simp:  split: option.splits) force+

lemma nonzero_component_within[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  shows "nonzero_component_within ivl sctn (PDP::'n eucl1 set) \<le> SPEC (\<lambda>b.
    (b \<longrightarrow> (\<forall>x\<in>PDP. fst x \<in> ivl \<and> (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl))) \<and>
    fst ` PDP \<subseteq> Csafe \<and>
    (\<forall>x\<in>PDP. ode (fst x) \<bullet> normal sctn \<noteq> 0))"
  unfolding nonzero_component_within_def
  by refine_vcg auto

lemma do_intersection_invar_inside:
  "do_intersection_invar guards b ivl sctn X (e, f, m, n, p, q, True) \<Longrightarrow>
  fst ` e \<subseteq> sabove_halfspace sctn \<Longrightarrow>
  fst ` mn \<subseteq> ivl \<Longrightarrow>
  mn = m \<or> mn = n \<Longrightarrow>
  do_intersection_spec UNIV guards ivl sctn X (mn, p)"
  subgoal premises prems
  proof -
    from prems have e: "e \<inter> sbelow_halfspace sctn \<times> UNIV = {}"
      by (auto simp: halfspace_simps plane_of_def)
    with prems(1) have
      "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} X UNIV p m"
      "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} X UNIV p n"
      "e \<inter> sbelow_halfspace sctn \<times> UNIV = {}"
      "fst ` X \<inter> b = {}"
      "fst ` X \<subseteq> sbelow_halfspace sctn"
      "ivl \<subseteq> plane (normal sctn) (pstn sctn)"
      "fst ` X \<subseteq> p"
      "fst ` m \<subseteq> Csafe"
      "fst ` n \<subseteq> Csafe"
      "p \<subseteq> Csafe"
      "fst ` e \<subseteq> Csafe"
      "f \<subseteq> {0..}"
      "p \<subseteq> sbelow_halfspace sctn - guards"
      "e \<subseteq> (- guards) \<times> UNIV"
      "fst ` (m \<union> n) \<inter> guards = {}"
      "0 \<notin> (\<lambda>x. ode x \<bullet> normal sctn) ` fst ` (m \<union> n)"
      "\<forall>x\<in>m \<union> n. \<forall>\<^sub>F x in at (fst x) within plane (normal sctn) (pstn sctn). x \<in> ivl"
      by (auto simp: do_intersection_invar_def do_intersection_spec_def plane_of_def)
    then show ?thesis
      using prems(2-)
      by (auto simp: do_intersection_spec_def plane_of_def halfspace_simps)
  qed
  done

lemma do_intersection_body_lemma:
  assumes "flowsto A T (i \<times> UNIV) (X' \<inter> sbelow_halfspace sctn \<times> UNIV)"
    "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV i PS "
    "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV i PS2"
    "T \<subseteq> {0..}"
    "i \<subseteq> sbelow_halfspace sctn - guards"
    "fst ` (A \<union> B) \<subseteq> sbelow_halfspace sctn"
    "fst ` PS \<subseteq> Csafe "
    "fst ` PS2 \<subseteq> Csafe "
    \<open>X = A \<union> B\<close>
  assumes ivl: "closed ivl" "ivl \<subseteq> plane_of sctn"
  assumes normal_Basis: "\<bar>normal sctn\<bar> \<in> Basis"
    and inter_empties: "fst ` Y \<inter> GUARDS = {}" "fst ` CX' \<inter> GUARDS = {}"
    "fst ` PDP' \<inter> GUARDS = {}" "fst ` PDP'' \<inter> GUARDS = {}"
    and h': "0 < h'" "h' \<le> h"
    and safe: "fst ` PDP \<subseteq> Csafe" "fst ` CX' \<subseteq> Csafe"
    "fst ` PDP' \<subseteq> Csafe"
    "fst ` PDP'' \<subseteq> Csafe"
    and PDP:
    "\<forall>(x,d)\<in>CX'. (x,
            d - (blinfun_scaleR_left (ode x) o\<^sub>L
                  (blinfun_scaleR_left (inverse (ode x \<bullet> \<bar>normal sctn\<bar>)) o\<^sub>L
                  (blinfun_inner_left \<bar>normal sctn\<bar> o\<^sub>L d))))
               \<in> PDP"
    and PDP': "PDP \<inter> plane_of sctn \<times> UNIV \<subseteq> PDP'"
    and PDP'': "PDP \<inter> plane_of sctn \<times> UNIV \<subseteq> PDP''"
    and evin:
    "\<forall>x\<in>PDP'. fst x \<in> ivl \<and> (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl)"
    "\<forall>x\<in>PDP''. fst x \<in> ivl \<and> (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl)"
    and through: "\<forall>(x, d)\<in>PDP. ode x \<bullet> \<bar>normal sctn\<bar> \<noteq> 0"
    "\<forall>x\<in>PDP'. ode (fst x) \<bullet> normal sctn \<noteq> 0"
    "\<forall>x\<in>PDP''. ode (fst x) \<bullet> normal sctn \<noteq> 0"
    and plane:
    "fst ` PDP' \<subseteq> plane_of sctn"
    "fst ` PDP'' \<subseteq> plane_of sctn"
    and flowpipe: "flowpipe X' h' h' CX' Y"
  shows "\<exists>A B. X = A \<union> B \<and>
        flowsto A {0<..} ((fst ` CX' \<inter> sbelow_halfspace sctn \<union> i) \<times> UNIV) (Y \<inter> sbelow_halfspace sctn \<times> UNIV) \<and>
        poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV (fst ` CX' \<inter> sbelow_halfspace sctn \<union> i) (PDP' \<union> PS) \<and>
        poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV (fst ` CX' \<inter> sbelow_halfspace sctn \<union> i) (PDP'' \<union> PS2)"
proof -
  from flowpipe
  have 1: "flowpipe (X' \<inter> (sbelow_halfspace sctn) \<times> UNIV) h' h' CX' Y"
    by (rule flowpipe_subset) (use flowpipe in \<open>auto dest!: flowpipe_safeD\<close>)
  have 2: "fst ` (X' \<inter> (sbelow_halfspace sctn) \<times> UNIV) \<inter> {x. pstn sctn \<le> x \<bullet> normal sctn} = {}"
    by (auto simp: halfspace_simps plane_of_def)
  from normal_Basis have 3: "normal sctn \<noteq> 0"
    by (auto simp: )
  note 4 = \<open>closed ivl\<close>
  from \<open>ivl \<subseteq> plane_of sctn\<close> have 5: "ivl \<subseteq> plane (normal sctn) (pstn sctn)"
    by (auto simp: plane_of_def)
  have 6: "(x, d) \<in> CX' \<Longrightarrow> x \<in> plane (normal sctn) (pstn sctn) \<Longrightarrow>
          (x, d - (blinfun_scaleR_left (ode x) o\<^sub>L
                   (blinfun_scaleR_left (inverse (ode x \<bullet> normal sctn)) o\<^sub>L (blinfun_inner_left (normal sctn) o\<^sub>L d))))
          \<in> PDP' \<inter> PDP''" for x d
    unfolding PDP_abs_lemma[OF normal_Basis]
    apply (drule PDP[rule_format, of "(x, d)", unfolded split_beta' fst_conv snd_conv])
    using PDP' PDP''
    by (auto simp: plane_of_def)
  from normal_Basis through
  have 7: "(x, d) \<in> PDP' \<Longrightarrow> ode x \<bullet> normal sctn \<noteq> 0" for x d
    by (auto elim!: abs_in_BasisE)
  have 8: "(x, d) \<in> PDP' \<Longrightarrow> x \<in> ivl" for x d
    using evin by auto
  have 9: "(x, d) \<in> PDP' \<Longrightarrow> \<forall>\<^sub>F x in at x within plane (normal sctn) (pstn sctn). x \<in> ivl" for x d
    using evin by (auto simp add: plane_of_def)
  obtain X1 X2
    where X1X2: "X' \<inter> sbelow_halfspace sctn \<times> UNIV = X1 \<union> X2"
      and X1: "flowsto X1 {0<..h'} (CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn} \<times> UNIV)
                      (CX' \<inter> {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} \<times> UNIV)"
      and X2: "flowsto X2 {h'..h'} (CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn} \<times> UNIV)
                      (Y \<inter> {x. x \<bullet> normal sctn < pstn sctn} \<times> UNIV)"
      and P: "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} X1 UNIV
                      (fst ` CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn}) (PDP' \<inter> PDP'')"
    by (rule flowpipe_split_at_above_halfspace[OF 1 2 3 4 5 6 7 8 9]) (auto simp: Ball_def)
  from \<open>flowsto A _ _ _\<close>[unfolded X1X2]
  obtain p1 p2 where p1p2: "A = p1 \<union> p2" and p1: "flowsto p1 T (i \<times> UNIV) X1" and p2: "flowsto p2 T (i \<times> UNIV) X2"
    by (rule flowsto_unionE)
  have "A \<union> B = p2 \<union> (p1 \<union> B)" using \<open>A = p1 \<union> p2\<close>
    by auto
  moreover
  from flowsto_trans[OF p2 X2]
  have "flowsto p2 {0<..} ((fst ` CX' \<inter> (sbelow_halfspace sctn) \<union> i) \<times> UNIV)
           (Y \<inter> (sbelow_halfspace sctn) \<times> UNIV)"
    apply (rule flowsto_subset)
    subgoal by (auto simp: halfspace_simps)
    subgoal using h' \<open>T \<subseteq> _\<close> by (auto simp: halfspace_simps intro!: add_nonneg_pos)
    subgoal
      using flowpipe_source_subset[OF 1, unfolded X1X2] X1X2
      apply auto
      by (auto simp: halfspace_simps)
    subgoal by (auto simp: halfspace_simps)
    done
  moreover
  have cls: "closed {x \<in> ivl. x \<bullet> normal sctn = pstn sctn}"
    by (rule closed_levelset_within continuous_intros \<open>closed ivl\<close>)+
  from flowsto_trans[OF p1 X1]
  have ftt: "flowsto p1 ({s + t |s t. s \<in> T \<and> t \<in> {0<..h'}})
       (i \<times> UNIV \<union> CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn} \<times> UNIV \<union> X1 \<inter> X1)
       (X1 - X1 \<union> CX' \<inter> {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} \<times> UNIV)"
    by auto
  from X1X2 have X1_sb: "X1 \<subseteq> sbelow_halfspace sctn \<times> UNIV" by auto
  have "{x \<in> ivl. x \<bullet> normal sctn = pstn sctn} \<times> UNIV \<inter> (i \<times> UNIV \<union> CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn} \<times> UNIV \<union> X1) = {}"
    apply (intro Int_Un_eq_emptyI)
    subgoal using \<open>i \<subseteq> sbelow_halfspace sctn - guards\<close> by (auto simp: halfspace_simps)
    subgoal by (auto simp: halfspace_simps)
    subgoal using X1_sb by (auto simp: halfspace_simps)
    done
  then have inter_empty:
    "{x \<in> ivl. x \<bullet> normal sctn = pstn sctn} \<times> UNIV \<inter> (i \<times> UNIV \<union> CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn} \<times> UNIV \<union> X1 \<inter> X1) = {}"
    by auto
  have p1ret: "returns_to {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x"
    and p1pm: "poincare_map {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x \<in> fst ` (PDP' \<inter> PDP'')"
    if "(x, d) \<in> p1" for x d
     apply (rule flowsto_poincareD[OF ftt _ inter_empty _ _ _ order_refl])
    subgoal by auto
    subgoal by fact
    subgoal using \<open>T \<subseteq> _\<close> by auto
    subgoal using that by auto
    subgoal
      apply (rule flowsto_poincareD[OF ftt _ inter_empty])
      subgoal by auto
      subgoal by fact
      subgoal using \<open>T \<subseteq> _\<close> by auto
      subgoal using that by auto
      subgoal using 6 by force
      done
    done
  have crt: "isCont (return_time {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0}) x" if "(x, d) \<in> p1" for x d
    apply (rule return_time_isCont_outside[where Ds="\<lambda>_. blinfun_inner_left (normal sctn)"])
    subgoal by (simp add: p1ret[OF that])
    subgoal by fact
    subgoal by (auto intro!: derivative_eq_intros)
    subgoal by simp
    subgoal apply simp
      using p1pm[OF that]
      by (auto dest!: 7)
    subgoal
      using p1pm[OF that]
      by (auto dest!: 9 simp: eventually_at_filter)
    subgoal
      using \<open>fst ` (A \<union> B) \<subseteq> sbelow_halfspace sctn\<close> that p1p2
      by (auto simp: halfspace_simps)
    done
  have pmij: "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} p1 UNIV
        (fst ` (i \<times> UNIV \<union> X1) \<union> fst ` CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn}) (PDP' \<inter> PDP'')"
    apply (rule flowsto_poincare_trans[OF \<open>flowsto _ _ _ X1\<close> P])
    subgoal using \<open>T \<subseteq> {0..}\<close> by auto
    subgoal by auto
    subgoal
      using \<open>i \<subseteq> sbelow_halfspace sctn - guards\<close> X1X2
      by (force simp: halfspace_simps)
    subgoal by fact
    subgoal for x d using crt by simp
    subgoal by auto
    done
  from pmij have "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} p1 UNIV (fst ` (i \<times> UNIV \<union> X1) \<union> fst ` CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn}) PDP'"
    apply (rule poincare_mapsto_subset)
    using \<open>fst ` PDP' \<subseteq> Csafe\<close>
    by auto
  from this \<open>poincare_mapsto _ _ _ i PS\<close>
  have "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} (p1 \<union> B) UNIV
      ((fst ` (i \<times> UNIV \<union> X1) \<union> fst ` CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn}) \<union> i) (PDP' \<union> PS)"
    by (intro poincare_mapsto_unionI) (auto simp: plane_of_def)
  then have "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} (p1 \<union> B) UNIV (fst ` CX' \<inter> sbelow_halfspace sctn \<union> i) (PDP' \<union> PS)"
    apply (rule poincare_mapsto_subset)
    subgoal by auto
    subgoal by auto
    subgoal
      using flowpipe_source_subset[OF 1, unfolded X1X2] X1X2 
      apply (auto simp: halfspace_simps subset_iff)
      done
    subgoal using safe \<open>fst ` PS \<subseteq> Csafe\<close> by auto
    done
  moreover
  from pmij have "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} p1 UNIV (fst ` (i \<times> UNIV \<union> X1) \<union> fst ` CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn}) PDP''"
    apply (rule poincare_mapsto_subset)
    using \<open>fst ` PDP'' \<subseteq> Csafe\<close>
    by auto
  from this \<open>poincare_mapsto _ _ _ i PS2\<close>
  have "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} (p1 \<union> B) UNIV
      ((fst ` (i \<times> UNIV \<union> X1) \<union> fst ` CX' \<inter> {x. x \<bullet> normal sctn < pstn sctn}) \<union> i) (PDP'' \<union> PS2)"
    by (intro poincare_mapsto_unionI) (auto simp: plane_of_def)
  then have "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} (p1 \<union> B) UNIV (fst ` CX' \<inter> sbelow_halfspace sctn \<union> i) (PDP'' \<union> PS2)"
    apply (rule poincare_mapsto_subset)
    subgoal by auto
    subgoal by auto
    subgoal
      using flowpipe_source_subset[OF 1, unfolded X1X2] X1X2
      apply (auto simp: halfspace_simps subset_iff)
      done
    subgoal using safe \<open>fst ` PS2 \<subseteq> Csafe\<close> by auto
    done
  ultimately
  show ?thesis
    unfolding \<open>X = A \<union> B\<close> by blast
qed

lemma do_intersection_body_spec:
  fixes guards::"'n::enum rvec set"
  assumes invar: "do_intersection_invar guards GUARDS ivl sctn X (X', T, PS, PS2, i, True, True)"
    and wdp[refine_vcg]: "wd TYPE('n rvec)"
    and X: "fst ` X \<subseteq> Csafe"
    and ivl: "closed ivl" and GUARDS: "guards \<subseteq> GUARDS"
  shows "do_intersection_body GUARDS ivl sctn h (X', T, PS, PS2, i, True, True) \<le>
    SPEC (do_intersection_invar guards GUARDS ivl sctn X)"
proof -
  from invar
  obtain A B where AB: "fst ` (A \<union> B) \<inter> GUARDS = {} "
    "fst ` (A \<union> B) \<subseteq> sbelow_halfspace sctn "
    "ivl \<subseteq> plane_of sctn "
    "fst ` (A \<union> B) \<subseteq> i "
    "fst ` PS \<subseteq> Csafe "
    "fst ` PS2 \<subseteq> Csafe "
    "i \<subseteq> Csafe "
    "fst ` X' \<subseteq> Csafe "
    "T \<subseteq> {0..}"
    "i \<subseteq> sbelow_halfspace sctn - guards "
    "X' \<subseteq> (- guards) \<times> UNIV "
    "fst ` (PS \<union> PS2) \<inter> guards = {} "
    "0 \<notin> (\<lambda>x. ode x \<bullet> normal sctn) ` fst ` (PS \<union> PS2) "
    "\<forall>x\<in>PS \<union> PS2. \<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl "
    "X = A \<union> B "
    "flowsto A T (i \<times> UNIV) (X' \<inter> sbelow_halfspace sctn \<times> UNIV)"
    "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV i PS "
    "poincare_mapsto {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} B UNIV i PS2"
    by (auto simp: do_intersection_invar_def)

  have ev_in_ivl: "\<forall>\<^sub>F x in at p within plane_of sctn. x \<in> ivl" if
    \<open>\<forall>x\<in>d. fst x \<in> ivl \<and> (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl)\<close>
    \<open>\<forall>x\<in>e. fst x \<in> ivl \<and> (\<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl)\<close>
    \<open>(p, q) \<in> d \<or> (p, q) \<in> PS \<or> (p, q) \<in> e \<or> (p, q) \<in> PS2\<close>
    for p q d e
      using \<open>\<forall>x\<in>PS \<union> PS2. \<forall>\<^sub>F x in at (fst x) within plane_of sctn. x \<in> ivl\<close>
      using that
      by (auto dest!: bspec[where x="(p, q)"])

  show ?thesis
    unfolding do_intersection_body_def do_intersection_invar_def
    apply simp
    apply (refine_vcg, clarsimp_all)
    subgoal using AB by (auto simp: )
    subgoal using AB by (auto simp: )
    subgoal using AB by (auto simp: )
    subgoal
      apply (rule conjI)
      subgoal using AB by auto\<comment> \<open>unnecessarily slow\<close>
      subgoal using AB by fastforce
      done
    subgoal using AB by (auto simp: )
    subgoal using AB by (auto simp: )
    subgoal using AB by (auto simp: )
    subgoal by (auto dest!: flowpipe_safeD)
    subgoal
      apply safe
      subgoal using AB GUARDS by auto
      subgoal using AB by auto
      subgoal using AB by auto
      subgoal using AB GUARDS by auto
      subgoal using AB by auto
      subgoal using AB by auto
      done
    subgoal using AB GUARDS by auto
    subgoal using AB GUARDS by auto\<comment> \<open>unnecessarily slow\<close>
    subgoal using AB GUARDS by auto
    subgoal using AB assms by (auto intro: ev_in_ivl)
    subgoal using AB assms apply - by (rule do_intersection_body_lemma)
    done
qed

lemma
  do_intersection_spec[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  shows "do_intersection guards ivl sctn (X::'n eucl1 set) h \<le>
    SPEC (\<lambda>(inside, P, P2, CX). (inside \<longrightarrow>
      (do_intersection_spec UNIV guards ivl sctn X (P, CX) \<and>
       do_intersection_spec UNIV guards ivl sctn X (P2, CX)) \<and> fst ` X \<subseteq> CX))"
  using assms
  unfolding do_intersection_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all)
  subgoal
    unfolding do_intersection_invar_def
    apply clarsimp
    apply (intro conjI)
       apply force
      apply force
     apply force
    apply (rule exI[where x=X])
    apply (rule exI[where x="{}"])
    by (auto intro!: flowsto_self)
  subgoal by (rule do_intersection_body_spec)
  subgoal by (rule do_intersection_invar_inside, assumption) auto
  subgoal by (rule do_intersection_invar_inside, assumption) auto
  subgoal by (auto simp: plane_of_def halfspace_simps do_intersection_invar_def)
  done

lemma mem_flow1_of_vec1_image_iff[simp]:
  "(c, d) \<in> flow1_of_vec1 ` a \<longleftrightarrow> vec1_of_flow1 (c, d) \<in> a"
  by force

lemma mem_vec1_of_flow1_image_iff[simp]:
  "(c, d) \<in> vec1_of_flow1 ` a \<longleftrightarrow> flow1_of_vec1 (c, d) \<in> a"
  by force

lemma split_spec_param1[le, refine_vcg]: "split_spec_param1 X \<le> SPEC (\<lambda>(A, B). X \<subseteq> A \<union> B)"
  unfolding split_spec_param1_def
  apply (refine_vcg)
  apply (auto simp add: subset_iff split: option.splits)
  by (metis flow1_of_vec1_vec1_of_flow1 surjective_pairing)

lemma do_intersection_spec_empty:
  "X = {} \<Longrightarrow> Y = {} \<Longrightarrow> do_intersection_spec S sctns ivl sctn X ({}, Y)"
  by (auto simp: do_intersection_spec_def halfspaces_union)

lemma do_intersection_spec_subset:
  "do_intersection_spec S osctns ivl csctns Y (a, b) \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> do_intersection_spec S osctns ivl csctns X (a, b)"
  by (auto simp: do_intersection_spec_def halfspaces_union intro: flowsto_subset poincare_mapsto_subset)

lemma do_intersection_spec_union:
  "do_intersection_spec S osctns ivl csctns a (b, c) \<Longrightarrow>
   do_intersection_spec S osctns ivl csctns f (g, h) \<Longrightarrow>
   do_intersection_spec S osctns ivl csctns (a \<union> f) (b \<union> g, c \<union> h)"
  by (auto simp: do_intersection_spec_def intro!: poincare_mapsto_unionI)

lemma scaleR2_rep_of_coll[le, refine_vcg]:
  "scaleR2_rep_coll X \<le> SPEC (\<lambda>((l, u), Y). X \<subseteq> scaleR2 l u Y)"
  unfolding scaleR2_rep_coll_def
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs ((l, u), Y). \<Union>Xs \<subseteq> scaleR2 l u Y"])
  subgoal by (auto intro: scaleR2_subset)
  subgoal
    apply clarsimp
    apply safe
    subgoal by (auto elim: scaleR2_subset)
    subgoal
      apply (rule set_rev_mp, assumption)
      apply (rule order_trans)
       apply (rule Union_upper, assumption)
      apply (rule order_trans, assumption)
      apply (rule subsetI)
      apply (erule scaleR2_subset)
      by (auto )
    done
  done

lemma split_spec_param1e[le, refine_vcg]: "split_spec_param1e X \<le> SPEC (\<lambda>(A, B). X \<subseteq> A \<union> B)"
  unfolding split_spec_param1e_def
  apply (refine_vcg)
  apply clarsimp
    apply (thin_tac "_ \<noteq> {}")
  apply (auto simp: scaleR2_def vimage_def image_def)
  apply (rule exI, rule conjI, assumption, rule conjI, assumption)
  apply (auto simp: split_beta')
  apply (drule_tac x = x in spec)
  apply auto
  by (metis (no_types, lifting) UnE prod.sel(1) prod.sel(2) subset_eq)

lemma reduce_spec1[le, refine_vcg]: "reduce_spec1 ro X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding reduce_spec1_def
  by refine_vcg auto

lemma reduce_spec1e[le, refine_vcg]: "reduce_spec1e ro X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding reduce_spec1e_def
  by refine_vcg (auto simp: scaleR2_def image_def vimage_def, force)

lemma split_under_threshold[le, refine_vcg]:
  "split_under_threshold ro th X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding split_under_threshold_def autoref_tag_defs
  by (refine_vcg) auto

lemma step_split[le, refine_vcg]:
  "wd TYPE((real, 'n::enum) vec) \<Longrightarrow> step_split ro (X::'n eucl1 set) \<le> SPEC (\<lambda>Y. X \<subseteq> Y \<and> fst ` Y \<subseteq> Csafe)"
  unfolding step_split_def
  by (refine_vcg refine_vcg) auto

lemma tolerate_error_SPEC[THEN order_trans, refine_vcg]:
  "tolerate_error Y E \<le> SPEC (\<lambda>b. True)"
  unfolding tolerate_error_def
  by refine_vcg

lemma flowpipe_scaleR2I: "flowpipe (scaleR2 x1 x2 bc) x1a x1a (fst ` aca \<times> UNIV) (scaleR2 x1 x2 bca)"
  if "flowpipe (bc) x1a x1a (fst ` aca \<times> UNIV) (bca)"
  using that
  apply (auto simp: flowpipe_def scaleR2_def)
  apply (drule bspec, assumption)
  apply (auto simp: image_def vimage_def )
  apply (rule exI, rule conjI, assumption, rule conjI, assumption)
  apply (rule bexI) prefer 2 apply assumption
  by (auto simp: scaleR_blinfun_compose_right)

lemma choose_step1e_flowpipe[le, refine_vcg]:
  assumes vwd[refine_vcg]: "wd TYPE('n::enum rvec)"
  shows "choose_step1e (X0::'n eucl1 set) h \<le> SPEC (\<lambda>(h', _, RES_ivl, RES::'n eucl1 set).
      0 < h' \<and> h' \<le> h \<and> flowpipe X0 h' h' (RES_ivl \<times> UNIV) RES)"
  unfolding choose_step1e_def
  apply (refine_vcg)
    apply (auto intro: flowpipe_scaleR2I)
  apply (erule contrapos_np)
  apply (auto intro!: flowpipe_scaleR2I)
  apply (rule flowpipe_subset)
         apply assumption
        apply (auto dest!: flowpipe_safeD)
  done

lemma width_spec_appr1[THEN order_trans, refine_vcg]: "width_spec_appr1 X \<le> SPEC (\<lambda>_. True)"
  unfolding width_spec_appr1_def
  by refine_vcg

lemma tolerate_error1_SPEC[THEN order_trans, refine_vcg]:
  "tolerate_error1 Y E \<le> SPEC (\<lambda>b. True)"
  unfolding tolerate_error1_def
  by refine_vcg

lemma
  step_adapt_time[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  shows "step_adapt_time (X::'n eucl1 set) h \<le> SPEC (\<lambda>(t, CX, X1, h). flowpipe X t t (CX \<times> UNIV) X1)"
  unfolding step_adapt_time_def  autoref_tag_defs
  apply (refine_vcg refine_vcg, clarsimp)
  apply (auto simp: flowpipe_def)
  apply force
  done

lemma
  resolve_step[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  shows "resolve_step roptns (X::'n::enum eucl1 set) h \<le> SPEC (\<lambda>(_, CX, X1, _).
    flowsto X {0..} (CX \<times> UNIV) X1 \<and> X \<union> X1 \<subseteq> CX \<times> UNIV \<and> X1 \<union> CX \<times> UNIV \<subseteq> Csafe \<times> UNIV)"
  unfolding resolve_step_def  autoref_tag_defs
  apply (refine_vcg refine_vcg)
  subgoal by (rule flowsto_self) auto
  subgoal by auto
  subgoal by auto
  subgoal
    apply clarsimp
    apply (frule flowpipe_imp_flowsto_nonneg)
    apply (rule flowsto_subset, assumption)
    by auto
  subgoal
    by (auto dest: flowpipe_source_subset)
  subgoal
    by (auto dest!: flowpipe_safeD)
  done

lemma pre_intersection_step[THEN order_trans, refine_vcg]:
  "pre_intersection_step ro (X::'n eucl1 set) h \<le> SPEC (\<lambda>(X', CX, G). X \<subseteq> X' \<union> G \<and> X \<union> X' \<union> G \<subseteq> CX \<times> UNIV)"
  if [refine_vcg]: "wd TYPE('n::enum rvec)"
  unfolding pre_intersection_step_def autoref_tag_defs
  by (refine_vcg) auto

lemma [THEN order_trans, refine_vcg]: "select_with_inter ci a \<le> SPEC (\<lambda>_. True)"
  unfolding select_with_inter_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>_ _. True"])

lemmas [refine_vcg del] = scaleR2_rep_of_coll

lemma fst_scaleR2_image[simp]: "ad \<le> ereal r \<Longrightarrow> ereal r \<le> bd \<Longrightarrow> fst ` scaleR2 ad bd be = fst ` be"
  by (cases ad; cases bd; force simp: scaleR2_def image_image split_beta' vimage_def)

lemma scaleR2_rep_of_coll2[le, refine_vcg]:
  "scaleR2_rep_coll X \<le> SPEC (\<lambda>((l, u), Y). X \<subseteq> scaleR2 l u Y \<and> fst ` X = fst ` Y)"
  unfolding scaleR2_rep_coll_def
  supply [simp del] = mem_scaleR2_union
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs ((l, u), Y).
      \<Union>Xs \<subseteq> scaleR2 l u Y \<and> fst ` \<Union>Xs \<subseteq> fst ` Y \<and> fst ` Y \<subseteq> fst ` X"])
        apply (auto intro: scaleR2_subset)
  subgoal by (auto simp: scaleR2_def)
  subgoal by (auto simp: scaleR2_def image_def vimage_def, fastforce)
  subgoal
    apply (rule scaleR2_subset)
       apply (rule subsetD)
        apply assumption
       apply auto
    done
  subgoal by force
  subgoal for a b c d e f g h i j k l
    apply (rule scaleR2_subset)
       apply (rule subsetD)
        apply assumption
    by auto
  subgoal by (auto simp: scaleR2_def)
  subgoal by (auto simp: scaleR2_def)
  subgoal by (auto simp: scaleR2_def image_def vimage_def, fastforce)
  done

lemma reach_cont[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  shows "reach_cont roptns guards (X::'n eucl1 set) \<le> SPEC (\<lambda>(CX, G).
    G \<union> (CX \<times> UNIV) \<subseteq> (Csafe - guards) \<times> UNIV \<and>
    X \<union> G \<subseteq> CX \<times> UNIV \<and>
    flowsto X {0..} (CX \<times> UNIV) G)"
  unfolding reach_cont_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all simp add: cancel_times_UNIV_subset)
  subgoal by (rule flowsto_self) (auto simp: )
  subgoal by (force simp: scaleR2_def)
  subgoal by (fastforce simp: scaleR2_def vimage_def image_def)
  subgoal premises prems for _ _ _ _ _ _ _ g
    using \<open>flowsto X _ _ (g \<union> _ \<union> _)\<close>  \<open>flowsto g _ _ _\<close>
    apply (rule flowsto_stepI)
    using prems
    by auto
  subgoal
    apply safe
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  subgoal by auto
  subgoal
    by (rule flowsto_subset, assumption) auto
  subgoal
    apply safe
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by fastforce
    subgoal by auto
    subgoal by auto
    subgoal
      by (metis (mono_tags, lifting) Diff_eq_empty_iff Diff_iff IntI)
    done
  subgoal
    apply safe
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  subgoal by auto
  done

lemma reach_cont_par[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  shows "reach_cont_par roptns guards (X::'n eucl1 set) \<le> SPEC (\<lambda>(CX, G).
    G \<union> (CX \<times> UNIV) \<subseteq> (Csafe - guards) \<times> UNIV \<and>
    X \<union> G \<subseteq> CX \<times> UNIV \<and>
    flowsto X {0..} (CX \<times> UNIV) G)"
  unfolding reach_cont_par_def
  apply refine_vcg
    apply auto
    apply force
    apply force
    apply force
     apply force
  subgoal
    apply (rule bexI)
     prefer 2 apply assumption
    by auto
  subgoal
    apply (rule bexI)
     prefer 2 apply assumption
    by auto
  subgoal for R
    apply (rule flowsto_source_Union)
    apply (drule bspec, assumption)
    apply auto
    apply (rule flowsto_subset, assumption)
       apply auto
    done
  done

lemma subset_iplane_coll[THEN order_trans, refine_vcg]:
  "subset_iplane_coll x ics \<le> SPEC (\<lambda>b. b \<longrightarrow> x \<subseteq> ics)"
  unfolding subset_iplane_coll_def
  apply refine_vcg
  subgoal for X icss
    by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>ic b. b \<longrightarrow> X \<subseteq> \<Union>(icss)"]) auto
  done

lemma subsets_iplane_coll[THEN order_trans, refine_vcg]:
  "subsets_iplane_coll x ics \<le> SPEC (\<lambda>b. b \<longrightarrow> \<Union>x \<subseteq> ics)"
  unfolding subsets_iplane_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>x b. (b \<longrightarrow> \<Union>x \<subseteq> ics)"]) auto

lemma symstart_coll[THEN order_trans, refine_vcg]:
  assumes [refine_vcg]: "wd (TYPE('n::enum rvec))"
  assumes [le, refine_vcg]:
    "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  shows "symstart_coll symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto ((X0::'n eucl1 set) - trap \<times> UNIV) {0..} (CX \<times> UNIV) X)"
  unfolding symstart_coll_def autoref_tag_defs
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X (CY, Y). flowsto (\<Union>X - trap \<times> UNIV) {0..} (CY \<times> UNIV) Y"], clarsimp_all)
  subgoal by force
  subgoal for a b c d e by (rule flowsto_subset, assumption) auto
  subgoal by force
  subgoal for a b c d e f g
    unfolding Un_Diff
    apply (rule flowsto_source_unionI)
    subgoal by (rule flowsto_subset, assumption) auto
    subgoal by (rule flowsto_subset, assumption) auto
    done
  done

lemma reach_cont_symstart[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  assumes [le, refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  shows "reach_cont_symstart roptns symstart guards (X::'n eucl1 set) \<le> SPEC (\<lambda>(CX, G).
    G \<union> (CX \<times> UNIV) \<subseteq> (Csafe - guards) \<times> UNIV \<and>
    X \<subseteq> CX \<times> UNIV \<and>
    G \<subseteq> CX \<times> UNIV \<and>
    flowsto (X - trap \<times> UNIV) {0..} (CX \<times> UNIV) (G))"
  unfolding reach_cont_symstart_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all)
  subgoal by (auto simp: times_subset_iff)
  subgoal by auto
  subgoal by auto
  subgoal for a b c d e f g
    apply (rule flowsto_stepI[OF _ _ order_refl])
         apply assumption
    by assumption auto
  done

lemma reach_conts[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) X)"
  shows "reach_conts roptns symstart trap guards (X::'n eucl1 set) \<le> SPEC (\<lambda>(CX, IGs, X0).
    \<Union>(snd ` IGs) \<union> (CX \<times> UNIV) \<subseteq> (Csafe - guards) \<times> UNIV \<and>
    X \<subseteq> CX \<times> UNIV \<and>
    \<Union>(snd ` IGs) \<subseteq> CX \<times> UNIV \<and>
    \<Union>(fst ` IGs) \<subseteq> guards \<and>
    X = \<Union>(X0 ` (snd ` IGs)) \<and>
    (\<forall>(I, G) \<in> IGs. flowsto (X0 G - trap \<times> UNIV) {0..} (CX \<times> UNIV) G))"
  unfolding reach_conts_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all)
  subgoal for a b
    apply (erule flowsto_Diff_to_Union_funE)
    apply (force simp: split_beta')
    subgoal for f
      apply (rule exI[where x=f])
      by (auto simp: split_beta')
    done
  subgoal by (auto)
  subgoal by (auto)
  subgoal by (auto)
  done

lemma leaves_halfspace[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  shows "leaves_halfspace S (X::'n::enum rvec set) \<le>
    SPEC (\<lambda>b. case b of None \<Rightarrow> S = UNIV
      | Some sctn \<Rightarrow>
        (S = below_halfspace sctn \<and> X \<subseteq> plane_of sctn \<and> (\<forall>x \<in> X. ode x \<bullet> normal sctn < 0)))"
  unfolding leaves_halfspace_def autoref_tag_defs op_set_to_list_def
  apply (refine_vcg, clarsimp_all)
  subgoal by (force simp add: halfspace_simps plane_of_def)
  done

lemma poincare_start_on[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  shows "poincare_start_on guards sctn (X0::'n eucl1 set) \<le> SPEC (\<lambda>(X1S, CX1S).
    fst ` (X1S \<union> (CX1S \<times> UNIV)) \<subseteq> Csafe \<and>
    fst ` X1S \<subseteq> sbelow_halfspace sctn \<and>
    fst ` (X1S \<union> (CX1S \<times> UNIV)) \<inter> guards = {} \<and>
    (X0 \<subseteq> (CX1S \<times> UNIV)) \<and>
    (\<forall>(x, d) \<in> CX1S \<times> UNIV. ode x \<bullet> normal sctn < 0) \<and>
    flowsto X0 pos_reals ((CX1S \<times> UNIV) \<inter> (sbelow_halfspace sctn \<times> UNIV)) X1S)"
  unfolding poincare_start_on_def autoref_tag_defs
  apply refine_vcg
  apply (rule FORWEAK_mono_rule[where I="\<lambda>X0S (X1S, CX1S).
      flowsto (\<Union>X0S) pos_reals ((CX1S \<times> UNIV) \<inter> sbelow_halfspace sctn \<times> UNIV) X1S \<and>
        fst ` (X1S \<union> (CX1S \<times> UNIV)) \<subseteq> Csafe \<and>
        (\<Union>X0S) \<subseteq> X0 \<and>
        (\<Union>X0S) \<subseteq> (CX1S \<times> UNIV) \<and>
        fst ` (X1S \<union> (CX1S \<times> UNIV)) \<inter> guards = {} \<and>
        (\<forall>(x, d) \<in> (CX1S \<times> UNIV). ode x \<bullet> normal sctn < 0) \<and>
        fst ` X1S  \<subseteq> sbelow_halfspace sctn"])
  subgoal by (refine_vcg)
  subgoal for A B
    apply (refine_vcg)
    subgoal
      apply (auto simp: dest!: flowpipe_imp_flowsto)
      apply (rule flowsto_subset)
          apply (rule flowsto_stays_sbelow[where sctn=sctn])
            apply (rule flowsto_subset) apply assumption
               apply (rule order_refl)
              apply force
             apply (rule order_refl)
            apply (rule order_refl)
           apply (auto simp: halfspace_simps)
      apply (rule le_less_trans)
       prefer 2 apply assumption
      apply (drule bspec)
       apply (rule subsetD, assumption)
       prefer 2 apply assumption
      apply auto
      done
    subgoal by auto
    subgoal by force
    subgoal by (auto simp: dest!: flowpipe_source_subset)
    subgoal by auto
    subgoal
      apply (auto simp: halfspace_simps subset_iff)
      apply (rule le_less_trans[rotated], assumption)
      by fastforce
    done
  subgoal by (auto intro: flowsto_subset) force
  subgoal for a b c d
    using assms
    apply (refine_vcg, clarsimp_all)
    subgoal for e f g h i j k l m n
      apply (rule flowsto_source_unionI)
      subgoal
        apply (drule flowpipe_imp_flowsto, assumption)
        apply (rule flowsto_subset[OF flowsto_stays_sbelow[where sctn=sctn] order_refl])
             apply (rule flowsto_subset[OF _ order_refl], assumption)
               apply force
              apply (rule order_refl)
             apply (rule order_refl)
            apply (auto simp: halfspace_simps)
        apply (rule le_less_trans)
         prefer 2 apply assumption
        apply (drule bspec)
         apply (rule subsetD, assumption)
         prefer 2 apply assumption
        apply auto
        done
      by (auto intro!: flowsto_source_unionI dest!: flowpipe_imp_flowsto intro: flowsto_subset[OF _ order_refl])
    subgoal
      apply (auto simp: subset_iff)
      apply (auto simp: image_Un)
      done
    subgoal by auto
    subgoal by (auto dest!: flowpipe_source_subset)
    subgoal by auto
    subgoal
      apply (auto simp: halfspace_simps subset_iff)
      apply (rule le_less_trans[rotated], assumption)
      by fastforce
    subgoal by auto
    done
  subgoal by auto
  done

lemma op_inter_fst_coll[le, refine_vcg]: "op_inter_fst_coll X Y \<le> SPEC (\<lambda>R. R = X \<inter> Y \<times> UNIV)"
  unfolding op_inter_fst_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. \<Union>Xs \<inter> Y \<times> UNIV \<subseteq> R \<and> R \<subseteq> X \<inter> Y \<times> UNIV"])
    auto

lemma scaleRe_ivl_coll_spec[le, refine_vcg]: "scaleRe_ivl_coll_spec l u X \<le> SPEC (\<lambda>Y. Y = scaleR2 l u X)"
  unfolding scaleRe_ivl_coll_spec_def
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. scaleR2 l u (\<Union>Xs) \<subseteq> R \<and> R \<subseteq> scaleR2 l u X"])
      apply (auto simp: intro: scaleR2_subset)
  subgoal
    by (force simp: intro: scaleR2_subset)
  done

lemma do_intersection_spec_scaleR2I:
  "do_intersection_spec UNIV sctns ivl sctn (scaleR2 x1 x2 baa) (scaleR2 x1 x2 aca, x1b)"
  if "do_intersection_spec UNIV sctns ivl sctn (baa) (aca, x1b)"
  using that
  by (auto simp: do_intersection_spec_def intro!: poincare_mapsto_scaleR2I)
     (auto simp: scaleR2_def image_def vimage_def)

lemma do_intersection_core[refine_vcg, le]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  shows "do_intersection_core sctns ivl sctn (X::'n eucl1 set) \<le>
    SPEC (\<lambda>(P1, P2, CX, X0s).
      do_intersection_spec UNIV sctns ivl sctn (X - X0s) (P1, CX) \<and>
      do_intersection_spec UNIV sctns ivl sctn (X - X0s) (P2, CX)
      \<and> fst ` (X - X0s) \<subseteq> CX
      \<and> X0s \<subseteq> X)"
  unfolding do_intersection_core_def autoref_tag_defs
  apply (refine_vcg assms, clarsimp_all)
  subgoal by (rule do_intersection_spec_scaleR2I) (auto simp: do_intersection_spec_def intro!: )
  subgoal by (rule do_intersection_spec_scaleR2I) (auto simp: do_intersection_spec_def intro!: )
  subgoal by (fastforce simp: scaleR2_def)
  subgoal by (auto simp: do_intersection_spec_def)
  subgoal by (auto simp: do_intersection_spec_def)
  done

lemma do_intersection_spec_Union:
  "do_intersection_spec S sctns ivl sctn (\<Union>X) A"
  if "\<And>x. x \<in> X \<Longrightarrow> do_intersection_spec S sctns ivl sctn x A"
    "X \<noteq> {}"
  using that(2)
  unfolding do_intersection_spec_def
  apply clarsimp
  apply safe
  subgoal by (rule poincare_mapsto_Union) (auto simp: do_intersection_spec_def dest!: that(1))
  subgoal by (auto simp: do_intersection_spec_def dest!: that(1))
  subgoal by (auto simp: do_intersection_spec_def dest!: that(1))
  subgoal by (fastforce simp: do_intersection_spec_def dest!: that(1))
  subgoal by (fastforce simp: do_intersection_spec_def dest!: that(1))
  subgoal by (fastforce simp: do_intersection_spec_def dest!: that(1))
  subgoal by (force simp: do_intersection_spec_def dest!: that(1))
  subgoal by (auto simp: do_intersection_spec_def dest!: that(1))
  subgoal by (fastforce simp: do_intersection_spec_def dest!: that(1))
  subgoal by (fastforce simp: do_intersection_spec_def dest!: that(1))
  done

lemma do_intersection_spec_subset2:
  "do_intersection_spec S p ivl sctn X1 (ab, CY) \<Longrightarrow> CY \<subseteq> CX \<Longrightarrow> CX \<subseteq> Csafe \<Longrightarrow>
    CX \<inter> p = {} \<Longrightarrow> CX \<inter> ivl \<inter> plane_of sctn = {} \<Longrightarrow> X0 \<subseteq> X1 \<Longrightarrow>
  do_intersection_spec S p ivl sctn X0 (ab, CX)"
  by (auto simp: do_intersection_spec_def intro: poincare_mapsto_subset)

lemma do_intersection_spec_Union3:
  "do_intersection_spec S osctns ivl csctns (\<Union>x\<in>X. a x) ((\<Union>x\<in>X. b x), (\<Union>x\<in>X. c x))"
  if  "finite X" "X \<noteq> {}" "\<And>x. x \<in> X \<Longrightarrow> do_intersection_spec S osctns ivl csctns (a x) (b x, c x)"
  using that
proof induction
  case empty
  then show ?case by (auto simp: )
next
  case (insert x F)
  show ?case
    apply (cases "F = {}")
    subgoal using insert by simp
    subgoal
      apply simp
      apply (rule do_intersection_spec_union)
       apply (rule insert.prems) apply simp
      apply (rule insert.IH)
       apply (assumption)
      apply (rule insert.prems) apply simp
      done
    done
qed

lemma do_intersection_coll[le]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  shows "do_intersection_coll sctns ivl sctn (X::'n eucl1 set) \<le>
    SPEC (\<lambda>(P1, P2, CX, X0s).
      do_intersection_spec UNIV sctns ivl sctn (X - X0s) (P1, CX) \<and>
      do_intersection_spec UNIV sctns ivl sctn (X - X0s) (P2, CX)
      \<and> fst ` (X - X0s) \<subseteq> CX
      \<and> X0s \<subseteq> X)"
  unfolding do_intersection_coll_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all)
  subgoal
    apply (rule do_intersection_spec_subset[OF _ diff_subset])
    apply (rule do_intersection_spec_Union3)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  subgoal
    apply (rule do_intersection_spec_subset[OF _ diff_subset])
    apply (rule do_intersection_spec_Union3)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  subgoal by fastforce
  subgoal by fastforce
  done

lemma
  do_intersection_flowsto_trans_outside:
  assumes "flowsto XS0 {0..} (CX \<times> UNIV) X1"
  assumes "do_intersection_spec UNIV guards ivl sctn X1 (P, CP)"
  assumes "fst ` X1 \<subseteq> CP"
  assumes "{x \<in> ivl. x \<in> plane_of sctn} \<inter> CX = {}"
  assumes "guards \<inter> (CX \<union> CP) = {}"
  assumes "XS0 \<subseteq> CX \<times> UNIV"
  assumes "closed ivl"
  assumes "CX \<subseteq> Csafe"
  shows "do_intersection_spec UNIV guards ivl sctn XS0 (P, CX \<union> CP)"
  using assms
  apply (auto simp: do_intersection_spec_def)
  subgoal
    apply (rule flowsto_poincare_trans, assumption, assumption)
    subgoal by simp
    subgoal by auto
    subgoal using assms(3) by auto
    subgoal by (auto intro!: closed_levelset_within continuous_intros simp: plane_of_def)
    subgoal premises prems for x d
    proof -
      have [intro, simp]: "closed {x \<in> ivl. x \<in> plane_of sctn} " "closed {x \<in> ivl. x \<bullet> normal sctn = pstn sctn}"
        by (auto intro!: closed_levelset_within continuous_intros simp: plane_of_def assms)
      from flowsto_poincare_mapsto_trans_flowsto[OF \<open>flowsto _ _ _ _\<close> \<open>poincare_mapsto _ _ _ _ _\<close> _ _ order_refl]
      have ft: "flowsto XS0 {0<..} (X1 \<union> CX \<times> UNIV \<union> CP \<times> UNIV) (fst ` P \<times> UNIV)"
        by (auto simp: )
      then have ret: "returns_to {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0} x"
        apply (rule returns_to_flowstoI[OF _ _ _ _ _ _ order_refl])
        using prems by (auto simp: plane_of_def)
      have pm: "poincare_map {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x \<in> fst ` P"
        apply (rule poincare_map_mem_flowstoI[OF ft])
        using prems by (auto simp: plane_of_def)
      from pm prems have "\<forall>\<^sub>F x in at (poincare_map {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x) within
        plane_of sctn. x \<in> ivl"
        by auto
      from ret have "isCont (return_time {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0}) x"
        apply (rule return_time_isCont_outside)
        using prems pm
        by (auto simp: eventually_at_filter plane_of_def intro!: assms derivative_eq_intros)
      then show "isCont (return_time {x \<in> ivl. x \<in> plane_of sctn}) x" by (simp add: plane_of_def)
    qed
    subgoal by simp
    done
  done

lemma do_intersection_coll_flowsto[le]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  assumes ft: "flowsto X0 {0..} (CX0 \<times> UNIV) X"
  assumes X_subset: "X \<subseteq> CX0 \<times> UNIV"
  assumes X0_subset: "X0 \<subseteq> CX0 \<times> UNIV" and CX0_safe: "CX0 \<subseteq> Csafe"
  assumes ci: "closed ivl"
  assumes disj: "ivl \<inter> plane_of sctn \<inter> CX0 = {}" "sctns \<inter> CX0 = {}"
  shows "do_intersection_coll sctns ivl sctn (X::'n eucl1 set) \<le>
    SPEC (\<lambda>(P1, P2, CX, X0s).
      \<exists>A.
        do_intersection_spec UNIV sctns ivl sctn A (P1, CX0 \<union> CX) \<and>
        do_intersection_spec UNIV sctns ivl sctn A (P2, CX0 \<union> CX) \<and>
        flowsto (X0 - A) {0..} (CX0 \<times> UNIV) X0s \<and>
        A \<subseteq> X0 \<and>
        P1 \<inter> X0s = {} \<and>
        P2 \<inter> X0s = {})"
  apply (rule do_intersection_coll)
   apply (rule wd)
proof (clarsimp, goal_cases)
  case (1 P1 P2 CX R)
  from ft have "flowsto X0 {0..} (CX0 \<times> UNIV) (X - R \<union> R)"
    by (rule flowsto_subset) auto
  from flowsto_union_DiffE[OF this]
  obtain A where AB: "A \<subseteq> X0"
    and A: "flowsto A {0..} (CX0 \<times> UNIV) (X - R)"
    and B: "flowsto (X0 - A) {0..} (CX0 \<times> UNIV) (R)"
    by auto
  have di: "do_intersection_spec UNIV sctns ivl sctn A (P1, CX0 \<union> CX)"
    apply (rule do_intersection_flowsto_trans_outside[OF A 1(1)])
    subgoal using 1 by simp
    subgoal using disj by auto
    subgoal using 1 disj by (auto simp: do_intersection_spec_def)
    subgoal using X0_subset AB by (auto simp: do_intersection_spec_def)
    subgoal using ci by simp
    subgoal using CX0_safe .
    done
  then have "P1 \<subseteq> (ivl \<inter> plane_of sctn) \<times> UNIV"
    by (auto simp: do_intersection_spec_def)
  then have disjoint: "P1 \<inter> R = {}"
    using \<open>R \<subseteq> X\<close> disj X_subset
      apply (auto simp: subset_iff)
    by (metis (no_types, lifting) Int_iff disjoint_iff_not_equal)

  have di2: "do_intersection_spec UNIV sctns ivl sctn A (P2, CX0 \<union> CX)"
    apply (rule do_intersection_flowsto_trans_outside[OF A 1(2)])
    subgoal using 1 by simp
    subgoal using disj by auto
    subgoal using 1 disj by (auto simp: do_intersection_spec_def)
    subgoal using X0_subset AB by (auto simp: do_intersection_spec_def)
    subgoal using ci by simp
    subgoal using CX0_safe .
    done
  then have "P2 \<subseteq> (ivl \<inter> plane_of sctn) \<times> UNIV"
    by (auto simp: do_intersection_spec_def)
  then have "P2 \<inter> R = {}"
    using \<open>R \<subseteq> X\<close> disj X_subset
      apply (auto simp: subset_iff)
    by (metis (no_types, lifting) Int_iff disjoint_iff_not_equal)
  from AB this disjoint di di2 B show ?case
    by (auto simp:)
qed

lemma op_enlarge_ivl_sctn[le, refine_vcg]:
  "op_enlarge_ivl_sctn ivl sctn d \<le> SPEC (\<lambda>ivl'. ivl \<subseteq> ivl')"
  unfolding op_enlarge_ivl_sctn_def
  apply refine_vcg
  unfolding plane_of_def
  apply (safe intro!: eventually_in_planerectI)
  apply (auto  intro!: simp: eucl_le[where 'a='a] inner_sum_left inner_Basis if_distrib
     algebra_simps cong: if_cong)
  done

lemma resolve_ivlplanes[le]:
  assumes wd[refine_vcg]: "wd TYPE('a::enum rvec)"
  assumes
    "\<forall>x\<in>Xg. case x of (I, G) \<Rightarrow> flowsto (XSf G) {0..} (CXS \<times> UNIV) G"
    "(\<Union>x\<in>Xg. snd x) \<subseteq> (Csafe - (ivlplanes \<union> guards)) \<times> UNIV"
    "CXS \<times> UNIV \<subseteq> (Csafe - (ivlplanes \<union> guards)) \<times> UNIV"
    "(\<Union>a\<in>Xg. XSf (snd a)) \<subseteq> (CXS::'a rvec set) \<times> UNIV"
    "(\<Union>x\<in>Xg. snd x) \<subseteq> CXS \<times> UNIV"
    "(\<Union>x\<in>Xg. fst x) \<subseteq> ivlplanes \<union> guards"
  shows "resolve_ivlplanes guards ivlplanes Xg \<le> SPEC (\<lambda>PS.
    CXS \<inter> (guards \<union> ivlplanes) = {} \<and>
    CXS \<subseteq> Csafe \<and>
    (\<exists>R0 P0. (\<Union>x\<in>PS. P0 x) \<union> (\<Union>x\<in>PS. R0 x) = (\<Union>a\<in>Xg. XSf (snd a))\<and>
       (\<forall>x\<in>PS. case x of (X, P1, P2, R, ivl, sctn, CX) \<Rightarrow>
          ivl \<inter> plane_of sctn \<subseteq> ivlplanes \<and> closed ivl \<and>
          P0 (X, P1, P2, R, ivl, sctn, CX) \<inter> R0 (X, P1, P2, R, ivl, sctn, CX) = {} \<and>
          R0 (X, P1, P2, R, ivl, sctn, CX) \<subseteq> (CXS \<times> UNIV) \<and>
          flowsto (R0 (X, P1, P2, R, ivl, sctn, CX)) {0..} (CXS \<times> UNIV) R \<and>
          do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX)) (P1, CXS \<union> CX) \<and>
          do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX)) (P2, CXS \<union> CX))))"
  using assms
  unfolding resolve_ivlplanes_def
  apply clarsimp_all
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xgs PS.
      (\<exists>R0 P0.
        snd ` Xgs \<subseteq> fst ` PS \<and> fst ` PS \<subseteq> snd ` Xg \<and>
        (\<forall>(X, P1, P2, R, ivl, sctn, CX) \<in> PS.
            P0 (X, P1, P2, R, ivl, sctn, CX) \<union> R0 (X, P1, P2, R, ivl, sctn, CX) = XSf X
          \<and> ivl \<inter> plane_of sctn \<subseteq> ivlplanes \<and> closed ivl
          \<and> P0 (X, P1, P2, R, ivl, sctn, CX) \<inter> R0 (X, P1, P2, R, ivl, sctn, CX) = {}
          \<and> R0 (X, P1, P2, R, ivl, sctn, CX) \<subseteq> (CXS \<times> UNIV)
          \<and> flowsto (R0 (X, P1, P2, R, ivl, sctn, CX)) {0..} (CXS \<times> UNIV) R
          \<and> do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX)) (P1, CXS \<union> CX)
          \<and> do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX)) (P2, CXS \<union> CX)))"],
        clarsimp_all)
    using [[goals_limit=1]]
    subgoal by auto
    subgoal by auto
    subgoal for a b c
      apply (frule bspec, assumption, clarsimp)
      apply (rule do_intersection_coll_flowsto)
              apply (rule wd)
             apply assumption
            apply force
           apply force
          apply blast
         apply assumption
      subgoal premises prems
      proof -
        have "(b \<inter> plane_of c, a) \<in> Xg" using prems by simp
        with \<open>(\<Union>x\<in>Xg. fst x) \<subseteq> ivlplanes \<union> guards\<close>
        have "b \<inter> plane_of c \<subseteq> ivlplanes \<union> guards"
          by (force simp: subset_iff)
        then show ?thesis
          using \<open>CXS \<times> UNIV \<subseteq> (Csafe - (ivlplanes \<union> guards)) \<times> UNIV\<close>
          by auto
      qed
      subgoal by (auto simp: subset_iff)
      subgoal apply (refine_vcg, clarsimp_all) apply force
        apply (intro exI conjI)defer defer defer apply assumption+
         apply simp
         apply force
        apply force
        apply force
        done
      done
    subgoal by (auto simp: subset_iff) blast
    subgoal for a b c d e f R0 P0
      apply (frule bspec, assumption, clarsimp)
      apply (rule do_intersection_coll_flowsto)
              apply (rule wd)
             apply assumption
      subgoal
        apply (rule order_trans[where y="(\<Union>x\<in>Xg. snd x)"]) 
        by auto
      subgoal
        apply (rule order_trans) defer apply assumption
        by auto
      subgoal by blast
      subgoal by simp
      subgoal premises prems
      proof -
        have "(d \<inter> plane_of e, c) \<in> Xg" using prems by simp
        with \<open>(\<Union>x\<in>Xg. fst x) \<subseteq> ivlplanes \<union> guards\<close>
        have "d \<inter> plane_of e \<subseteq> ivlplanes \<union> guards"
          by (force simp: subset_iff)
        then show ?thesis
          using \<open>CXS \<times> UNIV \<subseteq> (Csafe - (ivlplanes \<union> guards)) \<times> UNIV\<close>
          by auto
      qed
      subgoal by (auto simp: subset_iff)
      subgoal
        apply (refine_vcg, clarsimp_all)
        subgoal by (auto simp: subset_iff)
        subgoal by (auto simp: )
        subgoal for x1 x1' x2 x3 A
          apply (rule exI[where x="R0((c, x1, x1', x3, d, e, x2):=(XSf c - A))"])
          apply (rule exI[where x="P0((c, x1, x1', x3, d, e, x2):=A)"])
          apply clarsimp
          apply (rule conjI)
          subgoal by auto
          apply (rule conjI)
          subgoal premises prems
            using prems
            apply (auto simp: subset_iff)
            by fastforce
          apply clarsimp
          subgoal
            apply (drule bspec, assumption)
            apply (drule bspec, assumption)
            by force
          done
        done
      done
    subgoal by (auto simp: subset_iff)
    subgoal by (auto simp: subset_iff)
    subgoal for a R0 P0
      apply (rule exI[where x=R0])
      apply (rule exI[where x=P0])
      apply (rule conjI)
      subgoal premises prems
      proof -
        note prems
        show ?thesis
          using prems(9,8)
          by fastforce
      qed
      by auto
    done


lemma poincare_onto[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd TYPE('a::enum rvec)"
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le>
    SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) X)"
  assumes CXS0: "CXS0 \<inter> (guards \<union> ivlplanes) = {}"
  shows "poincare_onto ro symstart trap guards ivlplanes (XS0::'a eucl1 set) CXS0 \<le>
    SPEC (\<lambda>PS.
      (\<exists>R0 P0.
        \<Union>(P0 ` PS \<union> R0 ` PS) = XS0 - trap \<times> UNIV \<and>
        (\<forall>(X, P1, P2, R, ivl, sctn, CX, CXS) \<in> PS.
            ivl \<inter> plane_of sctn \<subseteq> ivlplanes \<and> closed ivl
          \<and> XS0 \<subseteq> CXS \<times> UNIV \<and> CXS0 \<subseteq> CXS \<and> CXS \<inter> (guards \<union> ivlplanes) = {}
          \<and> P0 (X, P1, P2, R, ivl, sctn, CX, CXS) \<inter> R0 (X, P1, P2, R, ivl, sctn, CX, CXS) = {}
          \<and> R0 (X, P1, P2, R, ivl, sctn, CX, CXS) \<subseteq> CXS \<times> UNIV
          \<and> flowsto (R0 (X, P1, P2, R, ivl, sctn, CX, CXS)) {0..} (CXS \<times> UNIV) R
          \<and> do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P1, CXS \<union> CX)
          \<and> do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P2, CXS \<union> CX))
        ))"
  unfolding poincare_onto_def autoref_tag_defs
  using [[goals_limit=1]]
  apply (refine_vcg, clarsimp_all)
  apply (refine_vcg resolve_ivlplanes[OF wd])
  subgoal by force
  apply clarsimp
  subgoal for a b c d R0 P0
    apply (rule exI[where x="\<lambda>(X, P1, P2, R, ivl, sctn, CX, CXS). R0 (X, P1, P2, R, ivl, sctn, CX)"])
    apply (rule exI[where x="\<lambda>(X, P1, P2, R, ivl, sctn, CX, CXS). P0 (X, P1, P2, R, ivl, sctn, CX)"])
    apply (rule conjI)
    subgoal premises prems
      using \<open>(\<Union>x\<in>d. P0 x) \<union> (\<Union>x\<in>d. R0 x) = (\<Union>x\<in>b. c (snd x)) - trap \<times> UNIV\<close>
      by auto
    subgoal
      apply clarsimp
      apply (drule bspec, assumption)+
      apply (rule conjI, force)
      apply (rule conjI, force)
      apply (rule conjI, force)
      apply (rule conjI)
      subgoal using CXS0 by (auto simp: )
      apply (rule conjI, force)
      apply (rule conjI, force)
      apply (rule conjI)
      subgoal by (auto intro: flowsto_subset)
      subgoal
        apply clarsimp
        apply (rule conjI)
        subgoal
          apply (rule do_intersection_spec_subset2, assumption)
          subgoal by force
          subgoal by (force simp: do_intersection_spec_def)
          subgoal using CXS0 by (auto simp: do_intersection_spec_def)
          subgoal using CXS0 by (auto simp: do_intersection_spec_def)
          subgoal by auto
          done
        subgoal
          apply (rule do_intersection_spec_subset2, assumption)
          subgoal by force
          subgoal by (force simp: do_intersection_spec_def)
          subgoal using CXS0 by (auto simp: do_intersection_spec_def)
          subgoal using CXS0 by (auto simp: do_intersection_spec_def)
          subgoal by auto
          done
        done
      done
    done
  done

lemma empty_remainders[le, refine_vcg]:
  "empty_remainders PS \<le> SPEC (\<lambda>b. b \<longrightarrow> (\<forall>(X, P1, P2, R, ivl, sctn, CX) \<in> PS. R = {}))"
  unfolding empty_remainders_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs b. b \<longrightarrow> (\<forall>(X, P1, P2, R, ivl, sctn, CX) \<in> Xs. R = {})"])
     auto

lemma poincare_onto_empty[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd TYPE('a::enum rvec)"
  assumes CXS0: "CXS0 \<inter> (guards \<union> ivlplanes) = {}"
  shows "poincare_onto_empty ro guards ivlplanes (XS0::'a eucl1 set) CXS0 \<le>
    SPEC (\<lambda>(PS).
      (\<exists>R0 P0.
        \<Union>(P0 ` PS \<union> R0 ` PS) = XS0 \<and>
        (\<forall>(X, P1, P2, R, ivl, sctn, CX, CXS) \<in> PS.
            ivl \<inter> plane_of sctn \<subseteq> ivlplanes \<and> closed ivl
          \<and> XS0 \<subseteq> CXS \<times> UNIV \<and> CXS0 \<subseteq> CXS \<and> CXS \<inter> (guards \<union> ivlplanes) = {}
          \<and> P0 (X, P1, P2, R, ivl, sctn, CX, CXS) \<inter> R0 (X, P1, P2, R, ivl, sctn, CX, CXS) = {}
          \<and> R0 (X, P1, P2, R, ivl, sctn, CX, CXS) \<subseteq> CXS \<times> UNIV
          \<and> flowsto (R0 (X, P1, P2, R, ivl, sctn, CX, CXS)) {0..} (CXS \<times> UNIV) R
          \<and> do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P1, CXS \<union> CX)
          \<and> do_intersection_spec UNIV guards ivl sctn (P0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P2, CXS \<union> CX))
        ))"
  using CXS0
  unfolding poincare_onto_empty_def autoref_tag_defs
  by (refine_vcg) (auto intro!: flowsto_self)

lemma do_intersection_spec_union2:
  assumes "do_intersection_spec S osctns ivl csctns a (b, c)"
    "do_intersection_spec S osctns ivl csctns f (b, c)"
  shows "do_intersection_spec S osctns ivl csctns (a \<union> f) (b, c)"
  using do_intersection_spec_union[OF assms]
  by auto

lemma poincare_onto2[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd TYPE('a::enum rvec)"
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le>
    SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) X)"
  notes [refine_vcg_def] = op_set_ndelete_spec
  shows "poincare_onto2 ro symstart trap guards ivlplanes (XS0::'a eucl1 set) \<le>
    SPEC (\<lambda>(PS).
      (\<exists>P0. \<Union>(P0 ` PS) = XS0 - trap \<times> UNIV \<and>
        (\<forall>(s, X, P1, P2, R, ivl, sctn, CX, CXS) \<in> PS.
          XS0 \<subseteq> CXS \<times> UNIV \<and>
          do_intersection_spec UNIV guards ivl sctn (P0 (s, X, P1, P2, R, ivl, sctn, CX, CXS)) (P1, CXS \<union> CX) \<and>
          do_intersection_spec UNIV guards ivl sctn (P0 (s, X, P1, P2, R, ivl, sctn, CX, CXS)) (P2, CXS \<union> CX))))"
  unfolding poincare_onto2_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all)
  subgoal for PS R0 P0
    apply (rule FORWEAK_mono_rule_empty[where I="\<lambda>PS1 PS2.
      (\<exists>X0.
        \<Union>(R0 ` PS1) \<subseteq> \<Union>(X0 ` PS2) \<and>
        (\<forall>(X, P1, P2, R, ivl, sctn, CX, CXS) \<in> PS2.
          XS0 \<subseteq> CXS \<times> UNIV \<and>
          do_intersection_spec UNIV guards ivl sctn (X0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P1, CXS \<union> CX) \<and>
          do_intersection_spec UNIV guards ivl sctn (X0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P2, CXS \<union> CX)))"])
    subgoal by refine_vcg
    subgoal by auto
    subgoal by auto
    subgoal
      apply clarsimp
      subgoal for c
        apply (rule exI[where x=c])
        apply (rule conjI)
         apply (rule order_trans) prefer 2 apply assumption
         apply (rule UN_mono) apply assumption apply (rule order_refl) apply assumption
        done
      done
    subgoal for \<sigma>
      apply (clarsimp)
      subgoal for X0
        apply (rule exI[where x="\<lambda>(b, x). (if b then X0 x else P0 x) \<inter> XS0 - trap \<times> UNIV "])
        apply (rule conjI)
        subgoal premises prems
          using \<open>(\<Union>x\<in>PS. P0 x) \<union> (\<Union>x\<in>PS. R0 x) = XS0 - trap \<times> UNIV\<close>
            \<open>(\<Union>x\<in>PS. R0 x) \<subseteq> (\<Union>x\<in>\<sigma>. X0 x)\<close>
          by auto
        subgoal by (auto intro: do_intersection_spec_subset)
        done
      done
    apply clarsimp
    subgoal for a b b' c d e f g h i j
      apply (cases "c = {}")
      subgoal by (auto intro!: exI[where x="j"])
      subgoal
        using [[goals_limit=1]]
        apply clarsimp
        apply refine_vcg
        subgoal premises prems for k l
        proof -
          note prems
          then show ?thesis
            apply -
            apply (drule bspec, assumption)+
            apply clarsimp
            subgoal premises prems
              using \<open>g \<inter> (guards \<union> \<Union>k) = {}\<close> \<open>l = k - {d \<inter> plane_of e} \<or> l = k\<close> \<open>d \<inter> plane_of e \<subseteq> \<Union>k\<close>
              by auto
            done
        qed
        apply simp
        apply (drule bspec, assumption)
        apply simp
        apply (erule exE conjE)+
        subgoal for k l m n p q
          apply (subgoal_tac "\<And>x. x \<in> m \<Longrightarrow> p x = {}")
           defer
          subgoal for x
          proof goal_cases
            case 1
            from 1(10,15,24)
            show ?case
              by (auto dest!: bspec[where x=x])
          qed
          apply simp
          subgoal premises prems
          proof -
            note prems
            from prems have "finite (q ` m)" "flowsto (R0 (a, b, b', c, d, e, f, g)) {0..} (g \<times> UNIV) (\<Union>(q ` m))"
              by auto
            from flowsto_Union_funE[OF this]
            obtain XGs where
              XGs: "\<And>G. G \<in> q ` m \<Longrightarrow> flowsto (XGs G) {0..} (g \<times> UNIV) G"
              "R0 (a, b, b', c, d, e, f, g) = \<Union>(XGs ` (q ` m))"
              by metis
            define q0 where "q0 = XGs o q"
            have "case x of (X, P1, P2, R, ivl, sctn, CX, CXS) \<Rightarrow>
                do_intersection_spec UNIV guards ivl sctn (q0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P1, CXS \<union> CX) \<and>
                do_intersection_spec UNIV guards ivl sctn (q0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P2, CXS \<union> CX)"
              if "x \<in> m"
              for x
            proof (clarsimp, goal_cases)
              case (1 X P1 P2 R ivl sctn CX CXS)
              with prems(10)[rule_format, OF \<open>x \<in> m\<close>] prems(15)[rule_format, OF \<open>x \<in> m\<close>] \<open>_ = c\<close>
              have *: "R = {}"
                "x = (X, P1, P2, {}, ivl, sctn, CX, CXS)"
                "ivl \<inter> plane_of sctn \<subseteq> \<Union>l"
                "closed ivl"
                "c \<subseteq> CXS \<times> UNIV"
                "g \<subseteq> CXS"
                "\<Union>(q ` m) \<subseteq> CXS \<times> UNIV"
                "CXS \<inter> (guards \<union> \<Union>l) = {}"
                "p (X, P1, P2, {}, ivl, sctn, CX, CXS) = {}"
                "p (X, P1, P2, R, ivl, sctn, CX, CXS) \<subseteq> CXS \<times> UNIV"
                "do_intersection_spec UNIV guards ivl sctn (q (X, P1, P2, {}, ivl, sctn, CX, CXS)) (P1, CXS \<union> CX)"
                "do_intersection_spec UNIV guards ivl sctn (q (X, P1, P2, {}, ivl, sctn, CX, CXS)) (P2, CXS \<union> CX)"
                by auto
              have "do_intersection_spec UNIV guards ivl sctn (q0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P1, (CXS \<union> CX) \<union> (CXS \<union> CX))"
                apply (rule do_intersection_flowsto_trans_outside)
                       apply (simp add: q0_def)
                       apply (rule flowsto_subset)
                           apply (rule XGs)
                using \<open>x \<in> m\<close> apply (rule imageI)
                using 1 apply force
                         apply force
                using * apply force
                       apply (rule order_refl)
                using * apply (auto intro!: *)[]
                subgoal
                  using * \<open>x \<in> m\<close>
                  by (auto simp add: )
                subgoal using * by (auto simp: do_intersection_spec_def)
                subgoal using * by (auto simp: do_intersection_spec_def)
                subgoal
                proof -
                  have "q0 (X, P1, P2, R, ivl, sctn, CX, CXS) \<subseteq> XGs (q x)"
                    by (auto simp: q0_def 1)
                  also have "\<dots> \<subseteq> R0 (a, b, b', c, d, e, f, g)" using \<open>x \<in>m\<close> XGs by auto
                  also have "\<dots> \<subseteq> (CXS \<union> CX) \<times> UNIV"
                    using prems(20) \<open>g \<subseteq> CXS\<close> by auto
                  finally show ?thesis by simp
                qed
                subgoal by fact
                subgoal using * by (auto simp: do_intersection_spec_def)
                done
              moreover have "do_intersection_spec UNIV guards ivl sctn (q0 (X, P1, P2, R, ivl, sctn, CX, CXS)) (P2, (CXS \<union> CX) \<union> (CXS \<union> CX))"
                apply (rule do_intersection_flowsto_trans_outside)
                       apply (simp add: q0_def)
                       apply (rule flowsto_subset)
                           apply (rule XGs)
                using \<open>x \<in> m\<close> apply (rule imageI)
                using 1 apply force
                         apply force
                using * apply force
                       apply (rule order_refl)
                using * apply (auto intro!: *)[]
                subgoal
                  using * \<open>x \<in> m\<close>
                  by (auto simp add: )
                subgoal using * by (auto simp: do_intersection_spec_def)
                subgoal using * by (auto simp: do_intersection_spec_def)
                subgoal
                proof -
                  have "q0 (X, P1, P2, R, ivl, sctn, CX, CXS) \<subseteq> XGs (q x)"
                    by (auto simp: q0_def 1)
                  also have "\<dots> \<subseteq> R0 (a, b, b', c, d, e, f, g)" using \<open>x \<in>m\<close> XGs by auto
                  also have "\<dots> \<subseteq> (CXS \<union> CX) \<times> UNIV"
                    using prems(20) \<open>g \<subseteq> CXS\<close> by auto
                  finally show ?thesis by simp
                qed
                subgoal by fact
                subgoal using * by (auto simp: do_intersection_spec_def)
                done
              ultimately show ?case
                by (simp add: )
            qed note q0 = this
            have q0': "(a, aa, aa', ab, ac, ad, ae, b) \<in> m \<Longrightarrow> XS0 \<subseteq> b \<times> UNIV" for a aa aa' ab ac ad ae b
              apply (drule prems(15)[rule_format])
              using \<open>XS0 \<subseteq> g \<times> UNIV\<close>
              by auto
            from prems
            show ?thesis
              apply (intro exI[where x="\<lambda>x. if x \<in> i \<inter> m then j x \<union> q0 x else if x \<in> i then j x else q0 x"] conjI)
              subgoal 1 premises prems
                unfolding XGs
                apply simp
                by (auto simp: q0_def)
              subgoal premises _
                by (rule order_trans[OF \<open>(\<Union>x\<in>h. R0 x) \<subseteq> (\<Union>x\<in>i. j x)\<close>]) auto
              subgoal premises _ using prems(6)[rule_format] q0
                apply auto
                subgoal by (auto dest!: prems(6)[rule_format] q0 intro!: do_intersection_spec_union2)
                subgoal by (auto dest!: prems(6)[rule_format] q0 intro!: do_intersection_spec_union2)
                subgoal by (auto intro!: do_intersection_spec_union2)
                subgoal by (auto dest!: prems(6)[rule_format] q0' intro!: do_intersection_spec_union2)
                subgoal by (auto dest!: prems(6)[rule_format] q0 intro!: do_intersection_spec_union2)
                subgoal by (auto dest!: prems(6)[rule_format] q0 intro!: do_intersection_spec_union2)
                subgoal by (auto dest!: prems(6)[rule_format] q0 intro!: do_intersection_spec_union2)
                subgoal by (auto dest!: prems(6)[rule_format] q0 intro!: do_intersection_spec_union2)
                done
              done
          qed
          done
        done
      done
    done
  done

lemma width_spec_ivl[THEN order_trans, refine_vcg]: "width_spec_ivl M X \<le> SPEC (\<lambda>x. True)"
  unfolding width_spec_ivl_def
  by (refine_vcg)

lemma partition_ivl_spec[le, refine_vcg]:
  shows "partition_ivl cg XS \<le> SPEC (\<lambda>YS. XS \<subseteq> YS)"
  unfolding partition_ivl_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all)
  subgoal by fastforce
  subgoal by fastforce
  subgoal by fastforce
  subgoal by fastforce
  subgoal premises prems for a b c d e f ws g h i j k l m n
  proof -
    note prems
    have disj: "\<And>A Aa. n \<notin> A \<or> \<not> XS \<inter> A \<subseteq> Aa \<or> n \<in> Aa"
      using prems by blast
    then have "n \<in> g"
      using prems by (metis (no_types) Un_iff atLeastAtMost_iff subset_iff)
    then show ?thesis
      using disj prems by (meson atLeastAtMost_iff)
  qed
  done

lemma op_inter_fst_ivl_scaleR2[le,refine_vcg]:
  "op_inter_fst_ivl_scaleR2 X Y \<le> SPEC (\<lambda>R. X \<inter> (Y \<times> UNIV) = R)"
  unfolding op_inter_fst_ivl_scaleR2_def
  apply refine_vcg
  apply (auto simp: scaleR2_def)
  subgoal for a b c d e f g h i j k
    by (rule image_eqI[where x="(i, (j, k))"]; fastforce)
  subgoal for a b c d e f g h i j k
    by (rule image_eqI[where x="(i, (j, k))"]; fastforce)
  done

lemma op_inter_fst_ivl_coll_scaleR2[le,refine_vcg]:
  "op_inter_fst_ivl_coll_scaleR2 X Y \<le> SPEC (\<lambda>R. X \<inter> (Y \<times> UNIV) = R)"
  unfolding op_inter_fst_ivl_coll_scaleR2_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. (\<Union>Xs) \<inter> (Y \<times> UNIV) \<subseteq> R \<and> R \<subseteq> X \<inter> (Y \<times> UNIV)"])
    auto

lemma op_inter_ivl_co[le, refine_vcg]: "op_ivl_of_ivl_coll X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding op_ivl_of_ivl_coll_def
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>R (l, u). \<Union>R \<subseteq> {l .. u}"])
   apply auto
   apply (metis Set.basic_monos(7) Sup_le_iff atLeastAtMost_iff inf.coboundedI2 inf_sup_aci(1))
  by (meson Set.basic_monos(7) UnionI atLeastAtMost_iff le_supI1)

lemma op_inter_ivl_coll_scaleR2[le,refine_vcg]:
  "op_inter_ivl_coll_scaleR2 X Y \<le> SPEC (\<lambda>R. X \<inter> (Y \<times> UNIV) \<subseteq> R)"
  unfolding op_inter_ivl_coll_scaleR2_def
  apply refine_vcg
  subgoal for _ _ _ A l u
    by (auto, rule scaleR2_subset[where i'=l and j'=u and k'=A], auto)
  done

lemma [le, refine_vcg]: "op_image_fst_ivl_coll X \<le> SPEC (\<lambda>R. R = fst ` X)"
  unfolding op_image_fst_ivl_coll_def
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. fst ` (\<Union>Xs) \<subseteq> R \<and> R \<subseteq> fst ` X"])
     apply auto
  apply force+
  done

lemma op_single_inter_ivl[le, refine_vcg]: "op_single_inter_ivl a fxs \<le> SPEC (\<lambda>R. a \<inter> fxs \<subseteq> R)"
  unfolding op_single_inter_ivl_def
  by refine_vcg auto

lemma partition_ivle_spec[le, refine_vcg]:
  shows "partition_ivle cg XS \<le> SPEC (\<lambda>YS. XS \<subseteq> YS)"
  unfolding partition_ivle_def autoref_tag_defs
  supply [refine_vcg del] = scaleR2_rep_of_coll2
    and [refine_vcg] = scaleR2_rep_of_coll
  apply (refine_vcg)
  subgoal by (fastforce simp: scaleR2_def)
  subgoal by auto
  apply clarsimp
  subgoal by (fastforce simp: scaleR2_def)
  done


lemma vec1repse[THEN order_trans, refine_vcg]:
  "vec1repse CX \<le> SPEC (\<lambda>R. case R of None \<Rightarrow> True | Some X \<Rightarrow> X = vec1_of_flow1 ` CX)"
  unfolding vec1repse_def
  apply (refine_vcg FORWEAK_mono_rule[where
        I="\<lambda>XS R. case R of None \<Rightarrow> True | Some R \<Rightarrow> vec1_of_flow1 ` (\<Union>XS) \<subseteq> R \<and> R \<subseteq> vec1_of_flow1 ` CX"])
  apply (auto simp: scaleR2_def split: option.splits)
  subgoal for a b c d e f g h i j
    apply (auto simp: vimage_def image_def)
    apply (rule exI[where x="h"])
    apply auto
    apply (rule exI[where x=f])
    apply (rule exI[where x="matrix j"])
    apply auto
     apply (rule bexI)
    by (auto simp: vec1_of_flow1_def matrix_scaleR)
  subgoal for a b c d e f g h i j
    apply (rule bexI)
     defer apply assumption
    apply (rule image_eqI[where x="(f, g, j)"])
    by (auto simp: flow1_of_vec1_def vec1_of_flow1_def matrix_scaleR[symmetric])
  subgoal by fastforce
  subgoal for a b c d e f g h i j k l
    apply (auto simp: vimage_def image_def)
    apply (rule exI[where x="j"])
    apply auto
    apply (rule exI[where x=h])
    apply (rule exI[where x="matrix l"])
    apply auto
     apply (rule bexI)
    by (auto simp: vec1_of_flow1_def matrix_scaleR)
  subgoal by fastforce
  subgoal for a b c d e f g h i j k l
    apply (rule bexI)
     defer apply assumption
    apply (rule image_eqI[where x="(h, i, l)"])
    by (auto simp: flow1_of_vec1_def vec1_of_flow1_def matrix_scaleR[symmetric])
  done

lemma scaleR2_rep1[le, refine_vcg]: "scaleR2_rep1 Y \<le> SPEC (\<lambda>R. Y \<subseteq> R)"
  unfolding scaleR2_rep1_def
  apply refine_vcg
  subgoal by (auto simp: norm2_slp_def)
  subgoal for a b c d e y z f g h i j prec k l m n p q r s
    apply (auto simp: scaleR2_def image_def vimage_def)
    subgoal premises prems for B C D E
    proof -
      define ij where "ij = (i + j) / 2"
      from prems
      have "ij > 0"
        by (auto simp: ij_def)
      show ?thesis
        unfolding ij_def[symmetric]
        apply (rule exI[where x="1 / ij * B"])
        apply (intro conjI) prefer 3
          apply (rule bexI[where x="(D, ij *\<^sub>R E)"])
        subgoal using \<open>ij > 0\<close> by auto
        subgoal
          using prems
          using \<open>(D, E) \<in> c\<close> \<open>c \<subseteq> {(n, p)..(q, r)}\<close> \<open>ij > 0\<close>
          by (auto simp: ij_def[symmetric] intro!: scaleR_left_mono)
        subgoal
          using \<open>d \<le> ereal B\<close> \<open>0 < ij\<close> \<open>0 < d\<close>
          apply (cases d)
            apply (simp only: times_ereal.simps ereal_less_eq)
            apply (rule mult_mono)
               apply (rule real_divl)
          by auto
        subgoal
          using \<open>0 < d\<close> \<open>d \<le> ereal B\<close> \<open>ereal B \<le> e\<close> \<open>0 < ij\<close> \<open>0 < e\<close>
            \<open>0 < real_divr prec 1 ((i + j) / 2)\<close>
          unfolding ij_def[symmetric]
          apply (cases e; cases d)
                  apply (simp only: times_ereal.simps ereal_less_eq)
                  apply (rule mult_mono)
                     apply (rule real_divr)
          by auto
        done
    qed
    done
  done

lemma reduce_ivl[le, refine_vcg]: "reduce_ivl Y b \<le> SPEC (\<lambda>R. Y \<subseteq> R)"
  unfolding reduce_ivl_def
  apply refine_vcg
     apply (auto simp add: scaleR2_def image_def vimage_def plane_of_def )
     prefer 2
  subgoal using basic_trans_rules(23) by blast
    prefer 3
  subgoal using basic_trans_rules(23) by blast
proof goal_cases
  case (1 i0 i1 s0 s1 y0 y1)
  from 1 have le: "1 \<le> (y1 \<bullet> b) / (i1 \<bullet> b)"
    by (auto simp: min_def dest!: inner_Basis_mono[OF _ \<open>b \<in> Basis\<close>])
  show ?case
    apply (rule exI[where x="(y1 \<bullet> b) / (i1 \<bullet> b)"])
    apply (rule conjI) apply fact
    apply (rule bexI[where x="(y0, ((i1 \<bullet> b) / (y1 \<bullet> b)) *\<^sub>R y1)"])
    subgoal using 1 le by simp
    subgoal using 1 le apply simp
      apply (rule conjI)
      subgoal
        apply (auto simp: eucl_le[where 'a="'c"])
        apply (auto simp: divide_simps)
        apply (subst mult.commute)
        subgoal for i
          apply (cases " y1 \<bullet> b \<le> i1 \<bullet> b")
           apply (rule order_trans)
            apply (rule mult_left_mono[where b="y1 \<bullet> i"])
             apply (auto simp: mult_le_cancel_right)
          apply (cases "i1 \<bullet> i \<le> 0")
           apply (rule order_trans)
            apply (rule mult_right_mono_neg[where b="i1 \<bullet> b"])
             apply auto
          by (auto simp: not_le inner_Basis split: if_splits dest!: bspec[where x=i])
        done
      subgoal
        apply (auto simp: eucl_le[where 'a="'c"])
        subgoal for i
          apply (cases "i = b")
           apply (auto simp: divide_simps)
          subgoal by (auto simp: divide_simps algebra_simps)
          subgoal apply (auto simp: divide_simps algebra_simps inner_Basis)
            apply (subst mult.commute)
            apply (rule order_trans)
             apply (rule mult_right_mono[where b="s1 \<bullet> i"]) apply simp
             apply simp
            apply (rule mult_left_mono)
            by auto
          done
        done
      done
    done
next
  case (2 i0 i1 s0 s1 y0 y1)
  from 2 have le: "1 \<le> (y1 \<bullet> b) / (s1 \<bullet> b)"
    by (auto simp: min_def abs_real_def divide_simps dest!: inner_Basis_mono[OF _ \<open>b \<in> Basis\<close>])
  show ?case
    apply (rule exI[where x="(y1 \<bullet> b) / (s1 \<bullet> b)"])
    apply (rule conjI) apply fact
    apply (rule bexI[where x="(y0, ((s1 \<bullet> b) / (y1 \<bullet> b)) *\<^sub>R y1)"])
    subgoal using 2 le by simp
    subgoal using 2 le apply simp
      apply (rule conjI)
      subgoal
        apply (auto simp: eucl_le[where 'a="'c"])
        subgoal for i
          apply (cases "i = b")
           apply (auto simp: divide_simps)
          subgoal by (auto simp: divide_simps algebra_simps)
          subgoal apply (auto simp: divide_simps algebra_simps inner_Basis)
            apply (subst mult.commute)
            apply (cases "y1 \<bullet> i \<le> 0")
             apply (rule order_trans)
              apply (rule mult_left_mono_neg[where b="y1 \<bullet> b"])
               apply (auto simp: mult_le_cancel_right not_le)
            apply (rule order_trans)
             apply (rule mult_right_mono_neg[where b="i1 \<bullet> i"])
              apply (auto intro!: mult_left_mono_neg)
            done
          done
        done
      subgoal
        apply (auto simp: eucl_le[where 'a="'c"])
        subgoal for i
          apply (cases "i = b")
          subgoal by (auto simp: divide_simps algebra_simps)
          subgoal apply (auto simp: divide_simps algebra_simps inner_Basis)
            apply (subst mult.commute)
            apply (cases "y1 \<bullet> i \<ge> 0")
             apply (rule order_trans)
              apply (rule mult_left_mono_neg[where b="y1 \<bullet> i"]) apply simp
              apply simp
             apply (rule mult_right_mono) apply force
             apply force
          proof -
            assume a1: "\<forall>i\<in>Basis. s1 \<bullet> b * (if b = i then 1 else 0) \<le> s1 \<bullet> i"
            assume a2: "i \<in> Basis"
            assume a3: "i \<noteq> b"
            assume a4: "y1 \<bullet> b < 0"
            assume a5: "s1 \<bullet> b < 0"
            assume a6: "\<not> 0 \<le> y1 \<bullet> i"
            have "s1 \<bullet> b * (if b = i then 1 else 0) \<le> s1 \<bullet> i"
              using a2 a1 by metis
            then have f7: "0 \<le> s1 \<bullet> i"
              using a3 by (metis (full_types) mult_zero_right)
            have f8: "y1 \<bullet> b \<le> 0"
              using a4 by (metis eucl_less_le_not_le)
            have "s1 \<bullet> b \<le> 0"
              using a5 by (metis eucl_less_le_not_le)
            then show "y1 \<bullet> b * (s1 \<bullet> i) \<le> s1 \<bullet> b * (y1 \<bullet> i)"
              using f8 f7 a6 by (metis mult_right_mono_le mult_zero_left zero_le_mult_iff zero_le_square)
          qed
          done
        done
      done
    done
qed

lemma reduce_ivle[le, refine_vcg]:
  "reduce_ivle Y b \<le> SPEC (\<lambda>R. Y \<subseteq> R)"
  unfolding reduce_ivle_def
  apply refine_vcg
  apply (auto simp: scaleR2_def image_def vimage_def)
  subgoal for a b c d e f g h i j k
    apply (drule subsetD, assumption)
    apply auto
    subgoal for l m
    apply (rule exI[where x="l * g"])
      apply (intro conjI)
    subgoal
      unfolding times_ereal.simps[symmetric]
      apply (rule ereal_mult_mono)
      subgoal by (cases e) auto
      subgoal by (cases b) auto
      subgoal by (cases b) auto
      subgoal by (cases e) auto
      done
    subgoal
      unfolding times_ereal.simps[symmetric]
      apply (rule ereal_mult_mono)
      subgoal by (cases b) auto
      subgoal by (cases b) auto
      subgoal by (cases b) auto
      subgoal by (cases e) auto
      done
    subgoal by force
    done
  done
  done


lemma reduces_ivle[le, refine_vcg]:
  "reduces_ivle X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding reduces_ivle_def
  by refine_vcg auto

lemma ivlse_of_setse[le, refine_vcg]: "ivlse_of_setse X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding ivlse_of_setse_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. \<Union>Xs \<subseteq> R"])
    (auto simp: scaleR2_def image_def vimage_def)

lemma setse_of_ivlse[le, refine_vcg]:
  "setse_of_ivlse X \<le> SPEC (\<lambda>R. R = X)"
  unfolding setse_of_ivlse_def
  apply (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xs R. \<Union>Xs \<subseteq> R \<and> R \<subseteq> X"])
       apply clarsimp_all
  subgoal by (rule bexI)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

lemma partition_set_spec[le, refine_vcg]:
  shows "partition_set ro XS \<le> SPEC (\<lambda>YS. XS \<subseteq> YS)"
  unfolding partition_set_def autoref_tag_defs
  apply (refine_vcg)
  subgoal by (fastforce simp: scaleR2_def vimage_def image_def)
  subgoal by fastforce
  done

lemma partition_sets_spec[le, refine_vcg]:
  shows "partition_sets ro XS \<le> SPEC (\<lambda>YS. (\<Union>(_, _, PS, _, _, _, _, _) \<in> XS. PS) \<subseteq> YS)"
  unfolding partition_sets_def autoref_tag_defs
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X Y. (\<Union>(_, _, PS, _, _, _, _, _) \<in> X. PS) \<subseteq> Y"]) auto

lemma
  do_intersection_poincare_mapstos_trans:
  assumes pm: "\<And>i. i \<in> I \<Longrightarrow> poincare_mapsto (p i) (X0 i) UNIV (CX i) (X1 i)"
  assumes di: "do_intersection_spec UNIV guards ivl sctn (\<Union>i\<in>I. X1 i) (P, CP)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> fst ` (X1 i) \<subseteq> CP"
  assumes "\<And>i. i \<in> I \<Longrightarrow> {x \<in> ivl. x \<in> plane_of sctn} \<inter> CX i = {}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> guards \<inter> (CX i \<union> CP) = {}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> X0 i \<subseteq> CX i \<times> UNIV"
  assumes "\<And>i. i \<in> I \<Longrightarrow> closed (p i)"
  assumes "closed ivl"
  assumes "\<And>i. i \<in> I \<Longrightarrow> CX i \<subseteq> Csafe"
  shows "do_intersection_spec UNIV guards ivl sctn (\<Union>i\<in>I. X0 i) (P, (\<Union>i\<in>I. CX i) \<union> CP)"
  apply (auto simp: do_intersection_spec_def)
  subgoal
    apply (simp del: UN_simps add: UN_extend_simps)
    apply (rule impI)
    apply (thin_tac "I \<noteq> {}")
    subgoal
    proof -
      from di have pmi: "poincare_mapsto {x \<in> ivl. x \<in> plane_of sctn} (X1 i) UNIV CP P" if "i \<in> I" for i
        by (auto simp: do_intersection_spec_def intro: poincare_mapsto_subset that)
      show ?thesis
        apply (rule poincare_mapsto_UnionI)
         apply (rule poincare_mapsto_trans[OF pm pmi])
               apply clarsimp_all
        subgoal s1 using assms by (auto simp: do_intersection_spec_def)
        subgoal using assms apply (auto simp: do_intersection_spec_def)
           apply blast
          by (metis (mono_tags, lifting) s1 mem_Collect_eq mem_simps(2) mem_simps(4))
        subgoal using assms by auto
        subgoal using assms by auto
        subgoal premises prems for i x d
        proof -
          note prems
          have [intro, simp]: "closed {x \<in> ivl. x \<in> plane_of sctn} " "closed {x \<in> ivl. x \<bullet> normal sctn = pstn sctn}"
            by (auto intro!: closed_levelset_within continuous_intros simp: plane_of_def assms)
          have set_eq: "(CX i \<union> CP) \<times> UNIV = (fst ` X1 i \<times> UNIV \<union> CX i \<times> UNIV \<union> CP \<times> UNIV)"
            using assms prems
            by auto
          have empty_inter: "{x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0} \<times> UNIV \<inter> (CX i \<union> CP) \<times> UNIV = {}"
            apply safe
            subgoal
              using assms(4)[of i] \<open>i \<in> I\<close>
              by (auto simp: plane_of_def )
            subgoal
              using assms(4)[of i]
              using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            done
          have ft: "flowsto (X0 i) {0<..} ((CX i \<union> CP) \<times> UNIV) (fst ` P \<times> UNIV)"
            unfolding set_eq
            apply (rule flowsto_poincare_mapsto_trans_flowsto[OF poincare_mapsto_imp_flowsto[OF pm[OF \<open>i \<in> I\<close>]]
                  pmi[OF \<open>i \<in> I\<close>] _ _ order_refl])
            using assms prems by (auto)
          then have ret: "returns_to {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0} x"
            apply (rule returns_to_flowstoI[OF _ _ _ _ _ _ order_refl])
            subgoal using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            subgoal by (rule empty_inter)
            subgoal using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            subgoal using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            subgoal using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            done
          have pm: "poincare_map {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x \<in> fst ` P"
            apply (rule poincare_map_mem_flowstoI[OF ft])
            subgoal using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            subgoal using empty_inter by simp
            subgoal by auto
            subgoal by auto
            subgoal using prems assms by (auto simp: plane_of_def do_intersection_spec_def)
            subgoal by auto
            done
          from ret have "isCont (return_time {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0}) x"
            apply (rule return_time_isCont_outside)
            subgoal by fact
                apply (force intro!: derivative_eq_intros)
            subgoal by (auto intro!: continuous_intros)
            subgoal using prems pm assms by (auto simp: do_intersection_spec_def)
            subgoal using prems pm assms
              by (auto simp: eventually_at_filter plane_of_def do_intersection_spec_def)
            subgoal
            proof -
              have "x \<in> CX i" using \<open>_ \<in> I \<Longrightarrow> X0 _ \<subseteq> CX _ \<times> UNIV\<close>[OF \<open>i \<in> I\<close>] \<open>(x, _) \<in> _\<close>
                by auto
              with assms(4)[OF \<open>i \<in> I\<close>] show ?thesis
                by (auto simp: plane_of_def)
            qed
            done
          then show "isCont (return_time {x \<in> ivl. x \<in> plane_of sctn}) x" by (simp add: plane_of_def)
        qed
        done
    qed
    done
  subgoal using assms by (fastforce simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (fastforce simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms(9) by (fastforce simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  subgoal using assms by (auto simp: plane_of_def do_intersection_spec_def)
  done

lemma flow_in_stable_setD:
  "flow0 x0 t \<in> stable_set trap \<Longrightarrow> t \<in> existence_ivl0 x0 \<Longrightarrow> x0 \<in> stable_set trap"
  apply (auto simp: stable_set_def)
proof goal_cases
  case (1 s)
  then show ?case
    apply (cases "s \<le> t")
    apply (meson atLeastAtMost_iff contra_subsetD local.ivl_subset_existence_ivl)
    using contra_subsetD local.existence_ivl_reverse local.existence_ivl_trans' local.flows_reverse by fastforce
next
  case (2)
  have "\<forall>\<^sub>F x in at_top. x > max t 0"
    by (simp add: max_def)
  then have "\<forall>\<^sub>F x in at_top. flow0 (flow0 x0 t) x = flow0 x0 (t + x)"
    apply eventually_elim
    apply (subst flow_trans)
    using 2
    by auto
  from this 2(3) have "((\<lambda>s. flow0 x0 (t + s)) \<longlongrightarrow> trap) (at_top)"
    by (rule Lim_transform_eventually)
  then show ?case by (simp add: tendsto_at_top_translate_iff ac_simps)
qed

lemma
  poincare_mapsto_avoid_trap:
  assumes "poincare_mapsto p (X0 - trap \<times> UNIV) S CX P"
  assumes "closed p"
  assumes trapprop[THEN stable_onD]: "stable_on (CX \<union> fst ` P) trap"
  shows "poincare_mapsto p (X0 - trap \<times> UNIV) S CX (P - trap \<times> UNIV)"
  using assms(1,2)
  apply (auto simp: poincare_mapsto_def)
  apply (drule bspec, force)
  apply auto
  subgoal for x0 d0 D
    apply (rule exI[where x=D])
    apply (auto dest!: trapprop simp: poincare_map_def intro!: return_time_exivl assms(1,2) return_time_pos)
    subgoal for s
      by (cases "s = return_time p x0") (auto simp: )
    done
  done

lemma poincare_onto_series[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd TYPE('a::enum rvec)"
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  assumes trapprop: "stable_on (Csafe - (ivl \<inter> plane_of sctn)) trap"
  shows "poincare_onto_series symstart trap guards (X0::'a eucl1 set) ivl sctn ro \<le>
       SPEC (\<lambda>XS. do_intersection_spec UNIV {} ivl sctn (X0 - trap \<times> UNIV)
          (XS, Csafe - (ivl \<inter> plane_of sctn)) \<and>
          fst ` X0 - trap \<subseteq> Csafe - (ivl \<inter> plane_of sctn))"
proof (induction guards arbitrary: X0)
  case Nil
  then show ?case
    apply (simp add:)
    apply refine_vcg
    apply (clarsimp simp add: ivlsctn_to_set_def)
     apply (rule do_intersection_spec_subset2, assumption)
    subgoal by (auto simp: do_intersection_spec_def)
    subgoal by (auto simp: do_intersection_spec_def)
    subgoal by (auto simp: do_intersection_spec_def)
    subgoal by (auto simp: do_intersection_spec_def)
    subgoal by (auto simp: do_intersection_spec_def)
    subgoal by (auto simp: do_intersection_spec_def)
    done
next
  case (Cons a guards)
  note Cons.IH[simplified, le, refine_vcg]
  show ?case
    apply auto
    apply refine_vcg
     apply clarsimp_all
     defer
    subgoal premises prems for b c d e f g h
    proof -
      from prems have "(f, g) \<in> (\<Union>x\<in>c. h x)"
        by auto
      then obtain x where "x \<in> c" "(f, g) \<in> (h x)"
        by auto
      then show ?thesis
        using prems(14)[rule_format, OF \<open>x \<in> c\<close>] prems(5-7)
        by (cases x) (auto simp: do_intersection_spec_def)
    qed
    subgoal premises prems for c ro d e f
    proof -
      let ?s = "trap \<times> UNIV"
      note prems
      from \<open>do_intersection_spec _ _ _ _ _ _ \<close>
      have disro: "do_intersection_spec UNIV {} ivl sctn ((\<Union>i\<in>ro. case i of (_, _, PS, _, _, _, _, _, _) \<Rightarrow> PS - ?s))
          (e, Csafe - ivl \<inter> plane_of sctn)"
        apply (rule do_intersection_spec_subset)
        using prems by auto
      have subset: "(Csafe - ivl \<inter> plane (normal sctn) (pstn sctn)) \<supseteq>
        (snd (snd (snd (snd (snd (snd (snd (snd i))))))) \<union>
        fst (snd (snd (snd (snd (snd (snd (snd i))))))) \<union> fst ` fst (snd (snd i)))" if "i \<in> ro" for i
        using prems(12)[rule_format, unfolded do_intersection_spec_def, OF that]
        apply (clarsimp )
        subgoal for s X P1 P2 R ivla sctna CX CXS
          apply (rule conjI)
          subgoal by (auto simp: plane_of_def)
          subgoal by (auto simp: plane_of_def)
          done
        done
      have pmro: "poincare_mapsto
            (case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> {x \<in> ivla. x \<in> plane_of sctna})
            (f i - ?s) UNIV
            (case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> CXS \<union> CX)
            (case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> P1)"
        if "i \<in> ro"
        for i
        using prems(12)[rule_format, unfolded do_intersection_spec_def, OF that]
        by (auto intro: poincare_mapsto_subset)
      then have pmro: "poincare_mapsto
            (case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> {x \<in> ivla. x \<in> plane_of sctna})
            (f i - ?s) UNIV
            (case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> CXS \<union> CX)
            (case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> P1 - ?s)"
        if "i \<in> ro"
        for i
        unfolding split_beta'
        apply (rule poincare_mapsto_avoid_trap)
        using that prems assms
        by (auto intro!: closed_levelset_within continuous_intros
            stable_on_mono[OF _ subset]
            simp: plane_of_def)
      have "do_intersection_spec UNIV {} ivl sctn (\<Union>i\<in>ro. f i - ?s)
        (e, (\<Union>i\<in>ro. case i of (s, X, P1, P2, R, ivla, sctna, CX, CXS) \<Rightarrow> CXS \<union> CX) \<union>
        (Csafe - ivl \<inter> plane_of sctn))"
        apply (rule do_intersection_poincare_mapstos_trans[OF pmro disro])
        subgoal by auto
        subgoal premises that for i
          using prems(12)[rule_format, unfolded do_intersection_spec_def, OF that]
          by (auto simp: do_intersection_spec_def)
        subgoal using assms(1,2) prems by (auto simp: do_intersection_spec_def)
        subgoal by auto
        subgoal premises that for i
          using prems(12)[rule_format, unfolded do_intersection_spec_def, OF that]
            prems(11) that
          by (auto simp: do_intersection_spec_def)
        subgoal using assms(1,2) prems by (auto simp: do_intersection_spec_def)
        subgoal using assms(1,2) prems by (auto simp: do_intersection_spec_def)
        subgoal using assms(1,2) prems by (auto simp: do_intersection_spec_def)
        done
      then show ?thesis
        unfolding \<open>(\<Union>x\<in>ro. f x) = X0 - trap \<times> UNIV\<close>
        apply (rule do_intersection_spec_subset2)
        subgoal using assms(1,2) prems by (auto simp: do_intersection_spec_def)
        using prems
        by (auto simp: do_intersection_spec_def intro: poincare_mapsto_subset)
    qed
    done
qed

lemma
  do_intersection_flowsto_trans_return:
  assumes "flowsto XS0 {0<..} (CX \<times> UNIV) X1"
  assumes "do_intersection_spec UNIV guards ivl sctn X1 (P, CP)"
  assumes "fst ` X1 \<subseteq> CP"
  assumes "{x \<in> ivl. x \<in> plane_of sctn} \<inter> CX = {}"
  assumes "guards \<inter> (CX \<union> CP) = {}"
  assumes "closed ivl"
  assumes "CX \<subseteq> sbelow_halfspace sctn \<inter> Csafe"
  assumes subset_plane: "fst ` XS0 \<subseteq> plane_of sctn \<inter> ivl"
  assumes down: "\<And>x d. (x, d) \<in> XS0 \<Longrightarrow> ode x \<bullet> normal sctn < 0" "\<And>x. x \<in> CX \<Longrightarrow> ode x \<bullet> normal sctn < 0"
  shows "do_intersection_spec (below_halfspace sctn) guards ivl sctn XS0 (P, CX \<union> CP)"
  using assms
  apply (auto simp: do_intersection_spec_def)
  subgoal
    apply (rule flowsto_poincare_trans, assumption, assumption)
    subgoal by simp
    subgoal by auto
    subgoal using assms(3) by auto
    subgoal by (auto intro!: closed_levelset_within continuous_intros simp: plane_of_def)
     prefer 2
    subgoal by (auto simp add: plane_of_def halfspace_simps)
    subgoal premises prems for x d
    proof -
      have [intro, simp]: "closed {x \<in> ivl. x \<in> plane_of sctn} " "closed {x \<in> ivl. x \<bullet> normal sctn = pstn sctn}"
        by (auto intro!: closed_levelset_within continuous_intros simp: plane_of_def assms)
      from subset_plane have "fst ` XS0 \<subseteq> below_halfspace sctn" by (auto simp: )
      from flowsto_stays_sbelow[OF \<open>flowsto _ _ _ _\<close> this down(2)]
      have ft_below: "flowsto XS0 pos_reals (CX \<times> UNIV \<inter> sbelow_halfspace sctn \<times> UNIV) X1"
        by auto
      from flowsto_poincare_mapsto_trans_flowsto[OF ft_below \<open>poincare_mapsto _ _ _ _ _\<close> _ _ order_refl]
      have ft: "flowsto XS0 {0<..} (X1 \<union> CX \<times> UNIV \<inter> sbelow_halfspace sctn \<times> UNIV \<union> CP \<times> UNIV) (fst ` P \<times> UNIV)"
        by (auto simp: )
      have ret: "returns_to {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0} x"
        apply (rule returns_to_flowstoI[OF ft])
        using prems by (auto simp: plane_of_def halfspace_simps)
      have pm: "poincare_map {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x \<in> fst ` P"
        apply (rule poincare_map_mem_flowstoI[OF ft])
        using prems by (auto simp: plane_of_def halfspace_simps)
      from pm prems have evmem: "\<forall>\<^sub>F x in at (poincare_map {x \<in> ivl. x \<bullet> normal sctn = pstn sctn} x) within
        plane_of sctn. x \<in> ivl"
        by auto
      from ret have "continuous (at x within {x. x \<bullet> normal sctn - pstn sctn \<le> 0})
        (return_time {x \<in> ivl. x \<bullet> normal sctn - pstn sctn = 0})"
        apply (rule return_time_continuous_below)
               apply (rule derivative_eq_intros refl)+
               apply force
        subgoal using \<open>closed ivl\<close> by auto
        subgoal using prems pm by (auto simp: plane_of_def eventually_at_filter)
        subgoal by (auto intro!: )
        subgoal using prems pm by auto
        subgoal using prems by auto
        subgoal using prems pm by (auto intro!: assms simp: plane_of_def)
        subgoal using prems pm by auto
        done
      then show "continuous (at x within below_halfspace sctn) (return_time {x \<in> ivl. x \<in> plane_of sctn})"
        by (simp add: plane_of_def halfspace_simps)
    qed
    done
  done

lemma do_intersection_spec_sctn_cong:
  assumes "sctn = sctn' \<or> (normal sctn = - normal sctn' \<and> pstn sctn = - pstn sctn')"
  shows "do_intersection_spec a b c sctn d e = do_intersection_spec a b c sctn' d e"
  using assms
  by (auto simp: do_intersection_spec_def plane_of_def set_eq_iff intro!: )

lemma poincare_onto_from[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd TYPE('a::enum rvec)"
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  assumes trapprop: "stable_on (Csafe - (ivl \<inter> plane_of sctn)) trap"
  shows "poincare_onto_from symstart trap S guards ivl sctn ro (XS0::'a eucl1 set) \<le>
    SPEC (poincare_mapsto (ivl \<inter> plane_of sctn) (XS0 - trap \<times> UNIV) S (Csafe - ivl \<inter> plane_of sctn))"
  unfolding poincare_onto_from_def autoref_tag_defs
  apply (refine_vcg, clarsimp_all simp: trapprop)
  subgoal by (auto simp: do_intersection_spec_def Int_def intro: poincare_mapsto_subset)
  subgoal premises prems for a b c d e f
  proof -
    note prems
    from trapprop
    have stable: "stable_on (fst ` (e \<times> UNIV \<inter> sbelow_halfspace a \<times> UNIV \<union> d)) trap"
      apply (rule stable_on_mono)
      using \<open>fst ` (d \<union> e \<times> UNIV) \<subseteq> Csafe\<close> \<open>a = sctn \<or> normal a = - normal sctn \<and> pstn a = - pstn sctn\<close>
        \<open>fst ` d \<subseteq> sbelow_halfspace a\<close>
      by (auto simp: halfspace_simps plane_of_def image_Un)
    from prems(16) have "flowsto (XS0 - trap \<times> UNIV) {0<..} (e \<times> UNIV \<inter> sbelow_halfspace a \<times> UNIV) d"
      by (rule flowsto_subset) auto
    then have ft: "flowsto (XS0 - trap \<times> UNIV) {0<..} ((e \<inter> sbelow_halfspace a) \<times> UNIV) (d - trap \<times> UNIV)"
      by (auto intro!: flowsto_mapsto_avoid_trap stable simp: Times_Int_distrib1)
    from prems(8) have di: "do_intersection_spec UNIV {} ivl a (d - trap \<times> UNIV) (f, Csafe - ivl \<inter> plane_of sctn)"
      apply (subst do_intersection_spec_sctn_cong)
       defer apply assumption
      using prems(2)
      by auto
    have "do_intersection_spec (below_halfspace a) {} ivl a (XS0 - trap \<times> UNIV)
         (f, e \<inter> sbelow_halfspace a \<union> (Csafe - ivl \<inter> plane_of sctn))"
      apply (rule do_intersection_flowsto_trans_return[OF ft di])
      subgoal using prems by (auto simp: do_intersection_spec_def halfspace_simps plane_of_def)
      subgoal by (auto simp: halfspace_simps plane_of_def)
      subgoal using prems by (auto simp: halfspace_simps plane_of_def)
      subgoal using prems by (auto simp: do_intersection_spec_def halfspace_simps plane_of_def)
      subgoal using prems by (auto simp: image_Un)
      subgoal using prems by (auto simp: do_intersection_spec_def halfspace_simps plane_of_def)
      subgoal using prems by (auto simp: do_intersection_spec_def halfspace_simps plane_of_def)
      subgoal using prems by (auto simp: do_intersection_spec_def halfspace_simps plane_of_def)
      done
    moreover have "plane_of a = plane_of sctn"
      using prems(2) by (auto simp: plane_of_def)
    ultimately show ?thesis
      apply (auto simp add: do_intersection_spec_def Int_def)
      apply (rule poincare_mapsto_subset, assumption)
      by auto
  qed
  done

lemma subset_spec1[refine_vcg]: "subset_spec1 R P dP \<le> SPEC (\<lambda>b. b \<longrightarrow> R \<subseteq> flow1_of_vec1 ` (P \<times> dP))"
  unfolding subset_spec1_def
  by refine_vcg (auto simp: vec1_of_flow1_def)


lemma subset_spec1_coll[le, refine_vcg]:
  "subset_spec1_coll R P dP \<le> subset_spec R (flow1_of_vec1 ` (P \<times> dP))"
  unfolding autoref_tag_defs subset_spec_def subset_spec1_coll_def
  by (refine_vcg) (auto simp: subset_iff set_of_ivl_def)

lemma one_step_until_time_spec[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  shows "one_step_until_time (X0::'n eucl1 set) CX t1 \<le> SPEC (\<lambda>(R, CX).
    (\<forall>(x0, d0) \<in> X0. t1 \<in> existence_ivl0 x0 \<and>
      (flow0 x0 t1, Dflow x0 t1 o\<^sub>L d0) \<in> R \<and>
      (\<forall>t \<in> {0 .. t1}. flow0 x0 t \<in> CX)) \<and>
      fst ` R \<union> CX \<subseteq> Csafe)"
  unfolding one_step_until_time_def autoref_tag_defs
  apply (refine_vcg WHILE_rule[where I="\<lambda>(t, h, X, CX). fst ` X \<subseteq> Csafe \<and> CX \<subseteq> Csafe \<and> 0 \<le> h \<and> 0 \<le> t \<and> t \<le> t1 \<and>
        (\<forall>(x0, d0) \<in> X0. t \<in> existence_ivl0 x0 \<and>
          (flow0 x0 t, Dflow x0 t o\<^sub>L d0) \<in> X \<and>
          (\<forall>s \<in> {0 .. t}. flow0 x0 s \<in> CX))"])
  subgoal by auto
  subgoal by (force simp: flowpipe_def existence_ivl_trans flow_trans)
  subgoal by (auto simp: flowpipe_def existence_ivl_trans flow_trans)
  apply clarsimp subgoal for startstep rk2_param a b c d e f g h i j
    apply (safe)
    subgoal by (auto simp: flowpipe_def intro!: existence_ivl_trans flow_trans)
    subgoal
      apply (subst flow_trans, force)
      subgoal by (auto simp: flowpipe_def intro!: existence_ivl_trans flow_trans)
      apply (subst Dflow_trans, force)
      subgoal by (auto simp: flowpipe_def intro!: existence_ivl_trans flow_trans)
      by (auto simp: blinfun_compose_assoc flowpipe_def)
    subgoal for s
      apply (drule bspec[where x="(i, j)"], assumption)
      apply auto
      apply (cases "s \<le> a")
      subgoal by auto
      subgoal
        apply (auto simp: blinfun_compose_assoc flowpipe_def)
        apply (drule bspec, assumption)
        apply auto
      proof goal_cases
        case 1
        have a: "a \<in> existence_ivl0 i" using 1 by auto
        have sa: "s - a \<in> existence_ivl0 (flow0 i a)"
          using "1"(15) "1"(19) "1"(20) local.ivl_subset_existence_ivl by fastforce
        have "flow0 i s = flow0 (flow0 i a) (s - a)"
          by (auto simp: a sa flow_trans[symmetric])
        also have "\<dots> \<in> f"
          using 1 by auto
        finally show ?case
          using 1 by simp
      qed
      done
    done
  subgoal by auto
  done

text \<open>solve ODE until the time interval \<open>{t1 .. t2}\<close>\<close>

lemma ivl_of_eucl1_coll[THEN order_trans, refine_vcg]: "ivl_of_eucl_coll X \<le> SPEC (\<lambda>R. X \<times> UNIV \<subseteq> R)"
  unfolding ivl_of_eucl_coll_def
  by refine_vcg auto

lemma one_step_until_time_ivl_spec[le, refine_vcg]:
  assumes wd[refine_vcg]: "wd (TYPE('n::enum rvec))"
  shows "one_step_until_time_ivl (X0::'n eucl1 set) CX t1 t2 \<le> SPEC (\<lambda>(R, CX).
    (\<forall>(x0, d0) \<in> X0. {t1 .. t2} \<subseteq> existence_ivl0 x0 \<and>
      (\<forall>t \<in> {t1 .. t2}. (flow0 x0 t, Dflow x0 t o\<^sub>L d0) \<in> R) \<and>
      (\<forall>t \<in> {0 .. t1}. (flow0 x0 t) \<in> CX)) \<and>
      fst ` R \<union> CX \<subseteq> Csafe)"
  unfolding one_step_until_time_ivl_def
  apply (refine_vcg, clarsimp_all)
  subgoal for X CX Y CY CY' x0 d0
    apply (drule bspec, assumption, clarsimp)
    apply (drule bspec, assumption, clarsimp simp add: nonneg_interval_mem_existence_ivlI)
    apply (rule subsetD, assumption)
    subgoal for t
      apply (drule bspec[where x=0], force)
      apply (drule bspec[where x="t - t1"], force)
      using interval_subset_existence_ivl[of t1 x0 t2]
      by (auto simp: flow_trans')
    done
  subgoal
    by (auto simp: scaleR2_def image_def vimage_def)
  done

lemma empty_symstart_flowsto:
  "X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow>
    RETURN ({}, X0) \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - {} \<times> UNIV) {0..} (CX \<times> UNIV) X)"
  by (auto intro!: flowsto_self)

subsection \<open>Poincare map returning to\<close>

lemma poincare_onto_from_ivla[le, refine_vcg]:
  assumes [refine_vcg]: "wd TYPE('n::enum rvec)"
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  assumes trapprop[refine_vcg]: "stable_on (Csafe - (ivl \<inter> plane_of sctn)) trap"
  shows "poincare_onto_from symstart trap S guards ivl sctn ro (XS0::'n eucl1 set) \<le> SPEC
     (\<lambda>P.
        wd TYPE((real, 'n) vec) \<and>
        poincare_mapsto (ivl \<inter> plane_of sctn) (XS0 - trap \<times> UNIV) S (Csafe - ivl \<inter> plane_of sctn) P)"
  by (refine_vcg)

subsection \<open>Poincare map onto (from outside of target)\<close>

subsection \<open>One step method (reachability in time)\<close>

lemma c0_info_of_apprsI:
  assumes "(b, a) \<in> clw_rel appr_rel"
  assumes "x \<in> a"
  shows "x \<in> c0_info_of_apprs b"
  using assms
  by (auto simp: appr_rel_br clw_rel_br c0_info_of_apprs_def c0_info_of_appr_def dest!: brD)

lemma c0_info_of_appr'I:
  assumes "(b, a) \<in> \<langle>clw_rel appr_rel\<rangle>phantom_rel"
  assumes "x \<in> a"
  shows "x \<in> c0_info_of_appr' b"
  using assms
  by (auto simp add: c0_info_of_appr'_def intro!: c0_info_of_apprsI split: option.splits)

lemma poincare_onto_from_in_ivl[le, refine_vcg]:
  assumes [refine_vcg]: "wd TYPE('n::enum rvec)"
  assumes [refine_vcg]: "\<And>X0. X0 \<subseteq> Csafe \<times> UNIV \<Longrightarrow> symstart X0 \<le> SPEC (\<lambda>(CX, X). flowsto (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  assumes trapprop: "stable_on (Csafe - (ivl \<inter> plane_of sctn)) trap"
  shows "poincare_onto_from_in_ivl symstart trap S guards ivl sctn ro (XS0::'n::enum eucl1 set) P dP \<le>
    SPEC (\<lambda>b. b \<longrightarrow> poincare_mapsto (ivl \<inter> plane_of sctn) (XS0 - trap \<times> UNIV) S (Csafe - ivl \<inter> plane_of sctn) (flow1_of_vec1 ` (P \<times> dP)))"
  unfolding poincare_onto_from_in_ivl_def
  apply (refine_vcg, clarsimp_all)
   apply (rule trapprop)
  apply (rule poincare_mapsto_subset)
      apply assumption
  by (auto simp: )

lemma lvivl_default_relI:
  "(dRi, set_of_lvivl' dRi::'e::executable_euclidean_space set) \<in> \<langle>lvivl_rel\<rangle>default_rel UNIV"
  if "lvivl'_invar DIM('e) dRi"
  using that
  by (auto simp: set_of_lvivl'_def set_of_lvivl_def set_of_ivl_def lvivl'_invar_def
      intro!: mem_default_relI lvivl_relI)

lemma stable_on_empty[simp]: "stable_on A {}"
  by (auto simp: stable_on_def)

lemma poincare_onto_in_ivl[le, refine_vcg]:
  assumes [simp]: "length (ode_e) = CARD('n::enum)"
  shows "poincare_onto_in_ivl guards ivl sctn ro (XS0::'n::enum eucl1 set) P dP \<le>
    SPEC (\<lambda>b. b \<longrightarrow> poincare_mapsto (ivl \<inter> plane_of sctn) (XS0) UNIV (Csafe - ivl \<inter> plane_of sctn) (flow1_of_vec1 ` (P \<times> dP)))"
proof -
  have wd[refine_vcg]: "wd TYPE((real, 'n) vec)" by (simp add: wd_def)
  show ?thesis
    unfolding poincare_onto_in_ivl_def
    apply (refine_vcg)
    subgoal by (auto intro!: flowsto_self)
    subgoal
      apply (clarsimp simp add: do_intersection_spec_def Int_def[symmetric])
      apply (rule poincare_mapsto_subset)
          apply assumption
      by auto
    done
qed


end

end