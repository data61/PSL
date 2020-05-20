theory Init_ODE_Solver
imports
  Concrete_Reachability_Analysis_C1
  Refine_Reachability_Analysis_C1
  Refine_Rigorous_Numerics_Aform
begin

subsection \<open>``Final'' Theorems, stated outside of refinement framework.\<close>

lemma br_Times_Univ: "br a I \<times>\<^sub>r (UNIV::(_ \<times> unit) set) = br (\<lambda>(x, _). (a x, ())) (\<lambda>(x, _). I x)"
  by (auto simp: br_def)

lemma TRANSFER_refl: "TRANSFER (x \<le> (x::_nres))" by (auto simp: )
lemma init_ode_ops: "(y \<Longrightarrow> x) \<Longrightarrow> (init_ode_ops x y odo, odo) \<in> ode_ops_rel"
  by (auto simp: ode_ops_rel_def init_ode_ops_def)

context approximate_sets begin

context includes autoref_syntax begin

theorem solves_poincare_map_ncc:
  fixes sctni pos ivli ssc XS ph rl ru dRi CXS X0 S trap
  defines "P \<equiv> set_of_lvivl ivli \<inter> plane_of (map_sctn eucl_of_list sctni)"
  defines "Sa \<equiv> below_halfspace (map_sctn eucl_of_list S)::'n::enum rvec set"
  defines "X0 \<equiv> c1_info_of_apprse XS"
  defines "X1 \<equiv> flow1_of_vec1 ` ({eucl_of_list rl .. eucl_of_list ru} \<times> set_of_lvivl' dRi)"
  assumes ncc: "ncc_precond TYPE('n rvec)" "ncc_precond TYPE('n vec1)"
  assumes ret: "solves_poincare_map odo symstart [S] guards ivli sctni roi XS (rl, ru) dRi"
  assumes symstart: "(symstart, symstarta::'n eucl1 set \<Rightarrow> ('n rvec set \<times> 'n eucl1 set)nres) \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>dres_nres_rel"
  assumes symstart_spec: "\<And>X0. X0 \<subseteq> Csafe odo \<times> UNIV \<Longrightarrow> symstarta X0 \<le> SPEC (\<lambda>(CX, X). flowsto odo (X0 - trap \<times> UNIV) {0..} (CX \<times> UNIV) (X))"
  assumes trapprop: "stable_on odo (Csafe odo - P) trap"
  assumes invar: "\<And>X. X \<in> set XS \<Longrightarrow> c1_info_invare CARD('n) X"
  assumes lens: "length (ode_e odo) = CARD('n)" "length (normal sctni) = CARD('n)" "length (fst ivli) = CARD('n)" "length (snd ivli) = CARD('n)"
    "length (normal S) = CARD('n)" "length rl = CARD('n)" "length ru = CARD('n)"
     "lvivl'_invar (CARD('n)*CARD('n)) dRi"
    "\<And>a xs b ba ro. (xs, ro) \<in> set guards \<Longrightarrow> ((a, b), ba) \<in> set xs \<Longrightarrow> length a = CARD('n) \<and> length b = CARD('n) \<and> length (normal ba) = CARD('n)"
  shows "poincare_mapsto odo P (X0 - trap \<times> UNIV) Sa (Csafe odo - P) X1"
proof -
  define guardsa::"('n rvec set \<times> unit) list"  where "guardsa \<equiv> map (\<lambda>(x, y). (\<Union>x\<in>set x. case x of (x, y) \<Rightarrow> (case x of (x, y) \<Rightarrow> set_of_ivl (eucl_of_list x, eucl_of_list y)) \<inter> plane_of (map_sctn eucl_of_list y), ())) guards"
  define roa where "roa = ()"
  have spm:
    "(XS, X0) \<in> clw_rel (appr1e_rel)"
    "([S], Sa) \<in> \<langle>lv_rel\<rangle>halfspaces_rel"
    "(guards, guardsa) \<in> \<langle>clw_rel (iplane_rel lvivl_rel) \<times>\<^sub>r reach_optns_rel\<rangle>list_rel"
    "(ivli, set_of_lvivl ivli::'n rvec set) \<in> lvivl_rel"
    "(sctni, map_sctn eucl_of_list sctni::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    "(roi, roa) \<in> reach_optns_rel"
    "(\<lambda>x. nres_of (symstart x), symstarta) \<in> appr1e_rel \<rightarrow> \<langle>clw_rel appr_rel \<times>\<^sub>r clw_rel appr1e_rel\<rangle>nres_rel"
    "((), trap) \<in> ghost_rel"
    using lens symstart[THEN dres_nres_rel_nres_relD]
    by (auto simp: X0_def X1_def Sa_def P_def appr_rel_br set_rel_br
        br_chain o_def clw_rel_br  lv_rel_def sctn_rel_br ivl_rel_br set_of_lvivl_def
        halfspaces_rel_def list_set_rel_brp below_halfspaces_def ghost_relI
        br_rel_prod br_list_rel guardsa_def Id_br inter_rel_br plane_rel_br
        roa_def br_Times_Univ reach_options_rel_def
        split: sctn.splits
        intro!: brI list_allI clw_rel_appr1e_relI assms)

  have ivls: "((rl, ru), {eucl_of_list rl .. eucl_of_list ru::'n rvec}) \<in> lvivl_rel"
    "(dRi, set_of_lvivl' dRi::(('n rvec), 'n) vec set) \<in> \<langle>lvivl_rel\<rangle>default_rel UNIV"
    by (auto intro!: lvivl_relI lvivl_default_relI lens simp: lens set_of_lvivl_def set_of_ivl_def
        split: option.splits)

  from lens(1) have wd: "wd odo TYPE('n rvec)" by (auto simp: wd_def)
  from lens(1) have DIM_precond: "DIM_precond TYPE('n rvec) (D odo)"
    by (auto simp: D_def)
  have pmspec: "poincare_onto_from_in_ivl $ odo $ symstarta $ trap $ S $ guards $ ivl $ sctn $ ro $ XS0 $ IVL $ dIVL
  \<le> SPEC (\<lambda>b. b \<longrightarrow> poincare_mapsto odo (ivl \<inter> plane_of sctn) (XS0 - trap \<times> UNIV) S (Csafe odo - ivl \<inter> plane_of sctn)
                      (flow1_of_vec1 ` (IVL \<times> dIVL)))"
    if trapprop: "stable_on odo (Csafe odo - ivl \<inter> plane_of sctn) trap"
    for ivl sctn XS0 S guards ro IVL dIVL
    using poincare_onto_from_in_ivl[OF wd symstart_spec trapprop order_refl,
        of S guards ro XS0 IVL dIVL]
    by auto

  have odo_init: "(init_ode_ops True (carries_c1 (hd XS)) odo, odo) \<in> ode_ops_rel"
    by (auto simp: intro!: init_ode_ops)
  from nres_rel_trans2[OF
      pmspec
      poincare_onto_from_in_ivl_impl.refine[OF DIM_precond ncc odo_init spm(1-7) TRANSFER_refl spm(8) ivls]
      ] ret trapprop
  show ?thesis
    by (auto simp: solves_poincare_map_def nres_rel_def P_def X1_def)
qed

lemma solves_poincare_map'_ncc:
  "ncc_precond TYPE('n::enum rvec) \<Longrightarrow>
  ncc_precond TYPE('n vec1) \<Longrightarrow>
  solves_poincare_map' odo S guards ivli sctni roi XS (rl, ru) dRi \<Longrightarrow>
  (\<And>X. X \<in> set XS \<Longrightarrow> c1_info_invare CARD('n) X) \<Longrightarrow>
  length (ode_e odo) = CARD('n) \<Longrightarrow>
  length (normal sctni) = CARD('n) \<Longrightarrow>
  length (fst ivli) = CARD('n) \<Longrightarrow>
  length (snd ivli) = CARD('n) \<Longrightarrow>
  length (normal S) = CARD('n) \<Longrightarrow>
  length (rl) = CARD('n) \<Longrightarrow>
  length (ru) = CARD('n) \<Longrightarrow>
  lvivl'_invar (CARD('n)*CARD('n)) dRi \<Longrightarrow>
  (\<And>a xs b ba ro.
      (xs, ro) \<in> set guards \<Longrightarrow>
      ((a, b), ba) \<in> set xs \<Longrightarrow>
      length a = CARD('n) \<and>
      length b = CARD('n) \<and> length (normal ba) = CARD('n)) \<Longrightarrow>
  poincare_mapsto odo
   (set_of_lvivl ivli \<inter> plane_of (map_sctn eucl_of_list sctni)::'n rvec set)
   (c1_info_of_apprse XS) (below_halfspace (map_sctn eucl_of_list S))
   (Csafe odo - set_of_lvivl ivli \<inter> plane_of (map_sctn eucl_of_list sctni))
   (flow1_of_vec1 ` ({eucl_of_list rl .. eucl_of_list ru} \<times> set_of_lvivl' dRi))"
  by (rule solves_poincare_map_ncc[OF _ _ _
        empty_symstart_dres_nres_rel[unfolded empty_symstart_def op_empty_coll_def mk_coll_def]
         empty_symstart_flowsto,
    folded solves_poincare_map'_def, simplified])
    auto


lemma one_step_until_time_ivl_in_ivl_spec[le, refine_vcg]:
  "one_step_until_time_ivl_in_ivl odo (X0::'n::enum eucl1 set) t1 t2 R dR \<le> SPEC (\<lambda>b. b \<longrightarrow>
    (\<forall>(x0, d0) \<in> X0. {t1 .. t2} \<subseteq> existence_ivl0 odo x0 \<and>
      (\<forall>t \<in> {t1 .. t2}. (flow0 odo x0 t, Dflow odo x0 t o\<^sub>L d0) \<in> flow1_of_vec1 ` (R \<times> dR))))"
  if [simp]: "length (ode_e odo) = CARD('n::enum)"
proof -
  have wd[refine_vcg]: "wd odo TYPE((real, 'n) vec)" by (simp add: wd_def)
  show ?thesis
    unfolding one_step_until_time_ivl_in_ivl_def
    apply (refine_vcg, clarsimp_all)
    subgoal for X CX Y CY CY' x0 d0
        apply (drule bspec, assumption, clarsimp)
      subgoal for t
          apply (drule bspec[where x=t], force)
        by (simp add: subset_iff )
      done
    done
qed

theorem one_step_in_ivl_ncc:
  "t \<in> existence_ivl0 odo x0 \<and> (flow0 odo x0 t::'n rvec) \<in> R \<and> Dflow odo x0 t o\<^sub>L d0 \<in> dR"
  if ncc: "ncc_precond TYPE('n::enum rvec)" "ncc_precond TYPE('n vec1)"
   and t: "t \<in> {t0 .. t1}"
   and x0: "(x0, d0) \<in> c1_info_of_appre X"
   and invar: "c1_info_invare CARD('n) X"
   and R: "{eucl_of_list rl .. eucl_of_list ru} \<subseteq> R"
   and lens: "length rl = CARD('n)" "length ru = CARD('n)"
   and dRinvar: "lvivl'_invar (CARD('n)*CARD('n)) dRi"
   and dR: "blinfun_of_vmatrix ` set_of_lvivl' dRi \<subseteq> dR"
   and len_ode: "length (ode_e odo) = CARD('n)"
   and chk: "one_step_until_time_ivl_in_ivl_check odo X t0 t1 (rl, ru) dRi"
proof -
  have ivl: "((rl, ru), {eucl_of_list rl .. eucl_of_list ru::'n rvec}) \<in> \<langle>lv_rel\<rangle>ivl_rel"
    apply (rule lv_relivl_relI)
    using lens
    by auto
  from dRinvar have "lvivl'_invar DIM(((real, 'n) vec, 'n) vec) dRi" by simp
  note dRi = lvivl_default_relI[OF this]
  from len_ode have DIM_precond: "DIM_precond TYPE('n rvec) (D odo)"
    by (auto simp: D_def)
  have odo: "(init_ode_ops True (carries_c1 X) odo, odo) \<in> ode_ops_rel"
    by (auto intro!: init_ode_ops)
  from one_step_until_time_ivl_in_ivl_impl_refine[param_fo, OF DIM_precond ncc odo appr1e_relI[OF invar] IdI IdI ivl dRi, of t0 t1]
  have "nres_of (one_step_until_time_ivl_in_ivl_impl (D odo) (init_ode_ops True (carries_c1 X) odo) X t0 t1 (rl, ru) dRi)
    \<le> one_step_until_time_ivl_in_ivl odo (c1_info_of_appre X) t0 t1 {eucl_of_list rl::'n rvec..eucl_of_list ru} (set_of_lvivl' dRi)"
    by (auto simp: nres_rel_def)
  also note one_step_until_time_ivl_in_ivl_spec[OF len_ode order_refl]
  also have "one_step_until_time_ivl_in_ivl_impl (D odo) (init_ode_ops True (carries_c1 X) odo) X t0 t1 (rl, ru) dRi = dRETURN True"
    unfolding one_step_until_time_ivl_in_ivl_check_def[symmetric]
    using chk .
  finally show ?thesis
    using t R dR
    by (auto dest!: bspec[OF _ x0] bspec[where x=t] simp: vec1_of_flow1_def)
qed

subsection \<open>Poincare onto (from the outside)\<close>

theorem solves_poincare_map_onto_ncc:
  fixes sctni pos ivli ssc XS ph rl ru dRi CXS X0
  defines "P \<equiv> set_of_lvivl ivli \<inter> plane_of (map_sctn eucl_of_list sctni)"
  defines "X0 \<equiv> c1_info_of_apprse XS"
  defines "X1 \<equiv> flow1_of_vec1 ` ({eucl_of_list rl .. eucl_of_list ru} \<times> set_of_lvivl' dRi)"
  assumes ncc: "ncc_precond TYPE('n::enum rvec)" "ncc_precond TYPE('n vec1)"
  assumes ret: "solves_poincare_map_onto odo guards ivli sctni roi XS (rl, ru) dRi"
  assumes invar: "\<And>X. X \<in> set XS \<Longrightarrow> c1_info_invare CARD('n) X"
  assumes lens: "length (ode_e odo) = CARD('n)" "length (normal sctni) = CARD('n)" "length (fst ivli) = CARD('n)" "length (snd ivli) = CARD('n)"
    "length rl = CARD('n)" "length ru = CARD('n)"
     "lvivl'_invar (CARD('n)*CARD('n)) dRi"
    "\<And>a xs b ba ro. (xs, ro) \<in> set guards \<Longrightarrow> ((a, b), ba) \<in> set xs \<Longrightarrow> length a = CARD('n) \<and> length b = CARD('n) \<and> length (normal ba) = CARD('n)"
  shows "poincare_maps_onto odo P (X0::('n rvec \<times> _)set) X1"
proof -
  define guardsa::"('n rvec set \<times> unit) list"  where "guardsa \<equiv> map (\<lambda>(x, y). (\<Union>x\<in>set x. case x of (x, y) \<Rightarrow> (case x of (x, y) \<Rightarrow> set_of_ivl (eucl_of_list x, eucl_of_list y)) \<inter> plane_of (map_sctn eucl_of_list y), ())) guards"
  define roa where "roa = ()"
  have spm:
    "(XS, X0) \<in> clw_rel (appr1e_rel)"
    "(guards, guardsa) \<in> \<langle>clw_rel (iplane_rel lvivl_rel) \<times>\<^sub>r reach_optns_rel\<rangle>list_rel"
    "(ivli, set_of_lvivl ivli::'n rvec set) \<in> lvivl_rel"
    "(sctni, map_sctn eucl_of_list sctni::'n rvec sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
    "(roi, roa) \<in> reach_optns_rel"
    using lens
    by (auto simp: X0_def X1_def P_def appr_rel_br set_rel_br
        br_chain o_def clw_rel_br  lv_rel_def sctn_rel_br ivl_rel_br set_of_lvivl_def
        halfspaces_rel_def list_set_rel_brp below_halfspaces_def ghost_relI
        br_rel_prod br_list_rel guardsa_def Id_br inter_rel_br plane_rel_br
        reach_options_rel_def br_Times_Univ
        split: sctn.splits
        intro!: brI list_allI clw_rel_appr1e_relI assms)

  have ivls: "((rl, ru), {eucl_of_list rl .. eucl_of_list ru::'n rvec}) \<in> lvivl_rel"
    "(dRi, set_of_lvivl' dRi::(('n rvec), 'n) vec set) \<in> \<langle>lvivl_rel\<rangle>default_rel UNIV"
    by (auto intro!: lvivl_relI lvivl_default_relI lens simp: lens set_of_lvivl_def set_of_ivl_def
        split: option.splits)

  have pmspec: "poincare_onto_in_ivl odo guards ivl sctn ro XS0 IVL dIVL
  \<le> SPEC (\<lambda>b. b \<longrightarrow> poincare_mapsto odo (ivl \<inter> plane_of sctn) (XS0) UNIV (Csafe odo - ivl \<inter> plane_of sctn)
                      (flow1_of_vec1 ` (IVL \<times> dIVL)))"
    for ivl::"'n rvec set" and sctn XS0 guards ro IVL dIVL
    using poincare_onto_in_ivl[OF lens(1) order_refl, of guards ivl sctn ro XS0 IVL dIVL]
    by auto
  from lens(1) have DIM_precond: "DIM_precond TYPE('n rvec) (D odo)"
    by (auto simp: D_def)
  have odo: "(init_ode_ops True (carries_c1 (hd XS)) odo, odo) \<in> ode_ops_rel"
    by (auto intro!: init_ode_ops)
  from nres_rel_trans2[OF
      pmspec
      poincare_onto_in_ivl_impl.refine[OF DIM_precond ncc odo spm(1-5) ivls]
      ] ret
  show ?thesis
    by (auto simp: poincare_maps_onto_def solves_poincare_map_onto_def nres_rel_def P_def X1_def)
qed

end
end

subsection \<open>Executable definitions for ODE solver based on affine arithmetic\<close>

global_interpretation aform: approximate_sets aform_ops Joints aforms_rel optns for optns
  defines solves_poincare_map_aform = aform.solves_poincare_map
    and solves_poincare_map_aform' = aform.solves_poincare_map'
    and solves_poincare_map_onto_aform = aform.solves_poincare_map_onto
    and solves_one_step_until_time_aform = aform.one_step_until_time_ivl_in_ivl_check
    and solve_poincare_map_aform = aform.poincare_onto_from_impl
    and one_step_until_time_ivl_in_ivl_impl_aform = aform.one_step_until_time_ivl_in_ivl_impl
    and poincare_onto_from_in_ivl_impl_aform = aform.poincare_onto_from_in_ivl_impl
    and poincare_onto_in_ivl_impl_aform = aform.poincare_onto_in_ivl_impl
    and solve_poincare_onto_aform = aform.poincare_onto_impl
    and solve_one_step_until_time_aform = aform.one_step_until_time_ivl
    and one_step_until_time_impl_aform = aform.one_step_until_time_impl
    and op_image_fst_coll_nres_impl_aform = aform.op_image_fst_coll_nres_impl
    and poincare_onto_series_impl_aform = aform.poincare_onto_series_impl
    and poincare_start_on_impl_aform = aform.poincare_start_on_impl
    and leaves_halfspace_impl_aform = aform.leaves_halfspace_impl
    and approximate_sets_aform = aform.subset_spec_ivl_collc
    and subset_spec_plane_impl_aform = aform.subset_spec_plane_impl
    and disjoints_spec_impl_aform = aform.disjoints_spec_impl
    and partition_set_impl_aform = aform.partition_set_impl
    and fst_safe_coll_impl_aform = aform.fst_safe_coll_impl
    and choose_step1_impl_aform = aform.choose_step1_impl
    and ivl_rep_of_set_coll_impl_aform = aform.ivl_rep_of_set_coll_impl
    and ode_set_impl_aform = aform.ode_set_impl
    and mk_safe_impl_aform = aform.mk_safe_impl
    and subset_spec_ivlc_aform = aform.subset_spec_ivlc
    and sbelow_sctn_impl_aform = aform.sbelow_sctn_impl
    and below_sctn_impl_aform = aform.below_sctn_impl
    and split_under_threshold_impl_aform = aform.split_under_threshold_impl
    and do_intersection_coll_impl_aform = aform.do_intersection_coll_impl
    and partition_ivl_impl_aform = aform.partition_ivl_impl
    and mk_safe_coll_impl_aform = aform.mk_safe_coll_impl
    and choose_step_impl_aform = aform.choose_step_impl
    and reach_cont_impl_aform = aform.reach_cont_impl
    and vec1reps_impl_aform = aform.vec1reps_impl
    and ivl_rep_of_sets_impl_aform = aform.ivl_rep_of_sets_impl
    and ivl_rep_of_set_impl_aform = aform.ivl_rep_of_set_impl
    and ivls_of_sets_impl_aform = aform.ivls_of_sets_impl
    and tolerate_error_impl_aform = aform.tolerate_error_impl
    and tolerate_error1_impl_aform = aform.tolerate_error1_impl
    and pre_intersection_step_impl_aform = aform.pre_intersection_step_impl
    and split_spec_param1_impl_aform = aform.split_spec_param1_impl
    and do_intersection_impl_aform = aform.do_intersection_impl
    and resolve_step_impl_aform = aform.resolve_step_impl
    and euler_step_impl_aform = aform.euler_step_impl
    and rk2_step_impl_aform = aform.rk2_step_impl
    and op_eventually_within_sctn_impl_aform = aform.op_eventually_within_sctn_impl
    and solve_poincare_plane_impl_aform = aform.solve_poincare_plane_impl
    and cert_stepsize_impl_dres_aform = aform.cert_stepsize_impl_dres
    and step_adapt_time_impl_aform = aform.step_adapt_time_impl
    and inter_sctn1_impl_aform = aform.inter_sctn1_impl
    and step_split_impl_aform = aform.step_split_impl
    and intersects_impl_aform = aform.intersects_impl
    and above_sctn_impl_aform = aform.above_sctn_impl
    and nonzero_component_impl_aform = aform.nonzero_component_impl
    and P_iter_impl_aform = aform.P_iter_impl
    and partition_sets_impl_aform = aform.partition_sets_impl
    and reach_conts_impl_aform = aform.reach_conts_impl
    and subsets_iplane_coll_impl_aform = aform.subsets_iplane_coll_impl
    and reach_cont_symstart_impl_aform = aform.reach_cont_symstart_impl
    and subset_iplane_coll_impl_aform = aform.subset_iplane_coll_impl
    and symstart_coll_impl_aform = aform.symstart_coll_impl
    and subset_spec_ivls_clw_impl_aform = aform.subset_spec_ivls_clw_impl
    and poincare_onto2_impl_aform = aform.poincare_onto2_impl
    and poincare_onto_empty_impl_aform = aform.poincare_onto_empty_impl
    and resolve_ivlplanes_impl_aform = aform.resolve_ivlplanes_impl
    and empty_remainders_impl_aform = aform.empty_remainders_impl
    and adapt_stepsize_fa_aform = aform.adapt_stepsize_fa
    and split_spec_param1e_impl_aform = aform.split_spec_param1e_impl
    and setse_of_ivlse_impl_aform = aform.setse_of_ivlse_impl
    and ivlse_of_setse_impl_aform = aform.ivlse_of_setse_impl
    and choose_step1e_impl_aform = aform.choose_step1e_impl
    and vec1repse_impl_aform = aform.vec1repse_impl
    and scaleR2_rep1_impl_aform = aform.scaleR2_rep1_impl
    and list_of_appr1e_aform = aform.list_of_appr1e
    and list_of_appr1_aform = aform.list_of_appr1
    and nonzero_component_within_impl_aform = aform.nonzero_component_within_impl
    and approx_fas_impl_aform = aform.approx_slp_appr_impl
    and mig_set_impl_aform = aform.mig_set_impl
    and op_eucl_of_list_image_pad_aform = aform.op_eucl_of_list_image_pad
    and reach_cont_par_impl_aform = aform.reach_cont_par_impl
    and do_intersection_core_impl_aform = aform.do_intersection_core_impl
    and reduce_spec1e_impl_aform = aform.reduce_spec1e_impl
    and reduce_spec1_impl_aform = aform.reduce_spec1_impl
    and one_step_until_time_ivl_impl_aform = aform.one_step_until_time_ivl_impl
    and subset_spec1_collc_aform = aform.subset_spec1_collc
    and ivl_of_appr1_coll_impl_aform = aform.ivl_of_appr1_coll_impl
    and do_intersection_body_impl_aform = aform.do_intersection_body_impl
    and ode_slp_impl_aform = aform.ode_slp_impl
    and print_msg_impl_aform = aform.print_msg_impl
    and ode_e_impl_aform = aform.ode_e_impl
    and safe_form_impl_aform = aform.safe_form_impl
    and D_impl_aform = aform.D_impl
    and safe_set_appr_aform = aform.safe_set_appr
    and var_ode_ops_impl = aform.var_ode_ops_impl
    and start_stepsize_impl_aform = aform.start_stepsize_impl
    and poincare_slp_impl_aform = aform.poincare_slp_impl
    and rk2_param_impl_aform = aform.rk2_param_impl

  unfolding aform_approximate_sets_def[symmetric]
  by (rule aform_approximate_sets)

lemma aform_ncc[autoref_rules_raw]: "aform.ncc_precond TYPE('a::executable_euclidean_space)"
  using aform.appr_rel_nonempty
  by (auto simp: aform.ncc_precond_def aform.ncc_def aform.appr_rel_br br_def compact_Affine
    convex_Affine
      eucl_of_list_image_Joints)

fun parts::"nat\<Rightarrow>'a list\<Rightarrow>'a list list"
  where
    "parts n [] = []"
| "parts 0 xs = [xs]"
| "parts n xs = take n xs # parts n (drop n xs)"


lemma Joints_in_lv_rel_set_relD:
  "(Joints xs, X) \<in> \<langle>lv_rel\<rangle>set_rel \<Longrightarrow> X = Affine (eucl_of_list_aform xs)"
  apply (auto simp: )
   apply (subst eucl_of_list_image_Joints[symmetric])
  unfolding lv_rel_def set_rel_br
    apply (auto simp: br_def )
  using aform.length_set_of_appr apply auto[1]
  apply (subst (asm) eucl_of_list_image_Joints[symmetric])
  unfolding lv_rel_def set_rel_br
   apply (auto simp: br_def )
  using aform.length_set_of_appr apply auto[1]
  done

lemma ncc_precond: "aform.ncc_precond TYPE('a::executable_euclidean_space)"
  apply (auto simp: aform.ncc_precond_def aform.ncc_def aform.appr_rel_def)
  apply (auto simp: aforms_rel_def br_def)
  subgoal by (auto simp: compact_Affine dest!: Joints_in_lv_rel_set_relD)
  subgoal by (auto simp: convex_Affine dest!: Joints_in_lv_rel_set_relD)
  done

lemma fst_eucl_of_list_aform_map: "fst (eucl_of_list_aform (map (\<lambda>x. (fst x, asdf x)) x)) =
  fst (eucl_of_list_aform x)"
  by (auto simp: eucl_of_list_aform_def o_def)

lemma
  Affine_pdevs_of_list:\<comment> \<open>TODO: move!\<close>
  "Affine (fst x, pdevs_of_list (map snd (list_of_pdevs (snd x)))) = Affine x"
  by (auto simp: Affine_def valuate_def aform_val_def
      elim: pdevs_val_of_list_of_pdevs2[where X = "snd x"]
        pdevs_val_of_list_of_pdevs[where X = "snd x"])

lemmas one_step_in_ivl = aform.one_step_in_ivl_ncc[OF ncc_precond ncc_precond]
lemmas solves_poincare_map = aform.solves_poincare_map_ncc[OF ncc_precond ncc_precond]
lemmas solves_poincare_map' = aform.solves_poincare_map'_ncc[OF ncc_precond ncc_precond]
lemmas solves_poincare_map_onto = aform.solves_poincare_map_onto_ncc[OF ncc_precond ncc_precond]

end