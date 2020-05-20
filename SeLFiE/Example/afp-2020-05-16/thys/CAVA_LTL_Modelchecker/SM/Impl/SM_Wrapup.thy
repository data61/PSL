theory SM_Wrapup
imports SM_Ample_Impl Stuttering_Equivalence.PLTL
begin

  export_code ty_program ltlc_next_free checking SML

  definition "vars_of_aprop e \<equiv> udvars_of_exp e \<union> gvars_of_exp e"
  definition "vars_of_ltlc \<phi> \<equiv> \<Union> (vars_of_aprop ` atoms_ltlc \<phi>)"

  lemma test_aprop_vars_cong:
    assumes "e \<in> atoms_ltlc \<phi>"
    shows "test_aprop e (v |` vars_of_ltlc \<phi>) \<longleftrightarrow> test_aprop e v"
  proof -
    have 1: "eval_exp e (\<lparr> local_state.variables = Map.empty \<rparr>,
      \<lparr> global_state.variables = v |` vars_of_ltlc \<phi> \<rparr>) =
      eval_exp e (\<lparr> local_state.variables = Map.empty \<rparr>, \<lparr> global_state.variables = v \<rparr>)"
    proof (rule eval_dep_vars)
      show "gs_eq_on (vars_of_ltlc \<phi>) \<lparr> global_state.variables = v |` vars_of_ltlc \<phi> \<rparr>
        \<lparr> global_state.variables = v \<rparr>" by (simp add: eq_on_def)
      show "udvars_of_exp e \<subseteq> vars_of_ltlc \<phi>"
        using assms vars_of_aprop_def vars_of_ltlc_def by blast
      show "gvars_of_exp e \<subseteq> vars_of_ltlc \<phi>"
        using assms vars_of_aprop_def vars_of_ltlc_def by blast
    qed
    show ?thesis unfolding test_aprop_def 1 by rule
  qed

  context cprog
  begin

    sublocale ample_impl: sa "\<lparr> g_V = UNIV,
      g_E = ample_step_impl4_impl prog (comp_info_of prog) is_vis_var,
      g_V0 = {pid_init_gc_impl_impl prog (comp_info_of prog)},
      sa_L = pid_interp_gc_impl is_vis_var \<rparr>"
      for is_vis_var by unfold_locales auto

    theorem ample_reduction_correct: 
      assumes "ty_program prog"
      assumes NF: "ltlc_next_free \<phi>"
      shows "
        (Collect (SM_LTL.ap_accept prog) \<subseteq> language_ltlc \<phi>)
        \<longleftrightarrow>
        (Collect (ample_impl.accept (\<lambda>x. x\<in>vars_of_ltlc \<phi>)) \<subseteq> language_ltlc \<phi>)"
    proof safe
      interpret visible_prog prog "(\<lambda>x. x\<in>vars_of_ltlc \<phi>)"
        apply unfold_locales
        by fact
        
      {  
        fix w  
        assume 1: "(Collect (SM_LTL.ap_accept prog) \<subseteq> language_ltlc \<phi>)"
        and 2: "ample_impl.accept (\<lambda>x. x\<in>vars_of_ltlc \<phi>) w"
        note t2 = 2[unfolded pid_init_gc_impl_impl ample_step_impl4_impl]
        from impl4_accept_subset[OF t2] obtain w' where 
          WEQ: "w=interp_gs o w'" and "ref_accept prog w'" 
          unfolding lv_accept_conv
          by blast
        hence "ap_accept prog (sm_props o global_state.variables o w')" 
          (is "ap_accept prog ?ww")
          unfolding ap_accept_def interp_gs_def[abs_def]
          by auto
        with 1 have "?ww \<in> language_ltlc \<phi>" by blast
        moreover have "pw_eq_on (atoms_ltlc \<phi>) w ?ww"
          apply (simp add: WEQ)
          unfolding pw_eq_on_def interp_gs_def[abs_def]
          unfolding sm_props_def[abs_def]
          by (auto simp: test_aprop_vars_cong)
        ultimately show "w \<in> language_ltlc \<phi>" 
          unfolding language_ltlc_def
          by (auto simp: ltlc_eq_on)
      }
  
      {
        fix w
        assume 1: "Collect (ample_impl.accept (\<lambda>x. x\<in>vars_of_ltlc \<phi>)) \<subseteq> language_ltlc \<phi>"
        and 2: "SM_LTL.ap_accept prog w"
        from 2 obtain w' where 
          WEQ: "w = (sm_props o global_state.variables o w')" 
          and ACC: "ref_accept prog w'"
          unfolding ap_accept_def by auto
        with lv_accept_conv[THEN iffD2] have ACC': "lv.sa.accept (interp_gs o w')"
          by (auto simp: interp_gs_def[abs_def])
          
        from impl4_accept_stuttering[OF ACC'] obtain ww where 
          E2: "interp_gs o w' \<approx> ww" and "ample_impl.accept (\<lambda>x. x\<in>vars_of_ltlc \<phi>) ww"
          unfolding pid_init_gc_impl_impl ample_step_impl4_impl
          unfolding lv_accept_conv
          by blast
        hence L: "ww \<in> language_ltlc \<phi>" using 1 by blast
        
        have E1: "pw_eq_on (atoms_ltlc \<phi>) w (interp_gs o w')"
          apply (simp add: WEQ)
          unfolding pw_eq_on_def interp_gs_def[abs_def]
          unfolding sm_props_def[abs_def]
          by (auto simp: test_aprop_vars_cong)

        from ltlc_next_free_stutter_invariant[OF NF E2] L 
        have "interp_gs o w' \<in> language_ltlc \<phi>" by (auto simp: language_ltlc_def)
        with ltlc_eq_on[OF E1] show "w\<in>language_ltlc \<phi>" by (auto simp: language_ltlc_def)
      }
    qed

  end

end

