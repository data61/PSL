section \<open>Code Generation for GBG Lasso Finding Algorithm\label{sec:gbg_code}\<close>
theory Gabow_GBG_Code
imports
  Gabow_GBG 
  Gabow_Skeleton_Code 
  CAVA_Automata.Automata_Impl
  Find_Path_Impl
  CAVA_Base.CAVA_Code_Target
begin

section \<open>Autoref Setup\<close>

locale impl_lasso_loc = igb_fr_graph G 
  + fr_graph_impl_loc "\<langle>mrel,Id\<rangle>igbg_impl_rel_eext" G_impl G
  for mrel and G_impl and G :: "('q::hashable,'more) igb_graph_rec_scheme"
begin

  lemma locale_this: "impl_lasso_loc mrel G_impl G"
    by unfold_locales

  context begin interpretation autoref_syn .

    lemma [autoref_op_pat]: 
      "goinitial_impl \<equiv> OP goinitial_impl"
      "ginitial_impl \<equiv> OP ginitial_impl"
      "gpath_is_empty_impl \<equiv> OP gpath_is_empty_impl"
      "gselect_edge_impl \<equiv> OP gselect_edge_impl"
      "gis_on_stack_impl \<equiv> OP gis_on_stack_impl"
      "gcollapse_impl \<equiv> OP gcollapse_impl"
      "last_is_acc_impl \<equiv> OP last_is_acc_impl"
      "ce_impl \<equiv> OP ce_impl"
      "gis_done_impl \<equiv> OP gis_done_impl"
      "gpush_impl \<equiv> OP gpush_impl"
      "gpop_impl \<equiv> OP gpop_impl"
      "goBrk_impl \<equiv> OP goBrk_impl" 
      "gto_outer_impl \<equiv> OP gto_outer_impl"
      "go_is_done_impl \<equiv> OP go_is_done_impl"
      "is_done_oimpl \<equiv> OP is_done_oimpl"
      "go_is_no_brk_impl \<equiv> OP go_is_no_brk_impl"
      by simp_all
  end

  abbreviation "gGSi_rel \<equiv> \<langle>\<langle>nat_rel\<rangle>bs_set_rel\<rangle>as_rel \<times>\<^sub>r GSi_rel"
  abbreviation (in -) "ce_rel \<equiv> \<langle>\<langle>Id\<rangle>fun_set_rel \<times>\<^sub>r \<langle>Id\<rangle>fun_set_rel\<rangle>option_rel"
  abbreviation "goGSi_rel \<equiv> ce_rel \<times>\<^sub>r oGSi_rel"
end

section \<open>Automatic Refinement\<close>

context impl_lasso_loc
begin

  schematic_goal goinitial_code_aux: "(?c,goinitial_impl)\<in>goGSi_rel"
    unfolding goinitial_impl_def[abs_def]
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) goinitial_code 
    uses impl_lasso_loc.goinitial_code_aux
  lemmas [autoref_rules] = goinitial_code.refine[OF locale_this]


  term ginitial_impl
  schematic_goal ginitial_code_aux: 
    "(?c,ginitial_impl)\<in>node_rel \<rightarrow> goGSi_rel \<rightarrow> gGSi_rel"
    unfolding ginitial_impl_def[abs_def] initial_impl_def GS_initial_impl_def
      (* TODO: Declare autoref-rule for initial*)
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) ginitial_code uses impl_lasso_loc.ginitial_code_aux
  lemmas [autoref_rules] = ginitial_code.refine[OF locale_this]

  schematic_goal gpath_is_empty_code_aux: 
    "(?c,gpath_is_empty_impl)\<in>gGSi_rel\<rightarrow>bool_rel"
    unfolding gpath_is_empty_impl_def[abs_def] path_is_empty_impl_def
      (* TODO: Declare autoref-rule for path_is_empty*)
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) gpath_is_empty_code 
    uses impl_lasso_loc.gpath_is_empty_code_aux
  lemmas [autoref_rules] = gpath_is_empty_code.refine[OF locale_this]

  term goBrk
  schematic_goal goBrk_code_aux: "(?c,goBrk_impl)\<in>goGSi_rel\<rightarrow>ce_rel"
    unfolding goBrk_impl_def[abs_def] goBrk_impl_def
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) goBrk_code uses impl_lasso_loc.goBrk_code_aux
  lemmas [autoref_rules] = goBrk_code.refine[OF locale_this]
  thm autoref_itype(1)

  term gto_outer_impl
  schematic_goal gto_outer_code_aux: 
    "(?c,gto_outer_impl)\<in>ce_rel \<rightarrow> gGSi_rel\<rightarrow>goGSi_rel"
    unfolding gto_outer_impl_def[abs_def] gto_outer_impl_def
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) gto_outer_code 
    uses impl_lasso_loc.gto_outer_code_aux
  lemmas [autoref_rules] = gto_outer_code.refine[OF locale_this]

  term go_is_done_impl
  schematic_goal go_is_done_code_aux: 
    "(?c,go_is_done_impl)\<in>node_rel \<rightarrow> goGSi_rel \<rightarrow> bool_rel"
    unfolding go_is_done_impl_def[abs_def] is_done_oimpl_def
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) go_is_done_code 
    uses impl_lasso_loc.go_is_done_code_aux
  lemmas [autoref_rules] = go_is_done_code.refine[OF locale_this]

  schematic_goal go_is_no_brk_code_aux: 
    "(?c,go_is_no_brk_impl)\<in>goGSi_rel\<rightarrow>bool_rel"
    unfolding go_is_no_brk_impl_def[abs_def] go_is_no_brk_impl_def
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) go_is_no_brk_code 
    uses impl_lasso_loc.go_is_no_brk_code_aux
  lemmas [autoref_rules] = go_is_no_brk_code.refine[OF locale_this]

(*
  schematic_lemma XXX_code_aux: "(?c,XXX_impl)\<in>goGSi_rel\<rightarrow>ce_rel"
    unfolding XXX_impl_def[abs_def] XXX_impl_def
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) XXX_code uses impl_lasso_loc.XXX_code_aux
  lemmas [autoref_rules] = XXX_code.refine[OF locale_this]
*)

  schematic_goal gselect_edge_code_aux: "(?c,gselect_edge_impl)
    \<in> gGSi_rel \<rightarrow> \<langle>\<langle>node_rel\<rangle>option_rel \<times>\<^sub>r gGSi_rel\<rangle>nres_rel"
    unfolding gselect_edge_impl_def[abs_def]
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) gselect_edge_code 
    uses impl_lasso_loc.gselect_edge_code_aux
  lemmas [autoref_rules] = gselect_edge_code.refine[OF locale_this]

  term gis_on_stack_impl
  schematic_goal gis_on_stack_code_aux: 
    "(?c,gis_on_stack_impl)\<in>node_rel \<rightarrow> gGSi_rel \<rightarrow> bool_rel"
    unfolding gis_on_stack_impl_def[abs_def] is_on_stack_impl_def[abs_def] 
      GS.is_on_stack_impl_def[abs_def]
      (* TODO: Declare autoref-rule for is_on_stack*)
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) gis_on_stack_code 
    uses impl_lasso_loc.gis_on_stack_code_aux
  lemmas [autoref_rules] = gis_on_stack_code.refine[OF locale_this]

  term gcollapse_impl
  schematic_goal gcollapse_code_aux: "(?c,gcollapse_impl)\<in>node_rel \<rightarrow> gGSi_rel 
    \<rightarrow> \<langle>gGSi_rel\<rangle>nres_rel"
    unfolding gcollapse_impl_def[abs_def]
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) gcollapse_code 
    uses impl_lasso_loc.gcollapse_code_aux
  lemmas [autoref_rules] = gcollapse_code.refine[OF locale_this]

  schematic_goal last_is_acc_code_aux: 
    "(?c,last_is_acc_impl)\<in>gGSi_rel\<rightarrow>\<langle>bool_rel\<rangle>nres_rel"
    unfolding last_is_acc_impl_def[abs_def]
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) last_is_acc_code 
    uses impl_lasso_loc.last_is_acc_code_aux
  lemmas [autoref_rules] = last_is_acc_code.refine[OF locale_this]

  schematic_goal ce_code_aux: "(?c,ce_impl)
    \<in>gGSi_rel\<rightarrow>\<langle>ce_rel \<times>\<^sub>r gGSi_rel\<rangle>nres_rel"
    unfolding ce_impl_def[abs_def] on_stack_less_def[abs_def] 
      on_stack_ge_def[abs_def]
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) ce_code uses impl_lasso_loc.ce_code_aux
  lemmas [autoref_rules] = ce_code.refine[OF locale_this]

  schematic_goal gis_done_code_aux: 
    "(?c,gis_done_impl)\<in>node_rel\<rightarrow>gGSi_rel\<rightarrow>bool_rel"
    unfolding gis_done_impl_def[abs_def] is_done_impl_def GS.is_done_impl_def
    (* TODO: Autoref rule for is_done *)
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) gis_done_code uses impl_lasso_loc.gis_done_code_aux
  lemmas [autoref_rules] = gis_done_code.refine[OF locale_this]

  schematic_goal gpush_code_aux: 
    "(?c,gpush_impl)\<in>node_rel \<rightarrow> gGSi_rel\<rightarrow>gGSi_rel"
    unfolding gpush_impl_def[abs_def]
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) gpush_code uses impl_lasso_loc.gpush_code_aux
  lemmas [autoref_rules] = gpush_code.refine[OF locale_this]

  schematic_goal gpop_code_aux: "(?c,gpop_impl)\<in>gGSi_rel\<rightarrow>\<langle>gGSi_rel\<rangle>nres_rel"
    unfolding gpop_impl_def[abs_def]
    using [[autoref_trace_failed_id]]
    by (autoref (trace,keep_goal))
  concrete_definition (in -) gpop_code uses impl_lasso_loc.gpop_code_aux
  lemmas [autoref_rules] = gpop_code.refine[OF locale_this]




  schematic_goal find_ce_code_aux: "(?c,find_ce_impl)\<in>\<langle>ce_rel\<rangle>nres_rel"
    unfolding find_ce_impl_def[abs_def] 
    using [[autoref_trace_failed_id]]
    apply (autoref (trace,keep_goal))
    done
  concrete_definition (in -) find_ce_code 
    uses impl_lasso_loc.find_ce_code_aux
  lemmas [autoref_rules] = find_ce_code.refine[OF locale_this]

  schematic_goal find_ce_tr_aux: "RETURN ?c \<le> find_ce_code G_impl"
    unfolding
      find_ce_code_def
      ginitial_code_def
      gpath_is_empty_code_def
      gselect_edge_code_def
      gis_on_stack_code_def
      gcollapse_code_def
      last_is_acc_code_def
      ce_code_def
      gis_done_code_def
      gpush_code_def
      gpop_code_def
    apply refine_transfer
    done
  concrete_definition (in -) find_ce_tr for G_impl
    uses impl_lasso_loc.find_ce_tr_aux
  lemmas [refine_transfer] = find_ce_tr.refine[OF locale_this]

  context begin interpretation autoref_syn .
    lemma [autoref_op_pat]: 
      "find_ce_spec \<equiv> OP find_ce_spec"
      by auto
  end
  
  theorem find_ce_autoref[autoref_rules]:
    \<comment> \<open>Main Correctness theorem (inside locale)\<close>
    shows "(find_ce_code G_impl, find_ce_spec) \<in> \<langle>ce_rel\<rangle>nres_rel"
  proof -
    note find_ce_code.refine[OF locale_this, THEN nres_relD]
    also note find_ce_impl_refine
    also note find_ce_refine
    also note find_ce_correct
    finally show ?thesis by (auto intro: nres_relI)
  qed
  
end

context impl_lasso_loc
begin

  context begin interpretation autoref_syn .

    lemma [autoref_op_pat]: 
      "reconstruct_reach \<equiv> OP reconstruct_reach"
      "reconstruct_lasso \<equiv> OP reconstruct_lasso"
      by auto
  end

  schematic_goal reconstruct_reach_code_aux:
    shows "(?c, reconstruct_reach)\<in>\<langle>node_rel\<rangle>fun_set_rel \<rightarrow>
    \<langle>node_rel\<rangle>fun_set_rel \<rightarrow>
    \<langle>\<langle>node_rel\<rangle>list_rel \<times>\<^sub>r node_rel\<rangle>nres_rel"
    unfolding reconstruct_lasso_def[abs_def] reconstruct_reach_def[abs_def]
    using [[autoref_trace_failed_id]]

    apply (autoref (keep_goal, trace))
    done
  concrete_definition (in -) reconstruct_reach_code 
    uses impl_lasso_loc.reconstruct_reach_code_aux
  lemmas [autoref_rules] = reconstruct_reach_code.refine[OF locale_this]


  schematic_goal reconstruct_lasso_code_aux:
    shows "(?c, reconstruct_lasso)\<in>\<langle>node_rel\<rangle>fun_set_rel \<rightarrow>
    \<langle>node_rel\<rangle>fun_set_rel \<rightarrow>
    \<langle>\<langle>node_rel\<rangle>list_rel \<times>\<^sub>r \<langle>node_rel\<rangle>list_rel\<rangle>nres_rel"
    unfolding reconstruct_lasso_def[abs_def]
    using [[autoref_trace_failed_id]]

    apply (autoref (keep_goal, trace))
    done
  concrete_definition (in -) reconstruct_lasso_code 
    uses impl_lasso_loc.reconstruct_lasso_code_aux
  lemmas [autoref_rules] = reconstruct_lasso_code.refine[OF locale_this]

  schematic_goal reconstruct_lasso_tr_aux: 
    "RETURN ?c \<le> reconstruct_lasso_code G_impl Vr Vl"
    unfolding reconstruct_lasso_code_def reconstruct_reach_code_def 
    apply (refine_transfer (post))
    done
  concrete_definition (in -) reconstruct_lasso_tr for G_impl
    uses impl_lasso_loc.reconstruct_lasso_tr_aux
  lemmas [refine_transfer] = reconstruct_lasso_tr.refine[OF locale_this]
  
  schematic_goal find_lasso_code_aux:
    shows "(?c::?'c, find_lasso)\<in>?R"
    unfolding find_lasso_def[abs_def]
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal, trace))
    done
  concrete_definition (in -) find_lasso_code 
    uses impl_lasso_loc.find_lasso_code_aux
  lemmas [autoref_rules] = find_lasso_code.refine[OF locale_this]

  schematic_goal find_lasso_tr_aux: 
    "RETURN ?c \<le> find_lasso_code G_impl"
    unfolding find_lasso_code_def
    apply (refine_transfer (post))
    done
  concrete_definition (in -) find_lasso_tr for G_impl
    uses impl_lasso_loc.find_lasso_tr_aux
  lemmas [refine_transfer] = find_lasso_tr.refine[OF locale_this]

end

export_code find_lasso_tr checking SML

section \<open>Main Correctness Theorem\<close>

abbreviation fl_rel :: "(_ \<times> ('a list \<times> 'b list) option) set" where  
  "fl_rel \<equiv> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel\<rangle>Relators.option_rel"

theorem find_lasso_tr_correct:
  \<comment> \<open>Correctness theorem for the constant we extracted to SML\<close>
  fixes Re
  assumes A: "(G_impl,G)\<in>igbg_impl_rel_ext Re Id"
  assumes B: "igb_fr_graph G"
  shows "RETURN (find_lasso_tr G_impl) 
  \<le> \<Down>fl_rel (igb_graph.find_lasso_spec G)"
proof -
  from B interpret igb_fr_graph G .

  have I: "impl_lasso_loc Re G_impl G"
    by unfold_locales fact
  then interpret impl_lasso_loc Re G_impl G .

  note find_lasso_tr.refine[OF I]
  also note find_lasso_code.refine[OF I, THEN nres_relD]
  also note find_lasso_correct
  finally show ?thesis .
qed

section \<open>Autoref Setup for \<open>igb_graph.find_lasso_spec\<close>\<close>
text \<open>Setup for Autoref, such that \<open>igb_graph.find_lasso_spec\<close> 
  can be used\<close>
definition [simp]: "op_find_lasso_spec \<equiv> igb_graph.find_lasso_spec"

context begin interpretation autoref_syn .

lemma [autoref_op_pat]: "igb_graph.find_lasso_spec \<equiv> op_find_lasso_spec"
  by simp

term op_find_lasso_spec

lemma [autoref_itype]: 
  "op_find_lasso_spec 
    ::\<^sub>i i_igbg Ie I \<rightarrow>\<^sub>i \<langle>\<langle>\<langle>\<langle>I\<rangle>\<^sub>ii_list, \<langle>I\<rangle>\<^sub>ii_list\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_option\<rangle>\<^sub>ii_nres"
  by simp

lemma find_lasso_spec_autoref[autoref_rules_raw]:
  fixes Re
  assumes "SIDE_PRECOND (igb_fr_graph G)"
  assumes "PREFER_id R"
  assumes "(G_impl,G)\<in>igbg_impl_rel_ext Re R"
  shows "(RETURN (find_lasso_tr G_impl), 
    (OP op_find_lasso_spec 
      ::: igbg_impl_rel_ext Re R \<rightarrow> \<langle>fl_rel\<rangle>nres_rel)$G) \<in> \<langle>fl_rel\<rangle>nres_rel"
  using find_lasso_tr_correct assms
  apply (fastforce intro!: nres_relI)
  done

end
    

end
