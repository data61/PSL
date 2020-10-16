section \<open>Set of Reachable Nodes\<close>
theory Reachable_Nodes
imports "../DFS_Framework"
  CAVA_Automata.Digraph_Impl
  "../Misc/Impl_Rev_Array_Stack"
begin
text \<open>
  This theory provides a re-usable algorithm to compute the set of reachable
  nodes in a graph.
\<close>

subsection \<open>Preliminaries\<close>
lemma gen_obtain_finite_set:
  assumes F: "finite S"
  assumes E: "(e,{})\<in>\<langle>R\<rangle>Rs"
  assumes I: "(i,insert)\<in>R\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs"
  assumes EE: "\<And>x. x\<in>S \<Longrightarrow> \<exists>xi. (xi,x)\<in>R"
  shows "\<exists>Si. (Si,S)\<in>\<langle>R\<rangle>Rs"
proof -
  define S' where "S' = S"

  have "S\<subseteq>S'" by (simp add: S'_def)
  from F this show "(\<exists>Si. (Si,S)\<in>\<langle>R\<rangle>Rs)"
  proof (induction)
    case empty thus ?case  
      using E by (blast)
  next
    case (insert x S)
    then obtain xi Si where 1: "(Si,S)\<in>\<langle>R\<rangle>Rs" and 2: "(xi,x)\<in>R" 
      using EE unfolding S'_def by blast
    from I[THEN fun_relD, OF 2, THEN fun_relD, OF 1] show ?case ..
  qed
qed        


lemma obtain_finite_ahs: "finite S \<Longrightarrow> \<exists>x. (x,S)\<in>\<langle>Id\<rangle>dflt_ahs_rel"
  apply (erule gen_obtain_finite_set)
  apply autoref
  apply autoref
  by blast



subsection \<open>Framework Instantiation\<close>
definition "unit_parametrization \<equiv> dflt_parametrization (\<lambda>_. ()) (RETURN ())"

lemmas unit_parametrization_simp[simp, DFS_code_unfold] = 
  dflt_parametrization_simp[mk_record_simp, OF, OF unit_parametrization_def]

interpretation unit_dfs: param_DFS_defs where param=unit_parametrization for G .

locale unit_DFS = param_DFS G unit_parametrization for G :: "('v, 'more) graph_rec_scheme"
begin
  sublocale DFS G unit_parametrization
    by unfold_locales simp_all
end

lemma unit_DFSI[Pure.intro?, intro?]: 
  assumes "fb_graph G" 
  shows "unit_DFS G"
proof -
  interpret fb_graph G by fact
  show ?thesis by unfold_locales
qed

(* Find Reachable Nodes *)
definition "find_reachable G \<equiv> do {
  ASSERT (fb_graph G);
  s \<leftarrow> unit_dfs.it_dfs TYPE('a) G;
  RETURN (dom (discovered s))
}"

definition "find_reachableT G \<equiv> do {
  ASSERT (fb_graph G);
  s \<leftarrow> unit_dfs.it_dfsT TYPE('a) G;
  RETURN (dom (discovered s))
}"

subsection \<open>Correctness\<close>

context unit_DFS begin
  lemma find_reachable_correct: "find_reachable G \<le> SPEC (\<lambda>r. r = reachable)"
    unfolding find_reachable_def
    apply (refine_vcg order_trans[OF it_dfs_correct])
    apply unfold_locales
    apply clarify
    apply (drule (1) DFS_invar.nc_discovered_eq_reachable)
    by auto

  lemma find_reachableT_correct: 
    "finite reachable \<Longrightarrow> find_reachableT G \<le> SPEC (\<lambda>r. r = reachable)"
    unfolding find_reachableT_def
    apply (refine_vcg order_trans[OF it_dfsT_correct])
    apply unfold_locales
    apply clarify
    apply (drule (1) DFS_invar.nc_discovered_eq_reachable)
    by auto
end

context unit_DFS begin
  (* Derive the implementation *)
  sublocale simple_impl G unit_parametrization unit_parametrization unit_rel 
    apply unfold_locales
    apply (clarsimp simp: simple_state_rel_def) []
    by auto

  lemmas impl_refine = simple_tailrecT_refine simple_tailrec_refine simple_rec_refine
end


interpretation unit_simple_impl: 
  simple_impl_defs G unit_parametrization unit_parametrization
  for G .

term unit_simple_impl.tailrec_impl term unit_simple_impl.rec_impl

definition [DFS_code_unfold]: "find_reachable_impl G \<equiv> do {
  ASSERT (fb_graph G);
  s \<leftarrow> unit_simple_impl.tailrec_impl TYPE('a) G;
  RETURN (simple_state.visited s)
}"

definition [DFS_code_unfold]: "find_reachable_implT G \<equiv> do {
  ASSERT (fb_graph G);
  s \<leftarrow> unit_simple_impl.tailrec_implT TYPE('a) G;
  RETURN (simple_state.visited s)
}"

definition [DFS_code_unfold]: "find_reachable_rec_impl G \<equiv> do {
  ASSERT (fb_graph G);
  s \<leftarrow> unit_simple_impl.rec_impl TYPE('a) G;
  RETURN (visited s)
}"


lemma find_reachable_impl_refine: 
  "find_reachable_impl G \<le> \<Down>Id (find_reachable G)"
  unfolding find_reachable_impl_def find_reachable_def
  apply (refine_vcg unit_DFS.impl_refine)
  apply (simp_all add: unit_DFSI simple_state_rel_def)
  done

lemma find_reachable_implT_refine: 
  "find_reachable_implT G \<le> \<Down>Id (find_reachableT G)"
  unfolding find_reachable_implT_def find_reachableT_def
  apply (refine_vcg unit_DFS.impl_refine)
  apply (simp_all add: unit_DFSI simple_state_rel_def)
  done
  
lemma find_reachable_rec_impl_refine: 
  "find_reachable_rec_impl G \<le> \<Down>Id (find_reachable G)"
  unfolding find_reachable_rec_impl_def find_reachable_def
  apply (refine_vcg unit_DFS.impl_refine)
  apply (simp_all add: unit_DFSI simple_state_rel_def)
  done

subsection \<open>Synthesis of Executable Implementation\<close>
(* Autoref *)
schematic_goal find_reachable_impl:
  defines "V \<equiv> Id :: ('v \<times> 'v::hashable) set"
  assumes [unfolded V_def,autoref_rules]: 
    "(Gi, G) \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext"
  notes [unfolded V_def,autoref_tyrel] = 
    TYRELI[where R="\<langle>V\<rangle>dflt_ahs_rel"]
    TYRELI[where R="\<langle>V \<times>\<^sub>r \<langle>V\<rangle>list_set_rel\<rangle>ras_rel"]
  shows "nres_of (?c::?'c dres) \<le>\<Down>?R (find_reachable_impl G)"
  unfolding if_cancel DFS_code_unfold ssnos_unfolds
  using [[autoref_trace_failed_id, goals_limit=1]]
  apply (autoref_monadic (trace))
  done
concrete_definition find_reachable_code uses find_reachable_impl
export_code find_reachable_code checking SML

lemma find_reachable_code_correct:
  assumes 1: "fb_graph G"
  assumes 2: "(Gi, G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
  assumes 4: "find_reachable_code Gi = dRETURN r"
  shows "(r, (g_E G)\<^sup>* `` g_V0 G)\<in>\<langle>Id\<rangle>dflt_ahs_rel"
proof -
  from 1 interpret unit_DFS by rule
  note find_reachable_code.refine[OF 2]
  also note find_reachable_impl_refine
  also note find_reachable_correct
  finally show ?thesis using 1 4 by (auto simp: RETURN_RES_refine_iff)
qed


schematic_goal find_reachable_implT:
  fixes V :: "('vi\<times>'v) set"
  assumes [autoref_ga_rules]: "is_bounded_hashcode V eq bhc"
  assumes [autoref_rules]: "(eq,(=)) \<in> V \<rightarrow> V \<rightarrow> bool_rel"
  assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE ('vi) sz"
  assumes [autoref_rules]: 
    "(Gi, G) \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext"
  notes [autoref_tyrel] = 
    TYRELI[where R="\<langle>V\<rangle>ahs_rel bhc"]
    TYRELI[where R="\<langle>V \<times>\<^sub>r \<langle>V\<rangle>list_set_rel\<rangle>ras_rel"]
  shows "RETURN (?c::?'c) \<le>\<Down>?R (find_reachable_implT G)"
  unfolding if_cancel DFS_code_unfold ssnos_unfolds
  using [[autoref_trace_failed_id, goals_limit=1]]
  apply (autoref_monadic (plain,trace))
  done
concrete_definition find_reachable_codeT for eq bhc sz Gi 
  uses find_reachable_implT
export_code find_reachable_codeT checking SML

lemma find_reachable_codeT_correct:
  fixes V :: "('vi\<times>'v) set"
  assumes G: "graph G"
  assumes FR: "finite ((g_E G)\<^sup>* `` g_V0 G)"
  assumes BHC: "is_bounded_hashcode V eq bhc"
  assumes EQ: "(eq,(=)) \<in> V \<rightarrow> V \<rightarrow> bool_rel"
  assumes VDS: "is_valid_def_hm_size TYPE ('vi) sz"
  assumes 2: "(Gi, G) \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext"
  shows "(find_reachable_codeT eq bhc sz Gi, (g_E G)\<^sup>* `` g_V0 G)\<in>\<langle>V\<rangle>ahs_rel bhc"
proof -
  from G interpret graph by this
  from FR interpret fb_graph using fb_graphI_fr by simp
  interpret unit_DFS by unfold_locales
  note find_reachable_codeT.refine[OF BHC EQ VDS 2]
  also note find_reachable_implT_refine
  also note find_reachableT_correct
  finally show ?thesis using FR by (auto simp: RETURN_RES_refine_iff)
qed


definition all_unit_rel :: "(unit \<times> 'a) set" where "all_unit_rel \<equiv> UNIV"

lemma all_unit_refine[simp]: 
  "((),x)\<in>all_unit_rel" unfolding all_unit_rel_def by simp

definition unit_list_rel :: "('c\<times>'a) set \<Rightarrow> (unit \<times> 'a list) set"
  where [to_relAPP]: "unit_list_rel R \<equiv> UNIV"

lemma unit_list_rel_refine[simp]: "((),y)\<in>\<langle>R\<rangle>unit_list_rel"
  unfolding unit_list_rel_def by auto

lemmas [autoref_rel_intf] = REL_INTFI[of unit_list_rel i_list]

lemma [autoref_rules]:
  "((),[])\<in>\<langle>R\<rangle>unit_list_rel"
  "(\<lambda>_. (),tl)\<in>\<langle>R\<rangle>unit_list_rel\<rightarrow>\<langle>R\<rangle>unit_list_rel"
  "(\<lambda>_ _. (),(#))\<in>R \<rightarrow> \<langle>R\<rangle>unit_list_rel\<rightarrow>\<langle>R\<rangle>unit_list_rel"
  by auto



schematic_goal find_reachable_rec_impl:
  defines "V \<equiv> Id :: ('v \<times> 'v::hashable) set"
  assumes [unfolded V_def,autoref_rules]: 
    "(Gi, G) \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext"
  notes [unfolded V_def,autoref_tyrel] = 
    TYRELI[where R="\<langle>V\<rangle>dflt_ahs_rel"]
  shows "nres_of (?c::?'c dres) \<le>\<Down>?R (find_reachable_rec_impl G)"
  unfolding unit_simple_impl.ssns_unfolds 
    DFS_code_unfold if_cancel if_False option.case
  using [[autoref_trace_failed_id, goals_limit=1]]
  apply (autoref_monadic (trace))
  done
concrete_definition find_reachable_rec_code uses find_reachable_rec_impl
prepare_code_thms find_reachable_rec_code_def
export_code find_reachable_rec_code checking SML

lemma find_reachable_rec_code_correct:
  assumes 1: "fb_graph G"
  assumes 2: "(Gi, G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
  assumes 4: "find_reachable_rec_code Gi = dRETURN r"
  shows "(r, (g_E G)\<^sup>* `` g_V0 G)\<in>\<langle>Id\<rangle>dflt_ahs_rel"
proof -
  from 1 interpret unit_DFS by rule
  note find_reachable_rec_code.refine[OF 2]
  also note find_reachable_rec_impl_refine
  also note find_reachable_correct
  finally show ?thesis using 1 4 by (auto simp: RETURN_RES_refine_iff)
qed

definition [simp]: "op_reachable G \<equiv> (g_E G)\<^sup>* `` g_V0 G"
lemmas [autoref_op_pat] = op_reachable_def[symmetric]

context begin interpretation autoref_syn .

lemma autoref_op_reachable[autoref_rules]:
  fixes V :: "('vi\<times>'v) set"
  assumes G: "SIDE_PRECOND (graph G)"
  assumes FR: "SIDE_PRECOND (finite ((g_E G)\<^sup>* `` g_V0 G))"
  assumes BHC: "SIDE_GEN_ALGO (is_bounded_hashcode V eq bhc)"
  assumes EQ: "GEN_OP eq (=) (V \<rightarrow> V \<rightarrow> bool_rel)"
  assumes VDS: "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE ('vi) sz)"
  assumes 2: "(Gi, G) \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext"
  shows "(find_reachable_codeT eq bhc sz Gi,
    (OP op_reachable ::: \<langle>Rm, V\<rangle>g_impl_rel_ext \<rightarrow> \<langle>V\<rangle>ahs_rel bhc)$G)\<in>\<langle>V\<rangle>ahs_rel bhc"
  using assms
  by (simp add: find_reachable_codeT_correct)  

end

subsection \<open>Conclusions\<close>
text \<open>
  We have defined an efficient DFS-based implementation for @{const op_reachable},
  and declared it to Autoref.
\<close>


end

