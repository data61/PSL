section \<open>Exploration of Deterministic Rabin Automata\<close>

theory DRA_Nodes
imports
  DFS_Framework.Reachable_Nodes
  DRA_Implement
begin

  definition dra_G :: "('label, 'state) dra \<Rightarrow> 'state graph_rec" where
    "dra_G A \<equiv> \<lparr> g_V = UNIV, g_E = E_of_succ (successors A), g_V0 = {initial A} \<rparr>"

  lemma dra_G_graph[simp]: "graph (dra_G A)" unfolding dra_G_def graph_def by simp
  lemma dra_G_reachable_nodes: "op_reachable (dra_G A) = nodes A"
  unfolding op_reachable_def dra_G_def graph_rec.simps E_of_succ_def
  proof safe
    show "p \<in> nodes A" if "(initial A, p) \<in> {(u, v). v \<in> successors A u}\<^sup>*" for p
      using that by induct auto
    show "(initial A, p) \<in> {(u, v). v \<in> successors A u}\<^sup>*" if "p \<in> nodes A" for p
      using that by (induct) (auto intro: rtrancl_into_rtrancl)
  qed

  context
  begin

    interpretation autoref_syn by this

    lemma dra_G_ahs: "dra_G A = \<lparr> g_V = UNIV, g_E = E_of_succ (\<lambda> p. CAST
      ((\<lambda> a. succ A a p ::: S) ` alphabet A ::: \<langle>S\<rangle> ahs_rel bhc)), g_V0 = {initial A} \<rparr>"
      unfolding dra_G_def CAST_def id_apply E_of_succ_def autoref_tag_defs by auto

    schematic_goal drai_Gi:
      notes map2set_to_list[autoref_ga_rules]
      fixes S :: "('statei \<times> 'state) set"
      assumes [autoref_ga_rules]: "is_bounded_hashcode S seq bhc"
      assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('statei) hms"
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S\<rangle> drai_dra_rel"
      shows "(?f :: ?'a, RETURN (dra_G A)) \<in> ?A"
      unfolding dra_G_ahs[where S = S and bhc = bhc] by (autoref_monadic (plain))
    concrete_definition drai_Gi uses drai_Gi
    (* TODO: why are term local.drai_Gi and term BA_Nodes.drai_Gi not the same *)
    lemma drai_Gi_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      shows "(DRA_Nodes.drai_Gi seq bhc hms, dra_G) \<in> \<langle>L, S\<rangle> drai_dra_rel \<rightarrow> \<langle>unit_rel, S\<rangle> g_impl_rel_ext"
      using drai_Gi.refine[THEN RETURN_nres_relD] assms unfolding autoref_tag_defs by blast

    schematic_goal dra_nodes:
      fixes S :: "('statei \<times> 'state) set"
      assumes [simp]: "finite ((g_E (dra_G A))\<^sup>* `` g_V0 (dra_G A))"
      assumes [autoref_ga_rules]: "is_bounded_hashcode S seq bhc"
      assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('statei) hms"
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S\<rangle> drai_dra_rel"
      shows "(?f :: ?'a, op_reachable (dra_G A)) \<in> ?R" by autoref
    concrete_definition dra_nodes uses dra_nodes
    lemma dra_nodes_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_PRECOND (finite (nodes A))"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      assumes "(Ai, A) \<in> \<langle>L, S\<rangle> drai_dra_rel"
      shows "(DRA_Nodes.dra_nodes seq bhc hms Ai,
        (OP nodes ::: \<langle>L, S\<rangle> drai_dra_rel \<rightarrow> \<langle>S\<rangle> ahs_rel bhc) $ A) \<in> \<langle>S\<rangle> ahs_rel bhc"
    proof -
      have "finite ((g_E (dra_G A))\<^sup>* `` g_V0 (dra_G A))"
        using assms(1) unfolding autoref_tag_defs dra_G_reachable_nodes[symmetric] by simp
      then show ?thesis using dra_nodes.refine assms
        unfolding autoref_tag_defs dra_G_reachable_nodes[symmetric] by blast
    qed

  end

end