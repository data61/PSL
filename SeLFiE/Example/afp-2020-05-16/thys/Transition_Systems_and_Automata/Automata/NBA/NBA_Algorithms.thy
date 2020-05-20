section \<open>Algorithms on Nondeterministic Büchi Automata\<close>

theory NBA_Algorithms
imports
  NBA_Graphs
  NBA_Implement
  DFS_Framework.Reachable_Nodes
  Gabow_SCC.Gabow_GBG_Code
begin

  subsection \<open>Miscellaneous Amendments\<close>

  lemma (in igb_fr_graph) acc_run_lasso_prpl: "Ex is_acc_run \<Longrightarrow> Ex is_lasso_prpl"
    using accepted_lasso is_lasso_prpl_of_lasso by blast
  lemma (in igb_fr_graph)  lasso_prpl_acc_run_iff: "Ex is_lasso_prpl \<longleftrightarrow> Ex is_acc_run"
    using acc_run_lasso_prpl lasso_prpl_acc_run by auto

  lemma [autoref_rel_intf]: "REL_INTF igbg_impl_rel_ext i_igbg" by (rule REL_INTFI)

  subsection \<open>Operations\<close>

  definition [simp]: "op_language_empty A \<equiv> language A = {}"

  lemmas [autoref_op_pat] = op_language_empty_def[symmetric]

  subsection \<open>Implementations\<close>

  context
  begin

    interpretation autoref_syn by this

    lemma nba_g_ahs: "nba_g A = \<lparr> g_V = UNIV, g_E = E_of_succ (\<lambda> p. CAST
      ((\<Union> a \<in> alphabet A. transition A a p ::: \<langle>S\<rangle> list_set_rel) ::: \<langle>S\<rangle> ahs_rel bhc)),
      g_V0 = initial A \<rparr>"
      unfolding nba_g_def nba.successors_alt_def CAST_def id_apply autoref_tag_defs by rule

    schematic_goal nbai_gi:
      notes [autoref_ga_rules] = map2set_to_list
      fixes S :: "('statei \<times> 'state) set"
      assumes [autoref_ga_rules]: "is_bounded_hashcode S seq bhc"
      assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('statei) hms"
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S\<rangle> nbai_nba_rel"
      shows "(?f :: ?'a, RETURN (nba_g A)) \<in> ?A"
      unfolding nba_g_ahs[where S = S and bhc = bhc] by (autoref_monadic (plain))
    concrete_definition nbai_gi uses nbai_gi
    lemma nbai_gi_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      shows "(NBA_Algorithms.nbai_gi seq bhc hms, nba_g) \<in>
        \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> \<langle>unit_rel, S\<rangle> g_impl_rel_ext"
      using nbai_gi.refine[THEN RETURN_nres_relD] assms unfolding autoref_tag_defs by blast

    schematic_goal nba_nodes:
      fixes S :: "('statei \<times> 'state) set"
      assumes [simp]: "finite ((g_E (nba_g A))\<^sup>* `` g_V0 (nba_g A))"
      assumes [autoref_ga_rules]: "is_bounded_hashcode S seq bhc"
      assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('statei) hms"
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S\<rangle> nbai_nba_rel"
      shows "(?f :: ?'a, op_reachable (nba_g A)) \<in> ?R" by autoref
    concrete_definition nba_nodes uses nba_nodes
    lemma nba_nodes_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_PRECOND (finite (nodes A))"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      assumes "(Ai, A) \<in> \<langle>L, S\<rangle> nbai_nba_rel"
      shows "(NBA_Algorithms.nba_nodes seq bhc hms Ai,
        (OP nodes ::: \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> \<langle>S\<rangle> ahs_rel bhc) $ A) \<in> \<langle>S\<rangle> ahs_rel bhc"
    proof -
      have 1: "nodes A = op_reachable (nba_g A)" by (auto simp: nba_g_V0 nba_g_E_rtrancl)
      have 2: "finite ((g_E (nba_g A))\<^sup>* `` g_V0 (nba_g A))" using assms(1) unfolding 1 by simp
      show ?thesis using nba_nodes.refine assms 2 unfolding autoref_tag_defs 1 by blast
    qed

    lemma nba_igbg_ahs: "nba_igbg A = \<lparr> g_V = UNIV, g_E = E_of_succ (\<lambda> p. CAST
      ((\<Union> a \<in> alphabet A. transition A a p ::: \<langle>S\<rangle> list_set_rel) ::: \<langle>S\<rangle> ahs_rel bhc)), g_V0 = initial A,
      igbg_num_acc = 1, igbg_acc = \<lambda> p. if accepting A p then {0} else {} \<rparr>"
      unfolding nba_g_def nba_igbg_def nba.successors_alt_def CAST_def id_apply autoref_tag_defs
      unfolding graph_rec.defs
      by simp

    schematic_goal nbai_igbgi:
      notes [autoref_ga_rules] = map2set_to_list
      fixes S :: "('statei \<times> 'state) set"
      assumes [autoref_ga_rules]: "is_bounded_hashcode S seq bhc"
      assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('statei) hms"
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S\<rangle> nbai_nba_rel"
      shows "(?f :: ?'a, RETURN (nba_igbg A)) \<in> ?A"
      unfolding nba_igbg_ahs[where S = S and bhc = bhc] by (autoref_monadic (plain))
    concrete_definition nbai_igbgi uses nbai_igbgi
    lemma nbai_igbgi_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      shows "(NBA_Algorithms.nbai_igbgi seq bhc hms, nba_igbg) \<in>
        \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> igbg_impl_rel_ext unit_rel S"
      using nbai_igbgi.refine[THEN RETURN_nres_relD] assms unfolding autoref_tag_defs by blast

    schematic_goal nba_language_empty:
      fixes S :: "('statei \<times> 'state) set"
      assumes [simp]: "igb_fr_graph (nba_igbg A)"
      assumes [autoref_ga_rules]: "is_bounded_hashcode S seq bhs"
      assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('statei) hms"
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S\<rangle> nbai_nba_rel"
      shows "(?f :: ?'a, do { r \<leftarrow> op_find_lasso_spec (nba_igbg A); RETURN (r = None)}) \<in> ?A"
      by (autoref_monadic (plain))
    concrete_definition nba_language_empty uses nba_language_empty
    lemma nba_language_empty_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_PRECOND (finite (nodes A))"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      assumes "(Ai, A) \<in> \<langle>L, S\<rangle> nbai_nba_rel"
      shows "(NBA_Algorithms.nba_language_empty seq bhc hms Ai,
        (OP op_language_empty ::: \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> bool_rel) $ A) \<in> bool_rel"
    proof -
      have 1: "nodes A = op_reachable (nba_g A)" by (auto simp: nba_g_V0 nba_g_E_rtrancl)
      have 2: "finite ((g_E (nba_g A))\<^sup>* `` g_V0 (nba_g A))" using assms(1) unfolding 1 by simp
      interpret igb_fr_graph "nba_igbg A"
        using 2 unfolding nba_igbg_def nba_g_def graph_rec.defs by unfold_locales auto
      have "(RETURN (NBA_Algorithms.nba_language_empty seq bhc hms Ai),
        do { r \<leftarrow> find_lasso_spec; RETURN (r = None) }) \<in> \<langle>bool_rel\<rangle> nres_rel"
        using nba_language_empty.refine assms igb_fr_graph_axioms by simp
      also have "(do { r \<leftarrow> find_lasso_spec; RETURN (r = None) },
        RETURN (\<not> Ex is_lasso_prpl)) \<in> \<langle>bool_rel\<rangle> nres_rel"
        unfolding find_lasso_spec_def by (refine_vcg) (auto split: option.splits)
      finally have "NBA_Algorithms.nba_language_empty seq bhc hms Ai \<longleftrightarrow> \<not> Ex is_lasso_prpl"
        unfolding nres_rel_comp using RETURN_nres_relD by force
      also have "\<dots> \<longleftrightarrow> \<not> Ex is_acc_run" using lasso_prpl_acc_run_iff by auto
      also have "\<dots> \<longleftrightarrow> language A = {}" using acc_run_language is_igb_graph by auto
      finally show ?thesis by simp
    qed

  end

end