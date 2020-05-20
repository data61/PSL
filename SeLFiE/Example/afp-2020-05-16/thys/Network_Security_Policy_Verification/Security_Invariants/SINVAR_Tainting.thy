theory SINVAR_Tainting
imports "../TopoS_Helper"
begin

subsection \<open>SecurityInvariant Tainting for IFS\<close>

context
begin

  qualified type_synonym taints = "string set"

  text\<open>Warning: an infinite set has cardinality 0\<close>
  lemma "card (UNIV::taints) = 0" by (simp add: infinite_UNIV_listI) 
  
  qualified definition default_node_properties :: "taints"
    where  "default_node_properties \<equiv> {}"
  
  
  (*The definition we want to present*)
  text\<open>For all nodes @{term n} in the graph, for all nodes @{term r} which are reachable from @{term n},
        node @{term n} needs the appropriate tainting fields which are set by @{term r}\<close>
  definition sinvar_tainting :: "'v graph \<Rightarrow> ('v \<Rightarrow> taints) \<Rightarrow> bool" where
    "sinvar_tainting G nP \<equiv> \<forall> n \<in> (nodes G). \<forall>r \<in> (succ_tran G n). nP n \<subseteq> nP r"
  
  
  private lemma sinvar_tainting_edges_def: "wf_graph G \<Longrightarrow>
    sinvar_tainting G nP \<longleftrightarrow> (\<forall> (v1,v2) \<in> edges G. \<forall>r \<in> (succ_tran G v1). nP v1 \<subseteq> nP r)"
    unfolding sinvar_tainting_def
    proof
      assume a1: "wf_graph G"
        and  a2: "\<forall>n\<in>nodes G. \<forall>r\<in>succ_tran G n. nP n \<subseteq> nP r"
        from a1[simplified wf_graph_def] have f1: "fst ` edges G \<subseteq> nodes G" by simp
        from f1 a2 have "\<forall>v \<in> (fst ` edges G). \<forall>r\<in>succ_tran G v. nP v \<subseteq> nP r" by auto
        thus "\<forall>(v1, _)\<in>edges G. \<forall>r\<in>succ_tran G v1. nP v1 \<subseteq> nP r" by fastforce
      next
      assume a1: "wf_graph G"
        and  a2: "\<forall>(v1, v2)\<in>edges G. \<forall>r\<in>succ_tran G v1. nP v1 \<subseteq> nP r"
        from a2 have g1: "\<forall> v \<in> (fst ` edges G). \<forall>r\<in>succ_tran G v. nP v \<subseteq> nP r" by fastforce
        from FiniteGraph.succ_tran_empty[OF a1]
        have g2: "\<forall> v. v \<notin> (fst ` edges G) \<longrightarrow> (\<forall>r\<in>succ_tran G v. nP v \<subseteq> nP r)" by blast
        from g1 g2 show "\<forall>n\<in>nodes G. \<forall>r\<in>succ_tran G n. nP n \<subseteq> nP r" by metis
    qed
  
  text\<open>Alternative definition of the @{const sinvar_tainting}\<close>
  
  qualified definition sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> taints) \<Rightarrow> bool" where
    "sinvar G nP \<equiv> \<forall> (v1,v2) \<in> edges G. nP v1 \<subseteq> nP v2"
  
  
  qualified lemma sinvar_preferred_def:
    "wf_graph G \<Longrightarrow> sinvar_tainting G nP = sinvar G nP"
    proof(unfold sinvar_tainting_edges_def sinvar_def, rule iffI, goal_cases)
    case 2
        have "(v, v') \<in> (edges G)\<^sup>+ \<Longrightarrow> nP v \<subseteq> nP v'" for v v'
          proof(induction rule: trancl_induct)
          case base thus ?case using 2(2) by fastforce
          next
          case step thus ?case using 2(2) by fastforce
          qed
        thus ?case
        by(simp add: succ_tran_def)
      next
      case 1
        from 1(1)[simplified wf_graph_def] have f1: "fst ` edges G \<subseteq> nodes G" by simp
        from f1 1(2) have "\<forall>v \<in> (fst ` edges G). \<forall>v'\<in>succ_tran G v. nP v \<subseteq> nP v'" by fastforce
        thus ?case unfolding succ_tran_def by fastforce
    qed
  
  
  text\<open>Information Flow Security\<close>
  qualified definition receiver_violation :: "bool" where "receiver_violation \<equiv> True"
  
  
  private lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
    apply(simp add: SecurityInvariant_withOffendingFlows.sinvar_mono_def sinvar_def)
    apply(clarify)
    by blast
  interpretation SecurityInvariant_preliminaries
  where sinvar = sinvar
  proof(unfold_locales, goal_cases)
    case (1 G nP)
      from 1 show ?case
      apply(frule_tac finite_distinct_list[OF wf_graph.finiteE])
      apply(erule_tac exE)
      apply(rename_tac list_edges)
      apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono])
          apply(auto simp add: sinvar_def)
       apply(auto simp add: sinvar_def SecurityInvariant_withOffendingFlows.is_offending_flows_def graph_ops)[1]
      done
    next
    case (2 N E E' nP) thus ?case by(simp add: sinvar_def) blast
    next
    case 3 thus ?case by(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
  qed
  
  
  
  private  lemma Taints_def_unique: "otherbot \<noteq> {} \<Longrightarrow>
      \<exists>G p i f. wf_graph G \<and> \<not> sinvar G p \<and> f \<in> (SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G p) \<and>
         sinvar (delete_edges G f) p \<and>
          i \<in> snd ` f \<and> sinvar G (p(i := otherbot)) "
    apply(simp)
    apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
        SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
        SecurityInvariant_withOffendingFlows.is_offending_flows_def)
    apply (simp add:graph_ops)
    apply (simp split: prod.split_asm prod.split)
    apply(rule_tac x="\<lparr> nodes=set [vertex_1,vertex_2], edges = set [(vertex_1,vertex_2)] \<rparr>" in exI, simp)
    apply(rule conjI)
     apply(simp add: wf_graph_def; fail)
    apply(subgoal_tac "\<exists>foo. foo \<in> otherbot")
     prefer 2
     subgoal by fastforce
    apply(erule exE, rename_tac foo)
    apply(rule_tac x="(\<lambda> x. {})(vertex_1 := {foo}, vertex_2 := {})" in exI)
    apply(rule conjI)
     apply(simp add: sinvar_def; fail)
    apply(rule_tac x="vertex_2" in exI)
    apply(rule_tac x="set [(vertex_1,vertex_2)]" in exI, simp)
    apply(simp add: sinvar_def)
    done
  
  
  
  subsubsection \<open>ENF\<close>
    private lemma Taints_ENF: "SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form sinvar (\<subseteq>)"
      unfolding SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_def sinvar_def
      by simp
    private lemma Taints_ENF_refl: "SecurityInvariant_withOffendingFlows.ENF_refl sinvar (\<subseteq>)"
      unfolding SecurityInvariant_withOffendingFlows.ENF_refl_def
       by(auto simp add: Taints_ENF)
  
    qualified definition Taints_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> taints) \<Rightarrow> ('v \<times> 'v) set set" where
    "Taints_offending_set G nP = (if sinvar G nP then
        {}
       else 
        { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> \<not> (nP e1) \<subseteq> (nP e2)} })"
    lemma Taints_offending_set: "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = Taints_offending_set"
      by(auto simp add: fun_eq_iff
                        SecurityInvariant_withOffendingFlows.ENF_offending_set[OF Taints_ENF]
                        Taints_offending_set_def)
     
  
    interpretation Taints: SecurityInvariant_IFS sinvar default_node_properties
    rewrites "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = Taints_offending_set"
      unfolding receiver_violation_def
      unfolding default_node_properties_def
      proof(unfold_locales, goal_cases)
      case 1
        from 1(2) show ?case
        apply(intro ballI)
        apply(rule SecurityInvariant_withOffendingFlows.ENF_snds_refl_instance[OF Taints_ENF_refl])
          apply(simp_all add: Taints_ENF Taints_ENF_refl)
        by blast
      next
      case 2 thus ?case
        proof(elim default_uniqueness_by_counterexample_IFS)
        qed(fact Taints_def_unique)
      next
      case 3 show "set_offending_flows = Taints_offending_set" by(fact Taints_offending_set)
     qed
  
  
    lemma TopoS_Tainting: "SecurityInvariant sinvar default_node_properties receiver_violation"
    unfolding receiver_violation_def by unfold_locales

end

end
