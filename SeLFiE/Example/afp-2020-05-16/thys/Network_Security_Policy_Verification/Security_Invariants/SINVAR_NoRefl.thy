theory SINVAR_NoRefl
imports "../TopoS_Helper"
begin

subsection \<open>SecurityInvariant NoRefl\<close>

text\<open>Hosts are not allowed to communicate with themselves.\<close>

text \<open>This can be used to effectively lift hosts to roles.
        Just list all roles that are allowed to communicate with themselves.
        Otherwise, communication between hosts of the same role (group) is prohibited. 
        Useful in conjunction with the security gateway.\<close>

datatype node_config = NoRefl | Refl

definition default_node_properties :: "node_config"
  where  "default_node_properties = NoRefl"


fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (s, r) \<in> edges G. s = r \<longrightarrow> nP s = Refl)"


definition receiver_violation :: "bool" where "receiver_violation = False"



subsubsection \<open>Preliminaries\<close>
  lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
    apply(simp only: SecurityInvariant_withOffendingFlows.sinvar_mono_def)
    apply(clarify)
    by auto
  
  interpretation SecurityInvariant_preliminaries
  where sinvar = sinvar
    apply unfold_locales
      apply(frule_tac finite_distinct_list[OF wf_graph.finiteE])
      apply(erule_tac exE)
      apply(rename_tac list_edges)
      apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono])
          apply(auto)[6]
     apply(auto simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def graph_ops)[1]
    apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
   done

 lemma NoRfl_ENRsr: "SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_sr sinvar (\<lambda> nP\<^sub>s s nP\<^sub>r r. s = r \<longrightarrow> nP\<^sub>s = Refl)"
    by(simp add: SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_sr_def)

  definition NoRefl_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> ('v \<times> 'v) set set" where
  "NoRefl_offending_set G nP = (if sinvar G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> e1 = e2 \<and> nP e1 = NoRefl} })"

 thm SecurityInvariant_withOffendingFlows.ENFsr_offending_set[OF NoRfl_ENRsr]

  lemma NoRefl_offending_set: "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = NoRefl_offending_set"
    apply(simp only: fun_eq_iff NoRefl_offending_set_def)
    apply(intro allI, rename_tac G nP)
    apply(simp only: SecurityInvariant_withOffendingFlows.ENFsr_offending_set[OF NoRfl_ENRsr])
    apply(case_tac "sinvar G nP")
     apply(simp; fail)
    apply(simp)
    apply(rule)
     apply(rule)
     apply(clarsimp)
     using node_config.exhaust apply blast
    apply(rule)
    apply(rule)
    apply(clarsimp)
   done


  lemma NoRefl_unique_default:
    "\<forall>G f nP i. wf_graph G \<and> f \<in> set_offending_flows G nP \<and> i \<in> fst ` f \<longrightarrow> \<not> sinvar G (nP(i := otherbot)) \<Longrightarrow>
     otherbot = NoRefl"
   apply(erule default_uniqueness_by_counterexample_ACS)
   apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
   apply (simp add:graph_ops)
   apply (simp split: prod.split_asm prod.split)
   apply(rule_tac x="\<lparr> nodes={vertex_1}, edges = {(vertex_1,vertex_1)} \<rparr>" in exI, simp)
   apply(rule conjI)
    apply(simp add: wf_graph_def)
   apply(case_tac otherbot, simp_all)
   apply(rule_tac x="(\<lambda> x. NoRefl)(vertex_1 := NoRefl, vertex_2 := NoRefl)" in exI, simp)
   apply(rule_tac x="{(vertex_1,vertex_1)}" in exI, simp)
   done

interpretation NoRefl: SecurityInvariant_ACS
where default_node_properties = default_node_properties
and sinvar = sinvar
rewrites "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = NoRefl_offending_set"
  unfolding default_node_properties_def
  apply unfold_locales
    apply(rule ballI)
    apply(frule SINVAR_NoRefl.offending_notevalD)
    apply(simp only: SecurityInvariant_withOffendingFlows.ENFsr_offending_set[OF NoRfl_ENRsr])
    apply fastforce
   apply(fact NoRefl_unique_default)
  apply(fact NoRefl_offending_set)
  done

text\<open>It can also be interpreted as IFS\<close>
lemma NoRefl_SecurityInvariant_IFS: "SecurityInvariant_IFS sinvar default_node_properties"
  unfolding default_node_properties_def
  apply unfold_locales
    apply(rule ballI)
    apply(frule SINVAR_NoRefl.offending_notevalD)
    apply(simp only: SecurityInvariant_withOffendingFlows.ENFsr_offending_set[OF NoRfl_ENRsr])
    apply fastforce
   apply(erule default_uniqueness_by_counterexample_IFS)
   apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
   apply (simp add:graph_ops)
   apply (simp split: prod.split_asm prod.split)
   apply(rule_tac x="\<lparr> nodes={vertex_1}, edges = {(vertex_1,vertex_1)} \<rparr>" in exI, simp)
   apply(rule conjI)
    apply(simp add: wf_graph_def)
   apply(case_tac otherbot, simp_all)
   apply(rule_tac x="(\<lambda> x. NoRefl)(vertex_1 := NoRefl, vertex_2 := NoRefl)" in exI, simp)
   apply(rule_tac x="{(vertex_1,vertex_1)}" in exI, simp)
  done

  lemma TopoS_NoRefl: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales  

hide_fact (open) sinvar_mono   
hide_const (open) sinvar receiver_violation default_node_properties


end
