theory SINVAR_Dependability_norefl
imports "../TopoS_Helper"
begin

subsection \<open>SecurityInvariant \<open>Dependability_norefl\<close>\<close>

text\<open>A version of the Dependability model but if a node reaches itself, it is ignored\<close>


type_synonym dependability_level = nat

definition default_node_properties :: "dependability_level"
  where  "default_node_properties \<equiv> 0"

text \<open>Less-equal other nodes depend on the output of a node than its dependability level.\<close>
fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> edges G. (num_reachable_norefl G e1) \<le> (nP e1))"


definition receiver_violation :: "bool" where 
  "receiver_violation \<equiv> False"





lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
  apply(rule_tac SecurityInvariant_withOffendingFlows.sinvar_mono_I_proofrule)
   apply(auto)
  apply(rename_tac nP e1 e2 N E' e1' e2' E)
  apply(drule_tac E'="E'" and v="e1'" in num_reachable_norefl_mono)
   apply simp
  apply(subgoal_tac "(e1', e2') \<in> E")
   apply(force)
  apply(blast)
 done
  

interpretation SecurityInvariant_preliminaries
where sinvar = sinvar
  apply unfold_locales
    apply(frule_tac finite_distinct_list[OF wf_graph.finiteE])
    apply(erule_tac exE)
    apply(rename_tac list_edges)
    apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono])
        apply(auto)[4]
    apply(auto simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def graph_ops)[1]
   apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_sinvar_mono[OF sinvar_mono])
  apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
 done



interpretation Dependability: SecurityInvariant_ACS
where default_node_properties = SINVAR_Dependability_norefl.default_node_properties
and sinvar = SINVAR_Dependability_norefl.sinvar
  unfolding SINVAR_Dependability_norefl.default_node_properties_def
  proof
    fix G::"'a graph" and f nP
    assume "wf_graph G" and "f \<in> set_offending_flows G nP"
    thus "\<forall>i\<in>fst ` f. \<not> sinvar G (nP(i := 0))"
     apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
     apply (simp split: prod.split_asm prod.split)
     apply (simp add:graph_ops)
     apply(clarify)
     apply (metis gr0I le0)
     done
  next
   fix otherbot 
   assume assm: "\<forall>G f nP i. wf_graph G \<and> f \<in> set_offending_flows G nP \<and> i \<in> fst ` f \<longrightarrow> \<not> sinvar G (nP(i := otherbot))"
   have unique_default_example_succ_tran:
     "succ_tran \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> vertex_1 = {vertex_2}"
    using unique_default_example1 by blast
   from assm show "otherbot = 0"
    apply -
    apply(elim default_uniqueness_by_counterexample_ACS)
    apply(simp)
    apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
        SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
        SecurityInvariant_withOffendingFlows.is_offending_flows_def)
    apply (simp add:graph_ops)
    apply (simp split: prod.split_asm prod.split)
    apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
    apply(rule conjI)
     apply(simp add: wf_graph_def)
    apply(rule_tac x="(\<lambda> x. 0)(vertex_1 := 0, vertex_2 := 0)" in exI, simp)
    apply(rule conjI)
     apply(simp add: unique_default_example_succ_tran num_reachable_norefl_def; fail)
    apply(rule_tac x="vertex_1" in exI, simp)
    apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
    apply(simp add: unique_default_example_succ_tran num_reachable_norefl_def)
    apply(simp add: succ_tran_def unique_default_example_simp1 unique_default_example_simp2)
    done
  qed


  lemma TopoS_Dependability_norefl: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales  

hide_const (open) sinvar receiver_violation default_node_properties

end
