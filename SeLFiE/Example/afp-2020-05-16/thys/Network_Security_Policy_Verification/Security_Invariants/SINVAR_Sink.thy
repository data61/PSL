theory SINVAR_Sink
imports "../TopoS_Helper"
begin

subsection \<open>SecurityInvariant Sink (IFS)\<close>

datatype node_config = Sink | SinkPool | Unassigned

definition default_node_properties :: "node_config"
  where  "default_node_properties = Unassigned"

fun allowed_sink_flow :: "node_config \<Rightarrow> node_config \<Rightarrow> bool" where
  "allowed_sink_flow Sink _ = False" |
  "allowed_sink_flow SinkPool SinkPool = True" |
  "allowed_sink_flow SinkPool Sink = True" |
  "allowed_sink_flow SinkPool _ = False" |
  "allowed_sink_flow Unassigned _ = True"


fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> edges G. e1 \<noteq> e2 \<longrightarrow> allowed_sink_flow (nP e1) (nP e2))"

definition receiver_violation :: "bool" where "receiver_violation = True"


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

subsubsection\<open>ENF\<close>
  lemma Sink_ENFnr: "SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_not_refl sinvar allowed_sink_flow"
    by(simp add: SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_not_refl_def)
  lemma Unassigned_to_All: "\<forall> e2. allowed_sink_flow Unassigned e2"
    by (rule allI, case_tac e2, simp_all)
  lemma Unassigned_default_candidate: "\<forall> e1 e2. \<not> allowed_sink_flow e1 e2 \<longrightarrow> \<not> allowed_sink_flow e1 Unassigned"
    apply(rule allI)+
    apply(case_tac "e2")
      apply simp_all
     apply(case_tac "e1")
       apply simp_all
    apply(case_tac "e1")
      apply simp_all
    done

  definition Sink_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> ('v \<times> 'v) set set" where
  "Sink_offending_set G nP = (if sinvar G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> e1 \<noteq> e2 \<and> \<not> allowed_sink_flow (nP e1) (nP e2)} })"
  lemma Sink_offending_set: 
  "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = Sink_offending_set"
    apply(simp only: fun_eq_iff ENFnr_offending_set[OF Sink_ENFnr] Sink_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto)
  done


interpretation Sink: SecurityInvariant_IFS
where default_node_properties = default_node_properties
and sinvar = sinvar
rewrites "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = Sink_offending_set"
  unfolding default_node_properties_def
  apply unfold_locales
    apply(rule ballI)
    apply (rule SecurityInvariant_withOffendingFlows.ENFnr_snds_weakrefl_instance[OF Sink_ENFnr Unassigned_default_candidate Unassigned_to_All])
     apply(simp_all)[2]

   apply(erule default_uniqueness_by_counterexample_IFS)
   apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
   apply (simp add:graph_ops)
   apply (simp split: prod.split_asm prod.split)
   apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
   apply(rule conjI)
    apply(simp add: wf_graph_def)
    apply(case_tac otherbot, simp_all)
    apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := SinkPool, vertex_2 := Unassigned)" in exI, simp)
    apply(rule_tac x="vertex_2" in exI, simp)
    apply(rule_tac x="{(vertex_1, vertex_2)}" in exI, simp)
   apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := SinkPool, vertex_2 := Unassigned)" in exI, simp)
   apply(rule_tac x="vertex_2" in exI, simp)
   apply(rule_tac x="{(vertex_1, vertex_2)}" in exI, simp)

  apply(fact Sink_offending_set)
  done


  lemma TopoS_Sink: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales

hide_fact (open) sinvar_mono   
hide_const (open) sinvar receiver_violation default_node_properties

end
