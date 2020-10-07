theory SINVAR_SubnetsInGW
imports"../TopoS_Helper"
begin

subsection \<open>SecurityInvariant SubnetsInGW\<close>

datatype subnets = Member | InboundGateway | Unassigned

definition default_node_properties :: "subnets"
  where  "default_node_properties \<equiv> Unassigned"

fun allowed_subnet_flow :: "subnets \<Rightarrow> subnets \<Rightarrow> bool" where
  "allowed_subnet_flow Member _ = True" |
  "allowed_subnet_flow InboundGateway _ = True" |
  "allowed_subnet_flow Unassigned Unassigned = True" |
  "allowed_subnet_flow Unassigned InboundGateway = True"|
  "allowed_subnet_flow Unassigned Member = False"

fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> subnets)  \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> edges G. allowed_subnet_flow (nP e1) (nP e2))"

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

subsubsection\<open>ENF\<close>
  lemma Unassigned_not_to_Member: "\<not> allowed_subnet_flow Unassigned Member"
    by(simp)
  lemma All_to_Unassigned: "allowed_subnet_flow e1 Unassigned"
    by (case_tac e1, simp_all)
  lemma Member_to_All: "allowed_subnet_flow Member e2"
    by (case_tac e2, simp_all)
  lemma Unassigned_default_candidate: "\<forall> nP e1 e2. \<not> allowed_subnet_flow (nP e1) (nP e2) \<longrightarrow> \<not> allowed_subnet_flow Unassigned (nP e2)"
    apply(rule allI)+
    apply(case_tac "nP e2")
      apply simp
     apply(case_tac "nP e1")
       apply(simp_all)[3]
    by(simp add: All_to_Unassigned)
  lemma allowed_subnet_flow_refl: "allowed_subnet_flow e e"
    by(case_tac e, simp_all)
  lemma SubnetsInGW_ENF: "SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form sinvar allowed_subnet_flow"
    unfolding SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_def
    by simp
  lemma SubnetsInGW_ENF_refl: "SecurityInvariant_withOffendingFlows.ENF_refl sinvar allowed_subnet_flow"
    unfolding SecurityInvariant_withOffendingFlows.ENF_refl_def
    apply(rule conjI)
     apply(simp add: SubnetsInGW_ENF)
    apply(simp add: allowed_subnet_flow_refl)
  done

  definition SubnetsInGW_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> ('v \<times> 'v) set set" where
  "SubnetsInGW_offending_set G nP = (if sinvar G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> \<not> allowed_subnet_flow (nP e1) (nP e2)} })"
  lemma SubnetsInGW_offending_set: 
  "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = SubnetsInGW_offending_set"
    apply(simp only: fun_eq_iff ENF_offending_set[OF SubnetsInGW_ENF] SubnetsInGW_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto)
  done

interpretation SubnetsInGW: SecurityInvariant_ACS
where default_node_properties = SINVAR_SubnetsInGW.default_node_properties
and sinvar = SINVAR_SubnetsInGW.sinvar
rewrites "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = SubnetsInGW_offending_set"
  unfolding SINVAR_SubnetsInGW.default_node_properties_def
  apply unfold_locales

    apply(rule ballI)
    thm SecurityInvariant_withOffendingFlows.ENF_fsts_refl_instance[OF SubnetsInGW_ENF_refl Unassigned_default_candidate]
    apply(rule SecurityInvariant_withOffendingFlows.ENF_fsts_refl_instance[OF SubnetsInGW_ENF_refl Unassigned_default_candidate])
      apply(simp_all)[2]

   apply(erule default_uniqueness_by_counterexample_ACS)
   apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
   apply (simp add:graph_ops)
   apply (simp split: prod.split_asm prod.split)
   apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
   apply(rule conjI)
    apply(simp add: wf_graph_def)
   apply(case_tac otherbot, simp_all)
   apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := Unassigned, vertex_2 := Member)" in exI, simp)
    apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
   apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := Unassigned, vertex_2 := Member)" in exI, simp)
   apply(rule_tac x="vertex_1" in exI, simp)
   apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
  
  apply(fact SubnetsInGW_offending_set)
  done



  lemma TopoS_SubnetsInGW: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales

 
hide_fact (open) sinvar_mono   
hide_const (open) sinvar receiver_violation default_node_properties

end
