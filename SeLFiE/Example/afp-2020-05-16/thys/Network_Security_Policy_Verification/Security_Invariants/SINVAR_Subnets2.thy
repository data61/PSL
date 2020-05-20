theory SINVAR_Subnets2
imports"../TopoS_Helper"
begin


(*EXPERIMENTAL!!*)

subsection \<open>SecurityInvariant Subnets2\<close>

text\<open>Warning, This is just a test. Please look at @{file \<open>SINVAR_Subnets.thy\<close>}.
This security invariant has the following changes, compared to @{file \<open>SINVAR_Subnets.thy\<close>}:
A new BorderRouter' is introduced which can send to the members of its subnet.
A new InboundRouter is accessible by anyone. It can access all other routers and the outside.
\<close>


datatype subnets = Subnet nat | BorderRouter nat | BorderRouter' nat | InboundRouter | Unassigned

definition default_node_properties :: "subnets"
  where "default_node_properties \<equiv> Unassigned"

fun allowed_subnet_flow :: "subnets \<Rightarrow> subnets \<Rightarrow> bool" where
  "allowed_subnet_flow (Subnet s1) (Subnet s2) = (s1 = s2)" | 
  "allowed_subnet_flow (Subnet s1) (BorderRouter s2) = (s1 = s2)" |
  "allowed_subnet_flow (Subnet s1) (BorderRouter' s2) = (s1 = s2)" |
  "allowed_subnet_flow (Subnet _) _ = True" | 
  "allowed_subnet_flow (BorderRouter _) (Subnet _) = False" |
  "allowed_subnet_flow (BorderRouter _) _ = True" |
  "allowed_subnet_flow (BorderRouter' s1) (Subnet s2) = (s1 = s2)" |
  "allowed_subnet_flow (BorderRouter' _) _ = True" | 
  "allowed_subnet_flow InboundRouter (Subnet _) = False" | 
  "allowed_subnet_flow InboundRouter _ = True" | 
  "allowed_subnet_flow Unassigned Unassigned  = True" |
  "allowed_subnet_flow Unassigned InboundRouter  = True" |
  "allowed_subnet_flow Unassigned _  = False"

fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> edges G. allowed_subnet_flow (nP e1) (nP e2))"


definition receiver_violation :: "bool" where "receiver_violation = False"


text\<open>Only members of the same subnet or their @{const BorderRouter'} can access them.\<close>
lemma "allowed_subnet_flow a (Subnet s1) \<Longrightarrow> a = (BorderRouter' s1) \<or> a = (Subnet s1)"
  apply(cases a)
      apply(simp_all)
  done


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
  lemma All_to_Unassigned: "\<forall> e1. allowed_subnet_flow e1 Unassigned"
    by (rule allI, case_tac e1, simp_all)
  lemma Unassigned_default_candidate: "\<forall> nP e1 e2. \<not> allowed_subnet_flow (nP e1) (nP e2) \<longrightarrow> \<not> allowed_subnet_flow Unassigned (nP e2)"
    apply(intro allI)
    apply(case_tac "nP e2")
       apply simp_all
     apply(case_tac "nP e1")
         apply simp_all
    by(simp add: All_to_Unassigned)
  lemma allowed_subnet_flow_refl: "\<forall> e. allowed_subnet_flow e e"
    by(rule allI, case_tac e, simp_all)
  lemma Subnets_ENF: "SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form sinvar allowed_subnet_flow"
    unfolding SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_def
    by simp
  lemma Subnets_ENF_refl: "SecurityInvariant_withOffendingFlows.ENF_refl sinvar allowed_subnet_flow"
    unfolding SecurityInvariant_withOffendingFlows.ENF_refl_def
    apply(rule conjI)
     apply(simp add: Subnets_ENF)
    apply(simp add: allowed_subnet_flow_refl)
  done


  definition Subnets_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> ('v \<times> 'v) set set" where
  "Subnets_offending_set G nP = (if sinvar G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> \<not> allowed_subnet_flow (nP e1) (nP e2)} })"
  lemma Subnets_offending_set: 
  "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = Subnets_offending_set"
    apply(simp only: fun_eq_iff ENF_offending_set[OF Subnets_ENF] Subnets_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto)
  done


interpretation Subnets: SecurityInvariant_ACS
where default_node_properties = SINVAR_Subnets2.default_node_properties
and sinvar = SINVAR_Subnets2.sinvar
rewrites "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = Subnets_offending_set"
  unfolding SINVAR_Subnets2.default_node_properties_def
  apply unfold_locales
    apply(rule ballI)
    apply (rule SecurityInvariant_withOffendingFlows.ENF_fsts_refl_instance[OF Subnets_ENF_refl Unassigned_default_candidate])[1]
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
      apply(rename_tac mysubnetcase)
      apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := Unassigned, vertex_2 := BorderRouter mysubnetcase)" in exI, simp)
      apply(rule_tac x="vertex_1" in exI, simp)
      apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
     apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := Unassigned, vertex_2 := BorderRouter whatever)" in exI, simp)
     apply(rule_tac x="vertex_1" in exI, simp)
     apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
    apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := Unassigned, vertex_2 := BorderRouter whatever)" in exI, simp)
    apply(rule_tac x="vertex_1" in exI, simp)
    apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
   apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := Unassigned, vertex_2 := BorderRouter whatever)" in exI, simp)
   apply(rule_tac x="vertex_1" in exI, simp)
   apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
  apply(fact Subnets_offending_set)
 done


  lemma TopoS_Subnets2: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales


hide_fact (open) sinvar_mono   
hide_const (open) sinvar receiver_violation default_node_properties

end
