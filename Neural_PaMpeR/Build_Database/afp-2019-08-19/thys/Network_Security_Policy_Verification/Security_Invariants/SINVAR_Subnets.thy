theory SINVAR_Subnets
imports"../TopoS_Helper"
begin

subsection \<open>SecurityInvariant Subnets\<close>

text\<open>If unsure, maybe you should look at @{file \<open>SINVAR_SubnetsInGW.thy\<close>}\<close>


datatype subnets = Subnet nat | BorderRouter nat | Unassigned

definition default_node_properties :: "subnets"
  where  "default_node_properties \<equiv> Unassigned"

fun allowed_subnet_flow :: "subnets \<Rightarrow> subnets \<Rightarrow> bool" where
  "allowed_subnet_flow (Subnet s1) (Subnet s2) = (s1 = s2)" | 
  "allowed_subnet_flow (Subnet s1) (BorderRouter s2) = (s1 = s2)" |
  "allowed_subnet_flow (Subnet s1) Unassigned = True" | 
  "allowed_subnet_flow (BorderRouter s1) (Subnet s2) = False" | (*(s1 = s2) would also be fine*)
  "allowed_subnet_flow (BorderRouter s1) Unassigned = True" | 
  "allowed_subnet_flow (BorderRouter s1) (BorderRouter s2) = True" |
  "allowed_subnet_flow Unassigned Unassigned  = True" |
  "allowed_subnet_flow Unassigned _  = False"

fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> bool" where
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
  lemma Unassigned_only_to_Unassigned: "allowed_subnet_flow Unassigned e2 \<longleftrightarrow> e2 = Unassigned"
    by(case_tac e2, simp_all)
  lemma All_to_Unassigned: "\<forall> e1. allowed_subnet_flow e1 Unassigned"
    by (rule allI, case_tac e1, simp_all)
  lemma Unassigned_default_candidate: "\<forall> nP e1 e2. \<not> allowed_subnet_flow (nP e1) (nP e2) \<longrightarrow> \<not> allowed_subnet_flow Unassigned (nP e2)"
    apply(rule allI)+
    apply(case_tac "nP e2")
      apply simp
     apply simp
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
where default_node_properties = SINVAR_Subnets.default_node_properties
and sinvar = SINVAR_Subnets.sinvar
rewrites "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = Subnets_offending_set"
  unfolding SINVAR_Subnets.default_node_properties_def
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
  apply(fact Subnets_offending_set)
 done


  lemma TopoS_Subnets: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales

subsubsection \<open>Analysis\<close>

lemma violating_configurations: "\<not> sinvar G nP \<Longrightarrow> 
    \<exists> (e1, e2) \<in> edges G. nP e1 = Unassigned \<or> (\<exists> s1. nP e1 = Subnet s1) \<or> (\<exists> s1. nP e1 = BorderRouter s1)"
  apply simp
  apply clarify
  apply(rename_tac a b)
  apply(case_tac "nP b", simp_all)
    apply(case_tac "nP a", simp_all)
      apply blast
     apply blast
    apply blast
   apply(case_tac "nP a", simp_all)
    apply blast
   apply blast
  apply(simp add: All_to_Unassigned)
done


text \<open>All cases where the model can become invalid:\<close>
theorem violating_configurations_exhaust: "\<not> sinvar G nP \<longleftrightarrow> 
   (\<exists> (e1, e2) \<in> (edges G). 
      nP e1 = Unassigned \<and> nP e2 \<noteq> Unassigned \<or> 
      (\<exists> s1 s2. nP e1 = Subnet s1 \<and> s1 \<noteq> s2 \<and> (nP e2 = Subnet s2 \<or> nP e2 = BorderRouter s2)) \<or> 
      (\<exists> s1 s2. nP e1 = BorderRouter s1 \<and> nP e2 = Subnet s2)
   )" (is "?l \<longleftrightarrow> ?r")
 proof
  assume ?l 
    have violating_configurations_exhaust_Unassigned:
      "(n1, n2) \<in> (edges G) \<Longrightarrow> nP n1 = Unassigned \<Longrightarrow> \<not> allowed_subnet_flow (nP n1) (nP n2) \<Longrightarrow>
        \<exists> (e1, e2) \<in> (edges G).  nP e1 = Unassigned \<and> nP e2 \<noteq> Unassigned " for n1 n2
      by(cases "nP n2", simp_all) force+

    have violating_configurations_exhaust_Subnet:
      "(n1, n2) \<in> (edges G) \<Longrightarrow> nP n1 = Subnet s1' \<Longrightarrow> \<not> allowed_subnet_flow (nP n1) (nP n2) \<Longrightarrow>
      \<exists> (e1, e2) \<in> (edges G). \<exists> s1 s2. nP e1 = Subnet s1 \<and> s1 \<noteq> s2 \<and> (nP e2 = Subnet s2 \<or> nP e2 = BorderRouter s2)"
      for n1 n2 s1' by(cases "nP n2", simp_all) blast+

    have violating_configurations_exhaust_BorderRouter:
    "(n1, n2) \<in> (edges G) \<Longrightarrow> nP n1 = BorderRouter s1' \<Longrightarrow> \<not> allowed_subnet_flow (nP n1) (nP n2) \<Longrightarrow>
      \<exists> (e1, e2) \<in> (edges G). \<exists> s1 s2. nP e1 = BorderRouter s1 \<and> nP e2 = Subnet s2" for n1 n2 s1'
      by(cases "nP n2", simp_all) blast+

    from \<open>?l\<close> show ?r
    apply simp
    apply clarify
    apply(rename_tac n1 n2)
    apply(case_tac "nP n1", simp_all)
      apply(rename_tac s1)
      apply(drule_tac s1'="s1" in violating_configurations_exhaust_Subnet, simp_all)
      apply blast
     apply(rename_tac s1)
     apply(drule_tac s1'="s1" in violating_configurations_exhaust_BorderRouter, simp_all)
     apply blast
    apply(drule_tac violating_configurations_exhaust_Unassigned, simp_all)
    apply blast
    done
  next
  assume ?r thus ?l
    apply simp
    apply(clarify)
    apply(safe)
       apply(rule_tac x="(a,b)" in bexI)
        apply (simp add: Unassigned_only_to_Unassigned; fail)
       apply(simp; fail)
      apply(rule_tac x="(a,b)" in bexI)
       apply(simp; fail)
      apply(simp; fail)
     apply(rule_tac x="(a,b)" in bexI)
      apply(simp; fail)
     apply(simp; fail)
    apply(rule_tac x="(a,b)" in bexI)
     apply(simp; fail)
    apply(simp; fail)
   done
 qed


hide_fact (open) sinvar_mono   
hide_const (open) sinvar receiver_violation default_node_properties

end
