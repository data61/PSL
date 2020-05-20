theory SINVAR_ACLcommunicateWith
imports "../TopoS_Helper"
begin
subsection \<open>SecurityInvariant ACLcommunicateWith\<close>
text\<open>An access control list strategy that says that hosts must only transitively access each other if allowed\<close>


text\<open>Warning: this transitive model has exponential computational complexity\<close>

definition default_node_properties :: "'v list"
  where  "default_node_properties \<equiv> []"


fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> 'v list) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> v \<in> nodes G. (\<forall>a \<in> (succ_tran G v). a \<in> set (nP v)))"

definition receiver_violation :: "bool" where 
  "receiver_violation \<equiv> False"


(*Alternative definition*)
lemma ACLcommunicateWith_sinvar_alternative:
  "wf_graph G \<Longrightarrow> sinvar G nP = (\<forall> (e1,e2) \<in> (edges G)\<^sup>+. e2 \<in> set (nP e1))"
  proof(unfold sinvar.simps, rule iffI, goal_cases)
  case 1
      from 1(1) have e1_nodes: "(e1, e2) \<in> edges G \<Longrightarrow> e1 \<in> nodes G" for e1 e2
        by (simp add: wf_graph.E_wfD(1)) 
      from 1(2) have "\<forall>v\<in>nodes G. \<forall>a. (v, a) \<in> (edges G)\<^sup>+ \<longrightarrow> a \<in> set (nP v)"
        by(simp add: succ_tran_def)
      with e1_nodes have "(e1, e2)\<in>(edges G)\<^sup>+ \<Longrightarrow> e2 \<in> set (nP e1)" for e1 e2
        by (meson tranclD)
      thus ?case by blast
    next
    case 2
      from 2(1) have e1_nodes: "(v, a) \<in> edges G \<Longrightarrow> v \<in> nodes G" for v a
        by (simp add: wf_graph.E_wfD(1))
      with 2(2) show ?case by(auto simp add: succ_tran_def)
  qed

lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
  unfolding SecurityInvariant_withOffendingFlows.sinvar_mono_def
  proof(clarify)
    fix nP::"('v \<Rightarrow> 'v list)" and N E' E
    assume a1: "wf_graph \<lparr>nodes = N, edges = E\<rparr>"
    and    a2: "E' \<subseteq> E"
    and    a3: "sinvar \<lparr>nodes = N, edges = E\<rparr> nP"

    from a3 have "v \<in> N \<Longrightarrow> \<forall>a\<in>(succ_tran \<lparr>nodes = N, edges = E\<rparr> v). a \<in> set (nP v)" for v by fastforce
    with a2 have g2: "v \<in> N \<Longrightarrow> (\<forall> a \<in> (succ_tran \<lparr>nodes = N, edges = E'\<rparr> v). a \<in> set (nP v))" for v
      using succ_tran_mono[OF a1] by blast
    thus "sinvar \<lparr>nodes = N, edges = E'\<rparr> nP" by simp
qed


interpretation SecurityInvariant_preliminaries
where sinvar = sinvar
  apply unfold_locales
    apply(frule_tac finite_distinct_list[OF wf_graph.finiteE])
    apply(erule_tac exE)
    apply(rename_tac list_edges)
    apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono])
        apply(auto)[4]
    apply(auto simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def graph_ops False_set succ_tran_empty)[1]
   apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_sinvar_mono[OF sinvar_mono])
  apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
 done


lemma unique_default_example: "succ_tran \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> vertex_2 = {}"
apply (simp add: succ_tran_def)
by (metis Domain.DomainI Domain_empty Domain_insert distinct_vertices12 singleton_iff trancl_domain)

interpretation ACLcommunicateWith: SecurityInvariant_ACS
where default_node_properties = SINVAR_ACLcommunicateWith.default_node_properties
and sinvar = SINVAR_ACLcommunicateWith.sinvar
  unfolding SINVAR_ACLcommunicateWith.default_node_properties_def
  apply unfold_locales
  
   apply simp
   apply(subst(asm) SecurityInvariant_withOffendingFlows.set_offending_flows_simp, simp)
   apply(clarsimp)
   apply (metis)


  apply(erule default_uniqueness_by_counterexample_ACS)
  apply(simp)
  apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
  apply (simp add:graph_ops)
  apply (simp split: prod.split_asm prod.split)
  apply(simp add: List.neq_Nil_conv)
  apply(erule exE)
  apply(rename_tac canAccessThis)
  apply(case_tac "canAccessThis = vertex_1")
   apply(rule_tac x="\<lparr> nodes={canAccessThis,vertex_2}, edges = {(vertex_2,canAccessThis)} \<rparr>" in exI, simp)
   apply(rule conjI)
    apply(simp add: wf_graph_def)
   apply(rule_tac x="(\<lambda> x. [])(vertex_1 := [], vertex_2 := [])" in exI, simp)
   apply(simp add: example_simps)
   apply(rule_tac x="{(vertex_2,vertex_1)}" in exI, simp)
   apply(simp add: example_simps)
   apply(fastforce)

  apply(rule_tac x="\<lparr> nodes={vertex_1,canAccessThis}, edges = {(vertex_1,canAccessThis)} \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: wf_graph_def)
  apply(rule_tac x="(\<lambda> x. [])(vertex_1 := [], canAccessThis := [])" in exI, simp)
  apply(simp add: example_simps)
  apply(rule_tac x="{(vertex_1,canAccessThis)}" in exI, simp)
  apply(simp add: example_simps)
  apply(fastforce)
 done


  lemma TopoS_ACLcommunicateWith: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales  

hide_const (open) sinvar receiver_violation default_node_properties

end
