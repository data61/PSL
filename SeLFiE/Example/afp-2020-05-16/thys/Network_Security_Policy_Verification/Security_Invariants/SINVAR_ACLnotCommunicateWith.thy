theory SINVAR_ACLnotCommunicateWith
imports "../TopoS_Helper" SINVAR_ACLcommunicateWith
begin

subsection \<open>SecurityInvariant ACLnotCommunicateWith\<close>
text\<open>An access control list strategy that says that hosts must not transitively access each other.\<close>

text\<open>node properties: a set of hosts this host must not access\<close>

definition default_node_properties :: "'v set"
  where  "default_node_properties \<equiv> UNIV"


fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> 'v set) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> v \<in> nodes G. \<forall> a \<in> (succ_tran G v). a \<notin> (nP v))"

definition receiver_violation :: "bool" where 
  "receiver_violation \<equiv> False"

text\<open>It is the inverse of @{const SINVAR_ACLcommunicateWith.sinvar}\<close>
lemma ACLcommunicateNotWith_inverse_ACLcommunicateWith:
  "\<forall>v. UNIV - nP' v = set (nP v) \<Longrightarrow> SINVAR_ACLcommunicateWith.sinvar G nP \<longleftrightarrow> sinvar G nP'"
  by auto


lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
  unfolding SecurityInvariant_withOffendingFlows.sinvar_mono_def
  proof(clarify)
    fix nP::"('v \<Rightarrow> 'v set)" and N E' E
    assume a1: "wf_graph \<lparr>nodes = N, edges = E\<rparr>"
    and    a2: "E' \<subseteq> E"
    and    a3: "sinvar \<lparr>nodes = N, edges = E\<rparr> nP"

    from a3 have "\<And>v a. v \<in> N \<Longrightarrow>  a \<in> (succ_tran \<lparr>nodes = N, edges = E\<rparr> v) \<Longrightarrow> a \<notin> (nP v)" by fastforce
    from this a2 have g1: "\<And>v a. v \<in> N \<Longrightarrow> a \<in> (succ_tran \<lparr>nodes = N, edges = E'\<rparr> v) \<Longrightarrow> a \<notin> (nP v)" 
      using succ_tran_mono[OF a1] by blast

    thus "sinvar \<lparr>nodes = N, edges = E'\<rparr> nP"
      by(clarsimp)
qed
  

lemma succ_tran_empty: "(succ_tran \<lparr>nodes = nodes G, edges = {}\<rparr> v) = {}"
  by(simp add: succ_tran_def)

interpretation SecurityInvariant_preliminaries
where sinvar = sinvar
  apply unfold_locales
    apply(frule_tac finite_distinct_list[OF wf_graph.finiteE])
    apply(erule_tac exE)
    apply(rename_tac list_edges)
    apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono])
        apply(auto)[4]
    apply(auto simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def graph_ops succ_tran_empty)[1]
   apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_sinvar_mono[OF sinvar_mono])
  apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
 done


lemma unique_default_example: "succ_tran \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> vertex_2 = {}"
apply (simp add: succ_tran_def)
by (metis Domain.DomainI Domain_empty Domain_insert distinct_vertices12 singleton_iff trancl_domain)

interpretation ACLnotCommunicateWith: SecurityInvariant_ACS
where default_node_properties = SINVAR_ACLnotCommunicateWith.default_node_properties
and sinvar = SINVAR_ACLnotCommunicateWith.sinvar
  unfolding SINVAR_ACLnotCommunicateWith.default_node_properties_def
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
  apply(case_tac "otherbot = {}")

   apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
   apply(rule conjI)
    apply(simp add: wf_graph_def)
   apply(rule_tac x="(\<lambda> x. UNIV)(vertex_1 := {vertex_2}, vertex_2 := {})" in exI, simp)
   apply(simp add: example_simps)
   apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
   apply(simp add: example_simps)

  apply(subgoal_tac "\<exists>canAccess. canAccess \<in> UNIV \<and> canAccess \<notin> otherbot")
   prefer 2
   apply blast
  apply(erule exE)
  apply(rename_tac canAccessThis)
  apply(case_tac "vertex_1 \<noteq> canAccessThis")

   apply(rule_tac x="\<lparr> nodes={vertex_1,canAccessThis}, edges = {(vertex_1,canAccessThis)} \<rparr>" in exI, simp)
   apply(rule conjI)
    apply(simp add: wf_graph_def)
   apply(rule_tac x="(\<lambda> x. UNIV)(vertex_1 := UNIV, canAccessThis := {})" in exI, simp)
   apply(simp add: example_simps)
   apply(rule_tac x="{(vertex_1,canAccessThis)}" in exI, simp)
   apply(simp add: example_simps)

  apply(rule_tac x="\<lparr> nodes={canAccessThis,vertex_2}, edges = {(vertex_2,canAccessThis)} \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: wf_graph_def)
  apply(rule_tac x="(\<lambda> x. UNIV)(vertex_2 := UNIV, canAccessThis := {})" in exI, simp)
  apply(simp add: example_simps)
  apply(rule_tac x="{(vertex_2,canAccessThis)}" in exI, simp)
  apply(simp add: example_simps)
 done

  lemma TopoS_ACLnotCommunicateWith: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales  

hide_const (open) sinvar receiver_violation default_node_properties

end
