theory SINVAR_Dependability
imports "../TopoS_Helper"
begin

subsection \<open>SecurityInvariant Dependability\<close>


type_synonym dependability_level = nat

definition default_node_properties :: "dependability_level"
  where  "default_node_properties \<equiv> 0"

text \<open>Less-equal other nodes depend on the output of a node than its dependability level.\<close>
fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> edges G. (num_reachable G e1) \<le> (nP e1))"

definition receiver_violation :: "bool" where 
  "receiver_violation \<equiv> False"


text\<open>It does not matter whether we iterate over all edges or all nodes. We chose all edges because it is in line with the other models.\<close>
  fun sinvar_nodes :: "'v graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> bool" where
    "sinvar_nodes G nP = (\<forall> v \<in> nodes G. (num_reachable G v) \<le> (nP v))"
  
  theorem sinvar_edges_nodes_iff: "wf_graph G \<Longrightarrow> 
    sinvar_nodes G nP = sinvar G nP"
  proof(unfold sinvar_nodes.simps sinvar.simps, rule iffI)
    assume a1: "wf_graph G"
      and  a2: "\<forall>v\<in>nodes G. num_reachable G v \<le> nP v"

      from a1[simplified wf_graph_def] have f1: "fst ` edges G \<subseteq> nodes G" by simp
      from f1 a2 have "\<forall>v \<in> (fst ` edges G). num_reachable G v \<le> nP v" by auto

      thus "\<forall>(e1, _) \<in> edges G. num_reachable G e1 \<le> nP e1" by auto
    next
    assume a1: "wf_graph G"
      and  a2: "\<forall>(e1, _)\<in>edges G. num_reachable G e1 \<le> nP e1"

      from a2 have g1: "\<forall> v \<in> (fst ` edges G). num_reachable G v \<le> nP v" by auto

      from FiniteGraph.succ_tran_empty[OF a1] num_reachable_zero_iff[OF a1, symmetric]
      have g2: "\<forall> v. v \<notin> (fst ` edges G) \<longrightarrow> num_reachable G v \<le> nP v" by (metis le0)

      from g1 g2 show "\<forall>v\<in>nodes G. num_reachable G v \<le> nP v" by metis
  qed




  lemma num_reachable_le_nodes: "\<lbrakk> wf_graph G \<rbrakk> \<Longrightarrow> num_reachable G v \<le> card (nodes G)"
    unfolding num_reachable_def
    using succ_tran_subseteq_nodes card_seteq nat_le_linear wf_graph.finiteV by metis


  text\<open>nP is valid if all dependability level are greater equal the total number of nodes in the graph\<close>
  lemma "\<lbrakk> wf_graph G; \<forall>v \<in> nodes G. nP v \<ge> card (nodes G) \<rbrakk> \<Longrightarrow> sinvar G nP"
    apply(subst sinvar_edges_nodes_iff[symmetric], simp)
    apply(simp add:)
    using num_reachable_le_nodes by (metis le_trans)



  text\<open>Generate a valid configuration to start from:\<close>
   text\<open>Takes arbitrary configuration, returns a valid one\<close>
   fun dependability_fix_nP :: "'v graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> ('v \<Rightarrow> dependability_level)" where
      "dependability_fix_nP G nP = (\<lambda>v. if num_reachable G v \<le> (nP v) then (nP v) else num_reachable G v)"
  
   text\<open>@{const dependability_fix_nP} always gives you a valid solution\<close>
   lemma dependability_fix_nP_valid: "\<lbrakk> wf_graph G \<rbrakk> \<Longrightarrow> sinvar G (dependability_fix_nP G nP)"
      by(subst sinvar_edges_nodes_iff[symmetric], simp_all)
  
   text\<open>furthermore, it gives you a minimal solution, i.e. if someone supplies a configuration with a value lower than
          calculated by @{const dependability_fix_nP}, this is invalid!\<close>
   lemma dependability_fix_nP_minimal_solution: "\<lbrakk> wf_graph G; \<exists> v \<in> nodes G. (nP v) < (dependability_fix_nP G (\<lambda>_. 0)) v \<rbrakk> \<Longrightarrow> \<not> sinvar G nP"
      apply(subst sinvar_edges_nodes_iff[symmetric], simp)
      apply(simp)
      apply(clarify)
      apply(rule_tac x="v" in bexI)
       apply(simp_all)
      done

(*
lemma card_less_equal_trancl: "finite A \<Longrightarrow> card {e2. (aa, e2) \<in> (A - X)\<^sup>+} \<le> card {e2. (aa, e2) \<in> (A)\<^sup>+}"
apply(subgoal_tac "{e2. (aa, e2) \<in> (A - X)\<^sup>+} \<subseteq> {e2. (aa, e2) \<in> (A)\<^sup>+}")
apply(rule card_mono)
defer
apply(simp)
apply (metis (lifting) Collect_mono Diff_subset trancl_mono)
by (metis (lifting) Range_iff finite_Range mem_Collect_eq rev_finite_subset subsetI trancl_range)
*)


lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
  apply(rule_tac SecurityInvariant_withOffendingFlows.sinvar_mono_I_proofrule)
   apply(auto) (*TODO: auto in the midddle*)
  apply(rename_tac nP e1 e2 N E' e1' e2' E)
  apply(drule_tac E'="E'" and v="e1'" in num_reachable_mono)
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
where default_node_properties = SINVAR_Dependability.default_node_properties
and sinvar = SINVAR_Dependability.sinvar
  unfolding SINVAR_Dependability.default_node_properties_def
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
     apply(simp add: unique_default_example_succ_tran num_reachable_def)
    apply(rule_tac x="vertex_1" in exI, simp)
    apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
    apply(simp add: unique_default_example_succ_tran num_reachable_def)
    apply(simp add: succ_tran_def unique_default_example_simp1 unique_default_example_simp2)
    done
  qed

  lemma TopoS_Dependability: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales  

hide_const (open) sinvar receiver_violation default_node_properties

end
