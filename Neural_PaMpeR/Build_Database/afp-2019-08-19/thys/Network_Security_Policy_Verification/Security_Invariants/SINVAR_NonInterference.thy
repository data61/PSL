theory SINVAR_NonInterference
imports "../TopoS_Helper"
begin

subsection \<open>SecurityInvariant NonInterference\<close>

datatype node_config = Interfering | Unrelated

definition default_node_properties :: "node_config"
  where  "default_node_properties = Interfering"

definition undirected_reachable :: "'v graph \<Rightarrow> 'v => 'v set" where
  "undirected_reachable G v = (succ_tran (undirected G) v) - {v}"


lemma undirected_reachable_mono:
  "E' \<subseteq> E \<Longrightarrow> undirected_reachable \<lparr>nodes = N, edges = E'\<rparr> n \<subseteq> undirected_reachable \<lparr>nodes = N, edges = E\<rparr> n"
unfolding undirected_reachable_def undirected_def succ_tran_def
by (fastforce intro: trancl_mono)

fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> n \<in> (nodes G). (nP n) = Interfering \<longrightarrow> (nP ` (undirected_reachable G n)) \<subseteq> {Unrelated})"

lemma "sinvar G nP \<longleftrightarrow> 
  (\<forall> n \<in> {v' \<in> (nodes G). (nP v') = Interfering}. {nP v' | v'. v' \<in> undirected_reachable G n} \<subseteq> {Unrelated})"
by auto

definition receiver_violation :: "bool" where 
  "receiver_violation = True"


text\<open>simplifications for sets we need in the uniqueness proof\<close>
  lemma tmp1: "{(b, a). a = vertex_1 \<and> b = vertex_2} = {(vertex_2, vertex_1)}" by auto
  lemma tmp6: "{(vertex_1, vertex_2), (vertex_2, vertex_1)}\<^sup>+ = 
    {(vertex_1, vertex_1), (vertex_2, vertex_2), (vertex_1, vertex_2), (vertex_2, vertex_1)}"
    apply(rule)
     apply(rule)
     apply(case_tac x, simp)
     apply(erule_tac r="{(vertex_1, vertex_2), (vertex_2, vertex_1)}" in trancl_induct)
      apply(auto)
     apply (metis (mono_tags) insertCI r_r_into_trancl)+
  done
  lemma tmp2: "(insert (vertex_1, vertex_2) {(b, a). a = vertex_1 \<and> b = vertex_2})\<^sup>+ = 
    {(vertex_1, vertex_1), (vertex_2, vertex_2), (vertex_1, vertex_2), (vertex_2, vertex_1)}"
    apply(subst tmp1)
    apply(fact tmp6)
    done
  lemma tmp4: "{(e1, e2). e1 = vertex_1 \<and> e2 = vertex_2 \<and> (e1 = vertex_1 \<longrightarrow> e2 \<noteq> vertex_2)} = {}" by blast
  lemma tmp5: "{(b, a). a = vertex_1 \<and> b = vertex_2 \<or> a = vertex_1 \<and> b = vertex_2 \<and> (a = vertex_1 \<longrightarrow> b \<noteq> vertex_2)} = 
    {(vertex_2, vertex_1)}" by fastforce
  lemma unique_default_example: "undirected_reachable \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> vertex_1 = {vertex_2}"
    by(auto simp add: undirected_def undirected_reachable_def succ_tran_def tmp2)
  lemma unique_default_example_hlp1: "delete_edges \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1, vertex_2)} = 
    \<lparr>nodes = {vertex_1, vertex_2}, edges = {}\<rparr>"
    by(simp add: delete_edges_def)
  lemma unique_default_example_2: 
    "undirected_reachable (delete_edges \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1,vertex_2 )}) vertex_1 = {}"
    by(simp add: undirected_def undirected_reachable_def succ_tran_def unique_default_example_hlp1)
  lemma unique_default_example_3: 
    "undirected_reachable (delete_edges \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1,vertex_2 )}) vertex_2 = {}"
    by(simp add: undirected_def undirected_reachable_def succ_tran_def unique_default_example_hlp1)
  lemma unique_default_example_4: 
    "(undirected_reachable (add_edge vertex_1 vertex_2 (delete_edges \<lparr>nodes = {vertex_1, vertex_2}, 
    edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1, vertex_2)})) vertex_1) = {vertex_2}"
    apply(simp add: delete_edges_def add_edge_def undirected_def undirected_reachable_def succ_tran_def)
    apply(subst tmp4)
    apply(subst tmp5)
    apply(simp)
    apply(subst tmp6)
    by force
  lemma unique_default_example_5: 
    "(undirected_reachable (add_edge vertex_1 vertex_2 (delete_edges \<lparr>nodes = {vertex_1, vertex_2}, 
    edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1, vertex_2)})) vertex_2) = {vertex_1}"
    apply(simp add: delete_edges_def add_edge_def undirected_def undirected_reachable_def succ_tran_def)
    apply(subst tmp4)
    apply(subst tmp5)
    apply(simp)
    apply(subst tmp6)
    by force


  (*lemma empty_undirected_reachable_false: "xb \<in> undirected_reachable \<lparr>nodes = nodes G, edges = {(e1, e2). False}\<rparr> na \<longleftrightarrow> False"
    apply(simp add: undirected_reachable_def succ_tran_def undirected_def)
    apply(subst tmp3)
    by fastforce*)

  lemma empty_undirected_reachable_false: "xb \<in> undirected_reachable (delete_edges G (edges G)) na \<longleftrightarrow> False"
    by(simp add: undirected_reachable_def succ_tran_def undirected_def delete_edges_edges_empty)

subsubsection\<open>monotonic and preliminaries\<close>
  lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
  unfolding SecurityInvariant_withOffendingFlows.sinvar_mono_def
    apply(clarsimp)
    apply(rename_tac nP N E' n E xa)
    apply(erule_tac x=n in ballE)
     prefer 2
     apply simp
    apply(simp)
    apply(drule_tac N=N and n=n in undirected_reachable_mono)
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
      apply(auto simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def empty_undirected_reachable_false)[1]
     apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_sinvar_mono[OF sinvar_mono])
    apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
  done


interpretation NonInterference: SecurityInvariant_IFS
where default_node_properties = SINVAR_NonInterference.default_node_properties
and sinvar = SINVAR_NonInterference.sinvar
  unfolding SINVAR_NonInterference.default_node_properties_def
  apply unfold_locales
   apply(rule ballI)
   apply(drule SINVAR_NonInterference.offending_notevalD)
   apply(simp)
   apply clarify
   apply(rename_tac xa)
   apply(case_tac "nP xa")
    (*case Interfering*)
    apply simp
    apply(erule_tac x=n and A="nodes G" in ballE)
     prefer 2
     apply fast
    apply(simp)
    apply(thin_tac "wf_graph G")
    apply(thin_tac "(a,b) \<in> f")
    apply(thin_tac "n \<in> nodes G")
    apply(thin_tac "nP n = Interfering")
    apply(erule disjE)
     apply fastforce
     apply fastforce
   (*case Unrelated*)
   apply simp
  (*unique: *)
  apply(erule default_uniqueness_by_counterexample_IFS)
  apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
  apply (simp add:delete_edges_set_nodes)
  apply (simp split: prod.split_asm prod.split)
  apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: wf_graph_def)
  apply(rule_tac x="(\<lambda> x. default_node_properties)(vertex_1 := Interfering, vertex_2 := Interfering)" in exI, simp)
  apply(rule conjI)
   apply(simp add: unique_default_example)
  apply(rule_tac x="vertex_2" in exI, simp)
  apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
  apply(simp add: unique_default_example)
  apply(simp add: unique_default_example_2)
  apply(simp add: unique_default_example_3)
  apply(simp add: unique_default_example_4)
  apply(simp add: unique_default_example_5)
  apply(case_tac otherbot)
   apply simp
  apply(simp add:graph_ops)
  done


  lemma TopoS_NonInterference: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales
   

hide_const (open) sinvar receiver_violation default_node_properties

\<comment> \<open>Hide all the helper lemmas.\<close>
hide_fact tmp1 tmp2 tmp4 tmp5 tmp6 unique_default_example 
          unique_default_example_2 unique_default_example_3 unique_default_example_4
          unique_default_example_5 empty_undirected_reachable_false

end
