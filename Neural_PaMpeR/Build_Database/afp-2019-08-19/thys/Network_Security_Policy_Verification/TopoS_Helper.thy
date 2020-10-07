theory TopoS_Helper
imports Main TopoS_Interface 
  TopoS_ENF
  vertex_example_simps
begin

lemma (in SecurityInvariant_preliminaries) sinvar_valid_remove_flattened_offending_flows:
  assumes "wf_graph \<lparr>nodes = nodesG, edges = edgesG\<rparr>" (*TODO: we could get rid of this assumption*)
  shows "sinvar \<lparr>nodes = nodesG, edges = edgesG - \<Union> (set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP) \<rparr> nP"
proof -
  { fix f
    assume *: "f\<in>set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP"

    from * have 1: "sinvar \<lparr>nodes = nodesG, edges = edgesG - f \<rparr> nP"
      by (metis (hide_lams, mono_tags) SecurityInvariant_withOffendingFlows.valid_without_offending_flows delete_edges_simp2 graph.select_convs(1) graph.select_convs(2))
    from * have 2: "edgesG - \<Union> (set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP) \<subseteq> edgesG - f"
      by blast
    note 1 2
  }
  with assms show ?thesis 
    by (metis (hide_lams, no_types) Diff_empty Union_empty defined_offending equals0I mono_sinvar wf_graph_remove_edges)
qed


lemma (in SecurityInvariant_preliminaries) sinvar_valid_remove_SOME_offending_flows:
  assumes "set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP \<noteq> {}"
  shows "sinvar \<lparr>nodes = nodesG, edges = edgesG - (SOME F. F \<in> set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP) \<rparr> nP"
proof -
  { fix f
    assume *: "f\<in>set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP"

    from * have 1: "sinvar \<lparr>nodes = nodesG, edges = edgesG - f \<rparr> nP"
      by (metis (hide_lams, mono_tags) SecurityInvariant_withOffendingFlows.valid_without_offending_flows delete_edges_simp2 graph.select_convs(1) graph.select_convs(2))
    from * have 2: "edgesG - \<Union> (set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP) \<subseteq> edgesG - f"
      by blast
    note 1 2
  }
  with assms show ?thesis by (simp add: some_in_eq)
qed


lemma (in SecurityInvariant_preliminaries) sinvar_valid_remove_minimalize_offending_overapprox:
  assumes "wf_graph \<lparr>nodes = nodesG, edges = edgesG\<rparr>"
      and "\<not> sinvar \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP" (*"set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP \<noteq> {}"*)
      and "set Es = edgesG" and "distinct Es"
  shows "sinvar \<lparr>nodes = nodesG, edges = edgesG -
              set (minimalize_offending_overapprox Es [] \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP) \<rparr> nP"
proof -
  from assms have off_Es: "is_offending_flows (set Es) \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP"
    by (metis (no_types, lifting) Diff_cancel
        SecurityInvariant_withOffendingFlows.valid_empty_edges_iff_exists_offending_flows defined_offending
        delete_edges_simp2 graph.select_convs(2) is_offending_flows_def sinvar_monoI) 
  from minimalize_offending_overapprox_gives_back_an_offending_flow[OF assms(1) off_Es _ assms(4)] have
    in_offending: "set (minimalize_offending_overapprox Es [] \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP)
      \<in> set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP"
     using assms(3) by simp

  { fix f
    assume *: "f\<in>set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP"
    from * have 1: "sinvar \<lparr>nodes = nodesG, edges = edgesG - f \<rparr> nP"
      by (metis (hide_lams, mono_tags) SecurityInvariant_withOffendingFlows.valid_without_offending_flows delete_edges_simp2 graph.select_convs(1) graph.select_convs(2))
    note 1
  }
  with in_offending show ?thesis by (simp add: some_in_eq)
qed

end
