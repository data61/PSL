section \<open>Imperative Weighted Graphs\<close>
theory Sepref_WGraph
imports 
  "../Sepref_ICF_Bindings"
  Dijkstra_Shortest_Path.Graph
begin
  
  type_synonym 'w graph_impl = "(('w\<times>nat) list) Heap.array"

  abbreviation (input) "node_rel \<equiv> nbn_rel"
  abbreviation (input) "node_assn \<equiv> nbn_assn"

  definition "is_graph n R G Gi \<equiv> 
      \<exists>\<^sub>Al. Gi \<mapsto>\<^sub>a l * \<up>(
        valid_graph G \<and>
        n = length l \<and>
        nodes G = {0..<length l} \<and>
        (\<forall>v\<in>nodes G. (l!v, succ G v) \<in> \<langle>R \<times>\<^sub>r node_rel (length l)\<rangle>list_set_rel)
      )"
  
  definition succi :: "'w::heap graph_impl \<Rightarrow> nat \<Rightarrow> ('w\<times>nat) list Heap"
  where "succi G v = do {
    l \<leftarrow> Array.len G;
    if v<l then do { \<comment> \<open>TODO: Alternatively, require \<open>v\<close> to be a valid node as precondition!\<close>
      r \<leftarrow> Array.nth G v;
      return r
    } else return []
  }"

  lemma "
    < is_graph n R G Gi * \<up>(v\<in>nodes G) > 
      succi Gi v 
    < \<lambda>r. is_graph n R G Gi * \<up>((r,succ G v)\<in>\<langle>R \<times>\<^sub>r node_rel n\<rangle>list_set_rel) >"
    unfolding is_graph_def succi_def
    by sep_auto
  
  lemma (in valid_graph) succ_no_node_empty: "v\<notin>V \<Longrightarrow> succ G v = {}"
    unfolding succ_def using E_valid
    by auto
  
  lemma [sepref_fr_rules]: " 
    hn_refine 
      (hn_ctxt (is_graph n R) G Gi * hn_ctxt (node_assn n) v vi) 
      (succi Gi vi) 
      (hn_ctxt (is_graph n R) G Gi * hn_ctxt (node_assn n) v vi) 
      (pure (\<langle>R \<times>\<^sub>r node_rel n\<rangle>list_set_rel))
      (RETURN$(succ$G$v))"
    apply rule
    unfolding hn_ctxt_def pure_def is_graph_def succi_def
    by (sep_auto simp: valid_graph.succ_no_node_empty list_set_autoref_empty)
  
  definition nodes_impl :: "'w::heap graph_impl \<Rightarrow> nat list Heap"
    where "nodes_impl Gi \<equiv> do {
    l \<leftarrow> Array.len Gi;
    return [0..<l]
  }"
  
  lemma node_list_rel_id: "\<forall>x\<in>set l. x<n \<Longrightarrow> (l,l)\<in>\<langle>node_rel n\<rangle>list_rel"
    by (induction l) auto

  lemma [sepref_fr_rules]: "hn_refine 
    (hn_ctxt (is_graph n R) G Gi) 
    (nodes_impl Gi) 
    (hn_ctxt (is_graph n R) G Gi) 
    (pure (\<langle>node_rel n\<rangle>list_set_rel))
    (RETURN$(nodes$G))"
    apply rule
    unfolding hn_ctxt_def pure_def is_graph_def nodes_impl_def
    apply (sep_auto simp: list_set_rel_def br_def intro!: relcompI node_list_rel_id)
    done
  
  sepref_register succ nodes  

  
  definition cr_graph 
    :: "nat \<Rightarrow> (nat \<times> nat \<times> 'w) list \<Rightarrow> 'w::heap graph_impl Heap"
  where
    "cr_graph numV Es \<equiv> do {
      a \<leftarrow> Array.new numV [];
      a \<leftarrow> imp_nfoldli Es (\<lambda>_. return True) (\<lambda>(u,v,w) a. do {
        l \<leftarrow> Array.nth a u;
        let l = (w,v)#l;
        a \<leftarrow> Array.upd u l a;
        return a
      }) a;
      return a
    }"
  
  export_code cr_graph checking SML_imp


end

