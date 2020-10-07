section \<open>Refine Kruskal\<close>

theory Kruskal_Refine
imports Kruskal SeprefUF
begin
 
subsection \<open>Refinement I: cycle check by connectedness\<close>

text \<open>As a first refinement step, the check for introduction of a cycle when adding an edge @{term e}
  can be replaced by checking whether the edge's endpoints are already connected. 
  By this we can shift from an edge-centric perspective to a vertex-centric perspective.\<close>

context Kruskal_interface
begin

abbreviation "empty_forest \<equiv> {}"

abbreviation "a_endpoints e \<equiv> SPEC (\<lambda>(a,b). joins a b e )"

definition kruskal0 
  where "kruskal0 \<equiv> do {
    l \<leftarrow> obtain_sorted_carrier;
    spanning_forest \<leftarrow> nfoldli l (\<lambda>_. True)
        (\<lambda>e T. do { 
            ASSERT (e \<in> E);      
            (a,b) \<leftarrow> a_endpoints e;
            ASSERT (joins a b e \<and> forest T \<and> e\<in>E \<and> T \<subseteq> E);
            if \<not> (a,b) \<in> connected T then
              do { 
                ASSERT (e\<notin>T);
                RETURN (insert e T)
              }
            else 
              RETURN T
        }) empty_forest;
        RETURN spanning_forest
      }"
 

lemma if_subst: "(if indep (insert e T) then
              RETURN (insert e T)
            else 
              RETURN T)
        = (if e\<notin> T \<and> indep (insert e T) then
              RETURN (insert e T)
            else 
              RETURN T)"
  by auto

lemma kruskal0_refine: "(kruskal0, minWeightBasis) \<in> \<langle>Id\<rangle>nres_rel"
  unfolding kruskal0_def minWeightBasis_def 
  apply(subst if_subst)
  apply refine_vcg
            apply refine_dref_type 
            apply (all \<open>(auto; fail)?\<close>)
  apply clarsimp
  apply (auto simp: augment_forest)
    using augment_forest joins_connected by blast+


subsection \<open>Refinement II: connectedness by PER operation\<close>

text \<open>Connectedness in the subgraph spanned by a set of edges is a partial equivalence relation and
  can be represented in a disjoint sets. This data structure is maintained while executing Kruskal's
  algorithm and can be used to efficiently check for connectedness (@{term per_compare}.\<close>


definition corresponding_union_find :: "'a per \<Rightarrow> 'edge set \<Rightarrow> bool" where
  "corresponding_union_find uf T \<equiv> (\<forall>a\<in>V. \<forall>b\<in>V. per_compare uf a b \<longleftrightarrow> ((a,b)\<in> connected T ))"

definition "uf_graph_invar uf_T
   \<equiv> case uf_T of (uf, T) \<Rightarrow> corresponding_union_find uf T \<and> Domain uf = V"

lemma uf_graph_invarD: "uf_graph_invar (uf, T) \<Longrightarrow> corresponding_union_find uf T"
  unfolding uf_graph_invar_def by simp

definition "uf_graph_rel \<equiv> br snd uf_graph_invar"

lemma uf_graph_relsndD: "((a,b),c) \<in> uf_graph_rel \<Longrightarrow> b=c"
  by(auto simp: uf_graph_rel_def in_br_conv)   

lemma uf_graph_relD: "((a,b),c) \<in> uf_graph_rel \<Longrightarrow> b=c \<and> uf_graph_invar (a,b)"
  by(auto simp: uf_graph_rel_def in_br_conv)      

definition kruskal1
  where "kruskal1 \<equiv> do {
    l \<leftarrow> obtain_sorted_carrier;
    let initial_union_find = per_init V;
    (per, spanning_forest) \<leftarrow> nfoldli l (\<lambda>_. True)
        (\<lambda>e (uf, T). do { 
            ASSERT (e \<in> E);
            (a,b) \<leftarrow> a_endpoints e;
            ASSERT (a\<in>V \<and> b\<in>V \<and> a \<in> Domain uf \<and> b \<in> Domain uf \<and> T\<subseteq>E);
            if \<not> per_compare uf a b then
              do { 
                let uf = per_union uf a b;
                ASSERT (e\<notin>T);
                RETURN (uf, insert e T)
              }
            else 
              RETURN (uf,T)
        }) (initial_union_find, empty_forest);
        RETURN spanning_forest
      }"


lemma corresponding_union_find_empty:
  shows "corresponding_union_find (per_init V) empty_forest"
  by(auto simp: corresponding_union_find_def connected_same per_init_def) 
   

lemma empty_forest_refine: "((per_init V, empty_forest), empty_forest)\<in>uf_graph_rel"
  using corresponding_union_find_empty
  unfolding  uf_graph_rel_def uf_graph_invar_def 
  by (auto simp: in_br_conv per_init_def)

lemma uf_graph_invar_preserve: 
  assumes "uf_graph_invar (uf, T)" "a\<in>V" "b\<in>V"
       "joins a b e" "e\<in>E" "T\<subseteq>E"
  shows "uf_graph_invar (per_union uf a b, insert e T)"
  using assms
  by(auto simp add: uf_graph_invar_def corresponding_union_find_def
                  insert_reachable per_union_def)    

theorem kruskal1_refine: "(kruskal1, kruskal0)\<in>\<langle>Id\<rangle>nres_rel"
  unfolding kruskal1_def kruskal0_def Let_def 
  apply (refine_rcg empty_forest_refine)
               apply refine_dref_type 
               apply (auto dest: uf_graph_relD E_inV uf_graph_invarD
      simp: corresponding_union_find_def uf_graph_rel_def
      simp: in_br_conv uf_graph_invar_preserve)  
  by (auto simp: uf_graph_invar_def dest: joins_in_V)  

end
      
end