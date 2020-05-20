section \<open>Abstract Datatype for Weighted Directed Graphs\<close>
theory Directed_Graph_Specs
imports Directed_Graph
begin

locale adt_wgraph =
  fixes \<alpha> :: "'g \<Rightarrow> ('v) wgraph"
    and invar :: "'g \<Rightarrow> bool"
    and succ :: "'g \<Rightarrow> 'v \<Rightarrow> (nat\<times>'v) list"
    and empty_graph :: 'g
    and add_edge :: "'v\<times>'v \<Rightarrow> nat \<Rightarrow> 'g \<Rightarrow> 'g"
  assumes succ_correct: "invar g \<Longrightarrow> set (succ g u) = {(d,v). \<alpha> g (u,v) = enat d}"
  assumes empty_graph_correct:
    "invar empty_graph"
    "\<alpha> empty_graph = (\<lambda>_. \<infinity>)"
  assumes add_edge_correct:
    "invar g \<Longrightarrow> \<alpha> g e = \<infinity> \<Longrightarrow> invar (add_edge e d g)"
    "invar g \<Longrightarrow> \<alpha> g e = \<infinity> \<Longrightarrow> \<alpha> (add_edge e d g) = (\<alpha> g)(e:=enat d)"
begin
  
lemmas wgraph_specs = succ_correct empty_graph_correct add_edge_correct
  
end

locale adt_finite_wgraph = adt_wgraph where \<alpha>=\<alpha> for \<alpha> :: "'g \<Rightarrow> ('v) wgraph" +
  assumes finite: "invar g \<Longrightarrow> finite (WGraph.edges (\<alpha> g))"


subsection \<open>Constructing Weighted Graphs from Lists\<close>  
lemma edges_empty[simp]: "WGraph.edges (\<lambda>_. \<infinity>) = {}" 
  by (auto simp: WGraph.edges_def)
  
lemma edges_insert[simp]: 
  "WGraph.edges (g(e:=enat d)) = Set.insert e (WGraph.edges g)" 
  by (auto simp: WGraph.edges_def)

text \<open>A list represents a graph if there are no multi-edges or duplicate edges\<close>
definition "valid_graph_rep l \<equiv> 
  (\<forall>u d d' v. (u,v,d)\<in>set l \<and> (u,v,d')\<in>set l \<longrightarrow> d=d')
\<and> distinct l
  "

text \<open>Alternative characterization: all node pairs must be distinct\<close>
lemma valid_graph_rep_code[code]: 
  "valid_graph_rep l \<longleftrightarrow> distinct (map (\<lambda>(u,v,_). (u,v)) l)"  
  by (auto simp: valid_graph_rep_def distinct_map inj_on_def)
  
lemma valid_graph_rep_simps[simp]:
  "valid_graph_rep []"
  "valid_graph_rep ((u,v,d) # l) \<longleftrightarrow> valid_graph_rep l \<and> (\<forall>d'. (u,v,d')\<notin>set l)"
  by (auto simp: valid_graph_rep_def)

  
text \<open>For a valid graph representation, there is exactly one graph that 
  corresponds to it\<close>  
lemma valid_graph_rep_ex1: 
  "valid_graph_rep l \<Longrightarrow> \<exists>! w. \<forall>u v d. w (u,v) = enat d \<longleftrightarrow> (u,v,d)\<in>set l"  
  unfolding valid_graph_rep_code
  apply safe
  subgoal 
    apply (rule exI[where x="\<lambda>(u,v).
        if \<exists>d. (u,v,d)\<in>set l then enat (SOME d. (u,v,d)\<in>set l) else \<infinity>"])
    by (auto intro: someI simp: distinct_map inj_on_def split: prod.splits; 
           blast)
  subgoal for w w'
    apply (simp add: fun_eq_iff)
    by (metis (mono_tags, hide_lams) not_enat_eq)
  done  

text \<open>We define this graph using determinate choice\<close>  
definition "wgraph_of_list l \<equiv> THE w. \<forall>u v d. w (u,v) = enat d \<longleftrightarrow> (u,v,d)\<in>set l"  

locale wgraph_from_list_algo = adt_wgraph 
begin

definition "from_list l \<equiv> fold (\<lambda>(u,v,d). add_edge (u,v) d) l empty_graph"

definition "edges_undef l w \<equiv> \<forall>u v d. (u,v,d)\<in>set l \<longrightarrow> w (u,v) = \<infinity>"  
  
lemma edges_undef_simps[simp]:
  "edges_undef [] w"  
  "edges_undef l (\<lambda>_. \<infinity>)"
  "edges_undef ((u,v,d)#l) w \<longleftrightarrow> edges_undef l w \<and> w (u,v) = \<infinity>"
  "edges_undef l (w((u,v) := enat d)) \<longleftrightarrow> edges_undef l w \<and> (\<forall>d'. (u,v,d')\<notin>set l)"  
  by (auto simp: edges_undef_def)

lemma from_list_correct_aux:
  assumes "valid_graph_rep l"
  assumes "edges_undef l (\<alpha> g)"
  assumes "invar g"
  defines "g' \<equiv> fold (\<lambda>(u,v,d). add_edge (u,v) d) l g"
  shows "invar g'"
    and "(\<forall>u v d. \<alpha> g' (u,v) = enat d \<longleftrightarrow> \<alpha> g (u,v) = enat d \<or> (u,v,d)\<in>set l)"
  using assms(1-3) unfolding g'_def
  apply (induction l arbitrary: g)
  by (auto simp: wgraph_specs split: if_splits)

lemma from_list_correct':
  assumes "valid_graph_rep l"
  shows "invar (from_list l)" 
    and "(u,v,d)\<in>set l \<longleftrightarrow> \<alpha> (from_list l) (u,v) = enat d"
  unfolding from_list_def 
  using from_list_correct_aux[OF assms, where g=empty_graph]
  by (auto simp: wgraph_specs)
  
lemma from_list_correct:
  assumes "valid_graph_rep l"
  shows "invar (from_list l)" "\<alpha> (from_list l) = wgraph_of_list l"
proof -
  from theI'[OF valid_graph_rep_ex1[OF assms], folded wgraph_of_list_def]
  have "(wgraph_of_list l (u, v) = enat d) = ((u, v, d) \<in> set l)" for u v d 
    by blast

  then show "\<alpha> (from_list l) = wgraph_of_list l" 
    using from_list_correct_aux[OF assms, where g=empty_graph]
    apply (clarsimp simp: fun_eq_iff wgraph_specs from_list_def)
    apply (metis (no_types) enat.exhaust)
    done
  
  show "invar (from_list l)"
    by (simp add: assms from_list_correct')
    
qed    
    
end



end
