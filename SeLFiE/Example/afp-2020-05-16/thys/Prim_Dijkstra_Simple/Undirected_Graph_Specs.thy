section \<open>Abstract Graph Datatype\<close>
theory Undirected_Graph_Specs
imports Undirected_Graph
begin

subsection \<open>Abstract Weighted Graph\<close>

locale adt_wgraph =
  fixes \<alpha>w :: "'g \<Rightarrow> 'v set \<Rightarrow> nat" and \<alpha>g :: "'g \<Rightarrow> 'v ugraph"
    and invar :: "'g \<Rightarrow> bool"
    and adj :: "'g \<Rightarrow> 'v \<Rightarrow> ('v\<times>nat) list"
    and empty :: 'g
    and add_edge :: "'v\<times>'v \<Rightarrow> nat \<Rightarrow> 'g \<Rightarrow> 'g"
  assumes adj_correct: "invar g 
    \<Longrightarrow> set (adj g u) = {(v,d). (u,v)\<in>edges (\<alpha>g g) \<and> \<alpha>w g {u,v} = d}"
  assumes empty_correct:
    "invar empty"
    "\<alpha>g empty = graph_empty"
    "\<alpha>w empty = (\<lambda>_. 0)"
  assumes add_edge_correct:
    "\<lbrakk>invar g; (u,v)\<notin>edges (\<alpha>g g); u\<noteq>v\<rbrakk> \<Longrightarrow> invar (add_edge (u,v) d g)"
    "\<lbrakk>invar g; (u,v)\<notin>edges (\<alpha>g g); u\<noteq>v\<rbrakk> 
      \<Longrightarrow> \<alpha>g (add_edge (u,v) d g) = ins_edge (u,v) (\<alpha>g g)"
    "\<lbrakk>invar g; (u,v)\<notin>edges (\<alpha>g g); u\<noteq>v\<rbrakk> 
      \<Longrightarrow> \<alpha>w (add_edge (u,v) d g) = (\<alpha>w g)({u,v}:=d)"
  
begin

lemmas wgraph_specs = adj_correct empty_correct add_edge_correct

lemma empty_spec_presentation: 
  "invar empty \<and> \<alpha>g empty = graph {} {} \<and> \<alpha>w empty = (\<lambda>_. 0)"
  by (auto simp: wgraph_specs)

lemma add_edge_spec_presentation:
  "\<lbrakk>invar g; (u,v)\<notin>edges (\<alpha>g g); u\<noteq>v\<rbrakk> \<Longrightarrow>
    invar (add_edge (u,v) d g)
  \<and> \<alpha>g (add_edge (u,v) d g) = ins_edge (u,v) (\<alpha>g g)
  \<and> \<alpha>w (add_edge (u,v) d g) = (\<alpha>w g)({u,v}:=d)"
  by (auto simp: wgraph_specs)
    
end



subsection \<open>Generic From-List Algorithm\<close>

definition valid_graph_repr :: "('v\<times>'v) list \<Rightarrow> bool" 
  where "valid_graph_repr l \<longleftrightarrow> (\<forall>(u,v)\<in>set l. u\<noteq>v)"
  
definition graph_from_list :: "('v\<times>'v) list \<Rightarrow> 'v ugraph"
  where "graph_from_list l = foldr ins_edge l graph_empty"

lemma graph_from_list_foldl: "graph_from_list l = fold ins_edge l graph_empty"  
  unfolding graph_from_list_def
  apply (rule foldr_fold[THEN fun_cong])
  by (auto simp: fun_eq_iff graph_eq_iff edges_ins_edge)

  
lemma nodes_of_graph_from_list: "nodes (graph_from_list l) = fst`set l \<union> snd`set l"
  apply (induction l)
  unfolding graph_from_list_def
  by auto

lemma edges_of_graph_from_list: 
  assumes valid: "valid_graph_repr l"
  shows "edges (graph_from_list l) = set l \<union> (set l)\<inverse>"
  using valid apply (induction l)
  unfolding graph_from_list_def valid_graph_repr_def
  by auto



definition "valid_weight_repr l \<equiv> distinct (map (uedge o fst) l)"
  
definition weight_from_list :: "(('v\<times>'v)\<times>nat) list \<Rightarrow> 'v set \<Rightarrow> nat" where
  "weight_from_list l \<equiv> foldr (\<lambda>((u,v),d) w. w({u,v}:=d)) l (\<lambda>_. 0)"

lemma graph_from_list_simps:
  "graph_from_list [] = graph_empty"
  "graph_from_list ((u,v)#l) = ins_edge (u,v) (graph_from_list l)"
  by (auto simp: graph_from_list_def)

lemma weight_from_list_simps:
  "weight_from_list [] = (\<lambda>_. 0)"  
  "weight_from_list (((u,v),d)#xs) = (weight_from_list xs)({u,v}:=d)"
  by (auto simp: weight_from_list_def)
  
lemma valid_graph_repr_simps:
  "valid_graph_repr []"
  "valid_graph_repr ((u,v)#xs) \<longleftrightarrow> u\<noteq>v \<and> valid_graph_repr xs"
  unfolding valid_graph_repr_def by auto

lemma valid_weight_repr_simps:
  "valid_weight_repr []"  
  "valid_weight_repr (((u,v),w)#xs) 
    \<longleftrightarrow> uedge (u,v)\<notin>uedge`fst`set xs \<and> valid_weight_repr xs"
  unfolding valid_weight_repr_def
  by (force simp: uedge_def doubleton_eq_iff)+
  
  
lemma weight_from_list_correct: 
  assumes "valid_weight_repr l"
  assumes "((u,v),d)\<in>set l"
  shows "weight_from_list l {u,v} = d"
proof -
  from assms show ?thesis  
    apply (induction l)
    unfolding valid_weight_repr_def weight_from_list_def
    subgoal by simp
    by (force simp: doubleton_eq_iff)
    
qed    
    
  

context adt_wgraph 
begin
  
definition "valid_wgraph_repr l 
  \<longleftrightarrow> valid_graph_repr (map fst l) \<and> valid_weight_repr l"

definition "from_list l = foldr (\<lambda>(e,d). add_edge e d) l empty"


lemma from_list_refine: "valid_wgraph_repr l \<Longrightarrow> 
    invar (from_list l) 
  \<and> \<alpha>g (from_list l) = graph_from_list (map fst l)
  \<and> \<alpha>w (from_list l) = weight_from_list l"
  unfolding from_list_def valid_wgraph_repr_def
  supply [simp] = wgraph_specs graph_from_list_simps weight_from_list_simps
  apply (induction l) 
  subgoal by auto
  subgoal by (
      intro conjI; 
      clarsimp 
        simp: uedge_def valid_graph_repr_simps valid_weight_repr_simps
        split: prod.splits;
      subst wgraph_specs; 
      auto simp: edges_of_graph_from_list
    )
  done  

lemma from_list_correct: 
  assumes "valid_wgraph_repr l"  
  shows 
    "invar (from_list l)"
    "nodes (\<alpha>g (from_list l)) = fst`fst`set l \<union> snd`fst`set l"
    "edges (\<alpha>g (from_list l)) = (fst`set l) \<union> (fst`set l)\<inverse>"
    "((u,v),d)\<in>set l \<Longrightarrow> \<alpha>w (from_list l) {u,v} = d"
    apply (simp_all add: from_list_refine[OF assms])
    using assms unfolding valid_wgraph_repr_def
    apply (simp_all add: 
      edges_of_graph_from_list nodes_of_graph_from_list weight_from_list_correct)
    done
  
lemma valid_wgraph_repr_presentation: "valid_wgraph_repr l \<longleftrightarrow> 
  (\<forall>((u,v),d)\<in>set l. u\<noteq>v) \<and> distinct [ {u,v}. ((u,v),d)\<leftarrow>l ]"
proof -
  have [simp]: "uedge \<circ> fst = (\<lambda>((u, v), w). {u, v})"
    unfolding uedge_def by auto
  show ?thesis
    unfolding valid_wgraph_repr_def valid_graph_repr_def valid_weight_repr_def
    by (auto split: prod.splits)
qed  
    
lemma from_list_correct_presentation:
  assumes "valid_wgraph_repr l"  
  shows "let gi=from_list l; g=\<alpha>g gi; w=\<alpha>w gi in
      invar gi 
    \<and> nodes g = \<Union>{{u,v} | u v. \<exists>d. ((u,v),d)\<in>set l}
    \<and> edges g = \<Union>{{(u,v),(v,u)} | u v. \<exists>d. ((u,v),d)\<in>set l}
    \<and> (\<forall>((u,v),d)\<in>set l. w {u,v}=d)
  "  
  unfolding Let_def from_list_correct(2-3)[OF assms]
  apply (intro conjI)
  subgoal by (simp add: from_list_correct(1)[OF assms])
  subgoal by (auto 0 0 simp: in_set_conv_decomp; blast)
  subgoal by (auto 0 0 simp: in_set_conv_decomp; blast) 
  subgoal using from_list_correct(4)[OF assms] by auto
  done
    
end

end
