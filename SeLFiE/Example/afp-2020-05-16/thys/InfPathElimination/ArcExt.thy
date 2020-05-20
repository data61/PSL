theory ArcExt
imports SubRel
begin

section \<open>Extending rooted graphs with edges\<close>

text \<open>In this section, we formalize the operation of adding to a rooted graph an edge whose source 
is already a vertex of the given graph but not its target. We call this operation an extension of the given graph by adding 
an edge. This corresponds to an abstraction of 
the act of adding an edge to the red part of a red\hyp{}black graph as a result of symbolic execution 
of the corresponding transition in the LTS under analysis, where all details about symbolic 
execution would have been abstracted.  We then state and prove a number of facts 
describing the evolution of the set of paths of the given graph, first without considering 
subsumption links then in the case of rooted graph equipped with a subsumption relation.\<close>

subsection \<open>Definition and Basic properties\<close>

text \<open>Extending a rooted graph with an edge consists in adding to its set of edges an edge whose 
source is a vertex of this graph but whose target is not.\<close>

abbreviation extends :: 
  "('v,'x) rgraph_scheme \<Rightarrow> 'v edge \<Rightarrow> ('v,'x) rgraph_scheme \<Rightarrow> bool" 
where
  "extends g e g' \<equiv> src e \<in> Graph.vertices g 
                  \<and> tgt e \<notin> Graph.vertices g 
                  \<and> g' = (add_edge g e)"



text \<open>After such an extension, the set of out-edges of the target of the new edge is empty.\<close>

lemma extends_tgt_out_edges :
  assumes "extends g e g'"
  shows   "out_edges g' (tgt e) = {}" 
using assms unfolding vertices_def image_def by force

text \<open>Consider a graph equipped with a sub-relation. This relation is also a sub-relation of any 
extension of this graph.\<close>

lemma (in sub_rel_of)
  assumes "extends g e g'"
  shows   "sub_rel_of g' subs"
using assms sub_rel_of by (auto simp add : sub_rel_of_def vertices_def)

text \<open>Extending a graph with an edge preserves the existing sub-paths.\<close>

lemma sp_in_extends :
  assumes "extends g e g'"
  assumes "Graph.subpath g  v1 es v2"
  shows   "Graph.subpath g' v1 es v2"
using assms by (auto simp add : Graph.subpath_def vertices_def)






subsection \<open>Extending trees\<close>

text \<open>We show that extending a rooted graph that is already a tree yields a new tree. Since 
the empty rooted graph is a tree, all graphs produced using only the extension by edge are trees.\<close>

lemma extends_is_tree :
  assumes "is_tree g"
  assumes "extends g e g'"
  shows   "is_tree g'"
unfolding is_tree_def Ball_def
proof (intro allI impI)
  fix v

  have "root g' = root g" using assms(2) by simp
  
  assume "v \<in> Graph.vertices g'"

  hence "v \<in> Graph.vertices g \<or> v = tgt e"
  using assms(2) by (auto simp add : vertices_def)

  thus "\<exists>!es. path g' es v"
  proof (elim disjE, goal_cases)
    case 1
    
    then obtain es 
    where "Graph.path g es v"
    and   "\<forall> es'. Graph.path g es' v \<longrightarrow> es' = es"
    using assms(1) unfolding Ex1_def is_tree_def by blast
  
    hence "Graph.path g' es v" 
    using assms(2) sp_in_extends[OF assms(2)]
    by (subst \<open>root g' = root g\<close>)
    
    moreover
    have "\<forall> es'. Graph.path g' es' v \<longrightarrow> es' =  es"
    proof (intro allI impI)
      fix es'
  
      assume "Graph.path g' es' v"
  
      thus "es' = es"
      proof (case_tac "e \<in> set es'", goal_cases)
        case 1
  
        then obtain es'' 
        where "es' = es'' @ [e]"
        and   "e \<notin> set es''" 
        using \<open>Graph.path g' es' v\<close>
              Graph.sp_through_de_decomp[OF extends_tgt_out_edges[OF assms(2)]]
        by blast
  
        hence "v = tgt e"
        using \<open>Graph.path g' es' v\<close> 
        by (simp add : Graph.sp_append_one)
  
        thus ?thesis 
        using assms(2) 
              Graph.lst_of_sp_is_vert[OF \<open>Graph.path g es v\<close>] 
        by simp
      next
        case 2 thus ?thesis 
        using assms 
              \<open>\<forall> es'. Graph.path g es' v \<longrightarrow> es' = es\<close> \<open>Graph.path g' es' v\<close>
        by (auto simp add : Graph.subpath_def vertices_def)
      qed
    qed

    ultimately
    show ?thesis by auto

  next
    case 2

    then obtain es 
    where "Graph.path g es (src e)"
    and   "\<forall> es'. Graph.path g es' (src e) \<longrightarrow> es' = es"
    using assms(1,2) unfolding is_tree_def by blast
  
    hence "Graph.path g' es (src e)" 
    using sp_in_extends[OF assms(2)] 
    by (subst \<open>root g' = root g\<close>)
  
    hence "Graph.path g' (es @ [e]) (tgt e)" 
    using assms(2) by (auto simp add : Graph.sp_append_one)
    
    moreover
    have "\<forall> es'. Graph.path g' es' (tgt e) \<longrightarrow> es' = es @ [e]"
    proof (intro allI impI)
      fix es'
  
      assume "Graph.path g' es' (tgt e)"
  
      moreover
      hence "e \<in> set es'" 
      using assms 
            sp_ends_in_tgt_imp_mem[of e g "root g" es']
      by (auto simp add : Graph.subpath_def vertices_def)
  
      moreover
      have   "out_edges g' (tgt e) = {}" 
      using assms 
      by (intro extends_tgt_out_edges)
  
      ultimately
      have "\<exists> es''. es' = es'' @ [e] \<and> e \<notin> set es''" 
      by (elim Graph.sp_through_de_decomp)
  
      then obtain es'' 
      where "es' = es'' @ [e]" 
      and   "e \<notin> set es''" 
      by blast
  
      hence "Graph.path g' es'' (src e)" 
      using \<open>Graph.path g' es'  (tgt e)\<close> 
      by (auto simp add : Graph.sp_append_one)
  
      hence "Graph.path g es'' (src e)"
      using assms(2) \<open>e \<notin> set es''\<close> 
      by (auto simp add : Graph.subpath_def vertices_def)
  
      hence "es'' = es" 
      using \<open>\<forall> as'. Graph.path g as' (src e) \<longrightarrow> as' = es\<close> 
      by simp
  
      thus "es' = es @ [e]" using \<open>es' = es'' @ [e]\<close> by simp
    qed
    
    ultimately
    show ?thesis using 2 by auto
  qed
qed



subsection \<open>Properties of sub-paths in an extension\<close>

text \<open>Extending a graph by an edge preserves the existing sub-paths.\<close>

lemma sp_in_extends_w_subs :
  assumes "extends g a g'"
  assumes "subpath g  v1 es v2 subs"
  shows   "subpath g' v1 es v2 subs"
using assms by (auto simp add : subpath_def sub_rel_of_def vertices_def)


text \<open>In an extension, the target of the new edge has no out-edges. Thus sub-paths of the 
extension starting and ending in old vertices are sub-paths of the graph prior to its extension.\<close>

lemma (in sub_rel_of) sp_from_old_verts_imp_sp_in_old :
  assumes "extends g e g'"
  assumes "v1 \<in> Graph.vertices g"
  assumes "v2 \<in> Graph.vertices g"
  assumes "subpath g' v1 es v2 subs"
  shows   "subpath g  v1 es v2 subs"
proof -
  have "e \<notin> set es"
  proof (intro notI)
    assume "e \<in> set es"
  
    have "v2 = tgt e"
    proof -
      have "tgt e \<notin> subsumees subs" using sub_rel_of assms(1) by fast
  
      moreover
      have  "out_edges g' (tgt e) = {}" using assms(1) by (rule extends_tgt_out_edges)
    
      ultimately
      have "\<exists> es'. es = es' @ [e] \<and> e \<notin> set es'" 
      using  assms(4) \<open>e \<in> set es\<close>
      by (intro sp_through_de_decomp)
    
      then obtain es' where "es = es' @ [e]" "e \<notin> set es'" by blast
  
      hence "tgt e = v2 \<or> (tgt e,v2) \<in> subs\<^sup>+"
      using assms(4) by (simp add : sp_append_one)
  
      thus ?thesis using \<open>tgt e \<notin> subsumees subs\<close> tranclD[of "tgt e" v2 subs] by force
    qed

    thus False using assms(1,3) by simp
  qed

  thus ?thesis 
  using sub_rel_of assms
  unfolding subpath_def sub_rel_of_def by auto
qed



text \<open>For the same reason, sub-paths starting at the target of the new edge are empty.\<close>

lemma (in sub_rel_of) sp_from_tgt_in_extends_is_Nil :
  assumes "extends g e g'"
  assumes "subpath g' (tgt e) es v subs"
  shows   "es = []"
using sub_rel_of assms
      extends_tgt_out_edges
      sp_from_de_empty[of "tgt e" subs g' es v]
by fast


text \<open>Moreover, a sub-path @{term es} starting in another vertex than the target of the new edge 
@{term e} but ending in this target has @{term e} as last element. This occurrence of @{term e} is 
unique among @{term es}. The prefix of @{term es} preceding @{term e} is a sub-path leading at the 
source of @{term e} in the original graph.\<close>

lemma (in sub_rel_of) sp_to_new_edge_tgt_imp :
  assumes "extends g e g'"
  assumes "subpath g' v es (tgt e) subs"
  assumes "v \<noteq> tgt e"
  shows   "\<exists> es'. es = es' @ [e] \<and> e \<notin> set es' \<and> subpath g v es' (src e) subs"
proof -
  obtain es' where "es = es' @ [e]" and "e \<notin> set es'" 
  using sub_rel_of assms(1,2,3)
        extends_tgt_out_edges[OF assms(1)]
        sp_through_de_decomp[of e subs g' v es "tgt e"]
        sp_ends_in_tgt_imp_mem[of e v es]
  by blast

  moreover
  have "subpath g v es' (src e) subs"
  proof -
    have "v \<in> Graph.vertices g" 
    using assms(1,3) fst_of_sp_is_vert[OF assms(2)] 
    by (auto simp add : vertices_def)

    moreover
    have "SubRel.subpath g' v es' (src e) subs" 
    using assms(2) \<open>es = es' @ [e]\<close> by (simp add : sp_append_one)

    ultimately 
    show ?thesis 
    using assms(1) sub_rel_of \<open>e \<notin> set es'\<close>
    unfolding subpath_def by (auto simp add : sub_rel_of_def)
  qed

  ultimately
  show ?thesis by blast
qed

end
