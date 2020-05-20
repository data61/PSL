theory FiniteListGraph
imports 
  FiniteGraph
  "Transitive-Closure.Transitive_Closure_List_Impl"
begin

section \<open>Specification of a finite graph, implemented by lists\<close>

text\<open>A graph \<open>G=(V,E)\<close> consits of a list of vertices @{term V}, also called nodes, 
       and a list of edges @{term E}. The edges are tuples of vertices.
       Using lists instead of sets, code can be easily created.\<close>

  record 'v list_graph =
    nodesL :: "'v list"
    edgesL :: "('v \<times>'v) list"

text\<open>Correspondence the FiniteGraph\<close>
  definition list_graph_to_graph :: "'v list_graph \<Rightarrow> 'v graph" where 
    "list_graph_to_graph G = \<lparr> nodes = set (nodesL G), edges = set (edgesL G) \<rparr>"


  definition wf_list_graph_axioms :: "'v list_graph \<Rightarrow> bool" where
    "wf_list_graph_axioms G \<longleftrightarrow> fst` set (edgesL G) \<subseteq> set (nodesL G) \<and> snd` set (edgesL G) \<subseteq> set (nodesL G)"


  lemma wf_list_graph_iff_wf_graph: "wf_graph (list_graph_to_graph G) \<longleftrightarrow> wf_list_graph_axioms G"
  unfolding list_graph_to_graph_def wf_graph_def wf_list_graph_axioms_def
  by simp

  text\<open>We say a @{typ "'v list_graph"} is valid if it fulfills the graph axioms and its lists are distinct\<close>
  definition wf_list_graph::"('v) list_graph \<Rightarrow> bool" where
   "wf_list_graph G = (distinct (nodesL G) \<and> distinct (edgesL G) \<and> wf_list_graph_axioms G)"


section\<open>FiniteListGraph operations\<close>

  text \<open>Adds a node to a graph.\<close>
  definition add_node :: "'v \<Rightarrow> 'v list_graph \<Rightarrow> 'v list_graph" where 
    "add_node v G = \<lparr> nodesL = (if v \<in> set (nodesL G) then nodesL G else v#nodesL G), edgesL=edgesL G \<rparr>"

  text \<open>Adds an edge to a graph.\<close>
  definition add_edge :: "'v \<Rightarrow> 'v \<Rightarrow> 'v list_graph \<Rightarrow> 'v list_graph" where 
    "add_edge v v' G = (add_node v (add_node v' G)) \<lparr>edgesL := (if (v, v') \<in> set (edgesL G) then edgesL G else (v, v')#edgesL G) \<rparr>"

  text \<open>Deletes a node from a graph. Also deletes all adjacent edges.\<close>
  definition delete_node :: "'v \<Rightarrow> 'v list_graph \<Rightarrow> 'v list_graph" where 
  "delete_node v G = \<lparr> 
    nodesL = remove1 v (nodesL G), edgesL = [(e1,e2) \<leftarrow> (edgesL G). e1 \<noteq> v \<and> e2 \<noteq> v]
    \<rparr>"

  text \<open>Deletes an edge from a graph.\<close>
  definition delete_edge :: "'v \<Rightarrow> 'v \<Rightarrow> 'v list_graph \<Rightarrow> 'v list_graph" where 
    "delete_edge v v' G = \<lparr>nodesL = nodesL G, edgesL = [(e1,e2) \<leftarrow> edgesL G. e1 \<noteq> v \<or> e2 \<noteq> v'] \<rparr>"

  
  fun delete_edges::"'v list_graph \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'v list_graph" where 
    "delete_edges G [] = G"|
    "delete_edges G ((v,v')#es) = delete_edges (delete_edge v v' G) es"



text \<open>extended graph operations\<close>
   text \<open>Reflexive transitive successors of a node. Or: All reachable nodes for v including v.\<close>
    definition succ_rtran :: "'v list_graph \<Rightarrow> 'v \<Rightarrow> 'v list" where
      "succ_rtran G v = rtrancl_list_impl (edgesL G) [v]"

   text \<open>Transitive successors of a node. Or: All reachable nodes for v.\<close>
    definition succ_tran :: "'v list_graph \<Rightarrow> 'v \<Rightarrow> 'v list" where
      "succ_tran G v = trancl_list_impl (edgesL G) [v]"
  
   text \<open>The number of reachable nodes from v\<close>
    definition num_reachable :: "'v list_graph \<Rightarrow> 'v \<Rightarrow> nat" where
      "num_reachable G v = length (succ_tran G v)"


    definition num_reachable_norefl :: "'v list_graph \<Rightarrow> 'v \<Rightarrow> nat" where
      "num_reachable_norefl G v = length ([ x \<leftarrow> succ_tran G v. x \<noteq> v])"


subsection\<open>undirected graph simulation\<close>
  text \<open>Create undirected graph from directed graph by adding backward links\<close>
  fun backlinks :: "('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list" where
    "backlinks [] = []" |
    "backlinks ((e1, e2)#es) = (e2, e1)#(backlinks es)"

  definition undirected :: "'v list_graph \<Rightarrow> 'v list_graph"
    where "undirected G \<equiv> \<lparr> nodesL = nodesL G, edgesL = remdups (edgesL G @ backlinks (edgesL G)) \<rparr>"

section\<open>Correctness lemmata\<close>

  \<comment> \<open>add node\<close>
  lemma add_node_wf: "wf_list_graph G \<Longrightarrow> wf_list_graph (add_node v G)"
  unfolding wf_list_graph_def wf_list_graph_axioms_def add_node_def
  by auto

  lemma add_node_set_nodes: "set (nodesL (add_node v G)) = set (nodesL G) \<union> {v}"
  unfolding add_node_def
  by auto

  lemma add_node_set_edges: "set (edgesL (add_node v G)) = set (edgesL G)"
  unfolding add_node_def
  by auto

  lemma add_node_correct: "FiniteGraph.add_node v (list_graph_to_graph G) = list_graph_to_graph (add_node v G)"
  unfolding FiniteGraph.add_node_def list_graph_to_graph_def
  by (simp add: add_node_set_edges add_node_set_nodes)

  lemma add_node_wf2: "wf_graph (list_graph_to_graph G) \<Longrightarrow> wf_graph (list_graph_to_graph (add_node v G))"
  by (subst add_node_correct[symmetric]) simp

  \<comment> \<open>add edge\<close>
  lemma add_edge_wf: "wf_list_graph G \<Longrightarrow> wf_list_graph (add_edge v v' G)"
  unfolding wf_list_graph_def add_edge_def add_node_def wf_list_graph_axioms_def
  by auto

  lemma add_edge_set_nodes: "set (nodesL (add_edge v v' G)) = set (nodesL G) \<union> {v,v'}"
  unfolding add_edge_def add_node_def
  by auto

  lemma add_edge_set_edges: "set (edgesL (add_edge v v' G)) = set (edgesL G) \<union> {(v,v')}"
  unfolding add_edge_def add_node_def
  by auto

  lemma add_edge_correct: "FiniteGraph.add_edge v v' (list_graph_to_graph G) = list_graph_to_graph (add_edge v v' G)"
  unfolding FiniteGraph.add_edge_def add_edge_def list_graph_to_graph_def
  by (auto simp: add_node_set_nodes)

  lemma add_edge_wf2: "wf_graph (list_graph_to_graph G) \<Longrightarrow> wf_graph (list_graph_to_graph (add_edge v v' G))"
  by (subst add_edge_correct[symmetric]) simp

  \<comment> \<open>delete node\<close>
  lemma delete_node_wf: "wf_list_graph G \<Longrightarrow> wf_list_graph (delete_node v G)"
  unfolding wf_list_graph_def delete_node_def wf_list_graph_axioms_def
  by auto

  lemma delete_node_set_edges:
    "set (edgesL (delete_node v G)) = {(a,b). (a, b) \<in> set (edgesL G) \<and> a \<noteq> v \<and> b \<noteq> v}"
  unfolding delete_node_def
  by auto

  lemma delete_node_correct:
    assumes "wf_list_graph G"
    shows "FiniteGraph.delete_node v (list_graph_to_graph G) = list_graph_to_graph (delete_node v G)"
  using assms
  unfolding FiniteGraph.delete_node_def delete_node_def list_graph_to_graph_def wf_list_graph_def
  by auto

  \<comment> \<open>delete edge\<close>
  lemma delete_edge_set_nodes: "set (nodesL (delete_edge v v' G)) = set (nodesL G)"
  unfolding delete_edge_def
  by simp

  lemma delete_edge_set_edges:
    "set (edgesL (delete_edge v v' G)) = {(a,b). (a,b) \<in> set (edgesL G) \<and> (a,b) \<noteq> (v,v')}"
  unfolding delete_edge_def
  by auto

  lemma delete_edge_set_edges2:
    "set (edgesL (delete_edge v v' G)) = set (edgesL G) - {(v,v')}"
  by (auto simp:delete_edge_set_edges)

  lemma delete_edge_wf: "wf_list_graph G \<Longrightarrow> wf_list_graph (delete_edge v v' G)"
  unfolding wf_list_graph_def delete_edge_def wf_list_graph_axioms_def
  by auto
    
  lemma delete_edge_length: "length (edgesL (delete_edge v v' G)) \<le> length (edgesL G)"
  unfolding delete_edge_def
  by simp

  lemma delete_edge_commute: "delete_edge a1 a2 (delete_edge b1 b2 G) = delete_edge b1 b2 (delete_edge a1 a2 G)"
  unfolding delete_edge_def
  by simp metis (* auto doesn't seem to like filter_cong *)

  lemma delete_edge_correct: "FiniteGraph.delete_edge v v' (list_graph_to_graph G) = list_graph_to_graph (delete_edge v v' G)"
  unfolding FiniteGraph.delete_edge_def delete_edge_def list_graph_to_graph_def
  by auto

  lemma delete_edge_wf2: "wf_graph (list_graph_to_graph G) \<Longrightarrow> wf_graph (list_graph_to_graph (delete_edge v v' G))"
  by (subst delete_edge_correct[symmetric]) simp

  \<comment> \<open>delete edges\<close>
  lemma delete_edges_wf: "wf_list_graph G \<Longrightarrow> wf_list_graph (delete_edges G E)"
  by (induction E arbitrary: G) (auto simp: delete_edge_wf)

  lemma delete_edges_set_nodes: "set (nodesL (delete_edges G E)) = set (nodesL G)"
  by (induction E arbitrary: G) (auto simp: delete_edge_set_nodes)

  lemma delete_edges_nodes: "nodesL (delete_edges G es) = nodesL G"
  by (induction es arbitrary: G) (auto simp: delete_edge_def)

  lemma delete_edges_set_edges: "set (edgesL (delete_edges G E)) = set (edgesL G) - set E"
  by (induction E arbitrary: G) (auto simp: delete_edge_def delete_edge_set_nodes)

  lemma delete_edges_set_edges2:
    "set (edgesL (delete_edges G E)) = {(a,b). (a,b) \<in> set (edgesL G) \<and> (a,b) \<notin> set E}"
  by (auto simp: delete_edges_set_edges)

  lemma delete_edges_length: "length (edgesL (delete_edges G f)) \<le> length (edgesL G)"
  proof (induction f arbitrary:G)
    case (Cons f fs)
    thus ?case
      apply (cases f, hypsubst)
      apply (subst delete_edges.simps(2))
      apply (metis delete_edge_length le_trans)
      done
  qed simp

  lemma delete_edges_chain: "delete_edges G (as @ bs) = delete_edges (delete_edges G as) bs"
  proof (induction as arbitrary: bs G)
    case (Cons f fs)
    thus ?case
      by (cases f) auto
  qed simp

  lemma delete_edges_delete_edge_commute:
    "delete_edges (delete_edge a1 a2 G) as = delete_edge a1 a2 (delete_edges G as)"
  proof (induction as arbitrary: G a1 a2)
    case (Cons f fs)
    thus ?case
      by (cases f) (simp add: delete_edge_commute)
  qed simp

  lemma delete_edges_commute:
    "delete_edges (delete_edges G as) bs = delete_edges (delete_edges G bs) as"
  proof (induction as arbitrary: bs G)
    case (Cons f fs)
    thus ?case
      by (cases f) (simp add: delete_edges_delete_edge_commute)
  qed simp

  lemma delete_edges_as_filter:
    "delete_edges G l = \<lparr> nodesL = nodesL G,  edgesL = [x \<leftarrow> edgesL G. x \<notin> set l] \<rparr>"
  proof (induction l)
    case (Cons f fs)
    thus ?case
      apply (cases f)
      apply (simp add: delete_edges_delete_edge_commute)
      apply (simp add: delete_edge_def)
      apply (metis (lifting, full_types) prod.exhaust case_prodI split_conv)
      done
  qed simp

  declare delete_edges.simps[simp del] (*do not automatically expand definition*)

  lemma delete_edges_correct:
    "FiniteGraph.delete_edges (list_graph_to_graph G) (set E) = list_graph_to_graph (delete_edges G E)"
  unfolding list_graph_to_graph_def FiniteGraph.delete_edges_def
  by (auto simp add: delete_edges_as_filter )
  
  lemma delete_edges_wf2:
    "wf_graph (list_graph_to_graph G) \<Longrightarrow> wf_graph (list_graph_to_graph (delete_edges G E))"
  by (subst delete_edges_correct[symmetric]) simp

  \<comment> \<open>helper about reflexive transitive closure impl\<close>
  lemma distinct_relpow_impl:
    "distinct L \<Longrightarrow> distinct new \<Longrightarrow> distinct have \<Longrightarrow> distinct (new@have) \<Longrightarrow> 
     distinct (relpow_impl (\<lambda>as. remdups (map snd [(a, b)\<leftarrow>L . a \<in> set as])) (\<lambda>xs ys. [x\<leftarrow>xs . x \<notin> set ys] @ ys) (\<lambda>x xs. x \<in> set xs) new have M)"
  proof (induction M arbitrary: "new" "have")
    case Suc
    hence
      "distinct ([x\<leftarrow>new . x \<notin> set have] @ have)"
      "set ([n\<leftarrow>remdups (map snd [(a, b)\<leftarrow>L . a \<in> set new]) . (n \<in> set new \<longrightarrow> n \<in> set have) \<and> n \<notin> set have]) \<inter> set ([x\<leftarrow>new . x \<notin> set have] @ have) = {}"
      by auto

    with Suc show ?case
      by auto
  qed auto

  lemma distinct_rtrancl_list_impl: "distinct L \<Longrightarrow> distinct ls \<Longrightarrow> distinct (rtrancl_list_impl L ls)"
  unfolding rtrancl_list_impl_def rtrancl_impl_def
  by (simp add:distinct_relpow_impl)

  lemma distinct_trancl_list_impl: "distinct L \<Longrightarrow> distinct ls \<Longrightarrow> distinct (trancl_list_impl L ls)"
  unfolding trancl_list_impl_def trancl_impl_def
  by (simp add:distinct_relpow_impl)

  \<comment> \<open>succ rtran\<close>
  value "succ_rtran \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr> 1"

  lemma succ_rtran_correct: "FiniteGraph.succ_rtran (list_graph_to_graph G) v = set (succ_rtran G v)"
  unfolding FiniteGraph.succ_rtran_def succ_rtran_def list_graph_to_graph_def
  by (simp add: rtrancl_list_impl)

  lemma distinct_succ_rtran: "wf_list_graph G \<Longrightarrow> distinct (succ_rtran G v)"
  unfolding succ_rtran_def wf_list_graph_def
  by (auto intro: distinct_rtrancl_list_impl)

  lemma succ_rtran_set: "set (succ_rtran G v) = {e2. (v,e2) \<in> (set (edgesL G))\<^sup>*}"
  unfolding succ_rtran_def
  by (simp add: rtrancl_list_impl)

  \<comment> \<open>succ tran\<close>
  lemma distinct_succ_tran: "wf_list_graph G \<Longrightarrow> distinct (succ_tran G v)"
  unfolding succ_tran_def wf_list_graph_def
  by (auto intro: distinct_trancl_list_impl)

  lemma succ_tran_set: "set (succ_tran G v) = {e2. (v,e2) \<in> (set (edgesL G))\<^sup>+}"
  unfolding succ_tran_def
  by (simp add: trancl_list_impl)

  value "succ_tran \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr> 1"

  lemma succ_tran_correct: "FiniteGraph.succ_tran (list_graph_to_graph G) v = set (succ_tran G v)"
  unfolding FiniteGraph.succ_tran_def succ_tran_def list_graph_to_graph_def
  by (simp add:trancl_list_impl)
  
  \<comment> \<open>num_reachable\<close>
  lemma num_reachable_correct:
    "wf_list_graph G \<Longrightarrow> FiniteGraph.num_reachable (list_graph_to_graph G) v = num_reachable G v"
  unfolding num_reachable_def FiniteGraph.num_reachable_def
  by (metis List.distinct_card distinct_succ_tran succ_tran_correct)

  \<comment> \<open>num_reachable_norefl\<close>
  lemma num_reachable_norefl_correct:
    "wf_list_graph G \<Longrightarrow> 
     FiniteGraph.num_reachable_norefl (list_graph_to_graph G) v = num_reachable_norefl G v"
 unfolding num_reachable_norefl_def FiniteGraph.num_reachable_norefl_def
 by (metis (full_types) List.distinct_card distinct_filter distinct_succ_tran set_minus_filter_out succ_tran_correct)

  \<comment> \<open>backlinks, i.e. backflows in formal def\<close>
  lemma backlinks_alt: "backlinks E = [(snd e, fst e). e \<leftarrow> E]"
  by (induction E) auto

  lemma backlinks_set: "set (backlinks E) = {(e2, e1). (e1, e2) \<in> set E}"
  by (induction E) auto

  lemma undirected_nodes_set: "set (edgesL (undirected G)) = set (edgesL G) \<union> {(e2, e1). (e1, e2) \<in> set (edgesL G)}"
  unfolding undirected_def
  by (simp add: backlinks_set)

  lemma undirected_succ_tran_set: "set (succ_tran (undirected G) v) = {e2. (v,e2) \<in> (set (edgesL (undirected G)))\<^sup>+}"
  by (fact succ_tran_set)

  lemma backlinks_in_nodes_G: "\<lbrakk> fst ` set (edgesL G) \<subseteq> set (nodesL G); snd ` set (edgesL G) \<subseteq> set (nodesL G) \<rbrakk> \<Longrightarrow> 
    fst` set (edgesL (undirected G)) \<subseteq> set (nodesL (undirected G)) \<and> snd` set (edgesL (undirected G)) \<subseteq> set (nodesL (undirected G))"
  unfolding undirected_def
  by(auto simp: backlinks_set)

  lemma backlinks_distinct: "distinct E \<Longrightarrow> distinct (backlinks E)"
  by (induction E) (auto simp: backlinks_alt)

  lemma backlinks_subset: "set (backlinks X) \<subseteq> set (backlinks Y) \<longleftrightarrow> set X \<subseteq> set Y"
  by (auto simp: backlinks_set)

  lemma backlinks_correct: "FiniteGraph.backflows (set E) = set (backlinks E)"
  unfolding backflows_def
  by(simp add: backlinks_set)

  \<comment> \<open>undirected\<close>
  lemma undirected_wf: "wf_list_graph G \<Longrightarrow> wf_list_graph (undirected G)"
  unfolding wf_list_graph_def wf_list_graph_axioms_def
  by (simp add:backlinks_in_nodes_G) (simp add: undirected_def)

  lemma undirected_correct: 
    "FiniteGraph.undirected (list_graph_to_graph G) = list_graph_to_graph (undirected G)"
  unfolding FiniteGraph.undirected_def undirected_def list_graph_to_graph_def
  by (simp add: backlinks_set)
      
lemmas wf_list_graph_wf =
  add_node_wf
  add_edge_wf
  delete_node_wf
  delete_edge_wf
  delete_edges_wf
  undirected_wf

lemmas list_graph_correct =
  add_node_correct
  add_edge_correct
  delete_node_correct
  delete_edge_correct
  delete_edges_correct
  succ_rtran_correct
  succ_tran_correct
  num_reachable_correct
  undirected_correct


end
