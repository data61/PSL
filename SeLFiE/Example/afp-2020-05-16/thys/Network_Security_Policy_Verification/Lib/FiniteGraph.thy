theory FiniteGraph
imports Main 
begin

(*Lots of this theory is based on a work by Benedikt Nordhoff and Peter Lammich*)

section \<open>Specification of a finite directed graph\<close>

text\<open>A graph \<open>G=(V,E)\<close> consits of a set of vertices \<open>V\<close>, also called nodes, 
       and a set of edges \<open>E\<close>. The edges are tuples of vertices. Both, 
       the set of vertices and edges is finite.\<close>

(* Inspired by
Title: Dijkstra's Shortest Path Algorithm
Author: Benedikt Nordhoff and Peter Lammich
http://isa-afp.org/entries/Dijkstra_Shortest_Path.shtml
*)

section \<open>Graph\<close>
subsection\<open>Definitions\<close>
  text \<open>A graph is represented by a record.\<close>
  record 'v graph =
    nodes :: "'v set"
    edges :: "('v \<times>'v) set"

  text \<open>In a well-formed graph, edges only go from nodes to nodes.\<close>
  locale wf_graph = 
    fixes G :: "'v graph"
    \<comment> \<open>Edges only reference to existing nodes\<close>
    assumes E_wf: "fst ` (edges G) \<subseteq> (nodes G)"
                     "snd ` (edges G) \<subseteq> (nodes G)"
    and finiteE: "finite (edges G)" (*implied by finiteV*)
    and finiteV: "finite (nodes G)"
  begin
    abbreviation "V \<equiv> (nodes G)"
    abbreviation "E \<equiv> (edges G)"

    lemma E_wfD: assumes "(v,v') \<in> E"
      shows "v \<in> V" "v' \<in> V"
      apply -
       apply (rule subsetD[OF E_wf(1)])
       using assms apply force
      apply (rule subsetD[OF E_wf(2)])
      using assms apply force
      done

    lemma E_wfD2: "\<forall>e \<in> E. fst e \<in> V \<and> snd e \<in> V"
    by (auto simp add: E_wfD)
  end

subsection \<open>Basic operations on Graphs\<close>
  text \<open>The empty graph.\<close>
  definition empty :: "'v graph" where 
    "empty \<equiv> \<lparr> nodes = {}, edges = {} \<rparr>"

  text \<open>Adds a node to a graph.\<close>
  definition add_node :: "'v \<Rightarrow> 'v graph \<Rightarrow> 'v graph" where 
    "add_node v G \<equiv> \<lparr> nodes = ({v} \<union> (nodes G)), edges=edges G \<rparr>"

  text \<open>Deletes a node from a graph. Also deletes all adjacent edges.\<close>
  definition delete_node where "delete_node v G \<equiv> \<lparr> 
      nodes = (nodes G) - {v},   
      edges = {(e1, e2). (e1, e2) \<in> edges G \<and> e1 \<noteq> v \<and> e2 \<noteq> v}
    \<rparr>"

  text \<open>Adds an edge to a graph.\<close>
  definition add_edge where 
  "add_edge v v' G = \<lparr>nodes = nodes G \<union> {v,v'}, edges = {(v, v')} \<union> edges G \<rparr>"

  text \<open>Deletes an edge from a graph.\<close>
  definition delete_edge where "delete_edge v v' G \<equiv> \<lparr>
      nodes = nodes G, 
      edges = {(e1,e2). (e1, e2) \<in> edges G \<and> (e1,e2) \<noteq> (v,v')}
    \<rparr>"
  
  definition delete_edges::"'v graph \<Rightarrow> ('v \<times> 'v) set \<Rightarrow> 'v graph" where 
    "delete_edges G es \<equiv> \<lparr>
      nodes = nodes G, 
      edges = {(e1,e2). (e1, e2) \<in> edges G \<and> (e1,e2) \<notin> es}
    \<rparr>"

  fun delete_edges_list::"'v graph \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'v graph" where 
    "delete_edges_list G [] = G"|
    "delete_edges_list G ((v,v')#es) = delete_edges_list (delete_edge v v' G) es"

  definition fully_connected :: "'v graph \<Rightarrow> 'v graph" where
    "fully_connected G \<equiv> \<lparr>nodes = nodes G, edges = nodes G \<times> nodes G \<rparr>"


text \<open>Extended graph operations\<close>
  text \<open>Reflexive transitive successors of a node. Or: All reachable nodes for \<open>v\<close> including \<open>v\<close>.\<close>
  definition succ_rtran :: "'v graph \<Rightarrow> 'v \<Rightarrow> 'v set" where
    "succ_rtran G v = {e2. (v,e2) \<in> (edges G)\<^sup>*}"

  text \<open>Transitive successors of a node. Or: All reachable nodes for \<open>v\<close>.\<close>
  definition succ_tran :: "'v graph \<Rightarrow> 'v \<Rightarrow> 'v set" where
    "succ_tran G v = {e2. (v,e2) \<in> (edges G)\<^sup>+}"

  \<comment> \<open>succ_tran is always finite\<close>
  lemma succ_tran_finite: "wf_graph G \<Longrightarrow> finite (succ_tran G v)"
  proof -
    assume "wf_graph G"
    from wf_graph.finiteE[OF this] have "finite ((edges G)\<^sup>+)" using finite_trancl[symmetric, of "edges G"] by metis
    from this have "finite {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+}" by simp
    from this have finite: "finite (snd ` {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+})" by (metis finite_imageI)
    have "{(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+ \<and> e1 = v} \<subseteq> {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+}" by blast
    have 1: "snd ` {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+ \<and> e1 = v} \<subseteq> snd ` {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+}" by blast
    have 2: "snd ` {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+ \<and> e1 = v} = {e2. (v,e2) \<in> (edges G)\<^sup>+}" by force
    from 1 2 have "{e2. (v,e2) \<in> (edges G)\<^sup>+} \<subseteq> snd ` {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+}" by blast
    from this finite have "finite {e2. (v, e2) \<in> (edges G)\<^sup>+}" by (metis finite_subset)
    thus "finite (succ_tran G v)" using succ_tran_def by metis
  qed
  
  text\<open>If there is no edge leaving from \<open>v\<close>, then \<open>v\<close> has no successors\<close>
  lemma succ_tran_empty: "\<lbrakk> wf_graph G; v \<notin> (fst ` edges G) \<rbrakk> \<Longrightarrow> succ_tran G v = {}"
    unfolding succ_tran_def using image_iff tranclD by fastforce

  text\<open>@{const succ_tran} is subset of nodes\<close>
  lemma succ_tran_subseteq_nodes: "\<lbrakk> wf_graph G \<rbrakk> \<Longrightarrow> succ_tran G v \<subseteq> nodes G"
    unfolding succ_tran_def using tranclD2 wf_graph.E_wfD(2) by fastforce

  text \<open>The number of reachable nodes from \<open>v\<close>\<close>
  definition num_reachable :: "'v graph \<Rightarrow> 'v \<Rightarrow> nat" where
    "num_reachable G v = card (succ_tran G v)"

  definition num_reachable_norefl :: "'v graph \<Rightarrow> 'v \<Rightarrow> nat" where
    "num_reachable_norefl G v = card (succ_tran G v - {v})"

  text\<open>@{const card} returns @{term 0} for infinite sets.
        Here, for a well-formed graph, if @{const num_reachable} is zero, there are actually no nodes reachable.\<close>
  lemma num_reachable_zero: "\<lbrakk>wf_graph G; num_reachable G v = 0\<rbrakk> \<Longrightarrow> succ_tran G v = {}"
  unfolding num_reachable_def
  apply(subgoal_tac "finite (succ_tran G v)")
   apply(simp)
  apply(blast intro: succ_tran_finite)
  done
  lemma num_succtran_zero: "\<lbrakk>succ_tran G v = {}\<rbrakk> \<Longrightarrow> num_reachable G v = 0"
    unfolding num_reachable_def by simp
  lemma num_reachable_zero_iff: "\<lbrakk>wf_graph G\<rbrakk> \<Longrightarrow> (num_reachable G v = 0) \<longleftrightarrow> (succ_tran G v = {})"
  by(metis num_succtran_zero num_reachable_zero)


section\<open>Undirected Graph\<close>

subsection\<open>undirected graph simulation\<close>
  text \<open>Create undirected graph from directed graph by adding backward links\<close>

  definition backflows :: "('v \<times> 'v) set \<Rightarrow> ('v \<times> 'v) set" where
    "backflows E \<equiv> {(r,s). (s,r) \<in> E}"

  definition undirected :: "'v graph \<Rightarrow> 'v graph"
    where "undirected G = \<lparr> nodes = nodes G, edges = (edges G) \<union> {(b,a). (a,b) \<in> edges G} \<rparr>"

section \<open>Graph Lemmas\<close>

  lemma graph_eq_intro: "(nodes (G::'a graph) = nodes G') \<Longrightarrow> (edges G = edges G') \<Longrightarrow> G = G'" by simp

  \<comment> \<open>finite\<close>
  lemma wf_graph_finite_filterE: "wf_graph G \<Longrightarrow> finite {(e1, e2). (e1, e2) \<in> edges G \<and> P e1 e2}"
  by(simp add: wf_graph.finiteE split_def)
  lemma wf_graph_finite_filterV: "wf_graph G \<Longrightarrow> finite {n. n \<in> nodes G \<and> P n}"
  by(simp add: wf_graph.finiteV)

  \<comment> \<open>empty\<close>
  lemma empty_wf[simp]: "wf_graph empty"
    unfolding empty_def by unfold_locales auto
  lemma nodes_empty[simp]: "nodes empty = {}" unfolding empty_def by simp
  lemma edges_empty[simp]: "edges empty = {}" unfolding empty_def by simp

  \<comment> \<open>add node\<close>
  lemma add_node_wf[simp]: "wf_graph g \<Longrightarrow> wf_graph (add_node v g)"
    unfolding add_node_def wf_graph_def by (auto)

  lemma delete_node_wf[simp]: "wf_graph G \<Longrightarrow> wf_graph (delete_node v G)"
    by(auto simp add: delete_node_def wf_graph_def wf_graph_finite_filterE)

  \<comment> \<open>add edgde\<close>
  lemma add_edge_wf[simp]: "wf_graph G \<Longrightarrow> wf_graph (add_edge v v' G)"
    by(auto simp add: add_edge_def add_node_def wf_graph_def)

  \<comment> \<open>delete edge\<close>
  lemma delete_edge_wf[simp]: "wf_graph G \<Longrightarrow> wf_graph (delete_edge v v' G)"
    by(auto simp add: delete_edge_def add_node_def wf_graph_def split_def)
 
  \<comment> \<open>delte edges\<close>
  lemma delete_edges_list_wf[simp]: "wf_graph G \<Longrightarrow> wf_graph (delete_edges_list G E)"
    by(induction E arbitrary: G, simp, force)
  lemma delete_edges_wf[simp]: "wf_graph G \<Longrightarrow> wf_graph (delete_edges G E)"
    by(auto simp add: delete_edges_def add_node_def wf_graph_def split_def)
  lemma delete_edges_list_set: "delete_edges_list G E = delete_edges G (set E)"
    proof(induction E arbitrary: G)
    case Nil thus ?case by (simp add: delete_edges_def)
    next
    case (Cons e E) thus ?case by(cases e)(simp add: delete_edge_def delete_edges_def)
    qed
  lemma delete_edges_list_union: "delete_edges_list G (ff @ keeps) = delete_edges G (set ff \<union> set keeps)"
   by(simp add: delete_edges_list_set)
  lemma add_edge_delete_edges_list: 
    "(add_edge (fst a) (snd a) (delete_edges_list G (a # ff))) = (add_edge (fst a) (snd a) (delete_edges G (set ff)))"
   by(auto simp add: delete_edges_list_set delete_edges_def add_edge_def add_node_def)
  lemma delete_edges_empty[simp]: "delete_edges G {} = G"
   by(simp add: delete_edges_def)
  lemma delete_edges_simp2: "delete_edges G E = \<lparr> nodes = nodes G, edges = edges G - E\<rparr>"
   by(auto simp add: delete_edges_def)
  lemma delete_edges_set_nodes: "nodes (delete_edges G E) = nodes G"
   by(simp add: delete_edges_simp2)
  lemma delete_edges_edges_mono: "E' \<subseteq> E \<Longrightarrow> edges (delete_edges G E) \<subseteq> edges (delete_edges G E')"
    by(simp add: delete_edges_def, fast)
  lemma delete_edges_edges_empty: "(delete_edges G (edges G)) = G\<lparr>edges := {}\<rparr>"
    by(simp add: delete_edges_simp2)

 \<comment> \<open>add delete\<close>
  lemma add_delete_edge: "wf_graph (G::'a graph) \<Longrightarrow> (a,b) \<in> edges G \<Longrightarrow> add_edge a b (delete_edge a b G) = G"
   apply(simp add: delete_edge_def add_edge_def wf_graph_def)
   apply(intro graph_eq_intro)
    by auto

  lemma add_delete_edges: "wf_graph (G::'v graph) \<Longrightarrow> (a,b) \<in> edges G \<Longrightarrow> (a,b) \<notin> fs \<Longrightarrow>
    add_edge a b (delete_edges G (insert (a, b) fs)) = (delete_edges G fs)"
    by(auto simp add: delete_edges_simp2 add_edge_def wf_graph_def)


 \<comment> \<open>fully_connected\<close>
  lemma fully_connected_simp: "fully_connected \<lparr>nodes = N, edges = ignore \<rparr>\<equiv> \<lparr>nodes = N, edges = N \<times> N \<rparr>"
    by(simp add: fully_connected_def)
  lemma fully_connected_wf: "wf_graph G \<Longrightarrow> wf_graph (fully_connected G)"
    by(simp add: fully_connected_def wf_graph_def)

 \<comment> \<open>succ_tran\<close>
 lemma succ_tran_mono: 
  "wf_graph \<lparr>nodes=N, edges=E\<rparr> \<Longrightarrow> E' \<subseteq> E \<Longrightarrow> succ_tran \<lparr>nodes=N, edges=E'\<rparr> v \<subseteq> succ_tran \<lparr>nodes=N, edges=E\<rparr> v"
   apply(drule wf_graph.finiteE)
   apply(frule_tac A="E'" in rev_finite_subset, simp)
   apply(simp add: num_reachable_def)
   apply(simp add: succ_tran_def)
   apply(metis (lifting, full_types) Collect_mono trancl_mono)
  done

  \<comment> \<open>num_reachable\<close>
  lemma num_reachable_mono:
  "wf_graph \<lparr>nodes=N, edges=E\<rparr> \<Longrightarrow> E' \<subseteq> E \<Longrightarrow> num_reachable \<lparr>nodes=N, edges=E'\<rparr> v \<le> num_reachable \<lparr>nodes=N, edges=E\<rparr> v"
   apply(simp add: num_reachable_def)
   apply(frule_tac E'="E'" and v="v" in succ_tran_mono, simp)
   apply(frule_tac v="v" in succ_tran_finite)
   apply(simp add: card_mono)
  done

  \<comment> \<open>num_reachable_norefl\<close>
  lemma num_reachable_norefl_mono:
  "wf_graph \<lparr>nodes=N, edges=E\<rparr> \<Longrightarrow> E' \<subseteq> E \<Longrightarrow> num_reachable_norefl \<lparr>nodes=N, edges=E'\<rparr> v \<le> num_reachable_norefl \<lparr>nodes=N, edges=E\<rparr> v"
   apply(simp add: num_reachable_norefl_def)
   apply(frule_tac E'="E'" and v="v" in succ_tran_mono, simp)
   apply(frule_tac v="v" in succ_tran_finite)
   using card_mono by (metis Diff_mono finite_Diff subset_refl)

  \<comment> \<open>backflows\<close>
  lemma backflows_wf: 
    "wf_graph \<lparr>nodes=N, edges=E\<rparr> \<Longrightarrow> wf_graph \<lparr>nodes=N, edges=backflows E\<rparr>"
    using [[simproc add: finite_Collect]] by(auto simp add: wf_graph_def backflows_def)
  lemma undirected_backflows: 
    "undirected G = \<lparr> nodes = nodes G, edges = (edges G) \<union> backflows (edges G) \<rparr>"
    by(simp add: backflows_def undirected_def)
  lemma backflows_id: 
    "backflows (backflows E) = E"
    by(simp add: backflows_def)
  lemma backflows_finite: "finite E \<Longrightarrow> finite (backflows E)"
    using [[simproc add: finite_Collect]] by(simp add: backflows_def) 
  lemma backflows_minus_backflows: "backflows (X - backflows Y) = (backflows X) - Y"
    by(auto simp add: backflows_def)
  lemma backflows_subseteq: "X \<subseteq> Y \<longleftrightarrow> backflows X \<subseteq> backflows Y"
    by(auto simp add: backflows_def)
  lemma backflows_un: "backflows (A \<union> B) = (backflows A) \<union> (backflows B)"
    by(auto simp add: backflows_def)
  lemma backflows_inter: "backflows (A \<inter> B) = (backflows A) \<inter> (backflows B)"
    by(auto simp add: backflows_def)
  lemma backflows_alt_fstsnd: "backflows E = (\<lambda>e. (snd e, fst e)) ` E"
    by(auto simp add: backflows_def, force)


lemmas graph_ops=add_node_def delete_node_def add_edge_def delete_edge_def delete_edges_simp2


  \<comment> \<open>wf_graph\<close>
  lemma wf_graph_remove_edges: "wf_graph \<lparr> nodes = V, edges = E \<rparr> \<Longrightarrow> wf_graph \<lparr> nodes = V, edges=E - X\<rparr>"
    by (metis delete_edges_simp2 delete_edges_wf select_convs(1) select_convs(2))

  lemma wf_graph_remove_edges_union: 
    "wf_graph \<lparr> nodes = V, edges = E \<union> E' \<rparr> \<Longrightarrow> wf_graph \<lparr> nodes = V, edges=E\<rparr>"
    by(auto simp add: wf_graph_def)

  lemma wf_graph_union_edges: "\<lbrakk> wf_graph \<lparr> nodes = V, edges = E \<rparr>; wf_graph \<lparr> nodes = V, edges=E'\<rparr> \<rbrakk> \<Longrightarrow>
     wf_graph \<lparr> nodes = V, edges=E \<union> E'\<rparr>"
    by(auto simp add: wf_graph_def)

  lemma wf_graph_add_subset_edges: "\<lbrakk> wf_graph \<lparr> nodes = V, edges = E \<rparr>; E' \<subseteq> E \<rbrakk> \<Longrightarrow>
     wf_graph \<lparr> nodes = V, edges= E \<union> E'\<rparr>"
    by(auto simp add: wf_graph_def) (metis rev_finite_subset)


(*Inspired by 
Benedikt Nordhoff and Peter Lammich
Dijkstra's Shortest Path Algorithm
http://isa-afp.org/entries/Dijkstra_Shortest_Path.shtml*)
(*more a literal copy of http://isa-afp.org/browser_info/current/AFP/Dijkstra_Shortest_Path/Graph.html*)

  text \<open>Successors of a node.\<close>
  definition succ :: "'v graph \<Rightarrow> 'v \<Rightarrow> 'v set"
    where "succ G v \<equiv> {v'. (v,v')\<in>edges G}"


  lemma succ_finite[simp, intro]: "finite (edges G) \<Longrightarrow> finite (succ G v)"
    unfolding succ_def
    by (rule finite_subset[where B="snd`edges G"]) force+

  lemma succ_empty: "succ empty v = {}" unfolding empty_def succ_def by auto

  lemma (in wf_graph) succ_subset: "succ G v \<subseteq> V"
    unfolding succ_def using E_wf
    by (force)


end

