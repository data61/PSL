section "Graph Interface"
theory GraphSpec
imports Main Graph 
  Collections.Collections 
  (*"../Collections/Lib/Proper_Iterator"*)
  (*"../Refine_Monadic/Refine_Autodet"*)
begin
  text \<open>
    This theory defines an ICF-style interface for graphs.
\<close>

  type_synonym ('V,'W,'G) graph_\<alpha> = "'G \<Rightarrow> ('V,'W) graph"

  locale graph =
    fixes \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes invar :: "'G \<Rightarrow> bool"
    assumes finite[simp, intro!]:
      "invar g \<Longrightarrow> finite (nodes (\<alpha> g))"
      "invar g \<Longrightarrow> finite (edges (\<alpha> g))"
    assumes valid: "invar g \<Longrightarrow> valid_graph (\<alpha> g)"

  type_synonym ('V,'W,'G) graph_empty = "unit \<Rightarrow> 'G"
  locale graph_empty = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes empty :: "unit \<Rightarrow> 'G"
    assumes empty_correct:
      "\<alpha> (empty ()) = Graph.empty"
      "invar (empty ())"

  type_synonym ('V,'W,'G) graph_add_node = "'V \<Rightarrow> 'G \<Rightarrow> 'G"
  locale graph_add_node = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes add_node :: "'V \<Rightarrow> 'G \<Rightarrow> 'G"
    assumes add_node_correct:
      "invar g \<Longrightarrow> invar (add_node v g)"
      "invar g \<Longrightarrow> \<alpha> (add_node v g) = Graph.add_node v (\<alpha> g)"

  type_synonym ('V,'W,'G) graph_delete_node = "'V \<Rightarrow> 'G \<Rightarrow> 'G"
  locale graph_delete_node = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes delete_node :: "'V \<Rightarrow> 'G \<Rightarrow> 'G"
    assumes delete_node_correct:
      "invar g \<Longrightarrow> invar (delete_node v g)"
      "invar g \<Longrightarrow> \<alpha> (delete_node v g) = Graph.delete_node v (\<alpha> g)"

  type_synonym ('V,'W,'G) graph_add_edge = "'V \<Rightarrow>'W \<Rightarrow> 'V \<Rightarrow> 'G \<Rightarrow> 'G"
  locale graph_add_edge = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes add_edge :: "'V \<Rightarrow> 'W \<Rightarrow> 'V \<Rightarrow> 'G \<Rightarrow> 'G"
    assumes add_edge_correct:
      "invar g \<Longrightarrow> invar (add_edge v e v' g)"
      "invar g \<Longrightarrow> \<alpha> (add_edge v e v' g) = Graph.add_edge v e v' (\<alpha> g)"

  type_synonym ('V,'W,'G) graph_delete_edge = "'V \<Rightarrow>'W \<Rightarrow> 'V \<Rightarrow> 'G \<Rightarrow> 'G"
  locale graph_delete_edge = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes delete_edge :: "'V \<Rightarrow> 'W \<Rightarrow> 'V \<Rightarrow> 'G \<Rightarrow> 'G"
    assumes delete_edge_correct:
      "invar g \<Longrightarrow> invar (delete_edge v e v' g)"
      "invar g \<Longrightarrow> \<alpha> (delete_edge v e v' g) = Graph.delete_edge v e v' (\<alpha> g)"

  type_synonym ('V,'W,'\<sigma>,'G) graph_nodes_it = "'G \<Rightarrow> ('V,'\<sigma>) set_iterator"

  locale graph_nodes_it_defs =
    fixes nodes_list_it :: "'G \<Rightarrow> ('V,'V list) set_iterator"
  begin
    definition "nodes_it g \<equiv> it_to_it (nodes_list_it g)"
  end

  locale graph_nodes_it = graph \<alpha> invar + graph_nodes_it_defs nodes_list_it 
    for \<alpha> :: "'G \<Rightarrow> ('V,'W) graph" and invar and
    nodes_list_it :: "'G \<Rightarrow> ('V,'V list) set_iterator"
    +
    assumes nodes_list_it_correct:
      "invar g \<Longrightarrow> set_iterator (nodes_list_it g) (Graph.nodes (\<alpha> g))"
  begin
    lemma nodes_it_correct: 
      "invar g \<Longrightarrow> set_iterator (nodes_it g) (Graph.nodes (\<alpha> g))"
      unfolding nodes_it_def
      apply (rule it_to_it_correct)
      by (rule nodes_list_it_correct)

    lemma pi_nodes_it[icf_proper_iteratorI]: 
      "proper_it (nodes_it S) (nodes_it S)"
      unfolding nodes_it_def 
      by (intro icf_proper_iteratorI)

    lemma nodes_it_proper[proper_it]:
      "proper_it' nodes_it nodes_it"
      apply (rule proper_it'I)
      by (rule pi_nodes_it)

  end

  type_synonym ('V,'W,'\<sigma>,'G) graph_edges_it 
    = "'G \<Rightarrow> (('V\<times>'W\<times>'V),'\<sigma>) set_iterator"

  locale graph_edges_it_defs =
    fixes edges_list_it :: "('V,'W,('V\<times>'W\<times>'V) list,'G) graph_edges_it"
  begin
    definition "edges_it g \<equiv> it_to_it (edges_list_it g)"
  end

  locale graph_edges_it = graph \<alpha> invar + graph_edges_it_defs edges_list_it
    for \<alpha> :: "'G \<Rightarrow> ('V,'W) graph" and invar and
    edges_list_it :: "('V,'W,('V\<times>'W\<times>'V) list,'G) graph_edges_it" 
    +
    assumes edges_list_it_correct:
      "invar g \<Longrightarrow> set_iterator (edges_list_it g) (Graph.edges (\<alpha> g))"
  begin
    lemma edges_it_correct: 
      "invar g \<Longrightarrow> set_iterator (edges_it g) (Graph.edges (\<alpha> g))"
      unfolding edges_it_def
      apply (rule it_to_it_correct)
      by (rule edges_list_it_correct)

    lemma pi_edges_it[icf_proper_iteratorI]: 
      "proper_it (edges_it S) (edges_it S)"
      unfolding edges_it_def 
      by (intro icf_proper_iteratorI)

    lemma edges_it_proper[proper_it]:
      "proper_it' edges_it edges_it"
      apply (rule proper_it'I)
      by (rule pi_edges_it)

  end

  type_synonym ('V,'W,'\<sigma>,'G) graph_succ_it = 
    "'G \<Rightarrow> 'V \<Rightarrow> ('W\<times>'V,'\<sigma>) set_iterator"

  locale graph_succ_it_defs =
    fixes succ_list_it :: "'G \<Rightarrow> 'V \<Rightarrow> ('W\<times>'V,('W\<times>'V) list) set_iterator"
  begin
    definition "succ_it g v \<equiv> it_to_it (succ_list_it g v)"
  end

  locale graph_succ_it = graph \<alpha> invar + graph_succ_it_defs succ_list_it
    for \<alpha> :: "'G \<Rightarrow> ('V,'W) graph" and invar and
    succ_list_it :: "'G \<Rightarrow> 'V \<Rightarrow> ('W\<times>'V,('W\<times>'V) list) set_iterator" +
    assumes succ_list_it_correct:
      "invar g \<Longrightarrow> set_iterator (succ_list_it g v) (Graph.succ (\<alpha> g) v)"
  begin
    lemma succ_it_correct: 
      "invar g \<Longrightarrow> set_iterator (succ_it g v) (Graph.succ (\<alpha> g) v)"
      unfolding succ_it_def
      apply (rule it_to_it_correct)
      by (rule succ_list_it_correct)

    lemma pi_succ_it[icf_proper_iteratorI]: 
      "proper_it (succ_it S v) (succ_it S v)"
      unfolding succ_it_def 
      by (intro icf_proper_iteratorI)

    lemma succ_it_proper[proper_it]:
      "proper_it' (\<lambda>S. succ_it S v) (\<lambda>S. succ_it S v)"
      apply (rule proper_it'I)
      by (rule pi_succ_it)

  end

  subsection "Adjacency Lists"
  type_synonym ('V,'W) adj_list = "'V list \<times> ('V\<times>'W\<times>'V) list"

  definition adjl_\<alpha> :: "('V,'W) adj_list \<Rightarrow> ('V,'W) graph" where
    "adjl_\<alpha> l \<equiv> let (nl,el) = l in \<lparr>
      nodes = set nl \<union> fst`set el \<union> snd`snd`set el,
      edges = set el
    \<rparr>"

  (* TODO: Do we have naming conventions for such a lemma ? *)
  lemma adjl_is_graph: "graph adjl_\<alpha> (\<lambda>_. True)"
    apply (unfold_locales)
    unfolding adjl_\<alpha>_def
    by force+

  type_synonym ('V,'W,'G) graph_from_list = "('V,'W) adj_list \<Rightarrow> 'G"
  locale graph_from_list = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes from_list :: "('V,'W) adj_list \<Rightarrow> 'G"
    assumes from_list_correct:
      "invar (from_list l)"
      "\<alpha> (from_list l) = adjl_\<alpha> l"

  type_synonym ('V,'W,'G) graph_to_list = "'G \<Rightarrow> ('V,'W) adj_list"
  locale graph_to_list = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes to_list :: "'G \<Rightarrow> ('V,'W) adj_list"
    assumes to_list_correct:
      "invar g \<Longrightarrow> adjl_\<alpha> (to_list g) = \<alpha> g"

  subsection \<open>Record Based Interface\<close>
  record ('V,'W,'G) graph_ops =
    gop_\<alpha> :: "('V,'W,'G) graph_\<alpha>"
    gop_invar :: "'G \<Rightarrow> bool"
    gop_empty :: "('V,'W,'G) graph_empty"
    gop_add_node :: "('V,'W,'G) graph_add_node"
    gop_delete_node :: "('V,'W,'G) graph_delete_node"
    gop_add_edge :: "('V,'W,'G) graph_add_edge"
    gop_delete_edge :: "('V,'W,'G) graph_delete_edge"
    gop_from_list :: "('V,'W,'G) graph_from_list"
    gop_to_list :: "('V,'W,'G) graph_to_list"
    gop_nodes_list_it :: "'G \<Rightarrow> ('V,'V list) set_iterator"
    gop_edges_list_it :: "('V,'W,('V\<times>'W\<times>'V) list,'G) graph_edges_it"
    gop_succ_list_it :: "'G \<Rightarrow> 'V \<Rightarrow> ('W\<times>'V,('W\<times>'V) list) set_iterator"    

  locale StdGraphDefs = 
    graph_nodes_it_defs "gop_nodes_list_it ops"
    + graph_edges_it_defs "gop_edges_list_it ops"
    + graph_succ_it_defs "gop_succ_list_it ops"
    for ops :: "('V,'W,'G,'m) graph_ops_scheme"
  begin
    abbreviation \<alpha> where "\<alpha> \<equiv> gop_\<alpha> ops"
    abbreviation invar where "invar \<equiv> gop_invar ops"
    abbreviation empty where "empty \<equiv> gop_empty ops"
    abbreviation add_node where "add_node \<equiv> gop_add_node ops"
    abbreviation delete_node where "delete_node \<equiv> gop_delete_node ops"
    abbreviation add_edge where "add_edge \<equiv> gop_add_edge ops"
    abbreviation delete_edge where "delete_edge \<equiv> gop_delete_edge ops"
    abbreviation from_list where "from_list \<equiv> gop_from_list ops"
    abbreviation to_list where "to_list \<equiv> gop_to_list ops"
    abbreviation nodes_list_it where "nodes_list_it \<equiv> gop_nodes_list_it ops"
    abbreviation edges_list_it where "edges_list_it \<equiv> gop_edges_list_it ops"
    abbreviation succ_list_it  where "succ_list_it \<equiv> gop_succ_list_it ops"
  end

  locale StdGraph = StdGraphDefs +
    graph \<alpha> invar +
    graph_empty \<alpha> invar empty +
    graph_add_node \<alpha> invar add_node +
    graph_delete_node \<alpha> invar delete_node +
    graph_add_edge \<alpha> invar add_edge +
    graph_delete_edge \<alpha> invar delete_edge +
    graph_from_list \<alpha> invar from_list +
    graph_to_list \<alpha> invar to_list +
    graph_nodes_it \<alpha> invar nodes_list_it +
    graph_edges_it \<alpha> invar edges_list_it +
    graph_succ_it \<alpha> invar succ_list_it
  begin
    lemmas correct = empty_correct add_node_correct delete_node_correct 
      add_edge_correct delete_edge_correct
      from_list_correct to_list_correct 

  end

  subsection \<open>Refinement Framework Bindings\<close>
  lemma (in graph_nodes_it) nodes_it_is_iterator[refine_transfer]:
    "invar g \<Longrightarrow> set_iterator (nodes_it g) (nodes (\<alpha> g))"
    by (rule nodes_it_correct)

  lemma (in graph_edges_it) edges_it_is_iterator[refine_transfer]:
    "invar g \<Longrightarrow> set_iterator (edges_it g) (edges (\<alpha> g))"
    by (rule edges_it_correct)
    
  lemma (in graph_succ_it) succ_it_is_iterator[refine_transfer]:
    "invar g \<Longrightarrow> set_iterator (succ_it g v) (Graph.succ (\<alpha> g) v)"
    by (rule succ_it_correct)

  lemma (in graph) drh[refine_dref_RELATES]: "RELATES (build_rel \<alpha> invar)"
    by (simp add: RELATES_def)

  (*text {* Autodet bindings: *}

  lemma (in graph_nodes_it) graph_nodes_it_t[trans_uc]:
    "DETREFe g (build_rel \<alpha> invar) g' \<Longrightarrow> 
      set_iterator (nodes_it g) (nodes g')"
    using nodes_it_correct by auto

  lemma (in graph_succ_it) graph_succ_it_t[trans_uc]:
    "DETREFe g (build_rel \<alpha> invar) g' \<Longrightarrow> DETREFe v Id v' \<Longrightarrow>
      set_iterator (succ_it g v) (succ g' v')"
    using succ_it_correct by auto

  lemma (in graph_edges_it) graph_edges_it_t[trans_uc]:
    "DETREFe g (build_rel \<alpha> invar) g' \<Longrightarrow> 
      set_iterator (edges_it g) (edges g')"
    using edges_it_correct by auto*)

end
