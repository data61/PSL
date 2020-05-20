section \<open>Example Instantiations\<close>

text \<open>
  This section provides a few example instantiations for the locales to show that they are not empty.
\<close>

theory ExampleInstantiations
imports TreewidthCompleteGraph begin

datatype Vertices = u0 | v0 | w0

text \<open>The empty graph is a tree.\<close>
definition "T1 \<equiv> \<lparr> verts = {}, arcs = {} \<rparr>"
interpretation Graph_T1: Graph T1 unfolding T1_def by standard simp_all
interpretation Tree_T1: Tree T1
  by (rule Tree.intro, simp add: Graph_T1.Graph_axioms, standard, unfold T1_def, simp)
     (metis T1_def Graph_T1.cycle_def equals0D simps(2))

text \<open>The complete graph with 2 vertices.\<close>
definition "T2 \<equiv> \<lparr> verts = {u0, v0}, arcs = {(u0,v0),(v0,u0)} \<rparr>"
lemma Graph_T2: "Graph T2" unfolding T2_def by standard auto
lemma Tree_T2: "Tree T2"
proof-
  interpret Graph T2 using Graph_T2 .
  show ?thesis proof
    fix v w assume "v \<in> V\<^bsub>T2\<^esub>" "w \<in> V\<^bsub>T2\<^esub>" thus "connected v w"
      by (metis T2_def connected_def connected_edge empty_iff insert_iff last.simps list.discI
          list.sel(1) path_singleton simps(1,2))
  next
    fix xs :: "Vertices list"
    {
      fix x y
      assume "cycle xs" and xy: "(x = v0 \<and> y = u0) \<or> (x = u0 \<and> y = v0)" and "hd xs = x"
      hence "last xs = y"
        by (metis T2_def cycleE distinct.simps(2) distinct_singleton insert_iff list.set(1)
            prod.inject simps(2))
      moreover have "\<And>v. v \<in> set xs \<Longrightarrow> v = x \<or> v = y" using \<open>cycle xs\<close> xy
        by (metis cycle_def walk_in_V T2_def empty_iff insertE insert_absorb insert_subset
            select_convs(1))
      ultimately have "xs = [x,y]" using \<open>cycle xs\<close> xy
        by (metis cycleE distinct_length_2_or_more last.simps list.exhaust_sel list.set_sel(1)
            list.set_sel(2) no_loops)
      hence False using \<open>cycle xs\<close> unfolding cycle_def by simp
    }
    thus "\<not>cycle xs" by (metis T2_def cycleE empty_iff insertE prod.inject simps(2))
  qed
qed
text \<open>As expected, the treewidth of the complete graph with 2 vertices is 1.

  Note that we use \<open>Graph.treewidth_complete_graph\<close> here and not \<open>treewidth_tree\<close>.
  This is because \<open>treewidth_tree\<close> requires the vertex set of the graph to be a set of
  natural numbers, which is not the case here.\<close>
lemma T2_complete: "\<lbrakk> v \<in> V\<^bsub>T2\<^esub>; w \<in> V\<^bsub>T2\<^esub>; v \<noteq> w \<rbrakk> \<Longrightarrow> v \<rightarrow>\<^bsub>T2\<^esub> w" unfolding T2_def by auto
lemma treewidth_T2: "Graph.treewidth T2 = 1"
  using Graph.treewidth_complete_graph[OF Graph_T2] T2_complete unfolding T2_def by simp

text \<open>The complete graph with 3 vertices.\<close>
definition "T3 \<equiv> \<lparr> verts = {u0, v0, w0}, arcs = {(u0,v0),(v0,u0),(v0,w0),(w0,v0),(w0,u0),(u0,w0)} \<rparr>"
lemma Graph_T3: "Graph T3" unfolding T3_def by standard auto
text \<open>@{term "[u0, v0, w0]"} is a cycle in @{const "T3"}, so @{const "T3"} is not a tree.\<close>
lemma Not_Tree_T3: "\<not>Tree T3" proof
  assume "Tree T3" then interpret Tree T3 .
  let ?xs = "[u0, v0, w0]"
  have "path ?xs" by (metis T3_def Vertices.distinct(1,3,5)
    distinct_length_2_or_more distinct_singleton insert_iff simps(2) walk.Cons walk_2)
  moreover have "(hd ?xs, last ?xs) \<in> arcs T3" by (simp add: T3_def)
  ultimately show False using meeting_paths_produce_cycle no_cycles walk_2
    by (metis distinct_length_2_or_more last_ConsL last_ConsR list.sel(1))
qed

lemma T3_complete: "\<lbrakk> v \<in> V\<^bsub>T3\<^esub>; w \<in> V\<^bsub>T3\<^esub>; v \<noteq> w \<rbrakk> \<Longrightarrow> v \<rightarrow>\<^bsub>T3\<^esub> w" unfolding T3_def by auto
lemma treewidth_T3: "Graph.treewidth T3 = 2"
  using Graph.treewidth_complete_graph[OF Graph_T3] T3_complete unfolding T3_def by simp

text \<open>We omit a concrete example for the \<open>TreeDecomposition\<close> locale because
  \<open>tree_decomposition_exists\<close> already shows that it is non-empty.\<close>

end
