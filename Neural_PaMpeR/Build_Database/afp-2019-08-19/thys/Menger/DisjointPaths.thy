section \<open>Internally Vertex-Disjoint Paths\<close>

theory DisjointPaths imports Separations begin

text \<open>
  Menger's Theorem talks about internally vertex-disjoint @{term v0}-@{term v1}-paths.  Let us
  define this concept.
\<close>

locale DisjointPaths = v0_v1_Digraph +
  fixes paths :: "'a Walk set"
  assumes paths:
    "\<And>xs. xs \<in> paths \<Longrightarrow> v0\<leadsto>xs\<leadsto>v1"
  and paths_disjoint: "\<And>xs ys v.
    \<lbrakk> xs \<in> paths; ys \<in> paths; xs \<noteq> ys; v \<in> set xs; v \<in> set ys \<rbrakk> \<Longrightarrow> v = v0 \<or> v = v1"

subsection \<open>Basic Properties\<close>

text \<open>The empty set of paths trivially satisfies the conditions.\<close>
lemma (in v0_v1_Digraph) DisjointPaths_empty: "DisjointPaths G v0 v1 {}"
  by (simp add: DisjointPaths.intro DisjointPaths_axioms_def v0_v1_Digraph_axioms)

text \<open>Re-adding a deleted vertex is fine.\<close>
lemma (in v0_v1_Digraph) DisjointPaths_supergraph:
  assumes "DisjointPaths (remove_vertex v) v0 v1 paths"
  shows "DisjointPaths G v0 v1 paths"
proof
  interpret H: DisjointPaths "remove_vertex v" v0 v1 paths using assms .
  show "\<And>xs. xs \<in> paths \<Longrightarrow> v0 \<leadsto>xs\<leadsto> v1" using remove_vertex_path_from_to_add H.paths by blast
  show "\<And>xs ys v. \<lbrakk> xs \<in> paths; ys \<in> paths; xs \<noteq> ys; v \<in> set xs; v \<in> set ys \<rbrakk> \<Longrightarrow> v = v0 \<or> v = v1"
    by (meson DisjointPaths.paths_disjoint H.DisjointPaths_axioms)
qed

context DisjointPaths begin

lemma paths_in_all_paths: "paths \<subseteq> all_paths" unfolding all_paths_def using paths by blast
lemma finite_paths: "finite paths"
  using finitely_many_paths infinite_super paths_in_all_paths by blast

lemma paths_edge_finite: "finite (\<Union>(edges_of_walk ` paths))" proof-
  have "\<Union>(edges_of_walk ` paths) \<subseteq> E" using edges_of_walk_in_E paths by fastforce
  then show ?thesis by (meson finite_edge_set finite_subset)
qed

lemma paths_tl_notnil: "xs \<in> paths \<Longrightarrow> tl xs \<noteq> Nil"
  by (metis path_from_toE hd_Cons_tl last_ConsL paths v0_neq_v1)

lemma paths_second_in_V: "xs \<in> paths \<Longrightarrow> hd (tl xs) \<in> V"
  by (metis paths edges_are_in_V(2) list.exhaust_sel path_from_toE paths_tl_notnil walk_first_edge')

lemma paths_second_not_v0: "xs \<in> paths \<Longrightarrow> hd (tl xs) \<noteq> v0"
  by (metis distinct.simps(2) hd_in_set list.exhaust_sel path_from_to_def paths paths_tl_notnil)

lemma paths_second_not_v1: "xs \<in> paths \<Longrightarrow> hd (tl xs) \<noteq> v1"
  using paths paths_tl_notnil v0_nonadj_v1 walk_first_edge' by fastforce

lemma paths_second_disjoint: "\<lbrakk> xs \<in> paths; ys \<in> paths; xs \<noteq> ys \<rbrakk> \<Longrightarrow> hd (tl xs) \<noteq> hd (tl ys)"
  by (metis paths_disjoint Nil_tl hd_in_set list.set_sel(2)
      paths_second_not_v0 paths_second_not_v1 paths_tl_notnil)

lemma paths_edge_disjoint:
  assumes "xs \<in> paths" "ys \<in> paths" "xs \<noteq> ys"
  shows "edges_of_walk xs \<inter> edges_of_walk ys = {}"
proof (rule ccontr)
  assume "edges_of_walk xs \<inter> edges_of_walk ys \<noteq> {}"
  then obtain v w where v_w: "(v,w) \<in> edges_of_walk xs" "(v,w) \<in> edges_of_walk ys" by auto
  then have "v \<in> set xs" "w \<in> set xs" "v \<in> set ys" "w \<in> set ys" by (meson walk_edges_vertices)+
  then have "v = v0 \<or> v = v1" "w = v0 \<or> w = v1" using assms paths_disjoint by blast+
  then show False using v_w(1) assms(1) v0_nonadj_v1 edges_of_walk_edge path_edges
    by (metis distinct_length_2_or_more path_decomp(2) path_from_to_def path_from_to_ends paths)
qed

text \<open>Specify the conditions for adding a new disjoint path to the set of disjoint paths.\<close>
lemma DisjointPaths_extend:
  assumes P_path: "v0\<leadsto>P\<leadsto>v1"
      and P_disjoint: "\<And>xs v. \<lbrakk> xs \<in> paths; xs \<noteq> P; v \<in> set xs; v \<in> set P \<rbrakk> \<Longrightarrow> v = v0 \<or> v = v1"
  shows "DisjointPaths G v0 v1 (insert P paths)"
proof
  fix xs ys v
  assume "xs \<in> insert P paths" "ys \<in> insert P paths" "xs \<noteq> ys" "v \<in> set xs" "v \<in> set ys"
  then show "v = v0 \<or> v = v1"
    by (metis DisjointPaths.paths_disjoint DisjointPaths_axioms P_disjoint insert_iff)
next
  show "\<And>xs. xs \<in> insert P paths \<Longrightarrow> v0 \<leadsto>xs\<leadsto> v1"
    using P_path paths by blast
qed

lemma DisjointPaths_reduce:
  assumes "paths' \<subseteq> paths"
  shows "DisjointPaths G v0 v1 paths'"
proof
  fix xs assume "xs \<in> paths'" then show "v0 \<leadsto>xs\<leadsto> v1" using assms paths by blast
next
  fix xs ys v assume "xs \<in> paths'" "ys \<in> paths'" "xs \<noteq> ys" "v \<in> set xs" "v \<in> set ys"
  then show "v = v0 \<or> v = v1" by (meson assms paths_disjoint subsetCE)
qed

subsection \<open>Second Vertices\<close>

text \<open>
  Let us now define the set of second vertices of the paths.  We are going to need this in order
  to find a path avoiding the old paths on its first edge.
\<close>

definition second_vertex where "second_vertex \<equiv> \<lambda>xs :: 'a Walk. hd (tl xs)"
definition second_vertices where "second_vertices \<equiv> second_vertex ` paths"

lemma second_vertex_inj: "inj_on second_vertex paths"
  unfolding second_vertex_def using paths_second_disjoint by (meson inj_onI)

lemma second_vertices_card: "card second_vertices = card paths"
  unfolding second_vertices_def using finite_paths card_image second_vertex_inj by blast

lemma second_vertices_in_V: "second_vertices \<subseteq> V"
  unfolding second_vertex_def second_vertices_def using paths_second_in_V by blast
lemma v0_v1_notin_second_vertices: "v0 \<notin> second_vertices" "v1 \<notin> second_vertices"
  unfolding second_vertices_def second_vertex_def
  using paths_second_not_v0 paths_second_not_v1 by blast+

lemma second_vertices_new_path: "hd (tl xs) \<notin> second_vertices \<Longrightarrow> xs \<notin> paths"
  by (metis image_iff second_vertex_def second_vertices_def)

lemma second_vertices_first_edge:
  "\<lbrakk> xs \<in> paths; first_edge_of_walk xs = (v,w) \<rbrakk> \<Longrightarrow> w \<in> second_vertices"
  unfolding second_vertices_def second_vertex_def
  using first_edge_hd_tl paths paths_tl_notnil by fastforce

text \<open>
  If we have no small separations, then the set of second vertices is not a separator and we can
  find a path avoiding this set.
\<close>
lemma disjoint_paths_new_path:
  assumes no_small_separations: "\<And>S. Separation G v0 v1 S \<Longrightarrow> card S \<ge> Suc (card paths)"
  shows "\<exists>P_new. v0\<leadsto>P_new\<leadsto>v1 \<and> set P_new \<inter> second_vertices = {}"
proof-
  have "\<not>Separation G v0 v1 second_vertices"
    using no_small_separations second_vertices_card by force
  then show ?thesis
      by (simp add: path_exists_if_no_separation second_vertices_in_V v0_v1_notin_second_vertices)
qed

text \<open>
  We need the following predicate to find the first vertex on a new path that hits one of the
  other paths.  We add the condition @{term "x = v1"} to cover the case @{term "paths = {}"}.
\<close>
definition hitting_paths where
  "hitting_paths \<equiv> \<lambda>x. x \<noteq> v0 \<and> ((\<exists>xs \<in> paths. x \<in> set xs) \<or> x = v1)"

end \<comment> \<open>DisjointPaths\<close>


section \<open>One More Path\<close>

text \<open>
  Let us define a set of disjoint paths with one more path.  Except for the first and last vertex,
  the new path must be disjoint from all other paths.  The first vertex must be @{term v0} and the
  last vertex must be on some other path.  In the ideal case, the last vertex will be @{term v1},
  in which case we are already done because we have found a new disjoint path between @{term v0}
  and @{term v1}.
\<close>
locale DisjointPathsPlusOne = DisjointPaths +
  fixes P_new :: "'a Walk"
  assumes P_new:
    "v0 \<leadsto>P_new\<leadsto> (last P_new)"
  and tl_P_new:
    "tl P_new \<noteq> Nil"
    "hd (tl P_new) \<notin> second_vertices"
  and last_P_new:
    "hitting_paths (last P_new)"
    "\<And>v. v \<in> set (butlast P_new) \<Longrightarrow> \<not>hitting_paths v"
begin

subsection \<open>Characterizing the New Path\<close>

lemma P_new_hd_disjoint: "\<And>xs. xs \<in> paths \<Longrightarrow> hd (tl P_new) \<noteq> hd (tl xs)"
  using tl_P_new(2) unfolding second_vertices_def second_vertex_def by blast

lemma P_new_new: "P_new \<notin> paths" using P_new_hd_disjoint by auto

definition paths_with_new where "paths_with_new \<equiv> insert P_new paths"

lemma card_paths_with_new: "card paths_with_new = Suc (card paths)"
  unfolding paths_with_new_def using P_new_new by (simp add: finite_paths)

lemma paths_with_new_no_Nil: "Nil \<notin> paths_with_new"
  using P_new paths_tl_notnil paths_with_new_def by fastforce

lemma paths_with_new_path: "xs \<in> paths_with_new \<Longrightarrow> path xs"
  using P_new paths paths_with_new_def by auto

lemma paths_with_new_start_in_v0: "xs \<in> paths_with_new \<Longrightarrow> hd xs = v0"
  using P_new paths paths_with_new_def by auto

subsection \<open>The Last Vertex of the New Path\<close>

text \<open>
  McCuaig in \cite{DBLP:journals/jgt/McCuaig84} calls the last vertex of @{term P_new} by the name
  @{term x}.  However, this name is somewhat confusing because it is so short and it will be visible
  in most places from now on, so let us give this vertex the more descriptive name of
  @{term new_last}.
\<close>
definition new_pre where "new_pre \<equiv> butlast P_new"
definition new_last where "new_last \<equiv> last P_new"

lemma P_new_decomp: "P_new = new_pre @ [new_last]"
  by (metis new_pre_def append_butlast_last_id list.sel(2) tl_P_new(1) new_last_def)

lemma new_pre_not_Nil: "new_pre \<noteq> Nil" using P_new(1) hitting_paths_def
  by (metis P_new_decomp list.sel(3) self_append_conv2 tl_P_new(1))

lemma new_pre_hitting: "x' \<in> set new_pre \<Longrightarrow> \<not>hitting_paths x'"
  by (simp add: new_pre_def last_P_new(2))

lemma P_hit: "hitting_paths new_last"
  by (simp add: last_P_new(1) new_last_def)

lemma new_last_neq_v0: "new_last \<noteq> v0" using hitting_paths_def P_hit by force

lemma new_last_in_V: "new_last \<in> V" using P_new new_last_def path_in_V by fastforce

lemma new_last_to_v1: "\<exists>R. new_last \<leadsto>R\<leadsto>\<^bsub>remove_vertex v0\<^esub> v1"
proof (cases)
  assume "new_last = v1"
  then have "new_last \<leadsto>[v1]\<leadsto>\<^bsub>remove_vertex v0\<^esub> v1"
    by (metis last.simps list.sel(1) list.set(1) list.simps(15) list.simps(3) path_from_to_def
        path_singleton remove_vertex_path_from_to singletonD v0_V v0_neq_v1 v1_V)
  then show ?thesis by blast
next
  assume "new_last \<noteq> v1"
  then obtain xs where xs: "xs \<in> paths" "new_last \<in> set xs"
    using hitting_paths_def last_P_new(1) new_last_def by auto
  then obtain xs_pre xs_post where xs_decomp: "xs = xs_pre @ new_last # xs_post"
    by (meson split_list)
  then have "new_last \<leadsto>(new_last # xs_post)\<leadsto> v1" using \<open>xs \<in> paths\<close>
    by (metis paths last_appendR list.sel(1) list.simps(3) path_decomp(2) path_from_to_def)
  then have "new_last \<leadsto>(new_last # xs_post)\<leadsto>\<^bsub>remove_vertex v0\<^esub> v1"
    using remove_vertex_path_from_to
    by (metis paths Set.set_insert xs_decomp xs(1) disjoint_insert(1) distinct_append hd_append
        hitting_paths_def last_P_new(1) list.set_sel(1) path_from_to_def v0_V new_last_def)
  then show ?thesis by blast
qed

lemma paths_plus_one_disjoint:
  assumes "xs \<in> paths_with_new" "ys \<in> paths_with_new" "xs \<noteq> ys" "v \<in> set xs" "v \<in> set ys"
  shows "v = v0 \<or> v = v1 \<or> v = new_last"
proof-
  have "xs \<in> paths \<or> ys \<in> paths" using assms(1,2,3) paths_with_new_def by auto
  then have "hitting_paths v \<or> v = v0" using assms(1,2,4,5) unfolding hitting_paths_def by blast
  then show ?thesis using assms last_P_new(2) set_butlast paths_disjoint
    by (metis insert_iff paths_with_new_def new_last_def)
qed

text \<open>If the new path is disjoint, we are happy.\<close>

lemma P_new_solves_if_disjoint:
  "new_last = v1 \<Longrightarrow> \<exists>paths'. DisjointPaths G v0 v1 paths' \<and> card paths' = Suc (card paths)"
  using DisjointPaths_extend P_new(1) paths_plus_one_disjoint card_paths_with_new
  unfolding paths_with_new_def new_last_def by blast

subsection \<open>Removing the Last Vertex\<close>

definition H_x where "H_x \<equiv> remove_vertex new_last"

lemma H_x_Digraph: "Digraph H_x" unfolding H_x_def using remove_vertex_Digraph .

lemma H_x_v0_v1_Digraph: "new_last \<noteq> v1 \<Longrightarrow> v0_v1_Digraph H_x v0 v1" unfolding H_x_def
  using remove_vertices_v0_v1_Digraph hitting_paths_def P_hit by (simp add: H_x_def)

subsection \<open>A New Path Following the Other Paths\<close>

text \<open>
  The following lemma is one of the most complicated technical lemmas in the proof of Menger's
  Theorem.

  Suppose we have a non-trivial path whose edges are all in the edge set of @{term path_with_new}
  and whose first edge equals the first edge of some @{term "P \<in> path_with_new"}.  Also suppose that
  the path does not contain @{term v1} or @{term new_last}.  Then it follows by induction that this
  path is an initial segment of @{term P}.

  Note that McCuaig does not mention this statement at all in his proof because it looks so obvious.
\<close>

lemma new_path_follows_old_paths:
  assumes xs: "v0 \<leadsto>xs\<leadsto> w" "tl xs \<noteq> Nil" "v1 \<notin> set xs" "new_last \<notin> set xs"
      and P: "P \<in> paths_with_new" "hd (tl xs) = hd (tl P)"
      and edges_subset: "edges_of_walk xs \<subseteq> \<Union>(edges_of_walk ` paths_with_new)"
    shows "edges_of_walk xs \<subseteq> edges_of_walk P"
using xs P(2) edges_subset proof (induct "length xs" arbitrary: xs w)
  case 0
  then show ?case using xs(1) by auto
next
  case (Suc n xs w)
  have "n \<noteq> 0" using Suc.hyps(2) Suc.prems(1,2)
    by (metis path_from_toE Nitpick.size_list_simp(2) Suc_inject length_0_conv)
  show ?case proof (cases)
    assume "n = Suc 0"
    then obtain v w where v_w: "xs = [v,w]"
      by (metis (full_types) Suc.hyps(2) length_0_conv length_Suc_conv)
    then have "v = v0" using Suc.prems(1) by auto
    moreover have "w = hd (tl P)" using Suc.prems(5) v_w by auto
    moreover have "edges_of_walk xs = {(v, w)}" using v_w edges_of_walk_2 by simp
    moreover have "(v0, hd (tl P)) \<in> edges_of_walk P" using P tl_P_new(1) P_new paths
      by (metis first_edge_hd_tl first_edge_in_edges insert_iff paths_tl_notnil paths_with_new_def)
    ultimately show ?thesis by auto
  next
    assume "n \<noteq> Suc 0"
    obtain xs' x where xs': "xs = xs' @ [x]"
      by (metis path_from_toE Suc.prems(1) append_butlast_last_id)
    then have "n = length xs'" using xs' using Suc.hyps(2) by auto
    moreover have xs'_path: "v0 \<leadsto>xs'\<leadsto> last xs'"
      using xs' Suc.prems(1) \<open>tl xs \<noteq> Nil\<close> walk_decomp(1)
      by (metis distinct_append hd_append list.sel(3) path_from_to_def self_append_conv2)
    moreover have "tl xs' \<noteq> []" using \<open>n \<noteq> Suc 0\<close>
      by (metis path_from_toE Nitpick.size_list_simp(2) calculation(1,2))
    moreover have "v1 \<notin> set xs'" using xs' Suc.prems(3) by auto
    moreover have "new_last \<notin> set xs'" using xs' Suc.prems(4) by auto
    moreover have "hd (tl xs') = hd (tl P)"
      using xs' \<open>tl xs' \<noteq> []\<close> Suc.prems(5) calculation(2) by auto
    moreover have "edges_of_walk xs' \<subseteq> \<Union>(edges_of_walk ` paths_with_new)"
      using xs' Suc.prems(6) edges_of_comp1 by blast
    ultimately have xs'_edges: "edges_of_walk xs' \<subseteq> edges_of_walk P" using Suc.hyps(1) by blast
    moreover have "edges_of_walk xs = edges_of_walk xs' \<union> { (last xs', x) }"
      using xs' using walk_edges_decomp'[of "butlast xs'" "last xs'" x Nil] xs'_path
      by (metis path_from_toE Un_empty_right append_assoc append_butlast_last_id butlast.simps(2)
          edges_of_walk_empty(2) last_ConsL last_ConsR list.distinct(1))
    moreover have "(last xs', x) \<in> edges_of_walk P" proof (rule ccontr)
      assume contra: "(last xs', x) \<notin> edges_of_walk P"
      have xs_last_edge: "(last xs', x) \<in> edges_of_walk xs"
        using xs' calculation(2) by blast
      then obtain P' where
        P': "P' \<in> paths_with_new" "(last xs', x) \<in> edges_of_walk P'"
        using Suc.prems(6) by auto
      then have "P \<noteq> P'" using contra by blast
      moreover have "last xs' \<in> set P" using xs_last_edge xs'_edges \<open>tl xs' \<noteq> []\<close> xs'_path
        by (metis path_from_toE last_in_set subsetCE walk_edges_subset)
      moreover have "last xs' \<in> set P'" using P'(2) by (meson walk_edges_vertices(1))
      ultimately have "last xs' = v0 \<or> last xs' = v1 \<or> last xs' = new_last"
        using paths_plus_one_disjoint P'(1) P paths_with_new_def by auto
      then show False using Suc.prems(3) \<open>new_last \<notin> set xs'\<close> \<open>tl xs' \<noteq> []\<close> xs' xs'_path
         by (metis path_from_toE butlast_snoc in_set_butlastD last_in_set last_tl path_from_to_first)
    qed
    ultimately show ?thesis by simp
  qed
qed

end \<comment> \<open>locale @{locale DisjointPathsPlusOne}\<close>

end
