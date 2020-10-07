section \<open>Graphs\<close>

theory Graph imports Main begin

text \<open>
  Let us now define digraphs, graphs, walks, paths, and related concepts.
\<close>

text \<open>@{typ 'a} is the vertex type.\<close>
type_synonym 'a Edge = "'a \<times> 'a"
type_synonym 'a Walk = "'a list"

record 'a Graph =
  verts :: "'a set" ("V\<index>")
  arcs :: "'a Edge set" ("E\<index>")
abbreviation is_arc :: "('a, 'b) Graph_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>\<index>" 60) where
  "v \<rightarrow>\<^bsub>G\<^esub> w \<equiv> (v,w) \<in> E\<^bsub>G\<^esub>"

text \<open>
  We consider directed and undirected finite graphs.  Our graphs do not have multi-edges.
\<close>
locale Digraph =
  fixes G :: "('a, 'b) Graph_scheme" (structure)
  assumes finite_vertex_set: "finite V"
      and valid_edge_set: "E \<subseteq> V \<times> V"

context Digraph begin

lemma finite_edge_set [simp]: "finite E" using finite_vertex_set valid_edge_set
  by (simp add: finite_subset)
lemma edges_are_in_V: assumes "v\<rightarrow>w" shows "v \<in> V" "w \<in> V"
  using assms valid_edge_set by blast+

subsection \<open>Walks\<close>

text \<open>A walk is sequence of vertices connected by edges.\<close>
inductive walk :: "'a Walk \<Rightarrow> bool" where
Nil [simp]: "walk []"
| Singleton [simp]: "v \<in> V \<Longrightarrow> walk [v]"
| Cons: "v\<rightarrow>w \<Longrightarrow> walk (w # vs) \<Longrightarrow> walk (v # w # vs)"

text \<open>
  Show a few composition/decomposition lemmas for walks.  These will greatly simplify the proofs
  that follow.\<close>
lemma walk_2 [simp]: "v\<rightarrow>w \<Longrightarrow> walk [v,w]" by (simp add: edges_are_in_V(2) walk.intros(3))
lemma walk_comp: "\<lbrakk> walk xs; walk ys; xs = Nil \<or> ys = Nil \<or> last xs\<rightarrow>hd ys \<rbrakk> \<Longrightarrow> walk (xs @ ys)"
  by (induct rule: walk.induct, simp_all add: walk.intros(3))
     (metis list.exhaust_sel walk.intros(2) walk.intros(3))
lemma walk_tl: "walk xs \<Longrightarrow> walk (tl xs)" by (induct rule: walk.induct) simp_all
lemma walk_drop: "walk xs \<Longrightarrow> walk (drop n xs)" by (induct n, simp) (metis drop_Suc tl_drop walk_tl)
lemma walk_take: "walk xs \<Longrightarrow> walk (take n xs)"
  by (induct arbitrary: n rule: walk.induct)
     (simp, metis Digraph.walk.simps Digraph_axioms take_Cons' take_eq_Nil,
      metis Digraph.walk.simps Digraph_axioms edges_are_in_V(1) take_Cons')
lemma walk_decomp: assumes "walk (xs @ ys)" shows "walk xs" "walk ys"
  using assms append_eq_conv_conj[of xs ys "xs @ ys"] walk_take walk_drop by metis+
lemma walk_in_V: "walk xs \<Longrightarrow> set xs \<subseteq> V" by (induct rule: walk.induct; simp add: edges_are_in_V)
lemma walk_first_edge: "walk (v # w # xs) \<Longrightarrow> v\<rightarrow>w" using walk.cases by fastforce
lemma walk_first_edge': "\<lbrakk> walk (v # xs); xs \<noteq> Nil \<rbrakk> \<Longrightarrow> v\<rightarrow>hd xs"
  using walk_first_edge by (metis list.exhaust_sel)
lemma walk_middle_edge: "walk (xs @ v # w # ys) \<Longrightarrow> v\<rightarrow>w"
  by (induct "xs @ v # w # ys" arbitrary: xs rule: walk.induct, simp, simp)
     (metis list.sel(1,3) self_append_conv2 tl_append2)
lemma walk_last_edge: "\<lbrakk> walk (xs @ ys); xs \<noteq> Nil; ys \<noteq> Nil \<rbrakk> \<Longrightarrow> last xs\<rightarrow>hd ys"
  using walk_middle_edge[of "butlast xs" "last xs" "hd ys" "tl ys"]
  by (metis Cons_eq_appendI append_butlast_last_id append_eq_append_conv2 list.exhaust_sel self_append_conv)


subsection \<open>Paths\<close>

text \<open>
  A path is a walk without repeated vertices.  This is simple enough, so most of the above lemmas
  transfer directly to paths.
\<close>

abbreviation path :: "'a Walk \<Rightarrow> bool" where "path xs \<equiv> walk xs \<and> distinct xs"

lemma path_singleton [simp]: "v \<in> V \<Longrightarrow> path [v]" by simp
lemma path_2 [simp]: "\<lbrakk> v\<rightarrow>w; v \<noteq> w \<rbrakk> \<Longrightarrow> path [v,w]" by simp
lemma path_cons: "\<lbrakk> path xs; xs \<noteq> Nil; v\<rightarrow>hd xs; v \<notin> set xs \<rbrakk> \<Longrightarrow> path (v # xs)"
  by (metis distinct.simps(2) list.exhaust_sel walk.Cons)
lemma path_comp: "\<lbrakk> walk xs; walk ys; xs = Nil \<or> ys = Nil \<or> last xs\<rightarrow>hd ys; distinct (xs @ ys) \<rbrakk>
  \<Longrightarrow> path (xs @ ys)" using walk_comp by blast
lemma path_tl: "path xs \<Longrightarrow> path (tl xs)" by (simp add: distinct_tl walk_tl)
lemma path_drop: "path xs \<Longrightarrow> path (drop n xs)" by (simp add: walk_drop)
lemma path_take: "path xs \<Longrightarrow> path (take n xs)" by (simp add: walk_take)
lemma path_decomp: assumes "path (xs @ ys)" shows "path xs" "path ys"
  using walk_decomp assms distinct_append by blast+
lemma path_decomp': "path (xs @ x # ys) \<Longrightarrow> path (xs @ [x])"
  by (metis Singleton distinct.simps(2) distinct1_rotate edges_are_in_V(1) list.discI list.sel(1)
      not_distinct_conv_prefix path_decomp(1) rotate1.simps(2) walk_comp walk_decomp(2)
      walk_first_edge' walk_last_edge)
lemma path_in_V: "path xs \<Longrightarrow> set xs \<subseteq> V" by (simp add: walk_in_V)
lemma path_length: "path xs \<Longrightarrow> length xs \<le> card V"
  by (metis card_mono distinct_card finite_vertex_set path_in_V)
lemma path_first_edge: "path (v # w # xs) \<Longrightarrow> v\<rightarrow>w" using walk_first_edge by blast
lemma path_first_edge': "\<lbrakk> path (v # xs); xs \<noteq> Nil \<rbrakk> \<Longrightarrow> v\<rightarrow>hd xs" using walk_first_edge' by blast
lemma path_middle_edge: "path (xs @ v # w # ys) \<Longrightarrow> v \<rightarrow> w" using walk_middle_edge by blast
lemma path_first_vertex: "path (x # xs) \<Longrightarrow> x \<notin> set xs" by simp
lemma path_disjoint: "\<lbrakk> path (xs @ ys); xs \<noteq> Nil; x \<in> set xs \<rbrakk> \<Longrightarrow> x \<notin> set ys" by auto

subsection \<open>The Set of All Paths\<close>

definition all_paths where "all_paths \<equiv> { xs | xs. path xs }"

text \<open>
  Because paths have no repeated vertices, every graph has at most finitely many distinct paths.
  This will be useful later to easily derive that any set of paths is finite.
\<close>

lemma finitely_many_paths: "finite all_paths" proof-
  have "all_paths \<subseteq> {xs. set xs \<subseteq> V \<and> length xs \<le> card V}"
    unfolding all_paths_def using path_length by (simp add: Collect_mono path_in_V)
  thus ?thesis using finite_lists_length_le[OF finite_vertex_set] walk_in_V infinite_super by blast
qed

end \<comment> \<open>context Digraph\<close>

text \<open>We introduce shorthand notation for a path connecting two vertices.\<close>

definition path_from_to :: "('a, 'b) Graph_scheme \<Rightarrow> 'a \<Rightarrow> 'a Walk \<Rightarrow> 'a \<Rightarrow> bool"
  ("_ \<leadsto>_\<leadsto>\<index> _" [71, 71, 71] 70) where
  "path_from_to G v xs w \<equiv> Digraph.path G xs \<and> xs \<noteq> Nil \<and> hd xs = v \<and> last xs = w"

context Digraph begin

lemma path_from_toI [intro]: "\<lbrakk> path xs; xs \<noteq> Nil; hd xs = v; last xs = w \<rbrakk> \<Longrightarrow> v \<leadsto>xs\<leadsto> w"
  and path_from_toE [dest]: "v \<leadsto>xs\<leadsto> w \<Longrightarrow> path xs \<and> xs \<noteq> Nil \<and> hd xs = v \<and> last xs = w"
  unfolding path_from_to_def by blast+

lemma path_from_to_ends: "v \<leadsto>(xs @ w # ys)\<leadsto> w \<Longrightarrow> ys = Nil"
  by (metis path_from_toE distinct.simps(2) last.simps last_appendR last_in_set list.discI path_decomp(2))

lemma path_from_to_combine:
  assumes "v \<leadsto>(xs @ x # xs')\<leadsto> w" "v' \<leadsto>(ys @ x # ys')\<leadsto> w'" "set xs \<inter> set ys' = {}"
  shows "v \<leadsto>(xs @ x # ys') \<leadsto> w'"
proof
  show "path (xs @ x # ys')"
    by (metis path_from_toE assms(1,2,3) disjoint_insert(1) distinct_append list.sel(1) list.set(2)
        list.simps(3) path_decomp(2) walk_comp walk_decomp(1) walk_last_edge)
  show "hd (xs @ x # ys') = v" by (metis path_from_toE assms(1) hd_append list.sel(1))
  show "last (xs @ x # ys') = w'" using assms(2) by auto
qed simp

lemma path_from_to_first: "v \<leadsto>xs\<leadsto> w \<Longrightarrow> v \<notin> set (tl xs)"
  by (metis path_from_toE list.collapse path_first_vertex)

lemma path_from_to_first': "v \<leadsto>(xs @ x # xs')\<leadsto> w \<Longrightarrow> v \<notin> set xs'"
  by (metis path_from_toE append_eq_append_conv2 distinct.simps(2) hd_append list.exhaust_sel
      list.sel(3) list.set_sel(1,2) list.simps(3) path_disjoint self_append_conv)

lemma path_from_to_last: "v \<leadsto>xs\<leadsto> w \<Longrightarrow> w \<notin> set (butlast xs)"
  by (metis path_from_toE append_butlast_last_id distinct_append not_distinct_conv_prefix)

lemma path_from_to_last': "v \<leadsto>(xs @ x # xs')\<leadsto> w \<Longrightarrow> w \<notin> set xs"
  by (metis path_from_toE bex_empty last_appendR last_in_set list.set(1) list.simps(3) path_disjoint)

text \<open>Every walk contains a path connecting the same vertices.\<close>

lemma walk_to_path:
  assumes "walk xs" "xs \<noteq> Nil" "hd xs = v" "last xs = w"
  shows "\<exists>ys. v \<leadsto>ys\<leadsto> w \<and> set ys \<subseteq> set xs"
proof-
  text \<open>We prove this by removing loops from @{term xs} until @{term xs} is a path.
    We want to perform induction over @{term "length xs"}, but @{term xs} in
    @{term "set ys \<subseteq> set xs"} should not be part of the induction hypothesis. To accomplish this,
    we hide @{term "set xs"} behind a definition for this specific part of the goal.\<close>
  define target_set where "target_set \<equiv> set xs"
  hence "set xs \<subseteq> target_set" by simp
  thus "\<exists>ys. v \<leadsto>ys\<leadsto> w \<and> set ys \<subseteq> target_set"
  using assms proof (induct "length xs" arbitrary: xs rule: infinite_descent0)
    case (smaller n)
    then obtain xs where
      xs: "n = length xs" "walk xs" "xs \<noteq> Nil" "hd xs = v" "last xs = w" "set xs \<subseteq> target_set" and
      hyp: "\<not>(\<exists>ys. v \<leadsto>ys\<leadsto> w \<and> set ys \<subseteq> target_set)" by blast
    text \<open>If @{term xs} is not a path, then @{term xs} is not distinct and we can decompose it.\<close>
    then obtain ys rest u
      where xs_decomp: "u \<in> set ys" "distinct ys" "xs = ys @ u # rest"
      using not_distinct_conv_prefix by (metis path_from_toI)
    text \<open>@{term u} appears in @{term ys}, so we have a loop in @{term xs} starting from an
      occurrence of @{term u} in @{term ys} ending in the vertex @{term u} in @{term "u # rest"}.
      We define @{term zs} as @{term xs} without this loop.\<close>
    obtain ys' ys_suffix where
      ys_decomp: "ys = ys' @ u # ys_suffix" by (meson split_list xs_decomp(1))
    define zs where "zs \<equiv> ys' @ u # rest"
    have "walk zs" unfolding zs_def using xs(2) xs_decomp(3) ys_decomp
      by (metis walk_decomp list.sel(1) list.simps(3) walk_comp walk_last_edge)
    moreover have "length zs < n" unfolding zs_def by (simp add: xs(1) xs_decomp(3) ys_decomp)
    moreover have "hd zs = v" unfolding zs_def
      by (metis append_is_Nil_conv hd_append list.sel(1) xs(4) xs_decomp(3) ys_decomp)
    moreover have "last zs = w" unfolding zs_def using xs(5) xs_decomp(3) by auto
    moreover have "set zs \<subseteq> target_set" unfolding zs_def using xs(6) xs_decomp(3) ys_decomp by auto
    ultimately show ?case using zs_def hyp by blast
  qed simp
qed

subsection \<open>Edges of Walks\<close>

text \<open>The set of edges on a walk.  Note that this is empty for walks of length 0 or 1.\<close>

definition edges_of_walk :: "'a Walk \<Rightarrow> 'a Edge set" where
  "edges_of_walk xs = { (v,w) | v w xs_pre xs_post. xs = xs_pre @ v # w # xs_post }"

lemma edges_of_walkE: "(v,w) \<in> edges_of_walk xs \<Longrightarrow> \<exists>xs_pre xs_post. xs = xs_pre @ v # w # xs_post"
  unfolding edges_of_walk_def by blast

lemma edges_of_walk_in_E: "walk xs \<Longrightarrow> edges_of_walk xs \<subseteq> E"
  unfolding edges_of_walk_def using walk_middle_edge by auto

lemma edges_of_walk_finite: "walk xs \<Longrightarrow> finite (edges_of_walk xs)"
  using edges_of_walk_in_E finite_edge_set finite_subset by blast

lemma edges_of_walk_empty: "edges_of_walk [] = {}" "edges_of_walk [v] = {}"
  unfolding edges_of_walk_def by simp_all

lemma edges_of_walk_2: "edges_of_walk [v,w] = {(v,w)}" proof
  {
    fix v' w' assume "(v', w') \<in> edges_of_walk [v,w]"
    then obtain xs_pre xs_post where xs_decomp: "[v,w] = xs_pre @ v' # w' # xs_post"
      using edges_of_walkE[of v' w' "[v,w]"] by blast
    then have "xs_pre = Nil"
      by (metis Nil_is_append_conv butlast.simps(2) butlast_append list.discI)
    then have "(v',w') \<in> {(v,w)}" using xs_decomp by simp
  }
  then show "edges_of_walk [v, w] \<subseteq> {(v, w)}" by (simp add: subrelI)
  show "{(v, w)} \<subseteq> edges_of_walk [v, w]" unfolding edges_of_walk_def by blast
qed

lemma edges_of_walk_edge: "\<lbrakk> walk xs; (v,w) \<in> edges_of_walk xs \<rbrakk> \<Longrightarrow> v\<rightarrow>w"
  using edges_of_walkE walk_middle_edge by fastforce

lemma edges_of_walk_middle [simp]: "(v,w) \<in> edges_of_walk (xs @ v # w # xs')"
  unfolding edges_of_walk_def by blast

lemma edges_of_comp1: "edges_of_walk xs \<subseteq> edges_of_walk (xs @ ys)"
  unfolding edges_of_walk_def by force
lemma edges_of_comp2: "edges_of_walk ys \<subseteq> edges_of_walk (xs @ ys)" proof-
  {
    fix v w assume "(v,w) \<in> edges_of_walk ys"
    then have "\<exists>ys_pre ys_post. ys = ys_pre @ v # w # ys_post" by (meson edges_of_walkE)
    then have "(v,w) \<in> edges_of_walk (xs @ ys)"
      by (metis (mono_tags, lifting) append.assoc edges_of_walk_def mem_Collect_eq)
  }
  then show ?thesis by (simp add: subrelI)
qed

lemma walk_edges_decomp_simple:
  "edges_of_walk (v # w # xs) = {(v,w)} \<union> edges_of_walk (w # xs)" (is "?A = ?B")
proof
  have "edges_of_walk (w # xs) \<subseteq> ?A" using edges_of_comp2[of "w # xs" "[v]"] by simp
  moreover have "(v,w) \<in> ?A" by (metis append_eq_Cons_conv edges_of_walk_middle)
  ultimately show "?B \<subseteq> ?A" by blast
  {
    fix v' w' assume "(v',w') \<in> ?A"
    then obtain xs_pre xs_post where xs_decomp: "v # w # xs = xs_pre @ v' # w' # xs_post"
      using edges_of_walkE by blast
    have "(v',w') \<in> ?B" proof (cases)
      assume "xs_pre = Nil" then show ?thesis using xs_decomp by auto
    next
      assume "xs_pre \<noteq> Nil" then show ?thesis
        by (metis Cons_eq_append_conv UnI2 edges_of_walk_middle xs_decomp)
    qed
  }
  then show "?A \<subseteq> ?B" by auto
qed

lemma walk_edges_decomp:
  "edges_of_walk (xs @ x # xs') = edges_of_walk (xs @ [x]) \<union> edges_of_walk (x # xs')"
proof (induct xs)
  case (Cons v xs)
  show ?case proof (cases)
    assume "xs = Nil"
    then show ?thesis using edges_of_walk_2 walk_edges_decomp_simple by auto
  next
    assume "xs \<noteq> Nil"
    then obtain w xs_post where "xs = w # xs_post" using list.exhaust_sel by blast
    then show ?thesis using Cons.hyps walk_edges_decomp_simple by auto
  qed
qed (simp add: edges_of_walk_empty(2))

lemma walk_edges_decomp':
  "edges_of_walk (xs @ v # w # xs') = edges_of_walk (xs @ [v]) \<union> {(v,w)} \<union> edges_of_walk (w # xs')"
  using walk_edges_decomp walk_edges_decomp_simple by (metis sup.assoc)

lemma walk_edges_vertices: assumes "(v, w) \<in> edges_of_walk xs" shows "v \<in> set xs" "w \<in> set xs"
  using assms edges_of_walkE by force+

lemma walk_edges_subset:
  assumes edges_subsets: "edges_of_walk xs \<subseteq> edges_of_walk ys"
    and non_trivial: "tl xs \<noteq> Nil"
  shows "set xs \<subseteq> set ys"
proof
  fix v assume "v \<in> set xs"
  then obtain xs_pre xs_post where
    xs_decomp: "xs = xs_pre @ v # xs_post" by (meson split_list)
  show "v \<in> set ys" proof (cases)
    assume "xs_pre = Nil"
    then have "xs_post \<noteq> Nil" using xs_decomp non_trivial by auto
    then have "xs = xs_pre @ v # hd xs_post # tl xs_post" by (simp add: xs_decomp)
    then have "(v, hd xs_post) \<in> edges_of_walk xs" using edges_of_walk_def by auto
    then show ?thesis using walk_edges_vertices(1) edges_subsets by fastforce
  next
    assume "xs_pre \<noteq> Nil"
    then have "xs = butlast xs_pre @ last xs_pre # v # xs_post" by (simp add: xs_decomp)
    then have "(last xs_pre, v) \<in> edges_of_walk xs" using edges_of_walk_def by auto
    then show ?thesis using walk_edges_vertices(2) edges_subsets by fastforce
  qed
qed

text \<open>
  A path has no repeated vertices, so if we split a path at an edge we find that the two pieces
  do not contain this edge any more.
\<close>

lemma path_edges:
  assumes "path xs" "(v,w) \<in> edges_of_walk xs"
  shows "\<exists>xs_pre xs_post. xs = xs_pre @ v # w # xs_post
    \<and> (v,w) \<notin> edges_of_walk (xs_pre @ [v])
    \<and> (v,w) \<notin> edges_of_walk (w # xs_post)"
proof-
  obtain xs_pre xs_post where
    xs_decomp: "xs = xs_pre @ v # w # xs_post" by (meson assms(2) edges_of_walkE)
  then have "(v,w) \<notin> edges_of_walk (xs_pre @ [v])" using assms(1) edges_of_walkE
    by (metis path_from_to_ends list.discI path_decomp' path_from_toI snoc_eq_iff_butlast)
  moreover have "(v,w) \<notin> edges_of_walk (w # xs_post)" using  assms(1)
    by (metis edges_of_walkE in_set_conv_decomp path_decomp(2) path_first_vertex xs_decomp)
  ultimately show ?thesis using xs_decomp by blast
qed

lemma path_edges_remove_prefix:
  assumes "path (xs @ x # xs')"
  shows "edges_of_walk (xs @ [x]) = edges_of_walk (xs @ x # xs') - edges_of_walk (x # xs')"
proof-
  {
    fix v w assume *: "(v,w) \<in> edges_of_walk (xs @ [x])"
    then have 1: "(v,w) \<in> edges_of_walk (xs @ x # xs')"
      using walk_edges_decomp[of xs x xs'] by force
    moreover have "(v,w) \<notin> edges_of_walk (x # xs')" proof
      assume contra: "(v,w) \<in> edges_of_walk (x # xs')"
      then have "w \<in> set (x # xs')" by (meson walk_edges_vertices(2))
      moreover have "w \<noteq> x" using assms contra * 1
        by (metis path_decomp(2) UnE edges_of_walkE edges_of_walk_edge list.set_intros(1)
            path_2 path_disjoint path_first_vertex self_append_conv2 set_append walk_edges_vertices(1))
      moreover have "w \<in> set (xs @ [x])" by (meson * walk_edges_vertices(2))
      ultimately show False using assms by auto
    qed
    ultimately have "(v,w) \<in> edges_of_walk (xs @ x # xs') - edges_of_walk (x # xs')" by blast
  }
  then show ?thesis using walk_edges_decomp[of xs x xs'] by auto
qed

subsection \<open>The First Edge of a Walk\<close>

text \<open>
  In the proof of Menger's Theorem, we will often talk about the first edge of a path.  Let us
  define this concept.
\<close>

fun first_edge_of_walk where
  "first_edge_of_walk (v # w # xs) = (v, w)"
| "first_edge_of_walk [v] = undefined"
| "first_edge_of_walk [] = undefined"

lemma first_edge_in_edges: "tl xs \<noteq> Nil \<Longrightarrow> first_edge_of_walk xs \<in> edges_of_walk xs"
  unfolding edges_of_walk_def by (induct rule: first_edge_of_walk.induct) auto

lemma first_edge_hd_tl: "\<lbrakk> v \<leadsto>xs\<leadsto> w; tl xs \<noteq> Nil \<rbrakk> \<Longrightarrow> first_edge_of_walk xs = (v, hd (tl xs))"
  by (induct "xs" rule: first_edge_of_walk.induct) auto

lemma first_edge_first:
  assumes "v \<leadsto>xs\<leadsto> w" "(v,w') \<in> edges_of_walk xs"
  shows "first_edge_of_walk xs = (v,w')"
using assms proof (induct rule: first_edge_of_walk.induct)
  case (1 v w xs)
  then show ?case
    by (metis path_decomp(1) append_self_conv2 edges_of_walkE first_edge_of_walk.simps(1)
        hd_append hd_in_set not_distinct_conv_prefix path_from_toE)
next
  case (2 v)
  then show ?case using path_edges by fastforce
qed blast

subsection \<open>Distance\<close>

text \<open>
  The distance between two vertices is the minimum length of a path.  Note that this is not a
  symmetric function because we are on digraphs.
\<close>
definition distance :: "'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "distance v w \<equiv> Min { length xs | xs. v\<leadsto>xs\<leadsto>w }"

text \<open>
  The @{const Min} operator applies only to finite sets, so let us prove that this is the case.
\<close>
lemma distance_lengths_finite: "finite { length xs | xs. v\<leadsto>xs\<leadsto>w }" proof-
  have "{ length xs | xs. v\<leadsto>xs\<leadsto>w } \<subseteq> { n | n. n \<le> card V }" using path_length by blast
  then show ?thesis using finite_Collect_le_nat by (meson finite_subset)
qed

text \<open>
  If we have a concrete path from @{term v} to @{term w}, then the length of this path bounds the
  distance from @{term v} to @{term w}.
\<close>

lemma distance_upper_bound: "v\<leadsto>xs\<leadsto>w \<Longrightarrow> distance v w \<le> length xs"
  unfolding distance_def using Min_le[OF distance_lengths_finite] by blast

text \<open>
  Another characterization of @{const distance}: If we have a concrete minimal path from @{term v}
  to @{term w}, this defines the distance.
\<close>

lemma distance_witness:
  assumes xs: "v \<leadsto>xs\<leadsto> w"
      and xs_min: "\<And>xs'. v \<leadsto>xs'\<leadsto> w \<Longrightarrow> length xs \<le> length xs'"
  shows "distance v w = length xs"
proof-
  have "\<And>d. d \<in> {length xs | xs. v \<leadsto>xs\<leadsto> w} \<Longrightarrow> length xs \<le> d" using xs_min by blast
  then show ?thesis unfolding distance_def using Min_eqI
    by (metis (mono_tags, lifting) distance_lengths_finite xs mem_Collect_eq)
qed

subsection \<open>Subgraphs\<close>

text \<open>We only need one kind of subgraph: The subgraph obtained by removing a single vertex.\<close>

definition remove_vertex :: "'a \<Rightarrow> ('a, 'b) Graph_scheme" where
  "remove_vertex x \<equiv> G\<lparr> verts := V - {x}, arcs := Restr E (V - {x}) \<rparr>"

lemma remove_vertex_V: "V\<^bsub>remove_vertex x\<^esub> = V - {x}" unfolding remove_vertex_def by auto
lemma remove_vertex_V': "V\<^bsub>remove_vertex x\<^esub> \<subseteq> V" unfolding remove_vertex_def by auto
lemma remove_vertex_E: "E\<^bsub>remove_vertex x\<^esub> = Restr E (V - {x})" unfolding remove_vertex_def by simp
lemma remove_vertex_E': "v \<rightarrow>\<^bsub>remove_vertex x\<^esub> w \<Longrightarrow> v\<rightarrow>w" by (simp add: remove_vertex_E)
lemma remove_vertex_E'': "\<lbrakk> v\<rightarrow>w; v \<noteq> x; w \<noteq> x \<rbrakk> \<Longrightarrow> v \<rightarrow>\<^bsub>remove_vertex x\<^esub> w"
  by (simp add: edges_are_in_V remove_vertex_E)

text \<open>Of course, this is still a digraph.\<close>
lemma remove_vertex_Digraph: "Digraph (remove_vertex v)" proof
  let ?V = "V\<^bsub>remove_vertex v\<^esub>" let ?E = "E\<^bsub>remove_vertex v\<^esub>"
  show "finite ?V" unfolding remove_vertex_def using finite_vertex_set by simp
  show "?E \<subseteq> ?V \<times> ?V" proof
    fix e assume "e \<in> ?E"
    then have "e \<in> (V - {v}) \<times> (V - {v})" by (metis Int_iff remove_vertex_E)
    then show "e \<in> ?V \<times> ?V" using remove_vertex_V by auto
  qed
  have "\<And>x y. \<lbrakk> (x,y) \<in> ?E; (x,y) \<notin> E \<rbrakk> \<Longrightarrow> (y,x) \<in> ?E" unfolding remove_vertex_def by simp
qed

text \<open>
  We are also going to need a few lemmas about how walks and paths behave when we remove a vertex.

  First, if we remove a vertex that is not on a walk @{term xs}, then @{term xs} is still a walk
  after removing this vertex.
\<close>

lemma remove_vertex_walk:
  assumes "walk xs" "x \<notin> set xs"
  shows "Digraph.walk (remove_vertex x) xs"
proof-
  interpret H: Digraph "remove_vertex x" using remove_vertex_Digraph by blast
  show ?thesis using assms proof (induct rule: walk.induct)
    case (Singleton v)
    then have "v \<in> V - {x}" by simp
    then show ?case using remove_vertex_V by simp
  next
    case (Cons v w vs)
    then have "v \<rightarrow>\<^bsub>remove_vertex x\<^esub> w" using remove_vertex_E'' by auto
    then show ?case
      by (meson Cons.hyps(3) Cons.prems(1) H.Cons assms(2) list.set_intros(2))
  qed simp
qed

text \<open>The same holds for paths.\<close>

lemma remove_vertex_path_from_to:
  "\<lbrakk> v \<leadsto>xs\<leadsto> w; x \<in> V; x \<notin> set xs \<rbrakk> \<Longrightarrow> v \<leadsto>xs\<leadsto>\<^bsub>remove_vertex x\<^esub> w"
  using path_from_to_def remove_vertex_walk by fastforce

text \<open>
  Conversely, if something was a walk or a path in the subgraph, then it is also a walk or a path
  in the supergraph.
\<close>
lemma remove_vertex_walk_add:
  assumes "Digraph.walk (remove_vertex x) xs"
  shows "walk xs"
proof-
  interpret H: Digraph "remove_vertex x" using remove_vertex_Digraph by blast
  show ?thesis using assms proof (induct rule: H.walk.induct)
    case (Singleton v)
    then show ?case by (meson Digraph.Singleton Digraph_axioms remove_vertex_V' subsetD)
  next
    case (Cons v w vs)
    then show ?case by (meson Digraph.Cons Digraph_axioms remove_vertex_E')
  qed simp
qed

lemma remove_vertex_path_from_to_add: "v \<leadsto>xs\<leadsto>\<^bsub>remove_vertex x\<^esub> w \<Longrightarrow> v \<leadsto>xs\<leadsto> w"
  using path_from_to_def remove_vertex_walk_add by fastforce

end \<comment> \<open>context Digraph\<close>

subsection \<open>Two Distinguished Distinct Non-adjacent Vertices.\<close>

text \<open>
  The setup for Menger's Theorem requires two distinguished distinct non-adjacent vertices
  @{term v0} and @{term v1}.  Let us pin down this concept with the following locale.
\<close>

locale v0_v1_Digraph = Digraph +
  fixes v0 v1 :: "'a"
  assumes v0_V: "v0 \<in> V" and v1_V: "v1 \<in> V"
    and v0_nonadj_v1: "\<not>v0\<rightarrow>v1"
    and v0_neq_v1: "v0 \<noteq> v1"

text \<open>
  The only lemma we need about @{locale v0_v1_Digraph} for now is that it is closed under removing
  a vertex that is not @{term v0} or @{term v1}.
\<close>
lemma (in v0_v1_Digraph) remove_vertices_v0_v1_Digraph:
  assumes "v \<noteq> v0" "v \<noteq> v1"
  shows "v0_v1_Digraph (remove_vertex v) v0 v1"
proof (rule v0_v1_Digraph.intro)
  show "v0_v1_Digraph_axioms (remove_vertex v) v0 v1"
    using assms v0_nonadj_v1 v0_neq_v1 v0_V v1_V remove_vertex_V remove_vertex_E'
    by unfold_locales blast+
qed (simp add: remove_vertex_Digraph)

subsection \<open>Undirected Graphs\<close>

text \<open>
  We represent undirecteded graphs as a special case of digraphs where every undirected edge
  is represented as an edge in both directions.  We also exclude loops because loops are uncommon
  in undirected graphs.

  As we will explain in the next paragraph, all of this has no bearing on the validity of
  Menger's Theorem for undirected graphs.
\<close>

locale Graph = Digraph +
  assumes undirected: "v\<rightarrow>w = w\<rightarrow>v"
      and no_loops: "\<not>v\<rightarrow>v"

text \<open>
  We observe that this makes @{locale Digraph} a sublocale of @{locale Graph}, meaning that every
  theorem we prove for digraphs automatically holds for undirected graphs, although it may not make
  sense because for example ``connectedness'' (if we were to define it) would need different
  definitions for directed and undirected graphs.

  Fortunately, the notions of ``separator'' and ``internally vertex-disjoint paths'' on directed
  graphs are the same for undirected graphs.  So Menger's Theorem, when we eventually prove it in
  the @{locale Digraph} locale, will apply automatically to the @{locale Graph} locale without
  any additional work.

  For this reason we will not use the @{term Graph} locale again in this proof development and it
  exists merely to show that undirected graphs are covered as a special case by our definitions.
\<close>

end
