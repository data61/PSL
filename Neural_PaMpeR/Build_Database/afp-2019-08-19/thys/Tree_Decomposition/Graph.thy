section \<open>Graphs\<close>

theory Graph
imports Main begin

text \<open>@{typ 'a} is the vertex type.\<close>
type_synonym 'a Edge = "'a \<times> 'a"
type_synonym 'a Walk = "'a list"

record 'a Graph =
  verts :: "'a set" ("V\<index>")
  arcs :: "'a Edge set" ("E\<index>")
abbreviation is_arc :: "('a, 'b) Graph_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>\<index>" 60) where
  "v \<rightarrow>\<^bsub>G\<^esub> w \<equiv> (v,w) \<in> E\<^bsub>G\<^esub>"

text \<open>
  We only consider undirected finite simple graphs, that is, graphs without multi-edges and without
  loops.
\<close>
locale Graph =
  fixes G :: "('a, 'b) Graph_scheme" (structure)
  assumes finite_vertex_set: "finite V"
    and valid_edge_set: "E \<subseteq> V \<times> V"
    and undirected: "v\<rightarrow>w = w\<rightarrow>v"
    and no_loops: "\<not>v\<rightarrow>v"
begin
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
     (simp, metis Graph.walk.simps Graph_axioms take_Cons' take_eq_Nil,
      metis Graph.walk.simps Graph_axioms edges_are_in_V(1) take_Cons')
lemma walk_rev: "walk xs \<Longrightarrow> walk (rev xs)"
  by (induct rule: walk.induct, simp, simp)
     (metis Singleton edges_are_in_V(1) last_ConsL last_appendR list.sel(1)
      not_Cons_self2 rev.simps(2) undirected walk_comp)
lemma walk_decomp: assumes "walk (xs @ ys)" shows "walk xs" "walk ys"
  using assms append_eq_conv_conj[of xs ys "xs @ ys"] walk_take walk_drop by metis+
lemma walk_dropWhile: "walk xs \<Longrightarrow> walk (dropWhile f xs)" by (simp add: walk_drop dropWhile_eq_drop)
lemma walk_takeWhile: "walk xs \<Longrightarrow> walk (takeWhile f xs)" using walk_take takeWhile_eq_take by metis

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

lemma walk_takeWhile_edge:
  assumes "walk (xs @ [v])" "xs \<noteq> Nil" "hd xs \<noteq> v"
  shows "last (takeWhile (\<lambda>x. x \<noteq> v) xs)\<rightarrow>v" (is "last ?xs\<rightarrow>v")
proof-
  obtain xs' where xs': "xs = ?xs @ xs'" by (metis takeWhile_dropWhile_id)
  thus ?thesis proof (cases)
    assume "xs' = Nil" thus ?thesis using xs' assms(1,2) walk_last_edge by force
  next
    assume "xs' \<noteq> Nil"
    hence "hd xs' = v" by (metis (full_types) hd_dropWhile same_append_eq takeWhile_dropWhile_id xs')
    thus ?thesis by (metis \<open>xs' \<noteq> []\<close> append_Nil assms(1,3) walk_decomp(1) walk_last_edge xs')
  qed
qed

subsection \<open>Connectivity\<close>

definition connected :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>\<^sup>*" 60) where
  "connected v w \<equiv> \<exists>xs. walk xs \<and> xs \<noteq> Nil \<and> hd xs = v \<and> last xs = w"
lemma connectedI [intro]: "\<lbrakk> walk xs; xs \<noteq> Nil; hd xs = v; last xs = w \<rbrakk> \<Longrightarrow> v \<rightarrow>\<^sup>* w"
  unfolding connected_def by blast
lemma connectedE:
  assumes "v \<rightarrow>\<^sup>* w"
  obtains xs where "walk xs" "xs \<noteq> Nil" "hd xs = v" "last xs = w"
  using assms that unfolding connected_def by blast

lemma connected_in_V: assumes "v \<rightarrow>\<^sup>* w" shows "v \<in> V" "w \<in> V"
  using assms unfolding connected_def by (meson hd_in_set last_in_set subsetCE walk_in_V)+
lemma connected_refl: "v \<in> V \<Longrightarrow> v \<rightarrow>\<^sup>* v" by (rule connectedI[of "[v]"]) simp_all
lemma connected_edge: "v\<rightarrow>w \<Longrightarrow> v \<rightarrow>\<^sup>* w" by (rule connectedI[of "[v,w]"]) simp_all
lemma connected_trans:
  assumes u_v: "u \<rightarrow>\<^sup>* v" and v_w: "v \<rightarrow>\<^sup>* w"
  shows "u \<rightarrow>\<^sup>* w"
proof-
  obtain xs where xs: "walk xs" "xs \<noteq> Nil" "hd xs = u" "last xs = v" using u_v connectedE by blast
  obtain ys where ys: "walk ys" "ys \<noteq> Nil" "hd ys = v" "last ys = w" using v_w connectedE by blast
  let ?R = "xs @ tl ys"
  show ?thesis proof
    show "walk ?R" using walk_comp[OF xs(1)] by (metis xs(4) ys(1,2,3) list.sel(1,3) walk.simps)
    show "?R \<noteq> Nil" by (simp add: xs(2))
    show "hd ?R = u" by (simp add: xs(2,3))
    show "last ?R = w" using xs(2,4) ys(2,3,4)
      by (metis append_butlast_last_id last_append last_tl list.exhaust_sel)
  qed
qed

subsection \<open>Paths\<close>

text \<open>A path is a walk without repeated vertices.  This is simple enough, so most of the above
  lemmas transfer directly to paths.\<close>

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
lemma path_rev: "path xs \<Longrightarrow> path (rev xs)" by (simp add: walk_rev)
lemma path_decomp: assumes "path (xs @ ys)" shows "path xs" "path ys"
  using walk_decomp assms distinct_append by blast+
lemma path_dropWhile: "path xs \<Longrightarrow> path (dropWhile f xs)" by (simp add: walk_dropWhile)
lemma path_takeWhile: "path xs \<Longrightarrow> path (takeWhile f xs)" by (simp add: walk_takeWhile)
lemma path_in_V: "path xs \<Longrightarrow> set xs \<subseteq> V" by (simp add: walk_in_V)
lemma path_first_edge: "path (v # w # xs) \<Longrightarrow> v\<rightarrow>w" using walk_first_edge by blast
lemma path_first_edge': "\<lbrakk> path (v # xs); xs \<noteq> Nil \<rbrakk> \<Longrightarrow> v\<rightarrow>hd xs" using walk_first_edge' by blast
lemma path_middle_edge: "path (xs @ v # w # ys) \<Longrightarrow> v \<rightarrow> w" using walk_middle_edge by blast
lemma path_takeWhile_edge: "\<lbrakk> path (xs @ [v]); xs \<noteq> Nil; hd xs \<noteq> v \<rbrakk>
  \<Longrightarrow> last (takeWhile (\<lambda>x. x \<noteq> v) xs)\<rightarrow>v" using walk_takeWhile_edge by blast

end
text \<open>We introduce shorthand notation for a path connecting two vertices.\<close>
definition path_from_to :: "('a, 'b) Graph_scheme \<Rightarrow> 'a \<Rightarrow> 'a Walk \<Rightarrow> 'a \<Rightarrow> bool"
  ("_ \<leadsto>_\<leadsto>\<index> _" [71, 71, 71] 70) where
  "path_from_to G v xs w \<equiv> Graph.path G xs \<and> xs \<noteq> Nil \<and> hd xs = v \<and> last xs = w"
context Graph begin
lemma path_from_toI [intro]: "\<lbrakk> path xs; xs \<noteq> Nil; hd xs = v; last xs = w \<rbrakk> \<Longrightarrow> v \<leadsto>xs\<leadsto> w"
  and path_from_toE [dest]: "v \<leadsto>xs\<leadsto> w \<Longrightarrow> path xs \<and> xs \<noteq> Nil \<and> hd xs = v \<and> last xs = w"
  unfolding path_from_to_def by blast+

text \<open>Every walk contains a path connecting the same vertices.\<close>
lemma walk_to_path:
  assumes "walk xs" "xs \<noteq> Nil" "hd xs = v" "last xs = w"
  shows "\<exists>ys. v \<leadsto>ys\<leadsto> w \<and> set ys \<subseteq> set xs"
proof-
  text \<open>We prove this by removing loops from @{term xs} until @{term xs} is a path.
    We want to perform induction over @{term "length xs"}, but @{term xs} in
    @{term "set ys \<subseteq> set xs"} should not be part of the induction hypothesis. To accomplish this,
    we hide @{term "set xs"} behind a definition for this specific part of the goal.\<close>
  define target_set where "target_set = set xs"
  hence "set xs \<subseteq> target_set" by simp
  thus "\<exists>ys. v \<leadsto>ys\<leadsto> w \<and> set ys \<subseteq> target_set"
    using assms
  proof (induct "length xs" arbitrary: xs rule: infinite_descent0)
    case (smaller n)
    then obtain xs where
      xs: "n = length xs" "walk xs" "xs \<noteq> Nil" "hd xs = v" "last xs = w" "set xs \<subseteq> target_set" and
      hyp: "\<not>(\<exists>ys. v \<leadsto>ys\<leadsto> w \<and> set ys \<subseteq> target_set)" by blast
    text \<open>If @{term xs} is not a path, then @{term xs} is not distinct and we can decompose it.\<close>
    then obtain ys zs u
      where xs_decomp: "u \<in> set ys" "distinct ys" "xs = ys @ u # zs"
      using not_distinct_conv_prefix by (metis path_from_toI)
    text \<open>@{term u} appears in @{term xs}, so we have a loop in @{term xs} starting from an
      occurrence of @{term u} in @{term xs} ending in the vertex @{term u} in @{term "u # ys"}.
      We define @{term zs} as @{term xs} without this loop.\<close>
    obtain ys' ys_suffix where
      ys_decomp: "ys = ys' @ u # ys_suffix" by (meson split_list xs_decomp(1))
    define zs' where "zs' = ys' @ u # zs"
    have "walk zs'" unfolding zs'_def using xs(2) xs_decomp(3) ys_decomp
      by (metis walk_decomp list.sel(1) list.simps(3) walk_comp walk_last_edge)
    moreover have "length zs' < n" unfolding zs'_def by (simp add: xs(1) xs_decomp(3) ys_decomp)
    moreover have "hd zs' = v" unfolding zs'_def
      by (metis append_is_Nil_conv hd_append list.sel(1) xs(4) xs_decomp(3) ys_decomp)
    moreover have "last zs' = w" unfolding zs'_def using xs(5) xs_decomp(3) by auto
    moreover have "set zs' \<subseteq> target_set" unfolding zs'_def using xs(6) xs_decomp(3) ys_decomp by auto
    ultimately show ?case using zs'_def hyp by blast
  qed simp
qed

corollary connected_by_path:
  assumes "v \<rightarrow>\<^sup>* w"
  obtains xs where "v \<leadsto>xs\<leadsto> w"
  using assms connected_def walk_to_path by blast

subsection \<open>Cycles\<close>

text \<open>A cycle in an undirected graph is a closed path with at least 3 different vertices.
  Closed paths with 0 or 1 vertex do not exist (graphs are loop-free), and paths with 2 vertices
  are not considered loops in undirected graphs.\<close>
definition cycle :: "'a Walk \<Rightarrow> bool" where
  "cycle xs \<equiv> path xs \<and> length xs > 2 \<and> last xs \<rightarrow> hd xs"

lemma cycleI [intro]: "\<lbrakk> path xs; length xs > 2; last xs\<rightarrow>hd xs \<rbrakk> \<Longrightarrow> cycle xs"
  unfolding cycle_def by blast
lemma cycleE: "cycle xs \<Longrightarrow> path xs \<and> xs \<noteq> Nil \<and> length xs > 2 \<and> last xs\<rightarrow>hd xs"
  unfolding cycle_def by auto

text \<open>We can now show a lemma that explains how to construct cycles from certain paths.
  If two paths both starting from @{term v} diverge immediately and meet again on their
  last vertices, then the graph contains a cycle with @{term v} on it.

  Note that if two paths do not diverge immediately but only eventually, then
  @{prop maximal_common_prefix} can be used to remove the common prefix.\<close>
lemma meeting_paths_produce_cycle:
  assumes xs: "path (v # xs)" "xs \<noteq> Nil"
      and ys: "path (v # ys)" "ys \<noteq> Nil"
      and meet: "last xs = last ys"
      and diverge: "hd xs \<noteq> hd ys"
  shows "\<exists>zs. cycle zs \<and> hd zs = v"
proof-
  have "set xs \<inter> set ys \<noteq> {}" using meet xs(2) ys(2) last_in_set by fastforce
  then obtain xs' x xs'' where xs': "xs = xs' @ x # xs''" "set xs' \<inter> set ys = {}" "x \<in> set ys"
    using split_list_first_prop[of xs "\<lambda>x. x \<in> set ys"] by (metis disjoint_iff_not_equal)
  then obtain ys' ys'' where ys': "ys = ys' @ x # ys''" "x \<notin> set ys'"
    using split_list_first_prop[of ys "\<lambda>y. y = x"] by blast

  let ?zs = "v # xs' @ x # (rev ys')"
  have "last ?zs\<rightarrow>hd ?zs"
    using undirected walk_first_edge walk_first_edge' ys'(1) ys(1) last_rev by fastforce
  moreover have "path ?zs" proof
    have "walk (x # rev ys')" proof(cases)
      assume "ys' = Nil" thus ?thesis using \<open>last ?zs\<rightarrow>hd ?zs\<close> edges_are_in_V(1) by auto
    next
      assume "ys' \<noteq> Nil"
      moreover hence "last ys'\<rightarrow>x" using walk_last_edge walk_tl ys'(1) ys(1) by fastforce
      moreover have "hd (rev ys') = last ys'" by (simp add: \<open>ys' \<noteq> []\<close> hd_rev)
      moreover have "walk (rev ys')" by (metis list.sel(3) walk_decomp(1) walk_rev walk_tl ys'(1) ys(1))
      ultimately show "walk (x # rev ys')" using path_cons undirected ys'(1) ys(1) by auto
    qed
    thus "walk (v # xs' @ x # rev ys')" using xs'(1) xs(1)
      by (metis append_Cons list.sel(1) list.simps(3) walk_comp walk_decomp(1) walk_last_edge)
  next
    show "distinct (v # xs' @ x # rev ys')" unfolding distinct_append distinct.simps(2) set_append
      using xs'(1,2) xs(1) ys'(1) ys(1) by auto
  qed
  moreover have "length ?zs \<noteq> 2" using diverge xs'(1) ys'(1) by auto
  ultimately show ?thesis using cycleI[of ?zs] by auto
qed

text \<open>A graph with unique paths between every pair of connected vertices has no cycles.\<close>
lemma unique_paths_implies_no_cycles:
  assumes unique_paths: "\<And>v w. v \<rightarrow>\<^sup>* w \<Longrightarrow> \<exists>!xs. v \<leadsto>xs\<leadsto> w"
  shows "\<And>xs. \<not>cycle xs"
proof
  fix xs assume "cycle xs"
  let ?v = "hd xs"
  let ?w = "last xs"
  let ?ys = "[?v,?w]"
  define good where "good xs \<longleftrightarrow> ?v \<leadsto>xs\<leadsto> ?w" for xs
  have "path ?ys" using \<open>cycle xs\<close> cycle_def no_loops undirected by auto
  hence "good ?ys" unfolding good_def by (simp add: path_from_toI)
  moreover have "good xs" unfolding good_def by (simp add: path_from_toI \<open>cycle xs\<close> cycleE)
  moreover have "?ys \<noteq> xs" using \<open>cycle xs\<close>
    by (metis One_nat_def Suc_1 cycleE length_Cons less_not_refl list.size(3))
  ultimately have "\<not>(\<exists>!xs. good xs)" by blast
  moreover have "connected ?v ?w" using \<open>cycle xs\<close> cycleE by blast
  ultimately show False unfolding good_def using unique_paths by blast
qed

text \<open>
  A graph without cycles (also called a forest) has a unique path between every pair of connected
  vertices.
\<close>
lemma no_cycles_implies_unique_paths:
  assumes no_cycles: "\<And>xs. \<not>cycle xs" and connected: "v \<rightarrow>\<^sup>* w"
  shows "\<exists>!xs. v \<leadsto>xs\<leadsto> w"
proof (rule ex_ex1I)
  show "\<exists>xs. v \<leadsto>xs\<leadsto> w" using connected connected_by_path by blast
next
  fix xs ys
  assume "v \<leadsto>xs\<leadsto> w" "v \<leadsto>ys\<leadsto> w"
  hence xs_valid: "path xs" "xs \<noteq> Nil" "hd xs = v" "last xs = w"
    and ys_valid: "path ys" "ys \<noteq> Nil" "hd ys = v" "last ys = w" by blast+
  show "xs = ys" proof (rule ccontr)
    assume "xs \<noteq> ys"
    hence "\<exists>ps xs' ys'. xs = ps @ xs' \<and> ys = ps @ ys' \<and> (xs' = Nil \<or> ys' = Nil \<or> hd xs' \<noteq> hd ys')"
      by (induct xs ys rule: list_induct2', blast, blast, blast)
         (metis (no_types, hide_lams) append_Cons append_Nil list.sel(1))
    then obtain ps xs' ys' where
      ps: "xs = ps @ xs'" "ys = ps @ ys'" "xs' = Nil \<or> ys' = Nil \<or> hd xs' \<noteq> hd ys'" by blast

    have "last xs \<in> set ps" if "xs' = Nil" using xs_valid(2) ps(1) by (simp add: that)
    hence xs_not_nil: "xs' \<noteq> Nil" using \<open>xs \<noteq> ys\<close> ys_valid(1,4) ps(1,2) xs_valid(4) by auto

    have "last ys \<in> set ps" if "ys' = Nil" using ys_valid(2) ps(2) by (simp add: that)
    hence ys_not_nil: "ys' \<noteq> Nil" using \<open>xs \<noteq> ys\<close> xs_valid(1,4) ps(1,2) ys_valid(4) by auto

    have "\<exists>zs. cycle zs" proof-
      let ?v = "last ps"
      have *: "ps \<noteq> Nil" using xs_valid(2,3) ys_valid(2,3) ps(1,2,3) by auto
      have "path (?v # xs')" using xs_valid(1) ps(1) * walk_decomp(2)
        by (metis append_Cons append_assoc append_butlast_last_id distinct_append self_append_conv2)
      moreover have "path (?v # ys')" using ys_valid(1) ps(2) * walk_decomp(2)
        by (metis append_Cons append_assoc append_butlast_last_id distinct_append self_append_conv2)
      moreover have "last xs' = last ys'"
        using xs_valid(4) ys_valid(4) xs_not_nil ys_not_nil ps(1,2) by auto
      ultimately show ?thesis using ps(3) meeting_paths_produce_cycle xs_not_nil ys_not_nil by blast
    qed
    thus False using no_cycles by blast
  qed
qed

end \<comment> \<open>locale Graph\<close>
end
