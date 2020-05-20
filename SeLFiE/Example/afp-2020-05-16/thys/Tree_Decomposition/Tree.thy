section \<open>Trees\<close>

theory Tree
imports Graph begin

text \<open>A tree is a connected graph without cycles.\<close>
locale Tree = Graph +
  assumes connected: "\<lbrakk> v \<in> V; w \<in> V \<rbrakk> \<Longrightarrow> v \<rightarrow>\<^sup>* w" and no_cycles: "\<not>cycle xs"
begin

subsection \<open>Unique Connecting Path\<close>

text \<open>For every pair of vertices in a tree, there exists a unique path connecting these two
  vertices.
\<close>
lemma unique_connecting_path: "\<lbrakk> v \<in> V; w \<in> V \<rbrakk> \<Longrightarrow> \<exists>!xs. v \<leadsto>xs\<leadsto> w"
  using connected no_cycles no_cycles_implies_unique_paths by blast

text \<open>Let us define a function mapping pair of vertices to their unique connecting path.\<close>
end \<comment> \<open>locale Tree\<close>
definition unique_connecting_path :: "('a, 'b) Graph_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a Walk"
  (infix "\<leadsto>\<index>" 71) where "unique_connecting_path G v w \<equiv> THE xs. v \<leadsto>xs\<leadsto>\<^bsub>G\<^esub> w"
text \<open>We defined this outside the locale in order to be able to use the index in the shorthand
  syntax @{term "v \<leadsto>\<index> w"}.\<close>

context Tree begin

lemma unique_connecting_path_set:
  assumes "v \<in> V" "w \<in> V"
  shows "v \<in> set (v \<leadsto> w)" "w \<in> set (v \<leadsto> w)"
  using theI'[OF unique_connecting_path[OF assms], folded unique_connecting_path_def]
    hd_in_set last_in_set by fastforce+

lemma unique_connecting_path_properties:
  assumes "v \<in> V" "w \<in> V"
  shows "path (v \<leadsto> w)" "v \<leadsto> w \<noteq> Nil" "hd (v \<leadsto> w) = v" "last (v \<leadsto> w) = w"
  using theI'[OF unique_connecting_path[OF assms], folded unique_connecting_path_def] by blast+

lemma unique_connecting_path_unique:
  assumes "v \<leadsto>xs\<leadsto> w"
  shows "xs = v \<leadsto> w"
proof-
  have "v \<in> V" "w \<in> V" using assms connected_in_V by blast+
  with unique_connecting_path_properties[OF this] show ?thesis
    using assms unique_connecting_path by blast
qed
corollary unique_connecting_path_connects: "\<lbrakk> v \<in> V; w \<in> V \<rbrakk> \<Longrightarrow> v \<leadsto>(v\<leadsto>w) \<leadsto> w"
  using unique_connecting_path unique_connecting_path_unique by blast

lemma unique_connecting_path_rev:
  assumes "v \<in> V" "w \<in> V"
  shows "v \<leadsto> w = rev (w \<leadsto> v)"
proof-
  have "v \<leadsto>(rev (w \<leadsto> v))\<leadsto> w" using assms
    by (simp add: unique_connecting_path_properties walk_rev hd_rev last_rev path_from_toI)
  thus ?thesis using unique_connecting_path_unique by simp
qed

lemma unique_connecting_path_decomp:
  assumes "v \<in> V" "w \<in> V" "v \<leadsto> w = ps @ u # ps'"
  shows "ps @ [u] = v \<leadsto> u" "u # ps' = u \<leadsto> w"
proof-
  have "hd (ps @ [u]) = v"
    by (metis append_Nil assms hd_append2 list.sel(1) unique_connecting_path_properties(3))
  moreover have "path (ps @ [u])" using unique_connecting_path_properties(1)[OF assms(1,2)]
    unfolding assms(3)
    by (metis distinct.simps(2) distinct1_rotate list.sel(1) list.simps(3) not_distinct_conv_prefix
        path_decomp(1) rev.simps(2) rotate1.simps(2) walk_comp walk_decomp(2) walk_last_edge walk_rev)
  moreover have "last (ps @ [u]) = u" "ps @ [u] \<noteq> Nil" by simp_all
  ultimately show "ps @ [u] = v \<leadsto> u" using unique_connecting_path_unique by blast
next
  have "last (u # ps') = w"
    using assms unique_connecting_path_properties(4) by fastforce
  moreover have "path (u # ps')" using unique_connecting_path_properties(1)[OF assms(1,2)]
    unfolding assms(3) using path_decomp(2) by blast
  moreover have "hd (u # ps') = u" "u # ps' \<noteq> Nil" by simp_all
  ultimately show "u # ps' = u \<leadsto> w" using unique_connecting_path_unique by blast
qed

lemma unique_connecting_path_tl:
  assumes "v \<in> V" "u \<in> set (w \<leadsto> v)" "u\<rightarrow>w"
  shows "tl (w \<leadsto> v) = u \<leadsto> v"
proof (rule ccontr)
  assume contra: "\<not>?thesis"
  from assms(2) obtain ps ps' where
    ps: "w \<leadsto> v = ps @ u # ps'" by (meson split_list)
  have "cycle (ps @ [u])" proof
    show "path (ps @ [u])" using unique_connecting_path_decomp assms(1,3) ps
        by (metis edges_are_in_V unique_connecting_path_properties(1))
    show "length (ps @ [u]) > 2" proof (rule ccontr)
      assume "\<not>?thesis"
      moreover have "u \<noteq> w" using assms(3) no_loops by blast
      ultimately have "length (ps @ [u]) = 2"
        by (metis edges_are_in_V(2) assms(1,3) hd_append length_0_conv length_append_singleton
            less_2_cases linorder_neqE_nat list.sel(1) nat.simps(1) ps snoc_eq_iff_butlast
            unique_connecting_path_properties(3))
      hence "tl (w \<leadsto> v) = u # ps'"
        by (metis One_nat_def Suc_1 append_Nil diff_Suc_1 length_0_conv length_Cons
            length_append_singleton list.collapse nat.simps(3) ps tl_append2)
      moreover have "u # ps' = u \<leadsto> v"
        using unique_connecting_path_decomp assms(1,3) edges_are_in_V(2) ps by blast
      ultimately show False using contra by simp
    qed
    show "last (ps @ [u]) \<rightarrow> hd (ps @ [u])" using assms(3)
      by (metis edges_are_in_V(2) unique_connecting_path_properties(3)
          assms(1) hd_append list.sel(1) ps snoc_eq_iff_butlast)
  qed
  thus False using no_cycles by auto
qed

text \<open>Every tree with at least two vertices contains an edge.\<close>
lemma tree_has_edge:
  assumes "card V > 1"
  shows "\<exists>v w. v\<rightarrow>w"
proof-
  obtain v where v: "v \<in> V" using assms
    by (metis List.finite_set One_nat_def card.empty card_mono empty_set less_le_trans linear
        not_less subsetI zero_less_Suc)
  then obtain w where "w \<in> V" "v \<noteq> w" using assms
    by (metis (no_types, lifting) One_nat_def card.empty card.insert distinct.simps(2) empty_set
      finite.intros(1) finite_distinct_list finite_vertex_set hd_in_set last.simps last_in_set
      less_or_eq_imp_le list.exhaust_sel list.simps(15) not_less path_singleton)
  hence "v \<rightarrow> hd (tl (v\<leadsto>w))" using v
    by (metis unique_connecting_path_properties last.simps list.exhaust_sel walk_first_edge')
  thus ?thesis by blast
qed

subsection \<open>Separations\<close>

text \<open>
  Removing a single edge always splits a tree into two subtrees.  Here we define the set of vertices
  of the left subtree.  The definition may not be obvious at first glance, but we will soon prove
  that it behaves as expected.  We say that a vertex @{term u} is in the left subtree if and only
  if the unique path from @{term u} to @{term t} visits @{term s}.
\<close>
definition left_tree :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "left_tree s t \<equiv> { u \<in> V. s \<in> set (u \<leadsto> t) }"
lemma left_treeI [intro]: "\<lbrakk> u \<in> V; s \<in> set (u \<leadsto> t) \<rbrakk> \<Longrightarrow> u \<in> left_tree s t"
  unfolding left_tree_def by blast
lemma left_treeE: "u \<in> left_tree s t \<Longrightarrow> u \<in> V \<and> s \<in> set (u \<leadsto> t)"
  unfolding left_tree_def by blast

lemma left_tree_in_V: "left_tree s t \<subseteq> V" unfolding left_tree_def by blast
lemma left_tree_initial: "\<lbrakk> s \<in> V; t \<in> V \<rbrakk> \<Longrightarrow> s \<in> left_tree s t"
  unfolding left_tree_def by (simp add: unique_connecting_path_set(1))
lemma left_tree_initial': "\<lbrakk> s \<in> V; t \<in> V; s \<noteq> t \<rbrakk> \<Longrightarrow> t \<notin> left_tree s t"
  by (metis distinct.simps(2) last.simps left_treeE list.discI list.sel(1) path_from_toI
      path_singleton set_ConsD unique_connecting_path_unique)
lemma left_tree_initial_edge: "s\<rightarrow>t \<Longrightarrow> t \<notin> left_tree s t"
  using edges_are_in_V(1) left_tree_initial' no_loops undirected by blast

text \<open>The union of the left and right subtree is @{term V}.\<close>
lemma left_tree_union_V:
  assumes "s\<rightarrow>t"
  shows "left_tree s t \<union> left_tree t s = V"
proof
  show "left_tree s t \<union> left_tree t s \<subseteq> V" using left_tree_in_V by auto
  {
    have s: "s \<in> V" and t: "t \<in> V" using assms using edges_are_in_V by blast+
    text \<open>Assume to the contrary that @{term "u \<in> V"} is in neither part.\<close>
    fix u assume u: "u \<in> V" "u \<notin> left_tree s t" "u \<notin> left_tree t s"
    text \<open>Then we can construct two different paths from @{term s} to @{term u}, which, in a
      tree, is a contradiction.  First, we get paths from @{term s} to @{term u} and from
      @{term t} to @{term u}.\<close>
    let ?xs = "s \<leadsto> u"
    let ?ys = "t \<leadsto> u"
    have "t \<notin> set ?xs" using u(1,3) unfolding left_tree_def
      by (metis (no_types, lifting) unique_connecting_path_rev mem_Collect_eq s set_rev)
    have "s \<notin> set ?ys" using u(1,2) unfolding left_tree_def
      by (metis (no_types, lifting) unique_connecting_path_rev mem_Collect_eq set_rev t)

    text \<open>Now we can define two different paths from @{term s} to @{term u}.\<close>
    define xs' where [simp]: "xs' = ?xs"
    define ys' where [simp]: "ys' = s # ?ys"

    have "path ys'" using path_cons \<open>s \<notin> set ?ys\<close> assms
      by (simp add: unique_connecting_path_properties(1-3) t u(1))
    moreover have "path xs'" "xs' \<noteq> []" "ys' \<noteq> []"  "hd xs' = s" "last xs' = u"
      by (simp_all add: unique_connecting_path_properties s u(1))
    moreover have "hd ys' = s" "last ys' = u"
      by simp (simp add: unique_connecting_path_properties(2,4) t u(1))
    moreover have "xs' \<noteq> ys'" using unique_connecting_path_set(1) \<open>t \<notin> set ?xs\<close> t u(1) by auto
    text \<open>The existence of two different paths is a contradiction.\<close>
    ultimately have False using unique_connecting_path_unique by blast
  }
  thus "V \<subseteq> left_tree s t \<union> left_tree t s" by blast
qed

text \<open>The left and right subtrees are disjoint.\<close>
lemma left_tree_disjoint:
  assumes "s\<rightarrow>t"
  shows "left_tree s t \<inter> left_tree t s = {}"
proof (rule ccontr)
  assume "\<not>?thesis"
  then obtain u where u: "u \<in> V" "s \<in> set (u \<leadsto> t)" "t \<in> set (u \<leadsto> s)" using left_treeE by blast

  have s: "s \<in> V" and t: "t \<in> V" using assms edges_are_in_V by blast+

  obtain ps ps' where ps: "u \<leadsto> t = ps @ s # ps'" by (meson split_list u(2))
  hence "ps' \<noteq> Nil"
    using assms last_snoc no_loops unique_connecting_path_properties(4)[OF u(1) t] by auto
  hence *: "length (ps @ [s]) < length (u \<leadsto> t)" by (simp add: ps)

  have ps': "ps @ [s] = u \<leadsto> s" using ps unique_connecting_path_decomp t u(1) by blast

  then obtain qs qs' where qs: "ps @ [s] = qs @ t # qs'" using split_list[OF u(3)] by auto
  hence "qs' \<noteq> Nil" using assms last_snoc no_loops by auto
  hence **: "length (qs @ [t]) < length (ps @ [s])" by (simp add: qs)

  have "qs @ [t] = u \<leadsto> t" using qs ps' unique_connecting_path_decomp s u(1) by metis
  thus False using less_trans[OF ** *] by simp
qed

text \<open>
  The path from a vertex in the left subtree to a vertex in the right subtree goes through @{term s}.
  In other words, an edge @{term "s\<rightarrow>t"} is a separator in a tree.
\<close>
theorem left_tree_separates:
  assumes st: "s\<rightarrow>t" and u: "u \<in> left_tree s t" and u': "u' \<in> left_tree t s"
  shows "s \<in> set (u \<leadsto> u')"
proof (rule ccontr)
  assume "\<not>?thesis"
  with assms have "set (u \<leadsto> u') \<subseteq> left_tree s t"
  proof(induct "u \<leadsto> u'" arbitrary: u u')
    case Nil thus ?case using unique_connecting_path_properties(2) by auto
  next
    case (Cons x xs u u')
    have "x = u" using Cons.hyps(2) Cons.prems(2,3)
      by (metis left_treeE list.sel(1) unique_connecting_path_properties(3))
    hence "u\<rightarrow>hd xs" using Cons.hyps(2) Cons.prems(2,3) st
      by (metis IntI left_tree_disjoint distinct.simps(2) last.simps left_treeE list.set(1)
          unique_connecting_path_properties(1,4) walk_first_edge')
    hence "u \<in> V" "hd xs \<in> V" using edges_are_in_V by blast+
    have *: "xs = hd xs \<leadsto> u'"
      by (metis Cons.hyps(2) Cons.prems(2,3) IntI left_tree_disjoint distinct.simps(2) last.simps
          left_treeE list.sel(1,3) list.set(1) path_from_toI st
          unique_connecting_path_properties(1,3,4) unique_connecting_path_unique walk_tl)
    moreover hence "s \<notin> set (hd xs \<leadsto> u')" using Cons.hyps(2) Cons.prems(4)
      by (metis list.set_intros(2))
    moreover have "hd xs \<in> left_tree s t" proof (rule ccontr)
      assume "\<not>?thesis"
      hence "hd xs \<in> left_tree t s" using \<open>hd xs \<in> V\<close> st left_tree_union_V by fastforce
      hence "t \<in> set (hd xs \<leadsto> s)" using left_treeE by blast
      let ?ys' = "hd xs \<leadsto> s"
      let ?ys = "u # ?ys'"
      have "u \<notin> set ?ys'" proof
        assume "u \<in> set ?ys'"
        hence "tl ?ys' = u \<leadsto> s"
          using unique_connecting_path_tl \<open>u\<rightarrow>hd xs\<close> edges_are_in_V(1) st by auto
        moreover have "t \<noteq> hd xs" proof
          let ?ys = "[u, hd xs]"
          have "t \<noteq> u" using Cons.prems(2) left_tree_initial_edge st by blast
          assume "t = hd xs"
          hence "?ys = u \<leadsto> t"
            using unique_connecting_path_unique[of u ?ys "hd xs"] \<open>u\<rightarrow>hd xs\<close> \<open>t \<noteq> u\<close>
            by (simp add: path_from_toI)
          hence "s \<notin> set (u \<leadsto> t)"
            by (metis Cons.hyps(2) Cons.prems(4) \<open>t = hd xs\<close> \<open>x = u\<close> distinct.simps(2)
                distinct_singleton list.set_intros(1) no_loops set_ConsD st)
          thus False using Cons.prems(2) left_treeE by blast
        qed
        ultimately have "t \<in> set (u \<leadsto> s)" using \<open>t \<in> set ?ys'\<close> \<open>hd xs \<in> V\<close> st
          by (metis edges_are_in_V(1) unique_connecting_path_properties(2,3) list.collapse set_ConsD)
        thus False using Cons.prems(2) st \<open>u \<in> V\<close>
          by (meson left_tree_disjoint disjoint_iff_not_equal left_treeI)
      qed
      hence "path ?ys" using path_cons \<open>u\<rightarrow>hd xs\<close>
        by (metis unique_connecting_path_properties(1-3) edges_are_in_V st)
      moreover have "?ys \<noteq> Nil" "hd ?ys = u" by simp_all
      moreover have "last ?ys = s" using st unique_connecting_path_properties(2,4) \<open>hd xs \<in> V\<close>
        by (simp add: edges_are_in_V(1))
      ultimately have "?ys = u \<leadsto> s" using unique_connecting_path_unique by blast
      hence "t \<in> set (u \<leadsto> s)" by (metis \<open>t \<in> set ?ys'\<close> list.set_intros(2))
      thus False using Cons.prems(2) \<open>u \<in> V\<close> st
        by (meson left_tree_disjoint disjoint_iff_not_equal left_treeI)
    qed
    ultimately have "set (hd xs \<leadsto> u') \<subseteq> left_tree s t"
      using Cons.hyps(1) st Cons.prems(3) by blast
    hence "set xs \<subseteq> left_tree s t" using * by simp
    thus ?case using Cons.hyps(2) Cons.prems(2,3)
      by (metis insert_subset left_treeE list.sel(1) list.set(2) unique_connecting_path_properties(3))
  qed
  hence "u' \<in> left_tree s t" using left_treeE u u' unique_connecting_path_set(2) by auto
  thus False by (meson left_tree_disjoint disjoint_iff_not_equal st u')
qed

text \<open>By symmetry, the path also visits @{term t}.\<close>
corollary left_tree_separates':
  assumes "s\<rightarrow>t" "u \<in> left_tree s t" "u' \<in> left_tree t s"
  shows "t \<in> set (u \<leadsto> u')"
  using assms left_tree_separates by (metis left_treeE set_rev undirected unique_connecting_path_rev)

end \<comment> \<open>locale Tree\<close>

subsection \<open>Rooted Trees\<close>

text \<open>A rooted tree is a tree with a distinguished vertex called root.\<close>

locale RootedTree = Tree +
  fixes root :: 'a
  assumes root_in_V: "root \<in> V"
begin
  text \<open>In a rooted tree, we can define the parent relation.\<close>
  definition parent :: "'a \<Rightarrow> 'a" where
    "parent v \<equiv> hd (tl (v \<leadsto> root))"

  lemma parent_edge: "\<lbrakk> v \<in> V; v \<noteq> root \<rbrakk> \<Longrightarrow> v\<rightarrow>parent v" unfolding parent_def
    by (metis last.simps list.exhaust_sel root_in_V unique_connecting_path_properties walk_first_edge')
  lemma parent_edge_root: "v\<rightarrow>root \<Longrightarrow> parent v = root" unfolding parent_def
    by (metis edges_are_in_V(1) path_from_toE undirected unique_connecting_path
        unique_connecting_path_set(2) unique_connecting_path_tl unique_connecting_path_unique)
  lemma parent_in_V: "\<lbrakk> v \<in> V; v \<noteq> root \<rbrakk> \<Longrightarrow> parent v \<in> V"
    using parent_edge edges_are_in_V(2) by blast
  lemma parent_edge_cases: "v\<rightarrow>w \<Longrightarrow> w = parent v \<or> v = parent w" unfolding parent_def
    by (metis Un_iff edges_are_in_V(1) left_tree_initial left_tree_separates' left_tree_union_V
        root_in_V undirected unique_connecting_path_properties(3) unique_connecting_path_tl)

  lemma sibling_path:
    assumes v: "v \<in> V" "v \<noteq> root" and w: "w \<in> V" "w \<noteq> root" and vw: "v \<noteq> w" "parent v = parent w"
    shows "v\<leadsto>w = [v,parent v,w]" (is "_ = ?xs")
  proof-
    have "path ?xs" using v w vw
      by (metis distinct_length_2_or_more distinct_singleton no_loops parent_edge undirected
          walk.Cons walk_2)
    thus ?thesis using unique_connecting_path_unique by fastforce
  qed
end \<comment> \<open>locale RootedTree\<close>

end
