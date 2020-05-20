section \<open>Tree Decompositions\<close>

theory TreeDecomposition
imports Tree begin

text \<open>A tree decomposition of a graph.\<close>

locale TreeDecomposition = Graph G + T: Tree T
  for G :: "('a, 'b) Graph_scheme" (structure) and T :: "('c,'d) Graph_scheme" +
  fixes bag :: "'c \<Rightarrow> 'a set"
  assumes
    \<comment> \<open>Every vertex appears somewhere\<close>
    bags_union: "\<Union> { bag t | t. t \<in> V\<^bsub>T\<^esub> } = V"
     \<comment> \<open>Every edge is covered\<close>
    and bags_edges: "v\<rightarrow>w \<Longrightarrow> \<exists>t \<in> V\<^bsub>T\<^esub>. v \<in> bag t \<and> w \<in> bag t"
    \<comment> \<open>Every vertex appearing in @{term s} and @{term u} also appears in every bag on the path
        connecting @{term s} and @{term u}\<close>
    and bags_continuous: "\<lbrakk> s \<in> V\<^bsub>T\<^esub>; u \<in> V\<^bsub>T\<^esub>; t \<in> set (s \<leadsto>\<^bsub>T\<^esub> u) \<rbrakk> \<Longrightarrow> bag s \<inter> bag u \<subseteq> bag t"
begin
text \<open>
  Following the usual literature, we will call elements of @{term V} vertices and
  elements of @{term "V\<^bsub>T\<^esub>"} bags (or nodes) from now on.\<close>

subsection \<open>Width of a Tree Decomposition\<close>

text \<open>We define the width of this tree decomposition as the size of the largest bag minus 1.\<close>
abbreviation "bag_cards \<equiv> { card (bag t) | t. t \<in> V\<^bsub>T\<^esub> }"
definition "max_bag_card \<equiv> Max bag_cards"
text \<open>We need a special case for @{term "V\<^bsub>T\<^esub> = {}"} because in this case @{const max_bag_card}
  is not well-defined.\<close>
definition "width \<equiv> if V\<^bsub>T\<^esub> = {} then 0 else max_bag_card - 1"

lemma bags_in_V: "t \<in> V\<^bsub>T\<^esub> \<Longrightarrow> bag t \<subseteq> V" using bags_union Sup_upper mem_Collect_eq by blast
lemma bag_finite: "t \<in> V\<^bsub>T\<^esub> \<Longrightarrow> finite (bag t)" using bags_in_V finite_subset finite_vertex_set by blast
lemma bag_bound_V: "t \<in> V\<^bsub>T\<^esub> \<Longrightarrow> card (bag t) \<le> card V" by (simp add: bags_in_V card_mono finite_vertex_set)
lemma bag_bound_V_empty: "\<lbrakk> V = {}; t \<in> V\<^bsub>T\<^esub> \<rbrakk> \<Longrightarrow> card (bag t) = 0" using bag_bound_V by auto
lemma empty_tree_empty_V: "V\<^bsub>T\<^esub> = {} \<Longrightarrow> V = {}" using bags_union by simp
lemma bags_exist: "v \<in> V \<Longrightarrow> \<exists>t \<in> V\<^bsub>T\<^esub>. v \<in> bag t" using bags_union using UnionE mem_Collect_eq by auto

text \<open>
  The width is never larger than the number of vertices, and if there is at least one vertex
  in the graph, then it is always smaller.  This is trivially true because a bag contains at most
  all of @{term V}.  However, the proof is not fully trivial because we also need to show that
  @{const width} is well-defined.\<close>
lemma bag_cards_finite: "finite bag_cards" using T.finite_vertex_set by simp
lemma bag_cards_nonempty: "V \<noteq> {} \<Longrightarrow> bag_cards \<noteq> {}"
  using bag_cards_finite empty_tree_empty_V empty_Collect_eq ex_in_conv by blast
lemma max_bag_card_in_bag_cards: "V \<noteq> {} \<Longrightarrow> max_bag_card \<in> bag_cards" unfolding max_bag_card_def
  using Max_in bag_cards_finite bag_cards_nonempty by auto
lemma max_bag_card_lower_bound_bag: "t \<in> V\<^bsub>T\<^esub> \<Longrightarrow> max_bag_card \<ge> card (bag t)"
  by (metis (mono_tags, lifting) Max_ge bag_cards_finite max_bag_card_def mem_Collect_eq)
lemma max_bag_card_lower_bound_1: assumes "V \<noteq> {}" shows "max_bag_card > 0" proof-
  have "\<exists>v \<in> V. \<exists>t \<in> V\<^bsub>T\<^esub>. v \<in> bag t" using \<open>V \<noteq> {}\<close> bags_union by blast
  thus "max_bag_card > 0" unfolding max_bag_card_def using bag_finite
    card_gt_0_iff emptyE Max_gr_iff[OF bag_cards_finite bag_cards_nonempty[OF assms]] by auto
qed
lemma max_bag_card_upper_bound_V: "V \<noteq> {} \<Longrightarrow> max_bag_card \<le> card V" unfolding max_bag_card_def
  using Max_le_iff[OF bag_cards_finite bag_cards_nonempty] bag_bound_V by blast

lemma width_upper_bound_V: "V \<noteq> {} \<Longrightarrow> width < card V" unfolding width_def
  using max_bag_card_upper_bound_V max_bag_card_lower_bound_1
    diff_less empty_tree_empty_V le_neq_implies_less less_imp_diff_less zero_less_one by presburger
lemma width_V_empty: "V = {} \<Longrightarrow> width = 0" unfolding width_def max_bag_card_def
  using bag_bound_V_empty T.finite_vertex_set by (cases "V\<^bsub>T\<^esub> = {}") auto
lemma width_bound_V_le: "width \<le> card V - 1"
  using width_upper_bound_V width_V_empty by (cases "V = {}") auto
lemma width_lower_bound_1:
  assumes "v\<rightarrow>w"
  shows "width \<ge> 1"
proof-
  obtain t where t: "t \<in> V\<^bsub>T\<^esub>" "v \<in> bag t" "w \<in> bag t" using bags_edges assms by blast
  have "card (bag t) \<noteq> 0" using t(1,2) bag_finite card_0_eq empty_iff by blast
  moreover have "card (bag t) \<noteq> 1" using t(2,3) assms no_loops
    by (metis One_nat_def card_Suc_eq empty_iff insertE)
  ultimately have "card (bag t) \<ge> 2" by simp
  hence "max_bag_card > 1" using t(1) max_bag_card_lower_bound_bag by fastforce
  thus ?thesis unfolding width_def using t(1) by fastforce
qed

end \<comment> \<open>locale TreeDecomposition\<close>

subsection \<open>Treewidth of a Graph\<close>

context Graph begin

text \<open>The treewidth of a graph is the minimum treewidth over all its tree decompositions.
  Here we assume without loss of generality that the universe of the vertices of the tree
  is @{type nat}.  Because trees are finite, @{type nat} always contains enough elements.\<close>
abbreviation treewidth_cards :: "nat set" where "treewidth_cards \<equiv>
  { TreeDecomposition.width T bag | (T :: nat Graph) bag. TreeDecomposition G T bag }"
definition treewidth :: "nat" where "treewidth \<equiv> Min treewidth_cards"

text \<open>Every graph has a trivial tree decomposition consisting of a single bag containing all of
  @{term V}.\<close>
proposition tree_decomposition_exists: "\<exists>(T :: 'c Graph) bag. TreeDecomposition G T bag" proof-
  obtain x where "x \<in> (UNIV :: 'c set)" by blast
  define T where [simp]: "T = \<lparr> verts = {x}, arcs = {} \<rparr>"
  define bag where [simp]: "bag = (\<lambda>_ :: 'c. V)"
  have "Graph T" by unfold_locales simp_all
  then interpret T: Graph T .
  have "\<And>xs. \<not>T.cycle xs" using T.cycleE by auto
  moreover have "\<And>v w. v \<in> V\<^bsub>T\<^esub> \<Longrightarrow> w \<in> V\<^bsub>T\<^esub> \<Longrightarrow> T.connected v w" using T.connected_refl by auto
  ultimately have "Tree T" by unfold_locales
  then interpret T: Tree T .
  have "TreeDecomposition G T bag" by unfold_locales (simp_all add: edges_are_in_V)
  thus ?thesis by blast
qed

corollary treewidth_cards_upper_bound_V: "n \<in> treewidth_cards \<Longrightarrow> n \<le> card V - 1"
  using TreeDecomposition.width_bound_V_le by blast
corollary treewidth_cards_finite: "finite treewidth_cards"
  using treewidth_cards_upper_bound_V finite_nat_set_iff_bounded_le by auto
corollary treewidth_cards_nonempty: "treewidth_cards \<noteq> {}" by (simp add: tree_decomposition_exists)

lemma treewidth_cards_treewidth:
  "\<exists>(T :: nat Graph) bag. TreeDecomposition G T bag \<and> treewidth = TreeDecomposition.width T bag"
  using Min_in treewidth_cards_finite treewidth_cards_nonempty treewidth_def by fastforce

corollary treewidth_upper_bound_V: "treewidth \<le> card V - 1" unfolding treewidth_def
  using treewidth_cards_nonempty Min_in treewidth_cards_finite treewidth_cards_upper_bound_V by auto
corollary treewidth_upper_bound_0: "V = {} \<Longrightarrow> treewidth = 0" using treewidth_upper_bound_V by simp
corollary treewidth_upper_bound_1: "card V = 1 \<Longrightarrow> treewidth = 0" using treewidth_upper_bound_V by simp
corollary treewidth_lower_bound_1: "v\<rightarrow>w \<Longrightarrow> treewidth \<ge> 1"
  using TreeDecomposition.width_lower_bound_1 treewidth_cards_treewidth by fastforce

lemma treewidth_upper_bound_ex:
  "\<lbrakk> TreeDecomposition G (T :: nat Graph) bag; TreeDecomposition.width T bag \<le> n \<rbrakk> \<Longrightarrow> treewidth \<le> n"
  unfolding treewidth_def
  by (metis (mono_tags, lifting) Min_le dual_order.trans mem_Collect_eq treewidth_cards_finite)

end \<comment> \<open>locale Graph\<close>

subsection \<open>Separations\<close>

context TreeDecomposition begin

text \<open>
  Every edge @{term "s\<rightarrow>\<^bsub>T\<^esub> t"} in @{term T} separates @{term T}.  In a tree decomposition,
  this edge also separates @{term G}.  Proving this is our goal.  First, let us define the set of
  vertices appearing in the left subtree when separating the tree at @{term "s \<rightarrow>\<^bsub>T\<^esub> t"}.
\<close>
definition left_part :: "'c \<Rightarrow> 'c \<Rightarrow> 'a set" where
  "left_part s t \<equiv> \<Union>{ bag u | u. u \<in> T.left_tree s t }"
lemma left_partI [intro]: "\<lbrakk> v \<in> bag u; u \<in> T.left_tree s t \<rbrakk> \<Longrightarrow> v \<in> left_part s t"
  unfolding left_part_def by blast

lemma left_part_in_V: "left_part s t \<subseteq> V" unfolding left_part_def
  using T.left_tree_in_V bags_in_V by blast

text \<open>Let us define the subgraph of @{term T} induced by a vertex of @{term G}.\<close>
definition vertex_subtree :: "'a \<Rightarrow> 'c set" where
  "vertex_subtree v \<equiv> { t \<in> V\<^bsub>T\<^esub>. v \<in> bag t }"
lemma vertex_subtreeI [intro]: "\<lbrakk> t \<in> V\<^bsub>T\<^esub>; v \<in> bag t \<rbrakk> \<Longrightarrow> t \<in> vertex_subtree v"
  unfolding vertex_subtree_def by blast

text \<open>
  The suggestive name @{const vertex_subtree} is correct: Because @{term T} is a tree
  decomposition, @{term "vertex_subtree v"} is a subtree (it is connected).\<close>
lemma vertex_subtree_connected:
  assumes v: "v \<in> V" and s: "s \<in> vertex_subtree v" and t: "t \<in> vertex_subtree v"
    and xs: "s \<leadsto>xs\<leadsto>\<^bsub>T\<^esub> t"
  shows "set xs \<subseteq> vertex_subtree v"
using assms proof (induct xs arbitrary: s)
  case (Cons x xs)
  show ?case proof (cases)
    assume "xs = []" thus ?thesis using Cons.prems(3,4) by auto
  next
    assume "xs \<noteq> []"
    moreover hence "last xs = t" using Cons.prems(4) last.simps by auto
    moreover have "T.path xs" using Cons.prems(4) T.walk_tl by fastforce
    moreover have "hd xs \<in> vertex_subtree v" proof
      have "hd xs \<in> set (s \<leadsto>\<^bsub>T\<^esub> t)" using T.unique_connecting_path_unique
        using Cons.prems(4) \<open>xs \<noteq> []\<close> by auto
      hence "bag s \<inter> bag t \<subseteq> bag (hd xs)"
        using bags_continuous Cons.prems(4) T.connected_in_V by blast
      thus "v \<in> bag (hd xs)" using Cons.prems(2,3) unfolding vertex_subtree_def by blast
      show "hd xs \<in> V\<^bsub>T\<^esub>" using T.connected_in_V(1) \<open>xs \<noteq> []\<close> \<open>T.path xs\<close> by blast
    qed
    ultimately have "set xs \<subseteq> vertex_subtree v" using Cons.hyps Cons.prems(1,3) by blast
    thus ?thesis using Cons.prems(2,4) by auto
  qed
qed simp

corollary vertex_subtree_unique_path_connected:
  assumes "v \<in> V" "s \<in> vertex_subtree v" "t \<in> vertex_subtree v"
  shows "set (s \<leadsto>\<^bsub>T\<^esub> t) \<subseteq> vertex_subtree v"
  using assms vertex_subtree_connected T.unique_connecting_path_properties
  by (metis (no_types, lifting) T.unique_connecting_path T.unique_connecting_path_unique
      mem_Collect_eq vertex_subtree_def)

text \<open>
  In order to prove that edges in @{term T} are separations in @{term G}, we need one key lemma.
  If a vertex appears on both sides of a separation, then it also appears in the separation.
\<close>
lemma vertex_in_separator:
  assumes st: "s \<rightarrow>\<^bsub>T\<^esub> t" and v: "v \<in> left_part s t" "v \<in> left_part t s"
  shows "v \<in> bag s" "v \<in> bag t"
proof-
  obtain u u' where u: "v \<in> bag u" "u \<in> T.left_tree s t" "v \<in> bag u'" "u' \<in> T.left_tree t s"
    using v unfolding left_part_def by blast
  have "s \<in> set (u \<leadsto>\<^bsub>T\<^esub> u')" using T.left_tree_separates st u by blast
  thus "v \<in> bag s" using bags_continuous u by (meson IntI T.left_treeE subsetCE)
  have "t \<in> set (u \<leadsto>\<^bsub>T\<^esub> u')" using T.left_tree_separates' st u by blast
  thus "v \<in> bag t" using bags_continuous u by (meson IntI T.left_treeE subsetCE)
qed

text \<open>Now we can show the main theorem: For every edge @{term "s \<rightarrow>\<^bsub>T\<^esub> t"} in @{term T}, the
  set @{term "bag s \<inter> bag t"} is a separator of @{term G}.  That is, every path from the left part
  to the right part goes through @{term "bag s \<inter> bag t"}.\<close>
theorem bags_separate:
  assumes st: "s \<rightarrow>\<^bsub>T\<^esub> t" and v: "v \<in> left_part s t" and w: "w \<in> left_part t s" and xs: "v \<leadsto>xs\<leadsto> w"
  shows "set xs \<inter> bag s \<inter> bag t \<noteq> {}"
proof (rule ccontr)
  assume "\<not>?thesis"
  {
    fix u assume "u \<in> set xs"
    with xs v \<open>\<not>?thesis\<close> have "vertex_subtree u \<subseteq> T.left_tree s t"
    proof (induct xs arbitrary: v)
      case (Cons x xs v)
      hence contra: "v \<notin> bag s \<or> v \<notin> bag t" by (metis path_from_toE IntI empty_iff hd_in_set)
      {
        assume "x = u" "\<not>vertex_subtree u \<subseteq> T.left_tree s t"
        then obtain z where z: "z \<in> vertex_subtree u" "z \<notin> T.left_tree s t" by blast
        hence "z \<in> vertex_subtree v" using Cons.prems(1,3) \<open>x = u\<close>
          by (metis list.sel(1) path_from_to_def)
        hence "v \<in> left_part t s" unfolding vertex_subtree_def
          using T.left_tree_union_V z st by auto
        hence False using vertex_in_separator contra st Cons.prems(2) by blast
      }
      moreover {
        assume "x \<noteq> u"
        hence "u \<in> set xs" using Cons.prems(4) by auto
        moreover hence "xs \<noteq> Nil" using empty_iff list.set(1) by auto
        moreover hence "last xs = w" using Cons.prems(1) by auto
        moreover have "path xs" using Cons.prems(1) walk_tl by force
        moreover have "hd xs \<in> left_part s t" proof-
          have "v\<rightarrow>hd xs" using Cons.prems(1,3) \<open>xs \<noteq> Nil\<close> walk_first_edge' by auto
          then obtain u' where u': "u' \<in> V\<^bsub>T\<^esub>" "v \<in> bag u'" "hd xs \<in> bag u'"
            using bags_edges by blast
          hence "u' \<in> T.left_tree s t"
            using contra vertex_in_separator st T.left_tree_union_V Cons.prems(2) by blast
          thus ?thesis using u'(3) unfolding left_part_def by blast
        qed
        moreover have "\<not>set xs \<inter> bag s \<inter> bag t \<noteq> {}" using Cons.prems(3)
          IntI disjoint_iff_not_equal inf_le1 inf_le2 set_subset_Cons subsetCE by auto
        ultimately have "vertex_subtree u \<subseteq> T.left_tree s t" using Cons.hyps by blast
      }
      ultimately show ?case by blast
    qed simp
  }
  hence "vertex_subtree w \<subseteq> T.left_tree s t" using xs last_in_set by blast
  moreover have "vertex_subtree w \<inter> T.left_tree t s \<noteq> {}" using w
    unfolding left_part_def T.left_tree_def by blast
  ultimately show False using T.left_tree_disjoint st by blast
qed

text \<open>It follows that vertices cannot be dropped from a bag if they have a neighbor that has
  not been visited yet (that is, a neighbor that is strictly in the right part of the separation).\<close>
corollary bag_no_drop:
  assumes st: "s \<rightarrow>\<^bsub>T\<^esub> t" and vw: "v\<rightarrow>w" and v: "v \<in> bag s" and w: "w \<notin> bag s" "w \<in> left_part t s"
  shows "v \<in> bag t"
proof-
  have "v \<leadsto>[v,w]\<leadsto> w" using v vw w(1) by auto
  hence "set [v,w] \<inter> bag s \<inter> bag t \<noteq> {}" using st v w(2)
    by (meson T.edges_are_in_V T.left_tree_initial bags_separate left_partI)
  thus ?thesis using w(1) by auto
qed

end \<comment> \<open>locale TreeDecomposition\<close>
end
