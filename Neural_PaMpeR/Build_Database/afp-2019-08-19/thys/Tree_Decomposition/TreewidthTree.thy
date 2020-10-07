section \<open>Treewidth of Trees\<close>

theory TreewidthTree
imports TreeDecomposition begin

text \<open>The treewidth of a tree is 1 if the tree has at least one edge, otherwise it is 0.

  For simplicity and without loss of generality, we assume that the vertex set of the tree is a
  subset of the natural numbers because this is what we use in the definition of
  @{const Graph.treewidth}.

  While it would be nice to lift this restriction, removing it would entail defining isomorphisms
  between graphs in order to map the tree decomposition to a tree decomposition over the natural
  numbers.  This is outside the scope of this theory and probably not terribly interesting by
  itself.\<close>
theorem treewidth_tree:
  fixes G :: "nat Graph" (structure)
  assumes "Tree G"
  shows "Graph.treewidth G \<le> 1"
proof-
  interpret Tree G using assms .
  {
    assume "V \<noteq> {}"
    then obtain root where root: "root \<in> V" by blast
    then interpret RootedTree G root by unfold_locales
    define bag where "bag v = (if v = root then {v} else {v, parent v})" for v
    have v_in_bag: "\<And>v. v \<in> bag v" unfolding bag_def by simp
    have bag_in_V: "\<And>v. v \<in> V \<Longrightarrow> bag v \<subseteq> V" unfolding bag_def
      using parent_in_V empty_subsetI insert_subset by auto
    have "TreeDecomposition G G bag" proof
      show "\<Union>{bag t | t. t \<in> V} = V" using bag_in_V v_in_bag by blast
    next
      fix v w assume "v\<rightarrow>w"
      moreover have "\<And>v' w'. \<lbrakk> v'\<rightarrow>w'; v' \<noteq> root \<rbrakk> \<Longrightarrow> w' \<in> bag v' \<or> v' \<in> bag w'" unfolding bag_def
        by (metis insertI2 parent_edge_cases parent_edge_root singletonI)
      ultimately have "v \<in> bag w \<or> w \<in> bag v" using no_loops undirected by blast
      thus "\<exists>t\<in>V. v \<in> bag t \<and> w \<in> bag t" using \<open>v\<rightarrow>w\<close> edges_are_in_V v_in_bag by blast
    next
      fix s u t assume s: "s \<in> V" and u: "u \<in> V" and t: "t \<in> set (s\<leadsto>u)"
      have "t \<in> V" using t by (meson s subsetCE u unique_connecting_path_properties(1) walk_in_V)
      hence "s = u \<Longrightarrow> t = s" using left_tree_initial' s t by blast
      moreover have "s\<rightarrow>u \<Longrightarrow> t = s \<or> t = u" using s t u \<open>t \<in> V\<close>
        by (metis insertE left_treeI left_tree_initial' list.exhaust_sel list.simps(15)
            undirected unique_connecting_path_properties(2,3) unique_connecting_path_set(2)
            unique_connecting_path_tl)
      moreover {
        assume *: "s \<noteq> u" "\<not>s\<rightarrow>u"
        have "s = root \<Longrightarrow> bag s \<inter> bag u = {}" unfolding bag_def
          using *(1,2) parent_edge u undirected by fastforce
        moreover have "u = root \<Longrightarrow> bag s \<inter> bag u = {}" unfolding bag_def
          using *(1,2) parent_edge s by fastforce
        moreover have "\<lbrakk> s \<noteq> root; u \<noteq> root; parent s \<noteq> parent u \<rbrakk> \<Longrightarrow> bag s \<inter> bag u = {}"
          unfolding bag_def using *(2) parent_edge s u undirected by fastforce
        moreover {
          assume **: "s \<noteq> root" "u \<noteq> root" "parent s = parent u" "t \<noteq> s" "t \<noteq> u"
          have "bag s \<inter> bag u = { parent s }" unfolding bag_def using *(1) **(1-3)
            Int_insert_left inf.orderE insertE insert_absorb subset_insertI by auto
          moreover have "t = parent s"
            using sibling_path[OF s **(1) u **(2) *(1) **(3)] t **(4,5) by auto
          ultimately have "bag s \<inter> bag u \<subseteq> bag t" by (simp add: v_in_bag)
        }
        ultimately have "bag s \<inter> bag u \<subseteq> bag t" by blast
      }
      ultimately show "bag s \<inter> bag u \<subseteq> bag t" by blast
    qed
    then interpret TreeDecomposition G G bag .
    {
      fix v
      have "card { v, parent v } \<le> 2"
        by (metis card.insert card_empty finite.emptyI finite_insert insert_absorb insert_not_empty
            lessI less_or_eq_imp_le numerals(2))
      hence "card (bag v) \<le> 2" unfolding bag_def by simp
    }
    hence "max_bag_card \<le> 2" using \<open>V \<noteq> {}\<close> max_bag_card_in_bag_cards by auto
    hence "width \<le> 1" unfolding width_def by (simp add: \<open>V \<noteq> {}\<close>)
    hence "\<exists>bag. TreeDecomposition G G bag \<and> TreeDecomposition.width G bag \<le> 1"
      using TreeDecomposition_axioms by blast
  }
  thus ?thesis by (metis TreeDecomposition.width_V_empty le_0_eq linear
    treewidth_cards_treewidth treewidth_upper_bound_ex)
qed

text \<open>If the tree is non-trivial, that is, if it contains more than one vertex, then its
  treewidth is exactly 1.\<close>
corollary treewidth_tree_exact:
  fixes G :: "nat Graph" (structure)
  assumes "Tree G" "card V\<^bsub>G\<^esub> > 1"
  shows "Graph.treewidth G = 1"
  using assms Graph.treewidth_lower_bound_1 Tree.tree_has_edge Tree_def treewidth_tree
  by fastforce

end
