section \<open>Treewidth of Complete Graphs\<close>

theory TreewidthCompleteGraph
imports TreeDecomposition begin

text \<open>As an application of the separator theorem \<open>bags_separate\<close>, or more precisely its
  corollary \<open>bag_no_drop\<close>, we show that a complete graph of size @{term "n :: nat"}
  (a clique) has treewidth @{term "(n::nat)-1"}.\<close>
theorem (in Graph) treewidth_complete_graph:
  assumes "\<And>v w. \<lbrakk> v \<in> V; w \<in> V; v \<noteq> w \<rbrakk> \<Longrightarrow> v\<rightarrow>w"
  shows "treewidth = card V - 1"
proof-
  {
    assume "V \<noteq> {}"
    obtain T bag where
      T: "TreeDecomposition G (T :: nat Graph) bag" "treewidth = TreeDecomposition.width T bag"
      using treewidth_cards_treewidth by blast
    interpret TreeDecomposition G T bag using T(1) .

    assume "\<not>?thesis"
    hence "width \<noteq> card V - 1" by (simp add: T(2))
    text \<open>Let @{term s} be a bag of maximal size.\<close>
    moreover obtain s where s: "s \<in> V\<^bsub>T\<^esub>" "card (bag s) = max_bag_card"
      using max_bag_card_in_bag_cards \<open>V \<noteq> {}\<close> by fastforce
    text \<open>The treewidth cannot be larger than @{term "card V - 1"}, so due to our assumption
      @{term "width \<noteq> card V - 1" } it must be smaller, hence @{term "card (bag s) < card V"}.\<close>
    ultimately have "card (bag s) < card V" unfolding width_def
      using \<open>V \<noteq> {}\<close> empty_tree_empty_V le_eq_less_or_eq max_bag_card_upper_bound_V by presburger
    then obtain v where v: "v \<in> V" "v \<notin> bag s" by (meson bag_finite card_mono not_less s(1) subsetI)

    text \<open>There exists a bag containing @{term v}.  We consider the path from @{term s} to
      @{term t} and find that somewhere along this path there exists a bag containing
      @{term "insert v (bag s)"}, which is a contradiction because such a bag would be too big.\<close>
    obtain t where t: "t \<in> V\<^bsub>T\<^esub>" "v \<in> bag t" using bags_exist v(1) by blast
    with s have "\<exists>t \<in> V\<^bsub>T\<^esub>. insert v (bag s) \<subseteq> bag t" proof (induct "s \<leadsto>\<^bsub>T\<^esub> t" arbitrary: s)
      case Nil thus ?case using T.unique_connecting_path_properties(2) by fastforce
    next
      case (Cons x xs s)
      show ?case proof (cases)
        assume "v \<in> bag s" thus ?thesis using t Cons.prems(1) by blast
      next
        assume "v \<notin> bag s"
        hence "s \<noteq> t" using t(2) by blast
        hence "xs \<noteq> Nil" using Cons.hyps(2) Cons.prems(1,3)
          by (metis T.unique_connecting_path_properties(3,4) last_ConsL list.sel(1))
        moreover have "x = s" using Cons.hyps(2) Cons.prems(1) t(1)
          by (metis T.unique_connecting_path_properties(3) list.sel(1))
        ultimately obtain s' xs' where s': "s # s' # xs' = s \<leadsto>\<^bsub>T\<^esub> t"
          using Cons.hyps(2) list.exhaust by metis
        moreover have st_path: "T.path (s \<leadsto>\<^bsub>T\<^esub> t)"
          by (simp add: Cons.prems(1) T.unique_connecting_path_properties(1) t(1))
        ultimately have "s' \<in> V\<^bsub>T\<^esub>" by (metis T.edges_are_in_V(2) T.path_first_edge)
        text \<open>Bags can never drop vertices because every vertex has a neighbor in @{term G} which
          has not yet been visited.\<close>
        have s_in_s': "bag s \<subseteq> bag s'" proof
          fix w assume "w \<in> bag s"
          moreover have "s \<rightarrow>\<^bsub>T\<^esub> s'" using s' st_path by (metis T.walk_first_edge)
          moreover have "v \<in> left_part s' s" using Cons.prems(1,4) s' t(1)
            by (metis T.left_treeI T.unique_connecting_path_rev insert_subset left_partI
                list.simps(15) set_rev subsetI)
          ultimately show "w \<in> bag s'"
            using bag_no_drop Cons.prems(1,4) \<open>v \<notin> bag s\<close> assms bags_in_V v(1) by blast
        qed
        text \<open>Bags can never gain vertices because we started with a bag of maximal size.\<close>
        moreover have "card (bag s') \<le> card (bag s)" proof-
          have "card (bag s') \<le> max_bag_card" unfolding max_bag_card_def
            using Max_ge \<open>s' \<in> V\<^bsub>T\<^esub>\<close> bag_cards_finite by blast
          thus ?thesis using Cons.prems(2) by auto
        qed
        ultimately have "bag s' = bag s" using \<open>s' \<in> V\<^bsub>T\<^esub>\<close> bag_finite card_seteq by blast
        thus ?thesis
          using Cons.hyps Cons.prems(1,2) \<open>s' \<in> V\<^bsub>T\<^esub>\<close> t s' st_path \<open>xs \<noteq> []\<close>
          by (metis T.path_from_toI T.path_tl T.unique_connecting_path_properties(4)
              T.unique_connecting_path_unique last.simps list.sel(1,3))
      qed
    qed
    hence "\<exists>t \<in> V\<^bsub>T\<^esub>. card (bag s) < card (bag t)" using v(2)
      by (metis bag_finite card_seteq insert_subset not_le)
    hence False using s Max.coboundedI bag_cards_finite not_le unfolding max_bag_card_def by auto
  }
  thus ?thesis using treewidth_upper_bound_V card_empty diff_diff_cancel zero_diff by fastforce
qed

end
