section \<open>The case $y \neq new\_last$\<close>

theory Y_neq_new_last imports MengerInduction begin

text \<open>
  Let us now consider the case that @{term "y \<noteq> v1 \<and> y \<noteq> new_last"}.  Our goal is to show that
  this is inconsistent: The following locale will be unsatisfiable, proving that
  @{term "y = v1 \<or> y = new_last"} holds.
\<close>
locale ProofStepInduct_y_neq_new_last = ProofStepInduct_NonTrivial_P_k_pre +
  assumes y_neq_v1: "y \<noteq> v1" and y_neq_new_last: "y \<noteq> new_last"
begin

lemma Q_hit_exists: obtains Q_hit Q_hit_pre Q_hit_post where
  "Q_hit \<in> Q" "y \<in> set Q_hit" "Q_hit = Q_hit_pre @ y # Q_hit_post"
proof-
  obtain Q_hit where "Q_hit \<in> Q" "y \<in> set Q_hit"
    using hitting_Q_or_new_last_def y y_neq_v1 y_neq_new_last by auto
  then show ?thesis using that by (meson split_list)
qed

text \<open>
  We open an anonymous context because we do not want to export any lemmas except the final lemma
  proving the contradiction.  This is also an easy way to get the decomposition of @{term Q_hit},
  whose existence we have established above.
\<close>

context
  fixes Q_hit Q_hit_pre Q_hit_post
  assumes Q_hit: "Q_hit \<in> Q" "y \<in> set Q_hit"
    and Q_hit_decomp: "Q_hit = Q_hit_pre @ y # Q_hit_post"
begin
  private lemma Q_hit_v0_v1: "v0 \<leadsto>Q_hit\<leadsto>\<^bsub>H_x\<^esub> v1" using Q.paths Q_hit(1) by blast

  private lemma Q_hit_vertices: "set Q_hit \<subseteq> V - {new_last}"
    using Q.walk_in_V H_x_def path_from_to_def remove_vertex_V Q_hit_v0_v1 by fastforce

  private lemma Q_hit_pre_not_Nil: "Q_hit_pre \<noteq> Nil"
    using Q_hit_v0_v1 y_neq_v0 unfolding Q_hit_decomp by auto

  private lemma tl_Q_hit_pre: "tl (Q_hit_pre @ [y]) \<noteq> Nil" using Q_hit_pre_not_Nil by simp

  private lemma Q_hit_pre_edges: "edges_of_walk (Q_hit_pre @ [y]) \<inter> B \<noteq> {}" proof
    assume "edges_of_walk (Q_hit_pre @ [y]) \<inter> B = {}"
    moreover have "edges_of_walk (Q_hit_pre @ [y]) \<subseteq> E"
      by (metis Q.paths H_x_def Q_hit(1) Q_hit_decomp edges_of_walk_in_E path_decomp'
          path_from_to_def remove_vertex_walk_add)
    ultimately have Q_hit_pre_edges:
      "edges_of_walk (Q_hit_pre @ [y]) \<subseteq> \<Union>(edges_of_walk ` paths_with_new)"
      unfolding B_def by blast
    then have *: "first_edge_of_walk (Q_hit_pre @ [y]) \<in> \<Union>(edges_of_walk ` paths_with_new)"
      using tl_Q_hit_pre first_edge_in_edges by blast

    define v' where "v' \<equiv> hd (tl (Q_hit_pre @ [y]))"
    then have v': "(v0, v') = first_edge_of_walk (Q_hit_pre @ [y])"
      using first_edge_hd_tl Q_hit_pre_not_Nil tl_Q_hit_pre
      by (metis Q.path_from_toE Q_hit_decomp Q_hit_v0_v1 first_edge_of_walk.simps(1)
          hd_Cons_tl hd_append snoc_eq_iff_butlast)

    then obtain P_i where
      P_i: "P_i \<in> paths_with_new" "(v0, v') \<in> edges_of_walk P_i" using * by auto
    then have P_i_first: "first_edge_of_walk P_i = (v0, v')"
      using first_edge_first paths_with_new_def paths P_new by (metis insert_iff)
    moreover have "first_edge_of_walk P_k = (v0, hd (tl P_k))"
      by (metis P_k_decomp P_k_pre_not_Nil append_is_Nil_conv first_edge_of_walk.simps(1)
          hd_P_k_v0 list.distinct(1) list.exhaust_sel tl_append2)
    ultimately have "P_i \<noteq> P_k"
      by (metis Q.first_edge_first P_k(2) Q.second_vertices_first_edge Q_hit(1) Q_hit_decomp
          Q_hit_v0_v1 Un_iff v' tl_Q_hit_pre first_edge_in_edges walk_edges_decomp)

    text \<open>
      Then @{term P_k} and @{term P_i} intersect in @{term y}, which is not one of @{term v0},
      @{term v1}, or @{term new_last}.  So we get a contradiction because these two paths should be
      disjoint on all other vertices.
\<close>

    moreover have "v1 \<notin> set (Q_hit_pre @ [y])"
      using Q_hit_v0_v1 Q_hit_decomp y_neq_v1 by (simp add: Q.path_from_to_last')
    moreover have "new_last \<notin> set (Q_hit_pre @ [y])" proof-
      have "new_last \<notin> set Q_hit_pre" using Q_hit_decomp Q_hit_vertices by auto
      then show ?thesis using y_neq_new_last by auto
    qed
    moreover have "hd (tl (Q_hit_pre @ [y])) = hd (tl P_i)" proof-
      have "hd (tl P_i) = v'" using P_i_first P_i(1) tl_P_new(1)
        by (metis Pair_inject first_edge_of_walk.simps(1) insert_iff list.collapse
            paths_tl_notnil paths_with_new_def tl_Nil)
      then show ?thesis using v'_def by simp
    qed
    moreover have "v0 \<leadsto>(Q_hit_pre @ [y])\<leadsto> y"
      by (metis Q.path_decomp' H_x_def Q_hit_decomp Q_hit_v0_v1 Q_hit_pre_not_Nil
          hd_append2 path_from_to_def remove_vertex_walk_add snoc_eq_iff_butlast)
    ultimately have "edges_of_walk (Q_hit_pre @ [y]) \<subseteq> edges_of_walk P_i"
      using new_path_follows_old_paths tl_Q_hit_pre P_i(1) Q_hit_pre_edges by blast
    from walk_edges_subset[OF this] have "y \<in> set P_i" by (simp add: tl_Q_hit_pre)
    moreover have "y \<in> set P_k" using P_k_decomp by auto
    ultimately show False
      using y_neq_v0 y_neq_v1 y_neq_new_last \<open>P_i \<noteq> P_k\<close>
        paths_plus_one_disjoint[OF P_i(1), of P_k y] P_k(1) P_new_decomp by auto
  qed

  private lemma P_k_pre_edges: "edges_of_walk (P_k_pre @ [y]) \<inter> B = {}" proof-
    have "edges_of_walk (P_k_pre @ [y]) \<subseteq> \<Union>(edges_of_walk ` paths_with_new)"
    proof (cases)
      assume "P_k = P_new"
      then have "edges_of_walk (P_k_pre @ [y]) \<subseteq> edges_of_walk P_new"
        using P_k_decomp edges_of_comp1 by force
      then show ?thesis unfolding paths_with_new_def by blast
    next
      assume "P_k \<noteq> P_new"
      then have "P_k \<in> paths" using P_k(1) paths_with_new_def by blast
      then have "edges_of_walk (P_k_pre @ [y]) \<subseteq> \<Union>(edges_of_walk ` paths)"
        using edges_of_comp1[of "P_k_pre @ [y]"] P_k_decomp by auto
      then show ?thesis unfolding paths_with_new_def by blast
    qed
    then show ?thesis unfolding B_def by blast
  qed

  private definition Q_hit' where "Q_hit' \<equiv> P_k_pre @ y # Q_hit_post"

  private lemma Q_hit'_v0_v1: "v0 \<leadsto>Q_hit'\<leadsto> v1" proof-
    {
      fix v assume "v \<in> set P_k_pre"
      then have "\<not>Q.hitting_paths v" using Q.paths Q_hit(1) y_min
        by (metis Q.hitting_paths_def hitting_Q_or_new_last_def last_in_set path_from_to_def)
      moreover have "v0 \<notin> set Q_hit_post" using Q.path_from_to_first' Q_hit_v0_v1
        unfolding Q_hit_decomp by blast
      ultimately have "v \<notin> set Q_hit_post" unfolding Q.hitting_paths_def
        using Q_hit(1) Q_hit_decomp by auto
    }
    then have "set P_k_pre \<inter> set Q_hit_post = {}" by blast
    then show ?thesis unfolding Q_hit'_def using path_from_to_combine
      by (metis H_x_def P_k_decomp P_k_pre_not_Nil Q_hit_decomp Q_hit_v0_v1 append_is_Nil_conv
          hd_P_k_v0 path_P_k path_from_toI remove_vertex_path_from_to_add)
  qed

  private lemma Q_hit'_v0_v1_H_x: "v0 \<leadsto>Q_hit'\<leadsto>\<^bsub>H_x\<^esub> v1" proof-
    have "new_last \<notin> set P_k_pre" using new_last_neq_v0 hitting_Q_or_new_last_def y_min by auto
    moreover have "new_last \<notin> set Q_hit_post" using Q_hit_vertices unfolding Q_hit_decomp by auto
    ultimately have "new_last \<notin> set Q_hit'" using y_neq_new_last Q_hit'_def by auto
    then show ?thesis using remove_vertex_path_from_to[OF Q_hit'_v0_v1] H_x_def new_last_in_V by simp
  qed

  private definition Q' where "Q' \<equiv> insert Q_hit' (Q - {Q_hit})"

  private lemma Q_hit_edges_disjoint:
    "\<Union>(edges_of_walk ` (Q - {Q_hit})) \<inter> edges_of_walk Q_hit = {}"
    using DiffD1 Q.paths_edge_disjoint Q_hit(1) by fastforce

  private lemma Q_hit'_notin_Q_minus_Q_hit: "Q_hit' \<notin> Q - {Q_hit}" proof-
    have "hd (tl Q_hit') \<notin> Q.second_vertices" using P_k(2) P_k_decomp
      by (metis P_k_pre_not_Nil Q_hit'_def append_eq_append_conv2 append_self_conv hd_append2
          list.sel(1) tl_append2)
    then show ?thesis using Q.second_vertices_new_path[of Q_hit'] by blast
  qed

  private lemma Q_weight_smaller: "Q_weight Q' < Q_weight Q" proof-
    define Q_edges where "Q_edges \<equiv> \<Union>(edges_of_walk ` Q) \<inter> B"
    define Q'_edges where "Q'_edges \<equiv> \<Union>(edges_of_walk ` Q') \<inter> B"
    {
      fix v w assume *: "(v,w) \<in> Q'_edges" "(v,w) \<notin> Q_edges"
      then have v_w_in_B: "(v,w) \<in> B" unfolding Q'_edges_def by blast

      obtain Q'_v_w_witness where Q'_v_w_witness:
        "Q'_v_w_witness \<in> Q'" "(v,w) \<in> edges_of_walk Q'_v_w_witness"
        using *(1) unfolding Q'_edges_def by blast

      have "Q'_v_w_witness \<noteq> Q_hit'" proof
        assume "Q'_v_w_witness = Q_hit'"
        then have "edges_of_walk Q'_v_w_witness =
            edges_of_walk (P_k_pre @ [y]) \<union> edges_of_walk (y # Q_hit_post)"
          unfolding Q_hit'_def using walk_edges_decomp[of P_k_pre y Q_hit_post] by simp
        moreover have "(v,w) \<notin> edges_of_walk (P_k_pre @ [y])"
          using P_k_pre_edges v_w_in_B by blast
        moreover have "(v,w) \<notin> edges_of_walk (y # Q_hit_post)" proof
          assume "(v,w) \<in> edges_of_walk (y # Q_hit_post)"
          then have "(v,w) \<in> edges_of_walk Q_hit"
            unfolding Q_hit_decomp by (metis UnCI walk_edges_decomp)
          then show False using *(2) v_w_in_B Q_hit(1) unfolding Q_edges_def by blast
        qed
        ultimately show False using Q'_v_w_witness(2) by blast
      qed
      then have "Q'_v_w_witness \<in> Q" using Q'_v_w_witness(1) unfolding Q'_def by blast
      then have False using *(2) v_w_in_B Q'_v_w_witness(2) unfolding Q_edges_def by blast
    }
    moreover have "\<exists>e \<in> Q_edges. e \<notin> Q'_edges" proof-
      obtain v w where v_w: "(v,w) \<in> edges_of_walk (Q_hit_pre @ [y]) \<inter> B"
        using Q_hit_pre_edges by auto
      then have v_w_in_Q_hit: "(v,w) \<in> edges_of_walk Q_hit \<inter> B" unfolding Q_hit_decomp
        by (metis Int_iff UnCI walk_edges_decomp)
      then have "(v,w) \<in> Q_edges" unfolding Q_edges_def using Q_hit(1) by blast
      moreover have "(v,w) \<notin> Q'_edges" proof
        assume "(v,w) \<in> Q'_edges"
        then have "(v,w) \<in> edges_of_walk Q_hit'" unfolding Q'_edges_def Q'_def
          using IntD1 v_w_in_Q_hit Q_hit_edges_disjoint by auto
        then have "(v,w) \<in> edges_of_walk (y # Q_hit_post)" unfolding Q_hit'_def
          using v_w P_k_pre_edges
          by (metis (no_types, lifting) IntD2 UnE disjoint_iff_not_equal walk_edges_decomp)
        then show False using v_w Q_hit(1) Q.paths Q_hit_decomp
          by (metis DiffE Q.path_edges_remove_prefix IntD1 path_from_to_def)
      qed
      ultimately show ?thesis by blast
    qed
    moreover have "finite Q_edges" unfolding Q_edges_def B_def by simp
    moreover have "finite Q'_edges" unfolding Q'_edges_def B_def by simp
    ultimately have "card Q'_edges < card Q_edges" by (metis card_seteq not_le subrelI)
    then have "card (\<Union>(edges_of_walk ` Q') \<inter> B) < card (\<Union>(edges_of_walk ` Q) \<inter> B)"
      unfolding Q_edges_def Q'_edges_def by blast
    then show ?thesis unfolding Q_weight_def by blast
  qed

  private lemma DisjointPaths_Q': "DisjointPaths H_x v0 v1 Q'" proof-
    interpret Q_reduced: DisjointPaths H_x v0 v1 "Q - {Q_hit}"
      using Q.DisjointPaths_reduce[of "Q - {Q_hit}"] by blast
    {
      fix xs v
      assume xs: "xs \<in> Q - {Q_hit}"
          and v: "v \<in> set xs" "v \<in> set Q_hit'" "v \<noteq> v0" "v \<noteq> v1"
      have "v \<notin> set P_k_pre" proof
        assume "v \<in> set P_k_pre"
        then have "\<not>hitting_Q_or_new_last v" using y_min by blast
        moreover have "v \<noteq> new_last" using v(2) calculation hitting_Q_or_new_last_def v(3) by auto
        ultimately show False unfolding hitting_Q_or_new_last_def using v(1,3) xs by blast
      qed
      moreover have "v \<noteq> y"
        by (metis DiffE Q.paths_disjoint Q_hit y_neq_v0 y_neq_v1 insert_iff v(1) xs)
      moreover have "v \<notin> set Q_hit_post" proof
        assume "v \<in> set Q_hit_post"
        then have "v \<in> set Q_hit" unfolding Q_hit_decomp by simp
        then show False using Q.paths_disjoint[of Q_hit xs] xs Q_hit(1) v by blast
      qed
      ultimately have False using v(2) unfolding Q_hit'_def by simp
    }
    then show ?thesis using Q_reduced.DisjointPaths_extend Q_hit'_v0_v1_H_x
      unfolding Q'_def by blast
  qed

  private lemma card_Q': "card Q' = sep_size" proof-
    have "Suc (card (Q - {Q_hit})) = card Q"
      using Q_hit(1) Q.finite_paths by (meson card_Suc_Diff1)
    then show ?thesis using Q(2) Q.finite_paths Q_hit'_notin_Q_minus_Q_hit
      unfolding Q'_def by simp
  qed

  lemma contradiction': "False" using Q_weight_smaller DisjointPaths_Q' card_Q' Q_min
    using Suc_leI not_less_eq_eq by blast
end \<comment> \<open>anonymous context\<close>

corollary contradiction: "False" using Q_hit_exists contradiction' by blast

end \<comment> \<open>locale @{locale ProofStepInduct_y_neq_new_last}\<close>
end
