section \<open>The case $y = new\_last$\<close>

theory Y_eq_new_last imports MengerInduction begin

text \<open>
  We may assume @{term "y \<noteq> v1"} now because @{thm ProofStepInduct_NonTrivial_P_k_pre.y_eq_v1_solves}
  shows that @{term "y = v1"} already gives us @{term "Suc sep_size"} many disjoint paths.

  We also assume that we have chosen the previous paths optimally in the sense that the distance
  from @{term new_last} to @{term v1} is minimal.
\<close>

locale ProofStepInduct_y_eq_new_last = ProofStepInduct_NonTrivial_P_k_pre +
  assumes y_neq_v1: "y \<noteq> v1" and y_eq_new_last: "y = new_last"
      and optimal_paths: "\<And>paths' P_new'.
            ProofStepInduct G v0 v1 paths' P_new' sep_size
            \<Longrightarrow> H.distance (last P_new) v1 \<le> H.distance (last P_new') v1"
begin

text \<open>Let @{term R} be a shortest path from @{term new_last} to @{term v1}.\<close>
definition R where "R \<equiv>
  SOME R. new_last \<leadsto>R\<leadsto>\<^bsub>H\<^esub> v1 \<and> (\<forall>R'. new_last \<leadsto>R'\<leadsto>\<^bsub>H\<^esub> v1 \<longrightarrow> length R \<le> length R')"

lemma R: "new_last \<leadsto>R\<leadsto>\<^bsub>H\<^esub> v1" "\<And>R'. new_last \<leadsto>R'\<leadsto>\<^bsub>H\<^esub> v1 \<Longrightarrow> length R \<le> length R'" proof-
  obtain R' where
    R': "new_last \<leadsto>R'\<leadsto>\<^bsub>H\<^esub> v1" "\<And>R''. new_last \<leadsto>R''\<leadsto>\<^bsub>H\<^esub> v1 \<Longrightarrow> length R' \<le> length R''"
    using arg_min_ex[OF new_last_to_v1] unfolding H_def by blast
  then show "new_last \<leadsto>R\<leadsto>\<^bsub>H\<^esub> v1" "\<And>R'. new_last \<leadsto>R'\<leadsto>\<^bsub>H\<^esub> v1 \<Longrightarrow> length R \<le> length R'"
    using someI[of "\<lambda>R. new_last \<leadsto>R\<leadsto>\<^bsub>H\<^esub> v1 \<and> (\<forall>R'. new_last \<leadsto>R'\<leadsto>\<^bsub>H\<^esub> v1 \<longrightarrow> length R \<le> length R')"]
      R_def by auto
qed

lemma v1_in_Q: "\<exists>Q_hit \<in> Q. v1 \<in> set Q_hit" proof-
  obtain xs where "xs \<in> Q" using Q(2) sep_size_not0 by fastforce
  then show ?thesis using Q.paths last_in_set by blast
qed

lemma R_hits_Q: "\<exists>z \<in> set R. Q.hitting_paths z" proof-
  have "v1 \<in> set R" using R(1) last_in_set by (metis path_from_to_def)
  then show ?thesis unfolding Q.hitting_paths_def using v0_neq_v1 by auto
qed

lemma R_decomp_exists:
  obtains R_pre z R_post
    where "R = R_pre @ z # R_post"
      and "Q.hitting_paths z"
      and "\<And>z'. z' \<in> set R_pre \<Longrightarrow> \<not>Q.hitting_paths z'"
  using R_hits_Q split_list_first_prop[of R Q.hitting_paths] by blast

text \<open>
  We open an anonymous context in order to hide all but the final lemma.  This also gives us the
  decomposition of @{term R} whose existence we established above.
\<close>

context fixes R_pre z R_post
  assumes R_decomp: "R = R_pre @ z # R_post"
      and z: "Q.hitting_paths z"
      and z_min: "\<And>z'. z' \<in> set R_pre \<Longrightarrow> \<not>Q.hitting_paths z'"
begin
  private lemma z_neq_v0: "z \<noteq> v0" using z Q.hitting_paths_def by auto

  private lemma z_neq_new_last: "z \<noteq> new_last" proof
    assume "z = new_last"
    then obtain Q_hit where Q_hit: "Q_hit \<in> Q" "new_last \<in> set Q_hit"
      using z Q.hitting_paths_def y_eq_new_last y_neq_v1 by auto
    then have "Q.path Q_hit" by (meson Q.paths path_from_to_def)
    then have "set Q_hit \<subseteq> V - {new_last}" using Q.walk_in_V H_x_def remove_vertex_V by simp
    then show False using Q_hit(2) by blast
  qed

  private lemma R_pre_neq_Nil: "R_pre \<noteq> Nil" using z_neq_new_last R_decomp R(1) by auto

  private lemma z_closer_than_new_last: "H.distance z v1 < H.distance new_last v1" proof-
    have "H.distance new_last v1 = length R" using H.distance_witness R by auto
    moreover have "z \<leadsto>(z # R_post)\<leadsto>\<^bsub>H\<^esub> v1" using R_decomp R(1)
      by (metis H.walk_decomp(2) distinct_append last_appendR list.sel(1)
          list.simps(3) path_from_to_def)
    moreover have "length R > length (z # R_post)"
      unfolding R_decomp using R_pre_neq_Nil by simp
    ultimately show ?thesis using H.distance_upper_bound by fastforce
  qed

  private definition R'_walk where "R'_walk \<equiv> P_k_pre @ R_pre @ [z]"

  private lemma R'_walk_not_Nil: "R'_walk \<noteq> Nil" using R'_walk_def R(1) by simp

  private lemma R'_walk_no_Q: "\<lbrakk> v \<in> set R'_walk; v \<noteq> z \<rbrakk> \<Longrightarrow> \<not>Q.hitting_paths v" proof-
    fix v assume "v \<in> set R'_walk" "v \<noteq> z"
    moreover have "v \<in> set P_k_pre \<Longrightarrow> \<not>Q.hitting_paths v"
      using Q.hitting_paths_def hitting_Q_or_new_last_def y_min v1_in_Q by auto
    moreover have "v \<in> set R_pre \<Longrightarrow> \<not>Q.hitting_paths v" using z_min by simp
    ultimately show "\<not>Q.hitting_paths v" unfolding R'_walk_def using R'_walk_def by auto
  qed

  text \<open>
    The original proof goes like this:
    ``Let @{term z} be the first vertex of @{term R} on some path in @{term Q}.
    Then the distance in @{term "H"} from @{term z} to @{term v1} is less than the distance
    from @{term new_last} to @{term v1}.  This contradicts the choice of @{term paths} and
    @{term P_new}.''

    It does not say exactly why it contradicts the choice of @{term paths} and @{term P_new}.
    It seems we can choose @{term Q} together with @{term R'_walk} as our new paths plus
    extrapath. But this seems to be wrong because we cannot show that @{term R'_walk} is a path:
    @{term P_k_pre} and @{term R_pre} could intersect.

    So we use @{thm walk_to_path} to transform @{term R'_walk} into a path @{term R'}.
\<close>
  private definition R' where
    "R' \<equiv> SOME R'. hd (tl R'_walk) \<leadsto>R'\<leadsto> z \<and> set R' \<subseteq> set (tl R'_walk)"

  private lemma R': "hd (tl R'_walk) \<leadsto>R'\<leadsto> z" "set R' \<subseteq> set (tl R'_walk)" proof-
    have "tl R'_walk \<noteq> Nil" by (simp add: P_k_pre_not_Nil R'_walk_def)
    moreover have "last R'_walk = z" unfolding R'_walk_def by simp
    moreover have "walk (tl R'_walk)"
      by (metis (no_types, lifting) path_from_toE walk_tl H_def P_k_decomp R'_walk_def R(1)
          R_decomp path_P_k y_eq_new_last hd_append list.sel(1) list.simps(3) path_decomp'
          remove_vertex_path_from_to_add walk_comp walk_decomp(1) walk_last_edge)
    ultimately obtain R'' where "hd (tl R'_walk) \<leadsto>R''\<leadsto> z" "set R'' \<subseteq> set (tl R'_walk)"
      using walk_to_path[of "tl R'_walk" "hd (tl R'_walk)" z] last_tl by force
    then show "hd (tl R'_walk) \<leadsto>R'\<leadsto> z" "set R' \<subseteq> set (tl R'_walk)" unfolding R'_def
      using someI[of "\<lambda>R'. hd (tl R'_walk) \<leadsto>R'\<leadsto> z \<and> set R' \<subseteq> set (tl R'_walk)"] by auto
  qed

  private lemma hd_R': "hd R' = hd (tl P_k)" proof-
    have "hd (tl R'_walk) = hd (tl P_k)" proof (cases)
      assume "tl P_k_pre = Nil"
      then show ?thesis unfolding R'_walk_def using P_k_decomp R(1) P_k_pre_not_Nil y_eq_new_last
        by (metis H.path_from_toE R_decomp hd_append list.sel(1) tl_append2)
    next
      assume "tl P_k_pre \<noteq> Nil"
      then show ?thesis unfolding R'_walk_def using P_k_pre_not_Nil by (simp add: P_k_decomp)
    qed
    then show ?thesis using R'(1) by auto
  qed

  private lemma R'_no_Q: "\<lbrakk> v \<in> set R'; v \<noteq> z \<rbrakk> \<Longrightarrow> \<not>Q.hitting_paths v"
    using R'_walk_no_Q by (meson R'(2) R'_walk_not_Nil list.set_sel(2) subsetCE)

  private lemma v0_R'_path: "v0 \<leadsto>(v0 # R')\<leadsto> z" proof-
    have "v0\<rightarrow>hd R'" using hd_R' hd_P_k_v0
      by (metis Nil_is_append_conv P_k_decomp P_k_pre_not_Nil path_P_k list.distinct(1)
          list.exhaust_sel path_first_edge' tl_append2)
    moreover have "v0 \<notin> set R'" proof-
      have "v0 \<notin> set R" using R(1) H_def H.path_in_V remove_vertex_V
        by (simp add: path_from_to_def subset_Diff_insert)
      then have "v0 \<notin> set R_pre" using R_decomp by simp
      moreover have "v0 \<notin> set (tl P_k_pre)" using hd_P_k_v0 path_P_k path_first_vertex
        by (metis P_k_decomp P_k_pre_not_Nil hd_append list.exhaust_sel path_decomp(1))
      ultimately show ?thesis using R'(2) unfolding R'_walk_def
        using P_k_pre_not_Nil z_neq_v0 by auto
    qed
    ultimately show ?thesis using path_cons
      by (metis R'(1) last.simps list.sel(1) list.simps(3) path_from_to_def)
  qed

  private corollary z_last_R': "z = last (v0 # R')" using v0_R'_path by auto

  private lemma z_eq_v1_solves:
    assumes "z = v1"
    shows "\<exists>paths. DisjointPaths G v0 v1 paths \<and> card paths = Suc sep_size"
  proof-
    interpret Q': DisjointPaths G v0 v1 Q
      using DisjointPaths_supergraph H_x_def Q.DisjointPaths_axioms by auto
    have "v0 \<leadsto>(v0 # R')\<leadsto> v1" using assms v0_R'_path by auto
    moreover {
      fix xs v assume "xs \<in> Q" "xs \<noteq> v0 # R'" "v \<in> set xs" "v \<in> set (v0 # R')"
      then have "v = v0 \<or> v = v1" using R'_no_Q Q.hitting_paths_def \<open>z = v1\<close> by auto
    }
    ultimately have "DisjointPaths G v0 v1 (insert (v0 # R') Q)"
      using Q'.DisjointPaths_extend by blast
    moreover have "card (insert (v0 # R') Q) = Suc sep_size"
      by (simp add: P_k(2) Q(2) Q.finite_paths Q.second_vertices_new_path hd_R')
    ultimately show ?thesis by blast
  qed

  private lemma z_neq_v1_solves:
    assumes "z \<noteq> v1"
    shows "\<exists>paths. DisjointPaths G v0 v1 paths \<and> card paths = Suc sep_size"
  proof-
    have "ProofStepInduct G v0 v1 Q (v0 # R') sep_size" proof (rule ProofStepInduct.intro)
      show "DisjointPathsPlusOne G v0 v1 Q (v0 # R')" proof (rule DisjointPathsPlusOne.intro)
        show "DisjointPaths G v0 v1 Q"
          using DisjointPaths_supergraph H_x_def Q.DisjointPaths_axioms by auto
        show "DisjointPathsPlusOne_axioms G v0 v1 Q (v0 # R')" proof
          show "v0 \<leadsto>(v0 # R')\<leadsto> last (v0 # R')" using v0_R'_path by blast
          show "tl (v0 # R') \<noteq> []" using R'(1) by auto
          show "hd (tl (v0 # R')) \<notin> Q.second_vertices" using hd_R' P_k(2) by auto
          show "Q.hitting_paths (last (v0 # R'))" using z z_last_R' by auto
        next
          fix v assume "v \<in> set (butlast (v0 # R'))"
          then show "\<not>Q.hitting_paths v" using R'_no_Q path_from_to_last[OF v0_R'_path]
            by (metis Q.hitting_paths_def in_set_butlastD set_ConsD)
        qed
      qed
      show "ProofStepInduct_axioms Q sep_size" using sep_size_not0 Q(2) by unfold_locales
    qed (insert NoSmallSeparationsInduct_axioms)
    then have "H.distance (last P_new) v1 \<le> H.distance (last (v0 # R')) v1"
      using H_def optimal_paths[of Q "v0 # R'"] by blast
    then have False using z_last_R' new_last_def z_closer_than_new_last by simp
    then show ?thesis by blast
  qed

  corollary with_optimal_paths_solves':
    shows "\<exists>paths. DisjointPaths G v0 v1 paths \<and> card paths = Suc sep_size"
    using optimal_paths z_eq_v1_solves z_neq_v1_solves by blast
end \<comment> \<open>anonymous context\<close>

corollary with_optimal_paths_solves:
  "\<exists>paths. DisjointPaths G v0 v1 paths \<and> card paths = Suc sep_size"
  using optimal_paths with_optimal_paths_solves' R_decomp_exists by blast

end \<comment> \<open>locale @{locale ProofStepInduct_y_eq_new_last}\<close>
end
