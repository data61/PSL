section \<open>Induction of Menger's Theorem\<close>

theory MengerInduction imports Separations DisjointPaths begin

subsection \<open>No Small Separations\<close>

text \<open>
  In this section we set up the general structure of the proof of Menger's Theorem.
  The proof is based on induction over @{term sep_size} (called @{term n} in McCuaig's proof), the
  minimum size of a separator.
\<close>

locale NoSmallSeparationsInduct = v0_v1_Digraph +
  fixes sep_size :: nat
  \<comment> \<open>The size of a minimum separator.\<close>
  assumes no_small_separations: "\<And>S. Separation G v0 v1 S \<Longrightarrow> card S \<ge> Suc sep_size"
  \<comment> \<open>The induction hypothesis.\<close>
  and no_small_separations_hyp: "\<And>G' :: ('a, 'b) Graph_scheme.
    (\<And>S. Separation G' v0 v1 S \<Longrightarrow> card S \<ge> sep_size)
    \<Longrightarrow> v0_v1_Digraph G' v0 v1
    \<Longrightarrow> \<exists>paths. DisjointPaths G' v0 v1 paths \<and> card paths = sep_size"

text \<open>
  Next, we want to combine this with @{locale DisjointPathsPlusOne}.

  If a minimum separator has size at least @{term "Suc sep_size"}, then it follows immediately from
  the induction hypothesis that we have @{term sep_size} many disjoint paths.  We then observe
  that @{term second_vertices} of these paths is not a separator because
  @{term "card second_vertices = sep_size"}.  So there exists a new path from @{term v0} to
  @{term v1} whose second vertex is not in @{term second_vertices}.

  If this path is disjoint from the other paths, we have found @{term "Suc sep_size"} many disjoint
  paths, so assume it is not disjoint.  Then there exist a vertex @{term x} on the new path that is
  not @{term v0} or @{term v1} such that @{term new_last} hits one of the other paths.  Let
  @{term P_new} be the initial segment of the new path up to @{term x}.  We call @{term x},
  the last vertex of @{term P_new}, now @{term new_last}.

  We then assume that @{term paths} and @{term P_new} have been chosen in such a way that
  @{term "distance new_last v1"} is minimal.

  First, we define a locale that expresses that we have no small separators (with the corresponding
  induction hypothesis) as well as @{term sep_size} many internally vertex-disjoint paths (with
  @{term "sep_size \<noteq> (0 :: nat)"} because the other case is trivial) and also one additional path
  that starts in @{term v1}, whose second vertex is not among @{term second_vertices} and whose last
  vertex is @{term new_last}.

  We will add the assumption @{term "new_last \<noteq> v1"} soon.
\<close>

locale ProofStepInduct =
  NoSmallSeparationsInduct G v0 v1 sep_size + DisjointPathsPlusOne G v0 v1 paths P_new
  for G (structure) and v0 v1 paths P_new sep_size +
  assumes sep_size_not0: "sep_size \<noteq> 0"
    and paths_sep_size: "card paths = sep_size"

lemma (in ProofStepInduct) hitting_paths_v1: "hitting_paths v1"
  unfolding hitting_paths_def using paths v0_neq_v1 by force

subsection \<open>Choosing Paths Avoiding $new\_last$\<close>

text \<open>Let us now consider only the non-trivial case that @{term "new_last \<noteq> v1"}.\<close>

locale ProofStepInduct_NonTrivial = ProofStepInduct +
  assumes new_last_neq_v1: "new_last \<noteq> v1"
begin

text \<open>
  The next step is the observation that in the graph @{term "remove_vertex new_last"}, which 
  we called @{term H_x}, there are also @{term sep_size} many internally vertex-disjoint paths,
  again by the induction hypothesis.
\<close>
lemma Q_exists: "\<exists>Q. DisjointPaths H_x v0 v1 Q \<and> card Q = sep_size"
proof-
  have "\<And>S. Separation H_x v0 v1 S \<Longrightarrow> card S \<ge> sep_size"
    using subgraph_separation_min_size paths walk_in_V P_hit new_last_neq_v1 no_small_separations
      by (metis H_x_def new_last_in_V new_last_neq_v0)
  then show ?thesis using H_x_v0_v1_Digraph new_last_neq_v1 by (meson no_small_separations_hyp)
qed

text \<open>
  We want to choose these paths in a clever way, too.  Our goal is to choose these paths such that
  the number of edges in @{term "(\<Union>(edges_of_walk ` Q) \<inter> (E - \<Union>(edges_of_walk ` paths_with_new)))"}
  is minimal.
\<close>

definition B where "B \<equiv> E - \<Union>(edges_of_walk ` paths_with_new)"

definition Q_weight where "Q_weight \<equiv> \<lambda>Q. card (\<Union>(edges_of_walk ` Q) \<inter> B)"

definition Q_good where "Q_good \<equiv> \<lambda>Q. DisjointPaths H_x v0 v1 Q \<and> card Q = sep_size \<and>
  (\<forall>Q'. DisjointPaths H_x v0 v1 Q' \<and> card Q' = sep_size \<longrightarrow> Q_weight Q \<le> Q_weight Q')"

definition Q where "Q \<equiv> SOME Q. Q_good Q"

text \<open>It is easy to show that such a @{const Q} exists.\<close>

lemma Q: "DisjointPaths H_x v0 v1 Q" "card Q = sep_size"
  and Q_min: "\<And>Q'. DisjointPaths H_x v0 v1 Q' \<and> card Q' = sep_size \<Longrightarrow> Q_weight Q \<le> Q_weight Q'"
proof-
  obtain Q' where "DisjointPaths H_x v0 v1 Q'" "card Q' = sep_size"
    "\<And>Q''. DisjointPaths H_x v0 v1 Q'' \<and> card Q'' = sep_size \<Longrightarrow> Q_weight Q' \<le> Q_weight Q''"
    using arg_min_ex[of "\<lambda>Q. DisjointPaths H_x v0 v1 Q \<and> card Q = sep_size" Q_weight]
      new_last_neq_v1 Q_exists by metis
  then have "Q_good Q'" unfolding Q_good_def by blast
  then show "DisjointPaths H_x v0 v1 Q" "card Q = sep_size"
    "\<And>Q'. DisjointPaths H_x v0 v1 Q' \<and> card Q' = sep_size \<Longrightarrow> Q_weight Q \<le> Q_weight Q'"
    using someI[of Q_good] by (simp_all add: Q_def Q_good_def)
qed

sublocale Q: DisjointPaths H_x v0 v1 Q using Q(1) .

subsection \<open>Finding a Path Avoiding $Q$\<close>

text \<open>
  Because @{const Q} contains only @{term sep_size} many paths, we have
  @{term "card Q.second_vertices = sep_size"}.  So there exists a path @{term P_k} among the
  @{term "Suc sep_size"} many paths in @{term paths_with_new} such that the second vertex of
  @{term P_k} is not among @{term Q.second_vertices}.
\<close>
definition P_k where
  "P_k \<equiv> SOME P_k. P_k \<in> paths_with_new \<and> hd (tl P_k) \<notin> Q.second_vertices"

lemma P_k: "P_k \<in> paths_with_new" "hd (tl P_k) \<notin> Q.second_vertices" proof-
  obtain y where "y \<in> insert (hd (tl P_new)) second_vertices" "y \<notin> Q.second_vertices" proof-
    have "hd (tl P_new) \<notin> second_vertices" using P_new_decomp tl_P_new(2) by simp
    moreover have "card second_vertices = card Q.second_vertices" using Q(2) paths_sep_size
      using Q.second_vertices_card second_vertices_card by (simp add: new_last_neq_v1)
    ultimately have "card (insert (hd (tl P_new)) second_vertices) = Suc (card Q.second_vertices)"
      using finite_paths second_vertices_def by auto
    then show ?thesis
      using that card_finite_less_ex
      by (metis Q.finite_paths Q.second_vertices_def Zero_not_Suc card_infinite finite_imageI lessI)
  qed
  then have "\<exists>P_k. P_k \<in> paths_with_new \<and> hd (tl P_k) \<notin> Q.second_vertices"
    by (metis (mono_tags, lifting) image_iff insertCI insertE paths_with_new_def second_vertex_def
        second_vertices_def)
  then show "P_k \<in> paths_with_new" "hd (tl P_k) \<notin> Q.second_vertices"
    using someI[of "\<lambda>P_k. P_k \<in> paths_with_new \<and> hd (tl P_k) \<notin> Q.second_vertices"] P_k_def by auto
qed

lemma path_P_k [simp]: "path P_k" by (simp add: P_k(1) paths_with_new_path)
lemma hd_P_k_v0 [simp]: "hd P_k = v0" by (simp add: P_k(1) paths_with_new_start_in_v0)

definition hitting_Q_or_new_last where
  "hitting_Q_or_new_last \<equiv> \<lambda>y. y \<noteq> v0 \<and> (y = new_last \<or> (\<exists>Q_hit \<in> Q. y \<in> set Q_hit))"

text \<open>
  @{term P_k} hits a vertex in @{term Q} or it hits @{term new_last} because it either ends in
  @{term v1} or in @{term new_last}.
\<close>

lemma P_k_hits_Q: "\<exists>y \<in> set P_k. hitting_Q_or_new_last y" proof (cases)
  assume "P_k \<noteq> P_new"
  then have "v1 \<in> set P_k"
    by (metis P_k(1) insertE last_in_set path_from_toE paths paths_with_new_def)
  moreover have "\<exists>Q_witness. Q_witness \<in> Q" using Q(2) sep_size_not0 finite.simps by fastforce
  ultimately show ?thesis
    using Q.paths path_from_toE hitting_Q_or_new_last_def v0_neq_v1 by fastforce
qed (metis P_new new_last_neq_v0 hitting_Q_or_new_last_def last_in_set path_from_toE new_last_def)

end \<comment> \<open>locale @{locale ProofStepInduct_NonTrivial}\<close>

subsection \<open>Decomposing $P_k$\<close>

text \<open>
  Having established with the previous lemma that @{term P_k} hits @{term Q} or @{term new_last},
  let @{term y} be the first such vertex on @{term P_k}.  Then we can split @{term P_k} at
  this vertex.
\<close>

locale ProofStepInduct_NonTrivial_P_k_pre = ProofStepInduct_NonTrivial +
  fixes P_k_pre y P_k_post
  assumes P_k_decomp: "P_k = P_k_pre @ y # P_k_post"
      and y: "hitting_Q_or_new_last y"
      and y_min: "\<And>y'. y' \<in> set P_k_pre \<Longrightarrow> \<not>hitting_Q_or_new_last y'"

text \<open>
  We can always go from @{locale ProofStepInduct_NonTrivial} to @{locale ProofStepInduct_NonTrivial_P_k_pre}.
\<close>
lemma (in ProofStepInduct_NonTrivial) ProofStepInduct_NonTrivial_P_k_pre_exists:
  shows "\<exists>P_k_pre y P_k_post.
     ProofStepInduct_NonTrivial_P_k_pre G v0 v1 paths P_new sep_size P_k_pre y P_k_post"
proof-
  obtain y P_k_pre P_k_post where
    "P_k = P_k_pre @ y # P_k_post" "hitting_Q_or_new_last y"
    "\<And>y'. y' \<in> set P_k_pre \<Longrightarrow> \<not>hitting_Q_or_new_last y'"
    using P_k_hits_Q split_list_first_prop[of P_k hitting_Q_or_new_last] by blast
  then have "ProofStepInduct_NonTrivial_P_k_pre G v0 v1 paths P_new sep_size P_k_pre y P_k_post"
    by unfold_locales
  then show ?thesis by blast
qed

context ProofStepInduct_NonTrivial_P_k_pre begin
  lemma y_neq_v0: "y \<noteq> v0" using hitting_Q_or_new_last_def y by auto

  lemma P_k_pre_not_Nil: "P_k_pre \<noteq> Nil"
    using P_k_decomp hd_P_k_v0 hitting_Q_or_new_last_def y by auto

  lemma second_P_k_pre_not_in_Q: "hd (tl (P_k_pre @ [y])) \<notin> Q.second_vertices"
    using P_k(2) P_k_decomp P_k_pre_not_Nil
    by (metis append_eq_append_conv2 append_self_conv hd_append2 list.sel(1) tl_append2)

  definition H where "H \<equiv> remove_vertex v0"
  sublocale H: Digraph H unfolding H_def using remove_vertex_Digraph .

  lemma y_eq_v1_implies_P_k_neq_P_new: assumes "y = v1" shows "P_k \<noteq> P_new" proof
    assume contra: "P_k = P_new"
    have "v0 \<leadsto>(new_pre @ [new_last])\<leadsto> new_last"
      using P_new(1) P_new_decomp new_last_def by auto
    then have "v0 \<leadsto>P_k\<leadsto> new_last" using P_new_decomp contra by auto
    moreover have "P_k = P_k_pre @ v1 # P_k_post" using P_k_decomp assms(1) by blast
    ultimately have **: "v0 \<leadsto>(P_k_pre @ v1 # P_k_post)\<leadsto> new_last" by simp
    then have "v1 \<in> set P_new" by (metis assms contra P_k_decomp in_set_conv_decomp)
    then have "new_last = v1"
      using hitting_paths_v1 assms last_P_new(2) set_butlast new_last_def by fastforce
    then show False using new_last_neq_v1 by blast
  qed

  text \<open>If @{term "y = v1"}, then we are done.\<close>
  lemma y_eq_v1_solves:
    assumes "y = v1"
    shows "\<exists>paths. DisjointPaths G v0 v1 paths \<and> card paths = Suc sep_size"
  proof-
    have "P_k \<noteq> P_new" using y_eq_v1_implies_P_k_neq_P_new assms by blast
    then have "P_k = P_k_pre @ [y]"
      using P_k(1) P_k_decomp paths assms paths_with_new_def by fastforce
    then have "v0 \<leadsto>(P_k_pre @ [y])\<leadsto> v1"
      using paths P_k(1) \<open>P_k \<noteq> P_new\<close> by (simp add: paths_with_new_def)
    moreover have "new_last \<notin> set P_k_pre"
      using hitting_Q_or_new_last_def y_min new_last_neq_v0 by auto
    ultimately have "v0 \<leadsto>(P_k_pre @ [y])\<leadsto>\<^bsub>H_x\<^esub> v1" using remove_vertex_path_from_to
        by (simp add: H_x_def assms new_last_in_V new_last_neq_v1)
    moreover {
      fix xs v assume "xs \<in> Q" "v \<in> set xs" "v \<in> set (P_k_pre @ [y])" "v \<noteq> v0" "v \<noteq> v1"
      then have "v \<in> set P_k_pre" using assms by simp
      then have "\<not>hitting_Q_or_new_last v" using y_min by blast
      then have "False" using \<open>v \<in> set xs\<close> \<open>xs \<in> Q\<close> hitting_Q_or_new_last_def \<open>v \<noteq> v0\<close> by auto
    }
    ultimately have "DisjointPaths H_x v0 v1 (insert (P_k_pre @ [y]) Q)"
      using Q.DisjointPaths_extend by blast
    then have "DisjointPaths G v0 v1 (insert (P_k_pre @ [y]) Q)"
      using DisjointPaths_supergraph H_x_def new_last_in_V new_last_neq_v0 new_last_neq_v1 by auto
    moreover have "card (insert (P_k_pre @ [y]) Q) = Suc sep_size" proof-
      have "P_k_pre @ [y] \<notin> Q"
        by (metis P_k(2) Q.second_vertices_def \<open>P_k = P_k_pre @ [y]\<close> image_iff second_vertex_def)
      then show ?thesis by (simp add: Q(2) Q.finite_paths)
    qed
    ultimately show ?thesis by blast
  qed
end \<comment> \<open>locale @{locale ProofStepInduct_NonTrivial_P_k_pre}\<close>

end
