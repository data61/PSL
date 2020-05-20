section \<open>Menger's Theorem\<close>

theory Menger imports Y_eq_new_last Y_neq_new_last begin

text \<open>In this section, we combine the cases and finally prove Menger's Theorem.\<close>

locale ProofStepInductOptimalPaths = ProofStepInduct +
  assumes optimal_paths:
    "\<And>paths' P_new'. ProofStepInduct G v0 v1 paths' P_new' sep_size
      \<Longrightarrow> Digraph.distance (remove_vertex v0) (last P_new) v1
       \<le> Digraph.distance (remove_vertex v0) (last P_new') v1"
begin

lemma one_more_paths_exists_trivial:
  "new_last = v1 \<Longrightarrow> \<exists>paths. DisjointPaths G v0 v1 paths \<and> card paths = Suc sep_size"
  using P_new_solves_if_disjoint paths_sep_size by blast

lemma one_more_paths_exists_nontrivial:
  assumes "new_last \<noteq> v1"
  shows "\<exists>paths. DisjointPaths G v0 v1 paths \<and> card paths = Suc sep_size"
proof-
  interpret ProofStepInduct_NonTrivial G v0 v1 paths P_new sep_size
    using assms new_last_def by unfold_locales simp
  obtain P_k_pre y P_k_post where
    "ProofStepInduct_NonTrivial_P_k_pre G v0 v1 paths P_new sep_size P_k_pre y P_k_post"
    using ProofStepInduct_NonTrivial_P_k_pre_exists by blast
  then interpret ProofStepInduct_NonTrivial_P_k_pre G v0 v1 paths P_new sep_size P_k_pre y P_k_post .
  {
    assume "y \<noteq> v1" "y = new_last"
    then interpret ProofStepInduct_y_eq_new_last G v0 v1 paths P_new sep_size P_k_pre y P_k_post
      using optimal_paths[folded H_def] by unfold_locales
    have ?thesis using with_optimal_paths_solves by blast
  } moreover {
    assume "y \<noteq> v1" "y \<noteq> new_last"
    then interpret ProofStepInduct_y_neq_new_last G v0 v1 paths P_new sep_size P_k_pre y P_k_post
      by unfold_locales
    have ?thesis using contradiction by blast
  }
  ultimately show ?thesis using y_eq_v1_solves by blast
qed

corollary one_more_paths_exists:
  shows "\<exists>paths. DisjointPaths G v0 v1 paths \<and> card paths = Suc sep_size"
  using one_more_paths_exists_trivial one_more_paths_exists_nontrivial by blast

end

lemma (in ProofStepInduct) one_more_paths_exists:
  "\<exists>paths. DisjointPaths G v0 v1 paths \<and> card paths = Suc sep_size"
proof-
  define paths_weight where "paths_weight \<equiv>
    \<lambda>(paths' :: 'a Walk set, P_new'). Digraph.distance (remove_vertex v0) (last P_new') v1"
  define paths_good where "paths_good \<equiv>
    \<lambda>(paths', P_new'). ProofStepInduct G v0 v1 paths' P_new' sep_size"
  have "\<exists>paths' P_new'. paths_good (paths', P_new')"
    unfolding paths_good_def using ProofStepInduct_axioms by auto
  then obtain P' where
    P': "paths_good P'" "\<And>P''. paths_good P'' \<Longrightarrow> paths_weight P' \<le> paths_weight P''"
    using arg_min_ex[of paths_good paths_weight] by blast

  then obtain paths' P_new' where P'_decomp: "P' = (paths', P_new')" by (meson surj_pair)

  have optimal_paths_good: "ProofStepInduct G v0 v1 paths' P_new' sep_size"
    using P'(1) P'_decomp unfolding paths_good_def by auto

  have "\<And>paths'' P_new''. paths_good (paths'', P_new'')
    \<Longrightarrow> paths_weight P' \<le> paths_weight (paths'', P_new'')" by (simp add: P'(2))
  then have optimal_paths_min: "\<And>paths'' P_new''. ProofStepInduct G v0 v1 paths'' P_new'' sep_size
    \<Longrightarrow> Digraph.distance (remove_vertex v0) (last P_new') v1
        \<le> Digraph.distance (remove_vertex v0) (last P_new'') v1"
    unfolding paths_good_def paths_weight_def by (simp add: P'_decomp)

  interpret G: ProofStepInductOptimalPaths G v0 v1 paths' P_new' sep_size
    using optimal_paths_good optimal_paths_min
    by (simp add: ProofStepInductOptimalPaths.intro ProofStepInductOptimalPaths_axioms.intro)
  show ?thesis using G.one_more_paths_exists by blast
qed

subsection \<open>Menger's Theorem\<close>

theorem (in v0_v1_Digraph) menger:
  assumes "\<And>S. Separation G v0 v1 S \<Longrightarrow> card S \<ge> n"
  shows "\<exists>paths. DisjointPaths G v0 v1 paths \<and> card paths = n"
using assms v0_v1_Digraph_axioms proof (induct n arbitrary: G)
  case (0 G)
  then show ?case using v0_v1_Digraph.DisjointPaths_empty[of G] card_empty by blast
next
  case (Suc n G)
  interpret G: v0_v1_Digraph G v0 v1 using Suc(3) .
  have "\<And>S. Separation G v0 v1 S \<Longrightarrow> n \<le> card S" using Suc.prems Suc_leD by blast
  then obtain paths where P: "DisjointPaths G v0 v1 paths" "card paths = n" using Suc(1,3) by blast
  interpret G: DisjointPaths G v0 v1 paths using P(1) .

  obtain P_new where
    P_new: "v0 \<leadsto>P_new\<leadsto>\<^bsub>G\<^esub> v1" "set P_new \<inter> G.second_vertices = {}"
    using G.disjoint_paths_new_path P(2) Suc.prems(1) by blast
  have P_new_new: "P_new \<notin> paths"
    by (metis G.paths_tl_notnil G.second_vertex_def G.second_vertices_def G.path_from_toE IntI
        P_new empty_iff image_eqI list.set_sel(1) list.set_sel(2))

  have "G.hitting_paths v1" unfolding G.hitting_paths_def using v0_neq_v1 by blast
  then have "\<exists>x \<in> set P_new. G.hitting_paths x" using P_new(1) by fastforce
  then obtain new_pre x new_post where
    P_new_decomp: "P_new = new_pre @ x # new_post"
    and x: "G.hitting_paths x"
           "\<And>y. y \<in> set new_pre \<Longrightarrow> \<not>G.hitting_paths y"
    by (metis split_list_first_prop)

  have 1: "DisjointPathsPlusOne G v0 v1 paths (new_pre @ [x])" proof
    show "v0 \<leadsto>(new_pre @ [x])\<leadsto>\<^bsub>G\<^esub> last (new_pre @ [x])" using P_new(1)
      by (metis G.path_decomp' P_new_decomp append_is_Nil_conv hd_append2 list.distinct(1)
          list.sel(1) path_from_to_def self_append_conv2)
    then show "tl (new_pre @ [x]) \<noteq> []"
      by (metis DisjointPaths.hitting_paths_def G.DisjointPaths_axioms G.path_from_toE
          butlast.simps(1) butlast_snoc list.distinct(1) list.sel(1) self_append_conv2
          tl_append2 x(1))
    have "new_pre \<noteq> Nil" using G.hitting_paths_def P_new(1) P_new_decomp x(1) by auto
    then have "hd (tl (new_pre @ [x])) = hd (tl P_new)" by (simp add: P_new_decomp hd_append)
    then show "hd (tl (new_pre @ [x])) \<notin> G.second_vertices"
      by (metis P_new(2) P_new_decomp \<open>new_pre \<noteq> []\<close> append_is_Nil_conv disjoint_iff_not_equal
          list.distinct(1) list.set_sel(1) list.set_sel(2) tl_append2)
    show "G.hitting_paths (last (new_pre @ [x]))" using x(1) by auto
    show "\<And>v. v \<in> set (butlast (new_pre @ [x])) \<Longrightarrow> \<not>G.hitting_paths v" by (simp add: x(2))
  qed

  have 2: "NoSmallSeparationsInduct G v0 v1 n"
    by (simp add: G.v0_v1_Digraph_axioms NoSmallSeparationsInduct.intro
        NoSmallSeparationsInduct_axioms_def Suc.hyps Suc.prems(1))

  show ?case proof (rule ccontr)
    assume not_case: "\<not>?case"
    have "x \<noteq> v1" proof
      assume "x = v1"
      define paths' where "paths' = insert P_new paths"
      {
        fix xs v
        assume *: "xs \<in> paths" "v \<in> set xs" "v \<in> set P_new" "v \<noteq> v0" "v \<noteq> v1"
        have "v \<in> set new_pre"
          by (metis *(3,5) G.path_from_to_ends G.path_from_toE P_new(1) P_new_decomp
              \<open>x = v1\<close> butlast_snoc set_butlast)
        then have False using *(1,2,4) G.hitting_paths_def x(2) by auto
      }
      then have "DisjointPaths G v0 v1 paths'" unfolding paths'_def
        using G.DisjointPaths_extend P_new(1) by blast
      moreover have "card paths' = Suc n"
        using P_new_new by (simp add: G.finite_paths P(2) paths'_def)
      ultimately show False using not_case by blast
    qed
    have "ProofStepInduct_axioms paths n" proof
      show "n \<noteq> 0"
        using G.DisjointPaths_extend G.finite_paths P(2) P_new(1) not_case card_insert_disjoint
        by fastforce
    qed (insert P(2))
    then have "ProofStepInduct G v0 v1 paths (new_pre @ [x]) n"
      using 1 2 by (simp add: ProofStepInduct.intro)
    then show False using ProofStepInduct.one_more_paths_exists not_case by metis
  qed
qed

text \<open>
  The previous theorem was the difficult direction of Menger's Theorem.  Let us now prove the other
  direction: If we have @{term n} disjoint paths, than every separator must contain at least
  @{term n} vertices.  This direction is rather trivial because every separator needs to separate
  at least the @{term n} paths, so we do not need induction or an elaborate setup to prove this.
\<close>

theorem (in v0_v1_Digraph) menger_trivial:
  assumes "DisjointPaths G v0 v1 paths" "card paths = n"
  shows "\<And>S. Separation G v0 v1 S \<Longrightarrow> card S \<ge> n"
proof-
  interpret DisjointPaths G v0 v1 paths using assms(1) .
  fix S assume "Separation G v0 v1 S"
  then interpret S: Separation G v0 v1 S .

  text \<open>
    Our plan is to show @{term "card S \<ge> n"} by defining an injective function from @{term paths}
    into @{term S}.  Because we have @{term "card paths = n"}, the result follows.

    For the injective function, we simply use the observation stated above: Every path needs to
    be separated by @{term S} at some vertex, so we can choose such a vertex.
\<close>
  define f where "f \<equiv> \<lambda>xs. SOME v. v \<in> S \<and> v \<in> set xs"

  have f_good: "\<And>xs. xs \<in> paths \<Longrightarrow> f xs \<in> S \<and> f xs \<in> set xs" proof-
    fix xs assume "xs \<in> paths"
    then obtain v where "v \<in> set xs \<inter> S" using S.S_separates paths by fastforce
    then show "f xs \<in> S \<and> f xs \<in> set xs" unfolding f_def
      using someI[of "\<lambda>v. v \<in> S \<and> v \<in> set xs" v] by blast
  qed

  text \<open>This @{term f} is injective because no two paths intersect in the same vertex.\<close>
  have "inj_on f paths" proof
    fix xs ys
    assume *: "xs \<in> paths" "ys \<in> paths" "f xs = f ys"
    then obtain v where "v \<in> S" "v \<in> set xs" "v \<in> set ys"
      using f_good by fastforce
    then show "xs = ys" using *(1,2) paths_disjoint S.v0_notin_S S.v1_notin_S by fastforce
  qed

  then show "card S \<ge> n" using assms(2) f_good
    by (metis S.finite_S finite_paths image_subsetI inj_on_iff_card_le)
qed

subsection \<open>Self-contained Statement of the Main Theorem\<close>

text \<open>
  Let us state both directions of Menger's Theorem again in a more self-contained way in the
  @{locale Digraph} locale. Stating the theorems in a self-contained way helps avoiding mistakes
  due to wrong definitions hidden in one of the numerous locales we used and also significantly
  reduces the work needed to review this formalization.

  With the statements below, all you need to do in order to verify that this formalization
  actually expresses Menger's Theorem (and not something else), is to look into the assumptions
  and definitions of the @{locale Digraph} locale.
\<close>

theorem (in Digraph) menger:
  fixes v0 v1 :: 'a and n :: nat
  assumes v0_V: "v0 \<in> V"
      and v1_V: "v1 \<in> V"
      and v0_nonadj_v1: "\<not>v0\<rightarrow>v1"
      and v0_neq_v1: "v0 \<noteq> v1"
      and no_small_separators: "\<And>S.
        \<lbrakk> S \<subseteq> V; v0 \<notin> S; v1 \<notin> S; \<And>xs. v0 \<leadsto>xs\<leadsto> v1 \<Longrightarrow> set xs \<inter> S \<noteq> {} \<rbrakk> \<Longrightarrow> card S \<ge> n"
  shows "\<exists>paths. card paths = n \<and> (\<forall>xs \<in> paths.
    v0 \<leadsto>xs\<leadsto> v1 \<and> (\<forall>ys \<in> paths - {xs}. (\<forall>v \<in> set xs \<inter> set ys. v = v0 \<or> v = v1)))"
proof-
  interpret v0_v1_Digraph G v0 v1 using v0_V v1_V v0_nonadj_v1 v0_neq_v1 by unfold_locales
  have "\<And>S. Separation G v0 v1 S \<Longrightarrow> n \<le> card S" using no_small_separators
    by (simp add: Separation.S_V Separation.S_separates Separation.v0_notin_S Separation.v1_notin_S)
  then obtain paths where
    paths: "DisjointPaths G v0 v1 paths" "card paths = n" using no_small_separators menger by blast
  then show ?thesis
    by (metis DiffD1 DiffD2 DisjointPaths.paths DisjointPaths.paths_disjoint IntD1 IntD2 singletonI)
qed

theorem (in Digraph) menger_trivial:
  fixes v0 v1 :: 'a and n :: nat
  assumes v0_V: "v0 \<in> V"
      and v1_V: "v1 \<in> V"
      and v0_nonadj_v1: "\<not>v0\<rightarrow>v1"
      and v0_neq_v1: "v0 \<noteq> v1"
      and n_paths: "card paths = n"
      and paths_disjoint: "\<forall>xs \<in> paths.
        v0 \<leadsto>xs\<leadsto> v1 \<and> (\<forall>ys \<in> paths - {xs}. (\<forall>v \<in> set xs \<inter> set ys. v = v0 \<or> v = v1))"
  shows "\<And>S. \<lbrakk> S \<subseteq> V; v0 \<notin> S; v1 \<notin> S; \<And>xs. v0 \<leadsto>xs\<leadsto> v1 \<Longrightarrow> set xs \<inter> S \<noteq> {} \<rbrakk> \<Longrightarrow> card S \<ge> n"
proof-
  interpret v0_v1_Digraph G v0 v1 using v0_V v1_V v0_nonadj_v1 v0_neq_v1 by unfold_locales
  interpret DisjointPaths G v0 v1 paths proof
    show "\<And>xs. xs \<in> paths \<Longrightarrow> v0 \<leadsto>xs\<leadsto> v1" using paths_disjoint by simp
  next
    fix xs ys v assume "xs \<in> paths" "ys \<in> paths" "xs \<noteq> ys" "v \<in> set xs" "v \<in> set ys"
    then have "xs \<in> paths" "ys \<in> paths - {xs}" "v \<in> set xs \<inter> set ys" by blast+
    then show "v = v0 \<or> v = v1" using paths_disjoint by blast
  qed
  fix S assume "S \<subseteq> V" "v0 \<notin> S" "v1 \<notin> S" "\<And>xs. v0 \<leadsto>xs\<leadsto> v1 \<Longrightarrow> set xs \<inter> S \<noteq> {}"
  then interpret Separation G v0 v1 S by unfold_locales
  show "card S \<ge> n" using menger_trivial DisjointPaths_axioms Separation_axioms n_paths by blast
qed

end
