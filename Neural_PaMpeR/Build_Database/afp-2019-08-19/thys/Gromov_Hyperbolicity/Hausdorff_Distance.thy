(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>Hausdorff distance\<close>

theory Hausdorff_Distance
  imports Library_Complements
begin

subsection \<open>Preliminaries\<close>



subsection \<open>Hausdorff distance\<close>

text \<open>The Hausdorff distance between two subsets of a metric space is the minimal $M$ such that
each set is included in the $M$-neighborhood of the other. For nonempty bounded sets, it
satisfies the triangular inequality, it is symmetric, but it vanishes on sets that have the same
closure. In particular, it defines a distance on closed bounded nonempty sets. We establish
all these properties below.\<close>

definition hausdorff_distance::"('a::metric_space) set \<Rightarrow> 'a set \<Rightarrow> real"
  where "hausdorff_distance A B = (if A = {} \<or> B = {} \<or> (\<not>(bounded A)) \<or> (\<not>(bounded B)) then 0
                                   else max (SUP x\<in>A. infdist x B) (SUP x\<in>B. infdist x A))"

lemma hausdorff_distance_self [simp]:
  "hausdorff_distance A A = 0"
unfolding hausdorff_distance_def by auto

lemma hausdorff_distance_sym:
  "hausdorff_distance A B = hausdorff_distance B A"
unfolding hausdorff_distance_def by auto

lemma hausdorff_distance_points [simp]:
  "hausdorff_distance {x} {y} = dist x y"
unfolding hausdorff_distance_def by (auto, metis dist_commute max.idem)

text \<open>The Hausdorff distance is expressed in terms of a supremum. To use it, one needs again
and again to show that this is the supremum of a set which is bounded from above.\<close>

lemma bdd_above_infdist_aux:
  assumes "bounded A" "bounded B"
  shows "bdd_above ((\<lambda>x. infdist x B)`A)"
proof (cases "B = {}")
  case True
  then show ?thesis unfolding infdist_def by auto
next
  case False
  then obtain y where "y \<in> B" by auto
  then have "infdist x B \<le> dist x y" if "x \<in> A" for x
    by (simp add: infdist_le)
  then show ?thesis unfolding bdd_above_def
    by (auto, metis assms(1) bounded_any_center dist_commute order_trans)
qed

lemma hausdorff_distance_nonneg [simp, mono_intros]:
  "hausdorff_distance A B \<ge> 0"
proof (cases "A = {} \<or> B = {} \<or> (\<not>(bounded A)) \<or> (\<not>(bounded B))")
  case True
  then show ?thesis unfolding hausdorff_distance_def by auto
next
  case False
  then have "A \<noteq> {}" "B \<noteq> {}" "bounded A" "bounded B" by auto
  have "(SUP x\<in>A. infdist x B) \<ge> 0"
    using bdd_above_infdist_aux[OF \<open>bounded A\<close> \<open>bounded B\<close>] infdist_nonneg
    by (metis \<open>A \<noteq> {}\<close> all_not_in_conv cSUP_upper2)
  moreover have "(SUP x\<in>B. infdist x A) \<ge> 0"
    using bdd_above_infdist_aux[OF \<open>bounded B\<close> \<open>bounded A\<close>] infdist_nonneg
    by (metis \<open>B \<noteq> {}\<close> all_not_in_conv cSUP_upper2)
  ultimately show ?thesis unfolding hausdorff_distance_def by auto
qed

lemma hausdorff_distanceI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> infdist x B \<le> D"
          "\<And>x. x \<in> B \<Longrightarrow> infdist x A \<le> D"
          "D \<ge> 0"
  shows "hausdorff_distance A B \<le> D"
proof (cases "A = {} \<or> B = {} \<or> (\<not>(bounded A)) \<or> (\<not>(bounded B))")
  case True
  then show ?thesis unfolding hausdorff_distance_def using \<open>D \<ge> 0\<close> by auto
next
  case False
  then have "A \<noteq> {}" "B \<noteq> {}" "bounded A" "bounded B" by auto
  have "(SUP x\<in>A. infdist x B) \<le> D"
    apply (rule cSUP_least, simp add: \<open>A \<noteq> {}\<close>) using assms(1) by blast
  moreover have "(SUP x\<in>B. infdist x A) \<le> D"
    apply (rule cSUP_least, simp add: \<open>B \<noteq> {}\<close>) using assms(2) by blast
  ultimately show ?thesis unfolding hausdorff_distance_def using False by auto
qed

lemma hausdorff_distanceI2:
  assumes "\<And>x. x \<in> A \<Longrightarrow> \<exists>y\<in>B. dist x y \<le> D"
          "\<And>x. x \<in> B \<Longrightarrow> \<exists>y\<in>A. dist x y \<le> D"
          "D \<ge> 0"
  shows "hausdorff_distance A B \<le> D"
proof (rule hausdorff_distanceI[OF _ _ \<open>D \<ge> 0\<close>])
  fix x assume "x \<in> A" show "infdist x B \<le> D" using assms(1)[OF \<open>x \<in> A\<close>] infdist_le2 by fastforce
next
  fix x assume "x \<in> B" show "infdist x A \<le> D" using assms(2)[OF \<open>x \<in> B\<close>] infdist_le2 by fastforce
qed

lemma infdist_le_hausdorff_distance [mono_intros]:
  assumes "x \<in> A" "bounded A" "bounded B"
  shows "infdist x B \<le> hausdorff_distance A B"
proof (cases "B = {}")
  case True
  then have "infdist x B = 0" unfolding infdist_def by auto
  then show ?thesis using hausdorff_distance_nonneg by auto
next
  case False
  have "infdist x B \<le> (SUP y\<in>A. infdist y B)"
    using bdd_above_infdist_aux[OF \<open>bounded A\<close> \<open>bounded B\<close>] by (meson assms(1) cSUP_upper)
  then show ?thesis unfolding hausdorff_distance_def using assms False by auto
qed

lemma hausdorff_distance_infdist_triangle [mono_intros]:
  assumes "B \<noteq> {}" "bounded B" "bounded C"
  shows "infdist x C \<le> infdist x B + hausdorff_distance B C"
proof (cases "C = {}")
  case True
  then have "infdist x C = 0" unfolding infdist_def by auto
  then show ?thesis using infdist_nonneg[of x B] hausdorff_distance_nonneg[of B C] by auto
next
  case False
  have "infdist x C - hausdorff_distance B C \<le> dist x b" if "b \<in> B" for b
  proof -
    have "infdist x C \<le> infdist b C + dist x b" by (rule infdist_triangle)
    also have "... \<le> dist x b + hausdorff_distance B C"
      using infdist_le_hausdorff_distance[OF \<open>b \<in> B\<close> \<open>bounded B\<close> \<open>bounded C\<close>] by auto
    finally show ?thesis by auto
  qed
  then have "infdist x C - hausdorff_distance B C \<le> infdist x B"
    unfolding infdist_def using \<open>B \<noteq> {}\<close> by (simp add: le_cINF_iff)
  then show ?thesis by auto
qed

lemma hausdorff_distance_triangle [mono_intros]:
  assumes "B \<noteq> {}" "bounded B"
  shows "hausdorff_distance A C \<le> hausdorff_distance A B + hausdorff_distance B C"
proof (cases "A = {} \<or> C = {} \<or> (\<not>(bounded A)) \<or> (\<not>(bounded C))")
  case True
  then have "hausdorff_distance A C = 0" unfolding hausdorff_distance_def by auto
  then show ?thesis
    using hausdorff_distance_nonneg[of A B] hausdorff_distance_nonneg[of B C] by auto
next
  case False
  then have *: "A \<noteq> {}" "C \<noteq> {}" "bounded A" "bounded C" by auto
  define M where "M = hausdorff_distance A B + hausdorff_distance B C"
  have "infdist x C \<le> M" if "x \<in> A" for x
    using hausdorff_distance_infdist_triangle[OF \<open>B \<noteq> {}\<close> \<open>bounded B \<close> \<open>bounded C\<close>, of x]
          infdist_le_hausdorff_distance[OF \<open>x \<in> A\<close> \<open>bounded A\<close> \<open>bounded B\<close>] by (auto simp add: M_def)
  moreover have "infdist x A \<le> M" if "x \<in> C" for x
    using hausdorff_distance_infdist_triangle[OF \<open>B \<noteq> {}\<close> \<open>bounded B \<close> \<open>bounded A\<close>, of x]
          infdist_le_hausdorff_distance[OF \<open>x \<in> C\<close> \<open>bounded C\<close> \<open>bounded B\<close>]
    by (auto simp add: hausdorff_distance_sym M_def)
  ultimately have "hausdorff_distance A C \<le> M"
    unfolding hausdorff_distance_def using * bdd_above_infdist_aux by (auto simp add: cSUP_least)
  then show ?thesis unfolding M_def by auto
qed

lemma hausdorff_distance_subset:
  assumes "A \<subseteq> B" "A \<noteq> {}" "bounded B"
  shows "hausdorff_distance A B = (SUP x\<in>B. infdist x A)"
proof -
  have H: "B \<noteq> {}" "bounded A" using assms bounded_subset by auto
  have "(SUP x\<in>A. infdist x B) = 0" using assms by (simp add: subset_eq)
  moreover have "(SUP x\<in>B. infdist x A) \<ge> 0"
    using bdd_above_infdist_aux[OF \<open>bounded B\<close> \<open>bounded A\<close>] infdist_nonneg[of _ A]
    by (meson H(1) cSUP_upper2 ex_in_conv)
  ultimately show ?thesis unfolding hausdorff_distance_def using assms H by auto
qed

lemma hausdorff_distance_closure [simp]:
  "hausdorff_distance A (closure A) = 0"
proof (cases "A = {} \<or> (\<not>(bounded A))")
  case True
  then show ?thesis unfolding hausdorff_distance_def by auto
next
  case False
  then have "A \<noteq> {}" "bounded A" by auto
  then have "closure A \<noteq> {}" "bounded (closure A)" "A \<subseteq> closure A"
    using closure_subset by auto
  have "infdist x A = 0" if "x \<in> closure A" for x
    using in_closure_iff_infdist_zero[OF \<open>A \<noteq> {}\<close>] that by auto
  then have "(SUP x\<in>closure A. infdist x A) = 0"
    using \<open>closure A \<noteq> {}\<close> by auto
  then show ?thesis
    unfolding hausdorff_distance_subset[OF \<open>A \<subseteq> closure A\<close> \<open>A \<noteq> {}\<close> \<open>bounded (closure A)\<close>] by simp
qed

lemma hausdorff_distance_closures [simp]:
  "hausdorff_distance (closure A) (closure B) = hausdorff_distance A B"
proof (cases "A = {} \<or> B = {} \<or> (\<not>(bounded A)) \<or> (\<not>(bounded B))")
  case True
  then have *: "hausdorff_distance A B = 0" unfolding hausdorff_distance_def by auto
  have "closure A = {} \<or> (\<not>(bounded (closure A))) \<or> closure B = {} \<or> (\<not>(bounded (closure B)))"
    using True bounded_subset closure_subset by auto
  then have "hausdorff_distance (closure A) (closure B) = 0"
    unfolding hausdorff_distance_def by auto
  then show ?thesis using * by simp
next
  case False
  then have H: "A \<noteq> {}" "B \<noteq> {}" "bounded A" "bounded B" by auto
  then have H2: "closure A \<noteq> {}" "closure B \<noteq> {}" "bounded (closure A)" "bounded (closure B)"
    by auto
  have "hausdorff_distance A B \<le> hausdorff_distance A (closure A) + hausdorff_distance (closure A) B"
    apply (rule hausdorff_distance_triangle) using H H2 by auto
  also have "... = hausdorff_distance (closure A) B"
    using hausdorff_distance_closure by auto
  also have "... \<le> hausdorff_distance (closure A) (closure B) + hausdorff_distance (closure B) B"
    apply (rule hausdorff_distance_triangle) using H H2 by auto
  also have "... = hausdorff_distance (closure A) (closure B)"
    using hausdorff_distance_closure by (auto simp add: hausdorff_distance_sym)
  finally have *: "hausdorff_distance A B \<le> hausdorff_distance (closure A) (closure B)" by simp

  have "hausdorff_distance (closure A) (closure B) \<le> hausdorff_distance (closure A) A + hausdorff_distance A (closure B)"
    apply (rule hausdorff_distance_triangle) using H H2 by auto
  also have "... = hausdorff_distance A (closure B)"
    using hausdorff_distance_closure by (auto simp add: hausdorff_distance_sym)
  also have "... \<le> hausdorff_distance A B + hausdorff_distance B (closure B)"
    apply (rule hausdorff_distance_triangle) using H H2 by auto
  also have "... = hausdorff_distance A B"
    using hausdorff_distance_closure by (auto simp add: hausdorff_distance_sym)
  finally have "hausdorff_distance (closure A) (closure B) \<le> hausdorff_distance A B" by simp
  then show ?thesis using * by auto
qed

lemma hausdorff_distance_zero:
  assumes "A \<noteq> {}" "bounded A" "B \<noteq> {}" "bounded B"
  shows "hausdorff_distance A B = 0 \<longleftrightarrow> closure A = closure B"
proof
  assume H: "hausdorff_distance A B = 0"
  have "A \<subseteq> closure B"
  proof
    fix x assume "x \<in> A"
    have "infdist x B = 0"
      using infdist_le_hausdorff_distance[OF \<open>x \<in> A\<close> \<open>bounded A\<close> \<open>bounded B\<close>] H infdist_nonneg[of x B] by auto
    then show "x \<in> closure B" using in_closure_iff_infdist_zero[OF \<open>B \<noteq> {}\<close>] by auto
  qed
  then have A: "closure A \<subseteq> closure B" by (simp add: closure_minimal)

  have "B \<subseteq> closure A"
  proof
    fix x assume "x \<in> B"
    have "infdist x A = 0"
      using infdist_le_hausdorff_distance[OF \<open>x \<in> B\<close> \<open>bounded B\<close> \<open>bounded A\<close>] H infdist_nonneg[of x A]
      by (auto simp add: hausdorff_distance_sym)
    then show "x \<in> closure A" using in_closure_iff_infdist_zero[OF \<open>A \<noteq> {}\<close>] by auto
  qed
  then have "closure B \<subseteq> closure A" by (simp add: closure_minimal)
  then show "closure A = closure B" using A by auto
next
  assume "closure A = closure B"
  then show "hausdorff_distance A B = 0"
    using hausdorff_distance_closures[of A B] by auto
qed

lemma hausdorff_distance_vimage:
  assumes "\<And>x. x \<in> A \<Longrightarrow> dist (f x) (g x) \<le> C"
          "C \<ge> 0"
  shows "hausdorff_distance (f`A) (g`A) \<le> C"
apply (rule hausdorff_distanceI2[OF _ _ \<open>C \<ge> 0\<close>]) using assms by (auto simp add: dist_commute, auto)

lemma hausdorff_distance_union [mono_intros]:
  assumes "A \<noteq> {}" "B \<noteq> {}" "C \<noteq> {}" "D \<noteq> {}"
  shows "hausdorff_distance (A \<union> B) (C \<union> D) \<le> max (hausdorff_distance A C) (hausdorff_distance B D)"
proof (cases "bounded A \<and> bounded B \<and> bounded C \<and> bounded D")
  case False
  then have "hausdorff_distance (A \<union> B) (C \<union> D) = 0"
    unfolding hausdorff_distance_def by auto
  then show ?thesis
    by (simp add: hausdorff_distance_nonneg le_max_iff_disj)
next
  case True
  show ?thesis
  proof (rule hausdorff_distanceI, auto)
    fix x assume H: "x \<in> A"
    have "infdist x (C \<union> D) \<le> infdist x C"
      by (simp add: assms infdist_union_min)
    also have "... \<le> hausdorff_distance A C"
      apply (rule infdist_le_hausdorff_distance) using H True by auto
    also have "... \<le> max (hausdorff_distance A C) (hausdorff_distance B D)"
      by auto
    finally show "infdist x (C \<union> D) \<le> max (hausdorff_distance A C) (hausdorff_distance B D)"
      by simp
  next
    fix x assume H: "x \<in> B"
    have "infdist x (C \<union> D) \<le> infdist x D"
      by (simp add: assms infdist_union_min)
    also have "... \<le> hausdorff_distance B D"
      apply (rule infdist_le_hausdorff_distance) using H True by auto
    also have "... \<le> max (hausdorff_distance A C) (hausdorff_distance B D)"
      by auto
    finally show "infdist x (C \<union> D) \<le> max (hausdorff_distance A C) (hausdorff_distance B D)"
      by simp
  next
    fix x assume H: "x \<in> C"
    have "infdist x (A \<union> B) \<le> infdist x A"
      by (simp add: assms infdist_union_min)
    also have "... \<le> hausdorff_distance C A"
      apply (rule infdist_le_hausdorff_distance) using H True by auto
    also have "... \<le> max (hausdorff_distance A C) (hausdorff_distance B D)"
      using hausdorff_distance_sym[of A C] by auto
    finally show "infdist x (A \<union> B) \<le> max (hausdorff_distance A C) (hausdorff_distance B D)"
      by simp
  next
    fix x assume H: "x \<in> D"
    have "infdist x (A \<union> B) \<le> infdist x B"
      by (simp add: assms infdist_union_min)
    also have "... \<le> hausdorff_distance D B"
      apply (rule infdist_le_hausdorff_distance) using H True by auto
    also have "... \<le> max (hausdorff_distance A C) (hausdorff_distance B D)"
      using hausdorff_distance_sym[of B D] by auto
    finally show "infdist x (A \<union> B) \<le> max (hausdorff_distance A C) (hausdorff_distance B D)"
      by simp
  qed (simp add: le_max_iff_disj)
qed

end (*of theory Hausdorff_Distance*)
