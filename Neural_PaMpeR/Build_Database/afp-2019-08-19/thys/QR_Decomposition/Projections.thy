(*  
    Title:      Projections.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Projections\<close>

theory Projections
imports 
  Miscellaneous_QR
begin

subsection\<open>Definitions of vector projection and projection of a vector onto a set.\<close>

definition "proj v u = (v \<bullet> u / (u \<bullet> u)) *\<^sub>R u"

definition "proj_onto a S = (sum (\<lambda>x. proj a x) S)"

subsection\<open>Properties\<close>

lemma proj_onto_sum_rw: 
  "sum (\<lambda>x. (x \<bullet> v / (x \<bullet> x)) *\<^sub>R x) A = sum (\<lambda>x. (v \<bullet> x / (x \<bullet> x)) *\<^sub>R x) A"
  by (rule sum.cong, auto simp add: inner_commute)

lemma vector_sub_project_orthogonal_proj:
  fixes b x :: "'a::euclidean_space"
  shows "inner b (x - proj x b) = 0"
  using vector_sub_project_orthogonal
  unfolding proj_def inner_commute[of x b]
  by auto

lemma orthogonal_proj_set:
  assumes yC: "y\<in>C" and C: "finite C" and p: "pairwise orthogonal C"
  shows "orthogonal (a - proj_onto a C) y"
proof -
  have Cy: "C = insert y (C - {y})" using yC
    by blast
  have fth: "finite (C - {y})"
    using C by simp
  show "orthogonal (a - proj_onto a C) y"
    unfolding orthogonal_def unfolding proj_onto_def unfolding proj_def[abs_def]
    unfolding inner_diff
    unfolding inner_sum_left 
    unfolding right_minus_eq
    unfolding sum.remove[OF C yC]
    apply (clarsimp simp add: inner_commute[of y a])
    apply (rule sum.neutral)
    apply clarsimp
    apply (rule p[unfolded pairwise_def orthogonal_def, rule_format])
    using yC by auto
qed


lemma pairwise_orthogonal_proj_set:
  assumes C: "finite C" and p: "pairwise orthogonal C"
  shows "pairwise orthogonal (insert (a - proj_onto a C) C)"
  by (rule pairwise_orthogonal_insert[OF p], auto simp add: orthogonal_proj_set C p)

subsection\<open>Orthogonal Complement\<close>

definition "orthogonal_complement W = {x. \<forall>y \<in> W. orthogonal x y}"

lemma in_orthogonal_complement_imp_orthogonal:
  assumes x: "y \<in> S"
  and "x \<in> orthogonal_complement S"
  shows "orthogonal x y" 
  using assms orthogonal_commute 
  unfolding orthogonal_complement_def 
  by blast

lemma subspace_orthogonal_complement: "subspace (orthogonal_complement W)"
  unfolding subspace_def orthogonal_complement_def
  by (simp add: orthogonal_def inner_left_distrib)

lemma orthogonal_complement_mono:
  assumes A_in_B: "A \<subseteq> B"
  shows "orthogonal_complement B \<subseteq> orthogonal_complement A"
proof
  fix x assume x: "x \<in> orthogonal_complement B"
  show "x \<in> orthogonal_complement A" using x unfolding orthogonal_complement_def
    by (simp add: orthogonal_def, metis A_in_B in_mono)
qed

lemma B_in_orthogonal_complement_of_orthogonal_complement:
  shows "B \<subseteq> orthogonal_complement (orthogonal_complement B)"
  by (auto simp add: orthogonal_complement_def orthogonal_def inner_commute)


lemma phytagorean_theorem_norm:
  assumes o: "orthogonal x y"
  shows "norm (x+y)^2=norm x^2 + norm y^2"
proof -
  have "norm (x+y)^2 = (x+y) \<bullet> (x+y)" unfolding power2_norm_eq_inner ..
  also have "... = ((x+y) \<bullet> x) + ((x+y) \<bullet> y)" unfolding inner_right_distrib ..
  also have "... = (x \<bullet> x) + (x \<bullet> y) + (y \<bullet> x) + (y \<bullet> y) "
    unfolding real_inner_class.inner_add_left by simp
  also have "... = (x \<bullet> x) + (y \<bullet> y)" using o unfolding orthogonal_def 
    by (metis monoid_add_class.add.right_neutral inner_commute)
  also have "... = norm x^2 + norm y^2" unfolding power2_norm_eq_inner ..
  finally show ?thesis .
qed

lemma in_orthogonal_complement_basis:
  fixes B::"'a::{euclidean_space} set"
  assumes S: "subspace S"
  and ind_B: "independent B"
  and B: "B \<subseteq> S"
  and span_B: "S \<subseteq> span B"
  shows "(v \<in> orthogonal_complement S) = (\<forall>a\<in>B. orthogonal a v)" 
proof (unfold orthogonal_complement_def, auto)
  fix a assume "\<forall>x\<in>S. orthogonal v x" and "a \<in> B"  
  thus "orthogonal a v" 
    by (metis B orthogonal_commute rev_subsetD)
next
  fix x assume o: "\<forall>a\<in>B. orthogonal a v" and x: "x \<in> S"
  have finite_B: "finite B" using independent_bound_general[OF ind_B] ..
  have span_B_eq: "S = span B" using B S span_B span_subspace by blast
  obtain f where f: "(\<Sum>a\<in>B. f a *\<^sub>R a) = x" using span_finite[OF finite_B]
    using x unfolding span_B_eq by force
  have "v \<bullet> x = v \<bullet> (\<Sum>a\<in>B. f a *\<^sub>R a)" unfolding f ..
  also have "... = (\<Sum>a\<in>B. v \<bullet> (f a *\<^sub>R a))" unfolding inner_sum_right ..
  also have "... = (\<Sum>a\<in>B. f a * (v \<bullet> a))" unfolding inner_scaleR_right ..
  also have "... = 0" using sum.neutral o by (simp add: orthogonal_def inner_commute)
  finally show "orthogonal v x" unfolding orthogonal_def .
qed


text\<open>See @{url "https://people.math.osu.edu/husen.1/teaching/571/least_squares.pdf"}\<close>

text\<open>Part 1 of the Theorem 1.7 in the previous website, but the proof has been carried out
  in other way.\<close>

lemma v_minus_p_orthogonal_complement:
  fixes X::"'a::{euclidean_space} set"
  assumes subspace_S: "subspace S"
  and ind_X: "independent X"
  and X: "X \<subseteq> S"
  and span_X: "S \<subseteq> span X"
  and o: "pairwise orthogonal X"
  shows "(v - proj_onto v X) \<in> orthogonal_complement S"
  unfolding in_orthogonal_complement_basis[OF subspace_S ind_X X span_X]
proof 
  fix a assume a: "a \<in> X"
  let ?p="proj_onto v X"
  show "orthogonal a (v - ?p)"
    unfolding orthogonal_commute[of a "v-?p"]
    by (rule orthogonal_proj_set[OF a _ o])
       (simp add: independent_bound_general[OF ind_X])
qed

text\<open>Part 2 of the Theorem 1.7 in the previous website.\<close>

lemma UNIV_orthogonal_complement_decomposition:
  fixes S::"'a::{euclidean_space} set"
  assumes s: "subspace S"
  shows "UNIV = S + (orthogonal_complement S)"
proof (unfold set_plus_def, auto)
  fix v
  obtain X where ind_X: "independent X"
    and X: "X \<subseteq> S"
    and span_X: "S \<subseteq> span X"
    and o: "pairwise orthogonal X"
    by (metis order_refl orthonormal_basis_subspace s)
  have finite_X: "finite X" by (metis independent_bound_general ind_X)
  let ?p="proj_onto v X"
  have "v=?p +(v-?p)" by simp
  moreover have "?p \<in> S" unfolding proj_onto_def proj_def[abs_def]
    by (rule subspace_sum[OF s])
      (simp add: X s rev_subsetD subspace_mul)
  moreover have "(v-?p) \<in> orthogonal_complement S"
    by (rule v_minus_p_orthogonal_complement[OF s ind_X X span_X o])
  ultimately show "\<exists>a\<in>S. \<exists>b\<in>orthogonal_complement S. v = a + b" by force
qed

subsection\<open>Normalization of vectors\<close>

definition normalize
  where "normalize x  = ((1/norm x) *\<^sub>R x)"
definition normalize_set_of_vec
  where "normalize_set_of_vec X  = normalize` X"

lemma norm_normalize:
  assumes "x \<noteq> 0"
  shows "norm (normalize x) = 1"
  by (simp add: normalize_def assms)

lemma normalize_0: "(normalize x = 0) = (x = 0)"
  unfolding normalize_def by auto

lemma norm_normalize_set_of_vec:
  assumes "x \<noteq> 0"
  and "x \<in> normalize_set_of_vec X"
  shows "norm x = 1" 
  using assms norm_normalize normalize_0 unfolding normalize_set_of_vec_def  by blast

end
