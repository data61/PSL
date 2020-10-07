(*  
    Title:      Least_Squares_Approximation.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Least Squares Approximation\<close>

theory Least_Squares_Approximation
imports
 QR_Decomposition
begin

subsection\<open>Second part of the Fundamental Theorem of Linear Algebra\<close>

text\<open>See @{url "http://en.wikipedia.org/wiki/Fundamental_theorem_of_linear_algebra"}\<close>

lemma null_space_orthogonal_complement_row_space:
  fixes A::"real^'cols^'rows::{finite,wellorder}"
  shows "null_space A = orthogonal_complement (row_space A)"
proof (unfold null_space_def orthogonal_complement_def, auto)
  fix x xa assume Ax: "A *v x = 0" and xa: "xa \<in> row_space A"
  obtain y where y: "xa = transpose A *v y" using xa unfolding row_space_eq by blast
  have "y v* A = xa"
    using transpose_vector y by fastforce
  thus "orthogonal x xa" unfolding orthogonal_def
    using Ax dot_lmul_matrix inner_commute inner_zero_right
    by (metis Ax dot_lmul_matrix inner_commute inner_zero_right)
next
  fix x assume xa: "\<forall>xa\<in>row_space A. orthogonal x xa"
  show "A *v x = 0"
    using xa unfolding row_space_eq orthogonal_def
    by (auto, metis transpose_transpose dot_lmul_matrix inner_eq_zero_iff transpose_vector)
qed

lemma left_null_space_orthogonal_complement_col_space:
  fixes A::"real^'cols::{finite,wellorder}^'rows"
  shows "left_null_space A = orthogonal_complement (col_space A)"
  using null_space_orthogonal_complement_row_space[of "transpose A"]
  unfolding left_null_space_eq_null_space_transpose
  unfolding col_space_eq_row_space_transpose .


subsection\<open>Least Squares Approximation\<close>

text\<open>See @{url "https://people.math.osu.edu/husen.1/teaching/571/least_squares.pdf"}\<close>

text\<open>Part 3 of the Theorem 1.7 in the previous website.\<close>

lemma least_squares_approximation:
  fixes X::"'a::{euclidean_space} set"
  assumes subspace_S: "subspace S"
  and ind_X: "independent X"
  and X: "X \<subseteq> S"
  and span_X: "S \<subseteq> span X"
  and o: "pairwise orthogonal X"
  and not_eq: "proj_onto v X \<noteq> y"
  and y: "y \<in> S"
  shows "norm (v - proj_onto v X) < norm (v - y)"
proof -
  have S_eq_spanX: "S = span X"
    using X span_X span_subspace subspace_S by auto
  let ?p="proj_onto v X"
  have not_0: "(norm(?p - y))^2 \<noteq> 0"
    by (metis (lifting) eq_iff_diff_eq_0 norm_eq_zero not_eq power_eq_0_iff)
  have "norm (v-y)^2 = norm (v - ?p + ?p - y)^2" by auto
  also have "... = norm ((v - ?p) + (?p - y))^2" 
    unfolding add.assoc[symmetric] by simp
  also have "... = (norm (v - ?p))^2 + (norm(?p - y))^2"
  proof (rule phytagorean_theorem_norm, rule in_orthogonal_complement_imp_orthogonal) 
    show "?p - y \<in> S" unfolding proj_onto_def proj_def[abs_def]
    proof (rule subspace_diff[OF subspace_S _ y],
        rule subspace_sum[OF subspace_S])
      show "x \<in> X \<Longrightarrow> (v \<bullet> x / (x \<bullet> x)) *\<^sub>R x \<in> S" for x
        by (metis S_eq_spanX X rev_subsetD span_mul)
    qed
    show "v - ?p \<in> orthogonal_complement S"
      using v_minus_p_orthogonal_complement assms by auto        
  qed
  finally have "norm (v-?p)^2 < norm (v-y)^2" using not_0 by fastforce
  thus ?thesis by (metis (full_types) norm_gt_square power2_norm_eq_inner)
qed


lemma least_squares_approximation2:
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "subspace S"
  and y: "y \<in> S"
  shows "\<exists>p\<in>S. norm (v - p) \<le> norm (v - y) \<and> (v-p) \<in> orthogonal_complement S"
proof -
  obtain X where  ind_X: "independent X"
    and X: "X \<subseteq> S"
    and span_X: "S \<subseteq> span X"
    and o: "pairwise orthogonal X"
    by (metis order_refl orthonormal_basis_subspace subspace_S)
  let ?p="proj_onto v X"
  show ?thesis 
  proof (rule bexI[of _ ?p], rule conjI)
    show "norm (v - proj_onto v X) \<le> norm (v - y)"
    proof (cases "?p=y")
      case True thus "norm (v - ?p) \<le> norm (v - y)" by simp
    next
      case False
      have "norm (v - ?p) < norm (v - y)" 
        by (rule least_squares_approximation[OF subspace_S ind_X X span_X o False y])
      thus "norm (v - ?p) \<le> norm (v - y)" by simp
    qed
    show "?p \<in> S"
      using [[unfold_abs_def = false]]
    proof (unfold proj_onto_def proj_def, rule subspace_sum)
      show "subspace S" using subspace_S .
      show "x\<in>X \<Longrightarrow> proj v x \<in> S" for x
        by (simp add: proj_def X rev_subsetD subspace_S subspace_mul)
    qed
    show "v - ?p\<in> orthogonal_complement S"
      by (rule v_minus_p_orthogonal_complement[OF subspace_S ind_X X span_X o])
  qed
qed

corollary least_squares_approximation3:
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "subspace S"
  shows "\<exists>p\<in>S. \<forall>y\<in>S. norm (v - p) \<le> norm (v - y) \<and> (v-p) \<in> orthogonal_complement S"
proof -
  obtain X where  ind_X: "independent X"
    and X: "X \<subseteq> S"
    and span_X: "S \<subseteq> span X"
    and o: "pairwise orthogonal X"
    by (metis order_refl orthonormal_basis_subspace subspace_S)
  let ?p="proj_onto v X"
  show ?thesis
  proof (rule bexI[of _ ?p], auto)
    fix y assume y: "y\<in>S"
    show "norm (v - ?p) \<le> norm (v - y)"
    proof (cases "?p=y")
      case True thus ?thesis by simp
    next
      case False
      have "norm (v - ?p) < norm (v - y)"
        by (rule least_squares_approximation[OF subspace_S ind_X X span_X o False y])
      thus ?thesis by simp
    qed
    show "v - ?p \<in> orthogonal_complement S"
      by (rule v_minus_p_orthogonal_complement[OF subspace_S ind_X X span_X o])
  next
    show "?p \<in> S" 
    proof (unfold proj_onto_def, rule subspace_sum)
      show "subspace S" using subspace_S .
      show "x \<in> X \<Longrightarrow> proj v x \<in> S" for x
        by (metis Projections.proj_def X subset_iff subspace_S subspace_mul)
    qed
  qed
qed

lemma norm_least_squares:
  fixes A::"real^'cols::{finite,wellorder}^'rows"
  shows "\<exists>x. \<forall>x'. norm (b - A *v x) \<le> norm (b - A *v x')"
proof -
  have "\<exists>p\<in>col_space A. \<forall>y\<in>col_space A. norm (b - p) \<le> norm (b - y) \<and> (b-p) \<in> orthogonal_complement (col_space A)"
    using least_squares_approximation3[OF subspace_col_space[of A, unfolded subspace_vec_eq]] .
  from this obtain p where p: "p \<in> col_space A" and least: "\<forall>y\<in>col_space A. norm (b - p) \<le> norm (b - y)"
    and bp_orthogonal: "(b-p) \<in> orthogonal_complement (col_space A)"
    by blast
  obtain x where x: "p = A *v x" using p unfolding col_space_eq by blast
  show ?thesis 
  proof (rule exI[of _ x], auto)
    fix x'
    have "A *v x' \<in> col_space A" unfolding col_space_eq by auto
    thus "norm (b - A *v x) \<le> norm (b - A *v x')" using least unfolding x by auto
  qed
qed

definition "set_least_squares_approximation A b = {x. \<forall>y. norm (b - A *v x) \<le> norm (b - A *v y)}"

corollary least_squares_approximation4:
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "subspace S"
  shows "\<exists>!p\<in>S. \<forall>y\<in>S-{p}. norm (v - p) < norm (v - y)"
proof (auto)
  obtain X where  ind_X: "independent X"
    and X: "X \<subseteq> S"
    and span_X: "S \<subseteq> span X"
    and o: "pairwise orthogonal X"
    by (metis order_refl orthonormal_basis_subspace subspace_S)
  let ?p="sum (proj v) X"
  show "\<exists>p. p \<in> S \<and> (\<forall>y\<in>S - {p}. norm (v - p) < norm (v - y))"
  proof (rule exI[of _ ?p], rule conjI,  rule subspace_sum)
    show "subspace S" using subspace_S .
    show "x \<in> X \<Longrightarrow> proj v x \<in> S" for x
      by (metis Projections.proj_def X subset_iff subspace_S subspace_mul)
    show "\<forall>y\<in>S - {?p}. norm (v - ?p) < norm (v - y)" 
      using X ind_X least_squares_approximation  o span_X subspace_S proj_onto_def
      by (metis (mono_tags) Diff_iff singletonI)
  qed
  fix p y
  assume p: "p \<in> S"
    and "\<forall>y\<in>S - {p}. norm (v - p) < norm (v - y)"
    and "y \<in> S"
    and "\<forall>ya\<in>S - {y}. norm (v - y) < norm (v - ya)"
  thus "p = y" by (metis member_remove not_less_iff_gr_or_eq remove_def)
qed


corollary least_squares_approximation4':
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "subspace S"
  shows "\<exists>!p\<in>S. \<forall>y\<in>S. norm (v - p) \<le> norm (v - y)"
proof (auto)
  obtain X where ind_X: "independent X"
    and X: "X \<subseteq> S"
    and span_X: "S \<subseteq> span X"
    and o: "pairwise orthogonal X"
    by (metis order_refl orthonormal_basis_subspace subspace_S)
  let ?p="sum (proj v) X"
  show "\<exists>p. p \<in> S \<and> (\<forall>y\<in>S. norm (v - p) \<le> norm (v - y))"
  proof (rule exI[of _ ?p], rule conjI, rule subspace_sum)
    show "subspace S" using subspace_S .
    show "x \<in> X \<Longrightarrow> proj v x \<in> S" for x
      by (metis Projections.proj_def X subset_iff subspace_S subspace_mul)
    show "\<forall>y\<in>S. norm (v - ?p) \<le> norm (v - y)"
      by (metis (mono_tags) proj_onto_def X dual_order.refl ind_X 
         least_squares_approximation less_imp_le o span_X subspace_S)
  qed
  fix p y
  assume p: "p \<in> S" and p': "\<forall>y\<in>S. norm (v - p) \<le> norm (v - y)"
    and y: "y \<in> S" and y': "\<forall>ya\<in>S. norm (v - y) \<le> norm (v - ya)"
  obtain a where a: "a\<in>S" and a': "\<forall>y\<in>S-{a}. norm (v - a) < norm (v - y)"
    and a_uniq: "\<forall>b. (b\<in>S \<and> (\<forall>c\<in>S-{b}. norm (v - b) < norm (v - c))) \<longrightarrow> b=a"
    using least_squares_approximation4[OF subspace_S]
    by metis
  have "p=a" using p p' a_uniq leD  by (metis a a' member_remove remove_def)
  moreover have "y=a" using y y' a_uniq
    by (metis a a' leD member_remove remove_def)
  ultimately show "p = y" by simp
qed

corollary least_squares_approximation5:
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "subspace S"
  shows "\<exists>!p\<in>S. \<forall>y\<in>S-{p}. norm (v - p) < norm (v - y) \<and> v-p \<in> orthogonal_complement S"
proof (auto)
  obtain X where  ind_X: "independent X"
    and X: "X \<subseteq> S"
    and span_X: "S \<subseteq> span X"
    and o: "pairwise orthogonal X"
    by (metis order_refl orthonormal_basis_subspace subspace_S)
  let ?p="sum (proj v) X"
  show "\<exists>p. p \<in> S \<and> (\<forall>y\<in>S - {p}. norm (v - p) < norm (v - y) \<and> v - p \<in> orthogonal_complement S)"
  proof (rule exI[of _ ?p], rule conjI, rule subspace_sum)
    show "subspace S" using subspace_S .
    show "x \<in> X \<Longrightarrow> proj v x \<in> S" for x
      by (simp add: Projections.proj_def X rev_subsetD subspace_S subspace_mul)
    have "\<forall>y\<in>S - {?p}. norm (v - ?p) < norm (v - y)" 
      using least_squares_approximation[OF subspace_S ind_X X span_X o]
      unfolding proj_onto_def
      by (metis (no_types) member_remove remove_def)
    moreover have "v - ?p \<in> orthogonal_complement S" 
      by (metis (no_types) X ind_X o span_X subspace_S v_minus_p_orthogonal_complement proj_onto_def)
    ultimately show "\<forall>y\<in>S - {?p}. norm (v - ?p) < norm (v - y) \<and> v - ?p \<in> orthogonal_complement S"
      by auto
  qed
  fix p y
  assume p: "p \<in> S" and p': "\<forall>y\<in>S - {p}. norm (v - p) < norm (v - y) \<and> v - p \<in> orthogonal_complement S"
    and y: "y \<in> S" and y': "\<forall>ya\<in>S - {y}. norm (v - y) < norm (v - ya) \<and> v - y \<in> orthogonal_complement S"
  show "p=y"
    by (metis least_squares_approximation4 p p' subspace_S y y')
qed

corollary least_squares_approximation5':
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "subspace S"
  shows "\<exists>!p\<in>S. \<forall>y\<in>S. norm (v - p) \<le> norm (v - y) \<and> v-p \<in> orthogonal_complement S"
  by (metis least_squares_approximation3 least_squares_approximation4' subspace_S)

corollary least_squares_approximation6:
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "subspace S"
  and "p\<in>S"
  and "\<forall>y\<in>S. norm (v - p) \<le> norm (v - y)"
  shows "v-p \<in> orthogonal_complement S"
proof -
  obtain a where a: "a\<in>S" and a': "\<forall>y\<in>S. norm (v - a) \<le> norm (v - y) \<and> v-a \<in> orthogonal_complement S"
    and "\<forall>b. (b\<in>S \<and> (\<forall>y\<in>S. norm (v - b) \<le> norm (v - y) \<and> v-b \<in> orthogonal_complement S)) \<longrightarrow> b=a"
    using least_squares_approximation5'[OF subspace_S] by metis
  have "p=a"
    by (metis a a' assms(2) assms(3) least_squares_approximation4' subspace_S)
  thus ?thesis using a' by (metis assms(2))
qed


corollary least_squares_approximation7:
  fixes S::"'a::{euclidean_space} set"
  assumes subspace_S: "subspace S"
  and "v - p \<in> orthogonal_complement S"
  and "p\<in>S"
  and "y \<in> S"
  shows "norm (v - p) \<le> norm (v - y)" 
proof (cases "y=p")
  case True thus ?thesis by simp
next
  case False
  have "norm (v - y)^2 = norm ((v - p) + (p - y))^2"
    by (metis (hide_lams, no_types) add_diff_cancel_left add_ac(1) add_diff_add add_diff_cancel)
  also have "... = norm (v - p)^2 + norm (p - y)^2" 
  proof (rule phytagorean_theorem_norm, rule in_orthogonal_complement_imp_orthogonal)
    show "p - y \<in> S" by (metis assms(3) assms(4) subspace_S subspace_diff)
    show "v - p \<in> orthogonal_complement S" by (metis assms(2)) 
  qed
  finally have "norm (v - p)^2 \<le> norm (v - y)^2" by auto
  thus "norm (v - p)\<le> norm (v - y)" by (metis norm_ge_zero power2_le_imp_le)
qed


lemma in_set_least_squares_approximation:
  fixes A::"real^'cols::{finite, wellorder}^'rows"
  assumes o: "A *v x - b \<in> orthogonal_complement (col_space A)"
  shows "(x \<in> set_least_squares_approximation A b)"
proof (unfold set_least_squares_approximation_def, auto)
  fix y 
  show " norm (b - A *v x) \<le> norm (b - A *v y)"
  proof (rule least_squares_approximation7)
    show "subspace (col_space A)" using subspace_col_space[of A, unfolded subspace_vec_eq] .
    show "b - A *v x \<in> orthogonal_complement (col_space A)"
      using o subspace_orthogonal_complement[of "(col_space A)"]
      using minus_diff_eq subspace_neg by metis
    show "A *v x \<in> col_space A" unfolding col_space_eq[of A] by auto
    show "A *v y \<in> col_space A" unfolding col_space_eq by auto
  qed
qed

lemma in_set_least_squares_approximation_eq:
  fixes A::"real^'cols::{finite,wellorder}^'rows"
  shows "(x \<in> set_least_squares_approximation A b) = (transpose A ** A *v x = transpose A *v b)"
proof
  assume x: "x \<in> set_least_squares_approximation A b"
  hence a: "\<forall>a. norm (b - A *v x) \<le> norm (b - A *v a)" unfolding set_least_squares_approximation_def by simp
  have "b - A *v x \<in> orthogonal_complement (col_space A)"
  proof (rule least_squares_approximation6)
    show "subspace (col_space A)" using subspace_col_space[of A, unfolded subspace_vec_eq] .
    show "A *v x \<in> col_space A" unfolding col_space_eq[of A] by auto
    show "\<forall>y\<in>col_space A. norm (b - A *v x) \<le> norm (b - y)" using a unfolding col_space_eq by auto
  qed
  hence "b - A *v x \<in> null_space (transpose A)"
    unfolding null_space_orthogonal_complement_row_space
    unfolding col_space_eq_row_space_transpose .
  hence "transpose A *v (b - A *v x) = 0" unfolding null_space_def by simp
  thus "(transpose A ** A) *v x = (transpose A) *v b"
    by (metis eq_iff_diff_eq_0 matrix_vector_mul_assoc matrix_vector_right_distrib_minus)
next
  assume "transpose A ** A *v x = transpose A *v b"
  hence "(transpose A) *v (A *v x - b) = 0" 
    by (metis diff_self matrix_vector_mul_assoc matrix_vector_right_distrib_minus)
  hence "(A *v x - b) \<in> null_space (transpose A)" unfolding null_space_def by simp
  hence "(A *v x - b) \<in> orthogonal_complement (col_space A)" 
    by (metis left_null_space_eq_null_space_transpose left_null_space_orthogonal_complement_col_space)
  thus "x \<in> set_least_squares_approximation A b" by (rule in_set_least_squares_approximation)
qed


lemma in_set_least_squares_approximation_eq_full_rank:
  fixes A::"real^'cols::mod_type^'rows::mod_type"
  assumes r: "rank A = ncols A"
  shows "(x \<in> set_least_squares_approximation A b) = (x = matrix_inv (transpose A ** A)**transpose A *v b)"
proof -
  have int_tA: "invertible (transpose A ** A)" using invertible_transpose_mult[OF r] .
  show ?thesis
  proof 
    fix x assume "x \<in> set_least_squares_approximation A b"
    hence "transpose A ** A *v x = transpose A *v b" using in_set_least_squares_approximation_eq by auto
    thus "x = matrix_inv (transpose A ** A) ** transpose A *v b"
      by (metis int_tA matrix_inv_left matrix_vector_mul_assoc matrix_vector_mul_lid)
  next
    fix x assume "x = matrix_inv (transpose A ** A) ** transpose A *v b"
    hence "transpose A ** A *v x = transpose A *v b"
      by (metis int_tA matrix_inv_right matrix_vector_mul_assoc matrix_vector_mul_lid)
    thus "x \<in> set_least_squares_approximation A b" unfolding in_set_least_squares_approximation_eq .
  qed
qed



lemma in_set_least_squares_approximation_eq_full_rank_QR:
  fixes A::"real^'cols::{mod_type}^'rows::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "(x \<in> set_least_squares_approximation A b) = ((snd (QR_decomposition A)) *v x = transpose (fst (QR_decomposition A)) *v b)"
proof -
  let ?Q = "fst (QR_decomposition A)"
  let ?R = "snd (QR_decomposition A)"
  have inv_tR: "invertible (transpose ?R)"
    by (metis invertible_snd_QR_decomposition invertible_transpose r)
  have inv_inv_tR: "invertible (matrix_inv (transpose ?R))"
    by (metis inv_tR invertible_fst_Gauss_Jordan_PA matrix_inv_Gauss_Jordan_PA)
  have "(x \<in> set_least_squares_approximation A b) = (transpose A ** A *v x = transpose A *v b)"
    using in_set_least_squares_approximation_eq .
  also have "... = (transpose (?Q ** ?R) ** (?Q ** ?R) *v x = transpose (?Q ** ?R) *v b)"
    using QR_decomposition_mult[OF r] by simp
  also have "... = (transpose ?R ** transpose ?Q **  (?Q ** ?R) *v x  = transpose ?R ** transpose ?Q *v b)"
    by (metis (hide_lams, no_types) matrix_transpose_mul)
  also have "... = (transpose ?R *v (transpose ?Q ** (?Q ** ?R) *v x)  = transpose ?R *v (transpose ?Q *v b))"
    by (metis (hide_lams, no_types) matrix_vector_mul_assoc)
  also have "... = (matrix_inv (transpose ?R) *v (transpose ?R *v (transpose ?Q ** (?Q ** ?R) *v x))  
    = matrix_inv (transpose ?R) *v (transpose ?R *v (transpose ?Q *v b)))"
    using inv_matrix_vector_mul_left[OF inv_inv_tR] by auto
  also have "... = ((matrix_inv (transpose ?R) ** transpose ?R) *v (transpose ?Q ** (?Q ** ?R) *v x)  
    = (matrix_inv (transpose ?R) ** transpose ?R) *v (transpose ?Q *v b))"
    by (metis (hide_lams, no_types) matrix_vector_mul_assoc)
  also have "... = (transpose ?Q ** (?Q ** ?R) *v x = transpose ?Q *v b)"
    unfolding matrix_inv_left[OF inv_tR]
    unfolding matrix_vector_mul_lid ..
  also have "... = ((transpose ?Q ** ?Q) ** ?R *v x = transpose ?Q *v b)"
    by (metis (hide_lams, no_types) matrix_mul_assoc)
  also have "... = (?R *v x = transpose ?Q *v b)"
    unfolding orthogonal_matrix_fst_QR_decomposition[OF r]
    unfolding matrix_mul_lid ..
  finally show "(x \<in> set_least_squares_approximation A b) = (?R *v x = (transpose ?Q) *v b)" .
qed

(*TODO: Maybe demonstrate that in this case there's only one solution.*)
corollary in_set_least_squares_approximation_eq_full_rank_QR2:
  fixes A::"real^'cols::{mod_type}^'rows::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "(x \<in> set_least_squares_approximation A b) = (x = matrix_inv (snd (QR_decomposition A)) ** transpose (fst (QR_decomposition A)) *v b)"
proof -
  let ?Q = "fst (QR_decomposition A)"
  let ?R = "snd (QR_decomposition A)"
  have inv_R: "invertible ?R" by (metis invertible_snd_QR_decomposition r)
  have "(x \<in> set_least_squares_approximation A b) = (?R *v x = transpose ?Q *v b)"
    using in_set_least_squares_approximation_eq_full_rank_QR[OF r] .
  also have "... = (matrix_inv ?R ** ?R *v x = matrix_inv ?R ** transpose ?Q *v b)"
    by (metis (hide_lams, no_types) Gauss_Jordan_PA_eq calculation fst_Gauss_Jordan_PA inv_R 
      inv_matrix_vector_mul_left invertible_fst_Gauss_Jordan_PA matrix_inv_Gauss matrix_vector_mul_assoc)
  also have "... = (x = matrix_inv ?R ** transpose ?Q *v b)"
    by (metis inv_R matrix_inv_left matrix_vector_mul_lid)
  finally show "(x \<in> set_least_squares_approximation A b) = (x = matrix_inv ?R ** transpose ?Q *v b)" .
qed

lemma set_least_squares_approximation_unique_solution:
  fixes A::"real^'cols::{mod_type}^'rows::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "(set_least_squares_approximation A b) = {matrix_inv (transpose A ** A)**transpose A *v b}"
  by (metis (hide_lams, mono_tags) empty_iff in_set_least_squares_approximation_eq_full_rank
    empty_iff insertI1 r subsetI subset_singletonD)

lemma set_least_squares_approximation_unique_solution_QR:
  fixes A::"real^'cols::{mod_type}^'rows::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "(set_least_squares_approximation A b) = {matrix_inv (snd (QR_decomposition A)) ** transpose (fst (QR_decomposition A)) *v b}"
  by (metis (hide_lams, mono_tags) empty_iff in_set_least_squares_approximation_eq_full_rank_QR2 insertI1 r subsetI subset_singletonD)

end
