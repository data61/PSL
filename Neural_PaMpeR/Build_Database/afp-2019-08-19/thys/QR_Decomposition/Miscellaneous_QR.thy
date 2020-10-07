(*  
    Title:      Miscellaneous_QR.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Miscellaneous file for the QR algorithm\<close>

theory Miscellaneous_QR
imports
 Gauss_Jordan.Examples_Gauss_Jordan_Abstract
begin


text\<open>These two lemmas maybe should be in the file \<open>Code_Matrix.thy\<close> of the Gauss-Jordan
  development.\<close>

lemma [code abstract]: "vec_nth (a - b) =  (%i. a$i - b$i)" by (metis vector_minus_component)
lemma [code abstract]: "vec_nth (c *\<^sub>R x) = (\<lambda>i. c *\<^sub>R (x$i))" by auto


text\<open>This lemma maybe should be in the file \<open>Mod_Type.thy\<close> of the Gauss-Jordan
  development.\<close>

lemma from_nat_le:
  fixes i::"'a::{mod_type}"
  assumes i: "to_nat i< k"
  and k: "k<CARD('a)"
  shows "i < from_nat k"
  by (metis (full_types) from_nat_mono from_nat_to_nat_id i k)

text\<open>Some properties about orthogonal matrices.\<close>

lemma orthogonal_mult:
  assumes "orthogonal a b"
  shows "orthogonal (x *\<^sub>R a) (y *\<^sub>R b)"
  using assms unfolding orthogonal_def by simp

lemma orthogonal_matrix_is_orthogonal:
  fixes A::"real^'n^'n"
  assumes o: "orthogonal_matrix A" 
  shows "(pairwise orthogonal (columns A))"
proof (unfold pairwise_def columns_def, auto)
  fix i j 
  assume column_i_not_j: "column i A \<noteq> column j A"
  hence i_not_j: "i \<noteq> j" by auto
  have "0 = (mat 1) $ i $ j" by (metis i_not_j mat_1_fun)
  also have "... = (transpose A ** A) $ i $ j" using o unfolding orthogonal_matrix by simp
  also have "... = row i (transpose A) \<bullet> column j A" unfolding matrix_matrix_mult_inner_mult by simp
  also have "... = column i A \<bullet> column j A" unfolding row_transpose .. 
  finally show "orthogonal (column i A) (column j A)" unfolding orthogonal_def ..
qed

lemma orthogonal_matrix_norm:
  fixes A::"real^'n^'n"
  assumes o: "orthogonal_matrix A" 
  shows "norm (column i A) = 1"
proof -
  have "1 = (transpose A ** A) $ i $ i" using o unfolding orthogonal_matrix by (simp add: mat_1_fun)
  also have "... = (column i A) \<bullet> (column i A)" unfolding matrix_matrix_mult_inner_mult row_transpose ..
  finally show "norm (column i A) = 1" using norm_eq_1 by auto
qed

lemma orthogonal_matrix_card:
  fixes A::"real^'n^'n"
  assumes o: "orthogonal_matrix A" 
  shows "card (columns A) = ncols A"
proof (rule ccontr)
  assume card_not_ncols: "card (columns A) \<noteq> ncols A"
  have "\<exists>i j. column i A = column j A \<and> i\<noteq>j"
  proof (rule ccontr, auto)
    assume col_eq: "\<forall>i j. column i A = column j A \<longrightarrow> i = j"
    have "card (columns A) = card {i. i \<in> (UNIV::'n set)}"
      by (rule bij_betw_same_card[symmetric, of "\<lambda>i. column i A"], 
        auto simp add: bij_betw_def columns_def inj_on_def col_eq)
    also have "... = ncols A" unfolding ncols_def by simp
    finally show False using card_not_ncols by contradiction
  qed
  from this obtain i j where col_eq: "column i A = column j A" and i_not_j: "i \<noteq> j" by auto
  have "0 = (mat 1) $ i $ j" using mat_1_fun i_not_j by metis
  also have "... = (transpose A ** A) $ i $ j" using o unfolding orthogonal_matrix by simp
  also have "... = column i A \<bullet> column j A" unfolding matrix_matrix_mult_inner_mult row_transpose ..
  show False
    by (metis calculation col_eq mat_1_fun matrix_matrix_mult_inner_mult 
      o orthogonal_matrix zero_neq_one)
qed


lemma orthogonal_matrix_intro:        
  fixes A::"real^'n^'n"
  assumes p: "(pairwise orthogonal (columns A))"
  and n: "\<forall>i. norm (column i A) = 1"
  and c: "card (columns A) = ncols A" (*We need that premise to avoid the case that column i A = column j A when i \<noteq> j*)
  shows "orthogonal_matrix A"
proof (unfold orthogonal_matrix vec_eq_iff, clarify, unfold mat_1_fun, auto)
  fix ia 
  have "(transpose A ** A) $ ia $ ia = column ia A \<bullet> column ia A"
    unfolding matrix_matrix_mult_inner_mult unfolding row_transpose ..
  also have "... = 1" using n norm_eq_1 by blast
  finally show "(transpose A ** A) $ ia $ ia = 1" .
  fix i
  assume i_not_ia: "i \<noteq> ia"
  have column_i_not_ia: "column i A \<noteq> column ia A"
  proof (rule ccontr, simp)
    assume col_i_ia: "column i A = column ia A"
    have rw: "(\<lambda>i. column i A)` (UNIV-{ia}) = {column i A|i. i\<noteq>ia}" unfolding columns_def by auto
    have "card (columns A) = card ({column i A|i. i\<noteq>ia})"
      by (rule bij_betw_same_card[of id], unfold bij_betw_def columns_def)
         (auto, metis col_i_ia i_not_ia)
    also have "... = card ((\<lambda>i. column i A)` (UNIV-{ia}))" unfolding rw ..
    also have "... \<le> card (UNIV - {ia})" by (metis card_image_le finite_code)
    also have "... < CARD ('n)" by simp
    finally show False using c unfolding ncols_def by simp
  qed
  hence oia: "orthogonal (column i A) (column ia A)"
    using p unfolding pairwise_def unfolding columns_def by auto
  have "(transpose A ** A) $ i $ ia = column i A \<bullet> column ia A"
    unfolding matrix_matrix_mult_inner_mult unfolding row_transpose ..
  also have "... = 0" using oia unfolding orthogonal_def .
  finally show "(transpose A ** A) $ i $ ia = 0" .
qed


lemma orthogonal_matrix2:
  fixes A::"real^'n^'n"
  shows "orthogonal_matrix A = ((pairwise orthogonal (columns A)) \<and> (\<forall>i. norm (column i A) = 1) \<and>
  (card (columns A) = ncols A))"
  using orthogonal_matrix_intro[of A] 
    orthogonal_matrix_is_orthogonal[of A]
    orthogonal_matrix_norm[of A]
    orthogonal_matrix_card[of A]
  by auto

lemma orthogonal_matrix': "orthogonal_matrix (Q:: real ^'n^'n) \<longleftrightarrow>  Q ** transpose Q= mat 1"
  by (metis matrix_left_right_inverse orthogonal_matrix_def)

lemma orthogonal_matrix_intro2:        
  fixes A::"real^'n^'n"
  assumes p: "(pairwise orthogonal (rows A))"
  and n: "\<forall>i. norm (row i A) = 1"
  and c: "card (rows A) = nrows A" (*We need that premise to avoid the case that row i A = row j A when i \<noteq> j*)
  shows "orthogonal_matrix A"
proof (unfold orthogonal_matrix' vec_eq_iff, clarify, unfold mat_1_fun, auto)
  fix ia 
  have "(A ** transpose A) $ ia $ ia = row ia A \<bullet> row ia A"
    unfolding matrix_matrix_mult_inner_mult unfolding column_transpose ..
  also have "... = 1" using n norm_eq_1 by blast
  finally show "(A ** transpose A) $ ia $ ia = 1" .
  fix i
  assume i_not_ia: "i \<noteq> ia"
  have row_i_not_ia: "row i A \<noteq> row ia A"
  proof (rule ccontr, simp)
    assume row_i_ia:"row i A = row ia A"
    have rw: "(\<lambda>i. row i A)` (UNIV-{ia}) = {row i A|i. i\<noteq>ia}" unfolding rows_def by auto
    have "card (rows A) = card ({row i A|i. i\<noteq>ia})"
      by (rule bij_betw_same_card[of id], unfold bij_betw_def rows_def)
         (auto, metis row_i_ia i_not_ia)
    also have "... = card ((\<lambda>i. row i A)` (UNIV-{ia}))" unfolding rw ..
    also have "... \<le> card (UNIV - {ia})" by (metis card_image_le finite_code)
    also have "... < CARD ('n)" by simp
    finally show False using c unfolding nrows_def by simp
  qed
  hence oia: "orthogonal (row i A) (row ia A)"
    using p unfolding pairwise_def unfolding rows_def by auto
  have "(A ** transpose A) $ i $ ia = row i A \<bullet> row ia A"
    unfolding matrix_matrix_mult_inner_mult unfolding column_transpose ..
  also have "... = 0" using oia unfolding orthogonal_def .
  finally show "(A ** transpose A) $ i $ ia = 0" .
qed


lemma is_basis_imp_full_rank:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  assumes b: "is_basis (columns A)"
  and c: "card (columns A) = ncols A"
  shows "rank A = ncols A"
proof -
  have "rank A = col_rank A" unfolding rank_col_rank ..
  also have "... = vec.dim (col_space A)" unfolding col_rank_def ..
  also have "... = card (columns A)"
    by (metis b col_space_def independent_is_basis vec.dim_eq_card_independent vec.dim_span) 
  also have "... = ncols A" using c .
  finally show ?thesis .
qed

lemma card_columns_le_ncols:
  "card (columns A) \<le> ncols A"
proof -
  have columns_rw: "columns A = (\<lambda>i. column i A)` UNIV" unfolding columns_def by auto
  show ?thesis unfolding columns_rw ncols_def by (rule card_image_le, auto)
qed

lemma full_rank_imp_is_basis:
  fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "is_basis (columns A) \<and> card (columns A) = ncols A"
proof (rule conjI, unfold is_basis_def, rule conjI)
  have "rank A = col_rank A" unfolding rank_col_rank ..
  also have "... = vec.dim (col_space A)" unfolding col_rank_def ..
  also have "... = card (columns A)"
    by (metis (full_types) antisym_conv calculation card_columns_le_ncols col_space_def
        finite_columns r vec.dim_le_card vec.dim_span vec.span_superset) 
  finally have *: "rank A = card (columns A)" .
  then show c_eq: "card (columns A) = ncols A" unfolding r ..
  show "vec.independent (columns A)" 
    by (metis * vec.card_eq_dim_span_indep col_rank_def 
      col_space_def finite_columns rank_col_rank)
  thus "vec.span (columns A) = (UNIV::('a^'n::{mod_type}) set)"
    using independent_is_basis[of "columns A"] c_eq unfolding is_basis_def ncols_def by simp  
qed

lemma full_rank_imp_is_basis2:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "vec.independent (columns A) \<and> vec.span (columns A) = col_space A 
        \<and> card (columns A) = ncols A" 
proof -
  have "rank A = col_rank A" unfolding rank_col_rank ..
  also have "... = vec.dim (col_space A)" unfolding col_rank_def ..
  also have "... = card (columns A)"
    by (metis (full_types) antisym_conv calculation card_columns_le_ncols col_space_def
        finite_columns r vec.dim_le_card vec.dim_span vec.span_superset) 
  finally have *: "rank A = card (columns A)" .
  then have c_eq: "card (columns A) = ncols A" unfolding r ..
  moreover have "vec.independent (columns A)" 
    by (metis * vec.card_eq_dim_span_indep
      col_rank_def col_space_def finite_columns rank_col_rank)
  moreover have "vec.span (columns A) = col_space A" by (metis col_space_def)
  ultimately show ?thesis by simp
qed

corollary full_rank_eq_is_basis:
  fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
  shows "(is_basis (columns A) \<and> (card (columns A) = ncols A)) = (rank A = ncols A)"
  using full_rank_imp_is_basis is_basis_imp_full_rank by blast

lemma full_col_rank_imp_independent_columns:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  assumes "rank A = ncols A"
  shows "vec.independent (columns A)"
  by (metis assms full_rank_imp_is_basis2)


lemma matrix_vector_right_distrib_minus:
  fixes A::"'a::{ring_1}^'n^'m"
  shows "A *v (b - c) = (A *v b) - (A *v c)"
proof -
  have "A *v (b - c) = A *v (b + - c)" by (metis diff_minus_eq_add minus_minus)
  also have "... = (A *v b) + (A *v (- c))" unfolding matrix_vector_right_distrib ..
  also have "... = (A *v b) - (A *v c)" 
    by (metis (no_types, hide_lams) add.commute add_minus_cancel
        matrix_vector_right_distrib uminus_add_conv_diff)
  finally show ?thesis .
qed

lemma inv_matrix_vector_mul_left:
  assumes i: "invertible A"
  shows "(A *v x = A *v y) = (x=y)"
  by (metis i invertible_def matrix_vector_mul_assoc matrix_vector_mul_lid)

lemma norm_mult_vec:
  fixes a::"(real,'b::finite) vec"
  shows "norm (x \<bullet> x) = norm x * norm x"
  by (metis inner_real_def norm_cauchy_schwarz_eq norm_mult)

lemma norm_equivalence: 
  fixes A::"real^'n^'m"
  shows "((transpose A) *v (A *v x) = 0) \<longleftrightarrow> (A *v x = 0)" 
proof -
  have "A *v x = 0" if "transpose A *v (A *v x) = 0"
  proof -
    have eq: "(x v* (transpose A)) = (A *v x)"
      by (metis transpose_transpose transpose_vector)
    have eq_0: "0 = (x v* (transpose A)) * (A *v x)"
      by auto (metis that dot_lmul_matrix inner_eq_zero_iff inner_zero_left mult_not_zero transpose_vector)
    hence "0 = norm ((x v* (transpose A)) * (A *v x))" by auto
    also have "... = norm ((A *v x)*(A *v x))" unfolding eq ..
    also have "... = norm ((A *v x) \<bullet> (A *v x))"
      by (metis eq_0 that dot_lmul_matrix eq inner_zero_right norm_zero)
    also have "... = norm (A *v x)^2" unfolding norm_mult_vec[of "(A *v x)"] power2_eq_square ..
    finally show "A *v x = 0"
      by simp
  qed
  then show ?thesis
    by auto
qed


lemma invertible_transpose_mult:
  fixes A::"real^'cols::{mod_type}^'rows::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "invertible (transpose A ** A)" 
proof -
  have null_eq: "null_space A = null_space (transpose A ** A)" 
  proof (auto)
    fix x assume x: "x \<in> null_space A"
    show "x \<in> null_space (transpose A ** A)" using x unfolding null_space_def
      by (metis (lifting, full_types) matrix_vector_mul_assoc matrix_vector_mult_0_right mem_Collect_eq)
  next
    fix x assume x: "x \<in> null_space (transpose A ** A)"
    show "x \<in> null_space A" 
      by (metis is_solution_def matrix_vector_mul_assoc mem_Collect_eq 
        norm_equivalence null_space_eq_solution_set solution_set_def x)
  qed
  have "rank A = vec.dim (UNIV::(real^'cols::{mod_type}) set) - vec.dim (null_space A)"  
    using rank_nullity_theorem_matrices[of A]
    unfolding rank_eq_dim_col_space'[of A, symmetric]
    by (simp only: add.commute diff_add_inverse2 ncols_def vec_dim_card)
  also have "... = vec.dim (UNIV::(real^'cols::{mod_type}) set) - vec.dim (null_space (transpose A ** A))" 
    unfolding null_eq ..
  also have "... = rank (transpose A ** A)" 
    by (metis add.commute diff_add_inverse2 ncols_def rank_eq_dim_col_space
        rank_nullity_theorem_matrices vec_dim_card)
  finally have r_A: "rank A = rank (transpose A ** A)" .
  show ?thesis using full_rank_implies_invertible r unfolding ncols_def nrows_def r_A .
qed

lemma matrix_inv_mult:
  fixes A::"'a::{semiring_1}^'n^'n"
  and B::"'a::{semiring_1}^'n^'n"
  assumes "invertible A" and "invertible B"
  shows "matrix_inv (A ** B) = matrix_inv B ** matrix_inv A"
proof (rule matrix_inv_unique[of "A**B"])
  show "A ** B ** (matrix_inv B ** matrix_inv A) = mat 1"
    by (metis assms(1) assms(2) matrix_inv_right matrix_mul_assoc matrix_mul_lid)
  show " matrix_inv B ** matrix_inv A ** (A ** B) = mat 1"
    by (metis assms(1) assms(2) matrix_inv_left matrix_mul_assoc matrix_mul_lid)
qed


lemma invertible_transpose:
  fixes A::"'a::{field}^'n^'n"
  assumes "invertible A"
  shows "invertible (transpose A)"
  by (metis invertible_det_nz assms det_transpose)

text\<open>The following lemmas are generalizations of some parts of the library. They should be 
  in the file \<open>Generalizations.thy\<close> of the Gauss-Jordan AFP entry.\<close>

context vector_space
begin
lemma span_eq: "(span S = span T) = (S \<subseteq> span T \<and> T \<subseteq> span S)"
  using span_superset[unfolded subset_eq] using span_mono[of T "span S"] span_mono[of S "span T"]
  by (auto simp add: span_span)
end

lemma basis_orthogonal:
  fixes B :: "'a::real_inner set"
  assumes fB: "finite B"
  shows "\<exists>C. finite C \<and> card C \<le> card B \<and> span C
        = span B \<and> pairwise orthogonal C"
  (is " \<exists>C. ?P B C")
  using fB
proof (induct rule: finite_induct)
  case empty
  then show ?case
    apply (rule exI[where x="{}"])
    apply (auto simp add: pairwise_def)
    done
next
  case (insert a B)
  note fB = \<open>finite B\<close> and aB = \<open>a \<notin> B\<close>
  from \<open>\<exists>C. finite C \<and> card C \<le> card B \<and> span C = span B \<and> pairwise orthogonal C\<close>
  obtain C where C: "finite C" "card C \<le> card B"
    "span C = span B" "pairwise orthogonal C" by blast
  let ?a = "a - sum (\<lambda>x. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x) C"
  let ?C = "insert ?a C"
  from C(1) have fC: "finite ?C"
    by simp
  from fB aB C(1,2) have cC: "card ?C \<le> card (insert a B)"
    by (simp add: card_insert_if)
  {
    fix x k
    have th0: "\<And>(a::'a) b c. a - (b - c) = c + (a - b)"
      by (simp add: field_simps)
    have "x - k *\<^sub>R (a - (\<Sum>x\<in>C. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x)) \<in> span C
      \<longleftrightarrow> x - k *\<^sub>R a \<in> span C"
      apply (simp only: scaleR_right_diff_distrib th0)
      apply (rule span_add_eq)
      apply (rule span_mul)
      apply (rule span_sum)
      apply (rule span_mul)
      apply (rule span_base)
      apply assumption
      done
  }
  then have SC: "span ?C = span (insert a B)"
    unfolding set_eq_iff span_breakdown_eq C(3)[symmetric] by auto
  {
    fix y
    assume yC: "y \<in> C"
    then have Cy: "C = insert y (C - {y})"
      by blast
    have fth: "finite (C - {y})"
      using C by simp
    have "orthogonal ?a y"
      unfolding orthogonal_def
      unfolding inner_diff inner_sum_left right_minus_eq
      unfolding sum.remove [OF \<open>finite C\<close> \<open>y \<in> C\<close>]
      apply (clarsimp simp add: inner_commute[of y a])
      apply (rule sum.neutral)
      apply clarsimp
      apply (rule C(4)[unfolded pairwise_def orthogonal_def, rule_format])
      using \<open>y \<in> C\<close> by auto
  }
  with \<open>pairwise orthogonal C\<close> have CPO: "pairwise orthogonal ?C"
    by (rule pairwise_orthogonal_insert)
  from fC cC SC CPO have "?P (insert a B) ?C"
    by blast
  then show ?case by blast
qed

lemma op_vec_scaleR: "(*s) = (*\<^sub>R)"
  by (force simp: scalar_mult_eq_scaleR)

end
