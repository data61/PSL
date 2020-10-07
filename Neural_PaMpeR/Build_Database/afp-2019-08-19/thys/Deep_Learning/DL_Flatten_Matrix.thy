(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Matrix to Vector Conversion\<close>

theory DL_Flatten_Matrix
imports Jordan_Normal_Form.Matrix
begin

definition extract_matrix :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
"extract_matrix a m n = mat m n (\<lambda>(i,j). a (i*n + j))"

definition flatten_matrix :: "'a mat \<Rightarrow> (nat \<Rightarrow> 'a)" where
"flatten_matrix A k = A $$ (k div dim_col A, k mod dim_col A)"

lemma two_digit_le:
  "i * n + j < m * n" if "i < m" "j < n" for i j :: nat
  using that by (auto dest!: less_imp_Suc_add simp add: algebra_simps)

lemma extract_matrix_cong:
assumes "\<And>i. i < m * n \<Longrightarrow> a i = b i"
shows "extract_matrix a m n = extract_matrix b m n"
proof -
  have "\<And>i j. i < m \<Longrightarrow> j < n \<Longrightarrow> a (i*n + j) = b (i*n + j)" using two_digit_le assms by blast
  then show ?thesis unfolding extract_matrix_def by auto
qed

lemma extract_matrix_flatten_matrix:
"extract_matrix (flatten_matrix A) (dim_row A) (dim_col A) = A"
unfolding extract_matrix_def flatten_matrix_def by auto

lemma extract_matrix_flatten_matrix_cong:
  assumes "\<And>x. x < dim_row A * dim_col A \<Longrightarrow> f x = flatten_matrix A x"
  shows "extract_matrix f (dim_row A) (dim_col A) = A"
  unfolding extract_matrix_def
  by (metis assms extract_matrix_cong extract_matrix_def extract_matrix_flatten_matrix)

lemma flatten_matrix_extract_matrix:
  "flatten_matrix (extract_matrix a m n) k = a k" if "k < m * n"
proof -
  from that have "m * n > 0"
    by (cases "m * n = 0") simp_all
  then have "m > 0" and "n > 0"
    by simp_all
  with that have "k div n < m"
    by (metis div_eq_0_iff div_mult2_eq mult.commute neq0_conv) 
  moreover have "k mod n < n"
    using \<open>n > 0\<close> by simp
  ultimately show ?thesis
    by (auto simp add: extract_matrix_def flatten_matrix_def)
qed

lemma index_extract_matrix:
assumes "i<m" "j<n"
shows "extract_matrix a m n $$ (i,j) = a (i*n + j)"
  unfolding extract_matrix_def using assms by simp

lemma dim_extract_matrix:
shows "dim_row (extract_matrix as m n) = m"
and "dim_col (extract_matrix as m n) = n"
  unfolding extract_matrix_def by simp_all

end
