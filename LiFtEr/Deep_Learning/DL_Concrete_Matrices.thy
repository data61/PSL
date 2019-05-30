(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Concrete Matrices\<close>

theory DL_Concrete_Matrices
imports Jordan_Normal_Form.Matrix
begin

text \<open>The following definition allows non-square-matrices, mat\_one (mat\_one n) only allows square matrices.\<close>

definition id_matrix::"nat \<Rightarrow> nat \<Rightarrow> real mat"
where "id_matrix nr nc = mat nr nc (\<lambda>(r, c). if r=c then 1 else 0)"

lemma id_matrix_dim: "dim_row (id_matrix nr nc) = nr" "dim_col (id_matrix nr nc) = nc" by (simp_all add: id_matrix_def)

lemma row_id_matrix:
assumes "i < nr"
shows "row (id_matrix nr nc) i = unit_vec nc i"
  by (rule eq_vecI, simp add: assms id_matrix_def unit_vec_def, simp add: id_matrix_dim(2))

lemma unit_eq_0[simp]:
  assumes i: "i \<ge> n"
  shows "unit_vec n i = 0\<^sub>v n"
  by (rule eq_vecI, insert i, auto simp: unit_vec_def)

lemma mult_id_matrix:
assumes "i < nr"
shows "(id_matrix nr (dim_vec v) *\<^sub>v v) $ i = (if i<dim_vec v then v $ i else 0)" (is "?a $ i = ?b")
proof -
  have "?a $ i = row (id_matrix nr (dim_vec v)) i \<bullet> v" using index_mult_mat_vec assms id_matrix_dim by auto
  also have "... = unit_vec (dim_vec v) i \<bullet> v" using row_id_matrix assms by auto
  also have "... = ?b" using scalar_prod_left_unit carrier_vecI unit_eq_0 scalar_prod_left_zero by fastforce
  finally show ?thesis by auto
qed


definition all1_vec::"nat \<Rightarrow> real vec"
where "all1_vec n = vec n (\<lambda>i. 1)"

definition all1_matrix::"nat \<Rightarrow> nat \<Rightarrow> real mat"
where "all1_matrix nr nc = mat nr nc (\<lambda>(r, c). 1)"

lemma all1_matrix_dim: "dim_row (all1_matrix nr nc) = nr" "dim_col (all1_matrix nr nc) = nc"
  by (simp_all add: all1_matrix_def)

lemma row_all1_matrix:
assumes "i < nr"
shows "row (all1_matrix nr nc) i = all1_vec nc"
  apply (rule eq_vecI)
  apply (simp add: all1_matrix_def all1_vec_def assms)
  by (simp add: all1_matrix_def all1_vec_def)

lemma all1_vec_scalar_prod:
shows "all1_vec (length xs) \<bullet> (vec_of_list xs) = sum_list xs"
proof -
  have "all1_vec (length xs) \<bullet> (vec_of_list xs) = (\<Sum>i = 0..<dim_vec (vec_of_list xs). vec_of_list xs $ i)"
    unfolding scalar_prod_def by (metis (no_types, lifting) all1_vec_def mult_cancel_right1 sum_ivl_cong
    vec.abs_eq dim_vec index_vec vec_of_list.abs_eq)
  also have "... = (\<Sum>i = 0..<length xs. xs ! i)" using vec.abs_eq dim_vec vec_of_list.abs_eq
    by (metis sum_ivl_cong index_vec)
  also have "... = sum_list xs" by (simp add: sum_list_sum_nth)
  finally show ?thesis by auto
qed


lemma mult_all1_matrix:
assumes "i < nr"
shows "((all1_matrix nr (dim_vec v)) *\<^sub>v v) $ i = sum_list (list_of_vec v)" (is "?a $ i = sum_list (list_of_vec v)")
proof -
  have "?a $ i = row (all1_matrix nr (dim_vec v)) i \<bullet> v" using index_mult_mat_vec assms all1_matrix_dim by auto
  also have "... = sum_list (list_of_vec v)" unfolding row_all1_matrix[OF assms] using all1_vec_scalar_prod[of "list_of_vec v"]
    by (metis vec.abs_eq dim_vec vec_list vec_of_list.abs_eq)
  finally show ?thesis by auto
qed


definition copy_first_matrix::"nat \<Rightarrow> nat \<Rightarrow> real mat"
where "copy_first_matrix nr nc = mat nr nc (\<lambda>(r, c). if c = 0 then 1 else 0)"

lemma copy_first_matrix_dim: "dim_row (copy_first_matrix nr nc) = nr" "dim_col (copy_first_matrix nr nc) = nc"
  by (simp_all add: copy_first_matrix_def)

lemma row_copy_first_matrix:
assumes "i < nr"
shows "row (copy_first_matrix nr nc) i = unit_vec nc 0"
  apply (rule eq_vecI)
  apply (auto simp add: copy_first_matrix_def assms)[1]
  by (simp add: copy_first_matrix_def)

lemma mult_copy_first_matrix:
assumes "i < nr" and "dim_vec v > 0"
shows "(copy_first_matrix nr (dim_vec v) *\<^sub>v v) $ i = v $ 0" (is "?a $ i = v $ 0")
proof -
  have "?a $ i = row (copy_first_matrix nr (dim_vec v)) i \<bullet> v" using index_mult_mat_vec assms copy_first_matrix_dim by auto
  also have "... = unit_vec (dim_vec v) 0 \<bullet> v" using row_copy_first_matrix assms by auto
  also have "... = v $ 0" using assms(2) scalar_prod_left_unit carrier_dim_vec by blast
  finally show ?thesis by auto
qed

end
