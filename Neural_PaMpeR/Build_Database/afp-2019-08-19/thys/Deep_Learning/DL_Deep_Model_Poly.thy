(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Polynomials representing the Deep Network Model\<close>

theory DL_Deep_Model_Poly
imports DL_Deep_Model Polynomials.More_MPoly_Type Jordan_Normal_Form.Determinant
begin

lemma polyfun_det:
assumes "\<And>x. (A x) \<in> carrier_mat n n"
assumes "\<And>x i j. i<n \<Longrightarrow> j<n \<Longrightarrow> polyfun N (\<lambda>x. (A x) $$ (i,j))"
shows "polyfun N (\<lambda>x. det (A x))"
proof -
  {
    fix p assume "p\<in> {p. p permutes {0..<n}}"
    then have "p permutes {0..<n}" by auto
    then have "\<And>x. x < n \<Longrightarrow> p x < n" using permutes_in_image by auto
    then have "polyfun N (\<lambda>x. \<Prod>i = 0..<n. A x $$ (i, p i))"
      using polyfun_Prod[of "{0..<n}" N "\<lambda>i x. A x $$ (i, p i)"] assms by simp
    then have "polyfun N (\<lambda>x. signof p * (\<Prod>i = 0..<n. A x $$ (i, p i)))" using polyfun_const polyfun_mult by blast
  }
  moreover have "finite {i. i permutes {0..<n}}" by (simp add: finite_permutations)
  ultimately show ?thesis  unfolding det_def'[OF assms(1)]
    using polyfun_Sum[OF \<open>finite {i. i permutes {0..<n}}\<close>, of N "\<lambda>p x. signof p * (\<Prod>i = 0..<n. A x $$ (i, p i))"]
    by blast
qed

lemma polyfun_extract_matrix:
assumes "i<m" "j<n"
shows "polyfun {..<a + (m * n + c)} (\<lambda>f. extract_matrix (\<lambda>i. f (i + a)) m n $$ (i,j))"
unfolding index_extract_matrix[OF assms] apply (rule polyfun_single) using two_digit_le[OF assms] by simp

lemma polyfun_mult_mat_vec:
assumes "\<And>x. v x \<in> carrier_vec n"
assumes "\<And>j. j<n \<Longrightarrow> polyfun N (\<lambda>x. v x $ j)"
assumes "\<And>x. A x \<in> carrier_mat m n"
assumes "\<And>i j. i<m \<Longrightarrow> j<n \<Longrightarrow> polyfun N (\<lambda>x. A x $$ (i,j))"
assumes "j < m"
shows "polyfun N (\<lambda>x. ((A x) *\<^sub>v (v x)) $ j)"
proof -
  have "\<And>x. j < dim_row (A x)" using \<open>j < m\<close> assms(3) carrier_matD(1) by force
  have "\<And>x. n = dim_vec (v x)" using assms(1) carrier_vecD by fastforce
  {
    fix i assume "i \<in> {0..<n}"
    then have "i < n" by auto
    {
      fix x
      have "i < dim_vec (v x)" using assms(1) carrier_vecD \<open>i<n\<close> by fastforce
      have "j < dim_row (A x)" using \<open>j < m\<close> assms(3) carrier_matD(1) by force
      have "dim_col (A x) = dim_vec (v x)" by (metis assms(1) assms(3) carrier_matD(2) carrier_vecD)
      then have "row (A x) j $ i = A x $$ (j,i)" "i<n" using \<open>j < dim_row (A x)\<close> \<open>i<n\<close> by (simp_all add: \<open>i < dim_vec (v x)\<close>)
    }
    then have "polyfun N (\<lambda>x. row (A x) j $ i * v x $ i)"
      using polyfun_mult assms(4)[OF \<open>j < m\<close>] assms(2) by fastforce
  }
  then show ?thesis unfolding index_mult_mat_vec[OF \<open>\<And>x. j < dim_row (A x)\<close>] scalar_prod_def
    using polyfun_Sum[of "{0..<n}" N "\<lambda>i x. row (A x) j $ i * v x $ i"] finite_atLeastLessThan[of 0 n] \<open>\<And>x. n = dim_vec (v x)\<close>
    by simp
qed

(* The variable a has been inserted here to make the induction work:*)
lemma polyfun_evaluate_net_plus_a:
assumes "map dim_vec inputs = input_sizes m"
assumes "valid_net m"
assumes "j < output_size m"
shows "polyfun {..<a + count_weights s m} (\<lambda>f. evaluate_net (insert_weights s m (\<lambda>i. f (i + a))) inputs $ j)"
using assms proof (induction m arbitrary:inputs j a)
  case (Input)
  then show ?case unfolding insert_weights.simps evaluate_net.simps using polyfun_const by metis
next
  case (Conv x m)
  then obtain x1 x2 where "x=(x1,x2)" by fastforce
  show ?case unfolding \<open>x=(x1,x2)\<close> insert_weights.simps evaluate_net.simps drop_map unfolding list_of_vec_index
  proof (rule polyfun_mult_mat_vec)
    {
      fix f
      have 1:"valid_net' (insert_weights s m (\<lambda>i. f (i + x1 * x2)))"
        using \<open>valid_net (Conv x m)\<close> valid_net.simps by (metis
        convnet.distinct(1) convnet.distinct(5) convnet.inject(2) remove_insert_weights)
      have 2:"map dim_vec inputs = input_sizes (insert_weights s m (\<lambda>i. f (i + x1 * x2)))"
        using input_sizes_remove_weights remove_insert_weights
        by (simp add: Conv.prems(1))
      have "dim_vec (evaluate_net (insert_weights s m (\<lambda>i. f (i + x1 * x2))) inputs) = output_size m"
       using output_size_correct[OF 1 2] using remove_insert_weights by auto
      then show "evaluate_net (insert_weights s m (\<lambda>i. f (i + x1 * x2))) inputs \<in> carrier_vec (output_size m)"
        using carrier_vec_def by (metis (full_types) mem_Collect_eq)
    }

    have "map dim_vec inputs = input_sizes m" by (simp add: Conv.prems(1))
    have "valid_net m" using Conv.prems(2) valid_net.cases by fastforce
    show "\<And>j. j < output_size m \<Longrightarrow>  polyfun {..<a + count_weights s (Conv (x1, x2) m)}
          (\<lambda>f. evaluate_net (insert_weights s m (\<lambda>i. f (i + x1 * x2 + a))) inputs $ j)"
      unfolding vec_of_list_index count_weights.simps
      using Conv(1)[OF \<open>map dim_vec inputs = input_sizes m\<close> \<open>valid_net m\<close>, of _ "x1 * x2 + a"]
      unfolding semigroup_add_class.add.assoc ab_semigroup_add_class.add.commute[of "x1 * x2" a]
      by blast

    have "output_size m = x2" using Conv.prems(2) \<open>x = (x1, x2)\<close> valid_net.cases by fastforce
    show "\<And>f. extract_matrix (\<lambda>i. f (i + a)) x1 x2 \<in> carrier_mat x1 (output_size m)" unfolding \<open>output_size m = x2\<close> using dim_extract_matrix
      using carrier_matI by (metis (no_types, lifting))

    show "\<And>i j. i < x1 \<Longrightarrow> j < output_size m \<Longrightarrow> polyfun {..<a + count_weights s (Conv (x1, x2) m)} (\<lambda>f. extract_matrix (\<lambda>i. f (i + a)) x1 x2 $$ (i, j))"
      unfolding \<open>output_size m = x2\<close> count_weights.simps using polyfun_extract_matrix[of _ x1 _ x2 a "count_weights s m"] by blast

    show "j < x1" using Conv.prems(3) \<open>x = (x1, x2)\<close> by auto
  qed
next
  case (Pool m1 m2 inputs j a)
  have A2:"\<And>f. map dim_vec (take (length (input_sizes (insert_weights s m1 (\<lambda>i. f (i + a))))) inputs) = input_sizes m1"
    by (metis Pool.prems(1)  append_eq_conv_conj input_sizes.simps(3) input_sizes_remove_weights remove_insert_weights take_map)
  have B2:"\<And>f. map dim_vec (drop (length (input_sizes (insert_weights s m1 (\<lambda>i. f (i + a))))) inputs) = input_sizes m2"
    using Pool.prems(1) append_eq_conv_conj input_sizes.simps(3) input_sizes_remove_weights remove_insert_weights by (metis drop_map)
  have A3:"valid_net m1" and B3:"valid_net m2" using \<open>valid_net (Pool m1 m2)\<close> valid_net.simps by blast+
  have "output_size (Pool m1 m2) = output_size m2" unfolding output_size.simps
    using \<open>valid_net (Pool m1 m2)\<close> "valid_net.cases" by fastforce
  then have A4:"j < output_size m1" and B4:"j < output_size m2" using \<open>j < output_size (Pool m1 m2)\<close> by simp_all

  let ?net1 = "\<lambda>f. evaluate_net (insert_weights s m1 (\<lambda>i. f (i + a)))
    (take (length (input_sizes (insert_weights s m1 (\<lambda>i. f (i + a))))) inputs)"
  let ?net2 = "\<lambda>f. evaluate_net (insert_weights s m2 (if s then \<lambda>i. f (i + a) else (\<lambda>i. f (i + count_weights s m1 + a))))
    (drop (length (input_sizes (insert_weights s m1 (\<lambda>i. f (i + a))))) inputs)"
  have length1: "\<And>f. output_size m1 = dim_vec (?net1 f)"
    by (metis A2 A3 input_sizes_remove_weights output_size_correct remove_insert_weights)
  then have jlength1:"\<And>f. j < dim_vec (?net1 f)" using A4 by metis
  have length2: "\<And>f. output_size m2 = dim_vec (?net2 f)"
    by (metis B2 B3 input_sizes_remove_weights output_size_correct remove_insert_weights)
  then have jlength2:"\<And>f. j < dim_vec (?net2 f)" using B4 by metis
  have cong1:"\<And>xf. (\<lambda>f. evaluate_net (insert_weights s m1 (\<lambda>i. f (i + a)))
        (take (length (input_sizes (insert_weights s m1 (\<lambda>i. xf (i + a))))) inputs) $ j)
         = (\<lambda>f. ?net1 f $ j)"
    using input_sizes_remove_weights remove_insert_weights by auto
  have cong2:"\<And>xf. (\<lambda>f. evaluate_net (insert_weights s m2 (\<lambda>i. f (i + (a + (if s then 0 else count_weights s m1)))))
        (drop (length (input_sizes (insert_weights s m1 (\<lambda>i. xf (i + a))))) inputs) $ j)
         = (\<lambda>f. ?net2 f $ j)"
    unfolding semigroup_add_class.add.assoc[symmetric] ab_semigroup_add_class.add.commute[of a "if s then 0 else count_weights s m1"]
    using input_sizes_remove_weights remove_insert_weights by auto

  show ?case unfolding insert_weights.simps evaluate_net.simps  count_weights.simps
    unfolding  index_component_mult[OF jlength1 jlength2]
    apply (rule polyfun_mult)
     using Pool.IH(1)[OF A2 A3 A4, of a, unfolded cong1]
     apply (simp add:polyfun_subset[of "{..<a + count_weights s m1}" "{..<a + (if s then max (count_weights s m1) (count_weights s m2) else count_weights s m1 + count_weights s m2)}"]) 
    using Pool.IH(2)[OF B2 B3 B4, of "a + (if s then 0 else count_weights s m1)", unfolded cong2 semigroup_add_class.add.assoc[of a]]
    by (simp add:polyfun_subset[of "{..<a + ((if s then 0 else count_weights s m1) + count_weights s m2)}" "{..<a + (if s then max (count_weights s m1) (count_weights s m2) else count_weights s m1 + count_weights s m2)}"])
qed

lemma polyfun_evaluate_net:
assumes "map dim_vec inputs = input_sizes m"
assumes "valid_net m"
assumes "j < output_size m"
shows "polyfun {..<count_weights s m} (\<lambda>f. evaluate_net (insert_weights s m f) inputs $ j)"
using polyfun_evaluate_net_plus_a[where a=0, OF assms] by simp

lemma polyfun_tensors_from_net:
assumes "valid_net m"
assumes "is \<lhd> input_sizes m"
assumes "j < output_size m"
shows "polyfun {..<count_weights s m} (\<lambda>f. Tensor.lookup (tensors_from_net (insert_weights s m f) $ j) is)"
proof -
  have 1:"\<And>f. valid_net' (insert_weights s m f)" by (simp add: assms(1) remove_insert_weights)
  have input_sizes:"\<And>f. input_sizes (insert_weights s m f) = input_sizes m"
    unfolding input_sizes_remove_weights by (simp add: remove_insert_weights)
  have 2:"\<And>f. is \<lhd> input_sizes (insert_weights s m f)"
    unfolding input_sizes using assms(2) by blast
  have 3:"\<And>f. j < output_size' (insert_weights s m f)"
    by (simp add: assms(3) remove_insert_weights)
  have "\<And>f1 f2. base_input (insert_weights s m f1) is = base_input (insert_weights s m f2) is"
    unfolding base_input_def by (simp add: input_sizes)
  then have "\<And>xf. (\<lambda>f. evaluate_net (insert_weights s m f) (base_input (insert_weights s m xf) is) $ j)
    = (\<lambda>f. evaluate_net (insert_weights s m f) (base_input (insert_weights s m f) is) $ j)"
    by metis
  then show ?thesis unfolding lookup_tensors_from_net[OF 1 2 3]
    using polyfun_evaluate_net[OF base_input_length[OF 2, unfolded input_sizes, symmetric] assms(1) assms(3), of s]
    by simp
qed

lemma polyfun_matricize:
assumes "\<And>x. dims (T x) = ds"
assumes "\<And>is. is \<lhd> ds \<Longrightarrow> polyfun N (\<lambda>x. Tensor.lookup (T x) is)"
assumes "\<And>x. dim_row (matricize I (T x)) = nr"
assumes "\<And>x. dim_col (matricize I (T x)) = nc"
assumes "i < nr"
assumes "j < nc"
shows "polyfun N (\<lambda>x. matricize I (T x) $$ (i,j))"
proof -
  let ?weave = "\<lambda> x. (weave I
    (digit_encode (nths ds I ) i)
    (digit_encode (nths ds (-I )) j))"
  have 1:"\<And>x. matricize I (T x) $$ (i,j) = Tensor.lookup (T x) (?weave x)" unfolding matricize_def
    by (metis (no_types, lifting) assms(1) assms(3) assms(4) assms(5) assms(6) case_prod_conv
    dim_col_mat(1) dim_row_mat(1) index_mat(1) matricize_def)
  have "\<And>x. ?weave x \<lhd> ds"
    using valid_index_weave(1) assms(2) digit_encode_valid_index dim_row_mat(1) matricize_def
    using assms digit_encode_valid_index matricize_def by (metis dim_col_mat(1))
  then have "polyfun N (\<lambda>x. Tensor.lookup (T x) (?weave x))" using assms(2) by simp
  then show ?thesis unfolding 1 using assms(1) by blast
qed

lemma "(\<not> (a::nat) < b) = (a \<ge> b)"
by (metis not_le)

lemma polyfun_submatrix:
assumes "\<And>x. (A x) \<in> carrier_mat m n"
assumes "\<And>x i j. i<m \<Longrightarrow> j<n \<Longrightarrow> polyfun N (\<lambda>x. (A x) $$ (i,j))"
assumes "i < card {i. i < m \<and> i \<in> I}"
assumes "j < card {j. j < n \<and> j \<in> J}"
assumes "infinite I" "infinite J"
shows "polyfun N (\<lambda>x. (submatrix (A x) I J) $$ (i,j))"
proof -
  have 1:"\<And>x. (submatrix (A x) I J) $$ (i,j) = (A x) $$ (pick I i, pick J j)"
    using submatrix_index by (metis (no_types, lifting) Collect_cong assms(1) assms(3) assms(4) carrier_matD(1) carrier_matD(2))
  have "pick I i < m"  "pick J j < n" using card_le_pick_inf[OF \<open>infinite I\<close>] card_le_pick_inf[OF \<open>infinite J\<close>]
    \<open>i < card {i. i < m \<and> i \<in> I}\<close>[unfolded set_le_in] \<open>j < card {j. j < n \<and> j \<in> J}\<close>[unfolded set_le_in] not_less by metis+
  then show ?thesis unfolding 1 by (simp add: assms(2))
qed

context deep_model_correct_params_y
begin

definition witness_submatrix where
"witness_submatrix f = submatrix (A' f) rows_with_1 rows_with_1"


lemma polyfun_tensor_deep_model:
assumes "is \<lhd> input_sizes (deep_model_l rs)"
shows "polyfun {..<weight_space_dim}
  (\<lambda>f. Tensor.lookup (tensors_from_net (insert_weights shared_weights (deep_model_l rs) f) $ y) is)"
proof -
  have 1:"\<And>f. remove_weights (insert_weights shared_weights (deep_model_l rs) f) = deep_model_l rs"
    using remove_insert_weights by metis
  then have "y < output_size ( deep_model_l rs)" using valid_deep_model y_valid length_output_deep_model by force
  have 0:"{..<weight_space_dim} = set [0..<weight_space_dim]" by auto
  then show ?thesis unfolding weight_space_dim_def using polyfun_tensors_from_net assms(1) valid_deep_model
    \<open>y < output_size ( deep_model_l rs )\<close> by metis
qed

lemma input_sizes_deep_model: "input_sizes (deep_model_l rs) = replicate (2 * N_half) (last rs)"
  unfolding N_half_def using input_sizes_deep_model deep
  by (metis (no_types, lifting) Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_le_lessD diff_Suc_Suc length_tl less_imp_le_nat list.size(3) not_less_eq numeral_3_eq_3 power_eq_if)

lemma polyfun_matrix_deep_model:
assumes "i<(last rs) ^ N_half"
assumes "j<(last rs) ^ N_half"
shows "polyfun {..<weight_space_dim} (\<lambda>f. A' f $$ (i,j))"
proof -
  have 0:"y < output_size ( deep_model_l rs )" using valid_deep_model y_valid length_output_deep_model by force
  have 1:"\<And>f. remove_weights (insert_weights shared_weights (deep_model_l rs) f) = deep_model_l rs"
    using remove_insert_weights by metis
  have 2:"(\<And>f is. is \<lhd> replicate (2 * N_half) (last rs) \<Longrightarrow>
         polyfun {..<weight_space_dim} (\<lambda>x. Tensor.lookup (A x) is))"
    unfolding A_def using polyfun_tensor_deep_model[unfolded input_sizes_deep_model] 0 by blast
  show ?thesis
    unfolding A'_def A_def apply (rule polyfun_matricize)
    using dims_tensor_deep_model[OF 1] 2[unfolded A_def]
    using dims_A'_pow[unfolded A'_def A_def] \<open>i<(last rs) ^ N_half\<close> \<open>j<(last rs) ^ N_half\<close>
    by auto
qed

lemma polyfun_submatrix_deep_model:
assumes "i < r ^ N_half"
assumes "j < r ^ N_half"
shows "polyfun {..<weight_space_dim} (\<lambda>f. witness_submatrix f $$ (i,j))"
unfolding witness_submatrix_def
proof (rule polyfun_submatrix)
  have 1:"\<And>f. remove_weights (insert_weights shared_weights (deep_model_l rs) f) = deep_model_l rs"
    using remove_insert_weights by metis
  show "\<And>f. A' f \<in> carrier_mat ((last rs) ^ N_half) ((last rs) ^ N_half)"
    using "1" dims_A'_pow using weight_space_dim_def by auto
  show "\<And>f i j. i < last rs ^ N_half \<Longrightarrow> j < last rs ^ N_half \<Longrightarrow>
        polyfun {..<weight_space_dim} (\<lambda>f. A' f $$ (i, j))"
    using polyfun_matrix_deep_model weight_space_dim_def by force
  show "i < card {i. i < last rs ^ N_half \<and> i \<in> rows_with_1}"
    using assms(1) card_rows_with_1 dims_Aw'_pow set_le_in by metis
  show "j < card {i. i < last rs ^ N_half \<and> i \<in> rows_with_1}"
    using assms(2) card_rows_with_1 dims_Aw'_pow set_le_in by metis
  show "infinite rows_with_1" "infinite rows_with_1" by (simp_all add: infinite_rows_with_1)
qed

lemma polyfun_det_deep_model:
shows "polyfun {..<weight_space_dim} (\<lambda>f. det (witness_submatrix f))"
proof (rule polyfun_det)
  fix f
  have "remove_weights (insert_weights shared_weights (deep_model_l rs) f) = deep_model_l rs"
    using remove_insert_weights by metis

  show "witness_submatrix f \<in> carrier_mat (r ^ N_half) (r ^ N_half)"
    unfolding witness_submatrix_def apply (rule carrier_matI) unfolding dim_submatrix[unfolded set_le_in]
    unfolding dims_A'_pow[unfolded weight_space_dim_def] using card_rows_with_1 dims_Aw'_pow by simp_all
  show "\<And>i j. i < r ^ N_half \<Longrightarrow> j < r ^ N_half \<Longrightarrow> polyfun {..<weight_space_dim} (\<lambda>f. witness_submatrix f $$ (i, j))"
    using polyfun_submatrix_deep_model by blast
qed

end

end
