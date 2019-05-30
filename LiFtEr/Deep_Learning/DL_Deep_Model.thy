(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Deep Network Model\<close>

theory DL_Deep_Model
imports DL_Network Tensor_Matricization Jordan_Normal_Form.DL_Submatrix DL_Concrete_Matrices
DL_Missing_Finite_Set Jordan_Normal_Form.DL_Missing_Sublist Jordan_Normal_Form.Determinant
begin

hide_const(open) Polynomial.order
hide_const (open) Matrix.unit_vec 


fun deep_model and deep_model' where
"deep_model' Y [] = Input Y" |
"deep_model' Y (r # rs) = Pool (deep_model Y r rs) (deep_model Y r rs)" |
"deep_model Y r rs = Conv (Y,r) (deep_model' r rs)"

abbreviation "deep_model'_l rs == deep_model' (rs!0) (tl rs)"
abbreviation "deep_model_l rs == deep_model (rs!0) (rs!1) (tl (tl rs))"

lemma valid_deep_model: "valid_net (deep_model Y r rs)"
apply (induction rs arbitrary: Y r)
apply (simp add: valid_net.intros(1) valid_net.intros(2))
using valid_net.intros(2) valid_net.intros(3) by auto

lemma valid_deep_model': "valid_net (deep_model' r rs)"
apply (induction rs arbitrary: r)
apply (simp add: valid_net.intros(1))
by (metis deep_model'.elims deep_model'.simps(2) deep_model.elims output_size.simps valid_net.simps)

lemma input_sizes_deep_model':
assumes "length rs \<ge> 1"
shows "input_sizes (deep_model'_l rs) = replicate (2^(length rs - 1)) (last rs)"
using assms proof (induction "butlast rs" arbitrary:rs)
  case Nil
  then have "rs = [rs!0]"
    by (metis One_nat_def diff_diff_cancel diff_zero length_0_conv length_Suc_conv length_butlast nth_Cons_0)
  then have "input_sizes (deep_model'_l rs) = [last rs]"
    by (metis deep_model'.simps(1) input_sizes.simps(1) last.simps list.sel(3))
  then show "input_sizes (deep_model'_l rs) = replicate (2 ^ (length rs - 1)) (last rs)"
    by (metis One_nat_def \<open>[] = butlast rs\<close> empty_replicate length_butlast list.size(3) power_0 replicate.simps(2))
next
  case (Cons r rs' rs)
  then have IH: "input_sizes (deep_model'_l (tl rs)) = replicate (2 ^ (length (tl rs) - 1)) (last rs)"
    by (metis (no_types, lifting) One_nat_def butlast_tl diff_is_0_eq' last_tl length_Cons
    length_butlast length_tl list.sel(3) list.size(3) nat_le_linear not_one_le_zero)
  have "rs = r # (tl rs)" by (metis Cons.hyps(2) Cons.prems One_nat_def append_Cons append_butlast_last_id length_greater_0_conv less_le_trans list.sel(3) zero_less_Suc)
  then have "deep_model'_l rs = Pool (deep_model_l rs) (deep_model_l rs)"
    by (metis Cons.hyps(2) One_nat_def butlast.simps(2) deep_model'.elims list.sel(3) list.simps(3) nth_Cons_0 nth_Cons_Suc)
  then have "input_sizes (deep_model'_l rs) = input_sizes (deep_model_l rs) @ input_sizes (deep_model_l rs)"
    using input_sizes.simps(3) by metis
  also have "... = input_sizes (deep_model'_l (tl rs)) @ input_sizes (deep_model'_l (tl rs))"
    by (metis (no_types, lifting) Cons.hyps(2) One_nat_def deep_model.elims input_sizes.simps(2)
    length_Cons length_butlast length_greater_0_conv length_tl list.sel(2) list.sel(3) list.size(3)
    nth_tl one_neq_zero)
  also have "... = replicate (2 ^ (length (tl rs) - 1)) (last rs) @ replicate (2 ^ (length (tl rs) - 1)) (last rs)"
     using IH by auto
  also have "... = replicate (2 ^ (length rs - 1)) (last rs)"
    using replicate_add[of "2 ^ (length (tl rs) - 1)" "2 ^ (length (tl rs) - 1)" "last rs"]
    by (metis Cons.hyps(2) One_nat_def butlast_tl length_butlast list.sel(3) list.size(4) mult_2_right
    power_add power_one_right)
  finally show ?case by auto
qed

lemma input_sizes_deep_model:
assumes "length rs \<ge> 2"
shows "input_sizes (deep_model_l rs) = replicate (2^(length rs - 2)) (last rs)"
proof -
  have "input_sizes (deep_model_l rs) = input_sizes (deep_model'_l (tl rs))"
    by (metis One_nat_def Suc_1 assms hd_Cons_tl deep_model.elims input_sizes.simps(2) length_Cons
    length_greater_0_conv lessI linorder_not_le list.size(3) not_numeral_le_zero nth_tl)
  also have "... = replicate (2^(length rs - 2)) (last rs)" using input_sizes_deep_model'
    by (metis (no_types, lifting) One_nat_def Suc_1 Suc_eq_plus1 assms diff_diff_left hd_Cons_tl
    last_tl length_Cons length_tl linorder_not_le list.size(3) not_less_eq not_numeral_le_zero
    numeral_le_one_iff semiring_norm(69))
  finally show ?thesis by auto
qed

lemma evaluate_net_Conv_id:
assumes "valid_net' m"
and "input_sizes m = map dim_vec input"
and "j<nr"
shows "evaluate_net (Conv (id_matrix nr (output_size' m)) m) input $ j
 = (if j<output_size' m then evaluate_net m input $ j else 0)"
  unfolding evaluate_net.simps output_size_correct[OF assms(1) assms(2)[symmetric]]
  using mult_id_matrix[OF `j<nr`, of "evaluate_net m input", unfolded dim_vec_of_list]
  by metis

lemma tensors_from_net_Conv_id:
assumes "valid_net' m"
and "i<nr"
shows "tensors_from_net (Conv (id_matrix nr (output_size' m)) m) $ i
 = (if i<output_size' m then tensors_from_net m $ i else tensor0 (input_sizes m))"
  (is "?a $ i = ?b")
proof (rule tensor_lookup_eqI)
  have "Tensor.dims (?a $ i) = input_sizes m" by (metis assms(1) assms(2) dims_tensors_from_net
    id_matrix_dim(1) id_matrix_dim(2) input_sizes.simps(2) output_size.simps(2)
    output_size_correct_tensors remove_weights.simps(2) valid_net.intros(2) vec_setI)
  moreover have "Tensor.dims (?b) = input_sizes m" using dims_tensors_from_net
    output_size_correct_tensors[OF assms(1)] dims_tensor0 by (simp add: vec_setI)
  ultimately show "Tensor.dims (?a $ i) = Tensor.dims (?b)" by auto

  define Convm where "Convm = Conv (id_matrix nr (output_size' m)) m"
  fix "is"
  assume "is \<lhd> Tensor.dims (?a$i)"
  then have "is \<lhd> input_sizes m" using `Tensor.dims (?a$i) = input_sizes m` by auto
  have "valid_net' Convm" by (simp add: assms id_matrix_dim valid_net.intros(2) Convm_def)
  have "base_input m is = base_input Convm is" by (simp add: Convm_def base_input_def)
  have "i < output_size' Convm" unfolding Convm_def remove_weights.simps output_size.simps
    id_matrix_dim using assms by metis
  have "is \<lhd> input_sizes (Conv (id_matrix nr (output_size' m)) m)"
    by (metis \<open>is \<lhd> input_sizes m\<close> input_sizes.simps(2))
  then have f1: "lookup (tensors_from_net (Conv (id_matrix nr (output_size' m)) m) $ i) is = evaluate_net (Conv (id_matrix nr (output_size' m)) m) (base_input (Conv (id_matrix nr (output_size' m)) m) is) $ i"
    using Convm_def \<open>i < output_size' Convm\<close> \<open>valid_net' Convm\<close> lookup_tensors_from_net by blast
  have "lookup (tensor0 (input_sizes m)) is = (0::real)"
    by (meson \<open>is \<lhd> input_sizes m\<close> lookup_tensor0)
  then show "Tensor.lookup (?a $ i) is = Tensor.lookup ?b is"
   using Convm_def \<open>base_input m is = base_input Convm is\<close> \<open>is \<lhd> input_sizes m\<close> assms(1) assms(2)
   base_input_length evaluate_net_Conv_id f1 lookup_tensors_from_net by auto
qed

lemma evaluate_net_Conv_copy_first:
assumes "valid_net' m"
and "input_sizes m = map dim_vec input"
and "j<nr"
and "output_size' m > 0"
shows "evaluate_net (Conv (copy_first_matrix nr (output_size' m)) m) input $ j
 = evaluate_net m input $ 0"
  unfolding evaluate_net.simps output_size_correct[OF assms(1) assms(2)[symmetric]]
  using mult_copy_first_matrix[OF `j<nr`, of "evaluate_net m input", unfolded dim_vec_of_list]
  assms(3) copy_first_matrix_dim(1) by (metis \<open>output_size' m = dim_vec (evaluate_net m input)\<close> assms(4))

lemma tensors_from_net_Conv_copy_first:
assumes "valid_net' m"
and "i<nr"
and "output_size' m > 0"
shows "tensors_from_net (Conv (copy_first_matrix nr (output_size' m)) m) $ i = tensors_from_net m $ 0"
  (is "?a $ i = ?b")
proof (rule tensor_lookup_eqI)
  have "Tensor.dims (?a$i) = input_sizes m"
    by (metis assms(1) assms(2) copy_first_matrix_dim(1) copy_first_matrix_dim(2) dims_tensors_from_net
    input_sizes.simps(2) output_size.simps(2) output_size_correct_tensors remove_weights.simps(2)
    valid_net.intros(2) vec_setI)
  moreover have "Tensor.dims (?b) = input_sizes m" using dims_tensors_from_net
    output_size_correct_tensors[OF assms(1)] using assms(3) by (simp add: vec_setI)
  ultimately show "Tensor.dims (?a$i) = Tensor.dims (?b)" by auto

  define Convm where "Convm = Conv (copy_first_matrix nr (output_size' m)) m"
  fix "is"
  assume "is \<lhd> Tensor.dims (?a$i)"
  then have "is \<lhd> input_sizes m" using `Tensor.dims (?a$i) = input_sizes m` by auto
  have "valid_net' Convm" by (simp add: assms copy_first_matrix_dim valid_net.intros(2) Convm_def)
  have "base_input m is = base_input Convm is" by (simp add: Convm_def base_input_def)
  have "i < output_size' Convm" unfolding Convm_def remove_weights.simps output_size.simps
    copy_first_matrix_dim using assms by metis
  show "Tensor.lookup (?a $ i) is = Tensor.lookup ?b is"
    by (metis Convm_def \<open>base_input m is = base_input Convm is\<close> \<open>i < output_size' Convm\<close>
    \<open>is \<lhd> input_sizes m\<close> \<open>valid_net' Convm\<close> assms(1) assms(2) assms(3) base_input_length
    evaluate_net_Conv_copy_first input_sizes.simps(2) lookup_tensors_from_net)
qed

lemma evaluate_net_Conv_all1:
assumes "valid_net' m"
and "input_sizes m = map dim_vec input"
and "i<nr"
shows "evaluate_net (Conv (all1_matrix nr (output_size' m)) m) input $ i
 = Groups_List.sum_list (list_of_vec (evaluate_net m input))"
  unfolding evaluate_net.simps output_size_correct[OF assms(1) assms(2)[symmetric]]
  using mult_all1_matrix[OF `i<nr`, of "evaluate_net m input", unfolded dim_vec_of_list]
  assms(3) all1_matrix_dim(1) by metis

lemma tensors_from_net_Conv_all1:
assumes "valid_net' m"
and "i<nr"
shows "tensors_from_net (Conv (all1_matrix nr (output_size' m)) m) $ i
 = listsum (input_sizes m) (list_of_vec (tensors_from_net m))"
  (is "?a $ i = ?b")
proof (rule tensor_lookup_eqI)
  have "i < dim_vec ?a" by (metis assms all1_matrix_dim output_size.simps(2)
    output_size_correct_tensors remove_weights.simps(2) valid_net.intros(2))
  then show "Tensor.dims (?a $ i) = Tensor.dims (?b)"
    using dims_tensors_from_net input_sizes.simps(2) listsum_dims
    by (metis index_vec_of_list in_set_conv_nth length_list_of_vec vec_list vec_setI)

  define Convm where "Convm = Conv (all1_matrix nr (output_size' m)) m"
  fix "is" assume "is \<lhd> Tensor.dims (?a $ i)"
  then have "is \<lhd> input_sizes m"
    using \<open>i < dim_vec ?a\<close> dims_tensors_from_net input_sizes.simps(2) by (metis vec_setI)
  then have "is \<lhd> input_sizes Convm" by (simp add: Convm_def)
  have "valid_net' Convm" by (simp add: Convm_def assms all1_matrix_dim valid_net.intros(2))
  have "i< output_size' Convm" using Convm_def \<open>i < dim_vec ?a\<close> \<open>valid_net' Convm\<close>
    output_size_correct_tensors by presburger
  have "base_input Convm is = base_input m is" unfolding base_input_def Convm_def input_sizes.simps by metis
  have "Tensor.lookup (?a $ i) is = evaluate_net Convm (base_input Convm is) $ i"
    using lookup_tensors_from_net[OF `valid_net' Convm` `is \<lhd> input_sizes Convm` `i< output_size' Convm`]
    by (metis Convm_def )
  also have "... = monoid_add_class.sum_list (list_of_vec (evaluate_net m (base_input Convm is)))"
    using evaluate_net_Conv_all1 Convm_def \<open>is \<lhd> input_sizes Convm\<close> assms base_input_length \<open>i < nr\<close>
    by simp
  also have "... = monoid_add_class.sum_list (list_of_vec (map_vec (\<lambda>A.  lookup A is)(tensors_from_net m)))"
    unfolding `base_input Convm is = base_input m is`
    using lookup_tensors_from_net[OF `valid_net' m` `is \<lhd> input_sizes m`]
     base_input_length[OF \<open>is \<lhd> input_sizes m\<close>] output_size_correct[OF assms(1)]  output_size_correct_tensors[OF assms(1)]
    eq_vecI[of "evaluate_net m (base_input m is)" "map_vec (\<lambda>A. lookup A is) (tensors_from_net m)"] index_map_vec(1) index_map_vec(2)
    by force
  also have "... = monoid_add_class.sum_list (map (\<lambda>A.  lookup A is) (list_of_vec (tensors_from_net m)))"
    using eq_vecI[of "vec_of_list (list_of_vec (map_vec (\<lambda>A.  lookup A is)(tensors_from_net m)))"
    "vec_of_list (map (\<lambda>A.  lookup A is) (list_of_vec (tensors_from_net m)))"]  dim_vec_of_list
    nth_list_of_vec length_map list_vec nth_map  index_map_vec(1) index_map_vec(2) vec_list
    by (metis (no_types, lifting))
  also have "... = Tensor.lookup ?b is"  using dims_tensors_from_net set_list_of_vec
    using lookup_listsum[OF `is \<lhd> input_sizes m`, of "list_of_vec (tensors_from_net m)"]
    by metis
  finally show "Tensor.lookup (?a $ i) is = Tensor.lookup ?b is" by blast
qed

fun witness and witness' where
"witness' Y [] = Input Y" |
"witness' Y (r # rs) = Pool (witness Y r rs) (witness Y r rs)" |
"witness Y r rs = Conv ((if length rs = 0 then id_matrix else (if length rs = 1 then all1_matrix else copy_first_matrix)) Y r) (witness' r rs)"

abbreviation "witness_l rs == witness (rs!0) (rs!1) (tl (tl rs))"
abbreviation "witness'_l rs == witness' (rs!0) (tl rs)"

lemma witness_is_deep_model: "remove_weights (witness Y r rs) = deep_model Y r rs"
proof (induction rs arbitrary: Y r)
  case Nil
  then show ?case unfolding witness.simps witness'.simps deep_model.simps deep_model'.simps
    by (simp add: id_matrix_dim)
next
  case (Cons r' rs Y r)
  have "dim_row ((if length (r' # rs) = 0 then id_matrix else (if length (r' # rs) = 1 then all1_matrix else copy_first_matrix)) Y r) = Y"
       "dim_col ((if length (r' # rs) = 0 then id_matrix else (if length (r' # rs) = 1 then all1_matrix else copy_first_matrix)) Y r) = r"
    by (simp_all add: all1_matrix_dim copy_first_matrix_dim)
  then show ?case unfolding witness.simps unfolding witness'.simps unfolding remove_weights.simps
    using Cons by simp
qed

lemma witness'_is_deep_model: "remove_weights (witness' Y rs) = deep_model' Y rs"
proof (induction rs arbitrary: Y)
  case Nil
  then show ?case unfolding witness.simps witness'.simps deep_model.simps deep_model'.simps
    by (simp add: id_matrix_dim)
next
  case (Cons r rs Y)
  have "dim_row ((if length rs = 0 then id_matrix else (if length rs = 1 then all1_matrix else copy_first_matrix)) Y r) = Y"
       "dim_col ((if length rs = 0 then id_matrix else (if length rs = 1 then all1_matrix else copy_first_matrix)) Y r) = r"
    by (simp_all add: all1_matrix_dim copy_first_matrix_dim id_matrix_dim)
  then show ?case unfolding witness'.simps unfolding witness.simps unfolding remove_weights.simps
    using Cons by simp
qed

lemma witness_valid: "valid_net' (witness Y r rs)"
  using valid_deep_model witness_is_deep_model by auto

lemma witness'_valid: "valid_net' (witness' Y rs)"
  using valid_deep_model' witness'_is_deep_model by auto

lemma shared_weight_net_witness: "shared_weight_net (witness Y r rs)"
proof (induction rs arbitrary:Y r)
case Nil
  then show ?case unfolding witness.simps witness'.simps by (simp add: shared_weight_net_Conv shared_weight_net_Input)
next
  case (Cons a rs)
  then show ?case unfolding witness.simps witness'.simps
    by (simp add: shared_weight_net_Conv shared_weight_net_Input shared_weight_net_Pool)
qed 

lemma witness_l0': "witness' Y [M] =
    (Pool
      (Conv (id_matrix Y M) (Input M))
      (Conv (id_matrix Y M) (Input M))
    )"
unfolding witness'.simps witness.simps by simp

lemma witness_l1: "witness Y r0 [M] =
  Conv (all1_matrix Y r0) (witness' r0 [M])"
unfolding witness'.simps by simp

lemma tensors_ht_l0:
assumes "j<r0"
shows "tensors_from_net (Conv (id_matrix r0 M) (Input M)) $ j
 = (if j<M then unit_vec M j else tensor0 [M])"
  by (metis assms input_sizes.simps(1) output_size.simps(1) remove_weights.simps(1) tensors_from_net.simps(1)
  tensors_from_net_Conv_id valid_net.intros(1) index_vec)

lemma tensor_prod_unit_vec:
"unit_vec M j \<otimes> unit_vec M j = tensor_from_lookup [M,M] (\<lambda>is. if is=[j,j] then 1 else 0)" (is "?A=?B")
proof (rule tensor_lookup_eqI)
  show "Tensor.dims ?A = Tensor.dims ?B"
    by (metis append_Cons self_append_conv2 dims_unit_vec dims_tensor_prod dims_tensor_from_lookup)
  fix "is" assume is_valid:"is \<lhd> Tensor.dims (unit_vec M j \<otimes> unit_vec M j)"
  then have "is \<lhd> [M,M]" by (metis append_Cons self_append_conv2 dims_unit_vec dims_tensor_prod)
  then obtain i1 i2 where is_split: "is = [i1, i2]" "i1 < M" "i2 < M" using list.distinct(1) by blast
  then have "[i1] \<lhd> Tensor.dims (unit_vec M j)" "[i2] \<lhd> Tensor.dims (unit_vec M j)"
    by (simp_all add: valid_index.Cons valid_index.Nil dims_unit_vec)
  have "is = [i1] @ [i2]" by (simp add: is_split(1))
  show "Tensor.lookup ?A is = Tensor.lookup ?B is"
     unfolding `is = [i1] @ [i2]`
     lookup_tensor_prod[OF `[i1] \<lhd> Tensor.dims (unit_vec M j)` `[i2] \<lhd> Tensor.dims (unit_vec M j)`]
     lookup_tensor_from_lookup[OF \<open>is \<lhd> [M, M]\<close>, unfolded  `is = [i1] @ [i2]`]
     lookup_unit_vec[OF \<open>i1 < M\<close>] lookup_unit_vec[OF \<open>i2 < M\<close>] by fastforce
qed

lemma tensors_ht_l0':
assumes "j<r0"
shows "tensors_from_net (witness' r0 [M]) $ j
 = (if j<M then unit_vec M j \<otimes> unit_vec M j else tensor0 [M,M])" (is "_ = ?b")
proof -
  have "valid_net' (Conv (id_matrix r0 M) (Input M))"
    by (metis convnet.inject(3) list.discI witness'.elims witness_l0' witness_valid)
  have j_le:"j < dim_vec (tensors_from_net (Conv (id_matrix r0 M) (Input M)))"
    using output_size_correct_tensors[OF `valid_net' (Conv (id_matrix r0 M) (Input M))`,
    unfolded remove_weights.simps output_size.simps id_matrix_dim]
    assms by simp
  show ?thesis
    unfolding tensors_from_net.simps(3) witness_l0' index_component_mult[OF j_le j_le]  tensors_ht_l0[OF assms]
    by auto
qed

lemma lookup_tensors_ht_l0':
assumes "j<r0"
and "is \<lhd> [M,M]"
shows "(Tensor.lookup (tensors_from_net (witness' r0 [M]) $ j)) is = (if is=[j,j] then 1 else 0)"

proof (cases "j<M")
  assume "j<M"
  show ?thesis unfolding tensors_ht_l0'[OF assms(1)] tensor_prod_unit_vec
    apply (cases "is = [j,j]")  using `j<M` assms(2)
    by (simp_all add:lookup_tensor_from_lookup)
next
  assume "\<not>j<M"
  then have "is \<noteq> [j, j]" using assms(2) using list.distinct(1) nth_Cons_0 valid_index.simps by blast
  show ?thesis unfolding tensors_ht_l0'[OF assms(1)] tensor_prod_unit_vec
    using  `\<not>j<M` by (simp add: lookup_tensor0[OF assms(2)] `is \<noteq> [j, j]`)
qed

lemma lookup_tensors_ht_l1:
assumes "j < r1"
and "is \<lhd> [M,M]"
shows "Tensor.lookup (tensors_from_net (witness r1 r0 [M]) $ j) is
   = (if is!0 = is!1 \<and> is!0<r0 then 1 else 0)"
proof -
  have witness_l0'_valid: "valid_net' (witness' r0 [M])" unfolding witness_l0'
    by (simp add: id_matrix_dim valid_net.intros)
  have "input_sizes (witness' r0 [M]) = [M,M]" unfolding witness_l0' by simp
  have "output_size' (witness' r0 [M]) = r0" unfolding witness_l0' using witness_l0'_valid
    by (simp add: id_matrix_dim)
  have "dim_vec (tensors_from_net (witness' r0 [M])) = r0"
    using \<open>output_size' (witness' r0 [M]) = r0\<close> witness_l0'_valid output_size_correct_tensors by fastforce
  have all0_but1:"\<And>i. i\<noteq>is!0 \<Longrightarrow> i<r0 \<Longrightarrow> Tensor.lookup (tensors_from_net (witness' r0 [M]) $ i) is = 0"
    using lookup_tensors_ht_l0' \<open>is \<lhd> [M, M]\<close> by auto



  have "tensors_from_net (witness r1 r0 [M]) $ j =
    Tensor_Plus.listsum [M,M] (list_of_vec (tensors_from_net (witness' r0 [M])))"
    unfolding witness_l1 using tensors_from_net_Conv_all1[OF witness_l0'_valid assms(1)]
    witness_l0' `output_size' (witness' r0 [M]) = r0` by simp
  then have "Tensor.lookup (tensors_from_net (witness r1 r0 [M]) $ j) is
    = monoid_add_class.sum_list (map (\<lambda>A. Tensor.lookup A is) (list_of_vec (tensors_from_net (witness' r0 [M]))))"
    using lookup_listsum[OF `is \<lhd> [M, M]`]  \<open>input_sizes (witness' r0 [M]) = [M, M]\<close>
    dims_tensors_from_net by (metis set_list_of_vec)
  also have "... = monoid_add_class.sum_list (map (\<lambda>i. lookup (tensors_from_net (witness' r0 [M]) $ i) is) [0..<r0])"
    using map_map[of "(\<lambda>A. Tensor.lookup A is)" "\<lambda>i. (tensors_from_net (witness' r0 [M]) $ i)" "[0..<r0]"]
    using list_of_vec_map `dim_vec (tensors_from_net (witness' r0 [M])) = r0` by (metis (mono_tags, lifting) comp_apply map_eq_conv)
  also have "... = (\<Sum>i<r0. Tensor.lookup ((tensors_from_net (witness' r0 [M])) $ i) is)"
    using sum_set_upt_conv_sum_list_nat atLeast0LessThan by (metis atLeast_upt)
  also have "... = (if is!0 = is!1 \<and> is!0<r0 then 1 else 0)"
  proof (cases "is!0<r0")
    case True
    have "finite {0..<r0}" by auto
    have "is!0 \<in> {0..<r0}" using True by auto
    have "(\<Sum>i<r0. Tensor.lookup ((tensors_from_net (witness' r0 [M])) $ i) is)
      = Tensor.lookup (tensors_from_net (witness' r0 [M]) $ (is!0)) is"
      using `dim_vec (tensors_from_net (witness' r0 [M])) = r0`
      using sum.remove[OF `finite {0..<r0}` `is!0 \<in> {0..<r0}`,
        of "\<lambda>i. (Tensor.lookup (tensors_from_net (witness' r0 [M])$i) is)"]
      using all0_but1 atLeast0LessThan by force
    then show ?thesis using lookup_tensors_ht_l0' \<open>is ! 0 < r0\<close> \<open>is \<lhd> [M, M]\<close> by fastforce
  next
    case False
    then show ?thesis using all0_but1 atLeast0LessThan sum.neutral by force
  qed
  finally show ?thesis by auto
qed

lemma length_output_deep_model:
assumes "remove_weights m = deep_model_l rs"
shows "dim_vec (tensors_from_net m) = rs ! 0"
  using output_size_correct_tensors valid_deep_model
   deep_model.elims output_size.simps(2) by (metis assms)

lemma length_output_deep_model':
assumes "remove_weights m = deep_model'_l rs"
shows "dim_vec (tensors_from_net m) = rs ! 0"
  using output_size_correct_tensors valid_deep_model'
   deep_model'.elims output_size.simps by (metis assms deep_model.elims)

lemma length_output_witness:
"dim_vec (tensors_from_net (witness_l rs)) = rs ! 0"
  using length_output_deep_model witness_is_deep_model by blast

lemma length_output_witness':
"dim_vec (tensors_from_net (witness'_l rs)) = rs ! 0"
  using length_output_deep_model' witness'_is_deep_model by blast

lemma dims_output_deep_model:
assumes "length rs \<ge> 2"
and "\<And>r. r\<in>set rs \<Longrightarrow> r > 0"
and "j < rs!0"
and "remove_weights m = deep_model_l rs"
shows "Tensor.dims (tensors_from_net m $ j) = replicate (2^(length rs - 2)) (last rs)"
  using dims_tensors_from_net input_sizes_deep_model[OF assms(1)] output_size_correct_tensors valid_deep_model
  assms(3) assms(4) input_sizes_remove_weights length_output_witness witness_is_deep_model by (metis vec_setI)

lemma dims_output_witness:
assumes "length rs \<ge> 2"
and "\<And>r. r\<in>set rs \<Longrightarrow> r > 0"
and "j < rs!0"
shows "Tensor.dims (tensors_from_net (witness_l rs) $ j) = replicate (2^(length rs - 2)) (last rs)"
  using dims_output_deep_model witness_is_deep_model assms by blast

lemma dims_output_deep_model':
assumes "length rs \<ge> 1"
and "\<And>r. r\<in>set rs \<Longrightarrow> r > 0"
and "j < rs!0"
and "remove_weights m = deep_model'_l rs"
shows "Tensor.dims (tensors_from_net m $ j) = replicate (2^(length rs - 1)) (last rs)"
proof -
  have "dim_vec (tensors_from_net m) > j"
    using length_output_deep_model' `remove_weights m = deep_model'_l rs` `j < rs!0` by auto
  then have "Tensor.dims (tensors_from_net m $ j) = input_sizes m"
    using dims_tensors_from_net[of _ m] output_size_correct_tensors
    vec_setI by metis
  then show ?thesis
    using assms(1) input_sizes_deep_model'
    input_sizes_remove_weights[of m, unfolded `remove_weights m = deep_model'_l rs`] by auto
qed

lemma dims_output_witness':
assumes "length rs \<ge> 1"
and "\<And>r. r\<in>set rs \<Longrightarrow> r > 0"
and "j < rs!0"
shows "Tensor.dims (tensors_from_net (witness'_l rs) $ j) = replicate (2^(length rs - 1)) (last rs)"
using dims_output_deep_model' assms witness'_is_deep_model by blast

abbreviation "ten2mat == matricize {n. even n}"
abbreviation "mat2ten == dematricize {n. even n}"

locale deep_model_correct_params =
fixes shared_weights::bool
fixes rs::"nat list"
assumes deep:"length rs \<ge> 3"
and no_zeros:"\<And>r. r\<in>set rs \<Longrightarrow> 0 < r"
begin

definition "r = min (last rs) (last (butlast rs))"
definition "N_half = 2^(length rs - 3)"
definition "weight_space_dim = count_weights shared_weights (deep_model_l rs)"

end

locale deep_model_correct_params_y = deep_model_correct_params +
fixes y::nat
assumes y_valid:"y < rs ! 0"
begin


definition A :: "(nat \<Rightarrow> real) \<Rightarrow> real tensor"
  where "A ws = tensors_from_net (insert_weights shared_weights (deep_model_l rs) ws) $ y"
definition A' :: "(nat \<Rightarrow> real) \<Rightarrow> real mat"
  where "A' ws = ten2mat (A ws)"


lemma dims_tensor_deep_model:
assumes "remove_weights m = deep_model_l rs"
shows "dims (tensors_from_net m $ y) = replicate (2 * N_half) (last rs)"
proof -
  have "dims (tensors_from_net m $ y) = replicate (2 ^ (length rs - 2)) (last rs)"
    using dims_output_deep_model[OF _ no_zeros y_valid assms] using less_imp_le_nat Suc_le_lessD deep numeral_3_eq_3
    by auto
  then show ?thesis using N_half_def by (metis One_nat_def Suc_1 Suc_eq_plus1 Suc_le_lessD deep
    diff_diff_left less_numeral_extra(3) numeral_3_eq_3 power_eq_if zero_less_diff)
qed

lemma order_tensor_deep_model:
assumes "remove_weights m = deep_model_l rs"
shows "order (tensors_from_net m $ y) = 2 * N_half"
  using dims_tensor_deep_model by (simp add: assms)

lemma dims_A:
shows "Tensor.dims (A ws) = replicate (2 * N_half) (last rs)"
  unfolding A_def
  using dims_tensor_deep_model remove_insert_weights by blast

lemma order_A:
shows "order (A ws) = 2 * N_half" using dims_A length_replicate by auto

lemma dims_A':
shows "dim_row (A' ws) = prod_list (nths (Tensor.dims (A ws)) {n. even n})"
and "dim_col (A' ws) = prod_list (nths (Tensor.dims (A ws)) {n. odd n})"
  unfolding A'_def matricize_def by (simp_all add: A_def Collect_neg_eq)

lemma dims_A'_pow:
shows "dim_row (A' ws) = (last rs) ^ N_half" "dim_col (A' ws) = (last rs) ^ N_half"
  unfolding dims_A' dims_A nths_replicate set_le_in card_even card_odd prod_list_replicate
  by simp_all



definition "Aw = tensors_from_net (witness_l rs) $ y"
definition "Aw' = ten2mat Aw"

definition "witness_weights = extract_weights shared_weights (witness_l rs)"

lemma witness_weights:"witness_l rs = insert_weights shared_weights (deep_model_l rs) witness_weights"
  by (metis (full_types) insert_extract_weights_cong_shared insert_extract_weights_cong_unshared shared_weight_net_witness witness_is_deep_model witness_weights_def)

lemma Aw_def': "Aw = A witness_weights" unfolding Aw_def A_def using witness_weights by auto

lemma Aw'_def': "Aw' = A' witness_weights" unfolding Aw'_def A'_def Aw_def' by auto

lemma dims_Aw: "Tensor.dims Aw = replicate (2 * N_half) (last rs)"
  unfolding Aw_def' using dims_A by auto

lemma order_Aw: "order Aw = 2 * N_half"
  unfolding Aw_def' using order_A by auto

lemma dims_Aw':
"dim_row Aw' = prod_list (nths (Tensor.dims Aw) {n. even n})"
"dim_col Aw' = prod_list (nths (Tensor.dims Aw) {n. odd n})"
  unfolding Aw'_def' Aw_def' using dims_A' by auto

lemma dims_Aw'_pow: "dim_row Aw' = (last rs) ^ N_half" "dim_col Aw' = (last rs) ^ N_half"
  unfolding Aw'_def' Aw_def' using dims_A'_pow by auto

lemma witness_tensor:
assumes "is \<lhd> Tensor.dims Aw"
shows "Tensor.lookup Aw is
   = (if nths is {n. even n} = nths is {n. odd n} \<and> (\<forall>i\<in>set is. i < last (butlast rs)) then 1 else 0)"
using assms deep no_zeros y_valid unfolding Aw_def proof (induction "butlast (butlast (butlast rs))" arbitrary:rs "is" y)
  case Nil
  have "length rs = 3"
    by (rule antisym, metis Nil.hyps One_nat_def Suc_1 Suc_eq_plus1 add_2_eq_Suc' diff_diff_left
      length_butlast less_numeral_extra(3) list.size(3) not_le numeral_3_eq_3 zero_less_diff, metis `3 \<le> length rs`)
  then have "rs = [rs!0, rs!1, rs!2]" by (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc_eq_plus1
    append_Nil id_take_nth_drop length_0_conv length_tl lessI list.sel(3) list.size(4) not_le numeral_3_eq_3
    numeral_le_one_iff one_add_one semiring_norm(70) take_0 zero_less_Suc)
  have "input_sizes (witness_l [rs ! 0, rs ! 1, rs ! 2]) = [rs!2, rs!2]"
    using witness.simps  witness'.simps input_sizes.simps by auto
  then have "Tensor.dims (tensors_from_net (witness_l rs) $ y) = [rs!2, rs!2]"
    using dims_tensors_from_net[of "tensors_from_net (witness_l rs) $ y" "witness_l rs"]
      Nil.prems(4) length_output_witness \<open>rs = [rs ! 0, rs ! 1, rs ! 2]\<close> vec_setI by metis
  then have "is \<lhd> [rs!2, rs!2]" using Nil.prems by metis
  then have "Tensor.lookup ((tensors_from_net (witness_l rs))$y) is
    = (if is ! 0 = is ! 1 \<and> is ! 0 < rs ! 1 then 1 else 0)"
    using Nil.prems(4) \<open>rs = [rs ! 0, rs ! 1, rs ! 2]\<close> by (metis list.sel(3) lookup_tensors_ht_l1)
  have "is ! 0 = is ! 1 \<and> is ! 0 < rs ! 1
    \<longleftrightarrow> nths is {n. even n} = nths is {n. odd n} \<and> (\<forall>i\<in>set is. i < last (butlast rs))"
  proof -
    have "length is = 2" by (metis One_nat_def Suc_eq_plus1 \<open>is \<lhd> [rs ! 2, rs ! 2]\<close> list.size(3) list.size(4) numeral_2_eq_2 valid_index_length)
    have "nths is {n. even n} = [is!0]"
      apply (rule nths_only_one)
      using subset_antisym less_2_cases `length is = 2` by fastforce
    have "nths is {n. odd n} = [is!1]"
      apply (rule nths_only_one)
      using subset_antisym less_2_cases `length is = 2` by fastforce
    have "last (butlast rs) = rs!1" by (metis One_nat_def Suc_eq_plus1 \<open>rs = [rs ! 0, rs ! 1, rs ! 2]\<close>
      append_butlast_last_id last_conv_nth length_butlast length_tl lessI list.sel(3) list.simps(3)
      list.size(3) list.size(4) nat.simps(3) nth_append)
    show ?thesis unfolding `last (butlast rs) = rs!1`
      apply (rule iffI; rule conjI)
         apply (simp add: \<open>nths is (Collect even) = [is ! 0]\<close> \<open>nths is {n. odd n} = [is ! 1]\<close>)
        apply (metis `length is = 2` One_nat_def in_set_conv_nth less_2_cases)
      apply (simp add: \<open>nths is (Collect even) = [is ! 0]\<close> \<open>nths is {n. odd n} = [is ! 1]\<close>)
     apply (simp add: \<open>length is = 2\<close>)
    done
  qed
  then show ?case unfolding \<open>Tensor.lookup (tensors_from_net (witness_l rs) $ y) is = (if is ! 0 = is ! 1 \<and> is ! 0 < rs ! 1 then 1 else 0)\<close>
    using witness_is_deep_model witness_valid \<open>rs = [rs ! 0, rs ! 1, rs ! 2]\<close> by auto
next
  case (Cons r rs' rs "is" j)

  text \<open>We prove the Induction Hypothesis for "tl rs" and j=0:\<close>

  have "rs = r # tl rs" by (metis Cons.hyps(2) append_butlast_last_id butlast.simps(1) hd_append2 list.collapse list.discI list.sel(1))
  have 1:"rs' = butlast (butlast (butlast (tl rs)))" by (metis Cons.hyps(2) butlast_tl list.sel(3))
  have 2:"3 \<le> length (tl rs)" by (metis (no_types, lifting) Cons.hyps(2) Cons.prems(2)
    Nitpick.size_list_simp(2) One_nat_def Suc_eq_plus1 \<open>rs = r # tl rs\<close> \<open>rs' = butlast (butlast (butlast (tl rs)))\<close>
    diff_diff_left diff_self_eq_0 gr0_conv_Suc le_Suc_eq length_butlast length_tl less_numeral_extra(3) list.simps(3) numeral_3_eq_3)
  have 3:"\<And>r. r \<in> set (tl rs) \<Longrightarrow> 0 < r" by (metis Cons.prems(3) list.sel(2) list.set_sel(2))
  have 4:"0 < (tl rs) ! 0" using "2" "3" by auto
  have IH: "\<And>is'. is' \<lhd> Tensor.dims (tensors_from_net (witness_l (tl rs)) $ 0)
    \<Longrightarrow> Tensor.lookup (tensors_from_net (witness_l (tl rs)) $ 0) is' =
    (if nths is' (Collect even) = nths is' {n. odd n} \<and> (\<forall>i\<in>set is'. i < last (butlast (tl rs))) then 1 else 0)"
      using "1" "2" "3" 4 Cons.hyps(1) by blast

  text \<open>The list "is" can be split in two parts:\<close>

  have "is \<lhd> replicate (2^(length rs - 2)) (last rs)"
    using Cons.prems(3) dims_output_witness 2 by (metis (no_types, lifting) Cons.prems(1) Cons.prems(3)
    Cons.prems(4) Nitpick.size_list_simp(2) One_nat_def diff_diff_left diff_is_0_eq length_tl
    nat_le_linear not_numeral_le_zero numeral_le_one_iff one_add_one semiring_norm(70))
  then have "is \<lhd> replicate (2^(length (tl rs) - 2)) (last rs) @ replicate (2^(length (tl rs) - 2)) (last rs)"
    using Cons.prems dims_output_witness by (metis "2" Nitpick.size_list_simp(2) One_nat_def
    diff_diff_left length_tl mult_2 not_numeral_le_zero numeral_le_one_iff one_add_one
    power.simps(2) replicate_add semiring_norm(70))
  then obtain is1 is2 where "is = is1 @ is2" and
    is1_replicate: "is1 \<lhd> replicate (2^(length (tl rs) - 2)) (last rs)" and
    is2_replicate: "is2 \<lhd> replicate (2^(length (tl rs) - 2)) (last rs)" by (metis valid_index_split)
  then have
    is1_valid: "is1 \<lhd> Tensor.dims (tensors_from_net (witness_l (tl rs)) $ 0)" (is ?is1) and
    is2_valid: "is2 \<lhd> Tensor.dims (tensors_from_net (witness_l (tl rs)) $ 0)" (is ?is2)
  proof -
    have "last (tl rs) = last rs" by (metis "2" \<open>rs = r # tl rs\<close> last_ConsR list.size(3) not_numeral_le_zero)
    then show ?is1 ?is2 using dims_output_witness[of "tl rs"]
      using dims_output_witness[of "tl rs"] 2 3 is1_replicate is2_replicate \<open>last (tl rs) = last rs\<close> by auto
  qed

  text \<open>A shorthand for the condition to find a "1" in the tensor:\<close>
  let ?cond = "\<lambda>is rs. nths is {n. even n} = nths is {n. odd n} \<and> (\<forall>i\<in>set is. i < last (butlast rs))"

  text \<open>We can use the IH on our newly created is1 and is2:\<close>
  have IH_is12:
    "Tensor.lookup (tensors_from_net (witness_l (tl rs)) $ 0) is1 =
      (if (?cond is1 (tl rs)) then 1 else 0)"
    "Tensor.lookup (tensors_from_net (witness_l (tl rs)) $ 0) is2 =
      (if (?cond is2 (tl rs)) then 1 else 0)"
    using IH is1_valid is2_valid by fast+

  text \<open>In the induction step we have to add two layers: first the Pool layer, then the Conv layer.

        The Pool layer connects the two subtrees. Therefore the two conditions on is1 and is2 become
        one, and we have to prove that they are equivalent:\<close>
  have "?cond is1 (tl rs) \<and> ?cond is2 (tl rs) \<longleftrightarrow> ?cond is rs"
  proof -
    have "length is1 = 2 ^ (length (tl rs) - 2)"
         "length is2 = 2 ^ (length (tl rs) - 2)"
      using is1_replicate is2_replicate by (simp_all add: valid_index_length)
    then have "even (length is1)" "even (length is2)"
      by (metis Cons.hyps(2) One_nat_def add_gr_0 diff_diff_left even_numeral even_power
      length_butlast length_tl list.size(4) one_add_one zero_less_Suc)+
    then have "{j. j + length is1 \<in> {n. even n}} = {n. even n}"
              "{j. j + length is1 \<in> {n. odd n}} = {n. odd n}" by simp_all
    have "length (nths is2 (Collect even)) = length (nths is2 (Collect odd))"
      using length_nths_even \<open>even (length is2)\<close> by blast
    have cond1_iff: "(nths is1 (Collect even) = nths is1 {n. odd n} \<and> nths is2 (Collect even) = nths is2 {n. odd n})
          = (nths is (Collect even) = nths is {n. odd n})"
        unfolding `is = is1 @ is2` nths_append
        `{j. j + length is1 \<in> {n. odd n}} = {n. odd n}` `{j. j + length is1 \<in> {n. even n}} = {n. even n}`
        by (simp add: \<open>length (nths is2 (Collect even)) = length (nths is2 (Collect odd))\<close>)
    have "last (butlast (tl rs)) = last (butlast rs)" using Nitpick.size_list_simp(2) \<open>even (length is1)\<close>
      \<open>length is1 = 2 ^ (length (tl rs) - 2)\<close> butlast_tl last_tl length_butlast length_tl not_less_eq zero_less_diff
      by (metis (full_types) Cons.hyps(2) length_Cons less_nat_zero_code)
    have cond2_iff: "(\<forall>i\<in>set is1. i < last (butlast (tl rs))) \<and> (\<forall>i\<in>set is2. i < last (butlast (tl rs))) \<longleftrightarrow> (\<forall>i\<in>set is. i < last (butlast rs))"
      unfolding `last (butlast (tl rs)) = last (butlast rs)` `is = is1 @ is2` set_append by blast
    then show ?thesis using cond1_iff cond2_iff by blast
  qed

  text \<open>Now we can make the Pool layer step: \<close>
  have lookup_witness': "Tensor.lookup ((tensors_from_net (witness' (rs ! 1) (tl (tl rs)))) $ 0) is =
    (if ?cond is rs then 1 else 0)"
  proof -
    have lookup_prod: "Tensor.lookup ((tensors_from_net (witness_l (tl rs)) $ 0) \<otimes> (tensors_from_net (witness_l (tl rs))) $ 0) is =
      (if ?cond is rs then 1 else 0)"
      using `?cond is1 (tl rs) \<and> ?cond is2 (tl rs) \<longleftrightarrow> ?cond is rs`
      unfolding `is = is1 @ is2` lookup_tensor_prod[OF is1_valid is2_valid] IH_is12
      by auto
    have witness_l_tl: "witness_l (tl rs) = witness (rs ! 1) (rs ! 2) (tl (tl (tl rs)))"
      by (metis One_nat_def Suc_1 \<open>rs = r # tl rs\<close> nth_Cons_Suc)
    have tl_tl:"(tl (tl rs)) = ((rs ! 2) # tl (tl (tl rs)))"
    proof -
      have "length (tl (tl rs)) \<noteq> 0"
        by (metis  One_nat_def Suc_eq_plus1 diff_diff_left diff_is_0_eq length_tl not_less_eq_eq
        Cons.prems(2) numeral_3_eq_3)
      then have "tl (tl rs) \<noteq> []"
        by fastforce
      then show ?thesis
        by (metis list.exhaust_sel nth_Cons_0 nth_Cons_Suc numeral_2_eq_2 tl_Nil)
    qed
    have length_gt0:"dim_vec (tensors_from_net (witness (rs ! 1) (rs ! 2) (tl (tl (tl rs))))) > 0"
      using output_size_correct_tensors[of "witness (rs ! 1) (rs ! 2) (tl (tl (tl rs)))"]
      witness_is_deep_model[of "rs ! 1" "rs ! 2" "tl (tl (tl rs))"]
      valid_deep_model[of "rs ! 1" "rs ! 2" "tl (tl (tl rs))"] output_size.simps witness.simps
      by (metis "2" "3" One_nat_def \<open>rs = r # tl rs\<close> deep_model.elims length_greater_0_conv list.size(3)
      not_numeral_le_zero nth_Cons_Suc nth_mem)
    then have "tensors_from_net (witness' (rs ! 1) ((rs ! 2) # tl (tl (tl rs)))) $ 0
       = (tensors_from_net (witness_l (tl rs)) $ 0) \<otimes> (tensors_from_net (witness_l (tl rs)) $ 0)"
      unfolding witness'.simps tensors_from_net.simps witness_l_tl using index_component_mult by blast
    then show ?thesis using lookup_prod tl_tl by simp
  qed

  text \<open>Then we can make the Conv layer step: \<close>
  show ?case
  proof -
    have "valid_net' (witness' (rs ! 1) (tl (tl rs)))" by (simp add: witness'_valid)
    have "output_size' (witness' (rs ! 1) (tl (tl rs))) = rs ! 1"
      by (metis "2" Nitpick.size_list_simp(2) diff_diff_left diff_is_0_eq hd_Cons_tl deep_model'.simps(2) deep_model.elims length_tl not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3 one_add_one output_size.simps(2) output_size.simps(3) tl_Nil witness'_is_deep_model)
    have if_resolve:"(if length (tl (tl rs)) = 0 then id_matrix else if length (tl (tl rs)) = 1 then all1_matrix else copy_first_matrix) = copy_first_matrix"
      by (metis "2" Cons.prems(2) Nitpick.size_list_simp(2) One_nat_def Suc_n_not_le_n not_numeral_le_zero numeral_3_eq_3)
    have "tensors_from_net (Conv (copy_first_matrix (rs ! 0) (rs ! 1)) (witness' (rs ! 1) (tl (tl rs)))) $ j =
      tensors_from_net (witness' (rs ! 1) (tl (tl rs))) $ 0"
      using tensors_from_net_Conv_copy_first[OF `valid_net' (witness' (rs ! 1) (tl (tl rs)))` `j < rs ! 0`, unfolded `output_size' (witness' (rs ! 1) (tl (tl rs))) = rs ! 1`]
      using "4" One_nat_def \<open>rs = r # tl rs\<close> nth_Cons_Suc by metis
    then show ?thesis unfolding witness.simps if_resolve `output_size' (witness' (rs ! 1) (tl (tl rs))) = rs ! 1`
      using lookup_witness' \<open>valid_net' (witness' (rs ! 1) (tl (tl rs)))\<close> hd_conv_nth output_size_correct_tensors
      by fastforce
  qed
qed

lemma witness_matricization:
assumes "i < dim_row Aw'" and "j < dim_col Aw'"
shows "Aw' $$ (i, j)
 = (if i=j \<and> (\<forall>i0\<in>set (digit_encode (nths (Tensor.dims Aw) {n. even n}) i). i0 < last (butlast rs)) then 1 else 0)"
proof -
  define "is" where "is = weave {n. even n}
    (digit_encode (nths (Tensor.dims Aw) {n. even n}) i)
    (digit_encode (nths (Tensor.dims Aw) {n. odd n}) j)"
  have lookup_eq: "Aw' $$ (i, j) = Tensor.lookup Aw is"
    using Aw'_def matricize_def dims_Aw'(1)[symmetric, unfolded A_def] dims_Aw'(2)[symmetric, unfolded A_def Collect_neg_eq]
    index_mat(1)[OF `i < dim_row Aw'` `j < dim_col Aw'`] is_def Collect_neg_eq case_prod_conv
    by (metis (no_types) Aw'_def Collect_neg_eq  case_prod_conv is_def matricize_def)
  have "is \<lhd> Tensor.dims Aw"
    using is_def valid_index_weave A_def Collect_neg_eq assms digit_encode_valid_index
    dims_Aw' by metis

  have "even (order Aw)"
    unfolding Aw_def using assms dims_output_witness even_numeral le_eq_less_or_eq numeral_2_eq_2 numeral_3_eq_3 deep no_zeros y_valid by fastforce

  have nths_dimsAw: "nths (Tensor.dims Aw) (Collect even) = nths (Tensor.dims Aw) {n. odd n}"
  proof -
    have 0:"Tensor.dims (tensors_from_net (witness_l rs) $ y) = replicate (2 ^ (length rs - 2)) (last rs)"
      using dims_output_witness[OF _ no_zeros y_valid] using deep by linarith
    show ?thesis unfolding A_def
      using nths_replicate
      by (metis (no_types, lifting) "0" Aw_def \<open>even (order Aw)\<close> length_replicate length_nths_even)
  qed

  have "i = j \<longleftrightarrow> nths is (Collect even) = nths is {n. odd n}"
  proof
    have eq_lengths: "length (digit_encode (nths (Tensor.dims Aw) (Collect even)) i)
        = length (digit_encode (nths (Tensor.dims Aw) {n. odd n}) j)"
      unfolding length_digit_encode by (metis \<open>even (order Aw)\<close> length_nths_even)

    then show "i = j \<Longrightarrow> nths is (Collect even) = nths is {n. odd n}" unfolding is_def
      using nths_weave[of "digit_encode (nths (Tensor.dims Aw) (Collect even)) i"
      "Collect even" "digit_encode (nths (Tensor.dims Aw) {n. odd n}) j", unfolded eq_lengths, unfolded Collect_neg_eq[symmetric] card_even mult_2[symmetric] card_odd]
      nths_dimsAw by simp
    show "nths is (Collect even) = nths is {n. odd n} \<Longrightarrow> i = j" unfolding is_def
      using nths_weave[of "digit_encode (nths (Tensor.dims Aw) (Collect even)) i"
      "Collect even" "digit_encode (nths (Tensor.dims Aw) {n. odd n}) j", unfolded eq_lengths, unfolded Collect_neg_eq[symmetric] card_even mult_2[symmetric] card_odd]
      using \<open>nths (Tensor.dims Aw) (Collect even) = nths (Tensor.dims Aw) {n. odd n}\<close>
        deep no_zeros y_valid assms digit_decode_encode dims_Aw'
      by auto (metis digit_decode_encode_lt) 
  qed

  have "i=j \<Longrightarrow> set (digit_encode (nths (Tensor.dims Aw) {n. even n}) i) = set is"
    unfolding is_def nths_dimsAw
    using set_weave[of "(digit_encode (nths (Tensor.dims Aw) {n. odd n}) j)" "Collect even"
                       "(digit_encode (nths (Tensor.dims Aw) {n. odd n}) j)",
                    unfolded mult_2[symmetric] card_even Collect_neg_eq[symmetric] card_odd]
    Un_absorb card_even card_odd mult_2 by blast
  then show ?thesis unfolding lookup_eq
    using witness_tensor[OF `is \<lhd> Tensor.dims Aw`]
    by (simp add: A_def \<open>(i = j) = (nths is (Collect even) = nths is {n. odd n})\<close>)
qed


definition "rows_with_1 = {i. (\<forall>i0\<in>set (digit_encode (nths (Tensor.dims Aw) {n. even n}) i). i0 < last (butlast rs))}"

lemma card_low_digits:
assumes "m>0" "\<And>d. d\<in>set ds \<Longrightarrow> m \<le> d"
shows "card {i. i<prod_list ds \<and> (\<forall>i0\<in>set (digit_encode ds i). i0 < m)} = m ^ (length ds)"
using assms proof (induction ds)
  case Nil
  then show ?case using prod_list.Nil by simp
next
  case (Cons d ds)
  define low_digits
    where "low_digits ds i \<longleftrightarrow> i < prod_list ds \<and> (\<forall>i0\<in>set (digit_encode ds i). i0 < m)" for ds i
  have "card {i. low_digits ds i} = m ^ (length ds)" unfolding low_digits_def
    by (simp add: Cons.IH Cons.prems(1) Cons.prems(2))
  have "card {i. low_digits (d # ds) i} = card ({..<m} \<times> {i. low_digits ds i})"
  proof -
    define f where "f p = fst p + d * snd p" for p
    have "inj_on f ({..<m} \<times> {i. low_digits ds i})"
    proof (rule inj_onI)
      fix x y assume "x \<in> {..<m} \<times> {i. low_digits ds i}" "y \<in> {..<m} \<times> {i. low_digits ds i}" "f x = f y"
      then have "fst x<m" "fst y<m" by auto
      then have "fst x<d" "fst y<d" using Cons(3) by (meson list.set_intros(1) not_le order_trans)+
      then have "f x mod d = fst x" "f y mod d = fst y" unfolding f_def by simp_all
      have "f x div d = snd x"  "f y div d = snd y" using \<open>f x = f y\<close> \<open>f x mod d = fst x\<close> \<open>fst y < d\<close> f_def by auto
      show "x = y" using \<open>f x = f y\<close> \<open>f x div d = snd x\<close> \<open>f x mod d = fst x\<close> \<open>f y div d = snd y\<close> \<open>f y mod d = fst y\<close> prod_eqI by fastforce
    qed
    have "f ` ({..<m} \<times> {i. low_digits ds i}) = {i. low_digits (d # ds) i}"
    proof (rule subset_antisym; rule subsetI)
      fix x assume "x \<in> f ` ({..<m} \<times> {i. low_digits ds i})"
      then obtain i0 i1 where "x = i0 + d * i1" "i0 < m" "low_digits ds i1" using f_def by force
      then have "i0<d" using Cons(3) by (meson list.set_intros(1) not_le order_trans)
      show "x \<in> {i. low_digits (d # ds) i}" unfolding low_digits_def
      proof (rule; rule conjI)
        have "i1 < prod_list ds" "\<forall>i0\<in>set (digit_encode ds i1). i0 < m"
          using `low_digits ds i1` low_digits_def by auto
        show "x < prod_list (d # ds)" unfolding prod_list.Cons `x = i0 + d * i1` using `i0<d` `i1 < prod_list ds`
        proof -
          have "d \<noteq> 0"
            by (metis \<open>i0 < d\<close> gr_implies_not0)
          then have "(i0 + d * i1) div (d * prod_list ds) = 0"
            by (simp add: Divides.div_mult2_eq \<open>i0 < d\<close> \<open>i1 < prod_list ds\<close>)
          then show "i0 + d * i1 < d * prod_list ds"
            by (metis (no_types) \<open>i0 < d\<close> \<open>i1 < prod_list ds\<close> div_eq_0_iff gr_implies_not0 no_zero_divisors)
        qed
        show "\<forall>i0\<in>set (digit_encode (d # ds) x). i0 < m"
          using \<open>\<forall>i0\<in>set (digit_encode ds i1). i0 < m\<close> \<open>i0 < d\<close> \<open>i0 < m\<close> \<open>x = i0 + d * i1\<close> by auto
      qed
    next
      fix x assume "x \<in> {i. low_digits (d # ds) i}"
      then have "x < prod_list (d # ds)" "\<forall>i0\<in>set (digit_encode (d # ds) x). i0 < m" using low_digits_def by auto
      have "x mod d < m" using `\<forall>i0\<in>set (digit_encode (d # ds) x). i0 < m`[unfolded digit_encode.simps] by simp
      have "x div d < prod_list ds" using `x < prod_list (d # ds)`[unfolded prod_list.Cons]
        by (metis div_eq_0_iff div_mult2_eq mult_0_right not_less0)
      have "\<forall>i0\<in>set (digit_encode ds (x div d)). i0 < m" by (simp add: \<open>\<forall>i0\<in>set (digit_encode (d # ds) x). i0 < m\<close>)
      have "f ((x mod d),(x div d)) = x" by (simp add: f_def)
      show "x \<in> f ` ({..<m} \<times> {i. low_digits ds i})" by (metis SigmaI \<open>\<forall>i0\<in>set (digit_encode ds (x div d)). i0 < m\<close> \<open>f (x mod d, x div d) = x\<close> \<open>x div d < prod_list ds\<close> \<open>x mod d < m\<close> image_eqI lessThan_iff low_digits_def mem_Collect_eq)
    qed
    then have "bij_betw f ({..<m} \<times> {i. low_digits ds i}) {i. low_digits (d # ds) i}"
      by (simp add: \<open>inj_on f ({..<m} \<times> {i. low_digits ds i})\<close> bij_betw_def)
    then show ?thesis by (simp add: bij_betw_same_card)
  qed
  then show ?case unfolding `card {i. low_digits ds i} = m ^ (length ds)` card_cartesian_product using low_digits_def by simp
qed

lemma card_rows_with_1: "card {i\<in>rows_with_1. i<dim_row Aw'} = r ^ N_half"
proof -
  have 1:"{i\<in>rows_with_1. i<dim_row Aw'} = {i. i < prod_list (nths (Tensor.dims Aw) (Collect even)) \<and>
             (\<forall>i0\<in>set (digit_encode (nths (Tensor.dims Aw) (Collect even)) i). i0 < r)}" (is "?A = ?B")
  proof (rule subset_antisym; rule subsetI)
    fix i assume "i \<in> ?A"
    then have "i < dim_row Aw'" "\<forall>i0\<in>set (digit_encode (nths (Tensor.dims Aw) {n. even n}) i). i0 < last (butlast rs)"
      using rows_with_1_def by auto
    then have "i < prod_list (nths (dims Aw) (Collect even))" using dims_Aw' by linarith
    then have "digit_encode (nths (dims Aw) (Collect even)) i \<lhd> nths (dims Aw) (Collect even)"
      using digit_encode_valid_index by auto
    have "\<forall>i0\<in>set (digit_encode (nths (Tensor.dims Aw) {n. even n}) i). i0 < r"
    proof
      fix i0 assume 1:"i0 \<in> set (digit_encode (nths (dims Aw) (Collect even)) i)"
      then obtain k where "k < length (digit_encode (nths (dims Aw) (Collect even)) i)"
              "digit_encode (nths (dims Aw) (Collect even)) i ! k = i0" by (meson in_set_conv_nth)
      have "i0 < last (butlast rs)"
        using \<open>\<forall>i0\<in>set (digit_encode (nths (dims Aw) (Collect even)) i). i0 < last (butlast rs)\<close> 1 by blast
      have "set (nths (dims Aw) (Collect even)) \<subseteq> {last rs}" unfolding dims_Aw using subset_eq by fastforce
      then have "nths (dims Aw) (Collect even) ! k = last rs"
        using \<open>digit_encode (nths (dims Aw) (Collect even)) i \<lhd> nths (dims Aw) (Collect even)\<close>
        \<open>k < length (digit_encode (nths (dims Aw) (Collect even)) i)\<close>
        nth_mem valid_index_length by auto
      then have "i0 < last rs"
        using valid_index_lt \<open>digit_encode (nths (dims Aw) (Collect even)) i ! k = i0\<close>
        \<open>digit_encode (nths (dims Aw) (Collect even)) i \<lhd> nths (dims Aw) (Collect even)\<close>
        \<open>k < length (digit_encode (nths (dims Aw) (Collect even)) i)\<close> valid_index_length by fastforce
      then show "i0 < r" unfolding r_def by (simp add: \<open>i0 < last (butlast rs)\<close>)
    qed
    then show "i \<in> ?B" using \<open>i < prod_list (nths (dims Aw) (Collect even))\<close> by blast
  next
    fix i assume "i\<in>?B"
    then show "i\<in>?A" by (simp add: dims_Aw' r_def rows_with_1_def)
  qed
  have 2:"\<And>d. d \<in> set (nths (Tensor.dims Aw) (Collect even)) \<Longrightarrow> r \<le> d"
  proof -
    fix d assume "d \<in> set (nths (Tensor.dims Aw) (Collect even))"
    then have "d \<in> set (Tensor.dims Aw)" using in_set_nthsD by fast
    then have "d = last rs" using dims_Aw by simp
    then show "r \<le> d" by (simp add: r_def)
  qed
  have 3:"0 < r" unfolding r_def by (metis deep diff_diff_cancel diff_zero dual_order.trans in_set_butlastD last_in_set length_butlast list.size(3) min_def nat_le_linear no_zeros not_numeral_le_zero numeral_le_one_iff rel_simps(3))
  have 4: "length (nths (Tensor.dims Aw) (Collect even)) = N_half"
    unfolding length_nths order_Aw using card_even[of N_half]
    by (metis (mono_tags, lifting) Collect_cong)
  then show ?thesis using card_low_digits[of "r" "nths (Tensor.dims Aw) (Collect even)"] 1 2 3 4 by metis
qed


lemma infinite_rows_with_1: "infinite rows_with_1"
proof -
  define listpr where "listpr = prod_list (nths (Tensor.dims Aw) {n. even n})"
  have "\<And>i. listpr dvd i \<Longrightarrow> i \<in> rows_with_1"
  proof -
    fix i assume dvd_i: "listpr dvd i"
    {
      fix i0::nat
      assume "i0\<in>set (digit_encode (nths (Tensor.dims Aw) {n. even n}) i)"
      then have "i0=0" using digit_encode_0 dvd_i listpr_def by auto
      then have "i0 < last (butlast rs)" using deep no_zeros
      by (metis Nitpick.size_list_simp(2) One_nat_def Suc_le_lessD in_set_butlastD last_in_set length_butlast length_tl not_numeral_less_zero numeral_2_eq_2 numeral_3_eq_3 numeral_le_one_iff semiring_norm(70))
    }
    then show "i\<in>rows_with_1" by (simp add: rows_with_1_def)
  qed
  have 0:"Tensor.dims Aw = replicate (2 ^ (length rs - 2)) (last rs)" unfolding Aw_def
      using dims_output_witness[OF _ no_zeros y_valid]  using deep by linarith
  then have "listpr > 0" unfolding listpr_def 0
    by (metis "0" deep last_in_set length_greater_0_conv less_le_trans no_zeros dims_Aw'_pow(1) dims_Aw'(1)
    zero_less_numeral zero_less_power)
  then have "inj (( * ) listpr)" by (metis injI mult_left_cancel neq0_conv)
  then show ?thesis using `\<And>i. listpr dvd i \<Longrightarrow> i \<in> rows_with_1`
    by (meson dvd_triv_left image_subset_iff infinite_iff_countable_subset)
qed

lemma witness_submatrix: "submatrix Aw' rows_with_1 rows_with_1 = 1\<^sub>m (r^N_half)"
proof
  show "dim_row (submatrix Aw' rows_with_1 rows_with_1) = dim_row (1\<^sub>m (r ^ N_half))"
    unfolding index_one_mat(2) dim_submatrix(1)
    by (metis (full_types) set_le_in card_rows_with_1)
  show "dim_col (submatrix Aw' rows_with_1 rows_with_1) = dim_col (1\<^sub>m (r ^ N_half))"
    by (metis \<open>dim_row (submatrix Aw' rows_with_1 rows_with_1) = dim_row (1\<^sub>m (r ^ N_half))\<close> dim_submatrix(1) dim_submatrix(2) index_one_mat(2) index_one_mat(3) dims_Aw'_pow)
  show "\<And>i j. i < dim_row (1\<^sub>m (r ^ N_half)) \<Longrightarrow>
           j < dim_col (1\<^sub>m (r ^ N_half)) \<Longrightarrow> submatrix Aw' rows_with_1 rows_with_1 $$ (i, j) = 1\<^sub>m (r ^ N_half) $$ (i, j)"
  proof -
    fix i j assume "i < dim_row (1\<^sub>m (r ^ N_half))" "j < dim_col (1\<^sub>m (r ^ N_half))"
    then have "i < r ^ N_half" "j < r ^ N_half" by auto
    then have "i < card {i \<in> rows_with_1. i < dim_row Aw'}" "j < card {i \<in> rows_with_1. i < dim_col Aw'}"
      using card_rows_with_1 dims_Aw'_pow by auto
    then have "pick rows_with_1 i < dim_row Aw'" "pick rows_with_1 j < dim_col Aw'"
      using card_le_pick_inf[OF infinite_rows_with_1, of "dim_row Aw'" i]
      using card_le_pick_inf[OF infinite_rows_with_1, of "dim_col Aw'" j] by force+
    have "\<forall>i0\<in>set (digit_encode (nths (dims Aw) (Collect even)) (pick rows_with_1 i)). i0 < last (butlast rs)"
      using infinite_rows_with_1 pick_in_set_inf rows_with_1_def by auto
    then have "Aw' $$ (pick rows_with_1 i, pick rows_with_1 j) = (if pick rows_with_1 i = pick rows_with_1 j then 1 else 0)"
      using witness_matricization[OF `pick rows_with_1 i < dim_row Aw'` `pick rows_with_1 j < dim_col Aw'`] by simp
    then have "submatrix Aw' rows_with_1 rows_with_1 $$ (i, j) = (if pick rows_with_1 i = pick rows_with_1 j then 1 else 0)"
      using submatrix_index by (metis (no_types, lifting)
      \<open>dim_col (submatrix Aw' rows_with_1 rows_with_1) = dim_col (1\<^sub>m (r ^ N_half))\<close>
      \<open>dim_row (submatrix Aw' rows_with_1 rows_with_1) = dim_row (1\<^sub>m (r ^ N_half))\<close>
      \<open>i < dim_row (1\<^sub>m (r ^ N_half))\<close> \<open>j < r ^ N_half\<close> dim_submatrix(1) dim_submatrix(2) index_one_mat(3))
    then have "submatrix Aw' rows_with_1 rows_with_1 $$ (i, j) = (if i = j then 1 else 0)"
      using pick_eq_iff_inf[OF infinite_rows_with_1] by auto
    then show "submatrix Aw' rows_with_1 rows_with_1 $$ (i, j) = 1\<^sub>m (r ^ N_half) $$ (i, j)"
      by (simp add: \<open>i < r ^ N_half\<close> \<open>j < r ^ N_half\<close>)
  qed
qed

lemma witness_det: "det (submatrix Aw' rows_with_1 rows_with_1) \<noteq> 0" unfolding witness_submatrix by simp

end

(* Examples to show that the locales can be instantiated: *)

interpretation example : deep_model_correct_params False "[10,10,10]"
  unfolding deep_model_correct_params_def by simp

interpretation example : deep_model_correct_params_y False "[10,10,10]" 1
  unfolding deep_model_correct_params_y_def deep_model_correct_params_y_axioms_def 
  deep_model_correct_params_def by simp

end
