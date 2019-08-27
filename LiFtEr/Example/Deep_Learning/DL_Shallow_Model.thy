(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Shallow Network Model\<close>

theory DL_Shallow_Model
imports DL_Network Tensor_Rank
begin

fun shallow_model' where
"shallow_model' Z M 0 = Conv (Z,M) (Input M)" |
"shallow_model' Z M (Suc N) = Pool (shallow_model' Z M 0) (shallow_model' Z M N)"

definition shallow_model where
"shallow_model Y Z M N = Conv (Y,Z) (shallow_model' Z M N)"

lemma valid_shallow_model': "valid_net (shallow_model' Z M N)"
  apply (induction N) unfolding shallow_model'.simps
  by (simp add: valid_net.intros, metis shallow_model'.elims shallow_model'.simps(1) valid_net.intros output_size.simps)

lemma output_size_shallow_model': "output_size (shallow_model' Z M N) = Z"
  apply (induction N) unfolding shallow_model'.simps using output_size.simps by simp_all

lemma valid_shallow_model: "valid_net (shallow_model Y Z M N)"
  unfolding shallow_model_def using valid_shallow_model' valid_net.intros output_size.simps output_size_shallow_model' by metis

lemma output_size_shallow_model: "output_size (shallow_model Y Z M N) = Y"
  unfolding shallow_model_def using output_size_shallow_model' output_size.simps by simp

lemma input_sizes_shallow_model: "input_sizes (shallow_model Y Z M N) = replicate (Suc N) M"
  apply (induction N) unfolding shallow_model_def input_sizes.simps by simp_all

lemma balanced_net_shallow_model': "balanced_net (shallow_model' Z M N)"
proof(induction N)
case 0
  then show ?case
    by (metis balanced_net.simps shallow_model'.simps(1))
next
  case (Suc N)
  have "count_weights True (Conv (Z, M) (Input M)) = count_weights True (shallow_model' Z M N)"
    by (induction N; simp)
  then show ?case unfolding shallow_model'.simps 
  by (simp add: Suc.IH balanced_net_Conv balanced_net_Input balanced_net_Pool)
qed

lemma balanced_net_shallow_model: "balanced_net (shallow_model Y Z M N)" 
  unfolding shallow_model_def
  by (simp add: balanced_net_Conv balanced_net_shallow_model')

lemma cprank_max1_shallow_model':
assumes "y < output_size (shallow_model' Z M N)"
shows "cprank_max1 (tensors_from_net (insert_weights s (shallow_model' Z M N) w) $ y)"
  using assms proof (induction N arbitrary:w)
  case 0
  then have "input_sizes (insert_weights s (shallow_model' Z M 0) w) = [M]"
    unfolding shallow_model_def shallow_model'.simps insert_weights.simps
    input_sizes.simps by metis
  then have "dims (tensors_from_net (insert_weights s (shallow_model' Z M 0) w) $ y) = [M]"
    using dims_tensors_from_net[OF vec_setI] "0.prems"(1) output_size_correct_tensors
    remove_insert_weights valid_shallow_model' by metis
  then show ?case
    using order1 by (metis One_nat_def eq_imp_le length_Cons list.size(3))
next
  case (Suc N)
  have y_le_IH:"y < dim_vec (tensors_from_net (insert_weights s (shallow_model' Z M N) (\<lambda>i. w (i + (count_weights s (shallow_model' Z M 0))))))"
    using output_size_correct_tensors[of "insert_weights s (shallow_model' Z M N) (\<lambda>i. w (i + (count_weights s (shallow_model' Z M 0))))",
    unfolded remove_insert_weights, OF valid_shallow_model']
    using Suc.prems(1) output_size_shallow_model' by auto
  have cprank_max1_IH:"cprank_max1 (tensors_from_net (insert_weights s (shallow_model' Z M N) (\<lambda>i. w (i + (count_weights s (shallow_model' Z M 0))))) $ y)"
    using Suc.IH Suc.prems(1) output_size_shallow_model' by auto
  have y_le_0:"y < dim_vec (tensors_from_net (insert_weights s (shallow_model' Z M 0) w))"
    by (metis assms output_size_correct_tensors output_size_shallow_model' remove_insert_weights valid_shallow_model')
  have cprank_max1_0:"cprank_max1 (tensors_from_net (insert_weights s (shallow_model' Z M 0) w) $ y)"
  proof -
    have "input_sizes (insert_weights s (shallow_model' Z M 0) w) = [M]"
      unfolding shallow_model_def shallow_model'.simps insert_weights.simps
      input_sizes.simps by metis
    then show ?thesis using order1 dims_tensors_from_net[OF vec_setI]  One_nat_def eq_imp_le length_Cons list.size(3) y_le_0 by metis
  qed
  then show ?case unfolding shallow_model'.simps(2) insert_weights.simps tensors_from_net.simps
    using cprank_max1_IH cprank_max1_0 cprank_max1_prod index_component_mult y_le_0 y_le_IH 
    by (metis Suc.IH output_size_correct_tensors remove_insert_weights valid_shallow_model')
qed


lemma cprank_shallow_model:
assumes "m = insert_weights s (shallow_model Y Z M N) w"
assumes "y < Y"
shows "cprank (tensors_from_net m $ y) \<le> Z"
proof -
  have "s \<Longrightarrow> shared_weight_net m"
    by (simp add: assms(1) balanced_net_shallow_model shared_weight_net_insert_weights)
  have "cprank_max Z (tensors_from_net m $ y)"
  proof -
    have dim_extract: "dim_row (extract_matrix w Y Z) = Y"
      using dim_extract_matrix(1) by force
    have dimc_extract_matrix: "dim_col (extract_matrix w Y Z) = Z"
      using dim_extract_matrix(2) by force
    have input_sizes: "(input_sizes (insert_weights s (shallow_model' Z M N) (\<lambda>i. w (i + Y * Z)))) = (input_sizes (shallow_model' Z M N))"
      using input_sizes_remove_weights remove_insert_weights by auto
    have 0:"tensors_from_net m $ y = Tensor_Plus.listsum (input_sizes (shallow_model' Z M N))
      (map (\<lambda>j. (extract_matrix w Y Z)  $$ (y, j) \<cdot> (tensors_from_net (insert_weights s (shallow_model' Z M N) (\<lambda>i. w (i + Y * Z)))) $ j) [0..<Z])"
      unfolding `m = insert_weights s (shallow_model Y Z M N) w` shallow_model_def insert_weights.simps tensors_from_net.simps
      using nth_mat_tensorlist_mult dims_tensors_from_net assms(2) dim_extract output_size_correct_tensors[of "insert_weights s (shallow_model' Z M N) (\<lambda>i. w (i + Y * Z))", unfolded remove_insert_weights, OF valid_shallow_model']
      dimc_extract_matrix output_size_shallow_model' input_sizes by auto

    define Bs where "Bs = map (\<lambda>j. extract_matrix w Y Z $$ (y, j) \<cdot> tensors_from_net (insert_weights s (shallow_model' Z M N) (\<lambda>i. w (i + Y * Z))) $ j) [0..<Z]"

    have "\<And>B. B \<in> set Bs \<Longrightarrow> cprank_max1 B" "\<And>B. B \<in> set Bs \<Longrightarrow> dims B = input_sizes (shallow_model' Z M N)"
    proof -
      fix B assume "B \<in> set Bs"
      then obtain j where "B = Bs ! j" "j < length Bs" by (metis in_set_conv_nth)
      then have "j < Z" using length_map Bs_def by simp
      have 1:"cprank_max1 (tensors_from_net (insert_weights s (shallow_model' Z M N) (\<lambda>i. w (i + Y * Z))) $ j)"
        using \<open>j < Z\<close> output_size_shallow_model' cprank_max1_shallow_model' by auto
      then have "cprank_max1 (extract_matrix w Y Z $$ (y, j) \<cdot> tensors_from_net (insert_weights s (shallow_model' Z M N) (\<lambda>i. w (i + Y * Z))) $ j)"
        using smult_prod_extract1 cprank_max1_order0[OF 1, of "extract_matrix w Y Z $$ (y, j) \<cdot> 1"]
        by (metis dims_smult mult.left_neutral order_tensor_one)
      then show "cprank_max1 B" by (simp add: Bs_def \<open>B = Bs ! j\<close> \<open>j < Z\<close>)
      show "dims B = input_sizes (shallow_model' Z M N)" unfolding `B = Bs ! j` Bs_def
        nth_map[of j "[0..<Z]", unfolded length_upt Nat.diff_0, OF `j < Z`] dims_smult
        input_sizes[symmetric]
        by (rule dims_tensors_from_net; rule vec_setI[where i=j], simp add:\<open>j < Z\<close>, metis (no_types) \<open>j < Z\<close> output_size_correct_tensors output_size_shallow_model' remove_insert_weights valid_shallow_model')
    qed
    then show ?thesis unfolding 0 using cprank_maxI length_map Bs_def by (metis (no_types, lifting) diff_zero length_upt)
  qed
  then show ?thesis unfolding cprank_def by (simp add: Least_le)
qed


end
