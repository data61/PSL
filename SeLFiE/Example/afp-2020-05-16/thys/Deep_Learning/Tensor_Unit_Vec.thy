(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Unit Vectors as Tensors\<close>

theory Tensor_Unit_Vec
imports Tensor_Product
begin

definition unit_vec::"nat \<Rightarrow> nat \<Rightarrow> 'a::ring_1 tensor"
where "unit_vec n i = tensor_from_lookup [n] (\<lambda>x. if x=[i] then 1 else 0)"

lemma dims_unit_vec: "dims (unit_vec n i) = [n]" unfolding unit_vec_def by (simp add: tensor_from_lookup_def)

lemma lookup_unit_vec:
assumes "j<n"
shows "lookup (unit_vec n i) [j] = (if i=j then 1 else 0)"
proof -
  have "[j] \<lhd> [n]" by (simp add: assms valid_index.Cons valid_index.Nil)
  then have "lookup (unit_vec n i) [j] = (\<lambda>x. if x=[i] then 1 else 0) [j]"
    by (simp add: lookup_tensor_from_lookup unit_vec_def)
  then show ?thesis by auto
qed

lemma subtensor_prod_with_unit_vec:
fixes A::"'a::ring_1 tensor"
assumes "j<n"
shows "subtensor (unit_vec n i \<otimes> A) j = (if i=j then A else (tensor0 (dims A)))"
proof -
  have 0:"lookup (unit_vec n i) [j] = (if i=j then 1 else 0)" unfolding unit_vec_def
    by (simp add: assms lookup_tensor_from_lookup valid_index.Cons valid_index.Nil)
  have 1:"order (unit_vec n i) = 1" unfolding unit_vec_def by (simp add: tensor_from_lookup_def)
  from assms have 2:"j < hd (dims (tensor_from_lookup [n] (\<lambda>x. if x = [i] then 1 else 0)))"
    by (simp add: dims_tensor_from_lookup)
  show ?thesis using unit_vec_def subtensor_prod_with_vec 1 2 0 smult_1 tensor_smult0
    by (metis (no_types, lifting) tensor_from_lookup_eqI)
qed

lemma subtensor_decomposition:
assumes "dims A \<noteq> []"
shows "listsum (dims A) (map (\<lambda>i. unit_vec (hd (dims A)) i \<otimes> subtensor A i) [0..<hd (dims A)]) = A" (is "?LS = A")
proof -
  let ?f = "\<lambda>i. unit_vec (hd (dims A)) i \<otimes> subtensor A i"
  have correct_dims:"\<And>B. B \<in> set (map ?f [0..<hd (dims A)]) \<Longrightarrow> dims B = dims A"
  proof-
    fix B
    assume "B \<in> set (map ?f [0..<hd (dims A)])"
    then obtain i where B:"B = ?f i" and "i<hd (dims A)" by auto
    then have "dims (subtensor A i) = tl (dims A)" using dims_subtensor using assms by blast
    then show "dims B = dims A" unfolding B
      by (metis append_Cons assms dims_tensor_prod dims_unit_vec list.exhaust_sel self_append_conv2)
  qed
  have "\<And>j. j < hd (dims A) \<Longrightarrow> subtensor ?LS j = subtensor A j"
  proof -
    fix j
    assume "j < hd (dims A)"
    have 1:"subtensor ?LS j = listsum (tl (dims A)) (map (\<lambda>A. subtensor A j) (map ?f [0..<hd (dims A)]))"
      using subtensor_listsum[of "(map (\<lambda>i. ?f i) [0..<hd (dims A)])" "dims A" j, OF correct_dims assms \<open>j < hd (dims A)\<close>]
      by linarith
    also have "... = listsum (tl (dims A)) (map (\<lambda>i. subtensor (?f i) j) [0..<hd (dims A)])"
    proof -
      have "map (\<lambda>A. subtensor A j) (map ?f [0..<hd (dims A)]) = map (\<lambda>i. subtensor (?f i) j) [0..<hd (dims A)]"
        unfolding map_map[of "(\<lambda>A. subtensor A j)" "?f" "[0..<hd (dims A)]"] by simp
      with 1 show ?thesis by metis
    qed
    also have "... =  map (\<lambda>i. if i = j then subtensor A i else tensor0 (dims (subtensor A i))) [0..<hd (dims A)] ! j"
      unfolding subtensor_prod_with_unit_vec[OF \<open>j < hd (dims A)\<close>]
      using listsum_all_0_but_one[of j "(map (\<lambda>i. if i = j then subtensor A i else tensor0 (dims (subtensor A i))) [0..<hd (dims A)])" "tl (dims A)"]
      by (simp add: \<open>j < hd (dims A)\<close> assms)
    also have "... = subtensor A j" by (simp add: \<open>j < hd (dims A)\<close>)
    finally show "subtensor ?LS j = subtensor A j" by auto
  qed
  moreover have "dims ?LS = dims A" using correct_dims listsum_dims by blast
  ultimately show ?thesis using subtensor_eqI by (metis (no_types, lifting) assms)
qed

end
