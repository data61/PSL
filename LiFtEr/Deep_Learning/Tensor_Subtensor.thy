(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Subtensors\<close>

theory Tensor_Subtensor
imports Tensor
begin

definition subtensor::"'a tensor \<Rightarrow> nat \<Rightarrow> 'a tensor" where
  "subtensor A i = tensor_from_vec (tl (dims A)) (fixed_length_sublist (vec A) (prod_list (tl (dims A))) i)"

definition subtensor_combine::"nat list \<Rightarrow> 'a tensor list \<Rightarrow> 'a tensor" where
  "subtensor_combine ds As = tensor_from_vec (length As # ds) (concat (map vec As))"

lemma length_fixed_length_sublist[simp]:
assumes "(Suc i)*l \<le> length xs"
shows "length (fixed_length_sublist xs l i) = l"
  unfolding fixed_length_sublist_def
  by (metis assms diff_add_inverse2 length_drop length_take min.absorb2 mult.commute mult_Suc take_drop)

lemma vec_subtensor[simp]:
assumes "dims A \<noteq> []" and "i < hd (dims A)"
shows "vec (subtensor A i) = fixed_length_sublist (vec A) (prod_list (tl (dims A))) i"
  by (metis (no_types, lifting) Suc_leI assms(1) assms(2) hd_Cons_tl length_fixed_length_sublist length_vec prod_list.Cons mult_le_mono1 subtensor_def vec_tensor)

lemma dims_subtensor[simp]:
assumes "dims A \<noteq> []" and "i < hd (dims A)"
shows "dims (subtensor A i) = tl (dims A)"
  using Suc_leI assms(1) assms(2) dims_tensor length_fixed_length_sublist length_vec list.collapse prod_list.Cons mult_le_mono1 subtensor_def
  by metis

lemma subtensor_combine_subtensor[simp]:
assumes "dims A \<noteq> []"
shows "subtensor_combine (tl (dims A)) (map (subtensor A) [0..<hd (dims A)]) = A"
proof -
  have length_vec_A: "hd (dims A) * prod_list (tl (dims A)) = length (Tensor.vec A)"
    by (metis assms length_vec list.collapse prod_list.Cons)
  let ?subtensor_vec = "fixed_length_sublist (vec A) (prod_list (tl (dims A)))"
  {
    fix i assume "i < hd (dims A)"
    then have "(Suc i)*(prod_list (tl (dims A))) \<le> length (vec A)"
      by (metis Suc_leI length_vec_A mult_le_mono1)
    then have "(vec \<circ> (\<lambda>i. tensor_from_vec (tl (dims A)) (?subtensor_vec i))) i = ?subtensor_vec i"
      by simp
  }
  then have 1:"map (Tensor.vec \<circ> (\<lambda>i. tensor_from_vec (tl (dims A)) (?subtensor_vec i))) [0..<hd (dims A)]
              = map ?subtensor_vec [0..<hd (dims A)]" by auto
  then have "subtensor_combine (tl (dims A)) (map (\<lambda>i. subtensor A i) [0..<hd (dims A)]) = A"
    unfolding subtensor_combine_def subtensor_def using concat_parts_eq[OF length_vec_A]
    by (auto simp add: 1 assms)
  then show ?thesis by auto
qed

lemma
assumes "\<And>A. A\<in>set As \<Longrightarrow> dims A = ds"
shows subtensor_combine_dims[simp]: "dims (subtensor_combine ds As) = length As # ds" (is ?D)
and subtensor_combine_vec[simp]: "vec (subtensor_combine ds As) = concat (map vec As)" (is ?V)
proof -
  have "\<And>v. v\<in>set (map Tensor.vec As) \<Longrightarrow> length v = prod_list ds" using assms length_vec by fastforce
  then have "length As * prod_list ds = length (concat (map Tensor.vec As))" using concat_equal_length
    by (metis length_map)
  then show ?D ?V unfolding subtensor_combine_def by simp+
qed

lemma subtensor_subtensor_combine:
assumes "\<And>A. A\<in>set As \<Longrightarrow> dims A = ds" and "i < length As"
shows "subtensor (subtensor_combine ds As) i = As ! i"
proof -
  have "fixed_length_sublist (concat (map vec As)) (prod_list ds) i = vec (As ! i)"
    using concat_parts[of "map vec As" "prod_list ds" i] assms imageE length_map length_vec
    nth_map set_map in_set_conv_nth by fastforce
  then show ?thesis
    unfolding subtensor_def using subtensor_combine_dims subtensor_combine_vec
    by (metis assms list.sel(3) nth_mem tensor_from_vec_simp)
qed

lemma subtensor_induct[case_names order_0 order_step]:
assumes order_0: "\<And>A. dims A = [] \<Longrightarrow> P A"
and order_step: "\<And>A. dims A \<noteq> [] \<Longrightarrow> (\<And>i. i < hd (dims A) \<Longrightarrow> P (subtensor A i)) \<Longrightarrow> P A"
shows "P B"
using assms proof (induction "dims B" arbitrary:B)
  case Nil
  then show ?case by auto
next
  case Cons
  then show ?case by (metis dims_subtensor list.sel(3))
qed

lemma subtensor_combine_induct[case_names order_0 order_step]:
assumes order_0:"\<And>A. dims A = [] \<Longrightarrow> P A"
and order_step:"\<And>As ds. (\<And>A. A\<in>set As \<Longrightarrow> P A) \<Longrightarrow> (\<And>A. A\<in>set As \<Longrightarrow> dims A = ds) \<Longrightarrow> P (subtensor_combine ds As)"
shows "P A"
proof (induction A rule:subtensor_induct)
  case (order_0 A)
  then show ?case by (simp add: assms(1))
next
  case (order_step A)
  have "P (subtensor_combine (tl (dims A)) (map (subtensor A) [0..<hd (dims A)]))"
    apply (rule assms(2))
      using atLeastLessThan_iff dims_subtensor imageE set_map set_upt order_step by auto
  then show ?case using subtensor_combine_subtensor[OF order_step.hyps] by metis
qed

lemma lookup_subtensor1[simp]:
assumes "i # is \<lhd> dims A"
shows "lookup (subtensor A i) is = lookup A (i # is)"
using assms
proof (induction A rule: subtensor_combine_induct)
  case order_0
  then show ?case by auto
next
  case (order_step As ds)
  have 0:"subtensor (subtensor_combine ds As) i = As ! i"
    by (metis list.discI list.sel(1) order_step.hyps order_step.prems subtensor_combine_dims subtensor_subtensor_combine valid_index_dimsE)
  have 1:"dims (subtensor_combine ds As) = length As # ds"
    using order_step subtensor_combine_def subtensor_combine_dims by force
  show ?case unfolding "0" lookup_def 1 unfolding lookup_base_Cons using  order_step.prems
    using Tensor.lookup_base_Cons dims_subtensor lookup_def list.discI list.sel(1)
    list.sel(3)  valid_index_dimsE vec_subtensor by (metis "0" "1")
qed

lemma lookup_subtensor:
assumes "is \<lhd> dims A"
shows "lookup A is = hd (vec (fold (\<lambda>i A. subtensor A i) is A))"
using assms proof (induction "is" arbitrary: A)
  case Nil
  then show ?case by (metis Tensor.lookup_base_Nil lookup_def fold_simps(1) length_0_conv valid_index_length)
next
  case (Cons a "is" A)
  then show ?case
    using dims_subtensor lookup_subtensor1 fold_simps(2) list.discI list.sel(1) list.sel(3)
    valid_indexE by (metis (no_types, lifting))
qed

lemma subtensor_eqI:
assumes "dims A \<noteq> []"
and dims_eq:"dims A = dims B"
and "\<And>i. i < hd (dims A) \<Longrightarrow> subtensor A i = subtensor B i"
shows "A=B"
proof -
  {
    fix "is" assume "is \<lhd> dims A"
    then obtain i is' where is_Cons:"is = i # is'" using assms(1) by blast
    then have "lookup A is = lookup B is"
      using lookup_subtensor1 assms by (metis \<open>is \<lhd> dims A\<close> is_Cons list.sel(1) valid_index_dimsE)
  }
  then show ?thesis using tensor_lookup_eqI[OF dims_eq] by auto
qed

end
