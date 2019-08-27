(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Tensor Addition\<close>

theory Tensor_Plus
imports Tensor_Subtensor
begin

(* Problem: typeclass plus only has one zero element. If this is the empty tensor, other zero tensors cannot be of rank 0.*)

definition "vec_plus a b = map (\<lambda>(x,y). plus x y) (zip a b)"

definition plus_base::"'a::semigroup_add tensor \<Rightarrow> 'a tensor \<Rightarrow> 'a tensor"
where "plus_base A B = (tensor_from_vec (dims A) (vec_plus (vec A) (vec B)))"

instantiation tensor:: (semigroup_add) plus
begin
  definition plus_def: "A + B = (if (dims A = dims B)
                  then plus_base A B
                  else undefined)"
  instance ..
end

lemma plus_dim1[simp]: "dims A = dims B \<Longrightarrow> dims (A + B) = dims A" unfolding plus_def plus_base_def
  using dims_tensor length_vec length_map map_fst_zip vec_plus_def by (metis (full_types))
lemma plus_dim2[simp]: "dims A = dims B \<Longrightarrow> dims (A + B) = dims B" using plus_dim1 by metis
lemma plus_base: "dims A = dims B \<Longrightarrow> A + B = plus_base A B" unfolding plus_def by metis

lemma fixed_length_sublist_plus:
assumes "length xs1 = c * l" "length xs2 = c * l" "i < c"
shows "fixed_length_sublist (vec_plus xs1 xs2) l i
          = vec_plus (fixed_length_sublist xs1 l i) (fixed_length_sublist xs2 l i)"
unfolding vec_plus_def fixed_length_sublist_def using drop_map drop_zip take_map take_zip by metis

lemma vec_plus[simp]:
assumes "dims A = dims B"
shows "vec (A+B) = vec_plus (vec A) (vec B)"
  unfolding plus_def plus_base_def vec_plus_def using assms
  by (auto; metis (no_types, lifting) length_map length_tensor_vec_from_lookup map_fst_zip tensor_lookup tensor_from_lookup_def vec_tensor)

lemma subtensor_plus:
fixes A::"'a::semigroup_add tensor" and B::"'a::semigroup_add tensor"
assumes "i < hd (dims A)"
and "dims A = dims B"
and "dims A \<noteq> []"
shows "subtensor (A + B) i = subtensor A i + subtensor B i"
proof -
   have "length (vec A) =  hd (dims A) * prod_list (tl (dims A))"
        "length (Tensor.vec B) = hd (dims A) * prod_list (tl (dims A))"
     using length_vec prod_list.Cons assms by (metis (no_types) list.exhaust_sel)+
   then show ?thesis
     using Tensor_Plus.vec_plus assms fixed_length_sublist_plus vec_subtensor tensor_eqI
     dims_subtensor plus_dim1 by fastforce
qed

lemma lookup_plus[simp]:
assumes "dims A = dims B"
and "is \<lhd> dims A"
shows "lookup (A + B) is = lookup A is + lookup B is"
using assms proof (induction "A+B" arbitrary:A B "is" rule: subtensor_induct)
  case (order_0 A B "is")
  then have "is = []" by auto
  have 1:"[] \<lhd> dims A" using order_0 `is = []` by auto
  have 2:"[] \<lhd> dims B" using order_0 `is = []` by auto
  have 3:"[] \<lhd> dims (A + B)" using order_0 `is = []` by auto
  have "length (vec A) = 1" "length (vec B) = 1"
    by (metis length_vec prod_list.Nil order_0.hyps order_0.prems(1) plus_dim1)+
  then show ?case unfolding lookup_subtensor[OF 1] lookup_subtensor[OF 2] lookup_subtensor[OF 3] `is = []`
    fold_simps(1) vec_plus[OF order_0.prems(1)] unfolding vec_plus_def using  order_0.prems  length_map
    list.map_sel(1) list.size(3)  map_fst_zip map_snd_zip order_0.hyps
    zero_neq_one case_prod_unfold length_vec by metis
next
  case (order_step A B "is")
  then obtain i is' where "is = i # is'" by auto
  have 1:"is \<lhd> dims A" using order_step by auto
  have 2:"is \<lhd> dims B" using order_step by auto
  have 3:"is \<lhd> dims (A + B)" using order_step by auto
  have "lookup (subtensor A i + subtensor B i) is' = lookup (subtensor A i) is' + lookup (subtensor B i) is'"
     apply (rule order_step.hyps(2)[of i])
        using `is = i # is'` 3 hd_conv_nth length_greater_0_conv nth_Cons_0 order_step.hyps(1) valid_index_lt
        apply auto[1]
       apply (metis "2" \<open>is = i # is'\<close> list.inject list.sel(1) list.simps(3) order_step.prems(1) subtensor_plus valid_index.cases)
      using "1" \<open>is = i # is'\<close> order_step.prems(1) plus_dim1 apply auto[1]
     using "1" \<open>is = i # is'\<close> plus_dim1 by auto
  then show ?case using lookup_subtensor[OF 1] lookup_subtensor[OF 2] lookup_subtensor[OF 3]
    using order_step `is = i # is'` plus_dim1 lookup_subtensor1 list.sel(1) subtensor_plus valid_index_dimsE by metis
qed

lemma plus_assoc:
assumes dimsA:"dims A = ds" and dimsB:"dims B = ds" and dimsC:"dims C = ds"
shows "(A + B) + C = A + (B + C)"
by (rule tensor_lookup_eqI; simp add: dimsA dimsB dimsC add.assoc)+

lemma tensor_comm[simp]:
fixes A::"'a::ab_semigroup_add tensor"
shows "A + B = B + A"
proof (cases "dims A = dims B")
  case True
  then show ?thesis unfolding plus_def plus_base_def
    using add.commute lookup_plus[OF True] plus_dim1[OF True] tensor_lookup_eqI[OF True] vec_plus[OF True]
    by (metis lookup_plus plus_dim1 tensor_lookup_eqI vec_plus)
next
  case False
  then show ?thesis unfolding plus_def plus_base_def by simp
qed

definition "vec0 n = replicate n 0"

definition tensor0::"nat list \<Rightarrow> 'a::zero tensor" where
"tensor0 d = tensor_from_vec d (vec0 (prod_list d))"

lemma dims_tensor0[simp]: "dims (tensor0 d) = d"
and   vec_tensor0[simp]:  "vec (tensor0 d) = vec0 (prod_list d)"
  unfolding tensor0_def vec0_def by simp_all

lemma lookup_is_in_vec: "is \<lhd> (dims A) \<Longrightarrow> lookup A is \<in> set (vec A)"
proof (induction arbitrary:"is" rule:subtensor_induct)
  case order_0
  then show ?case unfolding lookup_def using lookup_base_Nil
    by (metis length_0_conv length_vec list.set_sel(1) prod_list.Nil valid_index_length zero_neq_one)
next
  case (order_step A "is")
  then obtain i is' where "is = i # is'" using valid_index_dimsE by blast
  then have 1:"i < hd (dims A)" using dims_def order_step.prems by auto
  have 2:"is' \<lhd> dims (subtensor A i)" using \<open>is = i # is'\<close> dims_subtensor order_step.prems by auto
  have "lookup A is \<in> set (Tensor.vec (subtensor A i))"
    using order_step.IH [OF 1 2] lookup_subtensor1 \<open>is = i # is'\<close> order_step.prems by auto
  then show ?case using vec_subtensor fixed_length_sublist_def by (metis "1" in_set_dropD in_set_takeD order_step.hyps)
qed

lemma lookup_tensor0:
assumes "is \<lhd> ds"
shows "lookup (tensor0 ds) is = 0"
proof -
  have "lookup (tensor0 ds) is \<in> set (vec (tensor0 ds))" using lookup_is_in_vec assms by (metis dims_tensor0)
  moreover have "set (vec (tensor0 ds)) \<subseteq> {0}" unfolding vec_tensor0 vec0_def by (metis in_set_replicate singleton_iff subsetI)
  ultimately show ?thesis by auto
qed

lemma
fixes A::"'a::monoid_add tensor"
shows tensor_add_0_right[simp]: "A + tensor0 (dims A) = A"
  unfolding plus_def plus_base_def dims_tensor0
   apply (simp_all)
    apply (rule tensor_lookup_eqI)
   apply (metis (no_types, lifting)  dims_tensor dims_tensor0 length_vec plus_dim2 vec_plus vec_tensor0)
  by (metis add.right_neutral dims_tensor0 lookup_plus lookup_tensor0 plus_dim2 tensor_from_vec_simp vec_plus vec_tensor0)

lemma
fixes A::"'a::monoid_add tensor"
shows tensor_add_0_left[simp]:  "tensor0 (dims A) + A = A"
  unfolding plus_def plus_base_def dims_tensor0
   apply (simp_all)
    apply (rule tensor_lookup_eqI)
   apply (metis (no_types, lifting)  dims_tensor dims_tensor0 length_vec plus_dim2 vec_plus vec_tensor0)
  by (metis add.left_neutral dims_tensor0 lookup_plus lookup_tensor0 plus_dim2 tensor_from_vec_simp vec_plus vec_tensor0)


definition listsum::"nat list \<Rightarrow> 'a::monoid_add tensor list \<Rightarrow> 'a tensor" where
"listsum ds As = foldr (+) As (tensor0 ds)"

definition listsum'::"'a::monoid_add tensor list \<Rightarrow> 'a tensor" where
"listsum' As = listsum (dims (hd As)) As"

lemma listsum_Nil: "listsum ds [] = tensor0 ds" by (simp add: Tensor_Plus.listsum_def)

lemma listsum_one: "listsum (dims A) [A] = A" unfolding listsum_def by simp

lemma listsum_Cons: "listsum ds (A # As) = A + listsum ds As"
  unfolding listsum_def by auto

lemma listsum_dims:
assumes "\<And>A. A\<in>set As \<Longrightarrow> dims A = ds"
shows "dims (listsum ds As) = ds"
using assms proof (induction As)
  case Nil
  then show ?case by (metis dims_tensor0 listsum_Nil)
next
  case (Cons A As)
  then show ?case using listsum_Cons
    by (metis list.set_intros(1) list.set_intros(2) plus_dim2)
qed

lemma subtensor0:
assumes "ds \<noteq> []" and "i<hd ds"
shows "subtensor (tensor0 ds) i = tensor0 (tl ds)"
proof (rule tensor_lookup_eqI)
  show 1:"dims (subtensor (tensor0 ds) i) = dims (tensor0 (tl ds))" by (simp add: assms(1) assms(2))
  fix "is" assume "is \<lhd> dims (subtensor (tensor0 ds) i)"
  then have "i # is \<lhd> dims (tensor0 ds)" using assms(1) assms(2) valid_index.Cons by fastforce
  then show "lookup (subtensor (tensor0 ds) i) is = lookup (tensor0 (tl ds)) is"
    using lookup_subtensor1  1 \<open>is \<lhd> dims (subtensor (tensor0 ds) i)\<close> dims_tensor0 lookup_tensor0
    by metis
qed

lemma subtensor_listsum:
assumes "\<And>A. A\<in>set As \<Longrightarrow> dims A = ds"
and "ds \<noteq> []" and "i<hd ds"
shows "subtensor (listsum ds As) i = listsum (tl ds) (map (\<lambda>A. subtensor A i) As)"
using assms proof (induction As)
  case Nil
  then show ?case using lookup_tensor0 assms(2) assms(3) subtensor0 by (auto simp add: listsum_Nil)
next
  case (Cons A As)
  then show ?case  by (simp add: listsum_Cons; metis subtensor_plus listsum_dims)
qed


lemma listsum0:
assumes "\<And>A. A\<in>set As \<Longrightarrow> A = tensor0 ds"
shows "listsum ds As = tensor0 ds"
using assms proof (induction As)
  case Nil
  show ?case by (simp add: listsum_Nil)
next
  case Cons
  then show ?case using listsum_Cons
    by (metis dims_tensor0 list.set_intros(1) set_subset_Cons subsetCE tensor_add_0_right)
qed

lemma listsum_all_0_but_one:
assumes "\<And>i. i\<noteq>j \<Longrightarrow> i<length As \<Longrightarrow> As!i = tensor0 ds"
and "dims (As!j) = ds"
and "j < length As"
shows "listsum ds As = As!j"
using assms proof (induction As arbitrary:j)
  case Nil
  then show ?case by auto
next
  case (Cons A As j)
  then show ?case
  proof (cases j)
    case 0
    then have "\<And>i. i < length As \<Longrightarrow> As ! i = tensor0 ds" using Cons using Suc_less_eq length_Cons list.sel(3) nat.simps(3) nth_tl by fastforce
    then have "listsum ds As = tensor0 ds" using listsum0 by (metis in_set_conv_nth)
    then show ?thesis by (metis "0" Cons.prems(2) listsum_Cons nth_Cons_0 tensor_add_0_right)
  next
    case (Suc j')
    then have "listsum ds As = As!j'" by (metis (no_types, lifting) Cons.IH Cons.prems(1) Cons.prems(2) Cons.prems(3) Suc_less_eq length_Cons less_Suc_eq list.sel(3) not_less_eq nth_tl)
    then show ?thesis by (metis Cons.prems(1) Cons.prems(2) Suc length_greater_0_conv list.simps(3) listsum_Cons nat.simps(3) nth_Cons_0 nth_Cons_Suc tensor_add_0_left)
  qed
qed

lemma lookup_listsum:
assumes "is \<lhd> ds"
and "\<And>A. A \<in> set As \<Longrightarrow> dims A = ds"
shows "lookup (listsum ds As) is = (\<Sum>A\<leftarrow>As. lookup A is)"
using assms proof (induction As)
  case Nil
  then show ?case by (simp add: assms(1) listsum_Nil lookup_tensor0)
next
  case (Cons A As)
  then show ?case by (simp add: listsum_Cons list.set_intros listsum_dims)
qed


end
