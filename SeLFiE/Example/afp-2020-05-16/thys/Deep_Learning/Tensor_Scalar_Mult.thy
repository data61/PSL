(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Tensor Scalar Multiplication\<close>

theory Tensor_Scalar_Mult
imports Tensor_Plus Tensor_Subtensor
begin

definition vec_smult::"'a::ring \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"vec_smult \<alpha> \<beta> = map ((*) \<alpha>) \<beta>"

lemma vec_smult0: "vec_smult 0 as = vec0 (length as)"
  by (induction as; auto simp add:vec0_def vec_smult_def)

lemma vec_smult_distr_right:
shows "vec_smult (\<alpha> + \<beta>) as = vec_plus (vec_smult \<alpha> as) (vec_smult \<beta> as)"
  unfolding vec_smult_def vec_plus_def
  by (induction as; simp add: distrib_right)

lemma vec_smult_Cons:
shows "vec_smult \<alpha> (a # as) = (\<alpha> * a) # vec_smult \<alpha> as" by (simp add: vec_smult_def)

lemma vec_plus_Cons:
shows "vec_plus (a # as) (b # bs) = (a+b) # vec_plus as bs" by (simp add: vec_plus_def)

lemma vec_smult_distr_left:
assumes "length as = length bs"
shows "vec_smult \<alpha> (vec_plus as bs) = vec_plus (vec_smult \<alpha> as) (vec_smult \<alpha> bs)"
using assms proof (induction as arbitrary:bs)
  case Nil
  then show ?case unfolding vec_smult_def vec_plus_def by simp
next
  case (Cons a as')
  then obtain b bs' where "bs = b # bs'" by (metis Suc_length_conv)
  then have 0:"vec_smult \<alpha> (vec_plus (a # as') bs) = (\<alpha>*(a+b)) # vec_smult \<alpha> (vec_plus as' bs')"
    unfolding vec_smult_def vec_plus_def using Cons.IH[of bs'] by simp
  have "length bs' = length as'" using Cons.prems \<open>bs = b # bs'\<close> by auto
  then show ?case unfolding 0 unfolding  \<open>bs = b # bs'\<close> vec_smult_Cons vec_plus_Cons
    by (simp add: Cons.IH distrib_left)
qed

lemma length_vec_smult: "length (vec_smult \<alpha> v) = length v" unfolding vec_smult_def by simp

definition smult::"'a::ring \<Rightarrow> 'a tensor \<Rightarrow> 'a tensor" (infixl "\<cdot>" 70) where
"smult \<alpha> A = (tensor_from_vec (dims A) (vec_smult \<alpha> (vec A)))"


lemma tensor_smult0: fixes A::"'a::ring tensor"
shows "0 \<cdot> A = tensor0 (dims A)"
  unfolding smult_def tensor0_def vec_smult_def using vec_smult0 length_vec
  by (metis (no_types) vec_smult_def)

lemma dims_smult[simp]:"dims (\<alpha> \<cdot> A) = dims A"
and   vec_smult[simp]: "vec  (\<alpha> \<cdot> A) = map ((*) \<alpha>) (vec A)"
  unfolding smult_def vec_smult_def by (simp add: length_vec)+

lemma tensor_smult_distr_right: "(\<alpha> + \<beta>) \<cdot> A = \<alpha> \<cdot> A  + \<beta> \<cdot> A"
  unfolding plus_def plus_base_def
  by (auto; metis smult_def vec_smult_def vec_smult_distr_right)

lemma tensor_smult_distr_left: "dims A = dims B \<Longrightarrow> \<alpha> \<cdot> (A + B) = \<alpha> \<cdot> A  + \<alpha> \<cdot> B"
proof -
  assume a1: "dims A = dims B"
  then have f2: "length (vec_plus (vec A) (vec B)) = length (vec A)"
    by (simp add: length_vec vec_plus_def)
  have f3: "dims (tensor_from_vec (dims B) (vec_smult \<alpha> (vec A))) = dims B"
    using a1 by (simp add: length_vec vec_smult_def)
  have f4: "vec (\<alpha> \<cdot> A) = vec_smult \<alpha> (vec A)"
    by (simp add: vec_smult_def)
  have "length (vec_smult \<alpha> (vec B)) = length (vec B)"
    by (simp add: vec_smult_def)
  then show ?thesis
    unfolding plus_def plus_base_def using f4 f3 f2 a1
    by (simp add: length_vec smult_def vec_smult_distr_left)
qed

lemma smult_fixed_length_sublist:
assumes "length xs = l * c" "i<c"
shows "fixed_length_sublist (vec_smult \<alpha> xs) l i = vec_smult \<alpha> (fixed_length_sublist xs l i)"
unfolding fixed_length_sublist_def vec_smult_def by (simp add: drop_map take_map)

lemma smult_subtensor:
assumes "dims A \<noteq> []" "i < hd (dims A)"
shows "\<alpha> \<cdot> subtensor A i = subtensor (\<alpha> \<cdot> A) i"
proof (rule tensor_eqI)
  show "dims (\<alpha> \<cdot> subtensor A i) = dims (subtensor (\<alpha> \<cdot> A) i)"
    using dims_smult dims_subtensor assms(1) assms(2) by simp
  show "vec (\<alpha> \<cdot> subtensor A i) = vec (subtensor (\<alpha> \<cdot> A) i)"
    unfolding vec_smult
    unfolding vec_subtensor[OF \<open>dims A \<noteq> []\<close> \<open>i < hd (dims A)\<close>]
    using vec_subtensor[of "\<alpha> \<cdot> A" i]
    by (simp add: assms(1) assms(2) drop_map fixed_length_sublist_def take_map)
qed

lemma lookup_smult:
assumes "is \<lhd> dims A"
shows "lookup (\<alpha> \<cdot> A) is = \<alpha> * lookup A is"
using assms proof (induction A arbitrary:"is" rule:subtensor_induct)
  case (order_0 A "is")
  then have "length (vec A) = 1" by (simp add: length_vec)
  then have "hd (vec_smult \<alpha> (vec A)) = \<alpha> * hd (vec A)" unfolding vec_smult_def by (metis list.map_sel(1) list.size(3) zero_neq_one)
  moreover have "is = []" using order_0 by auto
  ultimately show ?case unfolding smult_def by (auto simp add: \<open>length (Tensor.vec A) = 1\<close> lookup_def length_vec_smult order_0.hyps)
next
  case (order_step A "is")
  then obtain i is' where "is = i # is'" by blast
  then have "lookup (\<alpha> \<cdot> subtensor A i) is' = \<alpha> * lookup (subtensor A i) is'"
    by (metis (no_types, lifting) dims_subtensor list.sel(1) list.sel(3) order_step.IH order_step.hyps order_step.prems valid_index_dimsE)
  then show ?case using smult_subtensor \<open>is = i # is'\<close> dims_smult lookup_subtensor1
    list.sel(1) order_step.hyps order_step.prems valid_index_dimsE
    by metis
qed

lemma tensor_smult_assoc:
fixes A::"'a::ring tensor"
shows "\<alpha> \<cdot> (\<beta> \<cdot> A) = (\<alpha> * \<beta>) \<cdot> A"
by (rule tensor_lookup_eqI, simp, metis lookup_smult dims_smult mult.assoc)

end
