(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Tensor Product\<close>

theory Tensor_Product
imports Tensor_Scalar_Mult Tensor_Subtensor
begin

instantiation tensor:: (ring) semigroup_mult
begin
  definition tensor_prod_def:"A * B = tensor_from_vec (dims A @ dims B) (concat (map (\<lambda>a. vec_smult a (vec B)) (vec A)))"

  abbreviation tensor_prod_otimes :: "'a tensor \<Rightarrow> 'a tensor \<Rightarrow> 'a tensor" (infixl "\<otimes>" 70)
    where "A \<otimes> B \<equiv> A * B"


  lemma vec_tensor_prod[simp]: "vec (A \<otimes> B) = concat (map (\<lambda>a. vec_smult a (vec B)) (vec A))" (is ?V)
  and dims_tensor_prod[simp]: "dims (A \<otimes> B) = dims A @ dims B" (is ?D)
  proof -
    have "length (concat (map (\<lambda>a. vec_smult a (vec B)) (vec A))) = prod_list (dims A @ dims B)"
    proof -
      have "\<And>xs. xs \<in> set (map (\<lambda>a. vec_smult a (vec B)) (vec A)) \<Longrightarrow> length xs = length (vec B)"
        using length_vec_smult by force
      then show ?thesis using concat_equal_length by (metis length_map length_vec prod_list.append)
    qed
    then show ?V ?D by (simp add: tensor_prod_def)+
  qed

  lemma tensorprod_subtensor_base:
  shows "concat (map f (concat xss)) = concat (map (\<lambda>xs. concat (map f xs)) xss)"
  by (induction xss; auto)

  lemma subtensor_combine_tensor_prod:
  assumes "\<And>A. A\<in>set As \<Longrightarrow> dims A = ds"
  shows "subtensor_combine ds As \<otimes> B = subtensor_combine (ds @ dims B) (map (\<lambda>A. A \<otimes> B) As)"
  proof -
    let ?f = "\<lambda>a. vec_smult a (Tensor.vec B)"
    let ?xss = "map Tensor.vec As"
    have 1:"prod_list (length As # ds) = length (concat ?xss)" by (metis assms length_vec subtensor_combine_dims subtensor_combine_vec)
    have 2:"\<And>A. A\<in>set As \<Longrightarrow> prod_list (dims A @ dims B) = length (concat (map ?f (Tensor.vec A)))"
      by (metis dims_tensor_prod length_vec vec_tensor_prod)
    have 3: "length As # ds @ dims B = (length (map (\<lambda>A. tensor_from_vec (dims A @ dims B)
      (concat (map (\<lambda>a. vec_smult a (vec B)) (vec A)))) As) # ds @ dims B)" by simp
    have 4:"(concat (map (\<lambda>xs. concat (map (\<lambda>a. vec_smult a (vec B)) xs)) (map vec As)))
         = (concat (map vec (map (\<lambda>A. tensor_from_vec (dims A @ dims B) (concat (map (\<lambda>a. vec_smult a (vec B)) (vec A))))  As)))"
      unfolding map_map[unfolded comp_def]  using vec_tensor by (metis (no_types, lifting) "2" map_eq_conv)
    have "subtensor_combine ds As \<otimes> B = tensor_from_vec (length As # ds @ dims B) (concat (map ?f (concat (?xss))))"
      unfolding subtensor_combine_def tensor_prod_def using 1 by auto
    also have "... = tensor_from_vec (length As # ds @ dims B) (concat (map (\<lambda>xs. concat (map ?f xs)) ?xss))"
      using tensorprod_subtensor_base[of ?f ?xss] by auto
    also have "... =subtensor_combine (ds @ dims B) (map (\<lambda>A. A \<otimes> B) As)"
      unfolding subtensor_combine_def tensor_prod_def using 3 4 by metis
    finally show ?thesis by metis
  qed

  (* evtl. besser ohne Induktion beweisen? Dann wäre das obige Lemma unnötig. Vllt aber auch schwierig. *)
  lemma subtensor_tensor_prod:
  assumes "dims A \<noteq> []" and "i < hd (dims A)"
  shows "subtensor (A \<otimes> B) i = subtensor A i \<otimes> B"
  using assms proof (induction A rule:subtensor_combine_induct)
    case order_0
    then show ?case by auto
  next
    case (order_step As ds)
    have 1:"i < length (map (\<lambda>A. A \<otimes> B) As)" using order_step by (simp add: order_step.hyps order_step.prems(1))
    have 2:"(\<And>A. A \<in> set (map (\<lambda>A. A \<otimes> B) As) \<Longrightarrow> dims A = ds @ dims B)" using order_step by auto
    have "subtensor (subtensor_combine ds As \<otimes> B) i = subtensor (subtensor_combine (ds @ dims B) (map (\<lambda>A. A \<otimes> B) As)) i"
      using subtensor_combine_tensor_prod order_step by metis
    also have "... = As ! i \<otimes> B"
      using order_step subtensor_subtensor_combine[of "(map (\<lambda>A. A \<otimes> B) As)" "ds @ dims B" i] 1 2 by auto
    also have "... = subtensor (subtensor_combine ds As) i \<otimes> B"
      by (metis "1" length_map order_step.hyps subtensor_subtensor_combine)
    finally show ?case by auto
  qed

  lemma lookup_tensor_prod[simp]:
  assumes is1_valid:"is1 \<lhd> dims A" and is2_valid:"is2 \<lhd> dims B"
  shows "lookup (A \<otimes> B) (is1 @ is2) = lookup A is1 * lookup B is2"
  using assms proof (induction A arbitrary:is1 rule:subtensor_induct)
    case (order_0 A is1)
    then obtain a where "vec A = [a]"
      using Suc_length_conv Tensor.tensor_vec_from_lookup_Nil length_0_conv length_tensor_vec_from_lookup length_vec by metis
    then have "A \<otimes> B = a \<cdot> B" unfolding tensor_prod_def smult_def using order_0 by simp
    moreover have "lookup A [] = a" by (simp add: `Tensor.vec A = [a]` lookup_def order_0.hyps)
    ultimately have "lookup (A \<otimes> B) (is2) = a * lookup B is2" by (simp add: lookup_smult is2_valid)
    then show ?case using `lookup A [] = a` null_rec(1) order_0.hyps order_0.prems(1) by auto
  next
    case (order_step A is1)
    then obtain i is1' where "i # is1' = is1" by blast
    have "lookup (subtensor A i \<otimes> B) (is1' @ is2) = lookup (subtensor A i) is1' * lookup B is2" using order_step
      by (metis `i # is1' = is1` dims_subtensor list.sel(1) list.sel(3) valid_index_dimsE)
    then show "lookup (A \<otimes> B) (is1 @ is2) = lookup A is1 * lookup B is2"
      using lookup_subtensor1[of i is1' A] lookup_subtensor1[of i "is1' @ is2" "A\<otimes>B"] subtensor_tensor_prod[of A i B]
      Cons_eq_appendI `i # is1' = is1` dims_tensor_prod is2_valid list.sel(1) order_step.hyps order_step.prems(1) valid_index_append valid_index_dimsE
      by metis
  qed

  lemma valid_index_split:
  assumes "is \<lhd> ds1 @ ds2"
  obtains is1 is2 where "is1 @ is2 = is" "is1 \<lhd> ds1" "is2 \<lhd> ds2"
  proof
    assume a: "\<And>is1 is2. is1 @ is2 = is \<Longrightarrow> is1 \<lhd> ds1 \<Longrightarrow> is2 \<lhd> ds2 \<Longrightarrow> thesis"
    have length_is:"length is = length ds1 + length ds2" using valid_index_length using assms by auto
    show "take (length ds1) is \<lhd> ds1"
      apply (rule valid_indexI)
      using valid_index_length using assms apply auto[1]
      by (metis add_leD1 assms length_append not_less nth_append nth_take valid_index_lt)
    show "drop (length ds1) is \<lhd> ds2"
      apply (rule valid_indexI)
      using valid_index_length using assms apply auto[1]
      using nth_drop[of "length ds1" "is"] valid_index_lt[OF assms(1)] nth_append[of ds1 ds2] length_is
      by (metis length_append nat_add_left_cancel_less nat_le_iff_add nth_append_length_plus)
    show "take (length ds1) is @ drop (length ds1) is = is" using length_is by auto
  qed

  instance proof
    fix A B C::"'a::ring tensor"
    show "(A \<otimes> B) \<otimes> C = A \<otimes> (B \<otimes> C)"
    proof (rule tensor_lookup_eqI, simp)
      fix "is" assume "is \<lhd> dims ((A \<otimes> B) \<otimes> C)"
      obtain is1 is23 where "is1 \<lhd> dims A" "is23 \<lhd> dims (B \<otimes> C)" "is1 @ is23 = is"
        by (metis (mono_tags, lifting) `is \<lhd> dims ((A \<otimes> B) \<otimes> C)` Tensor_Product.dims_tensor_prod append_assoc valid_index_split)
      obtain is2 is3 where "is2 \<lhd> dims B" "is3 \<lhd> dims C" "is2 @ is3 = is23"
        by (metis \<open>is23 \<lhd> dims (local.tensor_prod_otimes B C)\<close> dims_tensor_prod valid_index_split)
      define is12 where "is12 = is1 @ is2"
      have "is12 \<lhd> dims (A \<otimes> B)" by (simp add: \<open>is1 \<lhd> dims A\<close> \<open>is2 \<lhd> dims B\<close> is12_def valid_index_append)
      have "is12 @ is3 = is" by (simp add: \<open>is1 @ is23 = is\<close> \<open>is2 @ is3 = is23\<close> is12_def)
      show "lookup ((A \<otimes> B) \<otimes> C) is = lookup (A \<otimes> (B \<otimes> C)) is"
        unfolding lookup_tensor_prod[OF `is1 \<lhd> dims A` `is23 \<lhd> dims (B \<otimes> C)`, unfolded `is1 @ is23 = is`]
        lookup_tensor_prod[OF `is12 \<lhd> dims (A \<otimes> B)` `is3 \<lhd> dims C`, unfolded `is12 @ is3 = is`]
        using \<open>is1 \<lhd> dims A\<close> \<open>is2 @ is3 = is23\<close> \<open>is2 \<lhd> dims B\<close> \<open>is3 \<lhd> dims C\<close> is12_def mult.assoc by fastforce
    qed
  qed

end

lemma tensor_prod_distr_left:
assumes "dims A = dims B"
shows "(A + B) \<otimes> C = (A \<otimes> C) + (B \<otimes> C)"
proof -
  have "\<And>is. is \<lhd> dims A @ dims C \<Longrightarrow> lookup ((A + B) \<otimes> C) is = lookup (A \<otimes> C + B \<otimes> C) is"
  proof -
    fix "is" assume "is \<lhd> dims A @ dims C"
    obtain is1 is2 where "is = is1 @ is2" "is1 \<lhd> dims A" "is2 \<lhd> dims C" using valid_index_split using `is \<lhd> dims A @ dims C` by blast
    then show "lookup ((A + B) \<otimes> C) is = lookup ((A \<otimes> C) + (B \<otimes> C)) is"
     using lookup_plus
     `is1 \<lhd> dims A` `is2 \<lhd> dims C` assms plus_dim1 dims_tensor_prod lookup_tensor_prod ring_class.ring_distribs(2) valid_index_append
     by fastforce
  qed
  moreover have "tensor_from_lookup (dims A @ dims C) (lookup ((A + B) \<otimes> C)) = (A + B) \<otimes> C"
       "tensor_from_lookup (dims A @ dims C) (lookup ((A \<otimes> C) + (B \<otimes> C))) = (A \<otimes> C) + (B \<otimes> C)"
    by (metis (no_types, lifting) assms plus_dim1 dims_tensor_prod tensor_lookup)+
  ultimately show ?thesis using tensor_from_lookup_eqI
    by (metis `\<And>is. is \<lhd> dims A @ dims C \<Longrightarrow> lookup ((A + B) \<otimes> C) is = lookup (A \<otimes> C + B \<otimes> C) is`)
qed

lemma tensor_prod_distr_right:
assumes "dims A = dims B"
shows "C \<otimes> (A + B) = (C \<otimes> A) + (C \<otimes> B)"
proof -
  have "\<And>is. is \<lhd> dims C @ dims A \<Longrightarrow> lookup (C \<otimes> (A + B)) is = lookup (C \<otimes> A + C \<otimes> B) is"
  proof -
    fix "is" assume "is \<lhd> dims C @ dims A"
    obtain is1 is2 where "is = is1 @ is2" "is1 \<lhd> dims C" "is2 \<lhd> dims A" using valid_index_split using `is \<lhd> dims C @ dims A` by blast
    then show "lookup (C \<otimes> (A + B)) is = lookup ((C \<otimes> A) + (C \<otimes> B)) is"
     using lookup_plus
     using `is2 \<lhd> dims A` `is1 \<lhd> dims C` assms plus_dim1 dims_tensor_prod lookup_tensor_prod ring_class.ring_distribs(1) valid_index_append
     by fastforce
  qed
  moreover have "tensor_from_lookup (dims C @ dims A) (lookup (C \<otimes> (A + B))) = C \<otimes> (A + B)"
       "tensor_from_lookup (dims C @ dims A) (lookup ((C \<otimes> A) + (C \<otimes> B))) = (C \<otimes> A) + (C \<otimes> B)"
    by (metis (no_types, lifting) assms plus_dim1 dims_tensor_prod tensor_lookup)+
  ultimately show ?thesis using tensor_from_lookup_eqI
    by (metis `\<And>is. is \<lhd> dims C @ dims A \<Longrightarrow> lookup (C \<otimes> (A + B)) is = lookup (C \<otimes> A + C \<otimes> B) is`)
qed

instantiation tensor :: (ring_1) monoid_mult
begin
  definition tensor_one_def:"1 = tensor_from_vec [] [1]"

  lemma tensor_one_from_lookup: "1 = tensor_from_lookup [] (\<lambda>_. 1)"
    unfolding tensor_one_def by (rule tensor_eqI; simp_all add: tensor_from_lookup_def )

  instance proof
    fix A::"'a::ring_1 tensor"
    show "A * 1 = A" unfolding tensor_one_from_lookup
      by (rule tensor_lookup_eqI;metis lookup_tensor_prod[of _ "A" "[]" "tensor_from_lookup [] (\<lambda>_. 1)"]
          lookup_tensor_from_lookup valid_index.Nil append_Nil2 dims_tensor dims_tensor_prod
          length_tensor_vec_from_lookup mult.right_neutral tensor_from_lookup_def)
  next
    fix A::"'a::ring_1 tensor"
    show "1 * A = A" unfolding tensor_one_from_lookup
      by (rule tensor_lookup_eqI; metis lookup_tensor_prod[of "[]" "tensor_from_lookup [] (\<lambda>_. 1)" _ "A"]
          lookup_tensor_from_lookup valid_index.Nil List.append.append_Nil dims_tensor dims_tensor_prod
          length_tensor_vec_from_lookup mult.left_neutral tensor_from_lookup_def)
  qed
end

lemma order_tensor_one: "order 1 = 0" unfolding tensor_one_def by simp

lemma smult_prod_extract1:
fixes a::"'a::comm_ring_1"
shows "a \<cdot> (A \<otimes> B) = (a \<cdot> A) \<otimes> B"
proof (rule tensor_lookup_eqI)
  show "dims (a \<cdot> (A \<otimes> B)) = dims ((a \<cdot> A) \<otimes> B)" by simp
  fix "is" assume "is \<lhd> dims (a \<cdot> (A \<otimes> B))"
  then have "is \<lhd> dims (A \<otimes> B)" by auto
  then obtain is1 is2 where "is1 \<lhd> dims A" "is2 \<lhd> dims B" "is = is1 @ is2" by (metis dims_tensor_prod valid_index_split)
  then have "is1 \<lhd> dims (a \<cdot> A)" by auto
  show "lookup (a \<cdot> (A \<otimes> B)) is = lookup (a \<cdot> A \<otimes> B) is"
  using lookup_tensor_prod[OF `is1 \<lhd> dims A` `is2 \<lhd> dims B`] lookup_tensor_prod[OF `is1 \<lhd> dims (a \<cdot> A)` `is2 \<lhd> dims B`]
        lookup_smult[OF `is \<lhd> dims (A \<otimes> B)`] lookup_smult[OF `is1 \<lhd> dims A`] `is = is1 @ is2` by simp
qed

lemma smult_prod_extract2:
fixes a::"'a::comm_ring_1"
shows "a \<cdot> (A \<otimes> B) = A \<otimes> (a \<cdot> B)"
proof (rule tensor_lookup_eqI)
  show "dims (a \<cdot> (A \<otimes> B)) = dims (A \<otimes> (a \<cdot> B))" by simp
  fix "is" assume "is \<lhd> dims (a \<cdot> (A \<otimes> B))"
  then have "is \<lhd> dims (A \<otimes> B)" by auto
  then obtain is1 is2 where "is1 \<lhd> dims A" "is2 \<lhd> dims B" "is = is1 @ is2" by (metis dims_tensor_prod valid_index_split)
  then have "is2 \<lhd> dims (a \<cdot> B)" by auto
  show "lookup (a \<cdot> (A \<otimes> B)) is = lookup (A \<otimes> (a \<cdot> B)) is"
  using lookup_tensor_prod[OF `is1 \<lhd> dims A` `is2 \<lhd> dims B`] lookup_tensor_prod[OF `is1 \<lhd> dims A` `is2 \<lhd> dims (a \<cdot> B)`]
        lookup_smult[OF `is \<lhd> dims (A \<otimes> B)`] lookup_smult[OF `is2 \<lhd> dims B`] `is = is1 @ is2` by simp
qed


lemma order_0_multiple_of_one:
assumes "order A = 0"
obtains a where "A = a \<cdot> 1"
proof
  assume "(\<And>a. A = a \<cdot> 1 \<Longrightarrow> thesis)"
  have "length (vec A) = 1" using assms by (simp add:length_vec)
  then obtain a where "vec A = [a]" by (metis One_nat_def Suc_length_conv length_0_conv)
  moreover have "vec (a \<cdot> 1) = [a]" unfolding smult_def tensor_one_def by (simp add: vec_smult_def)
  ultimately have "A = a \<cdot> 1" using tensor_eqI by (metis assms dims_smult length_0_conv order_tensor_one)
  then show "A = hd (vec A) \<cdot> 1" using `vec A = [a]` by auto
qed

lemma smult_1:
fixes A::"'a::ring_1 tensor"
shows "A = 1 \<cdot> A" unfolding smult_def tensor_one_def
apply (rule tensor_eqI)
apply (simp add: length_vec length_vec_smult)
by (metis dims_tensor length_vec length_vec_smult lookup_smult mult.left_neutral smult_def tensor_lookup_eqI)


lemma tensor0_prod_right[simp]: "A \<otimes> tensor0 ds = tensor0 (dims A @ ds)"
proof (rule tensor_lookup_eqI,simp)
  fix "is" assume "is \<lhd> dims (A \<otimes> tensor0 ds)"
  then obtain is1 is2 where "is1 \<lhd> dims A" "is2 \<lhd> dims (tensor0 ds)" "is = is1 @ is2"
    by (metis dims_tensor0 dims_tensor_prod valid_index_split)
  then show "lookup (A \<otimes> tensor0 ds) is = lookup (tensor0 (dims A @ ds)) is"
    by (metis (no_types, lifting) \<open>is \<lhd> dims (A \<otimes> tensor0 ds)\<close> dims_tensor0 dims_tensor_prod lookup_tensor0 lookup_tensor_prod mult_zero_right)
qed

lemma tensor0_prod_left[simp]: "tensor0 ds \<otimes> A = tensor0 (ds @ dims A)"
proof (rule tensor_lookup_eqI,simp)
  fix "is" assume "is \<lhd> dims (tensor0 ds \<otimes> A)"
  then obtain is1 is2 where "is1 \<lhd> dims (tensor0 ds)" "is2 \<lhd> dims A" "is = is1 @ is2"
    by (metis dims_tensor0 dims_tensor_prod valid_index_split)
  then show "lookup (tensor0 ds \<otimes> A) is = lookup (tensor0 (ds @ dims A)) is"
    by (metis (no_types, lifting) \<open>is \<lhd> dims (tensor0 ds \<otimes> A)\<close> dims_tensor0 dims_tensor_prod lookup_tensor0 lookup_tensor_prod mult_zero_left)
qed

lemma subtensor_prod_with_vec:
assumes "order A = 1" "i < hd (dims A)"
shows "subtensor (A \<otimes> B) i = lookup A [i] \<cdot> B"
proof (rule tensor_lookup_eqI)
  have "dims (A \<otimes> B) \<noteq> []" using assms(1) by auto
  have "hd (dims A) =  hd (dims (A \<otimes> B))"
    by (metis One_nat_def Suc_length_conv append_Cons assms(1) dims_tensor_prod list.sel(1))
  show "dims (subtensor (A \<otimes> B) i) = dims (lookup A [i] \<cdot> B)"
    unfolding dims_smult dims_subtensor[OF `dims (A \<otimes> B) \<noteq> []` `i < hd (dims A)`[unfolded `hd (dims A) =  hd (dims (A \<otimes> B))`] ]
    by (metis One_nat_def Suc_length_conv append.simps(2) append_self_conv2 assms(1) dims_tensor_prod length_0_conv list.sel(3))
next
  fix "is" assume "is \<lhd> dims (subtensor (A \<otimes> B) i)"
  have "dims (A \<otimes> B) \<noteq> []" using assms(1) by auto
  have "hd (dims A) =  hd (dims (A \<otimes> B))"
    by (metis One_nat_def Suc_length_conv append_Cons assms(1) dims_tensor_prod list.sel(1))
  then have "is \<lhd> dims B"
    using `is \<lhd> dims (subtensor (A \<otimes> B) i)`[unfolded dims_subtensor[OF `dims (A \<otimes> B) \<noteq> []` `i < hd (dims A)`[unfolded `hd (dims A) =  hd (dims (A \<otimes> B))`] ]]
    by (metis One_nat_def Suc_length_conv append_self_conv2 assms(1) dims_tensor_prod length_0_conv list.sel(3) list.simps(3) tl_append2)
  have "[i] \<lhd> dims A" using assms by (metis One_nat_def Suc_length_conv length_0_conv list.sel(1) valid_index.Nil valid_index.simps)
  then have "i # is \<lhd> dims (A \<otimes> B)" using \<open>is \<lhd> dims (subtensor (A \<otimes> B) i)\<close> dims_subtensor valid_index.Cons by auto
  then show "lookup (subtensor (A \<otimes> B) i) is = lookup (lookup A [i] \<cdot> B) is"
  unfolding lookup_subtensor1[OF `i # is \<lhd> dims (A \<otimes> B)`]
    using lookup_tensor_prod[OF `[i] \<lhd> dims A` `is \<lhd> dims B`] lookup_smult
    \<open>is \<lhd> dims B\<close> using append_Cons by fastforce
qed

end
