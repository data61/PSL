(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Tensor\<close>

theory Tensor
imports Main
begin


typedef 'a tensor = "{t::nat list \<times> 'a list. length (snd t) = prod_list (fst t)}"
by (simp add: Ex_list_of_length)

definition dims::"'a tensor \<Rightarrow> nat list" where
  "dims A = fst (Rep_tensor A)"

definition vec::"'a tensor \<Rightarrow> 'a list" where
  "vec A = snd (Rep_tensor A)"

definition tensor_from_vec::"nat list \<Rightarrow> 'a list \<Rightarrow> 'a tensor" where
  "tensor_from_vec d v = Abs_tensor (d,v)"

lemma
assumes "length v = prod_list d"
shows dims_tensor[simp]: "dims (tensor_from_vec d v) = d"
and   vec_tensor[simp]:  "vec (tensor_from_vec d v) = v"
by (simp add: Abs_tensor_inverse assms dims_def tensor_from_vec_def vec_def)+

lemma tensor_from_vec_simp[simp]: "tensor_from_vec (dims A) (vec A) = A"
by (simp add: Rep_tensor_inverse Tensor.vec_def dims_def tensor_from_vec_def)

lemma length_vec: "length (vec A) = prod_list (dims A)"
by (metis (mono_tags, lifting) Rep_tensor Tensor.vec_def dims_def mem_Collect_eq)

lemma tensor_eqI[intro]:
assumes "dims A = dims B" and "vec A = vec B"
shows "A=B"
by (metis assms tensor_from_vec_simp)


abbreviation order::"'a tensor \<Rightarrow> nat" where
  "order t == length (dims t)"

inductive valid_index::"nat list \<Rightarrow> nat list \<Rightarrow> bool" (infix "\<lhd>" 50) where
  Nil: "[] \<lhd> []" |
  Cons: "is \<lhd> ds \<Longrightarrow> i<d \<Longrightarrow> i#is \<lhd> d#ds"

inductive_cases valid_indexE[elim]: "is \<lhd> ds"
inductive_cases valid_index_dimsE[elim]: "is \<lhd> dims A"

lemma valid_index_length: "is \<lhd> ds \<Longrightarrow> length is = length ds"
  by (induction rule:valid_index.induct; auto)

lemma valid_index_lt: "is \<lhd> ds \<Longrightarrow> m<length ds \<Longrightarrow> is!m < ds!m"
proof (induction arbitrary:m rule:valid_index.induct)
  case Nil
  then show ?case by auto
next
  case Cons
  then show ?case by (metis gr0_conv_Suc length_Cons linorder_neqE_nat not_less_eq nth_Cons' nth_Cons_Suc)
qed

lemma valid_indexI:
assumes "length is = length ds" and "\<And>m. m<length ds \<Longrightarrow> is!m < ds!m"
shows "is \<lhd> ds"
using assms proof (induction "is" arbitrary:ds)
  case Nil
  then show ?case by (metis length_0_conv valid_index.simps)
next
  case (Cons a "is" ds)
  then obtain d ds' where "ds = d # ds'" by (metis length_Suc_conv)
  then have "is \<lhd> ds'" using Cons by (metis length_Cons less_irrefl linorder_neqE_nat not_less_eq nth_Cons_Suc)
  then show ?case using Cons.prems(2) \<open>ds = d # ds'\<close> valid_index.Cons by fastforce
qed

lemma valid_index_append:
assumes is1_valid:"is1 \<lhd> ds1" and is2_valid:"is2 \<lhd> ds2"
shows "is1 @ is2 \<lhd> ds1 @ ds2"
  apply (rule valid_indexI[of "is1 @ is2" "ds1 @ ds2"])
  unfolding nth_append
  using valid_index_lt[OF is2_valid] valid_index_lt[OF is1_valid] valid_index_length[OF is1_valid] valid_index_length[OF is2_valid] length_append
  by (auto simp add: \<open>length is1 = length ds1\<close>)

lemma valid_index_list_all2_iff: "is \<lhd> ds \<longleftrightarrow> list_all2 (<) is ds"
by (metis list_all2_conv_all_nth list_all2_nthD valid_indexI valid_index_length valid_index_lt)

definition fixed_length_sublist::"'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
"fixed_length_sublist xs l i = (take l (drop (l*i) xs))"

fun lookup_base::"nat list \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> 'a" where
  lookup_base_Nil: "lookup_base [] v [] = hd v" |
  lookup_base_Cons: "lookup_base (d # ds) v (i # is) =
    lookup_base ds (fixed_length_sublist v (prod_list ds) i) is"

definition lookup::"'a tensor \<Rightarrow> nat list \<Rightarrow> 'a" where
  "lookup A = lookup_base (dims A) (vec A)"

fun tensor_vec_from_lookup::"nat list \<Rightarrow> (nat list \<Rightarrow> 'a) \<Rightarrow> 'a list" where
  tensor_vec_from_lookup_Nil: "tensor_vec_from_lookup [] e = [e []]" |
  tensor_vec_from_lookup_Cons: "tensor_vec_from_lookup (d # ds) e = concat (map (\<lambda>i. tensor_vec_from_lookup ds (\<lambda>is. e (i # is))) [0..<d])"

definition tensor_from_lookup::"nat list \<Rightarrow> (nat list \<Rightarrow> 'a) \<Rightarrow> 'a tensor" where
  "tensor_from_lookup ds e = tensor_from_vec ds (tensor_vec_from_lookup ds e)"

lemma concat_parts_leq:
assumes "a * d \<le> length v"
shows "concat (map (fixed_length_sublist v d) [0..<a]) = take (a*d) v"
using assms proof (induction a)
  case 0
  then show ?case by simp
next
  case (Suc a)
  then have "concat (map (fixed_length_sublist v d) [0..<a]) = take (a * d) v" by auto
  then have "concat (map (fixed_length_sublist v d) [0..<Suc a]) =
        take (a * d) v @ fixed_length_sublist v d a" using fixed_length_sublist_def by auto
  then show ?case using Suc by (metis add.commute mult.commute mult_Suc take_add fixed_length_sublist_def)
qed

lemma concat_parts_eq:
assumes "a * d = length v"
shows "concat (map (fixed_length_sublist v d) [0..<a]) = v"
by (simp add: concat_parts_leq assms)

lemma tensor_lookup_base:
assumes "length v = prod_list ds"
and "\<And>is. is \<lhd> ds \<Longrightarrow> lookup_base ds v is = e is"
shows "tensor_vec_from_lookup ds e = v"
using assms proof (induction ds arbitrary:v e)
  case Nil
  then show ?case unfolding tensor_vec_from_lookup.simps
    by (metis One_nat_def Tensor.lookup_base_Nil length_0_conv length_Suc_conv list.sel(1) prod_list.Nil valid_index.Nil)
next
  case (Cons a ds)
  then have "a * prod_list ds = length v" by auto
  {
    fix i assume "i<a"
    then have "prod_list ds * (i+1) \<le> length v" using \<open>a * prod_list ds = length v\<close> using discrete mult.commute mult_le_mono1 by metis
    have "\<And>is'. is' \<lhd> ds \<Longrightarrow> e (i # is') = lookup_base ds (fixed_length_sublist v (prod_list ds) i) is'"
      using \<open>i<a\<close> by (metis Cons.prems(2) Tensor.lookup_base_Cons valid_index.simps)
    then have "tensor_vec_from_lookup ds (\<lambda>is'. e (i # is')) = fixed_length_sublist v (prod_list ds) i"
      using Cons using \<open>prod_list ds * (i + 1) \<le> length v\<close> by (simp add: Cons.IH fixed_length_sublist_def)
  }
  then show ?case unfolding tensor_vec_from_lookup_Cons lookup_base_Cons
    using   concat_parts_eq[OF \<open>a * prod_list ds = length v\<close>]
     atLeastLessThan_iff map_eq_conv set_upt Cons by (metis (no_types, lifting))
qed

lemma tensor_lookup:
assumes "\<And>is. is \<lhd> dims A \<Longrightarrow> lookup A is = e is"
shows "tensor_from_lookup (dims A) e = A"
using tensor_lookup_base lookup_def length_vec tensor_from_lookup_def by (metis assms tensor_from_vec_simp)

lemma concat_equal_length:
assumes "\<And>xs. xs\<in>set xss \<Longrightarrow> length xs = l"
shows "length (concat xss) = length xss*l"
using assms by (induction xss;auto)

lemma concat_equal_length_map:
assumes "\<And>i. i<a \<Longrightarrow> length (f i) = d"
shows "length (concat (map (\<lambda>i. f i) [0..<a])) = a*d"
using assms by (induction a;auto)

lemma concat_parts:
assumes "\<And>xs. xs\<in>set xss \<Longrightarrow> length xs = d" and "i<length xss"
shows "fixed_length_sublist (concat xss) d i = xss ! i"
using assms proof (induction xss arbitrary:i)
  case Nil
  then show ?case by simp
next
  case (Cons xs xss)
  then have "length (concat xss) = length xss * d" by (simp add: Cons.prems(1) concat_equal_length)
  show ?case
  proof (cases i)
    case 0
    then have "fixed_length_sublist (concat (xs # xss)) d i = xs"
      unfolding fixed_length_sublist_def by (simp add: Cons.prems(1))
    then show ?thesis using 0 by auto
  next
    case (Suc i')
    then have "fixed_length_sublist (concat xss) d i' = xss ! i'" using Cons by auto
    then show ?thesis unfolding fixed_length_sublist_def using Suc Cons.prems(1) by auto
  qed
qed

lemma concat_parts':
assumes "\<And>i. i<a \<Longrightarrow> length (f i) = d"
and "i<a"
shows "fixed_length_sublist (concat (map (\<lambda>i. f i) [0..<a])) d i = f i"
using assms proof (induction a)
  case 0
  then show ?case by simp
next
  case (Suc a)
  then have "(\<And>i. i < a \<Longrightarrow> length (f i) = d)" by auto
  then have "length (concat (map f [0..<a])) = a*d" using concat_equal_length_map by auto
  show ?case
  proof (cases "i=a")
    assume "i=a"
    then have "fixed_length_sublist (concat (map f [0..<Suc a])) d i = f a"
      by (simp add: Suc.prems(1) \<open>length (concat (map f [0..<a])) = a * d\<close> fixed_length_sublist_def)
    then show ?case using \<open>i=a\<close> by auto
  next
    assume "i\<noteq>a"
    then have "fixed_length_sublist (concat (map f [0..<a])) d i = f i"
      "concat (map f [0..<Suc a]) = concat (map f [0..<a]) @ f a" using Suc by auto
    show ?case unfolding \<open>concat (map f [0..<Suc a]) = concat (map f [0..<a]) @ f a\<close>
      unfolding fixed_length_sublist_def drop_append
      using  \<open>length (concat (map f [0..<a])) = a * d\<close>  \<open>fixed_length_sublist (concat (map f [0..<a])) d i = f i\<close>
      using append_assoc append_eq_conv_conj append_take_drop_id assms(1) assms(2)  fixed_length_sublist_def
      by metis
  qed
qed

lemma length_tensor_vec_from_lookup:
"length (tensor_vec_from_lookup ds e) = prod_list ds"
by (induction ds arbitrary:e; auto simp add: concat_equal_length_map)

lemma lookup_tensor_vec:
assumes "is\<lhd>ds"
shows "lookup_base ds (tensor_vec_from_lookup ds e) is = e is"
using assms proof (induction arbitrary:e rule:valid_index.induct)
  case Nil
  then show ?case by simp
next
  case (Cons "is" ds i d e)
  then show ?case unfolding tensor_vec_from_lookup_Cons lookup_base_Cons
    by (simp add: length_tensor_vec_from_lookup concat_parts'[of d "\<lambda>i. tensor_vec_from_lookup ds (\<lambda>is. e (i # is))" "prod_list ds" i] \<open>i < d\<close>)
qed

lemma lookup_tensor_from_lookup:
assumes "is\<lhd>ds"
shows "lookup (tensor_from_lookup ds e) is = e is"
  unfolding lookup_def tensor_from_lookup_def
  by (simp add: lookup_tensor_vec assms length_tensor_vec_from_lookup)

lemma dims_tensor_from_lookup: "dims (tensor_from_lookup ds e) = ds"
  unfolding tensor_from_lookup_def
  by (simp add: length_tensor_vec_from_lookup)

lemma tensor_lookup_cong:
assumes "tensor_from_lookup ds e\<^sub>1 = tensor_from_lookup ds e\<^sub>2"
and "is\<lhd>ds"
shows "e\<^sub>1 is = e\<^sub>2 is" using assms lookup_tensor_from_lookup by metis

lemma tensor_from_lookup_eqI:
assumes "\<And>is. is\<lhd>ds \<Longrightarrow> e\<^sub>1 is = e\<^sub>2 is"
shows "tensor_from_lookup ds e\<^sub>1 = tensor_from_lookup ds e\<^sub>2"
by (metis assms lookup_tensor_vec length_tensor_vec_from_lookup tensor_lookup_base tensor_from_lookup_def)

lemma tensor_lookup_eqI:
assumes "dims A = dims B" and "\<And>is. is\<lhd>(dims A) \<Longrightarrow> lookup A is = lookup B is"
shows "A = B" by (metis assms(1) assms(2) tensor_lookup)

end
