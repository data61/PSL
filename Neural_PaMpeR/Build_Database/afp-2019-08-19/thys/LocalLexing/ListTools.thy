theory ListTools
imports Main
begin

definition is_first :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "is_first x u = (\<exists> v. u = [x]@v)"

definition is_last :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "is_last x u = (\<exists> v. u = v@[x])"

definition is_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "is_prefix u v = (\<exists> w. u@w = v)"

definition is_proper_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "is_proper_prefix u v = (\<exists> w. w \<noteq> [] \<and> u@w = v)"

lemma is_prefix_eq_proper_prefix: "is_prefix a b = (a = b \<or> is_proper_prefix a b)"
by (metis append_Nil2 is_prefix_def is_proper_prefix_def)

lemma is_proper_prefix_eq_prefix: "is_proper_prefix a b = (a \<noteq> b \<and> is_prefix a b)"
by (metis append_self_conv is_prefix_eq_proper_prefix is_proper_prefix_def)

definition is_suffix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "is_suffix u v = (\<exists> w. w@u = v)"

definition is_proper_suffix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "is_proper_suffix u v = (\<exists> w. w \<noteq> [] \<and> w@u = v)"

lemma is_suffix_eq_proper_suffix: "is_suffix a b = (a = b \<or> is_proper_suffix a b)"
by (metis append_Nil is_proper_suffix_def is_suffix_def)

lemma is_proper_suffix_eq_suffix: "is_proper_suffix a b = (a \<noteq> b \<and> is_suffix a b)"
by (metis is_proper_suffix_def is_suffix_eq_proper_suffix self_append_conv2)

lemma is_prefix_unsplit: "is_prefix u a \<Longrightarrow> u @ (drop (length u) a) = a"
  by (metis append_eq_conv_conj is_prefix_def)

lemma le_take_same: "i \<le> j \<Longrightarrow> take j a = take j b \<Longrightarrow> take i a = take i b"
 by (metis min.absorb1 take_take)

lemma is_first_drop_length: 
  assumes "k \<le> length a" 
  and "k > length u"
  and "v = X#w" 
  and "take k a = take k (u@v)"
  shows "is_first X (drop (length u) a)"
proof -
  let ?d = "k - length u"
  from assms have pos_d': "?d > 0" by auto
  from assms have take_d'_v: "take ?d (drop (length u) a) = take ?d v"
    by (metis append_eq_conv_conj drop_take)
  then have "take 1 (drop (length u) a) = take 1 v"
    by (metis One_nat_def Suc_leI le_take_same pos_d')
  then have "take 1 (drop (length u) a) = [X]"
    by (simp add: assms)
  then show ?thesis
    by (metis append_take_drop_id is_first_def)
qed

lemma is_first_cons: "is_first x (y#ys) = (x = y)"
  by (auto simp add: is_first_def)

lemma list_all_pos_neg_ex: "list_all P D \<Longrightarrow> \<not> (list_all Q D) \<Longrightarrow> 
       \<exists> k. k < length D \<and> P(D ! k) \<and> \<not>(Q(D ! k))"
using list_all_length by blast

lemma split_list_at: "k < length D \<Longrightarrow> D = (take k D)@[D ! k]@(drop (Suc k) D)"
  by (metis append_Cons append_Nil id_take_nth_drop)

lemma take_eq_take_append: "i \<le> j \<Longrightarrow> j \<le> length a \<Longrightarrow> \<exists> u. take j a = take i a @ u"
  by (metis le_Suc_ex take_add)

lemma is_proper_suffix_length_cmp: "is_proper_suffix a b \<Longrightarrow> length a < length b"
by (metis add_diff_cancel_right' append_Nil append_eq_append_conv 
  diff_is_0_eq is_proper_suffix_def leI length_append list.size(3))


end
