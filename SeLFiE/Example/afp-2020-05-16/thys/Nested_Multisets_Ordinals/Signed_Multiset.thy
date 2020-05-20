(*  Title:       Signed (Finite) Multisets
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Signed (Finite) Multisets\<close>

theory Signed_Multiset
imports Multiset_More
abbrevs
  "!z" = "\<^sub>z"
begin


subsection \<open>Definition of Signed Multisets\<close>

definition equiv_zmset :: "'a multiset \<times> 'a multiset \<Rightarrow> 'a multiset \<times> 'a multiset \<Rightarrow> bool" where
  "equiv_zmset = (\<lambda>(Mp, Mn) (Np, Nn). Mp + Nn = Np + Mn)"

quotient_type 'a zmultiset = "'a multiset \<times> 'a multiset" / equiv_zmset
  by (rule equivpI, simp_all add: equiv_zmset_def reflp_def symp_def transp_def)
    (metis multi_union_self_other_eq union_lcomm)


subsection \<open>Basic Operations on Signed Multisets\<close>

instantiation zmultiset :: (type) cancel_comm_monoid_add
begin

lift_definition zero_zmultiset :: "'a zmultiset" is "({#}, {#})" .

abbreviation empty_zmset :: "'a zmultiset" ("{#}\<^sub>z") where
  "empty_zmset \<equiv> 0"

lift_definition minus_zmultiset :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> 'a zmultiset" is
  "\<lambda>(Mp, Mn) (Np, Nn). (Mp + Nn, Mn + Np)"
  by (auto simp: equiv_zmset_def union_commute union_lcomm)

lift_definition plus_zmultiset :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> 'a zmultiset" is
  "\<lambda>(Mp, Mn) (Np, Nn). (Mp + Np, Mn + Nn)"
  by (auto simp: equiv_zmset_def union_commute union_lcomm)

instance
  by (intro_classes; transfer) (auto simp: equiv_zmset_def)

end

instantiation zmultiset :: (type) group_add
begin

lift_definition uminus_zmultiset :: "'a zmultiset \<Rightarrow> 'a zmultiset" is "\<lambda>(Mp, Mn). (Mn, Mp)"
  by (auto simp: equiv_zmset_def add.commute)

instance
  by (intro_classes; transfer) (auto simp: equiv_zmset_def)

end

lift_definition zcount :: "'a zmultiset \<Rightarrow> 'a \<Rightarrow> int" is
  "\<lambda>(Mp, Mn) x. int (count Mp x) - int (count Mn x)"
  by (auto simp del: of_nat_add simp: equiv_zmset_def fun_eq_iff multiset_eq_iff diff_eq_eq
    diff_add_eq eq_diff_eq of_nat_add[symmetric])

lemma zcount_inject: "zcount M = zcount N \<longleftrightarrow> M = N"
  by transfer (auto simp del: of_nat_add simp: equiv_zmset_def fun_eq_iff multiset_eq_iff
    diff_eq_eq diff_add_eq eq_diff_eq of_nat_add[symmetric])

lemma zmultiset_eq_iff: "M = N \<longleftrightarrow> (\<forall>a. zcount M a = zcount N a)"
  by (simp only: zcount_inject[symmetric] fun_eq_iff)

lemma zmultiset_eqI: "(\<And>x. zcount A x = zcount B x) \<Longrightarrow> A = B"
  using zmultiset_eq_iff by auto

lemma zcount_uminus[simp]: "zcount (- A) x = - zcount A x"
  by transfer auto

lift_definition add_zmset :: "'a \<Rightarrow> 'a zmultiset \<Rightarrow> 'a zmultiset" is
  "\<lambda>x (Mp, Mn). (add_mset x Mp, Mn)"
  by (auto simp: equiv_zmset_def)

syntax
  "_zmultiset" :: "args \<Rightarrow> 'a zmultiset" ("{#(_)#}\<^sub>z")
translations
  "{#x, xs#}\<^sub>z" == "CONST add_zmset x {#xs#}\<^sub>z"
  "{#x#}\<^sub>z" == "CONST add_zmset x {#}\<^sub>z"

lemma zcount_empty[simp]: "zcount {#}\<^sub>z a = 0"
  by transfer auto

lemma zcount_add_zmset[simp]:
  "zcount (add_zmset b A) a = (if b = a then zcount A a + 1 else zcount A a)"
  by transfer auto

lemma zcount_single: "zcount {#b#}\<^sub>z a = (if b = a then 1 else 0)"
  by simp

lemma add_add_same_iff_zmset[simp]: "add_zmset a A = add_zmset a B \<longleftrightarrow> A = B"
  by (auto simp: zmultiset_eq_iff)

lemma add_zmset_commute: "add_zmset x (add_zmset y M) = add_zmset y (add_zmset x M)"
  by (auto simp: zmultiset_eq_iff)

lemma
  singleton_ne_empty_zmset[simp]: "{#x#}\<^sub>z \<noteq> {#}\<^sub>z" and
  empty_ne_singleton_zmset[simp]: "{#}\<^sub>z \<noteq> {#x#}\<^sub>z"
  by (auto dest!: arg_cong2[of _ _ x _ zcount])

lemma
  singleton_ne_uminus_singleton_zmset[simp]: "{#x#}\<^sub>z \<noteq> - {#y#}\<^sub>z" and
  uminus_singleton_ne_singleton_zmset[simp]: "- {#x#}\<^sub>z \<noteq> {#y#}\<^sub>z"
  by (auto dest!: arg_cong2[of _ _ x x zcount] split: if_splits)


subsubsection \<open>Conversion to Set and Membership\<close>

definition set_zmset :: "'a zmultiset \<Rightarrow> 'a set" where
  "set_zmset M = {x. zcount M x \<noteq> 0}"

abbreviation elem_zmset :: "'a \<Rightarrow> 'a zmultiset \<Rightarrow> bool" where
  "elem_zmset a M \<equiv> a \<in> set_zmset M"

notation
  elem_zmset ("'(\<in>#\<^sub>z')") and
  elem_zmset ("(_/ \<in>#\<^sub>z _)" [51, 51] 50)

notation (ASCII)
  elem_zmset ("'(:#z')") and
  elem_zmset ("(_/ :#z _)" [51, 51] 50)

abbreviation not_elem_zmset :: "'a \<Rightarrow> 'a zmultiset \<Rightarrow> bool" where
  "not_elem_zmset a M \<equiv> a \<notin> set_zmset M"

notation
  not_elem_zmset ("'(\<notin>#\<^sub>z')") and
  not_elem_zmset ("(_/ \<notin>#\<^sub>z _)" [51, 51] 50)

notation (ASCII)
  not_elem_zmset ("'(~:#z')") and
  not_elem_zmset ("(_/ ~:#z _)" [51, 51] 50)

context
begin

qualified abbreviation Ball :: "'a zmultiset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Ball M \<equiv> Set.Ball (set_zmset M)"

qualified abbreviation Bex :: "'a zmultiset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Bex M \<equiv> Set.Bex (set_zmset M)"

end

syntax
  "_MBall" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool" ("(3\<forall>_\<in>#\<^sub>z_./ _)" [0, 0, 10] 10)
  "_MBex" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool" ("(3\<exists>_\<in>#\<^sub>z_./ _)" [0, 0, 10] 10)

syntax (ASCII)
  "_MBall" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool" ("(3\<forall>_:#\<^sub>z_./ _)" [0, 0, 10] 10)
  "_MBex" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool" ("(3\<exists>_:#\<^sub>z_./ _)" [0, 0, 10] 10)

translations
  "\<forall>x\<in>#\<^sub>zA. P" \<rightleftharpoons> "CONST Signed_Multiset.Ball A (\<lambda>x. P)"
  "\<exists>x\<in>#\<^sub>zA. P" \<rightleftharpoons> "CONST Signed_Multiset.Bex A (\<lambda>x. P)"

lemma zcount_eq_zero_iff: "zcount M x = 0 \<longleftrightarrow> x \<notin>#\<^sub>z M"
  by (auto simp add: set_zmset_def)

lemma not_in_iff_zmset: "x \<notin>#\<^sub>z M \<longleftrightarrow> zcount M x = 0"
  by (auto simp add: zcount_eq_zero_iff)

lemma zcount_ne_zero_iff[simp]: "zcount M x \<noteq> 0 \<longleftrightarrow> x \<in>#\<^sub>z M"
  by (auto simp add: set_zmset_def)

lemma zcount_inI:
  assumes "zcount M x = 0 \<Longrightarrow> False"
  shows "x \<in>#\<^sub>z M"
proof (rule ccontr)
  assume "x \<notin>#\<^sub>z M"
  with assms show False by (simp add: not_in_iff_zmset)
qed

lemma set_zmset_empty[simp]: "set_zmset {#}\<^sub>z = {}"
  by (simp add: set_zmset_def)

lemma set_zmset_single: "set_zmset {#b#}\<^sub>z = {b}"
  by (simp add: set_zmset_def)

lemma set_zmset_eq_empty_iff[simp]: "set_zmset M = {} \<longleftrightarrow> M = {#}\<^sub>z"
  by (auto simp add: zmultiset_eq_iff zcount_eq_zero_iff)

lemma finite_count_ne: "finite {x. count M x \<noteq> count N x}"
proof -
  have "{x. count M x \<noteq> count N x} \<subseteq> set_mset M \<union> set_mset N"
    by (auto simp: not_in_iff)
  moreover have "finite (set_mset M \<union> set_mset N)"
    by (rule finite_UnI[OF finite_set_mset finite_set_mset])
  ultimately show ?thesis
    by (rule finite_subset)
qed

lemma finite_set_zmset[iff]: "finite (set_zmset M)"
  unfolding set_zmset_def by transfer (auto intro: finite_count_ne)

lemma zmultiset_nonemptyE[elim]:
  assumes "A \<noteq> {#}\<^sub>z"
  obtains x where "x \<in>#\<^sub>z A"
proof -
  have "\<exists>x. x \<in>#\<^sub>z A"
    by (rule ccontr) (insert assms, auto)
  with that show ?thesis
    by blast
qed


subsubsection \<open>Union\<close>

lemma zcount_union[simp]: "zcount (M + N) a = zcount M a + zcount N a"
  by transfer auto

lemma union_add_left_zmset[simp]: "add_zmset a A + B = add_zmset a (A + B)"
  by (auto simp: zmultiset_eq_iff)

lemma union_zmset_add_zmset_right[simp]: "A + add_zmset a B = add_zmset a (A + B)"
  by (auto simp: zmultiset_eq_iff)

lemma add_zmset_add_single: \<open>add_zmset a A = A + {#a#}\<^sub>z\<close>
  by (subst union_zmset_add_zmset_right, subst add.comm_neutral) (rule refl)


subsubsection \<open>Difference\<close>

lemma zcount_diff[simp]: "zcount (M - N) a = zcount M a - zcount N a"
  by transfer auto

lemma add_zmset_diff_bothsides: \<open>add_zmset a M - add_zmset a A = M - A\<close>
  by (auto simp: zmultiset_eq_iff)

lemma in_diff_zcount: "a \<in>#\<^sub>z M - N \<longleftrightarrow> zcount N a \<noteq> zcount M a"
  by (fastforce simp: set_zmset_def)

lemma diff_add_zmset:
  fixes M N Q :: "'a zmultiset"
  shows "M - (N + Q) = M - N - Q"
  by (rule sym) (fact diff_diff_add)

lemma insert_Diff_zmset[simp]: "add_zmset x (M - {#x#}\<^sub>z) = M"
  by (clarsimp simp: zmultiset_eq_iff)

lemma diff_union_swap_zmset: "add_zmset b (M - {#a#}\<^sub>z) = add_zmset b M - {#a#}\<^sub>z"
  by (auto simp add: zmultiset_eq_iff)

lemma diff_add_zmset_swap[simp]: "add_zmset b M - A = add_zmset b (M - A)"
  by (auto simp add: zmultiset_eq_iff)

lemma diff_diff_add_zmset[simp]: "(M :: 'a zmultiset) - N - P = M - (N + P)"
  by (rule diff_diff_add)

lemma zmset_add[elim?]:
  obtains B where "A = add_zmset a B"
proof -
  have "A = add_zmset a (A - {#a#}\<^sub>z)"
    by simp
  with that show thesis .
qed


subsubsection \<open>Equality of Signed Multisets\<close>

lemma single_eq_single_zmset[simp]: "{#a#}\<^sub>z = {#b#}\<^sub>z \<longleftrightarrow> a = b"
  by (auto simp add: zmultiset_eq_iff)

lemma multi_self_add_other_not_self_zmset[simp]: "M = add_zmset x M \<longleftrightarrow> False"
  by (auto simp add: zmultiset_eq_iff)

lemma add_zmset_remove_trivial: \<open>add_zmset x M - {#x#}\<^sub>z = M\<close>
  by simp

lemma diff_single_eq_union_zmset: "M - {#x#}\<^sub>z = N \<longleftrightarrow> M = add_zmset x N"
  by auto

lemma union_single_eq_diff_zmset: "add_zmset x M = N \<Longrightarrow> M = N - {#x#}\<^sub>z"
  unfolding add_zmset_add_single[of _ M] by (fact add_implies_diff)

lemma add_zmset_eq_conv_diff:
  "add_zmset a M = add_zmset b N \<longleftrightarrow>
   M = N \<and> a = b \<or> M = add_zmset b (N - {#a#}\<^sub>z) \<and> N = add_zmset a (M - {#b#}\<^sub>z)"
  by (simp add: zmultiset_eq_iff) fastforce

lemma add_zmset_eq_conv_ex:
  "(add_zmset a M = add_zmset b N) =
    (M = N \<and> a = b \<or> (\<exists>K. M = add_zmset b K \<and> N = add_zmset a K))"
  by (auto simp add: add_zmset_eq_conv_diff)

lemma multi_member_split: "\<exists>A. M = add_zmset x A"
  by (rule exI[where x = "M - {#x#}\<^sub>z"]) simp


subsection \<open>Conversions from and to Multisets\<close>

lift_definition zmset_of :: "'a multiset \<Rightarrow> 'a zmultiset" is "\<lambda>f. (Abs_multiset f, {#})" .

lemma zmset_of_inject[simp]: "zmset_of M = zmset_of N \<longleftrightarrow> M = N"
  by (simp add: zmset_of_def, transfer, auto simp: equiv_zmset_def)

lemma zmset_of_empty[simp]: "zmset_of {#} = {#}\<^sub>z"
  by (simp add: zmset_of_def zero_zmultiset_def)

lemma zmset_of_add_mset[simp]: "zmset_of (add_mset x M) = add_zmset x (zmset_of M)"
  by transfer (auto simp: equiv_zmset_def add_mset_def cong: if_cong)

lemma zcount_of_mset[simp]: "zcount (zmset_of M) x = int (count M x)"
  by (induct M) auto

lemma zmset_of_plus: "zmset_of (M + N) = zmset_of M + zmset_of N"
  by (transfer, auto simp: equiv_zmset_def eq_onp_same_args plus_multiset.abs_eq)+

lift_definition mset_pos :: "'a zmultiset \<Rightarrow> 'a multiset" is "\<lambda>(Mp, Mn). count (Mp - Mn)"
  by (clarsimp simp: equiv_zmset_def intro!: arg_cong[of _ _ count])
    (metis add.commute add_diff_cancel_right)

lift_definition mset_neg :: "'a zmultiset \<Rightarrow> 'a multiset" is "\<lambda>(Mp, Mn). count (Mn - Mp)"
  by (clarsimp simp: equiv_zmset_def intro!: arg_cong[of _ _ count])
    (metis add.commute add_diff_cancel_right)

lemma
  zmset_of_inverse[simp]: "mset_pos (zmset_of M) = M" and
  minus_zmset_of_inverse[simp]: "mset_neg (- zmset_of M) = M"
  by (transfer, simp)+

lemma neg_zmset_pos[simp]: "mset_neg (zmset_of M) = {#}"
  by (rule zmset_of_inject[THEN iffD1], simp, transfer, auto simp: equiv_zmset_def)+

lemma
  count_mset_pos[simp]: "count (mset_pos M) x = nat (zcount M x)" and
  count_mset_neg[simp]: "count (mset_neg M) x = nat (- zcount M x)"
  by (transfer; auto)+

lemma
  mset_pos_empty[simp]: "mset_pos {#}\<^sub>z = {#}" and
  mset_neg_empty[simp]: "mset_neg {#}\<^sub>z = {#}"
  by (rule multiset_eqI, simp)+

lemma
  mset_pos_singleton[simp]: "mset_pos {#x#}\<^sub>z = {#x#}" and
  mset_neg_singleton[simp]: "mset_neg {#x#}\<^sub>z = {#}"
  by (rule multiset_eqI, simp)+

lemma
  mset_pos_neg_partition: "M = zmset_of (mset_pos M) - zmset_of (mset_neg M)" and
  mset_pos_as_neg: "zmset_of (mset_pos M) = zmset_of (mset_neg M) + M" and
  mset_neg_as_pos: "zmset_of (mset_neg M) = zmset_of (mset_pos M) - M"
  by (rule zmultiset_eqI, simp)+

lemma mset_pos_uminus[simp]: "mset_pos (- A) = mset_neg A"
  by (rule multiset_eqI) simp

lemma mset_neg_uminus[simp]: "mset_neg (- A) = mset_pos A"
  by (rule multiset_eqI) simp

lemma mset_pos_plus[simp]:
  "mset_pos (A + B) = (mset_pos A - mset_neg B) + (mset_pos B - mset_neg A)"
  by (rule multiset_eqI) simp

lemma mset_neg_plus[simp]:
  "mset_neg (A + B) = (mset_neg A - mset_pos B) + (mset_neg B - mset_pos A)"
  by (rule multiset_eqI) simp

lemma mset_pos_diff[simp]:
  "mset_pos (A - B) = (mset_pos A - mset_pos B) + (mset_neg B - mset_neg A)"
  by (rule mset_pos_plus[of A "- B", simplified])

lemma mset_neg_diff[simp]:
  "mset_neg (A - B) = (mset_neg A - mset_neg B) + (mset_pos B - mset_pos A)"
  by (rule mset_neg_plus[of A "- B", simplified])

lemma mset_pos_neg_dual:
  "mset_pos a + mset_pos b + (mset_neg a - mset_pos b) + (mset_neg b - mset_pos a) =
   mset_neg a + mset_neg b + (mset_pos a - mset_neg b) + (mset_pos b - mset_neg a)"
  using [[linarith_split_limit = 20]] by (rule multiset_eqI) simp

lemma decompose_zmset_of2:
  obtains A B C where
    "M = zmset_of A + C" and
    "N = zmset_of B + C"
proof
  let ?A = "zmset_of (mset_pos M + mset_neg N)"
  let ?B = "zmset_of (mset_pos N + mset_neg M)"
  let ?C = "- (zmset_of (mset_neg M) + zmset_of (mset_neg N))"

  show "M = ?A + ?C"
    by (simp add: zmset_of_plus mset_pos_neg_partition)
  show "N = ?B + ?C"
    by (simp add: zmset_of_plus diff_add_zmset mset_pos_neg_partition)
qed


subsubsection \<open>Pointwise Ordering Induced by @{const zcount}\<close>

definition subseteq_zmset :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> bool" (infix "\<subseteq>#\<^sub>z" 50) where
  "A \<subseteq>#\<^sub>z B \<longleftrightarrow> (\<forall>a. zcount A a \<le> zcount B a)"

definition subset_zmset :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> bool" (infix "\<subset>#\<^sub>z" 50) where
  "A \<subset>#\<^sub>z B \<longleftrightarrow> A \<subseteq>#\<^sub>z B \<and> A \<noteq> B"

abbreviation (input)
  supseteq_zmset :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> bool" (infix "\<supseteq>#\<^sub>z" 50)
where
  "supseteq_zmset A B \<equiv> B \<subseteq>#\<^sub>z A"

abbreviation (input)
  supset_zmset :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> bool" (infix "\<supset>#\<^sub>z" 50)
where
  "supset_zmset A B \<equiv> B \<subset>#\<^sub>z A"

notation (input)
  subseteq_zmset (infix "\<subseteq>#\<^sub>z" 50) and
  supseteq_zmset (infix "\<supseteq>#\<^sub>z" 50)

notation (ASCII)
  subseteq_zmset (infix "\<subseteq>#\<^sub>z" 50) and
  subset_zmset (infix "\<subset>#\<^sub>z" 50) and
  supseteq_zmset (infix "\<supseteq>#\<^sub>z" 50) and
  supset_zmset (infix ">#\<^sub>z" 50)

interpretation subset_zmset: ordered_ab_semigroup_add_imp_le "(+)" "(-)" "(\<subseteq>#\<^sub>z)" "(\<subset>#\<^sub>z)"
  by unfold_locales (auto simp add: subset_zmset_def subseteq_zmset_def zmultiset_eq_iff
    intro: order_trans antisym)

interpretation subset_zmset:
  ordered_ab_semigroup_monoid_add_imp_le "(+)" 0 "(-)" "(\<subseteq>#\<^sub>z)" "(\<subset>#\<^sub>z)"
  by unfold_locales

lemma zmset_subset_eqI: "(\<And>a. zcount A a \<le> zcount B a) \<Longrightarrow> A \<subseteq>#\<^sub>z B"
  by (simp add: subseteq_zmset_def)

lemma zmset_subset_eq_zcount: "A \<subseteq>#\<^sub>z B \<Longrightarrow> zcount A a \<le> zcount B a"
  by (simp add: subseteq_zmset_def)

lemma zmset_subset_eq_add_zmset_cancel: \<open>add_zmset a A \<subseteq>#\<^sub>z add_zmset a B \<longleftrightarrow> A \<subseteq>#\<^sub>z B\<close>
  unfolding add_zmset_add_single[of _ A] add_zmset_add_single[of _ B]
  by (rule subset_zmset.add_le_cancel_right)

lemma zmset_subset_eq_zmultiset_union_diff_commute:
  "A - B + C = A + C - B" for A B C :: "'a zmultiset"
  by (simp add: add.commute add_diff_eq)

lemma zmset_subset_eq_insertD: "add_zmset x A \<subseteq>#\<^sub>z B \<Longrightarrow> A \<subset>#\<^sub>z B"
  unfolding subset_zmset_def subseteq_zmset_def
  by (metis (no_types) add.commute add_le_same_cancel2 zcount_add_zmset dual_order.trans le_cases
    le_numeral_extra(2))

lemma zmset_subset_insertD: "add_zmset x A \<subset>#\<^sub>z B \<Longrightarrow> A \<subset>#\<^sub>z B"
  by (rule zmset_subset_eq_insertD) (rule subset_zmset.less_imp_le)

lemma subset_eq_diff_conv_zmset: "A - C \<subseteq>#\<^sub>z B \<longleftrightarrow> A \<subseteq>#\<^sub>z B + C"
  by (simp add: subseteq_zmset_def ordered_ab_group_add_class.diff_le_eq)

lemma multi_psub_of_add_self_zmset[simp]: "A \<subset>#\<^sub>z add_zmset x A"
  by (auto simp: subset_zmset_def subseteq_zmset_def)

lemma multi_psub_self_zmset: "A \<subset>#\<^sub>z A = False"
  by simp

lemma zmset_subset_add_zmset[simp]: "add_zmset x N \<subset>#\<^sub>z add_zmset x M \<longleftrightarrow> N \<subset>#\<^sub>z M"
  unfolding add_zmset_add_single[of _ N] add_zmset_add_single[of _ M]
  by (fact subset_zmset.add_less_cancel_right)

lemma zmset_of_subseteq_iff[simp]: "zmset_of M \<subseteq>#\<^sub>z zmset_of N \<longleftrightarrow> M \<subseteq># N"
  by (simp add: subseteq_zmset_def subseteq_mset_def)

lemma zmset_of_subset_iff[simp]: "zmset_of M \<subset>#\<^sub>z zmset_of N \<longleftrightarrow> M \<subset># N"
  by (simp add: subset_zmset_def subset_mset_def)

lemma
  mset_pos_supset: "A \<subseteq>#\<^sub>z zmset_of (mset_pos A)" and
  mset_neg_supset: "- A \<subseteq>#\<^sub>z zmset_of (mset_neg A)"
  by (auto intro: zmset_subset_eqI)

lemma subset_mset_zmsetE:
  assumes "M \<subset>#\<^sub>z N"
  obtains A B C where
    "M = zmset_of A + C" and "N = zmset_of B + C" and "A \<subset># B"
  by (metis assms decompose_zmset_of2 subset_zmset.add_less_cancel_right zmset_of_subset_iff)

lemma subseteq_mset_zmsetE:
  assumes "M \<subseteq>#\<^sub>z N"
  obtains A B C where
    "M = zmset_of A + C" and "N = zmset_of B + C" and "A \<subseteq># B"
  by (metis assms add.commute add.right_neutral subset_mset.order_refl subset_mset_def
    subset_mset_zmsetE subset_zmset_def zmset_of_empty)


subsubsection \<open>Subset is an Order\<close>

interpretation subset_zmset: order "(\<subseteq>#\<^sub>z)" "(\<subset>#\<^sub>z)"
  by unfold_locales


subsection \<open>Replicate and Repeat Operations\<close>

definition replicate_zmset :: "nat \<Rightarrow> 'a \<Rightarrow> 'a zmultiset" where
  "replicate_zmset n x = (add_zmset x ^^ n) {#}\<^sub>z"

lemma replicate_zmset_0[simp]: "replicate_zmset 0 x = {#}\<^sub>z"
  unfolding replicate_zmset_def by simp

lemma replicate_zmset_Suc[simp]: "replicate_zmset (Suc n) x = add_zmset x (replicate_zmset n x)"
  unfolding replicate_zmset_def by (induct n) (auto intro: add.commute)

lemma count_replicate_zmset[simp]:
  "zcount (replicate_zmset n x) y = (if y = x then of_nat n else 0)"
  unfolding replicate_zmset_def by (induct n) auto

fun repeat_zmset :: "nat \<Rightarrow> 'a zmultiset \<Rightarrow> 'a zmultiset" where
  "repeat_zmset 0 _ = {#}\<^sub>z" |
  "repeat_zmset (Suc n) A = A + repeat_zmset n A"

lemma count_repeat_zmset[simp]: "zcount (repeat_zmset i A) a = of_nat i * zcount A a"
  by (induct i) (auto simp: semiring_normalization_rules(3))

lemma repeat_zmset_right[simp]: "repeat_zmset a (repeat_zmset b A) = repeat_zmset (a * b) A"
  by (auto simp: zmultiset_eq_iff left_diff_distrib')

lemma left_diff_repeat_zmset_distrib':
  \<open>i \<ge> j \<Longrightarrow> repeat_zmset (i - j) u = repeat_zmset i u - repeat_zmset j u\<close>
  by (auto simp: zmultiset_eq_iff int_distrib(3) of_nat_diff)

lemma left_add_mult_distrib_zmset:
  "repeat_zmset i u + (repeat_zmset j u + k) = repeat_zmset (i+j) u + k"
  by (auto simp: zmultiset_eq_iff add_mult_distrib int_distrib(1))

lemma repeat_zmset_distrib: "repeat_zmset (m + n) A = repeat_zmset m A + repeat_zmset n A"
  by (auto simp: zmultiset_eq_iff Nat.add_mult_distrib int_distrib(1))

lemma repeat_zmset_distrib2[simp]:
  "repeat_zmset n (A + B) = repeat_zmset n A + repeat_zmset n B"
  by (auto simp: zmultiset_eq_iff add_mult_distrib2 int_distrib(2))

lemma repeat_zmset_replicate_zmset[simp]: "repeat_zmset n {#a#}\<^sub>z = replicate_zmset n a"
  by (auto simp: zmultiset_eq_iff)

lemma repeat_zmset_distrib_add_zmset[simp]:
  "repeat_zmset n (add_zmset a A) = replicate_zmset n a + repeat_zmset n A"
  by (auto simp: zmultiset_eq_iff int_distrib(2))

lemma repeat_zmset_empty[simp]: "repeat_zmset n {#}\<^sub>z = {#}\<^sub>z"
  by (induct n) simp_all


subsubsection \<open>Filter (with Comprehension Syntax)\<close>

lift_definition filter_zmset :: "('a \<Rightarrow> bool) \<Rightarrow> 'a zmultiset \<Rightarrow> 'a zmultiset" is
  "\<lambda>P (Mp, Mn). (filter_mset P Mp, filter_mset P Mn)"
  by (auto simp del: filter_union_mset simp: equiv_zmset_def filter_union_mset[symmetric])

syntax (ASCII)
  "_MCollect" :: "pttrn \<Rightarrow> 'a zmultiset \<Rightarrow> bool \<Rightarrow> 'a zmultiset" ("(1{#_ :#z _./ _#})")
syntax
  "_MCollect" :: "pttrn \<Rightarrow> 'a zmultiset \<Rightarrow> bool \<Rightarrow> 'a zmultiset" ("(1{#_ \<in>#\<^sub>z _./ _#})")
translations
  "{#x \<in>#\<^sub>z M. P#}" == "CONST filter_zmset (\<lambda>x. P) M"

lemma count_filter_zmset[simp]:
  "zcount (filter_zmset P M) a = (if P a then zcount M a else 0)"
  by transfer auto

lemma filter_empty_zmset[simp]: "filter_zmset P {#}\<^sub>z = {#}\<^sub>z"
  by (rule zmultiset_eqI) simp

lemma filter_single_zmset: "filter_zmset P {#x#}\<^sub>z = (if P x then {#x#}\<^sub>z else {#}\<^sub>z)"
  by (rule zmultiset_eqI) simp

lemma filter_union_zmset[simp]: "filter_zmset P (M + N) = filter_zmset P M + filter_zmset P N"
  by (rule zmultiset_eqI) simp

lemma filter_diff_zmset[simp]: "filter_zmset P (M - N) = filter_zmset P M - filter_zmset P N"
  by (rule zmultiset_eqI) simp

lemma filter_add_zmset[simp]:
  "filter_zmset P (add_zmset x A) =
   (if P x then add_zmset x (filter_zmset P A) else filter_zmset P A)"
  by (auto simp: zmultiset_eq_iff)

lemma zmultiset_filter_mono:
  assumes "A \<subseteq>#\<^sub>z B"
  shows "filter_zmset f A \<subseteq>#\<^sub>z filter_zmset f B"
  using assms by (simp add: subseteq_zmset_def)

lemma filter_filter_zmset: "filter_zmset P (filter_zmset Q M) = {#x \<in># M. Q x \<and> P x#}"
  by (auto simp: zmultiset_eq_iff)

lemma
  filter_zmset_True[simp]: "{#y \<in>#\<^sub>z M. True#} = M" and
  filter_zmset_False[simp]: "{#y \<in>#\<^sub>z M. False#} = {#}\<^sub>z"
  by (auto simp: zmultiset_eq_iff)


subsection \<open>Uncategorized\<close>

lemma multi_drop_mem_not_eq_zmset: "B - {#c#}\<^sub>z \<noteq> B"
  by (simp add: diff_single_eq_union_zmset)

lemma zmultiset_partition: "M = {#x \<in>#\<^sub>z M. P x #} + {#x \<in>#\<^sub>z M. \<not> P x#}"
  by (subst zmultiset_eq_iff) auto


subsection \<open>Image\<close>

definition image_zmset :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a zmultiset \<Rightarrow> 'b zmultiset" where
  "image_zmset f M =
   zmset_of (fold_mset (add_mset \<circ> f) {#} (mset_pos M)) -
   zmset_of (fold_mset (add_mset \<circ> f) {#} (mset_neg M))"


subsection \<open>Multiset Order\<close>

instantiation zmultiset :: (preorder) order
begin

lift_definition less_zmultiset :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> bool" is
  "\<lambda>(Mp, Mn) (Np, Nn). Mp + Nn < Mn + Np"
proof (clarsimp simp: equiv_zmset_def)
  fix A1 B2 B1 A2 C1 D2 D1 C2 :: "'a multiset"
  assume
    ab: "A1 + A2 = B1 + B2" and
    cd: "C1 + C2 = D1 + D2"

  have "A1 + D2 < B2 + C1 \<longleftrightarrow> A1 + A2 + D2 < A2 + B2 + C1"
    by simp
  also have "\<dots> \<longleftrightarrow> B1 + B2 + D2 < A2 + B2 + C1"
    unfolding ab by (rule refl)
  also have "\<dots> \<longleftrightarrow> B1 + D2 < A2 + C1"
    by simp
  also have "\<dots> \<longleftrightarrow> B1 + D1 + D2 < A2 + C1 + D1"
    by simp
  also have "\<dots> \<longleftrightarrow> B1 + C1 + C2 < A2 + C1 + D1"
    using cd by (simp add: add.assoc)
  also have "\<dots> \<longleftrightarrow> B1 + C2 < A2 + D1"
    by simp
  finally show "A1 + D2 < B2 + C1 \<longleftrightarrow> B1 + C2 < A2 + D1"
    by assumption
qed

definition less_eq_zmultiset :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> bool" where
  "less_eq_zmultiset M' M \<longleftrightarrow> M' < M \<or> M' = M"

instance
proof ((intro_classes; unfold less_eq_zmultiset_def; transfer),
    auto simp: equiv_zmset_def union_commute)
  fix A1 B1 D C B2 A2 :: "'a multiset"
  assume ab: "A1 + A2 \<noteq> B1 + B2"

  {
    assume ab1: "A1 + C < B1 + D"

    {
      assume ab2: "D + A2 < C + B2"
      show "A1 + A2 < B1 + B2"
      proof -
        have f1: "\<And>m. D + A2 + m < C + B2 + m"
          using ab2 add_less_cancel_right by blast
        have "\<And>m. C + (A1 + m) < D + (B1 + m)"
          by (simp add: ab1 add.commute)
        then have "D + (A2 + A1) < D + (B1 + B2)"
          using f1 by (metis add.assoc add.commute mset_le_trans)
        then show ?thesis
          by (simp add: add.commute)
      qed
    }
    {
      assume ab2: "D + A2 = C + B2"
      show "A1 + A2 < B1 + B2"
      proof -
        have "\<And>m. C + A1 + m < D + B1 + m"
          by (simp add: ab1 add.commute)
        then have "D + (A2 + A1) < D + (B1 + B2)"
          by (metis (no_types) ab2 add.assoc add.commute)
        then show ?thesis
          by (simp add: add.commute)
      qed
    }
  }

  {
    assume ab1: "A1 + C = B1 + D"

    {
      assume ab2: "D + A2 < C + B2"
      show "A1 + A2 < B1 + B2"
      proof -
        have "A1 + (D + A2) < B1 + (D + B2)"
          by (metis (no_types) ab1 ab2 add.assoc add_less_cancel_left)
        then show ?thesis
          by simp
      qed
    }
    {
      assume ab2: "D + A2 = C + B2"
      have False
        by (metis (no_types) ab ab1 ab2 add.assoc add.commute add_diff_cancel_right')
      thus "A1 + A2 < B1 + B2"
        by sat
    }
  }
qed

end

instance zmultiset :: (preorder) ordered_cancel_comm_monoid_add
  by (intro_classes, unfold less_eq_zmultiset_def, transfer, auto simp: equiv_zmset_def)

instance zmultiset :: (preorder) ordered_ab_group_add
  by (intro_classes; transfer; auto simp: equiv_zmset_def)

instantiation zmultiset :: (linorder) distrib_lattice
begin

definition inf_zmultiset :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> 'a zmultiset" where
  "inf_zmultiset A B = (if A < B then A else B)"

definition sup_zmultiset :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> 'a zmultiset" where
  "sup_zmultiset A B = (if B > A then B else A)"

lemma not_lt_iff_ge_zmset: "\<not> x < y \<longleftrightarrow> x \<ge> y" for x y :: "'a zmultiset"
  by (unfold less_eq_zmultiset_def, transfer, auto simp: equiv_zmset_def algebra_simps)

instance
  by intro_classes (auto simp: less_eq_zmultiset_def inf_zmultiset_def sup_zmultiset_def
    dest!: not_lt_iff_ge_zmset[THEN iffD1])

end

lemma zmset_of_less: "zmset_of M < zmset_of N \<longleftrightarrow> M < N"
  by (clarsimp simp: zmset_of_def, transfer, simp)+

lemma zmset_of_le: "zmset_of M \<le> zmset_of N \<longleftrightarrow> M \<le> N"
  by (simp_all add: less_eq_zmultiset_def zmset_of_def; transfer; auto simp: equiv_zmset_def)

instance zmultiset :: (preorder) ordered_ab_semigroup_add
  by (intro_classes, unfold less_eq_zmultiset_def, transfer, auto simp: equiv_zmset_def)

lemma uminus_add_conv_diff_mset[cancelation_simproc_pre]: \<open>-a + b = b - a\<close> for a :: \<open>'a zmultiset\<close>
  by (simp add: add.commute)

lemma uminus_add_add_uminus[cancelation_simproc_pre]: \<open>b -a + c = b + c - a\<close> for a :: \<open>'a zmultiset\<close>
  by (simp add: uminus_add_conv_diff_mset zmset_subset_eq_zmultiset_union_diff_commute)

lemma add_zmset_eq_add_NO_MATCH[cancelation_simproc_pre]:
  \<open>NO_MATCH {#}\<^sub>z H \<Longrightarrow> add_zmset a H = {#a#}\<^sub>z + H\<close>
  by auto

lemma repeat_zmset_iterate_add: \<open>repeat_zmset n M = iterate_add n M\<close>
  unfolding iterate_add_def by (induction n) auto

declare repeat_zmset_iterate_add[cancelation_simproc_pre]

declare repeat_zmset_iterate_add[symmetric, cancelation_simproc_post]

simproc_setup zmseteq_cancel_numerals
  ("(l::'a zmultiset) + m = n" | "(l::'a zmultiset) = m + n" |
   "add_zmset a m = n" | "m = add_zmset a n" |
   "replicate_zmset p a = n" | "m = replicate_zmset p a" |
   "repeat_zmset p m = n" | "m = repeat_zmset p m") =
  \<open>fn phi => Cancel_Simprocs.eq_cancel\<close>

lemma zmset_subseteq_add_iff1:
  \<open>j \<le> i \<Longrightarrow> (repeat_zmset i u + m \<subseteq>#\<^sub>z repeat_zmset j u + n) = (repeat_zmset (i - j) u + m \<subseteq>#\<^sub>z n)\<close>
  by (simp add: add.commute add_diff_eq left_diff_repeat_zmset_distrib' subset_eq_diff_conv_zmset)

lemma zmset_subseteq_add_iff2:
  \<open>i \<le> j \<Longrightarrow> (repeat_zmset i u + m \<subseteq>#\<^sub>z repeat_zmset j u + n) = (m \<subseteq>#\<^sub>z repeat_zmset (j - i) u + n)\<close>
proof -
  assume "i \<le> j"
  then have "\<And>z. repeat_zmset j (z::'a zmultiset) - repeat_zmset i z = repeat_zmset (j - i) z"
    by (simp add: left_diff_repeat_zmset_distrib')
  then show ?thesis
    by (metis add.commute diff_diff_eq2 subset_eq_diff_conv_zmset)
qed

lemma zmset_subset_add_iff1:
  \<open>j \<le> i \<Longrightarrow> (repeat_zmset i u + m \<subset>#\<^sub>z repeat_zmset j u + n) = (repeat_zmset (i - j) u + m \<subset>#\<^sub>z n)\<close>
  by (simp add: subset_zmset.less_le_not_le zmset_subseteq_add_iff1 zmset_subseteq_add_iff2)

lemma zmset_subset_add_iff2:
  \<open>i \<le> j \<Longrightarrow> (repeat_zmset i u + m \<subset>#\<^sub>z repeat_zmset j u + n) = (m \<subset>#\<^sub>z repeat_zmset (j - i) u + n)\<close>
  by (simp add: subset_zmset.less_le_not_le zmset_subseteq_add_iff1 zmset_subseteq_add_iff2)

ML_file \<open>zmultiset_simprocs.ML\<close>

simproc_setup zmsetsubset_cancel
  ("(l::'a zmultiset) + m \<subset>#\<^sub>z n" | "(l::'a zmultiset) \<subset>#\<^sub>z m + n" |
   "add_zmset a m \<subset>#\<^sub>z n" | "m \<subset>#\<^sub>z add_zmset a n" |
   "replicate_zmset p a \<subset>#\<^sub>z n" | "m \<subset>#\<^sub>z replicate_zmset p a" |
   "repeat_zmset p m \<subset>#\<^sub>z n" | "m \<subset>#\<^sub>z repeat_zmset p m") =
  \<open>fn phi => ZMultiset_Simprocs.subset_cancel_zmsets\<close>

simproc_setup zmsetsubseteq_cancel
  ("(l::'a zmultiset) + m \<subseteq>#\<^sub>z n" | "(l::'a zmultiset) \<subseteq>#\<^sub>z m + n" |
   "add_zmset a m \<subseteq>#\<^sub>z n" | "m \<subseteq>#\<^sub>z add_zmset a n" |
   "replicate_zmset p a \<subseteq>#\<^sub>z n" | "m \<subseteq>#\<^sub>z replicate_zmset p a" |
   "repeat_zmset p m \<subseteq>#\<^sub>z n" | "m \<subseteq>#\<^sub>z repeat_zmset p m") =
  \<open>fn phi => ZMultiset_Simprocs.subseteq_cancel_zmsets\<close>

instance zmultiset :: (preorder) ordered_ab_semigroup_add_imp_le
  by (intro_classes; unfold less_eq_zmultiset_def; transfer; auto)

simproc_setup zmsetless_cancel
  ("(l::'a::preorder zmultiset) + m < n" | "(l::'a zmultiset) < m + n" |
   "add_zmset a m < n" | "m < add_zmset a n" |
   "replicate_zmset p a < n" | "m < replicate_zmset p a" |
   "repeat_zmset p m < n" | "m < repeat_zmset p m") =
  \<open>fn phi => Cancel_Simprocs.less_cancel\<close>

simproc_setup zmsetless_eq_cancel
  ("(l::'a::preorder zmultiset) + m \<le> n" | "(l::'a zmultiset) \<le> m + n" |
   "add_zmset a m \<le> n" | "m \<le> add_zmset a n" |
   "replicate_zmset p a \<le> n" | "m \<le> replicate_zmset p a" |
   "repeat_zmset p m \<le> n" | "m \<le> repeat_zmset p m") =
  \<open>fn phi => Cancel_Simprocs.less_eq_cancel\<close>

simproc_setup zmsetdiff_cancel
  ("n + (l::'a zmultiset)" | "(l::'a zmultiset) - m" |
   "add_zmset a m - n" | "m - add_zmset a n" |
   "replicate_zmset p r - n" | "m - replicate_zmset p r" |
   "repeat_zmset p m - n" | "m - repeat_zmset p m") =
  \<open>fn phi => Cancel_Simprocs.diff_cancel\<close>

instance zmultiset :: (linorder) linordered_cancel_ab_semigroup_add
  by (intro_classes, unfold less_eq_zmultiset_def, transfer, auto simp: equiv_zmset_def add.commute)

lemma less_mset_zmsetE:
  assumes "M < N"
  obtains A B C where
    "M = zmset_of A + C" and "N = zmset_of B + C" and "A < B"
  by (metis add_less_imp_less_right assms decompose_zmset_of2 zmset_of_less)

lemma less_eq_mset_zmsetE:
  assumes "M \<le> N"
  obtains A B C where
    "M = zmset_of A + C" and "N = zmset_of B + C" and "A \<le> B"
  by (metis add.commute add.right_neutral assms le_neq_trans less_imp_le less_mset_zmsetE order_refl
    zmset_of_empty)

lemma subset_eq_imp_le_zmset: "M \<subseteq>#\<^sub>z N \<Longrightarrow> M \<le> N"
  by (metis (no_types) add_mono_thms_linordered_semiring(3) subset_eq_imp_le_multiset
    subseteq_mset_zmsetE zmset_of_le)

lemma subset_imp_less_zmset: "M \<subset>#\<^sub>z N \<Longrightarrow> M < N"
  by (metis le_neq_trans subset_eq_imp_le_zmset subset_zmset_def)

lemma lt_imp_ex_zcount_lt:
  assumes m_lt_n: "M < N"
  shows "\<exists>y. zcount M y < zcount N y"
proof (rule ccontr, clarsimp)
  assume "\<forall>y. \<not> zcount M y < zcount N y"
  hence "\<forall>y. zcount M y \<ge> zcount N y"
    by (simp add: leI)
  hence "M \<supseteq>#\<^sub>z N"
    by (simp add: zmset_subset_eqI)
  hence "M \<ge> N"
    by (simp add: subset_eq_imp_le_zmset)
  thus False
    using m_lt_n by simp
qed

instance zmultiset :: (preorder) no_top
proof
  fix M :: \<open>'a zmultiset\<close>
  obtain a :: 'a where True by fast
  let ?M = \<open>zmset_of (mset_pos M) + zmset_of (mset_neg M)\<close>
  have \<open>M < add_zmset a ?M + ?M\<close>
    by (subst mset_pos_neg_partition)
      (auto simp: subset_zmset_def subseteq_zmset_def zmultiset_eq_iff
        intro!: subset_imp_less_zmset)
  then show \<open>\<exists>N. M < N\<close>
    by blast
qed

end
