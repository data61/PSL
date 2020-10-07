(*  Title:       More about Multisets
    Author:      Mathias Fleury <mathias.fleury at mpi-inf.mpg.de>, 2015
    Author:      Jasmin Blanchette <blanchette at in.tum.de>, 2014, 2015
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Author:      Dmitriy Traytel <traytel at in.tum.de>, 2014
    Maintainer:  Mathias Fleury <mathias.fleury at mpi-inf.mpg.de>
*)

section \<open>More about Multisets\<close>

theory Multiset_More
imports "HOL-Library.Multiset_Order"
begin

text \<open>
Isabelle's theory of finite multisets is not as developed as other areas, such as lists and sets.
The present theory introduces some missing concepts and lemmas. Some of it is expected to move to
Isabelle's library.
\<close>


subsection \<open>Basic Setup\<close>

declare
  diff_single_trivial [simp]
  in_image_mset [iff]
  image_mset.compositionality [simp]

  (*To have the same rules as the set counter-part*)
  mset_subset_eqD[dest, intro?] (*@{thm subsetD}*)

  Multiset.in_multiset_in_set[simp]
  inter_add_left1[simp]
  inter_add_left2[simp]
  inter_add_right1[simp]
  inter_add_right2[simp]

  sum_mset_sum_list[simp]


subsection \<open>Lemmas about Intersection, Union and Pointwise Inclusion\<close>

lemma subset_add_mset_notin_subset_mset: \<open>A \<subseteq># add_mset b B \<Longrightarrow> b \<notin># A \<Longrightarrow> A \<subseteq># B\<close>
  by (simp add: subset_mset.le_iff_sup)

lemma subset_msetE: "\<lbrakk>A \<subset># B; \<lbrakk>A \<subseteq># B; \<not> B \<subseteq># A\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (simp add: subset_mset.less_le_not_le)

lemma Diff_triv_mset: "M \<inter># N = {#} \<Longrightarrow> M - N = M"
  by (metis diff_intersect_left_idem diff_zero)

lemma diff_intersect_sym_diff: "(A - B) \<inter># (B - A) = {#}"
  unfolding multiset_inter_def
proof -
  have "A - (B - (B - A)) = A - B"
    by (metis diff_intersect_right_idem multiset_inter_def)
  then show "A - B - (A - B - (B - A)) = {#}"
    by (metis diff_add diff_cancel diff_subset_eq_self subset_mset.diff_add)
qed

declare subset_msetE [elim!]


subsection \<open>Lemmas about Filter and Image\<close>

lemma count_image_mset_ge_count: "count (image_mset f A) (f b) \<ge> count A b"
  by (induction A) auto

lemma count_image_mset_inj:
  assumes \<open>inj f\<close>
  shows \<open>count (image_mset f M) (f x) = count M x\<close>
  by (induct M) (use assms in \<open>auto simp: inj_on_def\<close>)

lemma count_image_mset_le_count_inj_on:
  "inj_on f (set_mset M) \<Longrightarrow> count (image_mset f M) y \<le> count M (inv_into (set_mset M) f y)"
proof (induct M)
  case (add x M)
  note ih = this(1) and inj_xM = this(2)

  have inj_M: "inj_on f (set_mset M)"
    using inj_xM by simp

  show ?case
  proof (cases "x \<in># M")
    case x_in_M: True
    show ?thesis
    proof (cases "y = f x")
      case y_eq_fx: True
      show ?thesis
        using x_in_M ih[OF inj_M] unfolding y_eq_fx by (simp add: inj_M insert_absorb)
    next
      case y_ne_fx: False
      show ?thesis
        using x_in_M ih[OF inj_M] y_ne_fx insert_absorb by fastforce
    qed
  next
    case x_ni_M: False
    show ?thesis
    proof (cases "y = f x")
      case y_eq_fx: True
      have "f x \<notin># image_mset f M"
        using x_ni_M inj_xM by force
      thus ?thesis
        unfolding y_eq_fx
        by (metis (no_types) inj_xM count_add_mset count_greater_eq_Suc_zero_iff count_inI
          image_mset_add_mset inv_into_f_f union_single_eq_member)
    next
      case y_ne_fx: False
      show ?thesis
      proof (rule ccontr)
        assume neg_conj: "\<not> count (image_mset f (add_mset x M)) y
          \<le> count (add_mset x M) (inv_into (set_mset (add_mset x M)) f y)"

        have cnt_y: "count (add_mset (f x) (image_mset f M)) y = count (image_mset f M) y"
          using y_ne_fx by simp

        have "inv_into (set_mset M) f y \<in># add_mset x M \<Longrightarrow>
          inv_into (set_mset (add_mset x M)) f (f (inv_into (set_mset M) f y)) =
          inv_into (set_mset M) f y"
          by (meson inj_xM inv_into_f_f)
        hence "0 < count (image_mset f (add_mset x M)) y \<Longrightarrow>
          count M (inv_into (set_mset M) f y) = 0 \<or> x = inv_into (set_mset M) f y"
          using neg_conj cnt_y ih[OF inj_M]
          by (metis (no_types) count_add_mset count_greater_zero_iff count_inI f_inv_into_f
            image_mset_add_mset set_image_mset)
        thus False
          using neg_conj cnt_y x_ni_M ih[OF inj_M]
          by (metis (no_types) count_greater_zero_iff count_inI eq_iff image_mset_add_mset
            less_imp_le)
      qed
    qed
  qed
qed simp

lemma mset_filter_compl: "mset (filter p xs) + mset (filter (Not \<circ> p) xs) = mset xs"
  by (induction xs) (auto simp: mset_filter ac_simps)

text \<open>Near duplicate of @{thm [source] filter_eq_replicate_mset}: @{thm filter_eq_replicate_mset}.\<close>

lemma filter_mset_eq: "filter_mset ((=) L) A = replicate_mset (count A L) L"
  by (auto simp: multiset_eq_iff)

lemma filter_mset_cong[fundef_cong]:
  assumes "M = M'" "\<And>a. a \<in># M \<Longrightarrow> P a = Q a"
  shows "filter_mset P M = filter_mset Q M"
proof -
  have "M - filter_mset Q M = filter_mset (\<lambda>a. \<not>Q a) M"
    by (metis multiset_partition add_diff_cancel_left')
  then show ?thesis
    by (auto simp: filter_mset_eq_conv assms)
qed

lemma image_mset_filter_swap: "image_mset f {# x \<in># M. P (f x)#} = {# x \<in># image_mset f M. P x#}"
  by (induction M) auto

lemma image_mset_cong2:
  "(\<And>x. x \<in># M \<Longrightarrow> f x = g x) \<Longrightarrow> M = N \<Longrightarrow> image_mset f M = image_mset g N"
  by (hypsubst, rule image_mset_cong)

lemma filter_mset_empty_conv: \<open>(filter_mset P M = {#}) = (\<forall>L\<in>#M. \<not> P L)\<close>
  by (induction M) auto

lemma multiset_filter_mono2: \<open>filter_mset P A \<subseteq># filter_mset Q A \<longleftrightarrow> (\<forall>a\<in>#A. P a \<longrightarrow> Q a)\<close>
  by (induction A) (auto intro: subset_mset.order.trans)

lemma image_filter_cong:
  assumes \<open>\<And>C. C \<in># M \<Longrightarrow> P C \<Longrightarrow> f C = g C\<close>
  shows \<open>{#f C. C \<in># {#C \<in># M. P C#}#} = {#g C | C\<in># M. P C#}\<close>
  using assms by (induction M) auto

lemma image_mset_filter_swap2: \<open>{#C \<in># {#P x. x \<in># D#}. Q C #} = {#P x. x \<in># {#C| C \<in># D. Q (P C)#}#}\<close>
  by (simp add: image_mset_filter_swap)

declare image_mset_cong2 [cong]


subsection \<open>Lemmas about Sum\<close>

lemma sum_image_mset_sum_map[simp]: "sum_mset (image_mset f (mset xs)) = sum_list (map f xs)"
  by (metis mset_map sum_mset_sum_list)

lemma sum_image_mset_mono:
  fixes f :: "'a \<Rightarrow> 'b::canonically_ordered_monoid_add"
  assumes sub: "A \<subseteq># B"
  shows "(\<Sum>m \<in># A. f m) \<le> (\<Sum>m \<in># B. f m)"
  by (metis image_mset_union le_iff_add sub subset_mset.add_diff_inverse sum_mset.union)

lemma sum_image_mset_mono_mem:
  "n \<in># M \<Longrightarrow> f n \<le> (\<Sum>m \<in># M. f m)" for f :: "'a \<Rightarrow> 'b::canonically_ordered_monoid_add"
  using le_iff_add multi_member_split by fastforce

lemma count_sum_mset_if_1_0: \<open>count M a = (\<Sum>x\<in>#M. if x = a then 1 else 0)\<close>
  by (induction M) auto

lemma sum_mset_dvd:
  fixes k :: "'a::comm_semiring_1_cancel"
  assumes "\<forall>m \<in># M. k dvd f m"
  shows "k dvd (\<Sum>m \<in># M. f m)"
  using assms by (induct M) auto

lemma sum_mset_distrib_div_if_dvd:
  fixes k :: "'a::unique_euclidean_semiring"
  assumes "\<forall>m \<in># M. k dvd f m"
  shows "(\<Sum>m \<in># M. f m) div k = (\<Sum>m \<in># M. f m div k)"
  using assms by (induct M) (auto simp: div_plus_div_distrib_dvd_left)


subsection \<open>Lemmas about Remove\<close>

lemma set_mset_minus_replicate_mset[simp]:
  "n \<ge> count A a \<Longrightarrow> set_mset (A - replicate_mset n a) = set_mset A - {a}"
  "n < count A a \<Longrightarrow> set_mset (A - replicate_mset n a) = set_mset A"
  unfolding set_mset_def by (auto split: if_split simp: not_in_iff)

abbreviation removeAll_mset :: "'a \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" where
  "removeAll_mset C M \<equiv> M - replicate_mset (count M C) C"

lemma mset_removeAll[simp, code]: "removeAll_mset C (mset L) = mset (removeAll C L)"
  by (induction L) (auto simp: ac_simps multiset_eq_iff split: if_split_asm)

lemma removeAll_mset_filter_mset: "removeAll_mset C M = filter_mset ((\<noteq>) C) M"
  by (induction M) (auto simp: ac_simps multiset_eq_iff)

abbreviation remove1_mset :: "'a \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" where
  "remove1_mset C M \<equiv> M - {#C#}"

lemma removeAll_subseteq_remove1_mset: "removeAll_mset x M \<subseteq># remove1_mset x M"
  by (auto simp: subseteq_mset_def)

lemma in_remove1_mset_neq:
  assumes ab: "a \<noteq> b"
  shows "a \<in># remove1_mset b C \<longleftrightarrow> a \<in># C"
  by (metis assms diff_single_trivial in_diffD insert_DiffM insert_noteq_member)

lemma size_mset_removeAll_mset_le_iff: "size (removeAll_mset x M) < size M \<longleftrightarrow> x \<in># M"
  by (auto intro: count_inI mset_subset_size simp: subset_mset_def multiset_eq_iff)

lemma size_remove1_mset_If: \<open>size (remove1_mset x M) = size M - (if x \<in># M then 1 else 0)\<close>
  by (auto simp: size_Diff_subset_Int)

lemma size_mset_remove1_mset_le_iff: "size (remove1_mset x M) < size M \<longleftrightarrow> x \<in># M"
  using less_irrefl
  by (fastforce intro!: mset_subset_size elim: in_countE simp: subset_mset_def multiset_eq_iff)

lemma remove_1_mset_id_iff_notin: "remove1_mset a M = M \<longleftrightarrow> a \<notin># M"
  by (meson diff_single_trivial multi_drop_mem_not_eq)

lemma id_remove_1_mset_iff_notin: "M = remove1_mset a M \<longleftrightarrow> a \<notin># M"
  using remove_1_mset_id_iff_notin by metis

lemma remove1_mset_eqE:
  "remove1_mset L x1 = M \<Longrightarrow>
    (L \<in># x1 \<Longrightarrow> x1 = M + {#L#} \<Longrightarrow> P) \<Longrightarrow>
    (L \<notin># x1 \<Longrightarrow> x1 = M \<Longrightarrow> P) \<Longrightarrow>
  P"
  by (cases "L \<in># x1") auto

lemma image_filter_ne_mset[simp]:
  "image_mset f {#x \<in># M. f x \<noteq> y#} = removeAll_mset y (image_mset f M)"
  by (induction M) simp_all

lemma image_mset_remove1_mset_if:
  "image_mset f (remove1_mset a M) =
   (if a \<in># M then remove1_mset (f a) (image_mset f M) else image_mset f M)"
  by (auto simp: image_mset_Diff)

lemma filter_mset_neq: "{#x \<in># M. x \<noteq> y#} = removeAll_mset y M"
  by (metis add_diff_cancel_left' filter_eq_replicate_mset multiset_partition)

lemma filter_mset_neq_cond: "{#x \<in># M. P x \<and> x \<noteq> y#} = removeAll_mset y {# x\<in>#M. P x#}"
  by (metis filter_filter_mset filter_mset_neq)

lemma remove1_mset_add_mset_If:
  "remove1_mset L (add_mset L' C) = (if L = L' then C else remove1_mset L C + {#L'#})"
  by (auto simp: multiset_eq_iff)

lemma minus_remove1_mset_if:
  "A - remove1_mset b B = (if b \<in># B \<and> b \<in># A \<and> count A b \<ge> count B b then {#b#} + (A - B) else A - B)"
  by (auto simp: multiset_eq_iff count_greater_zero_iff[symmetric]
    simp del: count_greater_zero_iff)

lemma add_mset_eq_add_mset_ne:
  "a \<noteq> b \<Longrightarrow> add_mset a A = add_mset b B \<longleftrightarrow> a \<in># B \<and> b \<in># A \<and> A = add_mset b (B - {#a#})"
  by (metis (no_types, lifting) diff_single_eq_union diff_union_swap multi_self_add_other_not_self
    remove_1_mset_id_iff_notin union_single_eq_diff)

lemma add_mset_eq_add_mset: \<open>add_mset a M = add_mset b M' \<longleftrightarrow>
  (a = b \<and> M = M') \<or> (a \<noteq> b \<and> b \<in># M \<and> add_mset a (M - {#b#}) = M')\<close>
  by (metis add_mset_eq_add_mset_ne add_mset_remove_trivial union_single_eq_member)

(* TODO move to Multiset: could replace add_mset_remove_trivial_eq? *)
lemma add_mset_remove_trivial_iff: \<open>N = add_mset a (N - {#b#}) \<longleftrightarrow> a \<in># N \<and> a = b\<close>
  by (metis add_left_cancel add_mset_remove_trivial insert_DiffM2 single_eq_single
      size_mset_remove1_mset_le_iff union_single_eq_member)

lemma trivial_add_mset_remove_iff: \<open>add_mset a (N - {#b#}) = N \<longleftrightarrow> a \<in># N \<and> a = b\<close>
  by (subst eq_commute) (fact add_mset_remove_trivial_iff)

lemma remove1_single_empty_iff[simp]: \<open>remove1_mset L {#L'#} = {#} \<longleftrightarrow> L = L'\<close>
  using add_mset_remove_trivial_iff by fastforce

lemma add_mset_less_imp_less_remove1_mset:
  assumes xM_lt_N: "add_mset x M < N"
  shows "M < remove1_mset x N"
proof -
  have "M < N"
    using assms le_multiset_right_total mset_le_trans by blast
  then show ?thesis
    by (metis add_less_cancel_right add_mset_add_single diff_single_trivial insert_DiffM2 xM_lt_N)
qed


subsection \<open>Lemmas about Replicate\<close>

lemma replicate_mset_minus_replicate_mset_same[simp]:
  "replicate_mset m x - replicate_mset n x = replicate_mset (m - n) x"
  by (induct m arbitrary: n, simp, metis left_diff_repeat_mset_distrib' repeat_mset_replicate_mset)

lemma replicate_mset_subset_iff_lt[simp]: "replicate_mset m x \<subset># replicate_mset n x \<longleftrightarrow> m < n"
  by (induct n m rule: diff_induct) (auto intro: subset_mset.gr_zeroI)

lemma replicate_mset_subseteq_iff_le[simp]: "replicate_mset m x \<subseteq># replicate_mset n x \<longleftrightarrow> m \<le> n"
  by (induct n m rule: diff_induct) auto

lemma replicate_mset_lt_iff_lt[simp]: "replicate_mset m x < replicate_mset n x \<longleftrightarrow> m < n"
  by (induct n m rule: diff_induct) (auto intro: subset_mset.gr_zeroI gr_zeroI)

lemma replicate_mset_le_iff_le[simp]: "replicate_mset m x \<le> replicate_mset n x \<longleftrightarrow> m \<le> n"
  by (induct n m rule: diff_induct) auto

lemma replicate_mset_eq_iff[simp]:
  "replicate_mset m x = replicate_mset n y \<longleftrightarrow> m = n \<and> (m \<noteq> 0 \<longrightarrow> x = y)"
  by (cases m; cases n; simp)
    (metis in_replicate_mset insert_noteq_member size_replicate_mset union_single_eq_diff)

lemma replicate_mset_plus: "replicate_mset (a + b) C = replicate_mset a C + replicate_mset b C"
  by (induct a) (auto simp: ac_simps)

lemma mset_replicate_replicate_mset: "mset (replicate n L) = replicate_mset n L"
  by (induction n) auto

lemma set_mset_single_iff_replicate_mset: "set_mset U = {a} \<longleftrightarrow> (\<exists>n > 0. U = replicate_mset n a)"
  by (rule, metis count_greater_zero_iff count_replicate_mset insertI1 multi_count_eq singletonD
    zero_less_iff_neq_zero, force)

lemma ex_replicate_mset_if_all_elems_eq:
  assumes "\<forall>x \<in># M. x = y"
  shows "\<exists>n. M = replicate_mset n y"
  using assms by (metis count_replicate_mset mem_Collect_eq multiset_eqI neq0_conv set_mset_def)


subsection \<open>Multiset and Set Conversions\<close>

lemma count_mset_set_if: "count (mset_set A) a = (if a \<in> A \<and> finite A then 1 else 0)"
  by auto

lemma mset_set_set_mset_empty_mempty[iff]: "mset_set (set_mset D) = {#} \<longleftrightarrow> D = {#}"
  by (simp add: mset_set_empty_iff)

lemma count_mset_set_le_one: "count (mset_set A) x \<le> 1"
  by (simp add: count_mset_set_if)

lemma mset_set_set_mset_subseteq[simp]: "mset_set (set_mset A) \<subseteq># A"
  by (simp add: mset_set_set_mset_msubset)

lemma mset_sorted_list_of_set[simp]: "mset (sorted_list_of_set A) = mset_set A"
  by (metis mset_sorted_list_of_multiset sorted_list_of_mset_set)

lemma sorted_sorted_list_of_multiset[simp]:
  "sorted (sorted_list_of_multiset (M :: 'a::linorder multiset))"
  by (metis mset_sorted_list_of_multiset sorted_list_of_multiset_mset sorted_sort)

lemma mset_take_subseteq: "mset (take n xs) \<subseteq># mset xs"
  apply (induct xs arbitrary: n)
   apply simp
  by (case_tac n) simp_all

lemma sorted_list_of_multiset_eq_Nil[simp]: "sorted_list_of_multiset M = [] \<longleftrightarrow> M = {#}"
  by (metis mset_sorted_list_of_multiset sorted_list_of_multiset_empty)


subsection \<open>Duplicate Removal\<close>

(* TODO: use abbreviation? *)
definition remdups_mset :: "'v multiset \<Rightarrow> 'v multiset" where
  "remdups_mset S = mset_set (set_mset S)"

lemma set_mset_remdups_mset[simp]: \<open>set_mset (remdups_mset A) = set_mset A\<close>
  unfolding remdups_mset_def by auto

lemma count_remdups_mset_eq_1: "a \<in># remdups_mset A \<longleftrightarrow> count (remdups_mset A) a = 1"
  unfolding remdups_mset_def by (auto simp: count_eq_zero_iff intro: count_inI)

lemma remdups_mset_empty[simp]: "remdups_mset {#} = {#}"
  unfolding remdups_mset_def by auto

lemma remdups_mset_singleton[simp]: "remdups_mset {#a#} = {#a#}"
  unfolding remdups_mset_def by auto

lemma remdups_mset_eq_empty[iff]: "remdups_mset D = {#} \<longleftrightarrow> D = {#}"
  unfolding remdups_mset_def by blast

lemma remdups_mset_singleton_sum[simp]:
  "remdups_mset (add_mset a A) = (if a \<in># A then remdups_mset A else add_mset a (remdups_mset A))"
  unfolding remdups_mset_def by (simp_all add: insert_absorb)

lemma mset_remdups_remdups_mset[simp]: "mset (remdups D) = remdups_mset (mset D)"
  by (induction D) (auto simp add: ac_simps)

declare mset_remdups_remdups_mset[symmetric, code]

definition distinct_mset :: "'a multiset \<Rightarrow> bool" where
  "distinct_mset S \<longleftrightarrow> (\<forall>a. a \<in># S \<longrightarrow> count S a = 1)"

lemma distinct_mset_count_less_1: "distinct_mset S \<longleftrightarrow> (\<forall>a. count S a \<le> 1)"
  using eq_iff nat_le_linear unfolding distinct_mset_def by fastforce

lemma distinct_mset_empty[simp]: "distinct_mset {#}"
  unfolding distinct_mset_def by auto

lemma distinct_mset_singleton: "distinct_mset {#a#}"
  unfolding distinct_mset_def by auto

lemma distinct_mset_union:
  assumes dist: "distinct_mset (A + B)"
  shows "distinct_mset A"
  unfolding distinct_mset_count_less_1
proof (rule allI)
  fix a
  have \<open>count A a \<le> count (A + B) a\<close> by auto
  moreover have \<open>count (A + B) a \<le> 1\<close>
    using dist unfolding distinct_mset_count_less_1 by auto
  ultimately show \<open>count A a \<le> 1\<close>
    by simp
qed

lemma distinct_mset_minus[simp]: "distinct_mset A \<Longrightarrow> distinct_mset (A - B)"
  by (metis diff_subset_eq_self mset_subset_eq_exists_conv distinct_mset_union)

lemma count_remdups_mset_If: \<open>count (remdups_mset A) a = (if a \<in># A then 1 else 0)\<close>
  unfolding remdups_mset_def by auto

lemma distinct_mset_rempdups_union_mset:
  assumes "distinct_mset A" and "distinct_mset B"
  shows "A \<union># B = remdups_mset (A + B)"
  using assms nat_le_linear unfolding remdups_mset_def
  by (force simp add: multiset_eq_iff max_def count_mset_set_if distinct_mset_def not_in_iff)

lemma distinct_mset_add_mset[simp]: "distinct_mset (add_mset a L) \<longleftrightarrow> a \<notin># L \<and> distinct_mset L"
  unfolding distinct_mset_def
  apply (rule iffI)
   apply (auto split: if_split_asm; fail)[]
  by (auto simp: not_in_iff; fail)

lemma distinct_mset_size_eq_card: "distinct_mset C \<Longrightarrow> size C = card (set_mset C)"
  by (induction C) auto

lemma distinct_mset_add:
  "distinct_mset (L + L') \<longleftrightarrow> distinct_mset L \<and> distinct_mset L' \<and> L \<inter># L' = {#}"
  by (induction L arbitrary: L') auto

lemma distinct_mset_set_mset_ident[simp]: "distinct_mset M \<Longrightarrow> mset_set (set_mset M) = M"
  by (induction M) auto

lemma distinct_finite_set_mset_subseteq_iff[iff]:
  assumes "distinct_mset M" "finite N"
  shows "set_mset M \<subseteq> N \<longleftrightarrow> M \<subseteq># mset_set N"
  by (metis assms distinct_mset_set_mset_ident finite_set_mset msubset_mset_set_iff)

lemma distinct_mem_diff_mset:
  assumes dist: "distinct_mset M" and mem: "x \<in> set_mset (M - N)"
  shows "x \<notin> set_mset N"
proof -
  have "count M x = 1"
    using dist mem by (meson distinct_mset_def in_diffD)
  then show ?thesis
    using mem by (metis count_greater_eq_one_iff in_diff_count not_less)
qed

lemma distinct_set_mset_eq:
  assumes "distinct_mset M" "distinct_mset N" "set_mset M = set_mset N"
  shows "M = N"
  using assms distinct_mset_set_mset_ident by fastforce

lemma distinct_mset_union_mset[simp]:
  \<open>distinct_mset (D \<union># C) \<longleftrightarrow> distinct_mset D \<and> distinct_mset C\<close>
  unfolding distinct_mset_count_less_1 by force

lemma distinct_mset_inter_mset:
  "distinct_mset C \<Longrightarrow> distinct_mset (C \<inter># D)"
  "distinct_mset D \<Longrightarrow> distinct_mset (C \<inter># D)"
  by (simp_all add: multiset_inter_def,
    metis distinct_mset_minus multiset_inter_commute multiset_inter_def)

lemma distinct_mset_remove1_All: "distinct_mset C \<Longrightarrow> remove1_mset L C = removeAll_mset L C"
  by (auto simp: multiset_eq_iff distinct_mset_count_less_1)

lemma distinct_mset_size_2: "distinct_mset {#a, b#} \<longleftrightarrow> a \<noteq> b"
  by auto

lemma distinct_mset_filter: "distinct_mset M \<Longrightarrow> distinct_mset {# L \<in># M. P L#}"
  by (simp add: distinct_mset_def)

lemma distinct_mset_mset_distinct[simp]: \<open>distinct_mset (mset xs) = distinct xs\<close>
  by (induction xs) auto

lemma distinct_image_mset_inj:
  \<open>inj_on f (set_mset M) \<Longrightarrow> distinct_mset (image_mset f M) \<longleftrightarrow> distinct_mset M\<close>
  by (induction M) (auto simp: inj_on_def)


subsection \<open>Repeat Operation\<close>

lemma repeat_mset_compower: "repeat_mset n A = (((+) A) ^^ n) {#}"
  by (induction n) auto

lemma repeat_mset_prod: "repeat_mset (m * n) A = (((+) (repeat_mset n A)) ^^ m) {#}"
  by (induction m) (auto simp: repeat_mset_distrib)


subsection \<open>Cartesian Product\<close>

text \<open>Definition of the cartesian products over multisets. The construction mimics of the cartesian
  product on sets and use the same theorem names (adding only the suffix \<open>_mset\<close> to Sigma
  and Times). See file @{file \<open>~~/src/HOL/Product_Type.thy\<close>}\<close>

definition Sigma_mset :: "'a multiset \<Rightarrow> ('a \<Rightarrow> 'b multiset) \<Rightarrow> ('a \<times> 'b) multiset" where
  "Sigma_mset A B \<equiv> \<Union># {#{#(a, b). b \<in># B a#}. a \<in># A #}"

abbreviation Times_mset :: "'a multiset \<Rightarrow> 'b multiset \<Rightarrow> ('a \<times> 'b) multiset" (infixr "\<times>#" 80) where
  "Times_mset A B \<equiv> Sigma_mset A (\<lambda>_. B)"

hide_const (open) Times_mset

text \<open>Contrary to the set version @{term \<open>SIGMA x:A. B\<close>}, we use the non-ASCII symbol \<open>\<in>#\<close>.\<close>

syntax
  "_Sigma_mset" :: "[pttrn, 'a multiset, 'b multiset] => ('a * 'b) multiset"
  ("(3SIGMAMSET _\<in>#_./ _)" [0, 0, 10] 10)
translations
  "SIGMAMSET x\<in>#A. B" == "CONST Sigma_mset A (\<lambda>x. B)"

text \<open>Link between the multiset and the set cartesian product:\<close>

lemma Times_mset_Times: "set_mset (A \<times># B) = set_mset A \<times> set_mset B"
  unfolding Sigma_mset_def by auto

lemma Sigma_msetI [intro!]: "\<lbrakk>a \<in># A; b \<in># B a\<rbrakk> \<Longrightarrow> (a, b) \<in># Sigma_mset A B"
  by (unfold Sigma_mset_def) auto

lemma Sigma_msetE[elim!]: "\<lbrakk>c \<in># Sigma_mset A B; \<And>x y. \<lbrakk>x \<in># A; y \<in># B x; c = (x, y)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (unfold Sigma_mset_def) auto

text \<open>Elimination of @{term "(a, b) \<in># A \<times># B"} -- introduces no eigenvariables.\<close>

lemma Sigma_msetD1: "(a, b) \<in># Sigma_mset A B \<Longrightarrow> a \<in># A"
  by blast

lemma Sigma_msetD2: "(a, b) \<in># Sigma_mset A B \<Longrightarrow> b \<in># B a"
  by blast

lemma Sigma_msetE2: "\<lbrakk>(a, b) \<in># Sigma_mset A B; \<lbrakk>a \<in># A; b \<in># B a\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

lemma Sigma_mset_cong:
  "\<lbrakk>A = B; \<And>x. x \<in># B \<Longrightarrow> C x = D x\<rbrakk> \<Longrightarrow> (SIGMAMSET x \<in># A. C x) = (SIGMAMSET x \<in># B. D x)"
  by (metis (mono_tags, lifting) Sigma_mset_def image_mset_cong)

lemma count_sum_mset: "count (\<Union># M) b = (\<Sum>P \<in># M. count P b)"
  by (induction M) auto

lemma Sigma_mset_plus_distrib1[simp]: "Sigma_mset (A + B) C = Sigma_mset A C + Sigma_mset B C"
  unfolding Sigma_mset_def by auto

lemma Sigma_mset_plus_distrib2[simp]:
  "Sigma_mset A (\<lambda>i. B i + C i) = Sigma_mset A B + Sigma_mset A C"
  unfolding Sigma_mset_def by (induction A) (auto simp: multiset_eq_iff)

lemma Times_mset_single_left: "{#a#} \<times># B = image_mset (Pair a) B"
  unfolding Sigma_mset_def by auto

lemma Times_mset_single_right: "A \<times># {#b#} = image_mset (\<lambda>a. Pair a b) A"
  unfolding Sigma_mset_def by (induction A) auto

lemma Times_mset_single_single[simp]: "{#a#} \<times># {#b#} = {#(a, b)#}"
  unfolding Sigma_mset_def by simp

lemma count_image_mset_Pair:
  "count (image_mset (Pair a) B) (x, b) = (if x = a then count B b else 0)"
  by (induction B) auto

lemma count_Sigma_mset: "count (Sigma_mset A B) (a, b) = count A a * count (B a) b"
  by (induction A) (auto simp: Sigma_mset_def count_image_mset_Pair)

lemma Sigma_mset_empty1[simp]: "Sigma_mset {#} B = {#}"
  unfolding Sigma_mset_def by auto

lemma Sigma_mset_empty2[simp]: "A \<times># {#} = {#}"
  by (auto simp: multiset_eq_iff count_Sigma_mset)

lemma Sigma_mset_mono:
  assumes "A \<subseteq># C" and "\<And>x. x \<in># A \<Longrightarrow> B x \<subseteq># D x"
  shows "Sigma_mset A B \<subseteq># Sigma_mset C D"
proof -
  have "count A a * count (B a) b \<le> count C a * count (D a) b" for a b
    using assms unfolding subseteq_mset_def by (metis count_inI eq_iff mult_eq_0_iff mult_le_mono)
  then show ?thesis
    by (auto simp: subseteq_mset_def count_Sigma_mset)
qed

lemma mem_Sigma_mset_iff[iff]: "((a,b) \<in># Sigma_mset A B) = (a \<in># A \<and> b \<in># B a)"
  by blast

lemma mem_Times_mset_iff: "x \<in># A \<times># B \<longleftrightarrow> fst x \<in># A \<and> snd x \<in># B"
  by (induct x) simp

lemma Sigma_mset_empty_iff: "(SIGMAMSET i\<in>#I. X i) = {#} \<longleftrightarrow> (\<forall>i\<in>#I. X i = {#})"
  by (auto simp: Sigma_mset_def)

lemma Times_mset_subset_mset_cancel1: "x \<in># A \<Longrightarrow> (A \<times># B \<subseteq># A \<times># C) = (B \<subseteq># C)"
  by (auto simp: subseteq_mset_def count_Sigma_mset)

lemma Times_mset_subset_mset_cancel2: "x \<in># C \<Longrightarrow> (A \<times># C \<subseteq># B \<times># C) = (A \<subseteq># B)"
  by (auto simp: subseteq_mset_def count_Sigma_mset)

lemma Times_mset_eq_cancel2: "x \<in># C \<Longrightarrow> (A \<times># C = B \<times># C) = (A = B)"
  by (auto simp: multiset_eq_iff count_Sigma_mset dest!: in_countE)

lemma split_paired_Ball_mset_Sigma_mset[simp]:
  "(\<forall>z\<in>#Sigma_mset A B. P z) \<longleftrightarrow> (\<forall>x\<in>#A. \<forall>y\<in>#B x. P (x, y))"
  by blast

lemma split_paired_Bex_mset_Sigma_mset[simp]:
  "(\<exists>z\<in>#Sigma_mset A B. P z) \<longleftrightarrow> (\<exists>x\<in>#A. \<exists>y\<in>#B x. P (x, y))"
  by blast

lemma sum_mset_if_eq_constant:
  "(\<Sum>x\<in>#M. if a = x then (f x) else 0) = (((+) (f a)) ^^ (count M a)) 0"
  by (induction M) (auto simp: ac_simps)

lemma iterate_op_plus: "(((+) k) ^^ m) 0 = k * m"
  by (induction m) auto

lemma untion_image_mset_Pair_distribute:
  "\<Union>#{#image_mset (Pair x) (C x). x \<in># J - I#} =
   \<Union># {#image_mset (Pair x) (C x). x \<in># J#} - \<Union>#{#image_mset (Pair x) (C x). x \<in># I#}"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    iterate_op_plus diff_mult_distrib2)

lemma Sigma_mset_Un_distrib1: "Sigma_mset (I \<union># J) C = Sigma_mset I C \<union># Sigma_mset J C"
  by (auto simp: Sigma_mset_def sup_subset_mset_def untion_image_mset_Pair_distribute)

lemma Sigma_mset_Un_distrib2: "(SIGMAMSET i\<in>#I. A i \<union># B i) = Sigma_mset I A \<union># Sigma_mset I B"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    Sigma_mset_def diff_mult_distrib2 iterate_op_plus max_def not_in_iff)

lemma Sigma_mset_Int_distrib1: "Sigma_mset (I \<inter># J) C = Sigma_mset I C \<inter># Sigma_mset J C"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff)

lemma Sigma_mset_Int_distrib2: "(SIGMAMSET i\<in>#I. A i \<inter># B i) = Sigma_mset I A \<inter># Sigma_mset I B"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff)

lemma Sigma_mset_Diff_distrib1: "Sigma_mset (I - J) C = Sigma_mset I C - Sigma_mset J C"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff diff_mult_distrib2)

lemma Sigma_mset_Diff_distrib2: "(SIGMAMSET i\<in>#I. A i - B i) = Sigma_mset I A - Sigma_mset I B"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff diff_mult_distrib)

lemma Sigma_mset_Union: "Sigma_mset (\<Union>#X) B = (\<Union># (image_mset (\<lambda>A. Sigma_mset A B) X))"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff sum_mset_distrib_left)

lemma Times_mset_Un_distrib1: "(A \<union># B) \<times># C = A \<times># C \<union># B \<times># C"
  by (fact Sigma_mset_Un_distrib1)

lemma Times_mset_Int_distrib1: "(A \<inter># B) \<times># C = A \<times># C \<inter># B \<times># C"
  by (fact Sigma_mset_Int_distrib1)

lemma Times_mset_Diff_distrib1: "(A - B) \<times># C = A \<times># C - B \<times># C"
  by (fact Sigma_mset_Diff_distrib1)

lemma Times_mset_empty[simp]: "A \<times># B = {#} \<longleftrightarrow> A = {#} \<or> B = {#}"
  by (auto simp: Sigma_mset_empty_iff)

lemma Times_insert_left: "A \<times># add_mset x B = A \<times># B + image_mset (\<lambda>a. Pair a x) A"
  unfolding add_mset_add_single[of x B] Sigma_mset_plus_distrib2
  by (simp add: Times_mset_single_right)

lemma Times_insert_right: "add_mset a A \<times># B = A \<times># B + image_mset (Pair a) B"
  unfolding add_mset_add_single[of a A] Sigma_mset_plus_distrib1
  by (simp add: Times_mset_single_left)

lemma fst_image_mset_times_mset [simp]:
  "image_mset fst (A \<times># B) = (if B = {#} then {#} else repeat_mset (size B) A)"
  by (induct B) (auto simp: Times_mset_single_right ac_simps Times_insert_left)

lemma snd_image_mset_times_mset [simp]:
  "image_mset snd (A \<times># B) = (if A = {#} then {#} else repeat_mset (size A) B)"
  by (induct B) (auto simp add: Times_mset_single_right Times_insert_left image_mset_const_eq)

lemma product_swap_mset: "image_mset prod.swap (A \<times># B) = B \<times># A"
  by (induction A) (auto simp add: Times_mset_single_left Times_mset_single_right
      Times_insert_right Times_insert_left)

context
begin

qualified definition product_mset :: "'a multiset \<Rightarrow> 'b multiset \<Rightarrow> ('a \<times> 'b) multiset" where
  [code_abbrev]: "product_mset A B = A \<times># B"

lemma member_product_mset: "x \<in># product_mset A B \<longleftrightarrow> x \<in># A \<times># B"
  by (simp add: Multiset_More.product_mset_def)

end

lemma count_Sigma_mset_abs_def: "count (Sigma_mset A B) = (\<lambda>(a, b) \<Rightarrow> count A a * count (B a) b)"
  by (auto simp: fun_eq_iff count_Sigma_mset)

lemma Times_mset_image_mset1: "image_mset f A \<times># B = image_mset (\<lambda>(a, b). (f a, b)) (A \<times># B)"
  by (induct B) (auto simp: Times_insert_left)

lemma Times_mset_image_mset2: "A \<times># image_mset f B = image_mset (\<lambda>(a, b). (a, f b)) (A \<times># B)"
  by (induct A) (auto simp: Times_insert_right)

lemma sum_le_singleton: "A \<subseteq> {x} \<Longrightarrow> sum f A = (if x \<in> A then f x else 0)"
  by (auto simp: subset_singleton_iff elim: finite_subset)

lemma Times_mset_assoc: "(A \<times># B) \<times># C = image_mset (\<lambda>(a, b, c). ((a, b), c)) (A \<times># B \<times># C)"
  by (auto simp: multiset_eq_iff count_Sigma_mset count_image_mset vimage_def Times_mset_Times
      Int_commute count_eq_zero_iff intro!: trans[OF _ sym[OF sum_le_singleton[of _ "(_, _, _)"]]]
      cong: sum.cong if_cong)


subsection \<open>Transfer Rules\<close>

lemma plus_multiset_transfer[transfer_rule]:
  "(rel_fun (rel_mset R) (rel_fun (rel_mset R) (rel_mset R))) (+) (+)"
  by (unfold rel_fun_def rel_mset_def)
    (force dest: list_all2_appendI intro: exI[of _ "_ @ _"] conjI[rotated])

lemma minus_multiset_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique R"
  shows "(rel_fun (rel_mset R) (rel_fun (rel_mset R) (rel_mset R))) (-) (-)"
proof (unfold rel_fun_def rel_mset_def, safe)
  fix xs ys xs' ys'
  assume [transfer_rule]: "list_all2 R xs ys" "list_all2 R xs' ys'"
  have "list_all2 R (fold remove1 xs' xs) (fold remove1 ys' ys)"
    by transfer_prover
  moreover have "mset (fold remove1 xs' xs) = mset xs - mset xs'"
    by (induct xs' arbitrary: xs) auto
  moreover have "mset (fold remove1 ys' ys) = mset ys - mset ys'"
    by (induct ys' arbitrary: ys) auto
  ultimately show "\<exists>xs'' ys''.
    mset xs'' = mset xs - mset xs' \<and> mset ys'' = mset ys - mset ys' \<and> list_all2 R xs'' ys''"
    by blast
qed

declare rel_mset_Zero[transfer_rule]

lemma count_transfer[transfer_rule]:
  assumes "bi_unique R"
  shows "(rel_fun (rel_mset R) (rel_fun R (=))) count count"
unfolding rel_fun_def rel_mset_def proof safe
  fix x y xs ys
  assume "list_all2 R xs ys" "R x y"
  then show "count (mset xs) x = count (mset ys) y"
  proof (induct xs ys rule: list.rel_induct)
    case (Cons x' xs y' ys)
    then show ?case
      using assms unfolding bi_unique_alt_def2 by (auto simp: rel_fun_def)
  qed simp
qed

lemma subseteq_multiset_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique R" "right_total R"
  shows "(rel_fun (rel_mset R) (rel_fun (rel_mset R) (=)))
    (\<lambda>M N. filter_mset (Domainp R) M \<subseteq># filter_mset (Domainp R) N) (\<subseteq>#)"
proof -
  have count_filter_mset_less:
    "(\<forall>a. count (filter_mset (Domainp R) M) a \<le> count (filter_mset (Domainp R) N) a) \<longleftrightarrow>
     (\<forall>a \<in> {x. Domainp R x}. count M a \<le> count N a)" for M and N by auto
  show ?thesis unfolding subseteq_mset_def count_filter_mset_less
    by transfer_prover
qed

lemma sum_mset_transfer[transfer_rule]:
  "R 0 0 \<Longrightarrow> rel_fun R (rel_fun R R) (+) (+) \<Longrightarrow> (rel_fun (rel_mset R) R) sum_mset sum_mset"
  using sum_list_transfer[of R] unfolding rel_fun_def rel_mset_def by auto

lemma Sigma_mset_transfer[transfer_rule]:
  "(rel_fun (rel_mset R) (rel_fun (rel_fun R (rel_mset S)) (rel_mset (rel_prod R S))))
     Sigma_mset Sigma_mset"
  by (unfold Sigma_mset_def) transfer_prover


subsection \<open>Even More about Multisets\<close>

subsubsection \<open>Multisets and functions\<close>

lemma range_image_mset:
  assumes "set_mset Ds \<subseteq> range f"
  shows "Ds \<in> range (image_mset f)"
proof -
  have "\<forall>D. D \<in># Ds \<longrightarrow> (\<exists>C. f C = D)"
    using assms by blast
  then obtain f_i where
    f_p: "\<forall>D. D \<in># Ds \<longrightarrow> (f (f_i D) = D)"
    by metis
  define Cs where
    "Cs \<equiv> image_mset f_i Ds"
  from f_p Cs_def have "image_mset f Cs = Ds"
    by auto
  then show ?thesis
    by blast
qed


subsubsection \<open>Multisets and lists\<close>

definition list_of_mset :: "'a multiset \<Rightarrow> 'a list" where
  "list_of_mset m = (SOME l. m = mset l)"

lemma list_of_mset_exi: "\<exists>l. m = mset l"
  using ex_mset by metis

lemma [simp]: "mset (list_of_mset m) = m"
  by (metis (mono_tags, lifting) ex_mset list_of_mset_def someI_ex)

lemma range_mset_map:
  assumes "set_mset Ds \<subseteq> range f"
  shows "Ds \<in> range (\<lambda>Cl. mset (map f Cl))"
proof -
  have "Ds \<in> range (image_mset f)"
    by (simp add: assms range_image_mset)
  then obtain Cs where Cs_p: "image_mset f Cs = Ds"
    by auto
  define Cl where "Cl = list_of_mset Cs"
  then have "mset Cl = Cs"
    by auto
  then have "image_mset f (mset Cl) = Ds"
    using Cs_p by auto
  then have "mset (map f Cl) = Ds"
    by auto
  then show ?thesis
    by auto
qed

lemma list_of_mset_empty[iff]: "list_of_mset m = [] \<longleftrightarrow> m = {#}"
  by (metis (mono_tags, lifting) ex_mset list_of_mset_def mset_zero_iff_right someI_ex)

lemma in_mset_conv_nth: "(x \<in># mset xs) = (\<exists>i<length xs. xs ! i = x)"
  by (auto simp: in_set_conv_nth)

lemma in_mset_sum_list:
  assumes "L \<in># LL"
  assumes "LL \<in> set Ci"
  shows "L \<in># sum_list Ci"
  using assms by (induction Ci) auto

lemma in_mset_sum_list2:
  assumes "L \<in># sum_list Ci"
  obtains LL where
    "LL \<in> set Ci"
    "L \<in># LL"
  using assms by (induction Ci) auto

lemma subseteq_list_Union_mset:
  assumes "length Ci = n"
  assumes "length CAi = n"
  assumes "\<forall>i<n.  Ci ! i \<subseteq># CAi ! i "
  shows "\<Union># (mset Ci) \<subseteq># \<Union># (mset CAi)"
  using assms proof (induction n arbitrary: Ci CAi)
  case 0
  then show ?case by auto
next
  case (Suc n)
  from Suc have "\<forall>i<n. tl Ci ! i \<subseteq># tl CAi ! i"
    by (simp add: nth_tl)
  hence "\<Union>#(mset (tl Ci)) \<subseteq># \<Union>#(mset (tl CAi))" using Suc by auto
  moreover
  have "hd Ci \<subseteq># hd CAi" using Suc
    by (metis hd_conv_nth length_greater_0_conv zero_less_Suc)
  ultimately
  show "\<Union>#(mset Ci) \<subseteq># \<Union>#(mset CAi)"
    using Suc by (cases Ci; cases CAi) (auto intro: subset_mset.add_mono)
qed


subsubsection \<open>More on multisets and functions\<close>

lemma subseteq_mset_size_eql: "X \<subseteq># Y \<Longrightarrow> size Y = size X \<Longrightarrow> X = Y"
  using mset_subset_size subset_mset_def by fastforce

lemma image_mset_of_subset_list:
  assumes "image_mset \<eta> C' = mset lC"
  shows "\<exists>qC'. map \<eta> qC' = lC \<and> mset qC' = C'"
  using assms apply (induction lC arbitrary: C')
  subgoal by simp
  subgoal by (fastforce dest!: msed_map_invR intro: exI[of _ \<open>_ # _\<close>])
  done

lemma image_mset_of_subset:
  assumes "A \<subseteq># image_mset \<eta> C'"
  shows "\<exists>A'. image_mset \<eta> A' = A \<and> A' \<subseteq># C'"
proof -
  define C where "C = image_mset \<eta> C'"

  define lA where "lA = list_of_mset A"
  define lD where "lD = list_of_mset (C-A)"
  define lC where "lC = lA @ lD"

  have "mset lC = C"
    using C_def assms unfolding lD_def lC_def lA_def by auto
  then have "\<exists>qC'. map \<eta> qC' = lC \<and> mset qC' = C'"
    using assms image_mset_of_subset_list unfolding C_def by metis
  then obtain qC' where qC'_p: "map \<eta> qC' = lC \<and> mset qC' = C'"
    by auto
  let ?lA' = "take (length lA) qC'"
  have m: "map \<eta> ?lA' = lA"
    using qC'_p lC_def
    by (metis append_eq_conv_conj take_map)
  let ?A' = "mset ?lA'"

  have "image_mset \<eta> ?A' = A"
    using m using lA_def
    by (metis (full_types) ex_mset list_of_mset_def mset_map someI_ex)
  moreover have "?A' \<subseteq># C'"
    using qC'_p unfolding lA_def
    using mset_take_subseteq by blast
  ultimately show ?thesis by blast
qed

lemma all_the_same: "\<forall>x \<in># X. x = y \<Longrightarrow> card (set_mset X) \<le> Suc 0"
  by (metis card.empty card.insert card_mono finite.intros(1) finite_insert le_SucI singletonI subsetI)

lemma Melem_subseteq_Union_mset[simp]:
  assumes "x \<in># T"
  shows "x \<subseteq># \<Union>#T"
  using assms sum_mset.remove by force

lemma Melem_subset_eq_sum_list[simp]:
  assumes "x \<in># mset T"
  shows "x \<subseteq># sum_list T"
  using assms by (metis mset_subset_eq_add_left sum_mset.remove sum_mset_sum_list)

lemma less_subset_eq_Union_mset[simp]:
  assumes "i < length CAi"
  shows "CAi ! i \<subseteq># \<Union>#(mset CAi)"
proof -
  from assms have "CAi ! i \<in># mset CAi"
    by auto
  then show ?thesis
    by auto
qed

lemma less_subset_eq_sum_list[simp]:
  assumes "i < length CAi"
  shows "CAi ! i \<subseteq># sum_list CAi"
proof -
  from assms have "CAi ! i \<in># mset CAi"
    by auto
  then show ?thesis
    by auto
qed

end
