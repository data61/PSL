(*  Author:      Christian Sternagel <c.sternagel@gmail.com>
    Maintainer:  Christian Sternagel <c.sternagel@gmail.com>
*)
theory Efficient_Sort
  imports "HOL-Library.Multiset"
begin


section \<open>GHC Version of Mergesort\<close>

text \<open>
  In the following we show that the mergesort implementation
  used in GHC (see \<^url>\<open>http://hackage.haskell.org/package/base-4.11.1.0/docs/src/Data.OldList.html#sort\<close>)
  is a correct and stable sorting algorithm. Furthermore, experimental
  data suggests that generated code for this implementation is much more
  efficient than for the implementation provided by \<^theory>\<open>HOL-Library.Multiset\<close>.

  A high-level overview of an older version of this formalization as well as some experimental data
  is to be found in @{cite "Sternagel2012"}.
\<close>
subsection \<open>Definition of Natural Mergesort\<close>

context
  fixes key :: "'a \<Rightarrow> 'k::linorder"
begin

text \<open>
  Split a list into chunks of ascending and descending parts, where
  descending parts are reversed on the fly.
  Thus, the result is a list of sorted lists.
\<close>
fun sequences :: "'a list \<Rightarrow> 'a list list"
  and asc :: "'a \<Rightarrow> ('a list \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> 'a list list"
  and desc :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list"
  where
    "sequences (a # b # xs) =
      (if key a > key b then desc b [a] xs else asc b ((#) a) xs)"
  | "sequences [x] = [[x]]"
  | "sequences [] = []"
  | "asc a as (b # bs) =
      (if \<not> key a > key b then asc b (\<lambda>ys. as (a # ys)) bs
      else as [a] # sequences (b # bs))"
  | "asc a as [] = [as [a]]"
  | "desc a as (b # bs) =
      (if key a > key b then desc b (a # as) bs
      else (a # as) # sequences (b # bs))"
  | "desc a as [] = [a # as]"

fun merge :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "merge (a # as) (b # bs) =
      (if key a > key b then b # merge (a # as) bs else a # merge as (b # bs))"
  | "merge [] bs = bs"
  | "merge as [] = as"

fun merge_pairs :: "'a list list \<Rightarrow> 'a list list"
  where
    "merge_pairs (a # b # xs) = merge a b # merge_pairs xs"
  | "merge_pairs xs = xs"

lemma length_merge [simp]:
  "length (merge xs ys) = length xs + length ys"
  by (induct xs ys rule: merge.induct) simp_all

lemma length_merge_pairs [simp]:
  "length (merge_pairs xs) = (1 + length xs) div 2"
  by (induct xs rule: merge_pairs.induct) simp_all

fun merge_all :: "'a list list \<Rightarrow> 'a list"
  where
    "merge_all [] = []"
  | "merge_all [x] = x"
  | "merge_all xs = merge_all (merge_pairs xs)"

fun msort_key :: "'a list \<Rightarrow> 'a list"
  where
    "msort_key xs = merge_all (sequences xs)"


subsection \<open>Facts about Lengths\<close>

definition "ascP f = (\<forall>xs ys. f (xs @ ys) = f xs @ ys)"

lemma ascP_Cons [simp]: "ascP ((#) x)" by (simp add: ascP_def)

lemma ascP_comp_Cons [simp]: "ascP f \<Longrightarrow> ascP (\<lambda>ys. f (x # ys))"
  by (auto simp: ascP_def simp flip: append_Cons)

lemma ascP_comp_append: "ascP f \<Longrightarrow> ascP (\<lambda>xs. f [] @ x # xs)"
  by (auto simp: ascP_def)

lemma ascP_f_singleton:
  assumes "ascP f"
  shows "f [x] = f [] @ [x]"
  using assms [unfolded ascP_def, THEN spec, THEN spec, of "[]" "[x]"] by simp

lemma ascP_f_Cons:
  assumes "ascP f"
  shows "f (x # xs) = f [] @ x # xs"
  using assms [unfolded ascP_def, THEN spec, THEN spec, of "[]" "x # xs"] by simp

lemma
  shows length_sequences: "length (sequences xs) \<le> length xs"
    and length_asc: "ascP f \<Longrightarrow> length (asc a f ys) \<le> 1 + length ys"
    and length_desc: "length (desc a xs ys) \<le> 1 + length ys"
  by (induct xs and a f ys and a xs ys rule: sequences_asc_desc.induct) auto

lemma length_concat_merge_pairs [simp]:
  "length (concat (merge_pairs xss)) = length (concat xss)"
  by (induct xss rule: merge_pairs.induct) simp_all


subsection \<open>Functional Correctness\<close>

lemma mset_merge [simp]:
  "mset (merge xs ys) = mset xs + mset ys"
  by (induct xs ys rule: merge.induct) (simp_all add: ac_simps)

lemma set_merge [simp]:
  "set (merge xs ys) = set xs \<union> set ys"
  by (simp flip: set_mset_mset)

lemma mset_concat_merge_pairs [simp]:
  "mset (concat (merge_pairs xs)) = mset (concat xs)"
  by (induct xs rule: merge_pairs.induct) (auto simp: ac_simps)

lemma set_concat_merge_pairs [simp]:
  "set (concat (merge_pairs xs)) = set (concat xs)"
  by (simp flip: set_mset_mset)

lemma mset_merge_all [simp]:
  "mset (merge_all xs) = mset (concat xs)"
  by (induct xs rule: merge_all.induct) (simp_all add: ac_simps)

lemma set_merge_all [simp]:
  "set (merge_all xs) = set (concat xs)"
  by (simp flip: set_mset_mset)

lemma
  shows mset_seqeuences [simp]: "mset (concat (sequences xs)) = mset xs"
    and mset_asc: "ascP f \<Longrightarrow> mset (concat (asc x f ys)) = {#x#} + mset (f []) + mset ys"
    and mset_desc: "mset (concat (desc x xs ys)) = {#x#} + mset xs + mset ys"
  by (induct xs and x f ys and x xs ys rule: sequences_asc_desc.induct)
    (auto simp: ascP_f_singleton)

lemma mset_msort_key:
  "mset (msort_key xs) = mset xs"
  by (auto)

lemma sorted_merge [simp]:
  assumes "sorted (map key xs)" and "sorted (map key ys)"
  shows "sorted (map key (merge xs ys))"
  using assms by (induct xs ys rule: merge.induct) (auto)

lemma sorted_merge_pairs [simp]:
  assumes "\<forall>x\<in>set xs. sorted (map key x)"
  shows "\<forall>x\<in>set (merge_pairs xs). sorted (map key x)"
  using assms by (induct xs rule: merge_pairs.induct) simp_all

lemma sorted_merge_all:
  assumes "\<forall>x\<in>set xs. sorted (map key x)"
  shows "sorted (map key (merge_all xs))"
  using assms by (induct xs rule: merge_all.induct) simp_all

lemma
  shows sorted_sequences: "\<forall>x \<in> set (sequences xs). sorted (map key x)"
    and sorted_asc: "ascP f \<Longrightarrow> sorted (map key (f [])) \<Longrightarrow> \<forall>x\<in>set (f []). key x \<le> key a \<Longrightarrow> \<forall>x\<in>set (asc a f ys). sorted (map key x)"
    and sorted_desc: "sorted (map key xs) \<Longrightarrow> \<forall>x\<in>set xs. key a \<le> key x \<Longrightarrow> \<forall>x\<in>set (desc a xs ys). sorted (map key x)"
  by (induct xs and a f ys and a xs ys rule: sequences_asc_desc.induct)
    (auto simp: ascP_f_singleton sorted_append not_less dest: order_trans, fastforce)

lemma sorted_msort_key:
  "sorted (map key (msort_key xs))"
  by (unfold msort_key.simps) (intro sorted_merge_all sorted_sequences)


subsection \<open>Stability\<close>

lemma
  shows filter_by_key_sequences [simp]: "[y\<leftarrow>concat (sequences xs). key y = k] = [y\<leftarrow>xs. key y = k]"
    and filter_by_key_asc: "ascP f \<Longrightarrow> [y\<leftarrow>concat (asc a f ys). key y = k] = [y\<leftarrow>f [a] @ ys. key y = k]"
    and filter_by_key_desc: "sorted (map key xs) \<Longrightarrow> \<forall>x\<in>set xs. key a \<le> key x \<Longrightarrow> [y\<leftarrow>concat (desc a xs ys). key y = k] = [y\<leftarrow>a # xs @ ys. key y = k]"
proof (induct xs and a f ys and a xs ys rule: sequences_asc_desc.induct)
  case (4 a f b bs)
  then show ?case
    by (auto simp: o_def ascP_f_Cons [where f = f] ascP_comp_append)
next
  case (6 a as b bs)
  then show ?case
  proof (cases "key b < key a")
    case True
    with 6 have "[y\<leftarrow>concat (desc b (a # as) bs). key y = k] = [y\<leftarrow>b # (a # as) @ bs. key y = k]"
      by (auto simp: less_le order_trans)
    then show ?thesis
      using True and 6
      by (cases "key a = k", cases "key b = k")
        (auto simp: Cons_eq_append_conv intro!: filter_False)
  qed auto
qed auto
 
lemma filter_by_key_merge_is_append [simp]:
  assumes "sorted (map key xs)"
  shows "[y\<leftarrow>merge xs ys. key y = k] = [y\<leftarrow>xs. key y = k] @ [y\<leftarrow>ys. key y = k]"
  using assms
  by (induct xs ys rule: merge.induct) (auto simp: Cons_eq_append_conv leD intro!: filter_False)

lemma filter_by_key_merge_pairs [simp]:
  assumes "\<forall>xs\<in>set xss. sorted (map key xs)"
  shows "[y\<leftarrow>concat (merge_pairs xss). key y = k] = [y\<leftarrow>concat xss. key y = k]"
  using assms by (induct xss rule: merge_pairs.induct) simp_all

lemma filter_by_key_merge_all [simp]:
  assumes "\<forall>xs\<in>set xss. sorted (map key xs)"
  shows "[y\<leftarrow>merge_all xss. key y = k] = [y\<leftarrow>concat xss. key y = k]"
  using assms by (induct xss rule: merge_all.induct) simp_all

lemma filter_by_key_merge_all_sequences [simp]:
  "[x\<leftarrow>merge_all (sequences xs) . key x = k] = [x\<leftarrow>xs . key x = k]"
  using sorted_sequences [of xs] by simp

lemma msort_key_stable:
  "[x\<leftarrow>msort_key xs. key x = k] = [x\<leftarrow>xs. key x = k]"
  by auto

lemma sort_key_msort_key_conv:
  "sort_key key = msort_key"
  using msort_key_stable [of "key x" for x]
  by (intro ext properties_for_sort_key mset_msort_key sorted_msort_key)
    (metis (mono_tags, lifting) filter_cong)

end

text \<open>
  Replace existing code equations for \<^const>\<open>sort_key\<close> by \<^const>\<open>msort_key\<close>.
\<close>
declare sort_key_by_quicksort_code [code del]
declare sort_key_msort_key_conv [code]

end
