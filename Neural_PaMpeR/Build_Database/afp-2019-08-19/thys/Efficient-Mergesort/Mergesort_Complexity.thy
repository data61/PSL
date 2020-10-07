(*  Author:      Christian Sternagel <c.sternagel@gmail.com>
    Maintainer:  Christian Sternagel <c.sternagel@gmail.com>
*)
theory Mergesort_Complexity
  imports
    Efficient_Sort
    Complex_Main
begin

(*TODO: move?*)
lemma log2_mono:
  "x > 0 \<Longrightarrow> x \<le> y \<Longrightarrow> log 2 x \<le> log 2 y"
  by auto


section \<open>Counting the Number of Comparisons\<close>

context
  fixes key :: "'a \<Rightarrow> 'k::linorder"
begin

fun c_merge :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat"
  where
    "c_merge (x # xs) (y # ys) =
      1 + (if key y < key x then c_merge (x # xs) ys else c_merge xs (y # ys))"
  | "c_merge [] ys = 0"
  | "c_merge xs [] = 0"

fun c_merge_pairs :: "'a list list \<Rightarrow> nat"
  where
    "c_merge_pairs (xs # ys # zss) = c_merge xs ys + c_merge_pairs zss"
  | "c_merge_pairs [] = 0"
  | "c_merge_pairs [x] = 0"

fun c_merge_all :: "'a list list \<Rightarrow> nat"
  where
    "c_merge_all [] = 0"
  | "c_merge_all [x] = 0"
  | "c_merge_all xss = c_merge_pairs xss + c_merge_all (merge_pairs key xss)"

fun c_sequences :: "'a list \<Rightarrow> nat"
  and c_asc :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
  and c_desc :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
  where
    "c_sequences (x # y # zs) = 1 + (if key y < key x then c_desc y zs else c_asc y zs)"
  | "c_sequences [] = 0"
  | "c_sequences [x] = 0"
  | "c_asc x (y # ys) = 1 + (if \<not> key y < key x then c_asc y ys else c_sequences (y # ys))"
  | "c_asc x [] = 0"
  | "c_desc x (y # ys) = 1 + (if key y < key x then c_desc y ys else c_sequences (y # ys))"
  | "c_desc x [] = 0"

fun c_msort :: "'a list \<Rightarrow> nat"
  where
    "c_msort xs = c_sequences xs + c_merge_all (sequences key xs)"

lemma c_merge:
  "c_merge xs ys \<le> length xs + length ys"
  by (induct xs ys rule: c_merge.induct) simp_all

lemma c_merge_pairs:
  "c_merge_pairs xss \<le> length (concat xss)"
proof (induct xss rule: c_merge_pairs.induct)
  case (1 xs ys zss)
  then show ?case using c_merge [of xs ys] by simp
qed simp_all

lemma c_merge_all:
  "c_merge_all xss \<le> length (concat xss) * \<lceil>log 2 (length xss)\<rceil>"
proof (induction xss rule: c_merge_all.induct)
  case (3 xs ys zss)
  let ?clen = "\<lambda>xs. length (concat xs)"
  let ?xss = "xs # ys # zss"
  let ?xss2 = "merge_pairs key ?xss"

  have *: "\<lceil>log 2 (real n + 2)\<rceil> = \<lceil>log 2 (Suc n div 2 + 1)\<rceil> + 1" for n :: nat
    using ceiling_log2_div2 [of "n + 2"] by (simp add: algebra_simps)

  have "c_merge_all ?xss = c_merge_pairs ?xss + c_merge_all ?xss2" by simp
  also have "\<dots> \<le> ?clen ?xss + c_merge_all ?xss2"
    using c_merge [of xs ys] and c_merge_pairs [of ?xss] by auto
  also have "\<dots> \<le> ?clen ?xss + ?clen ?xss2 * \<lceil>log 2 (length ?xss2)\<rceil>"
    using "3.IH" by simp
  also have "\<dots> \<le> ?clen ?xss * \<lceil>log 2 (length ?xss)\<rceil>"
    by (auto simp: * algebra_simps)
  finally show ?case by simp
qed simp_all

lemma
  shows c_sequences: "c_sequences xs \<le> length xs - 1"
    and c_asc: "c_asc x ys \<le> length ys"
    and c_desc: "c_desc x ys \<le> length ys"
  by (induct xs and x ys and x ys rule: c_sequences_c_asc_c_desc.induct) simp_all

lemma
  shows length_concat_sequences [simp]: "length (concat (sequences key xs)) = length xs"
    and length_concat_asc: "ascP f \<Longrightarrow> length (concat (asc key a f ys)) = 1 + length (f []) + length ys"
    and length_concat_desc: "length (concat (desc key a xs ys)) = 1 + length xs + length ys"
  by (induct xs and a f ys and a xs ys rule: sequences_asc_desc.induct)
    (auto simp: ascP_f_singleton)

lemma
  shows sequences_ne: "xs \<noteq> [] \<Longrightarrow> sequences key xs \<noteq> []"
    and "ascP f \<Longrightarrow> asc key a f ys \<noteq> []"
    and "desc key a xs ys \<noteq> []"
  by (induct xs and a f ys and a xs ys taking: key rule: sequences_asc_desc.induct) simp_all

lemma c_msort:
  assumes [simp]: "length xs = n"
  shows "c_msort xs \<le> n + n * \<lceil>log 2 n\<rceil>"
proof -
  have [simp]: "xs = [] \<longleftrightarrow> length xs = 0" by blast
  have "int (c_merge_all (sequences key xs)) \<le> int n * \<lceil>log 2 (length (sequences key xs))\<rceil>"
    using c_merge_all [of "sequences key xs"] by simp
  also have "\<dots> \<le> int n * \<lceil>log 2 n\<rceil>"
    using length_sequences [of key xs]
    by (cases n) (auto intro!: sequences_ne mult_mono ceiling_mono log2_mono)
  finally have "int (c_merge_all (sequences key xs)) \<le> int n * \<lceil>log 2 n\<rceil>" .
  moreover have "c_sequences xs \<le> n" using c_sequences [of xs] by auto
  ultimately show ?thesis by (auto intro: add_mono)
qed

end

end
