(*
  File:     Range_Search.thy
  Author:   Martin Rau, TU München
*)

section "Search Queries on the \<open>k\<close>-d Tree"

theory Range_Search
imports 
  KDTree
begin

text\<open>
  Verifying k-dimensional searches on the k-d tree.

  Given two \<open>k\<close>-dimensional points \<open>p\<^sub>0\<close> and \<open>p\<^sub>1\<close> which bound the search space, the search should return
  only the points which satisfy the following criteria:

  For every point p in the resulting set: \newline
  \hspace{1cm}  For every axis @{term "a \<in> {0..k-1}"}: \newline
  \hspace{2cm}    @{term "min (p\<^sub>0!a) (p\<^sub>1!a) <= p!a \<and> p!a <= max (p\<^sub>0!a) (p\<^sub>1!a)"} \newline

  In a \<open>2\<close>-d tree a query corresponds to selecting all the points in the rectangle which
  has \<open>p\<^sub>0\<close> and \<open>p\<^sub>1\<close> as its defining edges.
\<close>

text \<open>
  Simplify the problem by assuming that the two given points \<open>p\<^sub>0\<close> and \<open>p\<^sub>1\<close> are the left lower
  and the right upper point.

  For every point p in the resulting set: \newline
  \hspace{1cm}  For every axis @{term "a \<in> {0..k-1}"}: \newline
  \hspace{2cm}    @{term "p\<^sub>0!a <= p\<^sub>1!a"} \newline
\<close>


subsection "Search Function and Auxiliary Definitions"

definition is_bounding_box :: "dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "is_bounding_box k p\<^sub>0 p\<^sub>1 \<longleftrightarrow> dim p\<^sub>0 = k \<and> dim p\<^sub>1 = k \<and> (\<forall>i < k. p\<^sub>0!i \<le> p\<^sub>1!i)"

definition in_bounding_box :: "dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "in_bounding_box k p p\<^sub>0 p\<^sub>1 \<longleftrightarrow> (\<forall>i < k. p\<^sub>0!i \<le> p!i \<and> p!i \<le> p\<^sub>1!i)"

fun search_rec :: "dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point set" where
  "search_rec k p\<^sub>0 p\<^sub>1 (Leaf p) = (if in_bounding_box k p p\<^sub>0 p\<^sub>1 then {p} else {})"
| "search_rec k p\<^sub>0 p\<^sub>1 (Node a s l r) = (
    if s < p\<^sub>0!a then
      search_rec k p\<^sub>0 p\<^sub>1 r
    else if p\<^sub>1!a < s then
      search_rec k p\<^sub>0 p\<^sub>1 l
    else
      search_rec k p\<^sub>0 p\<^sub>1 l \<union> search_rec k p\<^sub>0 p\<^sub>1 r
  )"


subsection "Auxiliary Lemmas"

lemma l_pibb_empty:
  assumes "invar k (Node a s l r)" "s < p\<^sub>0!a"
  shows "{ p \<in> set_kdt l. in_bounding_box k p p\<^sub>0 p\<^sub>1 } = {}"
  using assms
proof -
  have "\<forall>p \<in> set_kdt l. p!a < p\<^sub>0!a"
    using invar_l_le_a assms(1,2) by auto
  hence "\<forall>p \<in> set_kdt l. (\<exists>i < k. p!i < p\<^sub>0!i \<or> p\<^sub>1!i < p!i)"
    using assms(1) invar_axis_lt_d by blast
  hence "\<forall>p \<in> set_kdt l. \<not>in_bounding_box k p p\<^sub>0 p\<^sub>1"
    using in_bounding_box_def by fastforce
  thus ?thesis by blast
qed

lemma r_pibb_empty:
  assumes "invar k (Node a s l r)" "p\<^sub>1!a < s"
  shows "{ p \<in> set_kdt r. in_bounding_box k p p\<^sub>0 p\<^sub>1 } = {}"
  using assms
proof -
  have "\<forall>p \<in> set_kdt r. p\<^sub>1!a < p!a"
    using invar_r_ge_a assms(1,2) by auto
  hence "\<forall>p \<in> set_kdt r. (\<exists>i < k. p!i < p\<^sub>0!i \<or> p\<^sub>1!i < p!i)"
    using assms(1) invar_axis_lt_d by blast
  hence "\<forall>p \<in> set_kdt r. \<not>in_bounding_box k p p\<^sub>0 p\<^sub>1"
    using in_bounding_box_def by fastforce
  thus ?thesis by blast
qed


subsection "Simplified Main Theorem"

theorem search_rec:
  assumes "invar k kdt"
  shows "search_rec k p\<^sub>0 p\<^sub>1 kdt = { p \<in> set_kdt kdt. in_bounding_box k p p\<^sub>0 p\<^sub>1 }"
  using assms l_pibb_empty r_pibb_empty
  by (induction kdt) auto


subsection "Search and Auxiliary Definitions"

definition to_bounding_box :: "point \<Rightarrow> point \<Rightarrow> point * point" where
  "to_bounding_box p\<^sub>0 p\<^sub>1 = (
    let is = zip p\<^sub>0 p\<^sub>1 in 
    (map (\<lambda>(i, j). min i j) is, map (\<lambda>(i, j). max i j) is)
  )"

definition search :: "point \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point set" where
"search q\<^sub>0 q\<^sub>1 kdt =
  (let (p\<^sub>0, p\<^sub>1) = to_bounding_box q\<^sub>0 q\<^sub>1
   in search_rec (dim q\<^sub>0) p\<^sub>0 p\<^sub>1 kdt)"


subsection "Auxiliary Lemmas"

lemma to_bounding_box_is_bounding_box:
  assumes "dim q\<^sub>0 = k" "dim q\<^sub>1 = k" "(p\<^sub>0 ,p\<^sub>1) = to_bounding_box q\<^sub>0 q\<^sub>1"
  shows "is_bounding_box k p\<^sub>0 p\<^sub>1"
  using assms by (auto simp add: to_bounding_box_def is_bounding_box_def Let_def)

lemma in_bounding_box:
  assumes "dim q\<^sub>0 = k" "dim q\<^sub>1 = k" "(p\<^sub>0, p\<^sub>1) = to_bounding_box q\<^sub>0 q\<^sub>1"
  shows "in_bounding_box k p p\<^sub>0 p\<^sub>1 \<longleftrightarrow> (\<forall>i < k. min (q\<^sub>0!i) (q\<^sub>1!i) \<le> p!i \<and> p!i \<le> max (q\<^sub>0!i) (q\<^sub>1!i))"
  using assms by (auto simp add: min_def max_def to_bounding_box_def in_bounding_box_def Let_def)


subsection "Main Theorem and Corollaries"

theorem search:
  assumes "invar k kdt" "dim q\<^sub>0 = k" "dim q\<^sub>1 = k"
  shows "search q\<^sub>0 q\<^sub>1 kdt = { x \<in> set_kdt kdt. \<forall>i < k. min (q\<^sub>0!i) (q\<^sub>1!i) \<le> x!i \<and> x!i \<le> max (q\<^sub>0!i) (q\<^sub>1!i) }"
  using assms to_bounding_box_is_bounding_box in_bounding_box search_rec
  by (auto simp add: search_def)

corollary search_subset:
  assumes "invar k kdt" "dim q\<^sub>0 = k" "dim q\<^sub>1 = k"
  shows "search q\<^sub>0 q\<^sub>1 kdt \<subseteq> set_kdt kdt"
  using assms search by auto

corollary search_com:
  assumes "invar k kdt" "dim q\<^sub>0 = k" "dim q\<^sub>1 = k"
  shows "search q\<^sub>0 q\<^sub>1 kdt = search q\<^sub>1 q\<^sub>0 kdt"
  using assms search by auto

corollary search_inverse:
  assumes "invar k kdt" "dim q\<^sub>0 = k" "dim q\<^sub>1 = k" 
  assumes "p \<in> set_kdt kdt" "\<forall>i < k. min (q\<^sub>0!i) (q\<^sub>1!i) \<le> p!i \<and> p!i \<le> max (q\<^sub>0!i) (q\<^sub>1!i)"
  shows "p \<in> search q\<^sub>0 q\<^sub>1 kdt"
  using assms search by blast

corollary search_singleton:
  assumes "invar k kdt" "dim q\<^sub>0 = k" "q\<^sub>0 = q\<^sub>1" "q\<^sub>0 \<in> set_kdt kdt"
  shows "search q\<^sub>0 q\<^sub>1 kdt = {q\<^sub>0}"
proof -
  have *: "search q\<^sub>0 q\<^sub>1 kdt = { x \<in> set_kdt kdt. \<forall>i < k. q\<^sub>0!i = x!i }"
    using search assms(1,2,3) by auto
  have 1: "{q\<^sub>0} \<subseteq> search q\<^sub>0 q\<^sub>1 kdt"
    using * assms(4) by blast
  have "\<forall>p \<in> search q\<^sub>0 q\<^sub>1 kdt. dim p = k"
    using * assms(1) invar_dim by simp
  moreover have "\<forall>p \<noteq> q\<^sub>0. dim p = k \<longrightarrow> (\<exists>i < k. q\<^sub>0!i \<noteq> p!i)"
    using assms(2) nth_equalityI by fastforce
  ultimately have 2: "search q\<^sub>0 q\<^sub>1 kdt \<subseteq> {q\<^sub>0}"
    using * by blast
  show ?thesis
    using 1 2 by blast
qed

end