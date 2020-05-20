(*
  File:     Range_Search.thy
  Author:   Martin Rau, TU München
*)

section \<open>Range Searching\<close>

theory Range_Search
imports
  KD_Tree
begin

text\<open>
  Given two \<open>k\<close>-dimensional points \<open>p\<^sub>0\<close> and \<open>p\<^sub>1\<close> which bound the search space, the search should
  return only the points which satisfy the following criteria:

  For every point p in the resulting set: \newline
  \hspace{1cm}  For every axis @{term "k"}: \newline
  \hspace{2cm}    @{term "p\<^sub>0$k \<le> p$k \<and> p$k \<le> p\<^sub>1$k"} \newline

  For a \<open>2\<close>-d tree a query corresponds to selecting all the points in the rectangle that
  has \<open>p\<^sub>0\<close> and \<open>p\<^sub>1\<close> as its defining edges.
\<close>

subsection \<open>Rectangle Definition\<close>

lemma cbox_point_def:
  fixes p\<^sub>0 :: "('k::finite) point"
  shows "cbox p\<^sub>0 p\<^sub>1 = { p. \<forall>k. p\<^sub>0$k \<le> p$k \<and> p$k \<le> p\<^sub>1$k }"
proof -
  have "cbox p\<^sub>0 p\<^sub>1 = { p. \<forall>k. p\<^sub>0 \<bullet> axis k 1 \<le> p \<bullet> axis k 1 \<and> p \<bullet> axis k 1 \<le> p\<^sub>1 \<bullet> axis k 1 }"
    unfolding cbox_def using axis_inverse by auto
  also have "... = { p. \<forall>k. p\<^sub>0$k \<bullet> 1 \<le> p$k \<bullet> 1 \<and> p$k \<bullet> 1 \<le> p\<^sub>1$k \<bullet> 1 }"
    using inner_axis[of _ _ 1] by (smt Collect_cong)
  also have "... = { p. \<forall>k. p\<^sub>0$k \<le> p$k \<and> p$k \<le> p\<^sub>1$k }"
    by simp
  finally show ?thesis .
qed


subsection \<open>Search Function\<close>

fun search :: "('k::finite) point \<Rightarrow> 'k point \<Rightarrow> 'k kdt \<Rightarrow> 'k point set" where
  "search p\<^sub>0 p\<^sub>1 (Leaf p) = (if p \<in> cbox p\<^sub>0 p\<^sub>1 then { p } else {})"
| "search p\<^sub>0 p\<^sub>1 (Node k v l r) = (
    if v < p\<^sub>0$k then
      search p\<^sub>0 p\<^sub>1 r
    else if p\<^sub>1$k < v then
      search p\<^sub>0 p\<^sub>1 l
    else
      search p\<^sub>0 p\<^sub>1 l \<union> search p\<^sub>0 p\<^sub>1 r
  )"


subsection \<open>Auxiliary Lemmas\<close>

lemma l_empty:
  assumes "invar (Node k v l r)" "v < p\<^sub>0$k"
  shows "set_kdt l \<inter> cbox p\<^sub>0 p\<^sub>1 = {}"
proof -
  have "\<forall>p \<in> set_kdt l. p$k < p\<^sub>0$k"
    using assms by auto
  hence "\<forall>p \<in> set_kdt l. p \<notin> cbox p\<^sub>0 p\<^sub>1"
    using cbox_point_def leD by blast
  thus ?thesis by blast
qed

lemma r_empty:
  assumes "invar (Node k v l r)" "p\<^sub>1$k < v"
  shows "set_kdt r \<inter> cbox p\<^sub>0 p\<^sub>1 = {}"
proof -
  have "\<forall>p \<in> set_kdt r. p\<^sub>1$k < p$k"
    using assms by auto
  hence "\<forall>p \<in> set_kdt r. p \<notin> cbox p\<^sub>0 p\<^sub>1"
    using cbox_point_def leD by blast
  thus ?thesis by blast
qed


subsection \<open>Main Theorem\<close>

theorem search_cbox:
  assumes "invar kdt"
  shows "search p\<^sub>0 p\<^sub>1 kdt = set_kdt kdt \<inter> cbox p\<^sub>0 p\<^sub>1"
  using assms l_empty r_empty by (induction kdt) (auto, blast+)

end
