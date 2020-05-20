(* Author: Xingyuan Zhang, Chunhan Wu, Christian Urban *)

theory Myhill
  imports Myhill_2 "Regular-Sets.Derivatives"
begin

section \<open>The theorem\<close>

theorem Myhill_Nerode:
  fixes A::"('a::finite) lang"
  shows "(\<exists>r. A = lang r) \<longleftrightarrow> finite (UNIV // \<approx>A)"
using Myhill_Nerode1 Myhill_Nerode2 by auto


subsection \<open>Second direction proved using partial derivatives\<close>

text \<open>
  An alternaive proof using the notion of partial derivatives for regular 
  expressions due to Antimirov \cite{Antimirov95}.
\<close>

lemma MN_Rel_Derivs:
  shows "x \<approx>A y \<longleftrightarrow> Derivs x A = Derivs y A"
unfolding Derivs_def str_eq_def
by auto

lemma Myhill_Nerode3:
  fixes r::"'a rexp"
  shows "finite (UNIV // \<approx>(lang r))"
proof -
  have "finite (UNIV // =(\<lambda>x. pderivs x r)=)"
  proof - 
    have "range (\<lambda>x. pderivs x r) \<subseteq> Pow (pderivs_lang UNIV r)"
      unfolding pderivs_lang_def by auto
    moreover 
    have "finite (Pow (pderivs_lang UNIV r))" by (simp add: finite_pderivs_lang)
    ultimately
    have "finite (range (\<lambda>x. pderivs x r))"
      by (simp add: finite_subset)
    then show "finite (UNIV // =(\<lambda>x. pderivs x r)=)" 
      by (rule finite_eq_tag_rel)
  qed
  moreover 
  have "=(\<lambda>x. pderivs x r)= \<subseteq> \<approx>(lang r)"
    unfolding tag_eq_def
    by (auto simp add: MN_Rel_Derivs Derivs_pderivs)
  moreover 
  have "equiv UNIV =(\<lambda>x. pderivs x r)="
  and  "equiv UNIV (\<approx>(lang r))"
    unfolding equiv_def refl_on_def sym_def trans_def
    unfolding tag_eq_def str_eq_def
    by auto
  ultimately show "finite (UNIV // \<approx>(lang r))" 
    by (rule refined_partition_finite)
qed

end
