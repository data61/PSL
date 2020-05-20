section\<open>Ordinals in generic extensions\<close>
theory Ordinals_In_MG
  imports
    Forcing_Theorems Relative_Univ
begin

context G_generic
begin

lemma rank_val: "rank(val(G,x)) \<le> rank(x)" (is "?Q(x)")
proof (induct rule:ed_induction[of ?Q])
  case (1 x)
  have "val(G,x) = {val(G,u). u\<in>{t\<in>domain(x). \<exists>p\<in>P .  \<langle>t,p\<rangle>\<in>x \<and> p \<in> G }}"
    using def_val unfolding Sep_and_Replace by blast
  then
  have "rank(val(G,x)) = (\<Union>u\<in>{t\<in>domain(x). \<exists>p\<in>P .  \<langle>t,p\<rangle>\<in>x \<and> p \<in> G }. succ(rank(val(G,u))))"
    using rank[of "val(G,x)"] by simp
  moreover
  have "succ(rank(val(G, y))) \<le> rank(x)" if "ed(y, x)" for y 
    using 1[OF that] rank_ed[OF that] by (auto intro:lt_trans1)
  moreover from this
  have "(\<Union>u\<in>{t\<in>domain(x). \<exists>p\<in>P .  \<langle>t,p\<rangle>\<in>x \<and> p \<in> G }. succ(rank(val(G,u)))) \<le> rank(x)" 
    by (rule_tac UN_least_le) (auto)
  ultimately
  show ?case by simp
qed

lemma Ord_MG_iff:
  assumes "Ord(\<alpha>)" 
  shows "\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> M[G]"
proof
  show "\<alpha> \<in> M \<Longrightarrow> \<alpha> \<in> M[G]" 
    using generic[THEN one_in_G, THEN M_subset_MG] ..
next
  assume "\<alpha> \<in> M[G]"
  then
  obtain x where "x\<in>M" "val(G,x) = \<alpha>"
    using GenExtD by auto
  then
  have "rank(\<alpha>) \<le> rank(x)" 
    using rank_val by blast
  with assms
  have "\<alpha> \<le> rank(x)"
    using rank_of_Ord by simp
  then 
  have "\<alpha> \<in> succ(rank(x))" using ltD by simp
  with \<open>x\<in>M\<close>
  show "\<alpha> \<in> M"
    using cons_closed transitivity[of \<alpha> "succ(rank(x))"] 
      rank_closed unfolding succ_def by simp  
qed
  
end (* G_generic *)

end