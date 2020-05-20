subsection \<open>Sorting\<close>

text \<open>Some preliminary lemmas about sorting.\<close>

theory Sorting
  imports Main "HOL.List" "HOL-Library.Sublist"
begin

lemma insort:
  assumes "Suc l < length s"
  assumes "s ! l < (v :: 'a :: linorder)"
  assumes "s ! (l+1) > v"
  assumes "sorted_wrt (<) s"
  shows "sorted_wrt (<) ((take (Suc l) s)@v#(drop (Suc l) s))"
proof -
  have "sorted_wrt (<) (take (Suc l) s@(drop (Suc l) s))"
    using assms(4) by simp
  moreover have
    "\<And>x. x \<in> set (take (Suc l) s) = (\<exists>i. i < (Suc l) \<and> i < length s \<and> s ! i = x)" 
    by (metis in_set_conv_nth length_take min_less_iff_conj nth_take)
  hence "\<And>x. x \<in> set (take (Suc l) s) \<Longrightarrow> x < v"
    using assms apply (simp) 
    using less_Suc_eq sorted_wrt_nth_less by fastforce
  moreover have
    "\<And>x. x \<in> set (drop (Suc l) s) = (\<exists>i. Suc l + i < length s \<and> s ! (Suc l + i) = x)"
    using assms(1) by (simp add:in_set_conv_nth add.commute less_diff_conv)
  hence "\<And>x. x \<in> set (drop (Suc l) s) \<Longrightarrow> x > v"
    using assms apply (simp) 
    by (metis add.right_neutral add_diff_cancel_left' diff_Suc_Suc diff_is_0_eq'
        leI le_less_trans less_imp_le sorted_wrt_iff_nth_less)
  ultimately show ?thesis
    by (simp add:sorted_wrt_append del:append_take_drop_id)
qed

lemma sorted_wrt_irrefl_distinct:
  assumes "irreflp r"
  shows "sorted_wrt r xs \<longrightarrow> distinct xs"
  using assms by (induction xs, simp, simp, meson irreflp_def)

lemma sort_set_unique_h:
  assumes "irreflp r \<and> transp r"
  assumes "set (x#xs) = set (y#ys)" 
  assumes "\<forall>z \<in> set xs. r x z" 
  assumes "\<forall>z \<in> set ys. r y z" 
  shows "x = y \<and> set xs = set ys"
  by (metis assms insert_eq_iff irreflp_def list.set_intros(1)
      list.simps(15) set_ConsD transpD)

lemma sort_set_unique_rel:
  assumes "irreflp r \<and> transp r"
  assumes "set x = set y"
  assumes "sorted_wrt r x"
  assumes "sorted_wrt r y"
  shows "x = y"
proof -
  have "length x = length y" 
    using assms by (metis sorted_wrt_irrefl_distinct distinct_card)
  then show ?thesis using assms 
    apply(induct rule:list_induct2, simp, simp)
    by (metis assms(1) list.simps(15) sort_set_unique_h) 
qed

lemma sort_set_unique:
  assumes "set x = set y"
  assumes "sorted_wrt (<) (map (f :: ('a \<Rightarrow> ('b :: linorder)))  x)"
  assumes "sorted_wrt (<) (map f y)"
  shows "x = y"
  using assms apply (simp add:sorted_wrt_map) 
  by (metis (no_types, lifting) irreflp_def less_irrefl sort_set_unique_rel 
      transpD transpI transp_less)

text \<open>If two sequences contain the same element and strictly increasing with respect.\<close>

lemma subseq_imp_sorted:
  assumes "subseq s t"
  assumes "sorted_wrt p t"
  shows "sorted_wrt p s"
proof -
  have "sorted_wrt p s \<or> \<not> sorted_wrt p t"
  apply (rule list_emb.induct[where P="(=)"])
  using list_emb_set assms by fastforce+
  thus ?thesis using assms by blast
qed

text \<open>If a sequence @{text t} is sorted with respect to a relation @{text p} then a subsequence will 
  be as well.\<close>

fun to_ord where "to_ord r x y = (\<not>(r\<^sup>*\<^sup>* y x))"

lemma trancl_idemp: "r\<^sup>+\<^sup>+\<^sup>+\<^sup>+ x y = r\<^sup>+\<^sup>+ x y" 
  by (metis r_into_rtranclp reflclp_tranclp rtranclp_idemp rtranclp_reflclp 
      rtranclp_tranclp_tranclp tranclp.cases tranclp.r_into_trancl)

lemma top_sort:
  fixes rp
  assumes "acyclicP r"
  shows "finite s \<longrightarrow> (\<exists>l. set l = s \<and> sorted_wrt (to_ord r) l \<and> distinct l)"
proof (induction "card s" arbitrary:s)
  case 0
  then show ?case by auto
next
  case (Suc n)
  hence "s \<noteq> {}" by auto
  moreover 
  have "acyclicP (r\<^sup>+\<^sup>+)" using assms
    by (simp add:acyclic_def trancl_def trancl_idemp)
  hence "acyclic ({(x,y). r\<^sup>+\<^sup>+ x y} \<inter> s \<times> s)"
    by (meson acyclic_subset inf_le1)
  hence "wf ({(x,y). r\<^sup>+\<^sup>+ x y} \<inter> s \<times> s)" using Suc 
    by (metis card_infinite finite_Int finite_SigmaI nat.distinct(1) 
        wf_iff_acyclic_if_finite)
  ultimately obtain z where 
    "z \<in> s \<and> (\<forall>y. (y, z) \<in>  ({(x,y). r\<^sup>+\<^sup>+ x y} \<inter> s \<times> s) \<longrightarrow> y \<notin> s)" 
    by (metis ex_in_conv wf_eq_minimal)
  hence z_def: "z \<in> s \<and> (\<forall>y. r\<^sup>+\<^sup>+ y z \<longrightarrow> y \<notin> s)" by blast
  hence "card (s - {z}) = n"
    by (metis One_nat_def Suc.hyps(2) card_Diff_singleton_if card_infinite 
        diff_Suc_Suc diff_zero nat.simps(3))
  then obtain l where l_def: 
    "set l = s - {z} \<and> sorted_wrt (to_ord r) l \<and> distinct l" 
    by (metis Zero_not_Suc card_infinite finite_Diff Suc)
  hence "set (z#l) = s" using z_def by auto
  moreover have "\<forall>y \<in> set l. \<not>(r\<^sup>*\<^sup>* y z)" using z_def l_def rtranclpD by force
  ultimately show ?case 
    by (metis distinct.simps(2) insert_absorb l_def list.simps(15) 
        sorted_wrt.simps(2) to_ord.elims(3))
qed

lemma top_sort_eff:
  assumes "irreflp p\<^sup>+\<^sup>+"
  assumes "sorted_wrt (to_ord p) x" 
  assumes "i < length x"
  assumes "j < length x"
  assumes "(p\<^sup>+\<^sup>+ (x ! i) (x ! j))"
  shows "i < j"
  using assms apply (cases "i > j")
   apply (metis sorted_wrt_nth_less r_into_rtranclp reflclp_tranclp
          rtranclp_idemp rtranclp_reflclp to_ord.simps)
  by (metis irreflp_def nat_neq_iff)

end