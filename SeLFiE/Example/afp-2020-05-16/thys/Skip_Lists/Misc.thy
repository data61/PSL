(*
  File:    Misc.thy
  Authors: Max W. Haslbeck, Manuel Eberl
*)
section \<open>Auxiliary material\<close>
theory Misc
  imports "HOL-Analysis.Analysis"
begin

text \<open>Based on @{term sorted_list_of_set} and @{term the_inv_into} we construct a bijection between
  a finite set A of type 'a::linorder and a set of natural numbers @{term "{..< card A}"}\<close>

lemma bij_betw_mono_on_the_inv_into:
  fixes A::"'a::linorder set" and B::"'b::linorder set"
  assumes b: "bij_betw f A B" and m: "mono_on f A"
  shows "mono_on (the_inv_into A f) B"
proof (rule ccontr)
  assume "\<not> mono_on (the_inv_into A f) B"
  then have "\<exists>r s. r \<in> B \<and> s \<in> B \<and> r \<le> s \<and> \<not> the_inv_into A f s \<ge> the_inv_into A f r"
    unfolding mono_on_def by blast
  then obtain r s where rs: "r \<in> B" "s \<in> B" "r \<le> s" "the_inv_into A f s < the_inv_into A f r"
    by fastforce
  have f: "f (the_inv_into A f b) = b" if "b \<in> B" for b
    using that assms f_the_inv_into_f_bij_betw by metis
  have "the_inv_into A f s \<in> A" "the_inv_into A f r \<in> A"
    using rs assms by (auto simp add: bij_betw_def the_inv_into_into)
  then have "f (the_inv_into A f s) \<le> f (the_inv_into A f r)"
   using rs by (intro mono_onD[OF m]) (auto)
  then have "r = s"
    using rs f by simp
  then show False
    using rs by auto
qed

lemma rev_removeAll_removeAll_rev: "rev (removeAll x xs) = removeAll x (rev xs)"
  by (simp add: removeAll_filter_not_eq rev_filter)

lemma sorted_list_of_set_Min_Cons:
  assumes "finite A" "A \<noteq> {}"
  shows "sorted_list_of_set A = Min A # sorted_list_of_set (A - {Min A})"
proof -
  have *: "A = insert (Min A) A"
    using assms Min_in by (auto)
  then have "sorted_list_of_set A = insort (Min A) (sorted_list_of_set (A - {Min A}))"
    using assms by (subst *, intro sorted_list_of_set_insert) auto
  also have "\<dots> = Min A # sorted_list_of_set (A - {Min A})"
    using assms by (intro insort_is_Cons) (auto)
  finally show ?thesis
    by simp
qed

lemma sorted_list_of_set_filter:
  assumes "finite A"
  shows "sorted_list_of_set ({x\<in>A. P x}) = filter P (sorted_list_of_set A)"
  using assms proof (induction "sorted_list_of_set A" arbitrary: A)
  case (Cons x xs)
  have x: "x \<in> A"
    using Cons sorted_list_of_set list.set_intros(1) by metis
  have "sorted_list_of_set A = Min A # sorted_list_of_set (A - {Min A})"
    using Cons by (intro sorted_list_of_set_Min_Cons) auto
  then have 1: "x = Min A" "xs = sorted_list_of_set (A - {x})"
    using Cons by auto
  { assume Px: "P x"
    have 2: "sorted_list_of_set {x \<in> A. P x} = Min {x \<in> A. P x} # sorted_list_of_set ({x \<in> A. P x} - {Min {x \<in> A. P x}})"
      using Px Cons 1 sorted_list_of_set_eq_Nil_iff
      by (intro sorted_list_of_set_Min_Cons) fastforce+
    also have 3: "Min {x \<in> A. P x} = x"
      using Cons 1 Px x by (auto intro!: Min_eqI)
    also have 4: "{x \<in> A. P x} - {x} = {y \<in> A - {x}. P y}"
      by blast
    also have 5: "sorted_list_of_set {y \<in> A - {x}. P y} = filter P (sorted_list_of_set (A - {x}))"
      using 1 Cons by (intro Cons) (auto)
    also have "\<dots> = filter P xs"
      using 1 by simp
    also have "filter P (sorted_list_of_set A) = x # filter P xs"
      using Px by (simp flip: \<open>x # xs = sorted_list_of_set A\<close>)
    finally have ?case
      by auto }
  moreover
  { assume Px: "\<not> P x"
    then have "{x \<in> A. P x} = {y \<in> A - {x}. P y}"
      by blast
    also have "sorted_list_of_set \<dots> = filter P (sorted_list_of_set (A - {x}))"
      using 1 Cons by (intro Cons) auto
    also have  "filter P (sorted_list_of_set (A - {x})) = filter P (sorted_list_of_set A)"
      using 1 Px by (simp flip: \<open>x # xs = sorted_list_of_set A\<close>)
    finally have ?case
      by simp }
  ultimately show ?case
    by blast
qed (use sorted_list_of_set_eq_Nil_iff in fastforce)

lemma sorted_list_of_set_Max_snoc:
  assumes "finite A" "A \<noteq> {}"
  shows "sorted_list_of_set A = sorted_list_of_set (A - {Max A}) @ [Max A]"
proof -
  have *: "A = insert (Max A) A"
    using assms Max_in by (auto)
  then have "sorted_list_of_set A = insort (Max A) (sorted_list_of_set (A - {Max A}))"
    using assms by (subst *, intro sorted_list_of_set_insert) auto
  also have "\<dots> = sorted_list_of_set (A - {Max A}) @ [Max A]"
    using assms by (intro sorted_insort_is_snoc) (auto)
  finally show ?thesis
    by simp
qed

lemma sorted_list_of_set_image:
  assumes "mono_on g A" "inj_on g A"
  shows "(sorted_list_of_set (g ` A)) = map g (sorted_list_of_set A)"
proof (cases "finite A")
  case True
  then show ?thesis
    using assms proof (induction "sorted_list_of_set A" arbitrary: A)
    case Nil
    then show ?case
      using sorted_list_of_set_eq_Nil_iff by fastforce
  next
    case (Cons x xs A)
    have not_empty_A: "A \<noteq> {}"
      using Cons sorted_list_of_set_eq_Nil_iff by auto
    have *: "Min (g ` A) = g (Min A)"
    proof -
      have "g (Min A) \<le> g a" if "a \<in> A" for a
        using that Cons Min_in Min_le not_empty_A by (auto intro!: mono_onD[of g])
      then show ?thesis
        using Cons not_empty_A by (intro Min_eqI) auto
    qed
    have "g ` A \<noteq> {}" "finite (g ` A)"
      using Cons by auto
    then have "(sorted_list_of_set (g ` A)) =
             Min (g ` A) # sorted_list_of_set ((g ` A) - {Min (g ` A)})"
      by (auto simp add: sorted_list_of_set_Min_Cons)
    also have "(g ` A) - {Min (g ` A)} = g ` (A - {Min A})"
      using Cons Min_in not_empty_A * by (subst inj_on_image_set_diff[of _ A]) auto
    also have "sorted_list_of_set (g ` (A - {Min A})) = map g (sorted_list_of_set (A - {Min A}))"
      using not_empty_A Cons mono_on_subset[of _ A "A - {Min A}"] inj_on_subset[of _ A "A - {Min A}"]
      by (intro Cons) (auto simp add: sorted_list_of_set_Min_Cons)
    finally show ?case
      using Cons not_empty_A * by (auto simp add: sorted_list_of_set_Min_Cons)
  qed
next
  case False
  then show ?thesis
    using assms by (simp add: finite_image_iff)
qed

lemma sorted_list_of_set_length: "length (sorted_list_of_set A) = card A"
  using distinct_card sorted_list_of_set[of A] by (cases "finite A") fastforce+

lemma sorted_list_of_set_bij_betw:
  assumes "finite A"
  shows "bij_betw (\<lambda>n. sorted_list_of_set A ! n) {..<card A} A"
  by (rule bij_betw_nth) (fastforce simp add: assms sorted_list_of_set_length)+

lemma nth_mono_on:
  assumes "sorted xs" "distinct xs" "set xs = A"
  shows "mono_on (\<lambda>n. xs ! n) {..<card A}"
  using assms by (intro mono_onI sorted_nth_mono) (auto simp add: distinct_card)

lemma sorted_list_of_set_mono_on:
  "finite A \<Longrightarrow> mono_on (\<lambda>n. sorted_list_of_set A ! n) {..<card A}"
  by (rule nth_mono_on) (auto)

definition bij_mono_map_set_to_nat :: "'a::linorder set \<Rightarrow> 'a \<Rightarrow> nat" where
  "bij_mono_map_set_to_nat A =
    (\<lambda>x. if x \<in> A then the_inv_into {..<card A} ((!) (sorted_list_of_set A)) x
                  else card A)"

lemma bij_mono_map_set_to_nat:
  assumes "finite A"
  shows "bij_betw (bij_mono_map_set_to_nat A) A {..<card A}"
        "mono_on (bij_mono_map_set_to_nat A) A"
        "(bij_mono_map_set_to_nat A) ` A = {..<card A}"
proof -
  let ?f = "bij_mono_map_set_to_nat A"
  have "bij_betw (the_inv_into {..<card A} ((!) (sorted_list_of_set A))) A {..<card A}"
    using assms sorted_list_of_set_bij_betw  bij_betw_the_inv_into by blast
  moreover have "bij_betw (the_inv_into {..<card A} ((!) (sorted_list_of_set A))) A {..<card A}
                     = bij_betw ?f A {..<card A}"
    unfolding bij_mono_map_set_to_nat_def by (rule bij_betw_cong) simp
  ultimately show *: "bij_betw (bij_mono_map_set_to_nat A) A {..<card A}"
    by blast
  have "mono_on (the_inv_into {..<card A} ((!) (sorted_list_of_set A))) A"
    using assms sorted_list_of_set_bij_betw
      sorted_list_of_set_mono_on by (intro bij_betw_mono_on_the_inv_into) auto
  then show "mono_on (bij_mono_map_set_to_nat A) A"
    unfolding bij_mono_map_set_to_nat_def using mono_onD by (intro mono_onI) (auto)
  show "?f ` A = {..<card A}"
      using assms bij_betw_imp_surj_on * by blast
qed

end
