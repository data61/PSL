(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
License: LGPL
*)

section \<open>Minimization\<close>

theory Minimize_Wrt
  imports Sorted_Wrt
begin

fun minimize_wrt
  where
    "minimize_wrt P [] = []"
  | "minimize_wrt P (x # xs) = x # filter (P x) (minimize_wrt P xs)"

lemma minimize_wrt_subset: "set (minimize_wrt P xs) \<subseteq> set xs"
  by (induct xs) auto

lemmas minimize_wrtD = minimize_wrt_subset [THEN subsetD]

lemma sorted_wrt_minimize_wrt:
  "sorted_wrt P (minimize_wrt P xs)"
  by (induct xs) (auto simp: sorted_wrt_filter)

lemma sorted_wrt_imp_sorted_wrt_minimize_wrt:
  "sorted_wrt Q xs \<Longrightarrow> sorted_wrt Q (minimize_wrt P xs)"
  by (induct xs) (auto simp: sorted_wrt_filter dest: minimize_wrtD)

lemma in_minimize_wrt_False:
  assumes "\<And>x y. Q x y \<Longrightarrow> \<not> Q y x"
    and "sorted_wrt Q xs"
    and "x \<in> set (minimize_wrt P xs)"
    and "\<not> P y x" and "Q y x" and "y \<in> set xs" and "y \<noteq> x"
  shows False
  using assms by (induct xs) (auto dest: minimize_wrtD)

lemma in_minimize_wrtI:
  assumes "x \<in> set xs"
    and "\<forall>y\<in>set xs. P y x"
  shows "x \<in> set (minimize_wrt P xs)"
  using assms by (induct xs) auto

lemma minimize_wrt_eq:
  assumes "distinct xs" and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> P x y \<longleftrightarrow> Q x y \<or> x = y"
  shows "minimize_wrt P xs = minimize_wrt Q xs"
  using assms by (induct xs) (auto, metis contra_subsetD filter_cong minimize_wrt_subset)

lemma minimize_wrt_ni:
  assumes "x \<in> set xs"
    and "x \<notin> set (minimize_wrt Q xs)"
  shows "\<exists>y \<in> set xs. (\<not> Q y x) \<and> x \<noteq> y"
  using assms by (induct xs) (auto)

lemma in_minimize_wrtD:
  assumes "\<And>x y. Q x y \<Longrightarrow> \<not> Q y x"
    and "sorted_wrt Q xs"
    and "x \<in> set (minimize_wrt P xs)"
    and "\<And>x y. \<not> P x y \<Longrightarrow> Q x y"
    and "\<And>x. P x x"
  shows "x \<in> set xs \<and> (\<forall>y\<in>set xs. P y x)"
  using in_minimize_wrt_False [OF assms(1-3)] and minimize_wrt_subset [of P xs] and assms(3-5)
  by blast

lemma in_minimize_wrt_iff:
  assumes "\<And>x y. Q x y \<Longrightarrow> \<not> Q y x"
    and "sorted_wrt Q xs"
    and "\<And>x y. \<not> P x y \<Longrightarrow> Q x y"
    and "\<And>x. P x x"
  shows "x \<in> set (minimize_wrt P xs) \<longleftrightarrow> x \<in> set xs \<and> (\<forall>y\<in>set xs. P y x)"
  using assms and in_minimize_wrtD [of Q xs x P, OF assms(1,2) _ assms(3,4)]
  by (blast intro: in_minimize_wrtI)

lemma set_minimize_wrt:
  assumes "\<And>x y. Q x y \<Longrightarrow> \<not> Q y x"
    and "sorted_wrt Q xs"
    and "\<And>x y. \<not> P x y \<Longrightarrow> Q x y"
    and "\<And>x. P x x"
  shows "set (minimize_wrt P xs) = {x \<in> set xs. \<forall>y\<in>set xs. P y x}"
  by (auto simp: in_minimize_wrt_iff [OF assms])

lemma minimize_wrt_append:
  assumes "\<forall>x\<in>set xs. \<forall>y\<in>set (xs @ ys). P y x"
  shows "minimize_wrt P (xs @ ys) = xs @ filter (\<lambda>y. \<forall>x\<in>set xs. P x y) (minimize_wrt P ys)"
  using assms by (induct xs) (auto intro: filter_cong)

end
