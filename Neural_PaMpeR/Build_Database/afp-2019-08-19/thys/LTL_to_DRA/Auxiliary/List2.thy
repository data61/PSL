(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Auxiliary List Facts\<close>

theory List2                  
  imports Main "HOL-Library.Omega_Words_Fun" "List-Index.List_Index" 
begin

subsection \<open>remdups\_fwd\<close>
\<comment> \<open>Remove duplicates of a list in a forward moving direction\<close>

fun remdups_fwd_acc 
where
  "remdups_fwd_acc Acc [] = []"
| "remdups_fwd_acc Acc (x#xs) = (if x \<in> Acc then [] else [x]) @ remdups_fwd_acc (insert x Acc) xs"

lemma remdups_fwd_acc_append[simp]:
  "remdups_fwd_acc Acc (xs@ys) = (remdups_fwd_acc Acc xs) @ (remdups_fwd_acc (Acc \<union> set xs) ys)"
  by (induction xs arbitrary: Acc) simp+

lemma remdups_fwd_acc_set[simp]:
  "set (remdups_fwd_acc Acc xs) = set xs - Acc"
  by (induction xs arbitrary: Acc) force+

lemma remdups_fwd_acc_distinct:
  "distinct (remdups_fwd_acc Acc xs)"
  by (induction xs arbitrary: Acc rule: rev_induct) simp+

lemma remdups_fwd_acc_empty:
  "set xs \<subseteq> Acc \<longleftrightarrow> remdups_fwd_acc Acc xs = []"
  by (metis remdups_fwd_acc_set set_empty Diff_eq_empty_iff Diff_eq_empty_iff)

lemma remdups_fwd_acc_drop:
  "set ys \<subseteq> Acc \<union> set xs \<Longrightarrow> remdups_fwd_acc Acc (xs @ ys @ zs) = remdups_fwd_acc Acc (xs @ zs)"
  by (simp add: remdups_fwd_acc_empty sup.absorb1)

lemma remdups_fwd_acc_filter:
  "remdups_fwd_acc Acc (filter P xs) = filter P (remdups_fwd_acc Acc xs)"
  by (induction xs rule: rev_induct) simp+

fun remdups_fwd
where
  "remdups_fwd xs = remdups_fwd_acc {} xs "

lemma remdups_fwd_eq:
  "remdups_fwd xs = (rev o remdups o rev) xs"
  by (induction xs rule: rev_induct) simp+

lemma remdups_fwd_set[simp]:
  "set (remdups_fwd xs) = set xs"
  by simp

lemma remdups_fwd_distinct:
  "distinct (remdups_fwd xs)"
  using remdups_fwd_acc_distinct by simp

lemma remdups_fwd_filter:
  "remdups_fwd (filter P xs) = filter P (remdups_fwd xs)"
  using remdups_fwd_acc_filter by simp

subsection \<open>Split Lemmas\<close>

lemma map_splitE:
  assumes "map f xs = ys @ zs"
  obtains us vs where "xs = us @ vs" and "map f us = ys" and "map f vs = zs"
  by (insert assms; induction ys arbitrary: xs) 
     (simp_all add: map_eq_Cons_conv, metis append_Cons) 
  
lemma filter_split':
  "filter P xs = ys @ zs \<Longrightarrow> \<exists>us vs. xs = us @ vs \<and> filter P us = ys \<and> filter P vs = zs"
proof (induction ys arbitrary: zs xs rule: rev_induct)
  case (snoc y ys)
    obtain us vs where "xs = us @ vs" and "filter P us = ys" and "filter P vs = y # zs"
      using snoc(1)[OF snoc(2)[unfolded append_assoc]] by auto
    moreover
    then obtain vs' vs'' where "vs = vs' @ y # vs''" and "y \<notin> set vs'" and "(\<forall>u\<in>set vs'. \<not> P u)" and "filter P vs'' = zs" and "P y"
      unfolding filter_eq_Cons_iff by blast
    ultimately
    have "xs = (us @ vs' @ [y]) @ vs''" and "filter P (us @ vs' @ [y]) = ys @ [y]" and "filter P (vs'') = zs"
      unfolding filter_append by auto
    thus ?case
      by blast
qed fastforce

lemma filter_splitE:
  assumes "filter P xs = ys @ zs"
  obtains us vs where "xs = us @ vs" and "filter P us = ys" and "filter P vs = zs"
  using filter_split'[OF assms] by blast

lemma filter_map_splitE:
  assumes "filter P (map f xs) = ys @ zs"
  obtains us vs where "xs = us @ vs" and "filter P (map f us) = ys" and "filter P (map f vs) = zs"
  using assms by (fastforce elim: filter_splitE map_splitE)

lemma filter_map_split_iff:
  "filter P (map f xs) = ys @ zs \<longleftrightarrow> (\<exists>us vs. xs = us @ vs \<and> filter P (map f us) = ys \<and> filter P (map f vs) = zs)"
  by (fastforce elim: filter_map_splitE)

lemma list_empty_prefix:
  "xs @ y # zs = y # us \<Longrightarrow> y \<notin> set xs \<Longrightarrow> xs = []"
  by (metis hd_append2 list.sel(1) list.set_sel(1))

lemma remdups_fwd_split:
  "remdups_fwd_acc Acc xs = ys @ zs \<Longrightarrow> \<exists>us vs. xs = us @ vs \<and> remdups_fwd_acc Acc us = ys \<and> remdups_fwd_acc (Acc \<union> set ys) vs = zs"
proof (induction ys arbitrary: zs rule: rev_induct)
  case (snoc y ys)
    then obtain us vs where "xs = us @ vs" 
      and "remdups_fwd_acc Acc us = ys" 
      and "remdups_fwd_acc (Acc \<union> set ys) vs = y # zs"
      by fastforce
    moreover
    hence "y \<in> set vs" and "y \<notin> Acc \<union> set ys"
      using remdups_fwd_acc_set[of "Acc \<union> set ys" vs] by auto
    moreover
    then obtain vs' vs'' where "vs = vs' @ y # vs''" and "y \<notin> set vs'" 
      using split_list_first by metis
    moreover
    hence "remdups_fwd_acc (Acc \<union> set ys) vs' = []"
      using \<open>remdups_fwd_acc (Acc \<union> set ys) vs = y # zs\<close> \<open>y \<notin> Acc \<union> set ys\<close>
      by (force intro: list_empty_prefix)
    ultimately
    have "xs = (us @ vs' @ [y]) @ vs''"
      and "remdups_fwd_acc Acc (us @ vs' @ [y]) = ys @ [y]"
      and "remdups_fwd_acc (Acc \<union> set (ys @ [y])) vs'' = zs"
      by (auto simp add: remdups_fwd_acc_empty sup.absorb1) 
    thus ?case
      by blast  
qed force

lemma remdups_fwd_split_exact:
  assumes "remdups_fwd_acc Acc xs = ys @ x # zs"
  shows "\<exists>us vs. xs = us @ x # vs \<and> x \<notin> Acc \<and> x \<notin> set ys \<and> remdups_fwd_acc Acc us = ys \<and> remdups_fwd_acc (Acc \<union> set ys \<union> {x}) vs = zs"
proof -
  obtain us vs where "xs = us @ vs" and "remdups_fwd_acc Acc us = ys" and "remdups_fwd_acc (Acc \<union> set ys) vs = x # zs"
    using assms by (blast dest: remdups_fwd_split)
  moreover
  hence "x \<in> set vs" and "x \<notin> Acc \<union> set ys"
    using remdups_fwd_acc_set[of "Acc \<union> set ys"] by (fastforce, metis (no_types) Diff_iff list.set_intros(1))
  moreover
  then obtain vs' vs'' where "vs = vs' @ x # vs''" and "x \<notin> set vs'" 
    by (blast dest: split_list_first)
  moreover
  hence "set vs' \<subseteq> Acc \<union> set ys"
    using \<open>remdups_fwd_acc (Acc \<union> set ys) vs = x # zs\<close> \<open>x \<notin> Acc \<union> set ys\<close> 
    unfolding remdups_fwd_acc_empty by (fastforce intro: list_empty_prefix)
  moreover
  hence "remdups_fwd_acc (Acc \<union> set ys) vs' = []"
    using remdups_fwd_acc_empty by blast
  ultimately
  have "xs = (us @ vs') @ x # vs''"
    and "remdups_fwd_acc Acc (us @ vs') = ys"
    and "remdups_fwd_acc (Acc \<union> set ys \<union> {x}) vs'' = zs"
    by (fastforce dest: sup.absorb1)+ 
  thus ?thesis
    using \<open>x \<notin> Acc \<union> set ys\<close> by blast
qed

lemma remdups_fwd_split_exactE:
  assumes "remdups_fwd_acc Acc xs = ys @ x # zs"
  obtains us vs where "xs = us @ x # vs" and "x \<notin> set us" and "remdups_fwd_acc Acc us = ys" and "remdups_fwd_acc (Acc \<union> set ys \<union> {x}) vs = zs"
    using remdups_fwd_split_exact[OF assms] by auto

lemma remdups_fwd_split_exact_iff:
  "remdups_fwd_acc Acc xs = ys @ x # zs \<longleftrightarrow> 
    (\<exists>us vs. xs = us @ x # vs \<and> x \<notin> Acc \<and> x \<notin> set us \<and> remdups_fwd_acc Acc us = ys \<and> remdups_fwd_acc (Acc \<union> set ys \<union> {x}) vs = zs)"
  using remdups_fwd_split_exact by fastforce 

lemma sorted_pre:
  "(\<And>x y xs ys. zs = xs @ [x, y] @ ys \<Longrightarrow> x \<le> y) \<Longrightarrow> sorted zs"
apply (induction zs)
 apply simp
by (metis append_Nil append_Cons list.exhaust sorted1 sorted2)

lemma sorted_list:
  assumes "x \<in> set xs" and "y \<in> set xs"
  assumes "sorted (map f xs)" and "f x < f y"
  shows "\<exists>xs' xs'' xs'''. xs = xs' @ x # xs'' @ y # xs'''"
proof -
  obtain ys zs where "xs = ys @ y # zs" and "y \<notin> set ys"
    using assms by (blast dest: split_list_first)
  moreover
  hence "sorted (map f (y # zs))" 
    using \<open>sorted (map f xs)\<close> by (simp add: sorted_append)
  hence "\<forall>x\<in>set (map f (y # zs)). f y \<le> x"
    by force
  hence "\<forall>x\<in>set (y # zs). f y \<le> f x"
    by auto
  have "x \<in> set ys"
    apply (rule ccontr)
    using \<open>f x < f y\<close> \<open>x \<in> set xs\<close> \<open>\<forall>x\<in>set (y # zs). f y \<le> f x\<close> unfolding \<open>xs = ys @ y # zs\<close> set_append by auto
  then obtain ys' zs' where "ys = ys' @ x # zs'"
    using assms by (blast dest: split_list_first)
  ultimately
  show ?thesis
    by auto
qed
    
lemma takeWhile_foo:
  "x \<notin> set ys \<Longrightarrow> ys = takeWhile (\<lambda>y. y \<noteq> x) (ys @ x # zs)"
  by (metis (mono_tags, lifting) append_Nil2 takeWhile.simps(2) takeWhile_append2)

lemma takeWhile_split:
  "x \<in> set xs \<Longrightarrow> y \<in> set (takeWhile (\<lambda>y. y \<noteq> x) xs) \<Longrightarrow> \<exists>xs' xs'' xs'''. xs = xs' @ y # xs'' @ x # xs'''"
  using split_list_first by (metis append_Cons append_assoc takeWhile_foo)
 
lemma takeWhile_distinct:
  "distinct (xs' @ x # xs'') \<Longrightarrow> y \<in> set (takeWhile (\<lambda>y. y \<noteq> x) (xs' @ x # xs'')) \<longleftrightarrow> y \<in> set xs'"
  by (induction xs') simp+

lemma finite_lists_length_eqE:
  assumes "finite A" 
  shows "finite {xs. set xs = A \<and> length xs = n}"
proof -
  have "{xs. set xs = A \<and> length xs = n} \<subseteq> {xs. set xs \<subseteq> A \<and> length xs = n}"
    by blast
  thus ?thesis
    using finite_lists_length_eq[OF assms(1), of n] using finite_subset by auto
qed

lemma finite_set2:
  assumes "card A = n" and "finite A"
  shows "finite {xs. set xs = A \<and> distinct xs}"
proof -
  have "{xs. set xs = A \<and> distinct xs} \<subseteq> {xs. set xs = A \<and> length xs = n}"
    using assms(1) distinct_card by fastforce
  thus ?thesis
    by (metis (no_types, lifting) finite_lists_length_eqE[OF \<open>finite A\<close>, of n] finite_subset)
qed

lemma set_list: 
  assumes "finite (set ` XS)"
  assumes "\<And>xs. xs \<in> XS \<Longrightarrow> distinct xs"
  shows "finite XS"
proof -
  have "XS \<subseteq> {xs | xs. set xs \<in> set ` XS \<and> distinct xs}"
    using assms by auto
  moreover
  have 1: "{xs |xs. set xs \<in> set ` XS \<and> distinct xs} = \<Union>{{xs | xs. set xs = A \<and> distinct xs} | A. A \<in> set ` XS}"
    by auto
  have "finite {xs |xs. set xs \<in> set ` XS \<and> distinct xs}"
    using finite_set2[OF _ finite_set] distinct_card  assms(1) unfolding 1 by fastforce
  ultimately
  show ?thesis
    using finite_subset by blast
qed

lemma set_foldl_append:
  "set (foldl (@) i xs) = set i \<union> \<Union>{set x | x. x \<in> set xs}"
  by (induction xs arbitrary: i) auto

subsection \<open>Short-circuited Version of @{const foldl}\<close>

fun foldl_break :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
where
  "foldl_break f s a [] = a" 
| "foldl_break f s a (x # xs) = (if s a then a else foldl_break f s (f a x) xs)"

lemma foldl_break_append:
  "foldl_break f s a (xs @ ys) = (if s (foldl_break f s a xs) then foldl_break f s a xs else (foldl_break f s (foldl_break f s a xs) ys))"
  by (induction xs arbitrary: a) (cases ys, auto)

subsection \<open>Suffixes\<close>

\<comment> \<open>Non empty suffixes of finite words - specialised!\<close>

fun suffixes
where
  "suffixes [] = []"
| "suffixes (x#xs) = (suffixes xs) @ [x#xs]"

lemma suffixes_append:
  "suffixes (xs @ ys) = (suffixes ys) @ (map (\<lambda>zs. zs @ ys) (suffixes xs))"
  by (induction xs) simp_all

lemma suffixes_alt_def:
  "suffixes xs = rev (prefix (length xs) (\<lambda>i. drop i xs))"
proof (induction xs rule: rev_induct)
  case (snoc x xs)
    show ?case
      by (simp add: subsequence_def suffixes_append snoc rev_map)
qed simp

end
