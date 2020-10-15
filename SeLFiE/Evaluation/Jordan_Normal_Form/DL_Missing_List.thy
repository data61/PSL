(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Missing Lemmas of List\<close>

theory DL_Missing_List
imports Main
begin

lemma nth_map_zip:
assumes "i < length xs"
assumes "i < length ys"
shows "map f (zip xs ys) ! i = f (xs ! i, ys ! i)"
 using nth_zip nth_map length_zip by (simp add: assms(1) assms(2))

lemma nth_map_zip2:
assumes "i < length (map f (zip xs ys))"
shows "map f (zip xs ys) ! i = f (xs ! i, ys ! i)"
 using nth_zip nth_map length_zip assms by simp


fun find_first where
"find_first a [] = undefined" |
"find_first a (x # xs) = (if x = a then 0 else Suc (find_first a xs))"

lemma find_first_le:
assumes "a \<in> set xs"
shows "find_first a xs < length xs"
using assms proof (induction xs)
  case (Cons x xs)
  then show ?case
    using find_first.simps(2) nth_Cons_0 nth_Cons_Suc set_ConsD by auto
qed auto

lemma nth_find_first:
assumes "a \<in> set xs"
shows "xs ! (find_first a xs) = a"
using assms proof (induction xs)
  case (Cons x xs)
  then show ?case
    using find_first.simps(2) nth_Cons_0 nth_Cons_Suc set_ConsD by auto
qed auto

lemma find_first_unique:
assumes "distinct xs"
and "i < length xs"
shows "find_first (xs ! i) xs = i"
using assms proof (induction xs arbitrary:i)
  case (Cons x xs i)
  then show ?case by (cases i; auto)
qed auto

end
