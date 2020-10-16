section \<open>\isaheader{Additions to Distinct Lists}\<close>
theory Dlist_add 
  imports 
  "HOL-Library.Dlist" 
  Automatic_Refinement.Misc
  "../Iterator/SetIteratorOperations" 
begin

primrec dlist_remove1' :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "dlist_remove1' x z [] = z"
| "dlist_remove1' x z (y # ys) 
  = (if x = y then z @ ys else dlist_remove1' x (y # z) ys)"

definition dlist_remove' :: "'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist"
where "dlist_remove' a xs = Dlist (dlist_remove1' a [] (list_of_dlist xs))"

lemma distinct_remove1': "distinct (xs @ ys) \<Longrightarrow> 
  distinct (dlist_remove1' x xs ys)"
  by(induct ys arbitrary: xs) simp_all

lemma set_dlist_remove1': "distinct ys \<Longrightarrow> 
  set (dlist_remove1' x xs ys) = set xs \<union> (set ys - {x})"
  by(induct ys arbitrary: xs) auto

lemma list_of_dlist_remove' [simp, code abstract]:
  "list_of_dlist (dlist_remove' a xs) = dlist_remove1' a [] (list_of_dlist xs)"
by(simp add: dlist_remove'_def distinct_remove1')

lemma dlist_remove'_correct: 
  "y \<in> set (list_of_dlist (dlist_remove' x xs)) 
  \<longleftrightarrow> (if x = y then False else y \<in> set (list_of_dlist xs))"
  by(simp add: dlist_remove'_def 
    Dlist.member_def List.member_def set_dlist_remove1')

definition dlist_iteratei :: "'a dlist \<Rightarrow> ('a, 'b) set_iterator"
  where "dlist_iteratei xs = foldli (list_of_dlist xs)"

lemma dlist_iteratei_correct:
  "set_iterator (dlist_iteratei xs) (set (list_of_dlist xs))"
using distinct_list_of_dlist[of xs] 
      set_iterator_foldli_correct[of "list_of_dlist xs"]
unfolding Dlist.member_def List.member_def dlist_iteratei_def
by simp

lemma dlist_member_empty: "(set (list_of_dlist Dlist.empty)) = {}"
  by(simp add: Dlist.empty_def)

lemma dlist_member_insert [simp]: "set (list_of_dlist (Dlist.insert x xs)) 
  = insert x (set (list_of_dlist xs))"
  by(simp add: Dlist.insert_def Dlist.member_def )

lemma dlist_finite_member [simp, intro!]: "finite (set (list_of_dlist xs))"
by(simp add: member_def )

end
