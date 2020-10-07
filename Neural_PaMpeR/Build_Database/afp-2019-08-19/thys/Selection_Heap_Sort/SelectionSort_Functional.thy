(*  Title:      Sort.thy
    Author:     Danijela Petrovi\'c, Facylty of Mathematics, University of Belgrade *)

section \<open>Verification of functional Selection Sort\<close>

theory SelectionSort_Functional
imports RemoveMax
begin

subsection \<open>Defining data structure\<close>

text\<open>Selection sort works with list and that is the reason why {\em
  Collection} should be interpreted as list.\<close>

interpretation Collection "[]" "\<lambda> l. l = []" id mset
by (unfold_locales, auto)

subsection \<open>Defining function remove\_max\<close>

text\<open>The following is definition of {\em remove\_max} function. 
The idea is very well known -- assume that the maximum element is the
first one and then compare with each element of the list. Function
{\em f} is one step in iteration, it compares current maximum {\em m}
with one element {\em x}, if it is bigger then {\em m} stays current
maximum and {\em x} is added in the resulting list, otherwise {\em x}
is current maximum and {\em m} is added in the resulting
list.
\<close>

fun f where "f (m, l) x = (if x \<ge> m then (x, m#l) else (m, x#l))"

definition remove_max where
  "remove_max l = foldl f (hd l, []) (tl l)"

lemma max_Max_commute: 
  "finite A \<Longrightarrow> max (Max (insert m A)) x = max m (Max (insert x A))"
  apply (cases "A = {}", simp)  
  by (metis Max_insert max.commute max.left_commute)

text\<open>The function really returned the
maximum value.\<close>

lemma remove_max_max_lemma:
  shows "fst (foldl f (m, t) l) =  Max (set (m # l))"
proof (induct l arbitrary: m t rule: rev_induct)
  case (snoc x xs)
  let ?a = "foldl f (m, t) xs"
  let ?m' = "fst ?a" and ?t' = "snd ?a"
  have "fst (foldl f (m, t) (xs @ [x])) = max ?m' x"
    by (cases ?a) (auto simp add: max_def)
  thus ?case
    using snoc
    by (simp add: max_Max_commute)
qed simp

lemma remove_max_max:
  assumes "l \<noteq> []" "(m, l') = remove_max l"
  shows "m = Max (set l)"
using assms
unfolding remove_max_def
using remove_max_max_lemma[of "hd l" "[]" "tl l"]
using fst_conv[of m l']
by simp

text\<open>Nothing new is added in the list and noting is deleted
from the list except the maximum element.\<close>

lemma remove_max_mset_lemma:
  assumes "(m, l') = foldl f (m', t') l"
  shows "mset (m # l') = mset (m' # t' @ l)"
using assms
proof (induct l arbitrary: l' m m' t' rule: rev_induct)
  case (snoc x xs)
  let ?a = "foldl f (m', t') xs"
  let ?m' = "fst ?a" and ?t' = "snd ?a"
  have "mset (?m' # ?t') = mset (m' # t' @ xs)"
    using snoc(1)[of ?m' ?t' m' t']
    by simp
  thus ?case
    using snoc(2)
    apply (cases "?a")
    by (auto split: if_split_asm) 
qed simp

lemma remove_max_mset:
  assumes "l \<noteq> []" "(m, l') = remove_max l" 
  shows "add_mset m (mset l') = mset l"
using assms
unfolding remove_max_def
using remove_max_mset_lemma[of m l' "hd l" "[]" "tl l"]
by auto

definition ssf_ssort' where
  [simp, code del]: "ssf_ssort' = RemoveMax.ssort' (\<lambda> l. l = []) remove_max"
definition ssf_ssort where 
  [simp, code del]: "ssf_ssort = RemoveMax.ssort (\<lambda> l. l = []) id remove_max"

interpretation SSRemoveMax: 
  RemoveMax "[]" "\<lambda> l. l = []" id mset remove_max "\<lambda> _. True" 
  rewrites
 "RemoveMax.ssort' (\<lambda> l. l = []) remove_max = ssf_ssort'" and
 "RemoveMax.ssort (\<lambda> l. l = []) id remove_max = ssf_ssort"
using remove_max_max
by (unfold_locales, auto simp add: remove_max_mset)


  
end
