section \<open>Challenge 1.B\<close>
theory Challenge1B
  imports Challenge1A "HOL-Library.Multiset"
begin

(* TODO: Move *)
lemma mset_concat:
  "mset (concat xs) = fold (+) (map mset xs) {#}"
proof -
  have "mset (concat xs) + a = fold (+) (map mset xs) a" for a
  proof (induction xs arbitrary: a)
    case Nil
    then show ?case
      by auto
  next
    case (Cons x xs)
    show ?case
      using Cons.IH[of "mset x + a", symmetric] by simp
  qed
  from this[of "{#}"] show ?thesis
    by auto
qed

subsection \<open>Merging Two Segments\<close>

fun merge :: "'a::{linorder} list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
   "merge [] l2 = l2"
 | "merge l1 [] = l1"
 | "merge (x1 # l1) (x2 # l2) =
    (if (x1 < x2) then x1 # (merge l1 (x2 # l2)) else x2 # (merge (x1 # l1) l2))"

lemma merge_correct:
  assumes "sorted l1"
  assumes "sorted l2"
  shows "
    sorted (merge l1 l2)
  \<and> mset (merge l1 l2) = mset l1 + mset l2
  \<and> set (merge l1 l2) = set l1 \<union> set l2"
  using assms
proof (induction l1 arbitrary: l2)
  case Nil thus ?case
    by simp
next
  case (Cons x1 l1 l2)
  note IH = Cons.IH

  show ?case
    using Cons.prems
  proof (induction l2)
    case Nil then show ?case
      by simp
  next
    case (Cons x2 l2)
    then show ?case
      using IH by (force split: if_split_asm)
  qed
qed

subsection \<open>Merging a List of Segments\<close>

function merge_list :: "'a::{linorder} list list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
   "merge_list [] [] = []"
 | "merge_list [] [l] = l"
 | "merge_list (la # acc2) [] = merge_list [] (la # acc2)"
 | "merge_list (la # acc2) [l] = merge_list [] (l # la # acc2)"
 | "merge_list acc2 (l1 # l2 # ls) =
    merge_list ((merge l1 l2) # acc2) ls"
by pat_completeness simp_all
termination by (relation "measure (\<lambda>(acc, ls). 3 * length acc + 2 * length ls)"; simp)

lemma merge_list_correct:
assumes "\<And>l. l \<in> set ls \<Longrightarrow> sorted l"
assumes "\<And>l. l \<in> set as \<Longrightarrow> sorted l"
shows "
  sorted (merge_list as ls)
\<and> mset (merge_list as ls) = mset (concat (as @ ls))
\<and> set (merge_list as ls) = set (concat (as @ ls))"
using assms
proof (induction as ls rule: merge_list.induct)
next
  case (4 la acc2 l)
  then show ?case
    by (auto simp: algebra_simps)
next
  case (5 acc2 l1 l2 ls)
  have "sorted (merge_list (merge l1 l2 # acc2) ls)
    \<and> mset (merge_list (merge l1 l2 # acc2) ls) = mset (concat ((merge l1 l2 # acc2) @ ls))
    \<and> set (merge_list (merge l1 l2 # acc2) ls) = set (concat ((merge l1 l2 # acc2) @ ls))"
    using 5(2-) merge_correct[of l1 l2] by (intro 5(1)) auto
  then show ?case
    using merge_correct[of l1 l2] 5(2-) by auto
qed simp+

subsection \<open>GHC-Sort\<close>

definition
  "ghc_sort xs = merge_list [] (map (\<lambda>ys. if decr ys then rev ys else ys) (cuts xs))"

lemma decr_sorted:
  assumes "decr xs"
  shows "sorted (rev xs)"
  using assms by (induction xs rule: decr.induct) (auto simp: sorted_append)

lemma incr_sorted:
  assumes "incr xs"
  shows "sorted xs"
  using assms by (induction xs rule: incr.induct) auto

lemma reverse_phase_sorted:
  "\<forall>ys \<in> set (map (\<lambda>ys. if decr ys then rev ys else ys) (cuts xs)). sorted ys"
  using cuts_incr_decr by (auto intro: decr_sorted incr_sorted)

lemma reverse_phase_elements:
  "set (concat (map (\<lambda>ys. if decr ys then rev ys else ys) (cuts xs))) = set xs"
proof -
  have "set (concat (map (\<lambda>ys. if decr ys then rev ys else ys) (cuts xs)))
    = set (concat (cuts xs))"
    by auto
  also have "\<dots> = set xs"
    by (simp add: concat_cuts)
  finally show ?thesis .
qed

lemma reverse_phase_permutation:
  "mset (concat (map (\<lambda>ys. if decr ys then rev ys else ys) (cuts xs))) = mset xs"
proof -
  have "mset (concat (map (\<lambda>ys. if decr ys then rev ys else ys) (cuts xs)))
    = mset (concat (cuts xs))"
    unfolding mset_concat by (auto simp: comp_def intro!: arg_cong2[where f = "fold (+)"])
  also have "\<dots> = mset xs"
    by (simp add: concat_cuts)
  finally show ?thesis .
qed

subsection \<open>Correctness Lemmas\<close>
text \<open>The result is sorted and a permutation of the original elements.\<close>

theorem sorted_ghc_sort:
  "sorted (ghc_sort xs)"
  unfolding ghc_sort_def using reverse_phase_sorted
  by (intro merge_list_correct[THEN conjunct1]) auto

theorem permutation_ghc_sort:
  "mset (ghc_sort xs) = mset xs"
  unfolding ghc_sort_def
  apply (subst merge_list_correct[THEN conjunct2])
  subgoal
    using reverse_phase_sorted by auto
  subgoal
    using reverse_phase_sorted by auto
  apply (subst (2) reverse_phase_permutation[symmetric])
  apply simp
  done

corollary elements_ghc_sort: "set (ghc_sort xs) = set xs"
  using permutation_ghc_sort by (metis set_mset_mset)

subsection \<open>Executable Code\<close>  
export_code ghc_sort checking SML Scala OCaml? Haskell?

value [code] "ghc_sort [1,2,7,3,5,6,9,8,4]"

end