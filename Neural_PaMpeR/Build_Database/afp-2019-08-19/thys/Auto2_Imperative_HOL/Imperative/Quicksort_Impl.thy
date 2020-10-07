(*
  File: Quicksort_Impl.thy
  Author: Bohua Zhan
*)

section \<open>Implementation of quicksort\<close>

theory Quicksort_Impl
  imports Arrays_Impl "../Functional/Quicksort"
begin

text \<open>
  Imperative implementation of quicksort. Also verified in
  theory Imperative\_Quicksort in HOL/Imperative\_HOL/ex
  in the Isabelle library.
\<close>

partial_function (heap) part1 :: "'a::{heap,linorder} array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat Heap" where
  "part1 a l r p = (
     if r \<le> l then return r
     else do {
       v \<leftarrow> Array.nth a l;
       if v \<le> p then
         part1 a (l + 1) r p
       else do {
         swap a l r;
         part1 a l (r - 1) p }})"

lemma part1_to_fun [hoare_triple]:
  "r < length xs \<Longrightarrow> <p \<mapsto>\<^sub>a xs>
   part1 p l r a
   <\<lambda>rs. p \<mapsto>\<^sub>a snd (Quicksort.part1 xs l r a) * \<up>(rs = fst (Quicksort.part1 xs l r a))>"
@proof @fun_induct "Quicksort.part1 xs l r a" @unfold "Quicksort.part1 xs l r a" @qed

text \<open>Partition function\<close>
definition partition :: "'a::{heap,linorder} array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "partition a l r = do {
     p \<leftarrow> Array.nth a r;
     m \<leftarrow> part1 a l (r - 1) p;
     v \<leftarrow> Array.nth a m;
     m' \<leftarrow> return (if v \<le> p then m + 1 else m);
     swap a m' r;
     return m'
   }"

lemma partition_to_fun [hoare_triple]:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> <a \<mapsto>\<^sub>a xs>
   partition a l r
   <\<lambda>rs. a \<mapsto>\<^sub>a snd (Quicksort.partition xs l r) * \<up>(rs = fst (Quicksort.partition xs l r))>"
@proof @unfold "Quicksort.partition xs l r" @qed

text \<open>Quicksort function\<close>
partial_function (heap) quicksort :: "'a::{heap,linorder} array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "quicksort a l r = do {
     len \<leftarrow> Array.len a;
     if l \<ge> r then return ()
     else if r < len then do {
       p \<leftarrow> partition a l r;
       quicksort a l (p - 1);
       quicksort a (p + 1) r
     }
     else return ()
   }"

lemma quicksort_to_fun [hoare_triple]:
  "r < length xs \<Longrightarrow> <a \<mapsto>\<^sub>a xs>
   quicksort a l r
   <\<lambda>_. a \<mapsto>\<^sub>a Quicksort.quicksort xs l r>"
@proof @fun_induct "Quicksort.quicksort xs l r" @unfold "Quicksort.quicksort xs l r" @qed

definition quicksort_all :: "('a::{heap,linorder}) array \<Rightarrow> unit Heap" where
  "quicksort_all a = do {
     n \<leftarrow> Array.len a;
     if n = 0 then return ()
     else quicksort a 0 (n - 1)
   }"

text \<open>Correctness of quicksort.\<close>
theorem quicksort_sorts_basic [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs>
   quicksort_all a
   <\<lambda>_. a \<mapsto>\<^sub>a sort xs>" by auto2

end
