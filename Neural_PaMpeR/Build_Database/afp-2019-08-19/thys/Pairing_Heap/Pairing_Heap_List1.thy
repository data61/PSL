(* Author: Tobias Nipkow *)

section \<open>Pairing Heap According to Okasaki\<close>

theory Pairing_Heap_List1
imports
  "HOL-Library.Multiset"
  "HOL-Library.Pattern_Aliases"
  "HOL-Data_Structures.Priority_Queue_Specs"
begin

subsection \<open>Definitions\<close>

text
\<open>This implementation follows Okasaki \cite{Okasaki}.
It satisfies the invariant that \<open>Empty\<close> only occurs
at the root of a pairing heap. The functional correctness proof does not
require the invariant but the amortized analysis (elsewhere) makes use of it.\<close>

datatype 'a heap = Empty | Hp 'a "'a heap list"

fun get_min  :: "'a heap \<Rightarrow> 'a" where
"get_min (Hp x _) = x"

hide_const (open) insert

context includes pattern_aliases
begin

fun merge :: "('a::linorder) heap \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"merge h Empty = h" |
"merge Empty h = h" |
"merge (Hp x lx =: hx) (Hp y ly =: hy) = 
    (if x < y then Hp x (hy # lx) else Hp y (hx # ly))"

end

fun insert :: "('a::linorder) \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"insert x h = merge (Hp x []) h"

fun pass\<^sub>1 :: "('a::linorder) heap list \<Rightarrow> 'a heap list" where
  "pass\<^sub>1 [] = []"
| "pass\<^sub>1 [h] = [h]" 
| "pass\<^sub>1 (h1#h2#hs) = merge h1 h2 # pass\<^sub>1 hs"

fun pass\<^sub>2 :: "('a::linorder) heap list \<Rightarrow> 'a heap" where
  "pass\<^sub>2 [] = Empty"
| "pass\<^sub>2 (h#hs) = merge h (pass\<^sub>2 hs)"

fun merge_pairs :: "('a::linorder)  heap list \<Rightarrow> 'a heap" where
  "merge_pairs [] = Empty"
| "merge_pairs [h] = h" 
| "merge_pairs (h1 # h2 # hs) = merge (merge h1 h2) (merge_pairs hs)"

fun del_min :: "('a::linorder) heap \<Rightarrow> 'a heap" where
  "del_min Empty = Empty"
| "del_min (Hp x hs) = pass\<^sub>2 (pass\<^sub>1 hs)"


subsection \<open>Correctness Proofs\<close>

text \<open>An optimization:\<close>

lemma pass12_merge_pairs: "pass\<^sub>2 (pass\<^sub>1 hs) = merge_pairs hs"
by (induction hs rule: merge_pairs.induct) (auto split: option.split)

declare pass12_merge_pairs[code_unfold]


subsubsection \<open>Invariants\<close>

fun pheap :: "('a :: linorder) heap \<Rightarrow> bool" where
"pheap Empty = True" |
"pheap (Hp x hs) = (\<forall>h \<in> set hs. (\<forall>y \<in> set_heap h. x \<le> y) \<and> pheap h)"

lemma pheap_merge: "pheap h1 \<Longrightarrow> pheap h2 \<Longrightarrow> pheap (merge h1 h2)"
by (induction h1 h2 rule: merge.induct) fastforce+

lemma pheap_insert: "pheap h \<Longrightarrow> pheap (insert x h)"
by (auto simp: pheap_merge)

lemma pheap_pass1: "\<forall>h \<in> set hs. pheap h \<Longrightarrow> \<forall>h \<in> set (pass\<^sub>1 hs). pheap h"
by(induction hs rule: pass\<^sub>1.induct) (auto simp: pheap_merge)

lemma pheap_pass2: "\<forall>h \<in> set hs. pheap h \<Longrightarrow> pheap (pass\<^sub>2 hs)"
by (induction hs)(auto simp: pheap_merge)

lemma pheap_del_min: "pheap h \<Longrightarrow> pheap (del_min h)"
by(induction h rule: del_min.induct) (auto intro!: pheap_pass1 pheap_pass2)


subsubsection \<open>Functional Correctness\<close>

fun mset_heap :: "'a heap \<Rightarrow>'a multiset" where
"mset_heap Empty = {#}" |
"mset_heap (Hp x hs) = {#x#} + Union_mset(mset(map mset_heap hs))"

lemma set_mset_mset_heap: "set_mset (mset_heap h) = set_heap h"
by(induction h) auto

lemma mset_heap_empty_iff: "mset_heap h = {#} \<longleftrightarrow> h = Empty"
by (cases h) auto

lemma get_min_in: "h \<noteq> Empty \<Longrightarrow> get_min h \<in> set_heap(h)"
by(induction rule: get_min.induct)(auto)

lemma get_min_min: "\<lbrakk> h \<noteq> Empty; pheap h; x \<in> set_heap(h) \<rbrakk> \<Longrightarrow> get_min h \<le> x"
by(induction h rule: get_min.induct)(auto)

lemma get_min: "\<lbrakk> pheap h;  h \<noteq> Empty \<rbrakk> \<Longrightarrow> get_min h = Min_mset (mset_heap h)"
by (metis Min_eqI finite_set_mset get_min_in get_min_min set_mset_mset_heap)

lemma mset_merge: "mset_heap (merge h1 h2) = mset_heap h1 + mset_heap h2"
by(induction h1 h2 rule: merge.induct)(auto simp: add_ac)

lemma mset_insert: "mset_heap (insert a h) = {#a#} + mset_heap h"
by(cases h) (auto simp add: mset_merge insert_def add_ac)

lemma mset_merge_pairs: "mset_heap (merge_pairs hs) = Union_mset(image_mset mset_heap(mset hs))"
by(induction hs rule: merge_pairs.induct)(auto simp: mset_merge)

lemma mset_del_min: "h \<noteq> Empty \<Longrightarrow>
  mset_heap (del_min h) = mset_heap h - {#get_min h#}"
by(induction h rule: del_min.induct) (auto simp: pass12_merge_pairs mset_merge_pairs)


text \<open>Last step: prove all axioms of the priority queue specification:\<close>

interpretation pairing: Priority_Queue_Merge
where empty = Empty and is_empty = "\<lambda>h. h = Empty"
and merge = merge and insert = insert
and del_min = del_min and get_min = get_min
and invar = pheap and mset = mset_heap
proof(standard, goal_cases)
  case 1 show ?case by simp
next
  case (2 q) show ?case by (cases q) auto
next
  case 3 show ?case by(simp add: mset_insert mset_merge)
next
  case 4 thus ?case by(simp add: mset_del_min mset_heap_empty_iff)
next
  case 5 thus ?case using get_min mset_heap.simps(1) by blast
next
  case 6 thus ?case by(simp)
next
  case 7 thus ?case by(rule pheap_insert)
next
  case 8 thus ?case by (simp add: pheap_del_min)
next
  case 9 thus ?case by (simp add: mset_merge)
next
  case 10 thus ?case by (simp add: pheap_merge)
qed

end
