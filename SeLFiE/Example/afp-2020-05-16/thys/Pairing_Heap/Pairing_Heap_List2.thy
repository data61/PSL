(* Author: Tobias Nipkow *)

section \<open>Pairing Heap According to Oksaki (Modified)\<close>

theory Pairing_Heap_List2
imports
  "HOL-Library.Multiset"
  "HOL-Data_Structures.Priority_Queue_Specs"
begin

subsection \<open>Definitions\<close>

text \<open>This version of pairing heaps is a modified version
of the one by Okasaki \cite{Okasaki} that avoids structural invariants.\<close>

datatype 'a hp = Hp 'a (hps: "'a hp list")

type_synonym 'a heap = "'a hp option"

hide_const (open) insert

fun get_min  :: "'a heap \<Rightarrow> 'a" where
"get_min (Some(Hp x _)) = x"


fun link :: "('a::linorder) hp \<Rightarrow> 'a hp \<Rightarrow> 'a hp" where
"link (Hp x lx) (Hp y ly) = 
    (if x < y then Hp x (Hp y ly # lx) else Hp y (Hp x lx # ly))"

fun merge :: "('a::linorder) heap \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"merge h None = h" |
"merge None h = h" |
"merge (Some h1) (Some h2) = Some(link h1 h2)"

lemma merge_None[simp]: "merge None h = h"
by(cases h)auto

fun insert :: "('a::linorder) \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"insert x None = Some(Hp x [])" |
"insert x (Some h) = Some(link (Hp x []) h)"

fun pass\<^sub>1 :: "('a::linorder) hp list \<Rightarrow> 'a hp list" where
  "pass\<^sub>1 [] = []"
| "pass\<^sub>1 [h] = [h]" 
| "pass\<^sub>1 (h1#h2#hs) = link h1 h2 # pass\<^sub>1 hs"

fun pass\<^sub>2 :: "('a::linorder) hp list \<Rightarrow> 'a heap" where
  "pass\<^sub>2 [] = None"
| "pass\<^sub>2 (h#hs) = Some(case pass\<^sub>2 hs of None \<Rightarrow> h | Some h' \<Rightarrow> link h h')"

fun merge_pairs :: "('a::linorder) hp list \<Rightarrow> 'a heap" where
  "merge_pairs [] = None"
| "merge_pairs [h] = Some h" 
| "merge_pairs (h1 # h2 # hs) =
  Some(let h12 = link h1 h2 in case merge_pairs hs of None \<Rightarrow> h12 | Some h \<Rightarrow> link h12 h)"

fun del_min :: "('a::linorder) heap \<Rightarrow> 'a heap" where
  "del_min None = None"
| "del_min (Some(Hp x hs)) = pass\<^sub>2 (pass\<^sub>1 hs)"


subsection \<open>Correctness Proofs\<close>

text \<open>An optimization:\<close>

lemma pass12_merge_pairs: "pass\<^sub>2 (pass\<^sub>1 hs) = merge_pairs hs"
by (induction hs rule: merge_pairs.induct) (auto split: option.split)

declare pass12_merge_pairs[code_unfold]


subsubsection \<open>Invariants\<close>

fun php :: "('a::linorder) hp \<Rightarrow> bool" where
"php (Hp x hs) = (\<forall>h \<in> set hs. (\<forall>y \<in> set_hp h. x \<le> y) \<and> php h)"

definition invar :: "('a::linorder) heap \<Rightarrow> bool" where
"invar ho = (case ho of None \<Rightarrow> True | Some h \<Rightarrow> php h)"

lemma php_link: "php h1 \<Longrightarrow> php h2 \<Longrightarrow> php (link h1 h2)"
by (induction h1 h2 rule: link.induct) fastforce+

lemma invar_merge:
  "\<lbrakk> invar h1; invar h2 \<rbrakk> \<Longrightarrow> invar (merge h1 h2)"
by (auto simp: php_link invar_def split: option.splits)

lemma invar_insert: "invar h \<Longrightarrow> invar (insert x h)"
by (auto simp: php_link invar_def split: option.splits)

lemma invar_pass1: "\<forall>h \<in> set hs. php h \<Longrightarrow> \<forall>h \<in> set (pass\<^sub>1 hs). php h"
by(induction hs rule: pass\<^sub>1.induct) (auto simp: php_link)

lemma invar_pass2: "\<forall>h \<in> set hs. php h \<Longrightarrow> invar (pass\<^sub>2 hs)"
by (induction hs)(auto simp: php_link invar_def split: option.splits)

lemma invar_Some: "invar(Some h) = php h"
by(simp add: invar_def)

lemma invar_del_min: "invar h \<Longrightarrow> invar (del_min h)"
by(induction h rule: del_min.induct)
  (auto simp: invar_Some intro!: invar_pass1 invar_pass2)


subsubsection \<open>Functional Correctness\<close>

fun mset_hp :: "'a hp \<Rightarrow>'a multiset" where
"mset_hp (Hp x hs) = {#x#} + Union_mset(mset(map mset_hp hs))"

definition mset_heap :: "'a heap \<Rightarrow>'a multiset" where
"mset_heap ho = (case ho of None \<Rightarrow> {#} | Some h \<Rightarrow> mset_hp h)"

lemma set_mset_mset_hp: "set_mset (mset_hp h) = set_hp h"
by(induction h) auto

lemma mset_hp_empty[simp]: "mset_hp hp \<noteq> {#}"
by (cases hp) auto

lemma mset_heap_Some: "mset_heap(Some hp) = mset_hp hp"
by(simp add: mset_heap_def)

lemma mset_heap_empty: "mset_heap h = {#} \<longleftrightarrow> h = None"
by (cases h) (auto simp add: mset_heap_def)

lemma get_min_in:
  "h \<noteq> None \<Longrightarrow> get_min h \<in> set_hp(the h)"
by(induction rule: get_min.induct)(auto)

lemma get_min_min: "\<lbrakk> h \<noteq> None; invar h; x \<in> set_hp(the h) \<rbrakk> \<Longrightarrow> get_min h \<le> x"
by(induction h rule: get_min.induct)(auto simp: invar_def)


lemma mset_link: "mset_hp (link h1 h2) = mset_hp h1 + mset_hp h2"
by(induction h1 h2 rule: link.induct)(auto simp: add_ac)

lemma mset_merge: "mset_heap (merge h1 h2) = mset_heap h1 + mset_heap h2"
by (induction h1 h2 rule: merge.induct)
   (auto simp add: mset_heap_def mset_link ac_simps)

lemma mset_insert: "mset_heap (insert a h) = {#a#} + mset_heap h"
by(cases h) (auto simp add: mset_link mset_heap_def insert_def)

lemma mset_merge_pairs: "mset_heap (merge_pairs hs) = Union_mset(image_mset mset_hp (mset hs))"
by(induction hs rule: merge_pairs.induct)
  (auto simp: mset_merge mset_link mset_heap_def Let_def split: option.split)

lemma mset_del_min: "h \<noteq> None \<Longrightarrow>
  mset_heap (del_min h) = mset_heap h - {#get_min h#}"
by(induction h rule: del_min.induct)
  (auto simp: mset_heap_Some pass12_merge_pairs mset_merge_pairs)


text \<open>Last step: prove all axioms of the priority queue specification:\<close>

interpretation pairing: Priority_Queue_Merge
where empty = None and is_empty = "\<lambda>h. h = None"
and merge = merge and insert = insert
and del_min = del_min and get_min = get_min
and invar = invar and mset = mset_heap
proof(standard, goal_cases)
  case 1 show ?case by(simp add: mset_heap_def)
next
  case (2 q) thus ?case by(auto simp add: mset_heap_def split: option.split)
next
  case 3 show ?case by(simp add: mset_insert mset_merge)
next
  case 4 thus ?case by(simp add: mset_del_min mset_heap_empty)
next
  case (5 q) thus ?case using get_min_in[of q]
    by(auto simp add: eq_Min_iff get_min_min mset_heap_empty mset_heap_Some set_mset_mset_hp)
next
  case 6 thus ?case by (simp add: invar_def)
next
  case 7 thus ?case by(rule invar_insert)
next
  case 8 thus ?case by (simp add: invar_del_min)
next
  case 9 thus ?case by (simp add: mset_merge)
next
  case 10 thus ?case by (simp add: invar_merge)
qed

end
