theory Skew_Heap
imports
  "~~/src/HOL/Library/Tree_Multiset" "../../PSL"
begin

section "Skew Heap"

text{* Skew heaps~\cite{SleatorT-SIAM86} are possibly the simplest functional
priority queues that have logarithmic (albeit amortized) complexity.

The implementation below should be generalized to separate the elements from
their priorities. *}

type_synonym 'a heap = "'a tree"

fun heap :: "'a::linorder heap \<Rightarrow> bool" where
"heap Leaf = True" |
"heap (Node l m r) =
  (heap l \<and> heap r \<and> (\<forall>x \<in> set_tree l \<union> set_tree r. m \<le> x))"


subsection "Get Minimum"

fun get_min :: "'a::linorder heap \<Rightarrow> 'a" where
"get_min(Node l m r) = m"

lemma get_min_in:
  "h \<noteq> Leaf \<Longrightarrow> get_min h \<in> set_tree h"
by(auto simp add: neq_Leaf_iff)

lemma get_min_min:
  "\<lbrakk> heap h; x \<in> set_tree h \<rbrakk> \<Longrightarrow> get_min h \<le> x"
by(cases h)(auto)


subsection "Meld"

function meld :: "('a::linorder) heap \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"meld Leaf h = h" |
"meld h Leaf = h" |
"meld (Node l1 a1 r1) (Node l2 a2 r2) =
   (if a1 \<le> a2 then Node (meld (Node l2 a2 r2) r1) a1 l1
    else Node (meld (Node l1 a1 r1) r2) a2 l2)" 
by pat_completeness auto
termination
by (relation "measure (\<lambda>(x, y). size x + size y)") auto

lemma meld_code: "meld h1 h2 =
  (case h1 of
   Leaf \<Rightarrow> h2 |
   Node l1 a1 r1 \<Rightarrow> (case h2 of
     Leaf \<Rightarrow> h1 |
     Node l2 a2 r2 \<Rightarrow> 
       (if a1 \<le> a2
        then Node (meld h2 r1) a1 l1
        else Node (meld h1 r2) a2 l2)))"
by(auto split: tree.split)

text{* An alternative version that always walks to the Leaf of both heaps: *}
function meld2 :: "('a::linorder) heap \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"meld2 Leaf Leaf = Leaf" |
"meld2 Leaf (Node l2 a2 r2) = Node (meld2 r2 Leaf) a2 l2" |
"meld2 (Node l1 a1 r1) Leaf = Node (meld2 r1 Leaf) a1 l1" |
"meld2 (Node l1 a1 r1) (Node l2 a2 r2) =
   (if a1 \<le> a2
    then Node (meld2 (Node l2 a2 r2) r1) a1 l1
    else Node (meld2 (Node l1 a1 r1) r2) a2 l2)"
by pat_completeness auto
termination
by (relation "measure (\<lambda>(x, y). size x + size y)") auto

lemma size_meld[simp]: "size(meld t1 t2) = size t1 + size t2"
by(induction t1 t2 rule: meld.induct) auto

lemma size_meld2[simp]: "size(meld2 t1 t2) = size t1 + size t2"
by(induction t1 t2 rule: meld2.induct) auto

lemma mset_meld: "mset_tree (meld h1 h2) = mset_tree h1 + mset_tree h2"
by (induction h1 h2 rule: meld.induct) (auto simp add: ac_simps)

lemma set_meld: "set_tree (meld h1 h2) = set_tree h1 \<union> set_tree h2"
by (metis mset_meld set_mset_tree set_mset_union)

lemma heap_meld:
  "heap h1 \<Longrightarrow> heap h2 \<Longrightarrow> heap (meld h1 h2)"
by (induction h1 h2 rule: meld.induct)(auto simp: ball_Un set_meld)


subsection "Insert"

definition insert :: "'a::linorder \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"insert a t = meld (Node Leaf a Leaf) t"

hide_const (open) Skew_Heap.insert

lemma heap_insert: "heap h \<Longrightarrow> heap (Skew_Heap.insert a h)"
by (simp add: insert_def heap_meld)

lemma mset_insert: "mset_tree (Skew_Heap.insert a h) = {#a#} + mset_tree h"
by (auto simp: mset_meld insert_def)


subsection "Delete minimum"

fun del_min :: "'a::linorder heap \<Rightarrow> 'a heap" where
"del_min Leaf = Leaf" |
"del_min (Node l m r) = meld l r"

lemma heap_del_min: "heap h \<Longrightarrow> heap (del_min h)"
by (cases h) (auto simp: heap_meld)

lemma mset_del_min: "mset_tree (del_min h) = mset_tree h - {# get_min h #}"
  by (cases h) (auto simp: mset_meld ac_simps)
ML{* Isabelle_System.bash_output 
"less ~/Dokumente/PSL_PaMpeR/PSL/PaMpeR/FE_Interface.ML";
 Bash.process;

Bash_Syntax.string;

Isabelle_System.bash_output 
"less ~/.isabelle/Database";

*}
end
