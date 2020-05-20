(*
  File: BST_Impl.thy
  Author: Bohua Zhan
*)

section \<open>Implementation of binary search tree\<close>

theory BST_Impl
  imports SepAuto "../Functional/BST"
begin

text \<open>Imperative version of binary search trees.\<close>

subsection \<open>Tree nodes\<close>

datatype ('a, 'b) node =
  Node (lsub: "('a, 'b) node ref option") (key: 'a) (val: 'b) (rsub: "('a, 'b) node ref option")
setup \<open>fold add_rewrite_rule @{thms node.sel}\<close>

fun node_encode :: "('a::heap, 'b::heap) node \<Rightarrow> nat" where
  "node_encode (Node l k v r) = to_nat (l, k, v, r)"

instance node :: (heap, heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "node_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

fun btree :: "('a::heap, 'b::heap) tree \<Rightarrow> ('a, 'b) node ref option \<Rightarrow> assn" where
  "btree Tip p = \<up>(p = None)"
| "btree (tree.Node lt k v rt) (Some p) = (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp k v rp * btree lt lp * btree rt rp)"
| "btree (tree.Node lt k v rt) None = false"
setup \<open>fold add_rewrite_ent_rule @{thms btree.simps}\<close>

lemma btree_Tip [forward_ent]: "btree Tip p \<Longrightarrow>\<^sub>A \<up>(p = None)" by auto2

lemma btree_Node [forward_ent]:
  "btree (tree.Node lt k v rt) p \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Alp rp. the p \<mapsto>\<^sub>r Node lp k v rp * btree lt lp * btree rt rp * \<up>(p \<noteq> None))"
@proof @case "p = None" @qed

lemma btree_none: "emp \<Longrightarrow>\<^sub>A btree tree.Tip None" by auto2

lemma btree_constr_ent:
  "p \<mapsto>\<^sub>r Node lp k v rp * btree lt lp * btree rt rp \<Longrightarrow>\<^sub>A btree (tree.Node lt k v rt) (Some p)" by auto2

setup \<open>fold add_entail_matcher [@{thm btree_none}, @{thm btree_constr_ent}]\<close>
setup \<open>fold del_prfstep_thm @{thms btree.simps}\<close>

type_synonym ('a, 'b) btree = "('a, 'b) node ref option"

subsection \<open>Operations\<close>

subsubsection \<open>Basic operations\<close>

definition tree_empty :: "('a, 'b) btree Heap" where
  "tree_empty = return None"

lemma tree_empty_rule [hoare_triple]:
  "<emp> tree_empty <btree Tip>" by auto2

definition tree_is_empty :: "('a, 'b) btree \<Rightarrow> bool Heap" where
  "tree_is_empty b = return (b = None)"

lemma tree_is_empty_rule:
  "<btree t b> tree_is_empty b <\<lambda>r. btree t b * \<up>(r \<longleftrightarrow> t = Tip)>" by auto2

definition btree_constr ::
  "('a::heap, 'b::heap) btree \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_constr lp k v rp = do { p \<leftarrow> ref (Node lp k v rp); return (Some p) }"

lemma btree_constr_rule [hoare_triple]:
  "<btree lt lp * btree rt rp> btree_constr lp k v rp <btree (tree.Node lt k v rt)>" by auto2

subsubsection \<open>Insertion\<close>

partial_function (heap) btree_insert ::
  "'a::{heap,linorder} \<Rightarrow> 'b::heap \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_insert k v b = (case b of
     None \<Rightarrow> btree_constr None k v None
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if k = key t then do {
         p := Node (lsub t) k v (rsub t);
         return (Some p) }
       else if k < key t then do {
         q \<leftarrow> btree_insert k v (lsub t);
         p := Node q (key t) (val t) (rsub t);
         return (Some p) }
       else do {
         q \<leftarrow> btree_insert k v (rsub t);
         p := Node (lsub t) (key t) (val t) q;
         return (Some p)}) })"

lemma btree_insert_to_fun [hoare_triple]:
  "<btree t b>
   btree_insert k v b
   <btree (tree_insert k v t)>"
@proof @induct t arbitrary b @qed

subsubsection \<open>Deletion\<close>

partial_function (heap) btree_del_min :: "('a::heap, 'b::heap) btree \<Rightarrow> (('a \<times> 'b) \<times> ('a, 'b) btree) Heap" where
  "btree_del_min b = (case b of
     None \<Rightarrow> raise STR ''del_min: empty tree''
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if lsub t = None then
         return ((key t, val t), rsub t)
       else do {
         r \<leftarrow> btree_del_min (lsub t);
         p := Node (snd r) (key t) (val t) (rsub t);
         return (fst r, Some p) }) })"

lemma btree_del_min_to_fun [hoare_triple]:
  "<btree t b * \<up>(b \<noteq> None)>
   btree_del_min b
   <\<lambda>(r,p). btree (snd (del_min t)) p * \<up>(r = fst (del_min t))>\<^sub>t"
@proof @induct t arbitrary b @qed

definition btree_del_elt :: "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_del_elt b = (case b of
     None \<Rightarrow> raise STR ''del_elt: empty tree''
   | Some p \<Rightarrow> do {
       t \<leftarrow> !p;
       (if lsub t = None then return (rsub t)
        else if rsub t = None then return (lsub t)
        else do {
          r \<leftarrow> btree_del_min (rsub t);
          p := Node (lsub t) (fst (fst r)) (snd (fst r)) (snd r);
          return (Some p) }) })"

lemma btree_del_elt_to_fun [hoare_triple]:
  "<btree (tree.Node lt x v rt) b>
   btree_del_elt b
   <btree (delete_elt_tree (tree.Node lt x v rt))>\<^sub>t" by auto2

partial_function (heap) btree_delete ::
  "'a::{heap,linorder} \<Rightarrow> ('a, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_delete x b = (case b of
     None \<Rightarrow> return None
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if x = key t then do {
         r \<leftarrow> btree_del_elt b;
         return r }
       else if x < key t then do {
         q \<leftarrow> btree_delete x (lsub t);
         p := Node q (key t) (val t) (rsub t);
         return (Some p) }
       else do {
         q \<leftarrow> btree_delete x (rsub t);
         p := Node (lsub t) (key t) (val t) q;
         return (Some p)}) })"

lemma btree_delete_to_fun [hoare_triple]:
  "<btree t b>
   btree_delete x b
   <btree (tree_delete x t)>\<^sub>t"
@proof @induct t arbitrary b @qed

subsubsection \<open>Search\<close>

partial_function (heap) btree_search ::
  "'a::{heap,linorder} \<Rightarrow> ('a, 'b::heap) btree \<Rightarrow> 'b option Heap" where
  "btree_search x b = (case b of
     None \<Rightarrow> return None
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if x = key t then return (Some (val t))
       else if x < key t then btree_search x (lsub t)
       else btree_search x (rsub t)) })"

lemma btree_search_correct [hoare_triple]:
  "<btree t b * \<up>(tree_sorted t)>
   btree_search x b
   <\<lambda>r. btree t b * \<up>(r = tree_search t x)>"
@proof @induct t arbitrary b @qed

subsection \<open>Outer interface\<close>

text \<open>Express Hoare triples for operations on binary search tree in terms of
  the mapping represented by the tree.\<close>
definition btree_map :: "('a, 'b) map \<Rightarrow> ('a::{heap,linorder}, 'b::heap) node ref option \<Rightarrow> assn" where
  "btree_map M p = (\<exists>\<^sub>At. btree t p * \<up>(tree_sorted t) * \<up>(M = tree_map t))"
setup \<open>add_rewrite_ent_rule @{thm btree_map_def}\<close>

theorem btree_empty_rule_map [hoare_triple]:
  "<emp> tree_empty <btree_map empty_map>" by auto2

theorem btree_insert_rule_map [hoare_triple]:
  "<btree_map M b> btree_insert k v b <btree_map (M {k \<rightarrow> v})>" by auto2

theorem btree_delete_rule_map [hoare_triple]:
  "<btree_map M b> btree_delete x b <btree_map (delete_map x M)>\<^sub>t" by auto2

theorem btree_search_rule_map [hoare_triple]:
  "<btree_map M b> btree_search x b <\<lambda>r. btree_map M b * \<up>(r = M\<langle>x\<rangle>)>" by auto2

end
