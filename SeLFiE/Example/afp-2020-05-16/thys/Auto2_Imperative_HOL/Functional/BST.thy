(*
  File: BST.thy
  Author: Bohua Zhan
*)

section \<open>Binary search tree\<close>

theory BST
  imports Lists_Ex
begin

text \<open>
  Verification of functional programs on binary search trees. For
  basic technique, see comments in Lists\_Ex.thy.
\<close>

subsection \<open>Definition and setup for trees\<close>

datatype ('a, 'b) tree =
    Tip | Node (lsub: "('a, 'b) tree") (key: 'a) (nval: 'b) (rsub: "('a, 'b) tree")

setup \<open>add_resolve_prfstep @{thm tree.distinct(1)}\<close>
setup \<open>fold add_rewrite_rule @{thms tree.sel}\<close>
setup \<open>add_forward_prfstep @{thm tree.collapse}\<close>
setup \<open>add_var_induct_rule @{thm tree.induct}\<close>

subsection \<open>Inorder traversal, and set of elements of a tree\<close>

fun in_traverse :: "('a, 'b) tree \<Rightarrow> 'a list" where
  "in_traverse Tip = []"
| "in_traverse (Node l k v r) = in_traverse l @ k # in_traverse r"
setup \<open>fold add_rewrite_rule @{thms in_traverse.simps}\<close>

fun tree_set :: "('a, 'b) tree \<Rightarrow> 'a set" where
  "tree_set Tip = {}"
| "tree_set (Node l k v r) = {k} \<union> tree_set l \<union> tree_set r"
setup \<open>fold add_rewrite_rule @{thms tree_set.simps}\<close>

fun in_traverse_pairs :: "('a, 'b) tree \<Rightarrow> ('a \<times> 'b) list" where
  "in_traverse_pairs Tip = []"
| "in_traverse_pairs (Node l k v r) = in_traverse_pairs l @ (k, v) # in_traverse_pairs r"
setup \<open>fold add_rewrite_rule @{thms in_traverse_pairs.simps}\<close>

lemma in_traverse_fst [rewrite]:
  "map fst (in_traverse_pairs t) = in_traverse t"
@proof @induct t @qed

definition tree_map :: "('a, 'b) tree \<Rightarrow> ('a, 'b) map" where
  "tree_map t = map_of_alist (in_traverse_pairs t)"
setup \<open>add_rewrite_rule @{thm tree_map_def}\<close>

subsection \<open>Sortedness on trees\<close>

fun tree_sorted :: "('a::linorder, 'b) tree \<Rightarrow> bool" where
  "tree_sorted Tip = True"
| "tree_sorted (Node l k v r) = ((\<forall>x\<in>tree_set l. x < k) \<and> (\<forall>x\<in>tree_set r. k < x)
                              \<and> tree_sorted l \<and> tree_sorted r)"
setup \<open>fold add_rewrite_rule @{thms tree_sorted.simps}\<close>

lemma tree_sorted_lr [forward]:
  "tree_sorted (Node l k v r) \<Longrightarrow> tree_sorted l \<and> tree_sorted r" by auto2

lemma inorder_preserve_set [rewrite]:
  "tree_set t = set (in_traverse t)"
@proof @induct t @qed

lemma inorder_pairs_sorted [rewrite]:
  "tree_sorted t \<longleftrightarrow> strict_sorted (map fst (in_traverse_pairs t))"
@proof @induct t @qed

text \<open>Use definition in terms of in\_traverse from now on.\<close>
setup \<open>fold del_prfstep_thm (@{thms tree_set.simps} @ @{thms tree_sorted.simps})\<close>

subsection \<open>Rotation on trees\<close>

definition rotateL :: "('a, 'b) tree \<Rightarrow> ('a, 'b) tree" where [rewrite]:
  "rotateL t = (if t = Tip then t else if rsub t = Tip then t else
    (let rt = rsub t in
     Node (Node (lsub t) (key t) (nval t) (lsub rt)) (key rt) (nval rt) (rsub rt)))"

definition rotateR :: "('a, 'b) tree \<Rightarrow> ('a, 'b) tree" where [rewrite]:
  "rotateR t = (if t = Tip then t else if lsub t = Tip then t else
    (let lt = lsub t in
     Node (lsub lt) (key lt) (nval lt) (Node (rsub lt) (key t) (nval t) (rsub t))))"

lemma rotateL_in_trav [rewrite]: "in_traverse (rotateL t) = in_traverse t" by auto2
lemma rotateR_in_trav [rewrite]: "in_traverse (rotateR t) = in_traverse t" by auto2

lemma rotateL_sorted [forward]: "tree_sorted t \<Longrightarrow> tree_sorted (rotateL t)" by auto2
lemma rotateR_sorted [forward]: "tree_sorted t \<Longrightarrow> tree_sorted (rotateR t)" by auto2

subsection \<open>Insertion on trees\<close>

fun tree_insert :: "'a::ord \<Rightarrow> 'b \<Rightarrow> ('a, 'b) tree \<Rightarrow> ('a, 'b) tree" where
  "tree_insert x v Tip = Node Tip x v Tip"
| "tree_insert x v (Node l y w r) =
    (if x = y then Node l x v r
     else if x < y then Node (tree_insert x v l) y w r
     else Node l y w (tree_insert x v r))"
setup \<open>fold add_rewrite_rule @{thms tree_insert.simps}\<close>
 
lemma insert_in_traverse_pairs [rewrite]:
  "tree_sorted t \<Longrightarrow> in_traverse_pairs (tree_insert x v t) = ordered_insert_pairs x v (in_traverse_pairs t)"
@proof @induct t @qed

text \<open>Correctness results for insertion.\<close>
theorem insert_sorted [forward]:
  "tree_sorted t \<Longrightarrow> tree_sorted (tree_insert x v t)" by auto2

theorem insert_on_map:
  "tree_sorted t \<Longrightarrow> tree_map (tree_insert x v t) = (tree_map t) {x \<rightarrow> v}" by auto2

subsection \<open>Deletion on trees\<close>

fun del_min :: "('a, 'b) tree \<Rightarrow> ('a \<times> 'b) \<times> ('a, 'b) tree" where
  "del_min Tip = undefined"
| "del_min (Node lt x v rt) =
   (if lt = Tip then ((x, v), rt) else
    (fst (del_min lt), Node (snd (del_min lt)) x v rt))"
setup \<open>add_rewrite_rule @{thm del_min.simps(2)}\<close>

lemma delete_min_del_hd_pairs [rewrite]:
  "t \<noteq> Tip \<Longrightarrow> fst (del_min t) # in_traverse_pairs (snd (del_min t)) = in_traverse_pairs t"
@proof @induct t @qed

fun delete_elt_tree :: "('a, 'b) tree \<Rightarrow> ('a, 'b) tree" where
  "delete_elt_tree Tip = undefined"
| "delete_elt_tree (Node lt x v rt) =
    (if lt = Tip then rt else if rt = Tip then lt else
     Node lt (fst (fst (del_min rt))) (snd (fst (del_min rt))) (snd (del_min rt)))"
setup \<open>add_rewrite_rule @{thm delete_elt_tree.simps(2)}\<close>

lemma delete_elt_in_traverse_pairs [rewrite]:
  "in_traverse_pairs (delete_elt_tree (Node lt x v rt)) = in_traverse_pairs lt @ in_traverse_pairs rt" by auto2

fun tree_delete :: "'a::ord \<Rightarrow> ('a, 'b) tree \<Rightarrow> ('a, 'b) tree" where
  "tree_delete x Tip = Tip"
| "tree_delete x (Node l y w r) =
    (if x = y then delete_elt_tree (Node l y w r)
     else if x < y then Node (tree_delete x l) y w r
     else Node l y w (tree_delete x r))"
setup \<open>fold add_rewrite_rule @{thms tree_delete.simps}\<close>

lemma tree_delete_in_traverse_pairs [rewrite]:
  "tree_sorted t \<Longrightarrow> in_traverse_pairs (tree_delete x t) = remove_elt_pairs x (in_traverse_pairs t)"
@proof @induct t @qed

text \<open>Correctness results for deletion.\<close>
theorem tree_delete_sorted [forward]:
  "tree_sorted t \<Longrightarrow> tree_sorted (tree_delete x t)" by auto2

theorem tree_delete_map [rewrite]:
  "tree_sorted t \<Longrightarrow> tree_map (tree_delete x t) = delete_map x (tree_map t)" by auto2

subsection \<open>Search on sorted trees\<close>

fun tree_search :: "('a::ord, 'b) tree \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "tree_search Tip x = None"
| "tree_search (Node l k v r) x =
  (if x = k then Some v
   else if x < k then tree_search l x
   else tree_search r x)"
setup \<open>fold add_rewrite_rule @{thms tree_search.simps}\<close>

text \<open>Correctness of search.\<close>
theorem tree_search_correct [rewrite]:
  "tree_sorted t \<Longrightarrow> tree_search t x = (tree_map t)\<langle>x\<rangle>"
@proof @induct t @qed

end
