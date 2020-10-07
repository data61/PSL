(*
  File: Interval_Tree.thy
  Author: Bohua Zhan
*)

section \<open>Interval tree\<close>

theory Interval_Tree
  imports Lists_Ex Interval
begin

text \<open>
  Functional version of interval tree. This is an augmented data
  structure on top of regular binary search trees (see BST.thy).
  See \cite[Section 14.3]{cormen2009introduction} for a reference.
\<close>

subsection \<open>Definition of an interval tree\<close>

datatype interval_tree =
   Tip
 | Node (lsub: interval_tree) (val: "nat idx_interval") (tmax: nat) (rsub: interval_tree)
where
  "tmax Tip = 0"

setup \<open>add_resolve_prfstep @{thm interval_tree.distinct(1)}\<close>
setup \<open>fold add_rewrite_rule @{thms interval_tree.sel}\<close>
setup \<open>add_forward_prfstep @{thm interval_tree.collapse}\<close>
setup \<open>add_var_induct_rule @{thm interval_tree.induct}\<close>

subsection \<open>Inorder traversal, and set of elements of a tree\<close>

fun in_traverse :: "interval_tree \<Rightarrow> nat idx_interval list" where
  "in_traverse Tip = []"
| "in_traverse (Node l it m r) = in_traverse l @ it # in_traverse r"
setup \<open>fold add_rewrite_rule @{thms in_traverse.simps}\<close>

fun tree_set :: "interval_tree \<Rightarrow> nat idx_interval set" where
  "tree_set Tip = {}"
| "tree_set (Node l it m r) = {it} \<union> tree_set l \<union> tree_set r"
setup \<open>fold add_rewrite_rule @{thms tree_set.simps}\<close>

fun tree_sorted :: "interval_tree \<Rightarrow> bool" where
  "tree_sorted Tip = True"
| "tree_sorted (Node l it m r) = ((\<forall>x\<in>tree_set l. x < it) \<and> (\<forall>x\<in>tree_set r. it < x)
                                   \<and> tree_sorted l \<and> tree_sorted r)"
setup \<open>fold add_rewrite_rule @{thms tree_sorted.simps}\<close>

lemma tree_sorted_lr [forward]:
  "tree_sorted (Node l it m r) \<Longrightarrow> tree_sorted l \<and> tree_sorted r" by auto2

lemma tree_sortedD1 [forward]:
  "tree_sorted (Node l it m r) \<Longrightarrow> x \<in> tree_set l \<Longrightarrow> x < it" by auto2

lemma tree_sortedD2 [forward]:
  "tree_sorted (Node l it m r) \<Longrightarrow> x \<in> tree_set r \<Longrightarrow> x > it" by auto2

lemma inorder_preserve_set [rewrite]:
  "tree_set t = set (in_traverse t)"
@proof @induct t @qed

lemma inorder_sorted [rewrite]:
  "tree_sorted t \<longleftrightarrow> strict_sorted (in_traverse t)"
@proof @induct t @qed

text \<open>Use definition in terms of in\_traverse from now on.\<close>
setup \<open>fold del_prfstep_thm (@{thms tree_set.simps} @ @{thms tree_sorted.simps})\<close>

subsection \<open>Invariant on the maximum\<close>

definition max3 :: "nat idx_interval \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where [rewrite]:
  "max3 it b c = max (high (int it)) (max b c)"

fun tree_max_inv :: "interval_tree \<Rightarrow> bool" where
  "tree_max_inv Tip = True"
| "tree_max_inv (Node l it m r) \<longleftrightarrow> (tree_max_inv l \<and> tree_max_inv r \<and> m = max3 it (tmax l) (tmax r))"
setup \<open>fold add_rewrite_rule @{thms tree_max_inv.simps}\<close>

lemma tree_max_is_max [resolve]:
  "tree_max_inv t \<Longrightarrow> it \<in> tree_set t \<Longrightarrow> high (int it) \<le> tmax t"
@proof @induct t @qed

lemma tmax_exists [backward]:
  "tree_max_inv t \<Longrightarrow> t \<noteq> Tip \<Longrightarrow> \<exists>p\<in>tree_set t. high (int p) = tmax t"
@proof @induct t @with
  @subgoal "t = Node l it m r"
    @case "l = Tip" @with @case "r = Tip" @end
    @case "r = Tip"
  @endgoal @end
@qed

text \<open>For insertion\<close>
lemma max3_insert [rewrite]: "max3 it 0 0 = high (int it)" by auto2

setup \<open>del_prfstep_thm @{thm max3_def}\<close>

subsection \<open>Condition on the values\<close>

definition tree_interval_inv :: "interval_tree \<Rightarrow> bool" where [rewrite]:
  "tree_interval_inv t \<longleftrightarrow> (\<forall>p\<in>tree_set t. is_interval (int p))"

definition is_interval_tree :: "interval_tree \<Rightarrow> bool" where [rewrite]:
  "is_interval_tree t \<longleftrightarrow> (tree_sorted t \<and> tree_max_inv t \<and> tree_interval_inv t)"

lemma is_interval_tree_lr [forward]:
  "is_interval_tree (Node l x m r) \<Longrightarrow> is_interval_tree l \<and> is_interval_tree r" by auto2

subsection \<open>Insertion on trees\<close>

fun insert :: "nat idx_interval \<Rightarrow> interval_tree \<Rightarrow> interval_tree" where
  "insert x Tip = Node Tip x (high (int x)) Tip"
| "insert x (Node l y m r) =
    (if x = y then Node l y m r
     else if x < y then
       let l' = insert x l in
           Node l' y (max3 y (tmax l') (tmax r)) r
     else
       let r' = insert x r in
           Node l y (max3 y (tmax l) (tmax r')) r')"
setup \<open>fold add_rewrite_rule @{thms insert.simps}\<close>

lemma tree_insert_in_traverse [rewrite]:
  "tree_sorted t \<Longrightarrow> in_traverse (insert x t) = ordered_insert x (in_traverse t)"
@proof @induct t @qed

lemma tree_insert_max_inv [forward]:
  "tree_max_inv t \<Longrightarrow> tree_max_inv (insert x t)"
@proof @induct t @qed

text \<open>Correctness of insertion.\<close>
theorem tree_insert_all_inv [forward]:
  "is_interval_tree t \<Longrightarrow> is_interval (int it) \<Longrightarrow> is_interval_tree (insert it t)" by auto2

theorem tree_insert_on_set [rewrite]:
  "tree_sorted t \<Longrightarrow> tree_set (insert it t) = {it} \<union> tree_set t" by auto2

subsection \<open>Deletion on trees\<close>

fun del_min :: "interval_tree \<Rightarrow> nat idx_interval \<times> interval_tree" where
  "del_min Tip = undefined"
| "del_min (Node lt v m rt) =
   (if lt = Tip then (v, rt) else
    let lt' = snd (del_min lt) in
    (fst (del_min lt), Node lt' v (max3 v (tmax lt') (tmax rt)) rt))"
setup \<open>add_rewrite_rule @{thm del_min.simps(2)}\<close>
setup \<open>register_wellform_data ("del_min t", ["t \<noteq> Tip"])\<close>

lemma delete_min_del_hd:
  "t \<noteq> Tip \<Longrightarrow> fst (del_min t) # in_traverse (snd (del_min t)) = in_traverse t"
@proof @induct t @qed
setup \<open>add_forward_prfstep_cond @{thm delete_min_del_hd} [with_term "in_traverse (snd (del_min ?t))"]\<close>

lemma delete_min_max_inv [forward_arg]:
  "tree_max_inv t \<Longrightarrow> t \<noteq> Tip \<Longrightarrow> tree_max_inv (snd (del_min t))"
@proof @induct t @qed

lemma delete_min_on_set:
  "t \<noteq> Tip \<Longrightarrow> {fst (del_min t)} \<union> tree_set (snd (del_min t)) = tree_set t" by auto2
setup \<open>add_forward_prfstep_cond @{thm delete_min_on_set} [with_term "tree_set (snd (del_min ?t))"]\<close>

lemma delete_min_interval_inv [forward_arg]:
  "tree_interval_inv t \<Longrightarrow> t \<noteq> Tip \<Longrightarrow> tree_interval_inv (snd (del_min t))" by auto2

lemma delete_min_all_inv [forward_arg]:
  "is_interval_tree t \<Longrightarrow> t \<noteq> Tip \<Longrightarrow> is_interval_tree (snd (del_min t))" by auto2

fun delete_elt_tree :: "interval_tree \<Rightarrow> interval_tree" where
  "delete_elt_tree Tip = undefined"
| "delete_elt_tree (Node lt x m rt) =
    (if lt = Tip then rt else if rt = Tip then lt else
     let x' = fst (del_min rt);
         rt' = snd (del_min rt);
         m' = max3 x' (tmax lt) (tmax rt') in
       Node lt (fst (del_min rt)) m' rt')"
setup \<open>add_rewrite_rule @{thm delete_elt_tree.simps(2)}\<close>

lemma delete_elt_in_traverse [rewrite]:
  "in_traverse (delete_elt_tree (Node lt x m rt)) = in_traverse lt @ in_traverse rt" by auto2

lemma delete_elt_max_inv [forward_arg]:
  "tree_max_inv t \<Longrightarrow> t \<noteq> Tip \<Longrightarrow> tree_max_inv (delete_elt_tree t)" by auto2

lemma delete_elt_on_set [rewrite]:
  "t \<noteq> Tip \<Longrightarrow> tree_set (delete_elt_tree (Node lt x m rt)) = tree_set lt \<union> tree_set rt" by auto2

lemma delete_elt_interval_inv [forward_arg]:
  "tree_interval_inv t \<Longrightarrow> t \<noteq> Tip \<Longrightarrow> tree_interval_inv (delete_elt_tree t)" by auto2

lemma delete_elt_all_inv [forward_arg]:
  "is_interval_tree t \<Longrightarrow> t \<noteq> Tip \<Longrightarrow> is_interval_tree (delete_elt_tree t)" by auto2

fun delete :: "nat idx_interval \<Rightarrow> interval_tree \<Rightarrow> interval_tree" where
  "delete x Tip = Tip"
| "delete x (Node l y m r) =
    (if x = y then delete_elt_tree (Node l y m r)
     else if x < y then
       let l' = delete x l;
           m' = max3 y (tmax l') (tmax r) in Node l' y m' r
     else
       let r' = delete x r;
           m' = max3 y (tmax l) (tmax r') in Node l y m' r')"
setup \<open>fold add_rewrite_rule @{thms delete.simps}\<close>

lemma tree_delete_in_traverse [rewrite]:
  "tree_sorted t \<Longrightarrow> in_traverse (delete x t) = remove_elt_list x (in_traverse t)"
@proof @induct t @qed

lemma tree_delete_max_inv [forward]:
  "tree_max_inv t \<Longrightarrow> tree_max_inv (delete x t)"
@proof @induct t @qed

text \<open>Correctness of deletion.\<close>
theorem tree_delete_all_inv [forward]:
  "is_interval_tree t \<Longrightarrow> is_interval_tree (delete x t)"
@proof @have "tree_set (delete x t) \<subseteq> tree_set t" @qed

theorem tree_delete_on_set [rewrite]:
  "tree_sorted t \<Longrightarrow> tree_set (delete x t) = tree_set t - {x}" by auto2

subsection \<open>Search on interval trees\<close>

fun search :: "interval_tree \<Rightarrow> nat interval \<Rightarrow> bool" where
  "search Tip x = False"
| "search (Node l y m r) x =
   (if is_overlap (int y) x then True
    else if l \<noteq> Tip \<and> tmax l \<ge> low x then search l x
    else search r x)"
setup \<open>fold add_rewrite_rule @{thms search.simps}\<close>

text \<open>Correctness of search\<close>
theorem search_correct [rewrite]:
  "is_interval_tree t \<Longrightarrow> is_interval x \<Longrightarrow> search t x \<longleftrightarrow> has_overlap (tree_set t) x"
@proof
  @induct t @with
    @subgoal "t = Node l y m r"
      @let "t = Node l y m r"
      @case "is_overlap (int y) x"
      @case "l \<noteq> Tip \<and> tmax l \<ge> low x" @with
        @obtain "p\<in>tree_set l" where "high (int p) = tmax l"
        @case "is_overlap (int p) x"
      @end
      @case "l = Tip"
    @endgoal
  @end
@qed

end
