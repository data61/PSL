theory Test_Embed_Tree
imports
  Lazy_Case.Lazy_Case
  "../Preproc/Embed"
  "../Preproc/Eval_Instances"
  "HOL-Library.Tree"
begin

derive evaluate tree

text \<open>Integers are not supported out of the box, so we have to rewrite some code equations.\<close>

definition nat_diff :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nat_diff x y = (if x < y then y - x else x - y)"

lemma nat_diff_abs_int[simp]: "nat_diff x y = nat (abs (int x - int y))"
  unfolding nat_diff_def
  by auto

lemma [code]:
  "wbalanced Leaf = True"
  "wbalanced (Node l x r) = (nat_diff (size l) (size r) \<le> 1 \<and> wbalanced l \<and> wbalanced r)"
  by auto

text \<open>Sets are also unsupported, so we have to rewrite @{const set_tree} to use @{const inorder}.\<close>

lemma [code_unfold]: "(\<forall>x \<in> set_tree l. P x) \<longleftrightarrow> list_all P (inorder l)"
  by (induction l) auto

lemma [code]:
  "heap Leaf = True"
  "heap (Node l m r) = (heap l \<and> heap r \<and> (\<forall>x \<in> set_tree l. m \<le> x) \<and> (\<forall>x \<in> set_tree r. m \<le> x))"
  by auto

text \<open>@{term "(-)"} on @{typ nat} is not pattern compatible\<close>

declassify valid: wbalanced ipl preorder inorder postorder bst_wrt heap
thm valid

experiment begin

code_thms Tree_wbalanced (* FIXME bogus error message when using the non-dict-eliminated constant *)
embed (eval) test1 is Tree_wbalanced .

end

experiment begin

code_thms Tree_ipl Tree_preorder Tree_inorder Tree_postorder
embed (eval) test2 is Tree_ipl Tree_preorder Tree_inorder Tree_postorder .

end

(* FIXME auto-derive these things? *)
derive evaluate
  Orderings_ord__dict
  Orderings_preorder__dict
  Orderings_order__dict
  Orderings_linorder__dict

experiment begin

code_thms Tree_bst__wrt Tree_linorder__class_heap
embed (eval) test3 is Tree_bst__wrt Tree_linorder__class_heap .

end

end
