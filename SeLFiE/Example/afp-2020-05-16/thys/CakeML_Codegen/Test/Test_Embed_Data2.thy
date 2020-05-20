theory Test_Embed_Data2
imports
  Lazy_Case.Lazy_Case
  "../Preproc/Embed"
  "../Preproc/Eval_Instances"
  "Pairing_Heap.Pairing_Heap_Tree"
begin

declare List.Ball_set[code_unfold]

lemma [code_unfold]: "(\<forall>x \<in> set_tree l. P x) \<longleftrightarrow> list_all P (inorder l)"
  by (induction l) auto

declassify valid:
  Pairing_Heap_Tree.link
  Pairing_Heap_Tree.pass\<^sub>1
  Pairing_Heap_Tree.pass\<^sub>2
  Pairing_Heap_Tree.merge_pairs
  Pairing_Heap_Tree.is_root
  Pairing_Heap_Tree.pheap

thm valid

derive evaluate
  Tree.tree
  Orderings_ord__dict
  Orderings_preorder__dict
  Orderings_order__dict
  Orderings_linorder__dict
  HOL_equal__dict

experiment begin

embed (eval) test1 is
  Pairing__Heap__Tree_link
  Pairing__Heap__Tree_pass\<^sub>1
  Pairing__Heap__Tree_pass\<^sub>2
  Pairing__Heap__Tree_merge__pairs
  Pairing__Heap__Tree_pheap
  .

end

end
