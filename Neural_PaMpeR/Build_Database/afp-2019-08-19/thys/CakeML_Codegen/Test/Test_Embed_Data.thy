theory Test_Embed_Data
imports
  Lazy_Case.Lazy_Case
  "../Preproc/Embed"
  "../Preproc/Eval_Instances"
  "HOL-Data_Structures.Leftist_Heap"
begin

text \<open>Sets are unsupported, so we have to rewrite @{const set}.\<close>

declare List.Ball_set[code_unfold]
declare Let_def[code_unfold]

declassify valid:
  Leftist_Heap.rank
  Leftist_Heap.rk
  Leftist_Heap.ltree
  Leftist_Heap.node
  Leftist_Heap.merge
  Leftist_Heap.insert
  Leftist_Heap.del_min

thm valid

derive evaluate
  Tree2.tree
  Orderings_ord__dict

experiment begin

embed (eval) test1 is
  Leftist__Heap_rk
  Leftist__Heap_rank
  Leftist__Heap_ltree
  Leftist__Heap_node
  .

(* skipping proofs for performance *)
embed (eval, skip) test2 is
  Leftist__Heap_merge
  Leftist__Heap_insert
  Leftist__Heap_del__min
  .

end

end
