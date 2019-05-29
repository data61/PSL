theory Heap_Default
  imports
    Heap_Main
    "../Index"
begin

locale dp_consistency_heap_default =
  fixes bound :: "'k :: {index, heap} bound"
    and mem :: "'v::heap option array"
    and dp :: "'k \<Rightarrow> 'v"
begin

interpretation idx: bounded_index bound .

sublocale dp_consistency_heap
  where P="\<lambda>heap. Array.length heap mem = idx.size"
    and lookup="mem_lookup idx.size idx.checked_idx mem"
    and update="mem_update idx.size idx.checked_idx mem"
  apply (rule dp_consistency_heap.intro)
  apply (rule mem_heap_correct)
  apply (rule idx.checked_idx_injective)
  done

context
  fixes empty
  assumes empty: "map_of_heap empty \<subseteq>\<^sub>m Map.empty"
      and len: "Array.length empty mem = idx.size"
begin

interpretation consistent: dp_consistency_heap_empty
  where P="\<lambda>heap. Array.length heap mem = idx.size"
    and lookup="mem_lookup idx.size idx.checked_idx mem"
    and update="mem_update idx.size idx.checked_idx mem"
  by (standard; rule len empty)

lemmas memoizedI = consistent.memoized
lemmas successI = consistent.memoized_success

end

lemma mem_empty_empty:
  "map_of_heap (heap_of (mem_empty idx.size :: 'v option array Heap) Heap.empty) \<subseteq>\<^sub>m Map.empty"
  if "mem = result_of (mem_empty idx.size) Heap.empty"
  by (auto intro!: map_emptyI simp:
      that length_mem_empty Let_def nth_mem_empty mem_lookup_def heap_mem_defs.map_of_heap_def
      )

lemma memoized_empty:
  "dp x = result_of ((mem_empty idx.size :: 'v option array Heap) \<bind> (\<lambda>mem. dp\<^sub>T mem x)) Heap.empty"
  if "consistentDP (dp\<^sub>T mem)" "mem = result_of (mem_empty idx.size) Heap.empty"
  apply (subst execute_bind_success)
   defer
   apply (subst memoizedI[OF _ _ that(1)])
  using mem_empty_empty[OF that(2)] by (auto simp: that(2) length_mem_empty)

lemma init_success:
  "success ((mem_empty idx.size :: 'v option array Heap) \<bind> (\<lambda>mem. dp\<^sub>T mem x)) Heap.empty"
  if "consistentDP (dp\<^sub>T mem)" "mem = result_of (mem_empty idx.size) Heap.empty"
  apply (rule success_bind_I[OF success_empty])
  apply (frule execute_result_ofD)
  apply (drule execute_heap_ofD)
  using mem_empty_empty that by (auto simp: length_mem_empty intro: successI)

end

end