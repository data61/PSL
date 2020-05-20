section \<open>Host Properties\<close>

theory Wasm_Axioms imports Wasm begin

(* these were originally axioms, but memory now has a concrete representation in the model *)
lemma mem_grow_size:
  assumes "mem_grow m n = m'"
  shows "(mem_size m + (64000 * n)) = mem_size m'"
  using assms Abs_mem_inverse Abs_bytes_inverse
  unfolding mem_grow_def mem_size_def mem_append_def bytes_replicate_def
  by auto

lemma load_size:
  "(load m n off l = None) = (mem_size m < (off + n + l))"
  unfolding load_def
  by (cases "n + off + l \<le> mem_size m") auto

lemma load_packed_size:
  "(load_packed sx m n off lp l = None) = (mem_size m < (off + n + lp))"
  using load_size
  unfolding load_packed_def
  by (cases "n + off + l \<le> mem_size m") auto  

lemma store_size1:
  "(store m n off v l = None) = (mem_size m < (off + n + l))"
  unfolding store_def
  by (cases "n + off + l \<le> mem_size m") auto

lemma store_size:
  assumes "(store m n off v l = Some m')"
  shows "mem_size m = mem_size m'"
  using assms Abs_mem_inverse Abs_bytes_inverse
  unfolding store_def write_bytes_def bytes_takefill_def
  by (cases "n + off + l \<le> mem_size m") (auto simp add: mem_size_def)

lemma store_packed_size1:
  "(store_packed m n off v l = None) = (mem_size m < (off + n + l))"
  using store_size1
  unfolding store_packed_def
  by simp

lemma store_packed_size:
  assumes "(store_packed m n off v l = Some m')"
  shows "mem_size m = mem_size m'"
  using assms store_size
  unfolding store_packed_def
  by simp

axiomatization where
  wasm_deserialise_type:"typeof (wasm_deserialise bs t) = t"

axiomatization where
    host_apply_preserve_store:" list_all2 types_agree t1s vs \<Longrightarrow> host_apply s (t1s _> t2s) f vs hs = Some (s', vs') \<Longrightarrow> store_extension s s'"
and host_apply_respect_type:"list_all2 types_agree t1s vs \<Longrightarrow> host_apply s (t1s _> t2s) f vs hs = Some (s', vs') \<Longrightarrow> list_all2 types_agree t2s vs'"
end