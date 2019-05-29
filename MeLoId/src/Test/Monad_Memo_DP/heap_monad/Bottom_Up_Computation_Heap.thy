theory Bottom_Up_Computation_Heap
  imports "../state_monad/Bottom_Up_Computation" "../heap_monad/DP_CRelVH"
begin

definition (in iterator_defs)
  "iter_heap f \<equiv>
    wfrec
      {(nxt x, x) | x. cnt x}
      (\<lambda> rec x. if cnt x then do {f x; rec (nxt x)} else return ())"

lemma (in iterator) iter_heap_unfold:
  "iter_heap f x = (if cnt x then do {f x; iter_heap f (nxt x)} else return ())"
  unfolding iter_heap_def
  by (simp add: wfrec_fixpoint[OF iterator.wellfounded,OF iterator.intro,OF terminating] adm_wf_def)

locale dp_consistency_iterator_heap =
  dp_consistency_heap P update lookup dp + iterator cnt nxt sizef
  for lookup :: "'a \<Rightarrow> ('c option) Heap" and update and P dp
    and cnt :: "'a \<Rightarrow> bool" and nxt and sizef
begin

context
  includes lifting_syntax
begin

term iter_heap

term crel_vs

lemma crel_vs_iterate_state:
  "crel_vs op = () (iter_heap f x)" if "(op = ===> crel_vs R) g f"
  using wellfounded
proof induction
  case (less x)
  have unit_expand: "() = (\<lambda> a f. f a) () (\<lambda> _. ())" ..
  from less show ?case
    by (subst iter_heap_unfold)
       (auto intro:
          bind_transfer[unfolded rel_fun_def, rule_format, unfolded unit_expand]
          crel_vs_return_ext[unfolded Transfer.Rel_def] that[unfolded rel_fun_def, rule_format]
       )
qed

lemma crel_vs_bind_ignore:
  "crel_vs R a (do {d; b})" if "crel_vs R a b" "crel_vs S c d"
proof -
  have unit_expand: "a = (\<lambda> a f. f a) () (\<lambda> _. a)" ..
  show ?thesis
    by (subst unit_expand)
       (rule bind_transfer[unfolded rel_fun_def, rule_format, unfolded unit_expand] that)+
qed

lemma crel_vs_iter_and_compute:
  assumes "(op = ===> crel_vs R) g f"
  shows "crel_vs R (g x) (do {iter_heap f y; f x})"
  by (rule
        crel_vs_bind_ignore crel_vs_iterate_state HOL.refl
        assms[unfolded rel_fun_def, rule_format] assms
     )+

lemma consistent_DP_iter_and_compute:
  assumes "consistentDP f"
  shows "consistentDP (\<lambda> x. do {iter_heap f y; f x})"
  apply (rule consistentDP_intro)
  using assms unfolding consistentDP_def Rel_def
  by (rule crel_vs_iter_and_compute)

end (* Lifting Syntax *)

end (* DP Consistency Iterator Heap *)

end (* Theory *)