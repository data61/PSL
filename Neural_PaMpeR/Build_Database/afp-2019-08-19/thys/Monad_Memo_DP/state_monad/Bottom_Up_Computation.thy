subsection \<open>Bottom-Up Computation\<close>

theory Bottom_Up_Computation
  imports "../state_monad/Memory" "../state_monad/DP_CRelVS"
begin

fun iterate_state where
  "iterate_state f [] = State_Monad.return ()" |
  "iterate_state f (x # xs) = do {f x; iterate_state f xs}"

locale iterator_defs =
  fixes cnt :: "'a \<Rightarrow> bool" and nxt :: "'a \<Rightarrow> 'a"
begin

definition
  "iter_state f \<equiv>
    wfrec
      {(nxt x, x) | x. cnt x}
      (\<lambda> rec x. if cnt x then do {f x; rec (nxt x)} else State_Monad.return ())"

definition
  "iterator_to_list \<equiv>
    wfrec {(nxt x, x) | x. cnt x} (\<lambda> rec x. if cnt x then x # rec (nxt x) else [])
  "

end

locale iterator = iterator_defs +
  fixes sizef :: "'a \<Rightarrow> nat"
  assumes terminating:
    "finite {x. cnt x}" "\<forall> x. cnt x \<longrightarrow> sizef x < sizef (nxt x)"
begin

lemma admissible:
  "adm_wf
      {(nxt x, x) | x. cnt x}
      (\<lambda> rec x. if cnt x then do {f x; rec (nxt x)} else State_Monad.return ())"
  unfolding adm_wf_def by auto

lemma wellfounded:
  "wf {(nxt x, x) | x. cnt x}" (is "wf ?S")
proof -
  from terminating have "acyclic ?S"
    by (auto intro: acyclicI_order[where f = sizef])
  moreover have "finite ?S"
    using [[simproc add: finite_Collect]] terminating(1) by auto
  ultimately show ?thesis
    by - (rule finite_acyclic_wf)
qed

lemma iter_state_unfold:
  "iter_state f x = (if cnt x then do {f x; iter_state f (nxt x)} else State_Monad.return ())"
  unfolding iter_state_def by (simp add: wfrec_fixpoint[OF wellfounded admissible])

lemma iterator_to_list_unfold:
  "iterator_to_list x = (if cnt x then x # iterator_to_list (nxt x) else [])"
  unfolding iterator_to_list_def by (simp add: adm_wf_def wfrec_fixpoint[OF wellfounded])

lemma iter_state_iterate_state:
  "iter_state f x = iterate_state f (iterator_to_list x)"
  apply (induction "iterator_to_list x" arbitrary: x)
   apply (simp add: iterator_to_list_unfold split: if_split_asm)
   apply (simp add: iter_state_unfold)
  apply (subst (asm) (3) iterator_to_list_unfold)
  apply (simp split: if_split_asm)
  apply (auto simp: iterator_to_list_unfold iter_state_unfold)
  done

end (* Termination *)

context dp_consistency
begin

context
  includes lifting_syntax
begin

lemma crel_vs_iterate_state:
  "crel_vs (=) () (iterate_state f xs)" if "((=) ===>\<^sub>T R) g f"
proof (induction xs)
  case Nil
  then show ?case
    by (simp; rule crel_vs_return_ext[unfolded Transfer.Rel_def]; simp; fail)
next
  case (Cons x xs)
  have unit_expand: "() = (\<lambda> a f. f a) () (\<lambda> _. ())" ..
  from Cons show ?case
    by simp
      (rule
        bind_transfer[unfolded rel_fun_def, rule_format, unfolded unit_expand]
        that[unfolded rel_fun_def, rule_format] HOL.refl
      )+
qed

lemma crel_vs_bind_ignore:
  "crel_vs R a (do {d; b})" if "crel_vs R a b" "crel_vs S c d"
proof -
  have unit_expand: "a = (\<lambda> a f. f a) () (\<lambda> _. a)" ..
  show ?thesis
    by (subst unit_expand)
       (rule bind_transfer[unfolded rel_fun_def, rule_format, unfolded unit_expand] that)+
qed

lemma crel_vs_iterate_and_compute:
  assumes "((=) ===>\<^sub>T R) g f"
  shows "crel_vs R (g x) (do {iterate_state f xs; f x})"
  by (rule
        crel_vs_bind_ignore crel_vs_iterate_state HOL.refl
        assms[unfolded rel_fun_def, rule_format] assms
     )+

end (* Lifting Syntax *)

end (* DP Consistency *)

locale dp_consistency_iterator =
  dp_consistency lookup update + iterator cnt nxt sizef
  for lookup :: "'a \<Rightarrow> ('b, 'c option) state" and update
    and cnt :: "'a \<Rightarrow> bool" and nxt and sizef
begin

lemma crel_vs_iter_and_compute:
  assumes "((=) ===>\<^sub>T R) g f"
  shows "crel_vs R (g x) (do {iter_state f y; f x})"
  unfolding iter_state_iterate_state using crel_vs_iterate_and_compute[OF assms] .

lemma consistentDP_iter_and_compute:
  assumes "consistentDP f"
  shows "crel_vs (=) (dp x) (do {iter_state f y; f x})"
  using assms unfolding consistentDP_def by (rule crel_vs_iter_and_compute)

end (* Consistency + Iterator *)

locale dp_consistency_iterator_empty =
  dp_consistency_iterator + dp_consistency_empty
begin

lemma memoized:
  "dp x = fst (run_state (do {iter_state f y; f x}) empty)" if "consistentDP f"
  using consistentDP_iter_and_compute[OF that, of x y]
  by (auto elim!: crel_vs_elim intro: P_empty cmem_empty)

lemma cmem_result:
  "cmem (snd (run_state (do {iter_state f y; f x}) empty))" if "consistentDP f"
  using consistentDP_iter_and_compute[OF that, of x y]
  by (auto elim!: crel_vs_elim intro: P_empty cmem_empty)

end (* Consistency + Iterator *)

lemma dp_consistency_iterator_emptyI:
  "dp_consistency_iterator_empty P lookup update cnt
    nxt sizef empty"
  if "dp_consistency_empty lookup update P empty"
     "iterator cnt nxt sizef"
   for empty
  by (meson
      dp_consistency_empty.axioms(1) dp_consistency_iterator_def
      dp_consistency_iterator_empty_def that
     )

context
  fixes m :: nat \<comment> \<open>Width of a row\<close>
    and n :: nat \<comment> \<open>Number of rows\<close>
begin

lemma table_iterator_up:
  "iterator
    (\<lambda> (x, y). x \<le> n \<and> y \<le> m)
    (\<lambda> (x, y). if y < m then (x, y + 1) else (x + 1, 0))
    (\<lambda> (x, y). x * (m + 1) + y)"
  by standard auto

lemma table_iterator_down:
  "iterator
    (\<lambda> (x, y). x \<le> n \<and> y \<le> m \<and> x > 0)
    (\<lambda> (x, y). if y > 0 then (x, y - 1) else (x - 1, m))
    (\<lambda> (x, y). (n - x) * (m + 1) + (m - y))"
  using [[simproc add: finite_Collect]]  by standard (auto simp: Suc_diff_le)

end (* Table *)

end (* Theory *)
