(*
  File: Rect_Intersect_Impl.thy
  Author: Bohua Zhan
*)

section \<open>Implementation of rectangle intersection\<close>

theory Rect_Intersect_Impl
  imports "../Functional/Rect_Intersect" IntervalTree_Impl Quicksort_Impl
begin

text \<open>Imperative version of rectangle-intersection algorithm.\<close>

subsection \<open>Operations\<close>

fun operation_encode :: "('a::heap) operation \<Rightarrow> nat" where
  "operation_encode oper =
   (case oper of INS p i n \<Rightarrow> to_nat (is_INS oper, p, i, n)
               | DEL p i n \<Rightarrow> to_nat (is_INS oper, p, i, n))"

instance operation :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "operation_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  apply (simp add: operation.case_eq_if)
  ..

subsection \<open>Initial state\<close>

definition rect_inter_init :: "nat rectangle list \<Rightarrow> nat operation array Heap" where
  "rect_inter_init rects = do {
     p \<leftarrow> Array.of_list (ins_ops rects @ del_ops rects);
     quicksort_all p;
     return p }"

setup \<open>add_rewrite_rule @{thm all_ops_def}\<close>
lemma rect_inter_init_rule [hoare_triple]:
  "<emp> rect_inter_init rects <\<lambda>p. p \<mapsto>\<^sub>a all_ops rects>" by auto2
setup \<open>del_prfstep_thm @{thm all_ops_def}\<close>

definition rect_inter_next :: "nat operation array \<Rightarrow> int_tree \<Rightarrow> nat \<Rightarrow> int_tree Heap" where
  "rect_inter_next a b k = do {
    oper \<leftarrow> Array.nth a k;
    if is_INS oper then
      IntervalTree_Impl.insert_impl (IdxInterval (op_int oper) (op_idx oper)) b
    else
      IntervalTree_Impl.delete_impl (IdxInterval (op_int oper) (op_idx oper)) b }"

lemma op_int_is_interval:
  "is_rect_list rects \<Longrightarrow> ops = all_ops rects \<Longrightarrow> k < length ops \<Longrightarrow>
   is_interval (op_int (ops ! k))"
@proof @have "ops ! k \<in> set ops" @case "is_INS (ops ! k)" @qed
setup \<open>add_forward_prfstep_cond @{thm op_int_is_interval} [with_term "op_int (?ops ! ?k)"]\<close>

lemma rect_inter_next_rule [hoare_triple]:
  "is_rect_list rects \<Longrightarrow> k < length (all_ops rects) \<Longrightarrow>
   <a \<mapsto>\<^sub>a all_ops rects * int_tree_set S b>
   rect_inter_next a b k
   <\<lambda>r. a \<mapsto>\<^sub>a all_ops rects * int_tree_set (apply_ops_k_next rects S k) r>\<^sub>t" by auto2

partial_function (heap) rect_inter_impl ::
  "nat operation array \<Rightarrow> int_tree \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "rect_inter_impl a b k = do {
    n \<leftarrow> Array.len a;
    (if k \<ge> n then return False
     else do {
       oper \<leftarrow> Array.nth a k;
       (if is_INS oper then do {
          overlap \<leftarrow> IntervalTree_Impl.search_impl (op_int oper) b;
          if overlap then return True
          else if k = n - 1 then return False
          else do {
            b' \<leftarrow> rect_inter_next a b k;
            rect_inter_impl a b' (k + 1)}}
        else
          if k = n - 1 then return False
          else do {
            b' \<leftarrow> rect_inter_next a b k;
            rect_inter_impl a b' (k + 1)})})}"

lemma rect_inter_to_fun_ind [hoare_triple]:
  "is_rect_list rects \<Longrightarrow> k < length (all_ops rects) \<Longrightarrow>
   <a \<mapsto>\<^sub>a all_ops rects * int_tree_set S b>
   rect_inter_impl a b k
   <\<lambda>r. a \<mapsto>\<^sub>a all_ops rects * \<up>(r \<longleftrightarrow> rect_inter rects S k)>\<^sub>t"
@proof
  @let "d = length (all_ops rects) - k"
  @strong_induct d arbitrary k S b
  @case "k \<ge> length (all_ops rects)"
  @unfold "rect_inter rects S k"
  @case "is_INS (all_ops rects ! k)" @with
    @case "has_overlap S (op_int (all_ops rects ! k))"
    @case "k = length (all_ops rects) - 1"
    @apply_induct_hyp "length (all_ops rects) - (k + 1)" "k + 1"
    @have "length (all_ops rects) - (k + 1) < d"
  @end
  @case "k = length (all_ops rects) - 1"
  @apply_induct_hyp "length (all_ops rects) - (k + 1)" "k + 1"
  @have "length (all_ops rects) - (k + 1) < d"
@qed

definition rect_inter_all :: "nat rectangle list \<Rightarrow> bool Heap" where
  "rect_inter_all rects =
    (if rects = [] then return False
     else do {
       a \<leftarrow> rect_inter_init rects;
       b \<leftarrow> int_tree_empty;
       rect_inter_impl a b 0 })"

text \<open>Correctness of rectangle intersection algorithm.\<close>
theorem rect_inter_all_correct:
  "is_rect_list rects \<Longrightarrow>
   <emp>
   rect_inter_all rects
   <\<lambda>r. \<up>(r = has_rect_overlap rects)>\<^sub>t" by auto2

end
