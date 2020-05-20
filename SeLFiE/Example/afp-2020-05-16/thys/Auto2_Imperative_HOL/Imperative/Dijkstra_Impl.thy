(*
  File: Dijkstra_Impl.thy
  Author: Bohua Zhan
*)

section \<open>Implementation of Dijkstra's algorithm\<close>

theory Dijkstra_Impl
  imports Indexed_PQueue_Impl "../Functional/Dijkstra"
begin

text \<open>
  Imperative implementation of Dijkstra's shortest path algorithm. The
  algorithm is also verified by Nordhoff and Lammich in
  \cite{Dijkstra_Shortest_Path-AFP}.
\<close>

datatype dijkstra_state = Dijkstra_State (est_a: "nat array") (heap_pq: "nat indexed_pqueue")
setup \<open>add_simple_datatype "dijkstra_state"\<close>

fun dstate :: "state \<Rightarrow> dijkstra_state \<Rightarrow> assn" where
  "dstate (State e M) (Dijkstra_State a pq) = a \<mapsto>\<^sub>a e * idx_pqueue_map M (length e) pq"
setup \<open>add_rewrite_ent_rule @{thm dstate.simps}\<close>

subsection \<open>Basic operations\<close>

fun dstate_pq_init :: "graph \<Rightarrow> nat \<Rightarrow> nat indexed_pqueue Heap" where
  "dstate_pq_init G 0 = idx_pqueue_empty (size G)"
| "dstate_pq_init G (Suc k) = do {
    p \<leftarrow> dstate_pq_init G k;
    if k > 0 then update_idx_pqueue k (weight G 0 k) p
    else return p }"

lemma dstate_pq_init_to_fun [hoare_triple]:
  "k \<le> size G \<Longrightarrow>
   <emp>
   dstate_pq_init G k
   <idx_pqueue_map (map_constr (\<lambda>i. i > 0) (\<lambda>i. weight G 0 i) k) (size G)>\<^sub>t"
@proof @induct k @qed
 
definition dstate_init :: "graph \<Rightarrow> dijkstra_state Heap" where
  "dstate_init G = do {
     a \<leftarrow> Array.of_list (list (\<lambda>i. if i = 0 then 0 else weight G 0 i) (size G));
     pq \<leftarrow> dstate_pq_init G (size G);
     return (Dijkstra_State a pq)
   }"

lemma dstate_init_to_fun [hoare_triple]:
  "<emp>
   dstate_init G
   <dstate (dijkstra_start_state G)>\<^sub>t" by auto2

fun dstate_update_est :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat indexed_pqueue \<Rightarrow> nat array \<Rightarrow> nat array Heap" where
  "dstate_update_est G m 0 pq a = (return a)"
| "dstate_update_est G m (Suc k) pq a = do {
     b \<leftarrow> has_key_idx_pqueue k pq;
     if b then do {
       ek \<leftarrow> Array.nth a k;
       em \<leftarrow> Array.nth a m;
       a' \<leftarrow> dstate_update_est G m k pq a;
       a'' \<leftarrow> Array.upd k (min (em + weight G m k) ek) a';
       return a'' }
     else dstate_update_est G m k pq a }"

lemma dstate_update_est_ind [hoare_triple]:
  "k \<le> length e \<Longrightarrow> m < length e \<Longrightarrow>
   <a \<mapsto>\<^sub>a e * idx_pqueue_map M (length e) pq>
   dstate_update_est G m k pq a
   <\<lambda>r. dstate (State (list_update_set_impl (\<lambda>i. i \<in> keys_of M)
                      (\<lambda>i. min (e ! m + weight G m i) (e ! i)) e k) M) (Dijkstra_State r pq)>\<^sub>t"
@proof @induct k @qed

lemma dstate_update_est_to_fun [hoare_triple]:
  "<dstate (State e M) (Dijkstra_State a pq) * \<up>(m < length e)>
   dstate_update_est G m (length e) pq a
   <\<lambda>r. dstate (State (list_update_set (\<lambda>i. i \<in> keys_of M)
               (\<lambda>i. min (e ! m + weight G m i) (e ! i)) e) M) (Dijkstra_State r pq)>\<^sub>t" by auto2

fun dstate_update_heap ::
  "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat indexed_pqueue \<Rightarrow> nat indexed_pqueue Heap" where
  "dstate_update_heap G m 0 a pq = return pq"
| "dstate_update_heap G m (Suc k) a pq = do {
     b \<leftarrow> has_key_idx_pqueue k pq;
     if b then do {
       ek \<leftarrow> Array.nth a k;
       pq' \<leftarrow> dstate_update_heap G m k a pq;
       update_idx_pqueue k ek pq' }
     else dstate_update_heap G m k a pq }"

lemma dstate_update_heap_ind [hoare_triple]:
  "k \<le> length e \<Longrightarrow> m < length e \<Longrightarrow>
   <a \<mapsto>\<^sub>a e * idx_pqueue_map M (length e) pq>
   dstate_update_heap G m k a pq
   <\<lambda>r. dstate (State e (map_update_all_impl (\<lambda>i. e ! i) M k)) (Dijkstra_State a r)>\<^sub>t"
@proof @induct k @qed

lemma dstate_update_heap_to_fun [hoare_triple]:
  "m < length e \<Longrightarrow>
   \<forall>i\<in>keys_of M. i < length e \<Longrightarrow>
   <dstate (State e M) (Dijkstra_State a pq)>
   dstate_update_heap G m (length e) a pq
   <\<lambda>r. dstate (State e (map_update_all (\<lambda>i. e ! i) M)) (Dijkstra_State a r)>\<^sub>t" by auto2

fun dijkstra_extract_min :: "dijkstra_state \<Rightarrow> (nat \<times> dijkstra_state) Heap" where
  "dijkstra_extract_min (Dijkstra_State a pq) = do {
     (x, pq') \<leftarrow> delete_min_idx_pqueue pq;
     return (fst x, Dijkstra_State a pq') }"
  
lemma dijkstra_extract_min_rule [hoare_triple]:
  "M \<noteq> empty_map \<Longrightarrow>
   <dstate (State e M) (Dijkstra_State a pq)>
   dijkstra_extract_min (Dijkstra_State a pq)
   <\<lambda>(m, r). dstate (State e (delete_map m M)) r * \<up>(m < length e) * \<up>(is_heap_min m M)>\<^sub>t" by auto2

setup \<open>del_prfstep_thm @{thm dstate.simps}\<close>

subsection \<open>Main operations\<close>

fun dijkstra_step_impl :: "graph \<Rightarrow> dijkstra_state \<Rightarrow> dijkstra_state Heap" where
  "dijkstra_step_impl G (Dijkstra_State a pq) = do {
     (x, S') \<leftarrow> dijkstra_extract_min (Dijkstra_State a pq);
     a' \<leftarrow> dstate_update_est G x (size G) (heap_pq S') (est_a S');
     pq'' \<leftarrow> dstate_update_heap G x (size G) a' (heap_pq S');
     return (Dijkstra_State a' pq'') }"

lemma dijkstra_step_impl_to_fun [hoare_triple]:
  "heap S \<noteq> empty_map \<Longrightarrow> inv G S \<Longrightarrow>
   <dstate S (Dijkstra_State a pq)>
   dijkstra_step_impl G (Dijkstra_State a pq)
   <\<lambda>r. \<exists>\<^sub>AS'. dstate S' r * \<up>(is_dijkstra_step G S S')>\<^sub>t" by auto2

lemma dijkstra_step_impl_correct [hoare_triple]:
  "heap S \<noteq> empty_map \<Longrightarrow> inv G S \<Longrightarrow>
   <dstate S p>
   dijkstra_step_impl G p
   <\<lambda>r. \<exists>\<^sub>AS'. dstate S' r * \<up>(inv G S') * \<up>(card (unknown_set S') = card (unknown_set S) - 1)>\<^sub>t" by auto2

fun dijkstra_loop :: "graph \<Rightarrow> nat \<Rightarrow> dijkstra_state \<Rightarrow> dijkstra_state Heap" where
  "dijkstra_loop G 0 p = (return p)"
| "dijkstra_loop G (Suc k) p = do {
    p' \<leftarrow> dijkstra_step_impl G p;
    p'' \<leftarrow> dijkstra_loop G k p';
    return p'' }"

lemma dijkstra_loop_correct [hoare_triple]:
  "<dstate S p * \<up>(inv G S) * \<up>(n \<le> card (unknown_set S))>
   dijkstra_loop G n p
   <\<lambda>r. \<exists>\<^sub>AS'. dstate S' r * \<up>(inv G S') * \<up>(card (unknown_set S') = card (unknown_set S) - n)>\<^sub>t"
@proof @induct n arbitrary S p @qed

definition dijkstra :: "graph \<Rightarrow> dijkstra_state Heap" where
  "dijkstra G = do {
    p \<leftarrow> dstate_init G;
    dijkstra_loop G (size G - 1) p }"

text \<open>Correctness of Dijkstra's algorithm.\<close>
theorem dijkstra_correct [hoare_triple]:
  "size G > 0 \<Longrightarrow>
   <emp>
   dijkstra G
   <\<lambda>r. \<exists>\<^sub>AS. dstate S r * \<up>(inv G S) * \<up>(unknown_set S = {}) *
        \<up>(\<forall>i\<in>verts G. has_dist G 0 i \<and> est S ! i = dist G 0 i)>\<^sub>t" by auto2

end
