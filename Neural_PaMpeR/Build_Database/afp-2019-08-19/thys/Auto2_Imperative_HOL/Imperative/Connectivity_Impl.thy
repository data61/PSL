(*
  File: Connectivity_Impl.thy
  Author: Bohua Zhan
*)

section \<open>Implementation of connectivity on graphs\<close>

theory Connectivity_Impl
  imports Union_Find_Impl "../Functional/Connectivity"
begin

text \<open>Imperative version of graph-connectivity example.\<close>

subsection \<open>Constructing the connected relation\<close>

fun connected_rel_imp :: "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> uf Heap" where
  "connected_rel_imp n es 0 = do { p \<leftarrow> uf_init n; return p }"
| "connected_rel_imp n es (Suc k) = do {
    p \<leftarrow> connected_rel_imp n es k;
    p' \<leftarrow> uf_union p (fst (es ! k)) (snd (es ! k));
    return p' }"

lemma connected_rel_imp_to_fun [hoare_triple]:
  "is_valid_graph n (set es) \<Longrightarrow> k \<le> length es \<Longrightarrow>
   <emp>
   connected_rel_imp n es k
   <is_uf n (connected_rel_ind n es k)>"
@proof @induct k @qed

lemma connected_rel_imp_correct [hoare_triple]:
  "is_valid_graph n (set es) \<Longrightarrow>
   <emp>
   connected_rel_imp n es (length es)
   <is_uf n (connected_rel n (set es))>" by auto2

subsection \<open>Connectedness tests\<close>

text \<open>Correctness of the algorithm for detecting connectivity.\<close>
theorem uf_cmp_correct [hoare_triple]:
  "<is_uf n (connected_rel n S) p>
   uf_cmp p i j
   <\<lambda>r. is_uf n (connected_rel n S) p * \<up>(r \<longleftrightarrow> has_path n S i j)>" by auto2

end
