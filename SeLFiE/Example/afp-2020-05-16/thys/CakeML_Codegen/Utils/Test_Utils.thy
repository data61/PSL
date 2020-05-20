theory Test_Utils
imports
  Code_Utils
  Huffman.Huffman
  "HOL-Data_Structures.Leftist_Heap"
  "Pairing_Heap.Pairing_Heap_Tree"
  "Root_Balanced_Tree.Root_Balanced_Tree"
  "Dict_Construction.Dict_Construction"
begin

section \<open>Dynamic unfolding\<close>

definition one :: nat where
"one = 1"

fun plus_one :: "nat \<Rightarrow> nat" where
"plus_one (Suc x) = one + plus_one x" |
"plus_one _ = one"

ML\<open>
fun has_one ctxt =
  let
    val const = @{const_name plus_one}
    val {eqngr, ...} = Code_Preproc.obtain true {ctxt = ctxt, consts = [const], terms = []}
    val all_consts = Graph.all_succs eqngr [const]
  in
    member op = all_consts @{const_name one}
  end
\<close>

ML\<open>@{assert} (has_one @{context})\<close>

context
  notes [[dynamic_unfold]]
begin

ML\<open>@{assert} (not (has_one @{context}))\<close>

end

section \<open>Pattern compatibility\<close>

subsection \<open>Cannot deal with diagonal function\<close>

fun diagonal :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat" where
"diagonal x True False = 1" |
"diagonal False y True = 2" |
"diagonal True False z = 3"

code_thms diagonal

code_thms Leftist_Heap.ltree

context
  notes [[pattern_compatibility]]
begin

ML\<open>
  {ctxt = @{context}, consts = [@{const_name diagonal}], terms = []}
  |> can (Code_Preproc.obtain true)
  |> not
  |> @{assert}
\<close>

export_code huffman checking SML Scala

export_code
  Leftist_Heap.rank
  Leftist_Heap.rk
  Leftist_Heap.ltree
  Leftist_Heap.node
  Leftist_Heap.merge
  Leftist_Heap.insert
  Leftist_Heap.del_min
  checking SML Scala

export_code
  Pairing_Heap_Tree.link
  Pairing_Heap_Tree.pass\<^sub>1
  Pairing_Heap_Tree.pass\<^sub>2
  Pairing_Heap_Tree.merge_pairs
  Pairing_Heap_Tree.is_root
  Pairing_Heap_Tree.pheap
  checking SML Scala

export_code
  Root_Balanced_Tree.size_tree_tm
  Root_Balanced_Tree.inorder2_tm
  Root_Balanced_Tree.split_min_tm
  checking SML Scala

end

(* FIXME RBT *)

(* FIXME move to Dict_Construction *)

ML\<open>open Dict_Construction_Util\<close>

lemma
  assumes "P" "Q" "R"
  shows "P \<and> Q \<and> R"
apply (tactic \<open>
  (REPEAT_ALL_NEW (resolve_tac @{context} @{thms conjI}) CONTINUE_WITH
    [resolve_tac @{context} @{thms assms(1)}, resolve_tac @{context} @{thms assms(2)}, resolve_tac @{context} @{thms assms(3)}]) 1
\<close>)
done

lemma
  assumes "P" "Q" "R"
  shows "P \<and> Q \<and> R"
apply (tactic \<open>
  (REPEAT_ALL_NEW (resolve_tac @{context} @{thms conjI}) CONTINUE_WITH_FW
    [resolve_tac @{context} @{thms assms(1)}, K all_tac, resolve_tac @{context} @{thms assms(3)}]) 1
\<close>)
apply (rule assms(2))
done

lemma
  assumes "P" "Q"
  shows "(P \<and> Q)" "(P \<and> Q)"
apply (tactic \<open>Goal.recover_conjunction_tac THEN
  (Goal.conjunction_tac THEN_ALL_NEW
    (REPEAT_ALL_NEW (resolve_tac @{context} @{thms conjI}) CONTINUE_WITH
    [resolve_tac @{context} @{thms assms(1)}, resolve_tac @{context} @{thms assms(2)}])) 1
\<close>)
done

lemma
  assumes "Q" "P"
  shows "P \<and> Q"
apply (tactic \<open>
  (resolve_tac @{context} @{thms conjI conjI[rotated]} CONTINUE_WITH
    [resolve_tac @{context} @{thms assms(1)}, resolve_tac @{context} @{thms assms(2)}]) 1
\<close>)
done

end