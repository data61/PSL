(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section \<open>\isaheader{Fifo Queue by Pair of Lists}\<close>
theory Fifo
imports 
  "../gen_algo/ListGA"
  "../tools/Record_Intf"
  "../tools/Locale_Code"
begin
text_raw \<open>\label{thy:Fifo}\<close>

(* TODO: Move to Misc *)
lemma rev_tl_rev: "rev (tl (rev l)) = butlast l"
  by (induct l) auto


(*@impl List
  @type 'a fifo
  @abbrv fifo
  Fifo-Queues implemented by two stacks.
*)

text \<open>
  A fifo-queue is implemented by a pair of two lists (stacks). 
  New elements are pushed on the first stack, and elements are popped from 
  the second stack. If the second stack is empty, the first stack is reversed
  and replaces the second stack.

  If list reversal is implemented efficiently (what is the case in Isabelle/HOL, 
  cf @{thm [source] List.rev_conv_fold})
  the amortized time per buffer operation is constant.

  Moreover, this fifo implementation also supports efficient push and pop operations.
\<close>

subsection \<open>Definitions\<close>
type_synonym 'a fifo = "'a list \<times> 'a list"

text "Abstraction of the fifo to a list. The next element to be got is at 
      the head of the list, and new elements are appended at the end of the
      list"
definition fifo_\<alpha> :: "'a fifo \<Rightarrow> 'a list" 
  where "fifo_\<alpha> F == snd F @ rev (fst F)"

text "This fifo implementation has no invariants, any pair of lists is a 
  valid fifo"
definition [simp, intro!]: "fifo_invar x = True"


  \<comment> \<open>The empty fifo\<close>
definition fifo_empty :: "unit \<Rightarrow> 'a fifo" 
  where "fifo_empty == \<lambda>_::unit. ([],[])"

  \<comment> \<open>True, iff the fifo is empty\<close>
definition fifo_isEmpty :: "'a fifo \<Rightarrow> bool" where "fifo_isEmpty F == F=([],[])"

definition fifo_size :: "'a fifo \<Rightarrow> nat" where 
  "fifo_size F \<equiv> length (fst F) + length (snd F)"

  \<comment> \<open>Add an element to the fifo\<close>
definition fifo_appendr :: "'a \<Rightarrow> 'a fifo \<Rightarrow> 'a fifo" 
  where "fifo_appendr a F == (a#fst F, snd F)"

definition fifo_appendl :: "'a \<Rightarrow> 'a fifo \<Rightarrow> 'a fifo"
  where "fifo_appendl x F == case F of (e,d) \<Rightarrow> (e,x#d)"

\<comment> \<open>Get an element from the fifo\<close>
definition fifo_remover :: "'a fifo \<Rightarrow> ('a fifo \<times> 'a)" where 
  "fifo_remover F ==
    case fst F of
      (a#l) \<Rightarrow> ((l,snd F),a) |
      [] \<Rightarrow> let rp=rev (snd F) in
        ((tl rp,[]),hd rp)"

definition fifo_removel :: "'a fifo \<Rightarrow> ('a \<times> 'a fifo)" where 
  "fifo_removel F ==
    case snd F of
      (a#l) \<Rightarrow> (a, (fst F, l)) |
      [] \<Rightarrow> let rp=rev (fst F) in
        (hd rp, ([], tl rp))
"

definition fifo_leftmost :: "'a fifo \<Rightarrow> 'a" where
  "fifo_leftmost F \<equiv> case F of (_,x#_) \<Rightarrow> x | (l,[]) \<Rightarrow> last l"

definition fifo_rightmost :: "'a fifo \<Rightarrow> 'a" where
  "fifo_rightmost F \<equiv> case F of (x#_,_) \<Rightarrow> x | ([],l) \<Rightarrow> last l"

definition "fifo_iteratei F \<equiv> foldli (fifo_\<alpha> F)"
definition "fifo_rev_iteratei F \<equiv> foldri (fifo_\<alpha> F)"

definition "fifo_get F i \<equiv> 
  let
    l2 = length (snd F)
  in
    if i < l2 then 
      snd F!i 
    else
      (fst F)!(length (fst F) - Suc (i - l2))
  "

definition "fifo_set F i a \<equiv> case F of (f1,f2) \<Rightarrow>
  let
    l2 = length f2
  in
    if i < l2 then 
      (f1,f2[i:=a])
    else
      (f1[length (fst F) - Suc (i - l2) := a],f2)"

subsection "Correctness"

lemma fifo_empty_impl: "list_empty fifo_\<alpha> fifo_invar fifo_empty"
  apply (unfold_locales)
  by (auto simp add: fifo_\<alpha>_def fifo_empty_def)

lemma fifo_isEmpty_impl: "list_isEmpty fifo_\<alpha> fifo_invar fifo_isEmpty"
  apply (unfold_locales)
  by (case_tac s) (auto simp add: fifo_isEmpty_def fifo_\<alpha>_def)

lemma fifo_size_impl: "list_size fifo_\<alpha> fifo_invar fifo_size"
  apply unfold_locales
  by (auto simp add: fifo_size_def fifo_\<alpha>_def)
  
lemma fifo_appendr_impl: "list_appendr fifo_\<alpha> fifo_invar fifo_appendr"
  apply (unfold_locales)
  by (auto simp add: fifo_appendr_def fifo_\<alpha>_def)

lemma fifo_appendl_impl: "list_appendl fifo_\<alpha> fifo_invar fifo_appendl"
  apply (unfold_locales)
  by (auto simp add: fifo_appendl_def fifo_\<alpha>_def)

lemma fifo_removel_impl: "list_removel fifo_\<alpha> fifo_invar fifo_removel"
  apply (unfold_locales)
  apply (case_tac s)
  apply (case_tac b)
  apply (auto simp add: fifo_removel_def fifo_\<alpha>_def Let_def) [2]
  apply (case_tac s)
  apply (case_tac "b")
  apply (auto simp add: fifo_removel_def fifo_\<alpha>_def Let_def)
  done

lemma fifo_remover_impl: "list_remover fifo_\<alpha> fifo_invar fifo_remover"
  apply (unfold_locales)
  unfolding fifo_remover_def fifo_\<alpha>_def Let_def
  by (auto split: list.split simp: hd_rev rev_tl_rev butlast_append)

lemma fifo_leftmost_impl: "list_leftmost fifo_\<alpha> fifo_invar fifo_leftmost"
  apply unfold_locales
  by (auto simp: fifo_leftmost_def fifo_\<alpha>_def hd_rev split: list.split)

lemma fifo_rightmost_impl: "list_rightmost fifo_\<alpha> fifo_invar fifo_rightmost"
  apply unfold_locales
  by (auto simp: fifo_rightmost_def fifo_\<alpha>_def hd_rev split: list.split)

lemma fifo_get_impl: "list_get fifo_\<alpha> fifo_invar fifo_get"
  apply unfold_locales
  apply (auto simp: fifo_\<alpha>_def fifo_get_def Let_def nth_append rev_nth)
  done

lemma fifo_set_impl: "list_set fifo_\<alpha> fifo_invar fifo_set"
  apply unfold_locales
  apply (auto simp: fifo_\<alpha>_def fifo_set_def Let_def list_update_append
    rev_update)
  done

definition [icf_rec_def]: "fifo_ops \<equiv> \<lparr>
  list_op_\<alpha> = fifo_\<alpha>,
  list_op_invar = fifo_invar,
  list_op_empty = fifo_empty,
  list_op_isEmpty = fifo_isEmpty,
  list_op_size = fifo_size,
  list_op_appendl = fifo_appendl,
  list_op_removel = fifo_removel,
  list_op_leftmost = fifo_leftmost,
  list_op_appendr = fifo_appendr,
  list_op_remover = fifo_remover,
  list_op_rightmost = fifo_rightmost,
  list_op_get = fifo_get,
  list_op_set = fifo_set
  \<rparr>"

setup Locale_Code.open_block
interpretation fifo: StdList fifo_ops
  apply (rule StdList.intro)
  apply (simp_all add: icf_rec_unf)
  apply (rule 
    fifo_empty_impl
    fifo_isEmpty_impl
    fifo_size_impl
    fifo_appendl_impl
    fifo_removel_impl
    fifo_leftmost_impl
    fifo_appendr_impl
    fifo_remover_impl
    fifo_rightmost_impl
    fifo_get_impl
    fifo_set_impl)+
  done
interpretation fifo: StdList_no_invar fifo_ops
  by unfold_locales (simp add: icf_rec_unf)
setup Locale_Code.close_block
setup \<open>ICF_Tools.revert_abbrevs "fifo"\<close>

definition test_codegen where "test_codegen \<equiv> 
  (
    fifo.empty,
    fifo.isEmpty,
    fifo.size,
    fifo.appendl,
    fifo.removel,
    fifo.leftmost,
    fifo.appendr,
    fifo.remover,
    fifo.rightmost,
    fifo.get,
    fifo.set,
    fifo.iteratei,
    fifo.rev_iteratei
  )"

export_code test_codegen checking SML

end
