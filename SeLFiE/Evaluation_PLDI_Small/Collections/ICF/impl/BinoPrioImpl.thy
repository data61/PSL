section \<open>\isaheader{Implementation of Priority Queues by Binomial Heap}\<close>

theory BinoPrioImpl
imports 
  "Binomial-Heaps.BinomialHeap" 
  "../spec/PrioSpec"
  "../tools/Record_Intf"
  "../tools/Locale_Code"
begin

(*@impl Prio
  @type ('a,'p::linorder) bino
  @abbrv bino
  Binomial heaps.
*)

type_synonym ('a,'b) bino = "('a,'b) BinomialHeap"

subsection "Definitions"
definition bino_\<alpha> where "bino_\<alpha> q \<equiv> BinomialHeap.to_mset q"
definition bino_insert where "bino_insert \<equiv> BinomialHeap.insert"
abbreviation (input) bino_invar :: "('a,'b) BinomialHeap \<Rightarrow> bool"
  where "bino_invar \<equiv> \<lambda>_. True"
definition bino_find where "bino_find \<equiv> BinomialHeap.findMin"
definition bino_delete where "bino_delete \<equiv> BinomialHeap.deleteMin"
definition bino_meld where "bino_meld \<equiv> BinomialHeap.meld"
definition bino_empty where "bino_empty \<equiv> \<lambda>_::unit. BinomialHeap.empty"
definition bino_isEmpty where "bino_isEmpty = BinomialHeap.isEmpty"

definition [icf_rec_def]: "bino_ops == \<lparr>
  prio_op_\<alpha> = bino_\<alpha>,
  prio_op_invar = bino_invar,
  prio_op_empty = bino_empty,
  prio_op_isEmpty = bino_isEmpty,
  prio_op_insert = bino_insert,
  prio_op_find = bino_find,
  prio_op_delete = bino_delete,
  prio_op_meld = bino_meld
\<rparr>"

lemmas bino_defs =
  bino_\<alpha>_def
  bino_insert_def
  bino_find_def
  bino_delete_def
  bino_meld_def
  bino_empty_def
  bino_isEmpty_def

subsection "Correctness"

theorem bino_empty_impl: "prio_empty bino_\<alpha> bino_invar bino_empty"
  by (unfold_locales, auto simp add: bino_defs)

theorem bino_isEmpty_impl: "prio_isEmpty bino_\<alpha> bino_invar bino_isEmpty"
  by unfold_locales 
     (simp add: bino_defs BinomialHeap.isEmpty_correct BinomialHeap.empty_correct)

theorem bino_find_impl: "prio_find bino_\<alpha> bino_invar bino_find"
  apply unfold_locales
  apply (simp add: bino_defs BinomialHeap.empty_correct BinomialHeap.findMin_correct)
  done

lemma bino_insert_impl: "prio_insert bino_\<alpha> bino_invar bino_insert"
  apply(unfold_locales)
  apply(unfold bino_defs) 
  apply (simp_all add: BinomialHeap.insert_correct)
  done

lemma bino_meld_impl: "prio_meld bino_\<alpha> bino_invar bino_meld"
  apply(unfold_locales)
  apply(unfold bino_defs)
  apply(simp_all add: BinomialHeap.meld_correct)
  done
      
lemma bino_delete_impl: 
  "prio_delete bino_\<alpha> bino_invar bino_find bino_delete"
  apply intro_locales
  apply (rule bino_find_impl)
  apply(unfold_locales)
  apply(simp_all add: bino_defs BinomialHeap.empty_correct BinomialHeap.deleteMin_correct)
done 

setup Locale_Code.open_block
interpretation bino: StdPrio bino_ops
  apply (rule StdPrio.intro)
  apply (simp_all add: icf_rec_unf)
  apply (rule 
    bino_empty_impl
    bino_isEmpty_impl
    bino_find_impl
    bino_insert_impl
    bino_meld_impl
    bino_delete_impl
  )+
  done
interpretation bino: StdPrio_no_invar bino_ops
  apply unfold_locales
  apply (simp add: icf_rec_unf)
  done
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "bino"\<close>

definition test_codegen where "test_codegen = (
  bino.empty,
  bino.isEmpty,
  bino.find,
  bino.insert,
  bino.meld,
  bino.delete
)"

export_code test_codegen checking SML

end
