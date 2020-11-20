section \<open>\isaheader{Implementation of Priority Queues by Skew Binomial Heaps}\<close>

theory SkewPrioImpl
imports 
  "Binomial-Heaps.SkewBinomialHeap" 
  "../spec/PrioSpec"
  "../tools/Record_Intf"
  "../tools/Locale_Code"
begin

(*@impl Prio
  @type ('a,'p::linorder) skew
  @abbrv skew
  Priority queues by skew binomial heaps. 
*)

subsection "Definitions"
type_synonym ('a,'b) skew = "('a, 'b) SkewBinomialHeap"

definition skew_\<alpha> where "skew_\<alpha> q \<equiv> SkewBinomialHeap.to_mset q"
definition skew_insert where "skew_insert \<equiv> SkewBinomialHeap.insert"
abbreviation (input) skew_invar :: "('a, 'b) SkewBinomialHeap \<Rightarrow> bool" 
  where "skew_invar \<equiv> \<lambda>_. True"
definition skew_find where "skew_find \<equiv> SkewBinomialHeap.findMin"
definition skew_delete where "skew_delete \<equiv> SkewBinomialHeap.deleteMin"
definition skew_meld where "skew_meld \<equiv> SkewBinomialHeap.meld"
definition skew_empty where "skew_empty \<equiv> \<lambda>_::unit. SkewBinomialHeap.empty"
definition skew_isEmpty where "skew_isEmpty = SkewBinomialHeap.isEmpty"

definition [icf_rec_def]: "skew_ops == \<lparr>
  prio_op_\<alpha> = skew_\<alpha>,
  prio_op_invar = skew_invar,
  prio_op_empty = skew_empty,
  prio_op_isEmpty = skew_isEmpty,
  prio_op_insert = skew_insert,
  prio_op_find = skew_find,
  prio_op_delete = skew_delete,
  prio_op_meld = skew_meld
\<rparr>"

lemmas skew_defs =
  skew_\<alpha>_def
  skew_insert_def
  skew_find_def
  skew_delete_def
  skew_meld_def
  skew_empty_def
  skew_isEmpty_def

subsection "Correctness"

theorem skew_empty_impl: "prio_empty skew_\<alpha> skew_invar skew_empty"
  by (unfold_locales, auto simp add: skew_defs)

theorem skew_isEmpty_impl: "prio_isEmpty skew_\<alpha> skew_invar skew_isEmpty"
  by unfold_locales 
     (simp add: skew_defs SkewBinomialHeap.isEmpty_correct SkewBinomialHeap.empty_correct)

theorem skew_find_impl: "prio_find skew_\<alpha> skew_invar skew_find"
  apply unfold_locales
  apply (simp add: skew_defs SkewBinomialHeap.empty_correct SkewBinomialHeap.findMin_correct)
  done

lemma skew_insert_impl: "prio_insert skew_\<alpha> skew_invar skew_insert"
  apply(unfold_locales)
  apply(unfold skew_defs) 
  apply (simp_all add: SkewBinomialHeap.insert_correct)
  done

lemma skew_meld_impl: "prio_meld skew_\<alpha> skew_invar skew_meld"
  apply(unfold_locales)
  apply(unfold skew_defs)
  apply(simp_all add: SkewBinomialHeap.meld_correct)
  done
      
lemma skew_delete_impl: 
  "prio_delete skew_\<alpha> skew_invar skew_find skew_delete"
  apply intro_locales
  apply (rule skew_find_impl)
  apply(unfold_locales)
  apply(simp_all add: skew_defs SkewBinomialHeap.empty_correct SkewBinomialHeap.deleteMin_correct)
done 

setup Locale_Code.open_block
interpretation skew: StdPrio skew_ops
  apply (rule StdPrio.intro)
  apply (simp_all add: icf_rec_unf)
  apply (rule 
    skew_empty_impl
    skew_isEmpty_impl
    skew_find_impl
    skew_insert_impl
    skew_meld_impl
    skew_delete_impl
  )+
  done
interpretation skew: StdPrio_no_invar skew_ops
  by unfold_locales (simp add: icf_rec_unf)
setup Locale_Code.close_block

definition test_codegen where "test_codegen \<equiv> (
  skew.empty,
  skew.isEmpty,
  skew.find,
  skew.insert,
  skew.meld,
  skew.delete
)"

export_code test_codegen checking SML

end
