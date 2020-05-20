section \<open>\isaheader{Set Implementation by Arrays}\<close>
theory ArraySetImpl
imports 
  "../spec/SetSpec" 
  ArrayMapImpl 
  "../gen_algo/SetByMap" 
  "../gen_algo/SetGA"
begin
text_raw \<open>\label{thy:ArraySetImpl}\<close>

(*@impl Set
  @type ias
  @abbrv ias,is
  Sets of natural numbers implemented by arrays.
*)

subsection "Definitions"
type_synonym ias = "(unit) iam"

setup Locale_Code.open_block
interpretation ias_sbm: OSetByOMap iam_basic_ops by unfold_locales
setup Locale_Code.close_block
definition ias_ops :: "(nat,ias) oset_ops"
  where [icf_rec_def]:
  "ias_ops \<equiv> ias_sbm.obasic.dflt_oops"

setup Locale_Code.open_block
interpretation ias: StdOSet ias_ops
  unfolding ias_ops_def by (rule ias_sbm.obasic.dflt_oops_impl)
interpretation ias: StdSet_no_invar ias_ops
  by unfold_locales (simp add: icf_rec_unf SetByMapDefs.invar_def)
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "ias"\<close>

lemmas ias_it_to_it_map_code_unfold[code_unfold] = 
  it_to_it_map_fold'[OF pi_iam]
  it_to_it_map_fold'[OF pi_iam_rev]

lemma pi_ias[proper_it]: 
  "proper_it' ias.iteratei ias.iteratei"
  "proper_it' ias.iterateoi ias.iterateoi"
  "proper_it' ias.rev_iterateoi ias.rev_iterateoi"
  unfolding ias.iteratei_def[abs_def] ias.iterateoi_def[abs_def] 
    ias.rev_iterateoi_def[abs_def]
  apply (rule proper_it'I icf_proper_iteratorI)+
  done

interpretation 
  pi_ias: proper_it_loc ias.iteratei ias.iteratei +
  pi_ias_o: proper_it_loc ias.iterateoi ias.iterateoi +
  pi_ias_ro: proper_it_loc ias.rev_iterateoi ias.rev_iterateoi
  apply unfold_locales by (rule pi_ias)+

definition test_codegen where "test_codegen \<equiv> (
  ias.empty,
  ias.memb,
  ias.ins,
  ias.delete,
  ias.list_it,
  ias.sng,
  ias.isEmpty,
  ias.isSng,
  ias.ball,
  ias.bex,
  ias.size,
  ias.size_abort,
  ias.union,
  ias.union_dj,
  ias.diff,
  ias.filter,
  ias.inter,
  ias.subset,
  ias.equal,
  ias.disjoint,
  ias.disjoint_witness,
  ias.sel,
  ias.to_list,
  ias.from_list,

  ias.ordered_list_it,
  ias.rev_list_it,
  ias.min, 
  ias.max, 
  ias.to_sorted_list,
  ias.to_rev_list
)"

export_code test_codegen checking SML

end
