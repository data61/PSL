(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
theory ArrayHashSet
imports 
  ArrayHashMap 
  "../gen_algo/SetByMap"
  "../gen_algo/SetGA"
begin

(*@impl Set
  @type ('a) ahs
  @abbrv ahs,a
  Array based hash sets without explicit invariant.
*)

subsection "Definitions"
type_synonym
  'a ahs = "('a::hashable,unit) ahm"

setup Locale_Code.open_block
interpretation ahs_sbm: SetByMap ahm_basic_ops by unfold_locales
setup Locale_Code.close_block

definition ahs_ops :: "('a::hashable,'a ahs) set_ops"
  where [icf_rec_def]:
  "ahs_ops \<equiv> ahs_sbm.basic.dflt_ops"

setup Locale_Code.open_block
interpretation ahs: StdSet ahs_ops
  unfolding ahs_ops_def by (rule ahs_sbm.basic.dflt_ops_impl)
interpretation ahs: StdSet_no_invar ahs_ops 
  apply unfold_locales
  by (simp add: icf_rec_unf SetByMapDefs.invar_def)
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "ahs"\<close>

lemmas ahs_it_to_it_map_code_unfold[code_unfold] = 
  it_to_it_map_fold'[OF pi_ahm]

lemma pi_ahs[proper_it]: "proper_it' ahs.iteratei ahs.iteratei"
  unfolding ahs.iteratei_def[abs_def]
  by (rule proper_it'I icf_proper_iteratorI)+

interpretation pi_ahs: proper_it_loc ahs.iteratei ahs.iteratei
  by unfold_locales (rule pi_ahs)

definition test_codegen where "test_codegen \<equiv> (
  ahs.empty,
  ahs.memb,
  ahs.ins,
  ahs.delete,
  ahs.list_it,
  ahs.sng,
  ahs.isEmpty,
  ahs.isSng,
  ahs.ball,
  ahs.bex,
  ahs.size,
  ahs.size_abort,
  ahs.union,
  ahs.union_dj,
  ahs.diff,
  ahs.filter,
  ahs.inter,
  ahs.subset,
  ahs.equal,
  ahs.disjoint,
  ahs.disjoint_witness,
  ahs.sel,
  ahs.to_list,
  ahs.from_list
)"

export_code test_codegen checking SML

end
