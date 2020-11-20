(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section \<open>\isaheader{Hash Set}\<close>
theory HashSet
  imports 
  "../spec/SetSpec" 
  HashMap 
  "../gen_algo/SetByMap" 
  "../gen_algo/SetGA"
begin
text_raw \<open>\label{thy:HashSet}\<close>
(*@impl Set
  @type 'a::hashable hs
  @abbrv hs,h
  Hash sets based on red-black trees.
*)

subsection "Definitions"
type_synonym
  'a hs = "('a::hashable,unit) hm"

setup Locale_Code.open_block
interpretation hs_sbm: SetByMap hm_basic_ops by unfold_locales
setup Locale_Code.close_block

definition hs_ops :: "('a::hashable,'a hs) set_ops"
  where [icf_rec_def]:
  "hs_ops \<equiv> hs_sbm.basic.dflt_ops"

setup Locale_Code.open_block
interpretation hs: StdSet hs_ops
  unfolding hs_ops_def by (rule hs_sbm.basic.dflt_ops_impl)
interpretation hs: StdSet_no_invar hs_ops
  by unfold_locales (simp add: icf_rec_unf SetByMapDefs.invar_def)
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "hs"\<close>

lemmas hs_it_to_it_map_code_unfold[code_unfold] = 
  it_to_it_map_fold'[OF pi_hm]

lemma pi_hs[proper_it]: "proper_it' hs.iteratei hs.iteratei"
  unfolding hs.iteratei_def[abs_def]
  by (rule proper_it'I icf_proper_iteratorI)+

interpretation pi_hs: proper_it_loc hs.iteratei hs.iteratei
  by unfold_locales (rule pi_hs)

definition test_codegen where "test_codegen \<equiv> (
  hs.empty,
  hs.memb,
  hs.ins,
  hs.delete,
  hs.list_it,
  hs.sng,
  hs.isEmpty,
  hs.isSng,
  hs.ball,
  hs.bex,
  hs.size,
  hs.size_abort,
  hs.union,
  hs.union_dj,
  hs.diff,
  hs.filter,
  hs.inter,
  hs.subset,
  hs.equal,
  hs.disjoint,
  hs.disjoint_witness,
  hs.sel,
  hs.to_list,
  hs.from_list
)"

export_code test_codegen checking SML

end
