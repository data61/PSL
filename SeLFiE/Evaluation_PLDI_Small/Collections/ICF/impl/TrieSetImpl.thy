(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
section \<open>\isaheader{Set implementation via tries}\<close>
theory TrieSetImpl imports
  TrieMapImpl
  "../gen_algo/SetByMap"
  "../gen_algo/SetGA"
begin

(*@impl Set
  @type ('a) ts
  @abbrv ts,t
  Sets of elements of type @{typ "'a list"} implemented by tries.
*)

subsection "Definitions"

type_synonym
  'a ts = "('a, unit) trie"

setup Locale_Code.open_block
interpretation ts_sbm: SetByMap tm_basic_ops by unfold_locales
setup Locale_Code.close_block

definition ts_ops :: "('a list,'a ts) set_ops"
  where [icf_rec_def]:
  "ts_ops \<equiv> ts_sbm.basic.dflt_ops"

setup Locale_Code.open_block
interpretation ts: StdSet ts_ops
  unfolding ts_ops_def by (rule ts_sbm.basic.dflt_ops_impl)
interpretation ts: StdSet_no_invar ts_ops
  by unfold_locales (simp add: icf_rec_unf SetByMapDefs.invar_def)
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "ts"\<close>

lemmas ts_it_to_it_map_code_unfold[code_unfold] = 
  it_to_it_map_fold'[OF pi_trie]

lemma pi_ts[proper_it]: "proper_it' ts.iteratei ts.iteratei"
  unfolding ts.iteratei_def[abs_def]
  by (rule proper_it'I icf_proper_iteratorI)+

interpretation pi_ts: proper_it_loc ts.iteratei ts.iteratei
  by unfold_locales (rule pi_ts)

definition test_codegen where "test_codegen \<equiv> (
  ts.empty,
  ts.memb,
  ts.ins,
  ts.delete,
  ts.list_it,
  ts.sng,
  ts.isEmpty,
  ts.isSng,
  ts.ball,
  ts.bex,
  ts.size,
  ts.size_abort,
  ts.union,
  ts.union_dj,
  ts.diff,
  ts.filter,
  ts.inter,
  ts.subset,
  ts.equal,
  ts.disjoint,
  ts.disjoint_witness,
  ts.sel,
  ts.to_list,
  ts.from_list
)"

export_code test_codegen checking SML

end
