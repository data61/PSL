(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
(*
  Changes since submission on 2009-11-26:

  2009-12-10: OrderedSet, implemented iterators, min, max, to_sorted_list

*)

section \<open>\isaheader{Set Implementation by Red-Black-Tree}\<close>
theory RBTSetImpl
imports 
  "../spec/SetSpec"
  RBTMapImpl
  "../gen_algo/SetByMap"
  "../gen_algo/SetGA"
begin
text_raw \<open>\label{thy:RBTSetImpl}\<close>
(*@impl Set
  @type ('a::linorder) rs
  @abbrv rs,r
  Sets over linearly ordered elements implemented by red-black trees.
*)

subsection "Definitions"
type_synonym
  'a rs = "('a::linorder,unit) rm"

setup Locale_Code.open_block
interpretation rs_sbm: OSetByOMap rm_basic_ops by unfold_locales
setup Locale_Code.close_block

definition rs_ops :: "('x::linorder,'x rs) oset_ops"
  where [icf_rec_def]: "rs_ops \<equiv> rs_sbm.obasic.dflt_oops"

setup Locale_Code.open_block
interpretation rs: StdOSetDefs rs_ops .
interpretation rs: StdOSet rs_ops
  unfolding rs_ops_def
  by (rule rs_sbm.obasic.dflt_oops_impl)

interpretation rs: StdSet_no_invar rs_ops
  by unfold_locales (simp add: icf_rec_unf SetByMapDefs.invar_def)
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "rs"\<close>

lemmas rbt_it_to_it_map_code_unfold[code_unfold] = 
  it_to_it_map_fold'[OF pi_rm]
  it_to_it_map_fold'[OF pi_rm_rev]

lemma pi_rs[proper_it]:
  "proper_it' rs.iteratei rs.iteratei"
  "proper_it' rs.iterateoi rs.iterateoi"
  "proper_it' rs.rev_iterateoi rs.rev_iterateoi"
  unfolding rs.iteratei_def[abs_def] rs.iterateoi_def[abs_def] 
    rs.rev_iterateoi_def[abs_def]
  by (rule proper_it'I icf_proper_iteratorI)+

interpretation
  pi_rs: proper_it_loc rs.iteratei rs.iteratei +
  pi_rs_o: proper_it_loc rs.iterateoi rs.iterateoi +
  pi_rs_ro: proper_it_loc rs.rev_iterateoi rs.rev_iterateoi
  by unfold_locales (rule pi_rs)+

definition test_codegen where "test_codegen \<equiv> (
  rs.empty,
  rs.memb,
  rs.ins,
  rs.delete,
  rs.list_it,
  rs.sng,
  rs.isEmpty,
  rs.isSng,
  rs.ball,
  rs.bex,
  rs.size,
  rs.size_abort,
  rs.union,
  rs.union_dj,
  rs.diff,
  rs.filter,
  rs.inter,
  rs.subset,
  rs.equal,
  rs.disjoint,
  rs.disjoint_witness,
  rs.sel,
  rs.to_list,
  rs.from_list,

  rs.ordered_list_it,
  rs.rev_list_it,
  rs.min, 
  rs.max, 
  rs.to_sorted_list,
  rs.to_rev_list
)"

export_code test_codegen checking SML

end
