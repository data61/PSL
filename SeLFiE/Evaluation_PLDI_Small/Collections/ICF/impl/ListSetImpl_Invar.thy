(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section \<open>\isaheader{Set Implementation by List with explicit invariants}\<close>
theory ListSetImpl_Invar
  imports 
  "../spec/SetSpec"
  "../gen_algo/SetGA"
  "../../Lib/Dlist_add"
begin
text_raw \<open>\label{thy:ListSetImpl_Invar}\<close>

(*@impl Set
  @type 'a lsi
  @abbrv lsi,l
  Sets by lists with distinct elements. Version with explicit invariant that 
  supports efficient @{text "insert_dj"} operation.
*)

type_synonym
  'a lsi = "'a list"

subsection "Definitions"

definition lsi_ins :: "'a \<Rightarrow> 'a lsi \<Rightarrow> 'a lsi" where "lsi_ins x l == if  List.member l x then l else x#l"

definition lsi_basic_ops :: "('a,'a lsi) set_basic_ops" where
  [icf_rec_def]: "lsi_basic_ops \<equiv> \<lparr>
    bset_op_\<alpha> = set,
    bset_op_invar = distinct,
    bset_op_empty = \<lambda>_. [],
    bset_op_memb = (\<lambda>x s. List.member s x),
    bset_op_ins = lsi_ins,
    bset_op_ins_dj = (#),
    bset_op_delete = \<lambda>x l. Dlist_add.dlist_remove1' x [] l,
    bset_op_list_it = foldli
    \<rparr>"

setup Locale_Code.open_block
interpretation lsi_basic: StdBasicSet lsi_basic_ops
  apply unfold_locales
  unfolding lsi_basic_ops_def lsi_ins_def[abs_def]
  apply (auto simp: List.member_def set_dlist_remove1' 
  distinct_remove1')
  done
setup Locale_Code.close_block

definition [icf_rec_def]: "lsi_ops \<equiv> lsi_basic.dflt_ops \<lparr>
  set_op_union_dj := (@),
  set_op_to_list := id
\<rparr>"

setup Locale_Code.open_block
interpretation lsi: StdSet lsi_ops
proof -
  interpret aux: StdSet lsi_basic.dflt_ops by (rule lsi_basic.dflt_ops_impl)

  show "StdSet lsi_ops"
    unfolding lsi_ops_def
    apply (rule StdSet_intro)
    apply icf_locales
    apply (simp_all add: icf_rec_unf)
    apply (unfold_locales, auto)
    done
qed
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "lsi"\<close>

lemma pi_lsi[proper_it]: 
  "proper_it' foldli foldli"
  by (intro icf_proper_iteratorI proper_it'I)

interpretation pi_lsi: proper_it_loc foldli foldli
  apply unfold_locales by (rule pi_lsi)

definition test_codegen where "test_codegen \<equiv> (
  lsi.empty,
  lsi.memb,
  lsi.ins,
  lsi.delete,
  lsi.list_it,
  lsi.sng,
  lsi.isEmpty,
  lsi.isSng,
  lsi.ball,
  lsi.bex,
  lsi.size,
  lsi.size_abort,
  lsi.union,
  lsi.union_dj,
  lsi.diff,
  lsi.filter,
  lsi.inter,
  lsi.subset,
  lsi.equal,
  lsi.disjoint,
  lsi.disjoint_witness,
  lsi.sel,
  lsi.to_list,
  lsi.from_list
)"

export_code test_codegen checking SML

end
