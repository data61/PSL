(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section \<open>\isaheader{Set Implementation by List}\<close>
theory ListSetImpl
imports "../spec/SetSpec" "../gen_algo/SetGA" "../../Lib/Dlist_add"
begin
text_raw \<open>\label{thy:ListSetImpl}\<close>

(*@impl Set
  @type 'a ls
  @abbrv ls,l
  Sets implemented by distinct lists. For efficient 
  @{text "insert_dj"}-operations, use the version with explicit invariant (lsi).
*)

type_synonym
  'a ls = "'a dlist"

subsection "Definitions"

definition ls_\<alpha> :: "'a ls \<Rightarrow> 'a set" where "ls_\<alpha> l == set (list_of_dlist l)"

definition ls_basic_ops :: "('a,'a ls) set_basic_ops" where
  [icf_rec_def]: "ls_basic_ops \<equiv> \<lparr>
    bset_op_\<alpha> = ls_\<alpha>,
    bset_op_invar = \<lambda>_. True,
    bset_op_empty = \<lambda>_. Dlist.empty,
    bset_op_memb = (\<lambda>x s. Dlist.member s x),
    bset_op_ins = Dlist.insert,
    bset_op_ins_dj = Dlist.insert,
    bset_op_delete = dlist_remove',
    bset_op_list_it = dlist_iteratei
    \<rparr>"

setup Locale_Code.open_block
interpretation ls_basic: StdBasicSet ls_basic_ops
  apply unfold_locales
  unfolding ls_basic_ops_def ls_\<alpha>_def[abs_def]
  apply (auto simp: dlist_member_empty Dlist.member_def List.member_def
    dlist_iteratei_correct
    dlist_remove'_correct set_dlist_remove1'
  )
  done
setup Locale_Code.close_block

definition [icf_rec_def]: "ls_ops \<equiv> ls_basic.dflt_ops\<lparr> 
  set_op_to_list := list_of_dlist
  \<rparr>"

setup Locale_Code.open_block
interpretation ls: StdSetDefs ls_ops .
interpretation ls: StdSet ls_ops
proof -
  interpret aux: StdSet ls_basic.dflt_ops
    by (rule ls_basic.dflt_ops_impl)

  show "StdSet ls_ops"
    unfolding ls_ops_def
    apply (rule StdSet_intro)
    apply icf_locales
    apply (simp_all add: icf_rec_unf)
    apply (unfold_locales)
    apply (simp_all add: ls_\<alpha>_def)
    done
qed

interpretation ls: StdSet_no_invar ls_ops
  by unfold_locales (simp add: icf_rec_unf)
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "ls"\<close>

lemma pi_ls[proper_it]:
  "proper_it' dlist_iteratei dlist_iteratei"
  apply (rule proper_it'I)
  unfolding dlist_iteratei_def
  by (intro icf_proper_iteratorI)

lemma pi_ls'[proper_it]: 
  "proper_it' ls.iteratei ls.iteratei"
  apply (rule proper_it'I)
  unfolding ls.iteratei_def
  by (intro icf_proper_iteratorI)

interpretation pi_ls: proper_it_loc dlist_iteratei dlist_iteratei
  apply unfold_locales by (rule pi_ls)

interpretation pi_ls': proper_it_loc ls.iteratei ls.iteratei
  apply unfold_locales by (rule pi_ls')

definition test_codegen where "test_codegen \<equiv> (
  ls.empty,
  ls.memb,
  ls.ins,
  ls.delete,
  ls.list_it,
  ls.sng,
  ls.isEmpty,
  ls.isSng,
  ls.ball,
  ls.bex,
  ls.size,
  ls.size_abort,
  ls.union,
  ls.union_dj,
  ls.diff,
  ls.filter,
  ls.inter,
  ls.subset,
  ls.equal,
  ls.disjoint,
  ls.disjoint_witness,
  ls.sel,
  ls.to_list,
  ls.from_list
)"

export_code test_codegen checking SML

end
