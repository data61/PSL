(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
(*
  Changelist since submission on 2009-11-26:

  2009-12-09: Ordered iterators, to_list produces sorted list


*)
section \<open>\isaheader{Map Implementation by Red-Black-Trees}\<close>
theory RBTMapImpl
imports 
  "../spec/MapSpec"
  "../../Lib/RBT_add" 
  "HOL-Library.RBT"
  "../gen_algo/MapGA"
begin
text_raw \<open>\label{thy:RBTMapImpl}\<close>

hide_const (open) RBT.map RBT.fold RBT.foldi RBT.empty RBT.insert

(*@impl Map
  @type ('k::linorder,'v) rm 
  @abbrv rm,r
  Maps over linearly ordered keys implemented by red-black trees.
*)

type_synonym ('k,'v) rm = "('k,'v) RBT.rbt"

definition rm_basic_ops :: "('k::linorder,'v,('k,'v) rm) omap_basic_ops"
  where [icf_rec_def]: "rm_basic_ops \<equiv> \<lparr>
  bmap_op_\<alpha> = RBT.lookup,
  bmap_op_invar = \<lambda>_. True,
  bmap_op_empty = (\<lambda>_::unit. RBT.empty),
  bmap_op_lookup = (\<lambda>k m. RBT.lookup m k),
  bmap_op_update = RBT.insert,
  bmap_op_update_dj = RBT.insert,
  bmap_op_delete = RBT.delete,
  bmap_op_list_it = (\<lambda>r. RBT_add.rm_iterateoi (RBT.impl_of r)),
  bmap_op_ordered_list_it = (\<lambda>r. RBT_add.rm_iterateoi (RBT.impl_of r)),
  bmap_op_rev_list_it = (\<lambda>r. RBT_add.rm_reverse_iterateoi (RBT.impl_of r))
\<rparr>"

setup Locale_Code.open_block
interpretation rm_basic: StdBasicOMap rm_basic_ops
  apply unfold_locales
  apply (simp_all add: rm_basic_ops_def map_upd_eq_restrict)
  apply (rule map_iterator_linord_is_it)
  apply dup_subgoals
  unfolding RBT.lookup_def
  apply simp_all
  apply (rule rm_iterateoi_correct)
  apply simp
  apply (rule rm_reverse_iterateoi_correct)
  apply simp
  done
setup Locale_Code.close_block

definition [icf_rec_def]: "rm_ops \<equiv> rm_basic.dflt_oops\<lparr>map_op_add := RBT.union\<rparr>"
setup Locale_Code.open_block
interpretation rm: StdOMap rm_ops 
proof -
  interpret aux1: StdOMap rm_basic.dflt_oops
    unfolding rm_ops_def
    by (rule rm_basic.dflt_oops_impl)
  interpret aux2: map_add RBT.lookup "\<lambda>_. True" RBT.union
    apply unfold_locales
    apply (rule lookup_union)
    .

  show "StdOMap rm_ops"
    apply (rule StdOMap_intro)
    apply icf_locales
    done
qed

interpretation rm: StdMap_no_invar rm_ops 
  by unfold_locales (simp add: icf_rec_unf)
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "rm"\<close>

lemma pi_rm[proper_it]: 
  "proper_it' RBT_add.rm_iterateoi RBT_add.rm_iterateoi"
  apply (rule proper_it'I)
  by (induct_tac s) (simp_all add: rm_iterateoi_alt_def icf_proper_iteratorI)
lemma pi_rm_rev[proper_it]: 
  "proper_it' RBT_add.rm_reverse_iterateoi RBT_add.rm_reverse_iterateoi"
  apply (rule proper_it'I)
  by (induct_tac s) (simp_all add: rm_reverse_iterateoi_alt_def 
    icf_proper_iteratorI)

interpretation pi_rm: proper_it_loc RBT_add.rm_iterateoi RBT_add.rm_iterateoi
  apply unfold_locales by (rule pi_rm)
interpretation pi_rm_rev: proper_it_loc RBT_add.rm_reverse_iterateoi
  RBT_add.rm_reverse_iterateoi
  apply unfold_locales by (rule pi_rm_rev)

text \<open>Code generator test\<close>
definition "test_codegen \<equiv> (rm.add ,
  rm.add_dj ,
  rm.ball ,
  rm.bex ,
  rm.delete ,
  rm.empty ,
  rm.isEmpty ,
  rm.isSng ,
  rm.iterate ,
  rm.iteratei ,
  rm.iterateo ,
  rm.iterateoi ,
  rm.list_it ,
  rm.lookup ,
  rm.max ,
  rm.min ,
  rm.restrict ,
  rm.rev_iterateo ,
  rm.rev_iterateoi ,
  rm.rev_list_it ,
  rm.reverse_iterateo ,
  rm.reverse_iterateoi ,
  rm.sel ,
  rm.size ,
  rm.size_abort ,
  rm.sng ,
  rm.to_list ,
  rm.to_map ,
  rm.to_rev_list ,
  rm.to_sorted_list ,
  rm.update ,
  rm.update_dj)"

export_code test_codegen checking SML

end
