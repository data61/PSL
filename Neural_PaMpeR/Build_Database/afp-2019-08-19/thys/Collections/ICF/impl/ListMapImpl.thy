(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section \<open>\isaheader{Map Implementation by Associative Lists}\<close>
theory ListMapImpl
imports 
  "../spec/MapSpec" 
  "../../Lib/Assoc_List" 
  "../gen_algo/MapGA"
begin
text_raw \<open>\label{thy:ListMapImpl}\<close>

(*@impl Map
  @type 'a lm
  @abbrv lm,l
  Maps implemented by associative lists. If you need efficient 
  @{text "insert_dj"} operation, you should use list sets with explicit 
  invariants (lmi).
*)

type_synonym ('k,'v) lm = "('k,'v) assoc_list"

definition [icf_rec_def]: "lm_basic_ops \<equiv> \<lparr>
  bmap_op_\<alpha> = Assoc_List.lookup,
  bmap_op_invar = \<lambda>_. True,
  bmap_op_empty = (\<lambda>_::unit. Assoc_List.empty),
  bmap_op_lookup = (\<lambda>k m. Assoc_List.lookup m k),
  bmap_op_update = Assoc_List.update,
  bmap_op_update_dj = Assoc_List.update,
  bmap_op_delete = Assoc_List.delete,
  bmap_op_list_it = Assoc_List.iteratei
\<rparr>"

setup Locale_Code.open_block
interpretation lm_basic: StdBasicMapDefs lm_basic_ops .
interpretation lm_basic: StdBasicMap lm_basic_ops
  apply unfold_locales
  apply (simp_all add: icf_rec_unf 
    Assoc_List.lookup_empty' Assoc_List.iteratei_correct map_upd_eq_restrict)
  done
setup Locale_Code.close_block

definition [icf_rec_def]: "lm_ops \<equiv> lm_basic.dflt_ops"
setup Locale_Code.open_block
interpretation lm: StdMapDefs lm_ops .
interpretation lm: StdMap lm_ops 
  unfolding lm_ops_def
  by (rule lm_basic.dflt_ops_impl)
interpretation lm: StdMap_no_invar lm_ops 
  by unfold_locales (simp add: icf_rec_unf)
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "lm"\<close>

lemma pi_lm[proper_it]: 
  "proper_it' Assoc_List.iteratei Assoc_List.iteratei"
  unfolding Assoc_List.iteratei_def[abs_def]
  by (intro icf_proper_iteratorI proper_it'I)

interpretation pi_lm: proper_it_loc Assoc_List.iteratei Assoc_List.iteratei
  apply unfold_locales
  apply (rule pi_lm)
  done

lemma pi_lm'[proper_it]: 
  "proper_it' lm.iteratei lm.iteratei"
  unfolding lm.iteratei_def[abs_def]
  by (intro icf_proper_iteratorI proper_it'I)

interpretation pi_lm': proper_it_loc lm.iteratei lm.iteratei
  apply unfold_locales
  apply (rule pi_lm')
  done


text \<open>Code generator test\<close>
definition "test_codegen \<equiv> (
  lm.add ,
  lm.add_dj ,
  lm.ball ,
  lm.bex ,
  lm.delete ,
  lm.empty ,
  lm.isEmpty ,
  lm.isSng ,
  lm.iterate ,
  lm.iteratei ,
  lm.list_it ,
  lm.lookup ,
  lm.restrict ,
  lm.sel ,
  lm.size ,
  lm.size_abort ,
  lm.sng ,
  lm.to_list ,
  lm.to_map ,
  lm.update ,
  lm.update_dj)"

export_code test_codegen checking SML

end
