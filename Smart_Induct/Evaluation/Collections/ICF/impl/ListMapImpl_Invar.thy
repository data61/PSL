(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section \<open>\isaheader{Map Implementation by Association Lists with explicit invariants}\<close>
theory ListMapImpl_Invar
imports 
  "../spec/MapSpec"
  "../../Lib/Assoc_List" 
  "../gen_algo/MapGA"
begin
text_raw \<open>\label{thy:ListMapImpl_Invar}\<close>

(*@impl Map
  @type 'a lmi
  @abbrv lmi,l
  Maps implemented by associative lists. Version with explicit 
  invariants that allows for efficient xxx-dj operations.
*)

type_synonym ('k,'v) lmi = "('k\<times>'v) list"

term revg

definition "lmi_\<alpha> \<equiv> Map.map_of"
definition "lmi_invar \<equiv> \<lambda>m. distinct (List.map fst m)"

definition lmi_basic_ops :: "('k,'v,('k,'v) lmi) map_basic_ops"
  where [icf_rec_def]: "lmi_basic_ops \<equiv> \<lparr>
  bmap_op_\<alpha> = lmi_\<alpha>,
  bmap_op_invar = lmi_invar,
  bmap_op_empty = (\<lambda>_::unit. []),
  bmap_op_lookup = (\<lambda>k m. Map.map_of m k),
  bmap_op_update = AList.update,
  bmap_op_update_dj = (\<lambda>k v m. (k, v) # m),
  bmap_op_delete = AList.delete_aux,
  bmap_op_list_it = foldli
\<rparr>"


setup Locale_Code.open_block
interpretation lmi_basic: StdBasicMapDefs lmi_basic_ops .
interpretation lmi_basic: StdBasicMap lmi_basic_ops 
  unfolding lmi_basic_ops_def
  apply unfold_locales
  apply (simp_all 
    add: icf_rec_unf lmi_\<alpha>_def lmi_invar_def 
    add: AList.update_conv' AList.distinct_update AList.map_of_delete_aux'
      map_iterator_foldli_correct dom_map_of_conv_image_fst map_upd_eq_restrict
  )
  done
setup Locale_Code.close_block


definition [icf_rec_def]: "lmi_ops \<equiv> lmi_basic.dflt_ops \<lparr>
  map_op_add_dj := revg,
  map_op_to_list := id,
  map_op_size := length,
  map_op_isEmpty := case_list True (\<lambda>_ _. False),
  map_op_isSng := (\<lambda>l. case l of [_] \<Rightarrow> True | _ \<Rightarrow> False)
\<rparr>"

setup Locale_Code.open_block
interpretation lmi: StdMapDefs lmi_ops .
interpretation lmi: StdMap lmi_ops 
proof -
  interpret aux: StdMap lmi_basic.dflt_ops by (rule lmi_basic.dflt_ops_impl)

  have [simp]: "map_add_dj lmi_\<alpha> lmi_invar revg"
    apply (unfold_locales)
    apply (auto simp: lmi_\<alpha>_def lmi_invar_def)
    apply (blast intro: map_add_comm)
    apply (simp add: rev_map[symmetric])
    apply fastforce
    done

  have [simp]: "map_to_list lmi_\<alpha> lmi_invar id"
    apply unfold_locales
    by (simp_all add: lmi_\<alpha>_def lmi_invar_def)

  have [simp]: "map_isEmpty lmi_\<alpha> lmi_invar (case_list True (\<lambda>_ _. False))"
    apply unfold_locales
    unfolding lmi_\<alpha>_def lmi_invar_def
    by (simp split: list.split)

  have [simp]: "map_isSng lmi_\<alpha> lmi_invar
     (\<lambda>l. case l of [_] \<Rightarrow> True | _ \<Rightarrow> False)"
    apply unfold_locales
    unfolding lmi_\<alpha>_def lmi_invar_def
    apply (auto split: list.split)
    apply (metis (no_types) map_upd_nonempty)
    by (metis fun_upd_other fun_upd_same option.simps(3))

  have [simp]: "map_size_axioms lmi_\<alpha> lmi_invar length" 
    apply unfold_locales
    unfolding lmi_\<alpha>_def lmi_invar_def
    by (metis card_dom_map_of)

  show "StdMap lmi_ops"
    unfolding lmi_ops_def
    apply (rule StdMap_intro)
    apply (simp_all)
    apply intro_locales
    apply (simp_all add: icf_rec_unf)
    done
qed
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "lmi"\<close>

lemma pi_lmi[proper_it]: 
  "proper_it' foldli foldli"
  by (intro proper_it'I icf_proper_iteratorI)

interpretation pi_lmi: proper_it_loc foldli foldli
  apply unfold_locales
  apply (rule pi_lmi)
  done

definition lmi_from_list_dj :: "('k\<times>'v) list \<Rightarrow> ('k,'v) lmi" where
  "lmi_from_list_dj \<equiv> id"

lemma lmi_from_list_dj_correct: 
  assumes [simp]: "distinct (map fst l)"
  shows "lmi.\<alpha> (lmi_from_list_dj l) = map_of l"
        "lmi.invar (lmi_from_list_dj l)"
  by (auto simp add: lmi_from_list_dj_def icf_rec_unf lmi_\<alpha>_def lmi_invar_def)

text \<open>Code generator test\<close>
definition "test_codegen \<equiv> (
  lmi.add ,
  lmi.add_dj ,
  lmi.ball ,
  lmi.bex ,
  lmi.delete ,
  lmi.empty ,
  lmi.isEmpty ,
  lmi.isSng ,
  lmi.iterate ,
  lmi.iteratei ,
  lmi.list_it ,
  lmi.lookup ,
  lmi.restrict ,
  lmi.sel ,
  lmi.size ,
  lmi.size_abort ,
  lmi.sng ,
  lmi.to_list ,
  lmi.to_map ,
  lmi.update ,
  lmi.update_dj,
  lmi_from_list_dj
  )"

export_code test_codegen checking SML

end
