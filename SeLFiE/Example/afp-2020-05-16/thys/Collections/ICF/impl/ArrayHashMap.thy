(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
section \<open>\isaheader{Array-based hash maps without explicit invariants}\<close>
theory ArrayHashMap 
  imports ArrayHashMap_Impl
begin

(*@impl Map
  @type ('k,'v) ahm
  @abbrv ahm,a
  Array based hash maps without explicit invariant.
*)

subsection \<open>Abstract type definition\<close>

typedef (overloaded) ('key :: hashable, 'val) hashmap =
  "{hm :: ('key, 'val) ArrayHashMap_Impl.hashmap. ArrayHashMap_Impl.ahm_invar hm}"
  morphisms impl_of HashMap
proof
  interpret map_empty ArrayHashMap_Impl.ahm_\<alpha> ArrayHashMap_Impl.ahm_invar ArrayHashMap_Impl.ahm_empty
    by(rule ahm_empty_impl)
  show "ArrayHashMap_Impl.ahm_empty () \<in> ?hashmap"
    by(simp add: empty_correct)
qed

type_synonym ('k,'v) ahm = "('k,'v) hashmap"

lemma ahm_invar_impl_of [simp, intro]: "ArrayHashMap_Impl.ahm_invar (impl_of hm)"
using impl_of[of hm] by simp

lemma HashMap_impl_of [code abstype]: "HashMap (impl_of t) = t"
by(rule impl_of_inverse)

subsection \<open>Primitive operations\<close>

definition ahm_empty_const :: "('key :: hashable, 'val) hashmap"
where "ahm_empty_const \<equiv> (HashMap (ArrayHashMap_Impl.ahm_empty ()))"

definition ahm_empty :: "unit \<Rightarrow> ('key :: hashable, 'val) hashmap"
where "ahm_empty \<equiv> \<lambda>_. ahm_empty_const"

definition ahm_\<alpha> :: "('key :: hashable, 'val) hashmap \<Rightarrow> 'key \<Rightarrow> 'val option"
where "ahm_\<alpha> hm = ArrayHashMap_Impl.ahm_\<alpha> (impl_of hm)"

definition ahm_lookup :: "'key \<Rightarrow> ('key :: hashable, 'val) hashmap \<Rightarrow> 'val option"
where "ahm_lookup k hm = ArrayHashMap_Impl.ahm_lookup k (impl_of hm)"

definition ahm_iteratei :: "('key :: hashable, 'val) hashmap \<Rightarrow> ('key \<times> 'val, '\<sigma>) set_iterator"
where "ahm_iteratei hm = ArrayHashMap_Impl.ahm_iteratei (impl_of hm)"

definition ahm_update :: "'key \<Rightarrow> 'val \<Rightarrow> ('key :: hashable, 'val) hashmap \<Rightarrow> ('key, 'val) hashmap"
where
  "ahm_update k v hm = HashMap (ArrayHashMap_Impl.ahm_update k v (impl_of hm))"

definition ahm_delete :: "'key \<Rightarrow> ('key :: hashable, 'val) hashmap \<Rightarrow> ('key, 'val) hashmap"
where
  "ahm_delete k hm = HashMap (ArrayHashMap_Impl.ahm_delete k (impl_of hm))"

lemma impl_of_ahm_empty [code abstract]:
  "impl_of ahm_empty_const = ArrayHashMap_Impl.ahm_empty ()"
by(simp add: ahm_empty_const_def HashMap_inverse)

lemma impl_of_ahm_update [code abstract]:
  "impl_of (ahm_update k v hm) = ArrayHashMap_Impl.ahm_update k v (impl_of hm)"
by(simp add: ahm_update_def HashMap_inverse ahm_update_correct)

lemma impl_of_ahm_delete [code abstract]:
  "impl_of (ahm_delete k hm) = ArrayHashMap_Impl.ahm_delete k (impl_of hm)"
by(simp add: ahm_delete_def HashMap_inverse ahm_delete_correct)

lemma finite_dom_ahm_\<alpha>[simp]: "finite (dom (ahm_\<alpha> hm))"
  by (simp add: ahm_\<alpha>_def finite_dom_ahm_\<alpha>)

lemma ahm_empty_correct[simp]: "ahm_\<alpha> (ahm_empty ()) = Map.empty"
  by(simp add: ahm_\<alpha>_def ahm_empty_def ahm_empty_const_def HashMap_inverse)

lemma ahm_lookup_correct[simp]: "ahm_lookup k m = ahm_\<alpha> m k"
  by (simp add: ahm_lookup_def ArrayHashMap_Impl.ahm_lookup_def ahm_\<alpha>_def)

lemma ahm_update_correct[simp]: "ahm_\<alpha> (ahm_update k v hm) = (ahm_\<alpha> hm)(k \<mapsto> v)"
  by (simp add: ahm_\<alpha>_def ahm_update_def ahm_update_correct HashMap_inverse)

lemma ahm_delete_correct[simp]:
  "ahm_\<alpha> (ahm_delete k hm) = (ahm_\<alpha> hm) |` (- {k})"
  by (simp add: ahm_\<alpha>_def ahm_delete_def HashMap_inverse ahm_delete_correct)

lemma ahm_iteratei_impl[simp]: "map_iterator (ahm_iteratei m) (ahm_\<alpha> m)"
  unfolding ahm_iteratei_def ahm_\<alpha>_def
  apply (rule ahm_iteratei_correct)
  by simp

subsection \<open>ICF Integration\<close>

definition [icf_rec_def]: "ahm_basic_ops \<equiv> \<lparr>
  bmap_op_\<alpha> = ahm_\<alpha>,
  bmap_op_invar = \<lambda>_. True,
  bmap_op_empty = ahm_empty,
  bmap_op_lookup = ahm_lookup,
  bmap_op_update = ahm_update,
  bmap_op_update_dj = ahm_update, \<comment> \<open>TODO: We could use a more efficient bucket update here\<close>
  bmap_op_delete = ahm_delete,
  bmap_op_list_it = ahm_iteratei
\<rparr>"

setup Locale_Code.open_block
interpretation ahm_basic: StdBasicMap ahm_basic_ops
  apply unfold_locales
  apply (simp_all add: icf_rec_unf)
  done
setup Locale_Code.close_block

definition [icf_rec_def]: "ahm_ops \<equiv> ahm_basic.dflt_ops"

setup Locale_Code.open_block
interpretation ahm: StdMap ahm_ops 
  unfolding ahm_ops_def
  by (rule ahm_basic.dflt_ops_impl)
interpretation ahm: StdMap_no_invar ahm_ops 
  apply unfold_locales
  unfolding icf_rec_unf ..
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "ahm"\<close>

lemma pi_ahm[proper_it]: 
  "proper_it' ahm_iteratei ahm_iteratei"
  unfolding ahm_iteratei_def[abs_def] 
    ArrayHashMap_Impl.ahm_iteratei_def ArrayHashMap_Impl.ahm_iteratei_aux_def
  apply (rule proper_it'I)
  apply (case_tac "impl_of s")
  apply simp
  apply (rename_tac array nat)
  apply (case_tac array)
  apply simp
  by (intro icf_proper_iteratorI)

interpretation pi_ahm: proper_it_loc ahm_iteratei ahm_iteratei
  apply unfold_locales
  apply (rule pi_ahm)
  done

text \<open>Code generator test\<close>
definition test_codegen where "test_codegen \<equiv> (
  ahm.add ,
  ahm.add_dj ,
  ahm.ball ,
  ahm.bex ,
  ahm.delete ,
  ahm.empty ,
  ahm.isEmpty ,
  ahm.isSng ,
  ahm.iterate ,
  ahm.iteratei ,
  ahm.list_it ,
  ahm.lookup ,
  ahm.restrict ,
  ahm.sel ,
  ahm.size ,
  ahm.size_abort ,
  ahm.sng ,
  ahm.to_list ,
  ahm.to_map ,
  ahm.update ,
  ahm.update_dj)"

export_code test_codegen checking SML

end

