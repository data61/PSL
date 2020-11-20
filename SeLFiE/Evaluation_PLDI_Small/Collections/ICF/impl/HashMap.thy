(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
section \<open>\isaheader{Hash Maps}\<close>
theory HashMap 
  imports HashMap_Impl 
begin
text_raw \<open>\label{thy:HashMap}\<close>

(*@impl Map
  @type 'a::hashable hm
  @abbrv hm,h
  Hash maps based on red-black trees.
*)

subsection "Type definition"

typedef (overloaded) ('k, 'v) hashmap = "{hm :: ('k :: hashable, 'v) hm_impl. HashMap_Impl.invar hm}"
  morphisms impl_of_RBT_HM RBT_HM
proof
  show "HashMap_Impl.empty () \<in> {hm. HashMap_Impl.invar hm}"
    by(simp add: HashMap_Impl.empty_correct')
qed

lemma impl_of_RBT_HM_invar [simp, intro!]: "HashMap_Impl.invar (impl_of_RBT_HM hm)"
using impl_of_RBT_HM[of hm] by simp

lemma RBT_HM_imp_of_RBT_HM [code abstype]:
  "RBT_HM (impl_of_RBT_HM hm) = hm"
by(fact impl_of_RBT_HM_inverse)

definition hm_empty_const :: "('k :: hashable, 'v) hashmap"
where "hm_empty_const = RBT_HM (HashMap_Impl.empty ())"

definition hm_empty :: "unit \<Rightarrow> ('k :: hashable, 'v) hashmap"
where "hm_empty = (\<lambda>_. hm_empty_const)"

definition "hm_lookup k hm == HashMap_Impl.lookup k (impl_of_RBT_HM hm)"

definition hm_update :: "('k :: hashable) \<Rightarrow> 'v \<Rightarrow> ('k, 'v) hashmap \<Rightarrow> ('k, 'v) hashmap"
where "hm_update k v hm = RBT_HM (HashMap_Impl.update k v (impl_of_RBT_HM hm))"

definition hm_update_dj :: "('k :: hashable) \<Rightarrow> 'v \<Rightarrow> ('k, 'v) hashmap \<Rightarrow> ('k, 'v) hashmap"
where "hm_update_dj = hm_update"

definition hm_delete :: "('k :: hashable) \<Rightarrow> ('k, 'v) hashmap \<Rightarrow> ('k, 'v) hashmap"
where "hm_delete k hm = RBT_HM (HashMap_Impl.delete k (impl_of_RBT_HM hm))"

definition hm_isEmpty :: "('k :: hashable, 'v) hashmap \<Rightarrow> bool"
where "hm_isEmpty hm = HashMap_Impl.isEmpty (impl_of_RBT_HM hm)"

(*definition hm_sel :: "('k :: hashable, 'v) hashmap \<Rightarrow> ('k \<times> 'v \<rightharpoonup> 'a) \<rightharpoonup> 'a"
  where "hm_sel hm = HashMap_Impl.sel (impl_of_RBT_HM hm)"*)

(*definition "hm_sel' = MapGA.sel_sel' hm_sel"*)

definition "hm_iteratei hm == HashMap_Impl.iteratei (impl_of_RBT_HM hm)"

lemma impl_of_hm_empty [simp, code abstract]:
  "impl_of_RBT_HM (hm_empty_const) = HashMap_Impl.empty ()"
by(simp add: hm_empty_const_def empty_correct' RBT_HM_inverse)

lemma impl_of_hm_update [simp, code abstract]:
  "impl_of_RBT_HM (hm_update k v hm) = HashMap_Impl.update k v (impl_of_RBT_HM hm)"
by(simp add: hm_update_def update_correct' RBT_HM_inverse)

lemma impl_of_hm_delete [simp, code abstract]:
  "impl_of_RBT_HM (hm_delete k hm) = HashMap_Impl.delete k (impl_of_RBT_HM hm)"
by(simp add: hm_delete_def delete_correct' RBT_HM_inverse)

subsection "Correctness w.r.t. Map"
text \<open>
  The next lemmas establish the correctness of the hashmap operations w.r.t. the 
  associated map. This is achieved by chaining the correctness lemmas of the 
  concrete hashmap w.r.t. the abstract hashmap and the correctness lemmas of the
  abstract hashmap w.r.t. maps.
\<close>

type_synonym ('k, 'v) hm = "('k, 'v) hashmap"

  \<comment> \<open>Abstract concrete hashmap to map\<close>
definition "hm_\<alpha> == ahm_\<alpha> \<circ> hm_\<alpha>' \<circ> impl_of_RBT_HM"

abbreviation (input) hm_invar :: "('k :: hashable, 'v) hashmap \<Rightarrow> bool"
where "hm_invar == \<lambda>_. True"


lemma hm_aux_correct:
  "hm_\<alpha> (hm_empty ()) = Map.empty "
  "hm_lookup k m = hm_\<alpha> m k"
  "hm_\<alpha> (hm_update k v m) = (hm_\<alpha> m)(k\<mapsto>v)"
  "hm_\<alpha> (hm_delete k m) = (hm_\<alpha> m) |` (-{k})"
by(auto simp add: hm_\<alpha>_def hm_correct' hm_empty_def ahm_correct hm_lookup_def)

lemma hm_finite[simp, intro!]:
  "finite (dom (hm_\<alpha> m))"
proof(cases m)
  case (RBT_HM m')
  hence SS: "dom (hm_\<alpha> m) \<subseteq> \<Union>{ dom (lm.\<alpha> lm) | lm hc. rm.\<alpha> m' hc = Some lm }"
    apply(clarsimp simp add: RBT_HM_inverse hm_\<alpha>_def hm_\<alpha>'_def [abs_def] ahm_\<alpha>_def [abs_def])
    apply(auto split: option.split_asm option.split)
    done
  moreover have "finite \<dots>" (is "finite (\<Union>?A)")
  proof
    have "{ dom (lm.\<alpha> lm) | lm hc. rm.\<alpha> m' hc = Some lm } 
          \<subseteq> (\<lambda>hc. dom (lm.\<alpha> (the (rm.\<alpha> m' hc)) )) ` (dom (rm.\<alpha> m'))" 
      (is "?S \<subseteq> _")
      by force
    thus "finite ?A" by(rule finite_subset) auto
  next
    fix M
    assume "M \<in> ?A"
    thus "finite M" by auto
  qed
  ultimately show ?thesis unfolding RBT_HM by(rule finite_subset)
qed


lemma hm_iteratei_impl: 
  "map_iterator (hm_iteratei m) (hm_\<alpha> m)"
  apply (unfold hm_\<alpha>_def hm_iteratei_def o_def)
  apply(rule iteratei_correct'[OF impl_of_RBT_HM_invar])
  done

subsection "Integration in Isabelle Collections Framework"
text \<open>
  In this section, we integrate hashmaps into the Isabelle Collections Framework.
\<close>



definition [icf_rec_def]: "hm_basic_ops \<equiv> \<lparr>
  bmap_op_\<alpha> = hm_\<alpha>,
  bmap_op_invar = \<lambda>_. True,
  bmap_op_empty = hm_empty,
  bmap_op_lookup = hm_lookup,
  bmap_op_update = hm_update,
  bmap_op_update_dj = hm_update, \<comment> \<open>TODO: Optimize bucket-ins here\<close>
  bmap_op_delete = hm_delete,
  bmap_op_list_it = hm_iteratei
\<rparr>"


setup Locale_Code.open_block
interpretation hm_basic: StdBasicMap hm_basic_ops
  apply unfold_locales
  apply (simp_all add: icf_rec_unf hm_aux_correct hm_iteratei_impl)
  done
setup Locale_Code.close_block

definition [icf_rec_def]: "hm_ops \<equiv> hm_basic.dflt_ops"

setup Locale_Code.open_block
interpretation hm: StdMapDefs hm_ops .
interpretation hm: StdMap hm_ops 
  unfolding hm_ops_def
  by (rule hm_basic.dflt_ops_impl)
interpretation hm: StdMap_no_invar hm_ops 
  by unfold_locales (simp add: icf_rec_unf)
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "hm"\<close>

lemma pi_hm[proper_it]:
  shows "proper_it' hm_iteratei hm_iteratei"
  apply (rule proper_it'I)
  unfolding hm_iteratei_def HashMap_Impl.iteratei_alt_def 
  by (intro icf_proper_iteratorI)

interpretation pi_hm: proper_it_loc hm_iteratei hm_iteratei
  apply unfold_locales
  apply (rule pi_hm)
  done

text \<open>Code generator test\<close>

definition test_codegen where "test_codegen \<equiv> (
  hm.add ,
  hm.add_dj ,
  hm.ball ,
  hm.bex ,
  hm.delete ,
  hm.empty ,
  hm.isEmpty ,
  hm.isSng ,
  hm.iterate ,
  hm.iteratei ,
  hm.list_it ,
  hm.lookup ,
  hm.restrict ,
  hm.sel ,
  hm.size ,
  hm.size_abort ,
  hm.sng ,
  hm.to_list ,
  hm.to_map ,
  hm.update ,
  hm.update_dj)"

export_code test_codegen checking SML


end

