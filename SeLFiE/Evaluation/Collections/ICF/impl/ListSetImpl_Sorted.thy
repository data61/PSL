(*  Title:       Isabelle Collections Library
    Author:      Thomas Tuerk <tuerk@in.tum.de>
    Maintainer:  Thomas Tuerk <tuerk@in.tum.de>
*)
section \<open>\isaheader{Set Implementation by sorted Lists}\<close>
theory ListSetImpl_Sorted
imports 
  "../spec/SetSpec"
  "../gen_algo/SetGA"
  "../../Lib/Sorted_List_Operations"
begin
text_raw \<open>\label{thy:ListSetImpl_Sorted}\<close>

(*@impl Set
  @type 'a::linorder lss
  @abbrv lss
  Sets implemented by sorted lists.
*)

type_synonym
  'a lss = "'a list"

subsection "Definitions"
definition lss_\<alpha> :: "'a lss \<Rightarrow> 'a set" where "lss_\<alpha> == set"
definition lss_invar :: "'a::{linorder} lss \<Rightarrow> bool" where "lss_invar l == distinct l \<and> sorted l"
definition lss_empty :: "unit \<Rightarrow> 'a lss" where "lss_empty == (\<lambda>_::unit. [])"
definition lss_memb :: "'a::{linorder} \<Rightarrow> 'a lss \<Rightarrow> bool" where "lss_memb x l == Sorted_List_Operations.memb_sorted l x"
definition lss_ins :: "'a::{linorder} \<Rightarrow> 'a lss \<Rightarrow> 'a lss" where "lss_ins x l == insertion_sort x l"
definition lss_ins_dj :: "'a::{linorder} \<Rightarrow> 'a lss \<Rightarrow> 'a lss" where "lss_ins_dj == lss_ins"

definition lss_delete :: "'a::{linorder} \<Rightarrow> 'a lss \<Rightarrow> 'a lss" where "lss_delete x l == delete_sorted x l"

definition lss_iterateoi :: "'a lss \<Rightarrow> ('a,'\<sigma>) set_iterator" 
where "lss_iterateoi l = foldli l"

definition lss_reverse_iterateoi :: "'a lss \<Rightarrow> ('a,'\<sigma>) set_iterator" 
where "lss_reverse_iterateoi l = foldli (rev l)"

definition lss_iteratei :: "'a lss \<Rightarrow> ('a,'\<sigma>) set_iterator" 
where "lss_iteratei l = foldli l"

definition lss_isEmpty :: "'a lss \<Rightarrow> bool" where "lss_isEmpty s == s=[]"

definition lss_union :: "'a::{linorder} lss \<Rightarrow> 'a lss \<Rightarrow> 'a lss" 
  where "lss_union s1 s2 == Misc.merge s1 s2"
definition lss_union_list :: "'a::{linorder} lss list \<Rightarrow> 'a lss" 
  where "lss_union_list l == merge_list [] l"
definition lss_inter :: "'a::{linorder} lss \<Rightarrow> 'a lss \<Rightarrow> 'a lss" 
  where "lss_inter == inter_sorted"
definition lss_union_dj :: "'a::{linorder} lss \<Rightarrow> 'a lss \<Rightarrow> 'a lss" 
  where "lss_union_dj == lss_union" \<comment> \<open>Union of disjoint sets\<close>

definition lss_image_filter 
  where "lss_image_filter f l = 
         mergesort_remdups (List.map_filter f l)"

definition lss_filter where [code_unfold]: "lss_filter = List.filter"

definition lss_inj_image_filter 
  where "lss_inj_image_filter == lss_image_filter"

definition "lss_image == iflt_image lss_image_filter"
definition "lss_inj_image == iflt_inj_image lss_inj_image_filter"

definition lss_to_list :: "'a lss \<Rightarrow> 'a list" where "lss_to_list == id"
definition list_to_lss :: "'a::{linorder} list \<Rightarrow> 'a lss" where "list_to_lss == mergesort_remdups"

subsection "Correctness"
lemmas lss_defs = 
  lss_\<alpha>_def
  lss_invar_def
  lss_empty_def
  lss_memb_def
  lss_ins_def
  lss_ins_dj_def
  lss_delete_def
  lss_iteratei_def
  lss_isEmpty_def
  lss_union_def
  lss_union_list_def
  lss_inter_def
  lss_union_dj_def
  lss_image_filter_def
  lss_inj_image_filter_def
  lss_image_def
  lss_inj_image_def
  lss_to_list_def
  list_to_lss_def

lemma lss_empty_impl: "set_empty lss_\<alpha> lss_invar lss_empty"
by (unfold_locales) (auto simp add: lss_defs)

lemma lss_memb_impl: "set_memb lss_\<alpha> lss_invar lss_memb"
by (unfold_locales) (auto simp add: lss_defs memb_sorted_correct)

lemma lss_ins_impl: "set_ins lss_\<alpha> lss_invar lss_ins"
by (unfold_locales) (auto simp add: lss_defs insertion_sort_correct)

lemma lss_ins_dj_impl: "set_ins_dj lss_\<alpha> lss_invar lss_ins_dj"
by (unfold_locales) (auto simp add: lss_defs insertion_sort_correct)

lemma lss_delete_impl: "set_delete lss_\<alpha> lss_invar lss_delete"
by(unfold_locales)(auto simp add: lss_delete_def lss_\<alpha>_def lss_invar_def delete_sorted_correct)

lemma lss_\<alpha>_finite[simp, intro!]: "finite (lss_\<alpha> l)"
  by (auto simp add: lss_defs)

lemma lss_is_finite_set: "finite_set lss_\<alpha> lss_invar"
by (unfold_locales) (auto simp add: lss_defs)

lemma lss_iterateoi_impl: "poly_set_iterateoi lss_\<alpha> lss_invar lss_iterateoi"
proof 
  fix l :: "'a::{linorder} list"
  assume invar_l: "lss_invar l"
  show "finite (lss_\<alpha> l)"
    unfolding lss_\<alpha>_def by simp

  from invar_l
  show "set_iterator_linord (lss_iterateoi l) (lss_\<alpha> l)"
    apply (rule_tac set_iterator_linord_I [of "l"])
    apply (simp_all add: lss_\<alpha>_def lss_invar_def lss_iterateoi_def)
  done
qed

lemma lss_reverse_iterateoi_impl: "poly_set_rev_iterateoi lss_\<alpha> lss_invar lss_reverse_iterateoi"
proof 
  fix l :: "'a list"
  assume invar_l: "lss_invar l"
  show "finite (lss_\<alpha> l)"
    unfolding lss_\<alpha>_def by simp

  from invar_l
  show "set_iterator_rev_linord (lss_reverse_iterateoi l) (lss_\<alpha> l)"
    apply (rule_tac set_iterator_rev_linord_I [of "rev l"])
    apply (simp_all add: lss_\<alpha>_def lss_invar_def lss_reverse_iterateoi_def)
  done
qed

lemma lss_iteratei_impl: "poly_set_iteratei lss_\<alpha> lss_invar lss_iteratei"
proof 
  fix l :: "'a list"
  assume invar_l: "lss_invar l"
  show "finite (lss_\<alpha> l)"
    unfolding lss_\<alpha>_def by simp

  from invar_l
  show "set_iterator (lss_iteratei l) (lss_\<alpha> l)"
    apply (rule_tac set_iterator_I [of "l"])
    apply (simp_all add: lss_\<alpha>_def lss_invar_def lss_iteratei_def)
  done
qed

lemma lss_isEmpty_impl: "set_isEmpty lss_\<alpha> lss_invar lss_isEmpty"
by(unfold_locales)(auto simp add: lss_defs)

lemma lss_inter_impl: "set_inter lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_inter"
by (unfold_locales) (auto simp add: lss_defs inter_sorted_correct)

lemma lss_union_impl: "set_union lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_union"
by (unfold_locales) (auto simp add: lss_defs merge_correct)

lemma lss_union_list_impl: "set_union_list lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_union_list"
proof 
  fix l :: "'a::{linorder} lss list"
  assume "\<forall>s1\<in>set l. lss_invar s1"

  with merge_list_correct [of l "[]"]
  show "lss_\<alpha> (lss_union_list l) = \<Union>{lss_\<alpha> s1 |s1. s1 \<in> set l}"
       "lss_invar (lss_union_list l)"
    by (auto simp add: lss_defs)
qed

lemma lss_union_dj_impl: "set_union_dj lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_union_dj"
by (unfold_locales) (auto simp add: lss_defs merge_correct)

lemma lss_image_filter_impl : "set_image_filter lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_image_filter"
apply (unfold_locales)
apply (simp_all add: 
  lss_invar_def lss_image_filter_def lss_\<alpha>_def mergesort_remdups_correct
  set_map_filter Bex_def)
done

lemma lss_inj_image_filter_impl : "set_inj_image_filter lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_inj_image_filter"
apply (unfold_locales)
apply (simp_all add: lss_invar_def lss_inj_image_filter_def lss_image_filter_def
                     mergesort_remdups_correct lss_\<alpha>_def
                     set_map_filter Bex_def)
done

lemma lss_filter_impl : "set_filter lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_filter"
apply (unfold_locales)
apply (simp_all add: lss_invar_def lss_filter_def sorted_filter lss_\<alpha>_def
                     set_map_filter Bex_def sorted_filter')
done

lemmas lss_image_impl = iflt_image_correct[OF lss_image_filter_impl, folded lss_image_def]
lemmas lss_inj_image_impl = iflt_inj_image_correct[OF lss_inj_image_filter_impl, folded lss_inj_image_def]

lemma lss_to_list_impl: "set_to_list lss_\<alpha> lss_invar lss_to_list"
by(unfold_locales)(auto simp add: lss_defs)

lemma list_to_lss_impl: "list_to_set lss_\<alpha> lss_invar list_to_lss"
  by (unfold_locales) (auto simp add: lss_defs mergesort_remdups_correct)


definition lss_basic_ops :: "('x::linorder,'x lss) oset_basic_ops" 
  where [icf_rec_def]: "lss_basic_ops \<equiv> \<lparr>
    bset_op_\<alpha> = lss_\<alpha>,
    bset_op_invar = lss_invar,
    bset_op_empty = lss_empty,
    bset_op_memb = lss_memb,
    bset_op_ins = lss_ins,
    bset_op_ins_dj = lss_ins_dj,
    bset_op_delete = lss_delete,
    bset_op_list_it = lss_iteratei,
    bset_op_ordered_list_it = lss_iterateoi,
    bset_op_rev_list_it = lss_reverse_iterateoi
  \<rparr>"

setup Locale_Code.open_block
interpretation lss_basic: StdBasicOSet lss_basic_ops
  apply (rule StdBasicOSet.intro)
  apply (rule StdBasicSet.intro)
  apply (simp_all add: icf_rec_unf)
  apply (rule lss_empty_impl lss_memb_impl lss_ins_impl lss_ins_dj_impl
    lss_delete_impl lss_iteratei_impl lss_iterateoi_impl 
    lss_reverse_iterateoi_impl)+
  done
setup Locale_Code.close_block

definition [icf_rec_def]: "lss_ops \<equiv> lss_basic.dflt_oops \<lparr>
  set_op_isEmpty := lss_isEmpty,
  set_op_union := lss_union,
  set_op_union_dj := lss_union_dj,
  set_op_filter := lss_filter,
  set_op_to_list := lss_to_list,
  set_op_from_list := list_to_lss
  \<rparr>"

setup Locale_Code.open_block
interpretation lss: StdOSetDefs lss_ops .
interpretation lss: StdOSet lss_ops
proof -
  interpret aux: StdOSet lss_basic.dflt_oops
    by (rule lss_basic.dflt_oops_impl)

  show "StdOSet lss_ops"
    unfolding lss_ops_def
    apply (rule StdOSet_intro)
    apply icf_locales
    apply (simp_all add: icf_rec_unf
      lss_isEmpty_impl lss_union_impl lss_union_dj_impl lss_to_list_impl
      lss_filter_impl
      list_to_lss_impl
    )
    done
qed
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "lss"\<close>

lemma pi_lss[proper_it]: 
  "proper_it' lss_iteratei lss_iteratei"
  apply (rule proper_it'I)
  unfolding lss_iteratei_def
  by (intro icf_proper_iteratorI)

interpretation pi_lss: proper_it_loc lss_iteratei lss_iteratei
  apply unfold_locales by (rule pi_lss)

definition test_codegen where "test_codegen \<equiv> (
  lss.empty,
  lss.memb,
  lss.ins,
  lss.delete,
  lss.list_it,
  lss.sng,
  lss.isEmpty,
  lss.isSng,
  lss.ball,
  lss.bex,
  lss.size,
  lss.size_abort,
  lss.union,
  lss.union_dj,
  lss.diff,
  lss.filter,
  lss.inter,
  lss.subset,
  lss.equal,
  lss.disjoint,
  lss.disjoint_witness,
  lss.sel,
  lss.to_list,
  lss.from_list
)"

export_code test_codegen checking SML

end
