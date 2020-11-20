(*  Title:       Isabelle Collections Library
    Author:      Thomas Tuerk <tuerk@in.tum.de>
    Maintainer:  Thomas Tuerk <tuerk@in.tum.de>
*)
section \<open>\isaheader{Set Implementation by non-distinct Lists}\<close>
theory ListSetImpl_NotDist
imports 
  "../spec/SetSpec"
  "../gen_algo/SetGA"
  (*"../common/ListAdd"*)
begin
text_raw \<open>\label{thy:ListSetImpl_NotDist}\<close>

(*@impl Set
  @type 'a lsnd
  @abbrv lsnd
  Sets implemented by lists that may contain duplicate elements. 
  Insertion is quick, but other operations are less performant than on 
  lists with distinct elements.
*)

type_synonym
  'a lsnd = "'a list"

subsection "Definitions"

definition lsnd_\<alpha> :: "'a lsnd \<Rightarrow> 'a set" where "lsnd_\<alpha> == set"
abbreviation (input) lsnd_invar 
  :: "'a lsnd \<Rightarrow> bool" where "lsnd_invar == (\<lambda>_. True)"
definition lsnd_empty :: "unit \<Rightarrow> 'a lsnd" where "lsnd_empty == (\<lambda>_::unit. [])"
definition lsnd_memb :: "'a \<Rightarrow> 'a lsnd \<Rightarrow> bool" where "lsnd_memb x l == List.member l x"
definition lsnd_ins :: "'a \<Rightarrow> 'a lsnd \<Rightarrow> 'a lsnd" where "lsnd_ins x l == x#l"
definition lsnd_ins_dj :: "'a \<Rightarrow> 'a lsnd \<Rightarrow> 'a lsnd" where "lsnd_ins_dj x l == x#l"

definition lsnd_delete :: "'a \<Rightarrow> 'a lsnd \<Rightarrow> 'a lsnd" where "lsnd_delete x l == remove_rev x l"

definition lsnd_iteratei :: "'a lsnd \<Rightarrow> ('a,'\<sigma>) set_iterator" 
where "lsnd_iteratei l = foldli (remdups l)"

definition lsnd_isEmpty :: "'a lsnd \<Rightarrow> bool" where "lsnd_isEmpty s == s=[]"

definition lsnd_union :: "'a lsnd \<Rightarrow> 'a lsnd \<Rightarrow> 'a lsnd" 
  where "lsnd_union s1 s2 == revg s1 s2"
definition lsnd_union_dj :: "'a lsnd \<Rightarrow> 'a lsnd \<Rightarrow> 'a lsnd" 
  where "lsnd_union_dj s1 s2 == revg s1 s2" \<comment> \<open>Union of disjoint sets\<close>

definition lsnd_to_list :: "'a lsnd \<Rightarrow> 'a list" where "lsnd_to_list == remdups"
definition list_to_lsnd :: "'a list \<Rightarrow> 'a lsnd" where "list_to_lsnd == id"

subsection "Correctness"
lemmas lsnd_defs = 
  lsnd_\<alpha>_def
  lsnd_empty_def
  lsnd_memb_def
  lsnd_ins_def
  lsnd_ins_dj_def
  lsnd_delete_def
  lsnd_iteratei_def
  lsnd_isEmpty_def
  lsnd_union_def
  lsnd_union_dj_def
  lsnd_to_list_def
  list_to_lsnd_def

lemma lsnd_empty_impl: "set_empty lsnd_\<alpha> lsnd_invar lsnd_empty"
by (unfold_locales) (auto simp add: lsnd_defs)

lemma lsnd_memb_impl: "set_memb lsnd_\<alpha> lsnd_invar lsnd_memb"
by (unfold_locales)(auto simp add: lsnd_defs in_set_member)

lemma lsnd_ins_impl: "set_ins lsnd_\<alpha> lsnd_invar lsnd_ins"
by (unfold_locales) (auto simp add: lsnd_defs in_set_member)

lemma lsnd_ins_dj_impl: "set_ins_dj lsnd_\<alpha> lsnd_invar lsnd_ins_dj"
by (unfold_locales) (auto simp add: lsnd_defs)

lemma lsnd_delete_impl: "set_delete lsnd_\<alpha> lsnd_invar lsnd_delete"
by (unfold_locales) (auto simp add: lsnd_delete_def lsnd_\<alpha>_def remove_rev_alt_def)

lemma lsnd_\<alpha>_finite[simp, intro!]: "finite (lsnd_\<alpha> l)"
  by (auto simp add: lsnd_defs)

lemma lsnd_is_finite_set: "finite_set lsnd_\<alpha> lsnd_invar"
by (unfold_locales) (auto simp add: lsnd_defs)

lemma lsnd_iteratei_impl: "poly_set_iteratei lsnd_\<alpha> lsnd_invar lsnd_iteratei"
proof 
  fix l :: "'a list"
  show "finite (lsnd_\<alpha> l)"
    unfolding lsnd_\<alpha>_def by simp

  show "set_iterator (lsnd_iteratei l) (lsnd_\<alpha> l)"
    apply (rule set_iterator_I [of "remdups l"])
    apply (simp_all add: lsnd_\<alpha>_def lsnd_iteratei_def)
  done
qed

lemma lsnd_isEmpty_impl: "set_isEmpty lsnd_\<alpha> lsnd_invar lsnd_isEmpty"
by(unfold_locales)(auto simp add: lsnd_defs)

lemma lsnd_union_impl: "set_union lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_union"
by(unfold_locales)(auto simp add: lsnd_defs)

lemma lsnd_union_dj_impl: "set_union_dj lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_union_dj"
by(unfold_locales)(auto simp add: lsnd_defs)

lemma lsnd_to_list_impl: "set_to_list lsnd_\<alpha> lsnd_invar lsnd_to_list"
by(unfold_locales)(auto simp add: lsnd_defs)

lemma list_to_lsnd_impl: "list_to_set lsnd_\<alpha> lsnd_invar list_to_lsnd"
by(unfold_locales)(auto simp add: lsnd_defs)

definition lsnd_basic_ops :: "('x,'x lsnd) set_basic_ops" 
  where [icf_rec_def]: "lsnd_basic_ops \<equiv> \<lparr>
    bset_op_\<alpha> = lsnd_\<alpha>,
    bset_op_invar = lsnd_invar,
    bset_op_empty = lsnd_empty,
    bset_op_memb = lsnd_memb,
    bset_op_ins = lsnd_ins,
    bset_op_ins_dj = lsnd_ins_dj,
    bset_op_delete = lsnd_delete,
    bset_op_list_it = lsnd_iteratei
  \<rparr>"

setup Locale_Code.open_block
interpretation lsnd_basic: StdBasicSet lsnd_basic_ops
  apply (rule StdBasicSet.intro)
  apply (simp_all add: icf_rec_unf)
  apply (rule lsnd_empty_impl lsnd_memb_impl lsnd_ins_impl lsnd_ins_dj_impl
    lsnd_delete_impl lsnd_iteratei_impl)+
  done
setup Locale_Code.close_block


definition [icf_rec_def]: "lsnd_ops \<equiv> lsnd_basic.dflt_ops \<lparr>
  set_op_isEmpty := lsnd_isEmpty,
  set_op_union := lsnd_union,
  set_op_union_dj := lsnd_union_dj,
  set_op_to_list := lsnd_to_list,
  set_op_from_list := list_to_lsnd
  \<rparr>"

setup Locale_Code.open_block
interpretation lsnd: StdSetDefs lsnd_ops .
interpretation lsnd: StdSet lsnd_ops
proof -
  interpret aux: StdSet lsnd_basic.dflt_ops
    by (rule lsnd_basic.dflt_ops_impl)

  show "StdSet lsnd_ops"
    unfolding lsnd_ops_def
    apply (rule StdSet_intro)
    apply icf_locales
    apply (simp_all add: icf_rec_unf
      lsnd_isEmpty_impl lsnd_union_impl lsnd_union_dj_impl lsnd_to_list_impl
      list_to_lsnd_impl
    )
    done
qed
interpretation lsnd: StdSet_no_invar lsnd_ops
  by unfold_locales (simp add: icf_rec_unf)
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "lsnd"\<close>

lemma pi_lsnd[proper_it]: 
  "proper_it' lsnd_iteratei lsnd_iteratei"
  apply (rule proper_it'I)
  unfolding lsnd_iteratei_def
  by (intro icf_proper_iteratorI)

interpretation pi_lsnd: proper_it_loc lsnd_iteratei lsnd_iteratei
  apply unfold_locales by (rule pi_lsnd)

definition test_codegen where "test_codegen \<equiv> (
  lsnd.empty,
  lsnd.memb,
  lsnd.ins,
  lsnd.delete,
  lsnd.list_it,
  lsnd.sng,
  lsnd.isEmpty,
  lsnd.isSng,
  lsnd.ball,
  lsnd.bex,
  lsnd.size,
  lsnd.size_abort,
  lsnd.union,
  lsnd.union_dj,
  lsnd.diff,
  lsnd.filter,
  lsnd.inter,
  lsnd.subset,
  lsnd.equal,
  lsnd.disjoint,
  lsnd.disjoint_witness,
  lsnd.sel,
  lsnd.to_list,
  lsnd.from_list
)"

export_code test_codegen checking SML

end
