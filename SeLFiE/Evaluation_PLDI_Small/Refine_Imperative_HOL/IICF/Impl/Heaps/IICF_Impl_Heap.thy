section \<open>Implementation of Heaps with Arrays\<close>
theory IICF_Impl_Heap
imports 
  IICF_Abs_Heap 
  "../IICF_HOL_List" 
  "../IICF_Array_List" 
  "HOL-Library.Rewrite"
begin
  text \<open>We implement the heap data structure by an array.
    The implementation is automatically synthesized by the Sepref-tool.
    \<close>
  subsection \<open>Setup of the Sepref-Tool\<close>

  context 
    fixes prio :: "'a::{heap,default} \<Rightarrow> 'b::linorder"
  begin  
    interpretation heapstruct prio .
    definition "heap_rel A \<equiv> hr_comp (hr_comp (arl_assn id_assn) heap_rel1) (\<langle>the_pure A\<rangle>mset_rel)"
  end  

  locale heapstruct_impl = 
    fixes prio :: "'a::{heap,default} \<Rightarrow> 'b::linorder"
  begin  
    sublocale heapstruct prio .

(*  locale heap_impl = heapstruct prio for prio :: "'a::heap \<Rightarrow> 'b::linorder"
  begin*)

    abbreviation "rel \<equiv> arl_assn id_assn"

    sepref_register prio
    lemma [sepref_import_param]: "(prio,prio) \<in> Id \<rightarrow> Id" by simp

    lemma [sepref_import_param]: 
      "((\<le>), (\<le>)::'b \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> bool_rel"
      "((<), (<)::'b \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> bool_rel"
      by simp_all


    sepref_register 
      update_op
      val_of_op
      "PR_CONST prio_of_op"
      exch_op
      valid
      "length::'a list \<Rightarrow> _"
      append_op
      butlast_op
      
      "PR_CONST sink_op"
      "PR_CONST swim_op"
      "PR_CONST repair_op"

    lemma [def_pat_rules]: 
      "heapstruct.prio_of_op$prio \<equiv> PR_CONST prio_of_op"
      "heapstruct.sink_op$prio \<equiv> PR_CONST sink_op"
      "heapstruct.swim_op$prio \<equiv> PR_CONST swim_op"
      "heapstruct.repair_op$prio \<equiv> PR_CONST repair_op"
      by simp_all

  end

  context
    fixes prio :: "'a::{heap,default} \<Rightarrow> 'b::linorder"
  begin

    interpretation heapstruct_impl prio .

subsection \<open>Synthesis of operations\<close>
  text \<open>Note that we have to repeat some boilerplate per operation.
    It is future work to add more automation here.\<close>

  sepref_definition update_impl is "uncurry2 update_op" :: "rel\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a rel"
    unfolding update_op_def[abs_def]
    by sepref
  lemmas [sepref_fr_rules] = update_impl.refine

  sepref_definition val_of_impl is "uncurry val_of_op" :: "rel\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
    unfolding val_of_op_def[abs_def]
    by sepref
  lemmas [sepref_fr_rules] = val_of_impl.refine

  sepref_definition exch_impl is "uncurry2 exch_op" :: "rel\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a rel"
    unfolding exch_op_def[abs_def]
    by sepref
  lemmas [sepref_fr_rules] = exch_impl.refine

  sepref_definition valid_impl is "uncurry (RETURN oo valid)" :: "rel\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    unfolding valid_def[abs_def]
    by sepref
  lemmas [sepref_fr_rules] = valid_impl.refine

  sepref_definition prio_of_impl is "uncurry (PR_CONST prio_of_op)" :: "rel\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
    unfolding prio_of_op_def[abs_def] PR_CONST_def
    by sepref
  lemmas [sepref_fr_rules] = prio_of_impl.refine

  sepref_definition swim_impl is "uncurry (PR_CONST swim_op)" :: "rel\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a rel"
    unfolding swim_op_def[abs_def] parent_def PR_CONST_def
    by sepref

  lemmas [sepref_fr_rules] = swim_impl.refine

  sepref_definition sink_impl is "uncurry (PR_CONST sink_op)" :: "rel\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a rel"
    unfolding sink_op_opt_def[abs_def] sink_op_opt_eq[symmetric,abs_def]  PR_CONST_def
    by sepref
  lemmas [sepref_fr_rules] = sink_impl.refine

  lemmas [fcomp_norm_unfold] = heap_rel_def[symmetric] 

  sepref_definition empty_impl is "uncurry0 empty_op" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a rel"
    unfolding empty_op_def arl.fold_custom_empty
    by sepref

  sepref_decl_impl (no_register) heap_empty: empty_impl.refine[FCOMP empty_op_refine] .

  sepref_definition is_empty_impl is "is_empty_op" :: "rel\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    unfolding is_empty_op_def[abs_def]
    by sepref

  sepref_decl_impl heap_is_empty: is_empty_impl.refine[FCOMP is_empty_op_refine] .  

  sepref_definition insert_impl is "uncurry insert_op" :: "id_assn\<^sup>k *\<^sub>a rel\<^sup>d \<rightarrow>\<^sub>a rel"
    unfolding insert_op_def[abs_def] append_op_def
    by sepref
  sepref_decl_impl heap_insert: insert_impl.refine[FCOMP insert_op_refine] .  
  
  sepref_definition pop_min_impl is "pop_min_op" :: "rel\<^sup>d \<rightarrow>\<^sub>a prod_assn id_assn rel"
    unfolding pop_min_op_def[abs_def] butlast_op_def
    by sepref

  sepref_decl_impl (no_mop) heap_pop_min: pop_min_impl.refine[FCOMP pop_min_op_refine] .

  sepref_definition peek_min_impl is "peek_min_op" :: "rel\<^sup>k \<rightarrow>\<^sub>a id_assn"
    unfolding peek_min_op_def[abs_def]
    by sepref
  sepref_decl_impl (no_mop) heap_peek_min: peek_min_impl.refine[FCOMP peek_min_op_refine] .

end

definition [simp]: "heap_custom_empty \<equiv> op_mset_empty"
interpretation heap: mset_custom_empty 
  "heap_rel prio A" empty_impl heap_custom_empty for prio A
  apply unfold_locales
  apply (rule heap_empty_hnr)
  by simp



subsection \<open>Regression Test\<close>
export_code empty_impl is_empty_impl insert_impl pop_min_impl peek_min_impl checking SML

definition "sort_by_prio prio l \<equiv> do {
  q \<leftarrow> nfoldli l (\<lambda>_. True) (\<lambda>x q. mop_mset_insert x q) heap_custom_empty;
  (l,q) \<leftarrow> WHILET (\<lambda>(l,q). \<not>op_mset_is_empty q) (\<lambda>(l,q). do {
    (x,q) \<leftarrow> mop_prio_pop_min prio q;
    RETURN (l@[x],q)
  }) (op_arl_empty,q);
  RETURN l
}"


context fixes prio:: "'a::{default,heap} \<Rightarrow> 'b::linorder" begin
sepref_definition sort_impl is 
  "sort_by_prio prio" :: "(list_assn (id_assn::'a::{default,heap} \<Rightarrow> _))\<^sup>k \<rightarrow>\<^sub>a arl_assn id_assn"
  unfolding sort_by_prio_def[abs_def]
  by sepref
end
definition "sort_impl_nat \<equiv> sort_impl (id::nat\<Rightarrow>nat) "

export_code sort_impl checking SML

ML \<open>
  @{code sort_impl_nat} (map @{code nat_of_integer} [4,1,7,2,3,9,8,62]) ()
\<close>

hide_const sort_impl sort_impl_nat
hide_fact sort_impl_def sort_impl_nat_def sort_impl.refine

end
