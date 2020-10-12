section \<open>Multisets by Lists\<close>
theory IICF_List_Mset
imports "../Intf/IICF_Multiset"
begin

subsection \<open>Abstract Operations\<close>
  definition "list_mset_rel \<equiv> br mset (\<lambda>_. True)"

  lemma lms_empty_aref: "([],op_mset_empty) \<in> list_mset_rel"
    unfolding list_mset_rel_def by (auto simp: in_br_conv)

  (*definition [simp]: "list_single x \<equiv> [x]"
  lemma lms_single_aref: "(list_single,op_mset_single) \<in> Id \<rightarrow> list_mset_rel"  
    unfolding list_mset_rel_def by (auto simp: in_br_conv split: list.splits)*)

  lemma lms_is_empty_aref: "(is_Nil,op_mset_is_empty) \<in> list_mset_rel \<rightarrow> bool_rel"  
    unfolding list_mset_rel_def by (auto simp: in_br_conv split: list.splits)

  lemma lms_insert_aref: "((#), op_mset_insert) \<in> Id \<rightarrow> list_mset_rel \<rightarrow> list_mset_rel"
    unfolding list_mset_rel_def by (auto simp: in_br_conv)

  lemma lms_union_aref: "((@), op_mset_plus) \<in> list_mset_rel \<rightarrow> list_mset_rel \<rightarrow> list_mset_rel"
    unfolding list_mset_rel_def by (auto simp: in_br_conv)

  lemma lms_pick_aref: "(\<lambda>x#l \<Rightarrow> RETURN (x,l), mop_mset_pick) \<in> list_mset_rel \<rightarrow> \<langle>Id \<times>\<^sub>r list_mset_rel\<rangle>nres_rel"
    unfolding list_mset_rel_def mop_mset_pick_alt[abs_def]
    apply1 (refine_vcg nres_relI fun_relI)
    apply1 (clarsimp simp: in_br_conv neq_Nil_conv)
    apply1 (refine_vcg RETURN_SPEC_refine)
    applyS (clarsimp simp: in_br_conv algebra_simps)
    done

  definition "list_contains x l \<equiv>  list_ex ((=) x) l"
  lemma lms_contains_aref: "(list_contains, op_mset_contains) \<in> Id \<rightarrow> list_mset_rel \<rightarrow> bool_rel"  
    unfolding list_mset_rel_def list_contains_def[abs_def]
    by (auto simp: in_br_conv list_ex_iff in_multiset_in_set)
    
  fun list_remove1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "list_remove1 x [] = []"
  | "list_remove1 x (y#ys) = (if x=y then ys else y#list_remove1 x ys)"

  lemma mset_list_remove1[simp]: "mset (list_remove1 x l) = mset l - {#x#}"
    apply (induction l) 
    applyS simp
    by (clarsimp simp: algebra_simps)
    
  lemma lms_remove_aref: "(list_remove1, op_mset_delete) \<in> Id \<rightarrow> list_mset_rel \<rightarrow> list_mset_rel"  
    unfolding list_mset_rel_def by (auto simp: in_br_conv)
    
  fun list_count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
    "list_count _ [] = 0"
  | "list_count x (y#ys) = (if x=y then 1 + list_count x ys else list_count x ys)"  
    
  lemma mset_list_count[simp]: "list_count x ys = count (mset ys) x"
    by (induction ys) auto

  lemma lms_count_aref: "(list_count, op_mset_count) \<in> Id \<rightarrow> list_mset_rel \<rightarrow> nat_rel"  
    unfolding list_mset_rel_def by (auto simp: in_br_conv)


  definition list_remove_all :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "list_remove_all xs ys \<equiv> fold list_remove1 ys xs"
  lemma list_remove_all_mset[simp]: "mset (list_remove_all xs ys) = mset xs - mset ys"  
    unfolding list_remove_all_def
    by (induction ys arbitrary: xs) (auto simp: algebra_simps)

  lemma lms_minus_aref: "(list_remove_all,op_mset_minus) \<in> list_mset_rel \<rightarrow> list_mset_rel \<rightarrow> list_mset_rel"
    unfolding list_mset_rel_def by (auto simp: in_br_conv)
    
subsection \<open>Declaration of Implementations\<close>

  definition "list_mset_assn A \<equiv> pure (list_mset_rel O \<langle>the_pure A\<rangle>mset_rel)"
  declare list_mset_assn_def[symmetric,fcomp_norm_unfold]
  lemma [safe_constraint_rules]: "is_pure (list_mset_assn A)" unfolding list_mset_assn_def by simp

  sepref_decl_impl (no_register) lms_empty: lms_empty_aref[sepref_param] .
  (*sepref_decl_impl (no_register) lms_single: lms_single_aref[sepref_param] .*)

  definition [simp]: "op_list_mset_empty \<equiv> op_mset_empty"
  lemma lms_fold_custom_empty:
    "{#} = op_list_mset_empty"
    "op_mset_empty = op_list_mset_empty"
    by auto
  sepref_register op_list_mset_empty
  lemmas [sepref_fr_rules] = lms_empty_hnr[folded op_list_mset_empty_def]

  (*  
  definition [simp]: "op_list_mset_single \<equiv> op_mset_single"
  lemma lms_fold_custom_single:
    "{#x#} = op_list_mset_single x"
    "op_mset_single x = op_list_mset_single x"
    by auto
  sepref_register op_list_mset_single
  lemmas [sepref_fr_rules] = lms_single_hnr[folded op_list_mset_single_def]
  *)

  sepref_decl_impl lms_is_empty: lms_is_empty_aref[sepref_param] .
  sepref_decl_impl lms_insert: lms_insert_aref[sepref_param] .
  sepref_decl_impl lms_union: lms_union_aref[sepref_param] .

  \<comment> \<open>Some extra work is required for nondetermistic ops\<close>
  lemma lms_pick_aref': 
    "(\<lambda>x#l \<Rightarrow> return (x,l), mop_mset_pick) \<in> (pure list_mset_rel)\<^sup>k \<rightarrow>\<^sub>a prod_assn id_assn (pure list_mset_rel)"
    apply (simp only: prod_assn_pure_conv)
    apply sepref_to_hoare
    apply (sep_auto simp: refine_pw_simps list_mset_rel_def in_br_conv algebra_simps eintros del: exI)
    done
  sepref_decl_impl (ismop) lms_pick: lms_pick_aref' .
  sepref_decl_impl lms_contains: lms_contains_aref[sepref_param] .
  sepref_decl_impl lms_remove: lms_remove_aref[sepref_param] .
  sepref_decl_impl lms_count: lms_count_aref[sepref_param] .
  sepref_decl_impl lms_minus: lms_minus_aref[sepref_param] .

end
