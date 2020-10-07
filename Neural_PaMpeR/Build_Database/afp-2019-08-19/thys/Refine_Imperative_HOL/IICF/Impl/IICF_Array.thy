section \<open>Plain Arrays Implementing List Interface\<close>
theory IICF_Array
imports "../Intf/IICF_List"
begin

  text \<open>Lists of fixed length are directly implemented with arrays. \<close>
  definition "is_array l p \<equiv> p\<mapsto>\<^sub>al"

  lemma is_array_precise[safe_constraint_rules]: "precise is_array"
    apply rule
    unfolding is_array_def
    apply prec_extract_eqs
    by simp

  definition array_assn where "array_assn A \<equiv> hr_comp is_array (\<langle>the_pure A\<rangle>list_rel)"
  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "array_assn A" for A]

  definition [simp,code_unfold]: "heap_array_empty \<equiv> Array.of_list []"
  definition [simp,code_unfold]: "heap_array_set p i v \<equiv> Array.upd i v p" 



context 
  notes [fcomp_norm_unfold] = array_assn_def[symmetric]
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI]
  notes [simp] = pure_def hn_ctxt_def is_array_def invalid_assn_def
begin  

  lemma array_empty_hnr_aux: "(uncurry0 heap_array_empty,uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a is_array"
    by sep_auto
  sepref_decl_impl (no_register) array_empty: array_empty_hnr_aux .

  lemma array_replicate_hnr_aux: 
    "(uncurry Array.new, uncurry (RETURN oo op_list_replicate)) 
      \<in> nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a is_array"
    by (sep_auto)
  sepref_decl_impl (no_register) array_replicate: array_replicate_hnr_aux .
   
  definition [simp]: "op_array_replicate \<equiv> op_list_replicate"
  sepref_register op_array_replicate
  lemma array_fold_custom_replicate:
    "replicate = op_array_replicate"
    "op_list_replicate = op_array_replicate"
    "mop_list_replicate = RETURN oo op_array_replicate"
    by (auto simp: op_array_replicate_def intro!: ext)
  lemmas array_replicate_custom_hnr[sepref_fr_rules] = array_replicate_hnr[unfolded array_fold_custom_replicate]

  lemma array_of_list_hnr_aux: "(Array.of_list,RETURN o op_list_copy) \<in> (list_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a is_array"
    unfolding list_assn_pure_conv
    by (sep_auto)
  sepref_decl_impl (no_register) array_of_list: array_of_list_hnr_aux .

  definition [simp]: "op_array_of_list \<equiv> op_list_copy"
  sepref_register op_array_of_list
  lemma array_fold_custom_of_list:
    "l = op_array_of_list l"
    "op_list_copy = op_array_of_list"
    "mop_list_copy = RETURN o op_array_of_list"
    by (auto intro!: ext)
  lemmas array_of_list_custom_hnr[sepref_fr_rules] = array_of_list_hnr[folded op_array_of_list_def]

  lemma array_copy_hnr_aux: "(array_copy, RETURN o op_list_copy) \<in> is_array\<^sup>k \<rightarrow>\<^sub>a is_array"
    by sep_auto
  sepref_decl_impl array_copy: array_copy_hnr_aux .


  lemma array_get_hnr_aux: "(uncurry Array.nth,uncurry (RETURN oo op_list_get)) \<in> [\<lambda>(l,i). i<length l]\<^sub>a is_array\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> id_assn"  
    by sep_auto
  sepref_decl_impl array_get: array_get_hnr_aux .  

  lemma array_set_hnr_aux: "(uncurry2 heap_array_set,uncurry2 (RETURN ooo op_list_set)) \<in> [\<lambda>((l,i),_). i<length l]\<^sub>a is_array\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> is_array"  
    by sep_auto
  sepref_decl_impl array_set: array_set_hnr_aux .

  lemma array_length_hnr_aux: "(Array.len,RETURN o op_list_length) \<in> is_array\<^sup>k \<rightarrow>\<^sub>a nat_assn"  
    by sep_auto
  sepref_decl_impl array_length: array_length_hnr_aux . 

end

definition [simp]: "op_array_empty \<equiv> op_list_empty"
interpretation array: list_custom_empty "array_assn A" heap_array_empty op_array_empty
  apply unfold_locales
  apply (rule array_empty_hnr[simplified pre_list_empty_def])
  by (auto)



end
