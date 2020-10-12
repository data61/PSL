theory IICF_Array_List
imports 
  "../Intf/IICF_List" 
  Separation_Logic_Imperative_HOL.Array_Blit
begin

  type_synonym 'a array_list = "'a Heap.array \<times> nat"

  definition "is_array_list l \<equiv> \<lambda>(a,n). \<exists>\<^sub>Al'. a \<mapsto>\<^sub>a l' * \<up>(n \<le> length l' \<and> l = take n l' \<and> length l'>0)"

  lemma is_array_list_prec[safe_constraint_rules]: "precise is_array_list"
    unfolding is_array_list_def[abs_def]
    apply(rule preciseI)
    apply(simp split: prod.splits) 
  	using preciseD snga_prec by fastforce

  definition "initial_capacity \<equiv> 16::nat"
  definition "minimum_capacity \<equiv> 16::nat"

  definition "arl_empty \<equiv> do {
    a \<leftarrow> Array.new initial_capacity default;
    return (a,0)
  }"

  definition "arl_empty_sz init_cap \<equiv> do {
    a \<leftarrow> Array.new (max init_cap minimum_capacity) default;
    return (a,0)
  }"

  definition "arl_append \<equiv> \<lambda>(a,n) x. do {
    len \<leftarrow> Array.len a;

    if n<len then do {
      a \<leftarrow> Array.upd n x a;
      return (a,n+1)
    } else do {
      let newcap = 2 * len;
      a \<leftarrow> array_grow a newcap default;
      a \<leftarrow> Array.upd n x a;
      return (a,n+1)
    }
  }"

  definition "arl_copy \<equiv> \<lambda>(a,n). do {
    a \<leftarrow> array_copy a;
    return (a,n)
  }"

  definition arl_length :: "'a::heap array_list \<Rightarrow> nat Heap" where
    "arl_length \<equiv> \<lambda>(a,n). return (n)"

  definition arl_is_empty :: "'a::heap array_list \<Rightarrow> bool Heap" where
    "arl_is_empty \<equiv> \<lambda>(a,n). return (n=0)"

  definition arl_last :: "'a::heap array_list \<Rightarrow> 'a Heap" where
    "arl_last \<equiv> \<lambda>(a,n). do {
      Array.nth a (n - 1)
    }"

  definition arl_butlast :: "'a::heap array_list \<Rightarrow> 'a array_list Heap" where
    "arl_butlast \<equiv> \<lambda>(a,n). do {
      let n = n - 1;
      len \<leftarrow> Array.len a;
      if (n*4 < len \<and> n*2\<ge>minimum_capacity) then do {
        a \<leftarrow> array_shrink a (n*2);
        return (a,n)
      } else
        return (a,n)
    }"

  definition arl_get :: "'a::heap array_list \<Rightarrow> nat \<Rightarrow> 'a Heap" where
    "arl_get \<equiv> \<lambda>(a,n) i. Array.nth a i"

  definition arl_set :: "'a::heap array_list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array_list Heap" where
    "arl_set \<equiv> \<lambda>(a,n) i x. do { a \<leftarrow> Array.upd i x a; return (a,n)}"


  lemma arl_empty_rule[sep_heap_rules]: "< emp > arl_empty <is_array_list []>"
    by (sep_auto simp: arl_empty_def is_array_list_def initial_capacity_def)

  lemma arl_empty_sz_rule[sep_heap_rules]: "< emp > arl_empty_sz N <is_array_list []>"
    by (sep_auto simp: arl_empty_sz_def is_array_list_def minimum_capacity_def)

  lemma arl_copy_rule[sep_heap_rules]: "< is_array_list l a > arl_copy a <\<lambda>r. is_array_list l a * is_array_list l r>"  
    by (sep_auto simp: arl_copy_def is_array_list_def)

  lemma arl_append_rule[sep_heap_rules]: "
    < is_array_list l a > 
      arl_append a x 
    <\<lambda>a. is_array_list (l@[x]) a >\<^sub>t"  
    by (sep_auto 
      simp: arl_append_def is_array_list_def take_update_last neq_Nil_conv
      split: prod.splits nat.split)
    
  lemma arl_length_rule[sep_heap_rules]: "
    <is_array_list l a> 
      arl_length a
    <\<lambda>r. is_array_list l a * \<up>(r=length l)>"
    by (sep_auto simp: arl_length_def is_array_list_def)
    
  lemma arl_is_empty_rule[sep_heap_rules]: "
    <is_array_list l a> 
      arl_is_empty a
    <\<lambda>r. is_array_list l a * \<up>(r\<longleftrightarrow>(l=[]))>"
    by (sep_auto simp: arl_is_empty_def is_array_list_def)

  lemma arl_last_rule[sep_heap_rules]: "
    l\<noteq>[] \<Longrightarrow>
    <is_array_list l a> 
      arl_last a
    <\<lambda>r. is_array_list l a * \<up>(r=last l)>"
    by (sep_auto simp: arl_last_def is_array_list_def last_take_nth_conv)
    
  lemma arl_butlast_rule[sep_heap_rules]: "
    l\<noteq>[] \<Longrightarrow>
    <is_array_list l a> 
      arl_butlast a
    <is_array_list (butlast l)>\<^sub>t"
  proof -
    assume [simp]: "l\<noteq>[]"
  
    have [simp]: "\<And>x. min (x-Suc 0) ((x-Suc 0)*2) = x-Suc 0" by auto

    show ?thesis
      by (sep_auto 
        split: prod.splits
        simp: arl_butlast_def is_array_list_def butlast_take minimum_capacity_def)
  qed  

  lemma arl_get_rule[sep_heap_rules]: "
    i<length l \<Longrightarrow>
    <is_array_list l a> 
      arl_get a i
    <\<lambda>r. is_array_list l a * \<up>(r=l!i)>"
    by (sep_auto simp: arl_get_def is_array_list_def split: prod.split)

  lemma arl_set_rule[sep_heap_rules]: "
    i<length l \<Longrightarrow>
    <is_array_list l a> 
      arl_set a i x
    <is_array_list (l[i:=x])>"
    by (sep_auto simp: arl_set_def is_array_list_def split: prod.split)

  definition "arl_assn A \<equiv> hr_comp is_array_list (\<langle>the_pure A\<rangle>list_rel)"
  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "arl_assn A" for A]


  lemma arl_assn_comp: "is_pure A \<Longrightarrow> hr_comp (arl_assn A) (\<langle>B\<rangle>list_rel) = arl_assn (hr_comp A B)"
    unfolding arl_assn_def
    by (auto simp: hr_comp_the_pure hr_comp_assoc list_rel_compp)

  lemma arl_assn_comp': "hr_comp (arl_assn id_assn) (\<langle>B\<rangle>list_rel) = arl_assn (pure B)"
    by (simp add: arl_assn_comp)

context 
  notes [fcomp_norm_unfold] = arl_assn_def[symmetric] arl_assn_comp'
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI]
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def
begin  


  lemma arl_empty_hnr_aux: "(uncurry0 arl_empty,uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a is_array_list"  
    by sep_auto
  sepref_decl_impl (no_register) arl_empty: arl_empty_hnr_aux .

  lemma arl_empty_sz_hnr_aux: "(uncurry0 (arl_empty_sz N),uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a is_array_list"  
    by sep_auto
  sepref_decl_impl (no_register) arl_empty_sz: arl_empty_sz_hnr_aux .

  definition "op_arl_empty \<equiv> op_list_empty"
  definition "op_arl_empty_sz (N::nat) \<equiv> op_list_empty"

  lemma arl_copy_hnr_aux: "(arl_copy,RETURN o op_list_copy) \<in> is_array_list\<^sup>k \<rightarrow>\<^sub>a is_array_list"
    by sep_auto
  sepref_decl_impl arl_copy: arl_copy_hnr_aux .  

  lemma arl_append_hnr_aux: "(uncurry arl_append,uncurry (RETURN oo op_list_append)) \<in> (is_array_list\<^sup>d *\<^sub>a id_assn\<^sup>k) \<rightarrow>\<^sub>a is_array_list"
    by sep_auto
  sepref_decl_impl arl_append: arl_append_hnr_aux .

  lemma arl_length_hnr_aux: "(arl_length,RETURN o op_list_length) \<in> is_array_list\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    by sep_auto
  sepref_decl_impl arl_length: arl_length_hnr_aux .

  lemma arl_is_empty_hnr_aux: "(arl_is_empty,RETURN o op_list_is_empty) \<in> is_array_list\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    by sep_auto
  sepref_decl_impl arl_is_empty: arl_is_empty_hnr_aux .  

  lemma arl_last_hnr_aux: "(arl_last,RETURN o op_list_last) \<in> [pre_list_last]\<^sub>a is_array_list\<^sup>k \<rightarrow> id_assn"
    by sep_auto
  sepref_decl_impl arl_last: arl_last_hnr_aux . 

  lemma arl_butlast_hnr_aux: "(arl_butlast,RETURN o op_list_butlast) \<in> [pre_list_butlast]\<^sub>a is_array_list\<^sup>d \<rightarrow> is_array_list"
    by sep_auto
  sepref_decl_impl arl_butlast: arl_butlast_hnr_aux .

  lemma arl_get_hnr_aux: "(uncurry arl_get,uncurry (RETURN oo op_list_get)) \<in> [\<lambda>(l,i). i<length l]\<^sub>a (is_array_list\<^sup>k *\<^sub>a nat_assn\<^sup>k) \<rightarrow> id_assn"
    by sep_auto
  sepref_decl_impl arl_get: arl_get_hnr_aux .

  lemma arl_set_hnr_aux: "(uncurry2 arl_set,uncurry2 (RETURN ooo op_list_set)) \<in> [\<lambda>((l,i),_). i<length l]\<^sub>a (is_array_list\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k) \<rightarrow> is_array_list"
    by sep_auto
  sepref_decl_impl arl_set: arl_set_hnr_aux .

  sepref_definition arl_swap is "uncurry2 mop_list_swap" :: "((arl_assn id_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a arl_assn id_assn)"
    unfolding gen_mop_list_swap[abs_def]
    by sepref
  sepref_decl_impl (ismop) arl_swap: arl_swap.refine .  
end


interpretation arl: list_custom_empty "arl_assn A" arl_empty op_arl_empty
  apply unfold_locales
  apply (rule arl_empty_hnr)
  by (auto simp: op_arl_empty_def)

lemma [def_pat_rules]: "op_arl_empty_sz$N \<equiv> UNPROTECT (op_arl_empty_sz N)" by simp
interpretation arl_sz: list_custom_empty "arl_assn A" "arl_empty_sz N" "PR_CONST (op_arl_empty_sz N)"
  apply unfold_locales
  apply (rule arl_empty_sz_hnr)
  by (auto simp: op_arl_empty_sz_def)

end
