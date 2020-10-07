theory IICF_MS_Array_List
imports 
  "../Intf/IICF_List" 
  Separation_Logic_Imperative_HOL.Array_Blit
  "../../../Separation_Logic_Imperative_HOL/Examples/Default_Insts"
begin

  type_synonym 'a ms_array_list = "'a Heap.array \<times> nat"

  definition "is_ms_array_list ms l \<equiv> \<lambda>(a,n). \<exists>\<^sub>Al'. a \<mapsto>\<^sub>a l' * \<up>(n \<le> length l' \<and> l = take n l' \<and> ms=length l')"

  lemma is_ms_array_list_prec[safe_constraint_rules]: "precise (is_ms_array_list ms)"
    unfolding is_ms_array_list_def[abs_def]
    apply(rule preciseI)
    apply(simp split: prod.splits) 
  	using preciseD snga_prec by fastforce

  definition "marl_empty_sz maxsize \<equiv> do {
    a \<leftarrow> Array.new maxsize default;
    return (a,0)
  }"

  definition "marl_append \<equiv> \<lambda>(a,n) x. do {
      a \<leftarrow> Array.upd n x a;
      return (a,n+1)
  }"

  definition marl_length :: "'a::heap ms_array_list \<Rightarrow> nat Heap" where
    "marl_length \<equiv> \<lambda>(a,n). return (n)"

  definition marl_is_empty :: "'a::heap ms_array_list \<Rightarrow> bool Heap" where
    "marl_is_empty \<equiv> \<lambda>(a,n). return (n=0)"

  definition marl_last :: "'a::heap ms_array_list \<Rightarrow> 'a Heap" where
    "marl_last \<equiv> \<lambda>(a,n). do {
      Array.nth a (n - 1)
    }"

  definition marl_butlast :: "'a::heap ms_array_list \<Rightarrow> 'a ms_array_list Heap" where
    "marl_butlast \<equiv> \<lambda>(a,n). do {
      return (a,n - 1)
    }"

  definition marl_get :: "'a::heap ms_array_list \<Rightarrow> nat \<Rightarrow> 'a Heap" where
    "marl_get \<equiv> \<lambda>(a,n) i. Array.nth a i"

  definition marl_set :: "'a::heap ms_array_list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a ms_array_list Heap" where
    "marl_set \<equiv> \<lambda>(a,n) i x. do { a \<leftarrow> Array.upd i x a; return (a,n)}"

  lemma marl_empty_sz_rule[sep_heap_rules]: "< emp > marl_empty_sz N <is_ms_array_list N []>"
    by (sep_auto simp: marl_empty_sz_def is_ms_array_list_def)

  lemma marl_append_rule[sep_heap_rules]: "length l < N \<Longrightarrow>
    < is_ms_array_list N l a > 
      marl_append a x 
    <\<lambda>a. is_ms_array_list N (l@[x]) a >\<^sub>t"  
    by (sep_auto 
      simp: marl_append_def is_ms_array_list_def take_update_last 
      split: prod.splits)
    
  lemma marl_length_rule[sep_heap_rules]: "
    <is_ms_array_list N l a> 
      marl_length a
    <\<lambda>r. is_ms_array_list N l a * \<up>(r=length l)>"
    by (sep_auto simp: marl_length_def is_ms_array_list_def)
    
  lemma marl_is_empty_rule[sep_heap_rules]: "
    <is_ms_array_list N l a> 
      marl_is_empty a
    <\<lambda>r. is_ms_array_list N l a * \<up>(r\<longleftrightarrow>(l=[]))>"
    by (sep_auto simp: marl_is_empty_def is_ms_array_list_def)

  lemma marl_last_rule[sep_heap_rules]: "
    l\<noteq>[] \<Longrightarrow>
    <is_ms_array_list N l a> 
      marl_last a
    <\<lambda>r. is_ms_array_list N l a * \<up>(r=last l)>"
    by (sep_auto simp: marl_last_def is_ms_array_list_def last_take_nth_conv)
    
  lemma marl_butlast_rule[sep_heap_rules]: "
    l\<noteq>[] \<Longrightarrow>
    <is_ms_array_list N l a> 
      marl_butlast a
    <is_ms_array_list N (butlast l)>\<^sub>t"
    by (sep_auto 
      split: prod.splits
      simp: marl_butlast_def is_ms_array_list_def butlast_take)

  lemma marl_get_rule[sep_heap_rules]: "
    i<length l \<Longrightarrow>
    <is_ms_array_list N l a> 
      marl_get a i
    <\<lambda>r. is_ms_array_list N l a * \<up>(r=l!i)>"
    by (sep_auto simp: marl_get_def is_ms_array_list_def split: prod.split)

  lemma marl_set_rule[sep_heap_rules]: "
    i<length l \<Longrightarrow>
    <is_ms_array_list N l a> 
      marl_set a i x
    <is_ms_array_list N (l[i:=x])>"
    by (sep_auto simp: marl_set_def is_ms_array_list_def split: prod.split)

  definition "marl_assn N A \<equiv> hr_comp (is_ms_array_list N) (\<langle>the_pure A\<rangle>list_rel)"
  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "marl_assn N A" for N A]

context 
  notes [fcomp_norm_unfold] = marl_assn_def[symmetric]
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI]
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def
begin  

  definition [simp]: "op_marl_empty_sz (N::nat) \<equiv> op_list_empty"
  context fixes N :: nat begin
    sepref_register "PR_CONST (op_marl_empty_sz N)"
  end

  lemma [def_pat_rules]: "op_marl_empty_sz$N \<equiv> UNPROTECT (op_marl_empty_sz N)" by simp

  lemma marl_fold_custom_empty_sz: 
    "op_list_empty = op_marl_empty_sz N"
    "mop_list_empty = RETURN (op_marl_empty_sz N)"
    "[] = op_marl_empty_sz N"
    by auto

  lemma marl_empty_hnr_aux: "(uncurry0 (marl_empty_sz N), uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a is_ms_array_list N"
    by sep_auto
  lemmas marl_empty_hnr = marl_empty_hnr_aux[FCOMP op_list_empty.fref[of "the_pure A" for A]]
  lemmas marl_empty_hnr_mop = marl_empty_hnr[FCOMP mk_mop_rl0_np[OF mop_list_empty_alt]]

  lemma marl_empty_sz_hnr[sepref_fr_rules]:
    "(uncurry0 (marl_empty_sz N), uncurry0 (RETURN (PR_CONST (op_marl_empty_sz N)))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a marl_assn N A"
    using marl_empty_hnr
    by simp

  lemma marl_append_hnr_aux: "(uncurry marl_append,uncurry (RETURN oo op_list_append)) \<in> [\<lambda>(l,_). length l<N]\<^sub>a ((is_ms_array_list N)\<^sup>d *\<^sub>a id_assn\<^sup>k) \<rightarrow> is_ms_array_list N"
    by sep_auto
  lemmas marl_append_hnr[sepref_fr_rules] = marl_append_hnr_aux[FCOMP op_list_append.fref]
  lemmas marl_append_hnr_mop[sepref_fr_rules] = marl_append_hnr[FCOMP mk_mop_rl2_np[OF mop_list_append_alt]]

  lemma marl_length_hnr_aux: "(marl_length,RETURN o op_list_length) \<in> (is_ms_array_list N)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    by sep_auto
  lemmas marl_length_hnr[sepref_fr_rules] = marl_length_hnr_aux[FCOMP op_list_length.fref[of "the_pure A" for A]]
  lemmas marl_length_hnr_mop[sepref_fr_rules] = marl_length_hnr[FCOMP mk_mop_rl1_np[OF mop_list_length_alt]]

  lemma marl_is_empty_hnr_aux: "(marl_is_empty,RETURN o op_list_is_empty) \<in> (is_ms_array_list N)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    by sep_auto
  lemmas marl_is_empty_hnr[sepref_fr_rules] = marl_is_empty_hnr_aux[FCOMP op_list_is_empty.fref[of "the_pure A" for A]]
  lemmas marl_is_empty_hnr_mop[sepref_fr_rules] = marl_is_empty_hnr[FCOMP mk_mop_rl1_np[OF mop_list_is_empty_alt]]

  lemma marl_last_hnr_aux: "(marl_last,RETURN o op_list_last) \<in> [\<lambda>x. x\<noteq>[]]\<^sub>a (is_ms_array_list N)\<^sup>k \<rightarrow> id_assn"
    by sep_auto
  lemmas marl_last_hnr[sepref_fr_rules] = marl_last_hnr_aux[FCOMP op_list_last.fref]
  lemmas marl_last_hnr_mop[sepref_fr_rules] = marl_last_hnr[FCOMP mk_mop_rl1[OF mop_list_last_alt]]

  lemma marl_butlast_hnr_aux: "(marl_butlast,RETURN o op_list_butlast) \<in> [\<lambda>x. x\<noteq>[]]\<^sub>a (is_ms_array_list N)\<^sup>d \<rightarrow> (is_ms_array_list N)"
    by sep_auto
  lemmas marl_butlast_hnr[sepref_fr_rules] = marl_butlast_hnr_aux[FCOMP op_list_butlast.fref[of "the_pure A" for A]]
  lemmas marl_butlast_hnr_mop[sepref_fr_rules] = marl_butlast_hnr[FCOMP mk_mop_rl1[OF mop_list_butlast_alt]]

  lemma marl_get_hnr_aux: "(uncurry marl_get,uncurry (RETURN oo op_list_get)) \<in> [\<lambda>(l,i). i<length l]\<^sub>a ((is_ms_array_list N)\<^sup>k *\<^sub>a nat_assn\<^sup>k) \<rightarrow> id_assn"
    by sep_auto
  lemmas marl_get_hnr[sepref_fr_rules] = marl_get_hnr_aux[FCOMP op_list_get.fref]
  lemmas marl_get_hnr_mop[sepref_fr_rules] = marl_get_hnr[FCOMP mk_mop_rl2[OF mop_list_get_alt]]

  lemma marl_set_hnr_aux: "(uncurry2 marl_set,uncurry2 (RETURN ooo op_list_set)) \<in> [\<lambda>((l,i),_). i<length l]\<^sub>a ((is_ms_array_list N)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k) \<rightarrow> (is_ms_array_list N)"
    by sep_auto
  lemmas marl_set_hnr[sepref_fr_rules] = marl_set_hnr_aux[FCOMP op_list_set.fref]
  lemmas marl_set_hnr_mop[sepref_fr_rules] = marl_set_hnr[FCOMP mk_mop_rl3[OF mop_list_set_alt]]

end

context
  fixes N :: nat
  assumes N_sz: "N>10"
begin

schematic_goal "hn_refine (emp) (?c::?'c Heap) ?\<Gamma>' ?R (do {
  let x = op_marl_empty_sz N;
  RETURN (x@[1::nat])
})"  
  using N_sz
  by sepref

end

schematic_goal "hn_refine (emp) (?c::?'c Heap) ?\<Gamma>' ?R (do {
  let x = op_list_empty;
  RETURN (x@[1::nat])
})"  
  apply (subst marl_fold_custom_empty_sz[where N=10])
  apply sepref
  done

end
