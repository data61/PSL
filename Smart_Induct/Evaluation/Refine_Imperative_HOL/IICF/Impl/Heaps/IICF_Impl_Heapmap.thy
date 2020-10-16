section \<open>Implementation of Heaps by Arrays\<close>
theory IICF_Impl_Heapmap
imports IICF_Abs_Heapmap "../IICF_Indexed_Array_List"
begin

(* TODO/FIXME: Division setup of the code generator is a mess.
  TODO: Why does [code_unfold] not work to rewrite "x div 2"?
*)
text \<open>Some setup to circumvent the really inefficient implementation 
  of division in the code generator, which has to consider several
  cases for negative divisors and dividends. \<close>
definition [code_unfold]: 
  "efficient_nat_div2 n     
    \<equiv> nat_of_integer (fst (Code_Numeral.divmod_abs (integer_of_nat n) 2))"

lemma efficient_nat_div2[simp]: "efficient_nat_div2 n = n div 2"
  by (simp add: efficient_nat_div2_def nat_of_integer.rep_eq)

  type_synonym 'v hma = "nat list \<times> ('v list)"
  sepref_decl_intf 'v i_hma is "nat list \<times> (nat \<rightharpoonup> 'v)"

  locale hmstruct_impl = hmstruct prio for prio :: "'v::heap \<Rightarrow> 'p::linorder"
  begin
    lemma param_prio: "(prio,prio) \<in> Id \<rightarrow> Id" by simp
    lemmas [sepref_import_param] = param_prio
    sepref_register prio
  end

  context
    fixes maxsize :: nat
    fixes prio :: "'v::heap \<Rightarrow> 'p::linorder"
    notes [map_type_eqs] = map_type_eqI[Pure.of "TYPE((nat,'v) ahm)" "TYPE('v i_hma)"]
  begin

    interpretation hmstruct .
    interpretation hmstruct_impl .
  
    definition "hm_impl1_\<alpha> \<equiv> \<lambda>(pq,ml). 
      (pq,\<lambda>k. if k\<in>set pq then Some (ml!k) else None)"

    definition "hm_impl1_invar \<equiv> \<lambda>(pq,ml). 
        hmr_invar (hm_impl1_\<alpha> (pq,ml))
      \<and> set pq \<subseteq> {0..<maxsize}  
      \<and> ((pq=[] \<and> ml=[]) \<or> (length ml = maxsize))"  

    definition "hm_impl1_weak_invar \<equiv> \<lambda>(pq,ml). 
        set pq \<subseteq> {0..<maxsize}  
      \<and> ((pq=[] \<and> ml=[]) \<or> (length ml = maxsize))"  

    definition "hm_impl1_rel \<equiv> br hm_impl1_\<alpha> hm_impl1_invar"
    definition "hm_weak_impl'_rel \<equiv> br hm_impl1_\<alpha> hm_impl1_weak_invar"


    lemmas hm_impl1_rel_defs = 
      hm_impl1_rel_def hm_weak_impl'_rel_def hm_impl1_weak_invar_def hm_impl1_invar_def hm_impl1_\<alpha>_def in_br_conv
    

    lemma hm_impl_\<alpha>_fst_eq: 
        "(x1, x2) = hm_impl1_\<alpha> (x1a, x2a) \<Longrightarrow> x1 = x1a"
      unfolding hm_impl1_\<alpha>_def by (auto split: if_split_asm)


    term hm_empty_op  
    definition hm_empty_op' :: "'v hma nres" 
      where "hm_empty_op' \<equiv> do {
        let pq = op_ial_empty_sz maxsize;
        let ml = op_list_empty;
        RETURN (pq,ml)
      }"


    lemma hm_empty_op'_refine: "(hm_empty_op', hm_empty_op) \<in> \<langle>hm_impl1_rel\<rangle>nres_rel"  
      apply (intro fun_relI nres_relI)
      unfolding hm_empty_op'_def hm_empty_op_def hm_impl1_rel_defs 
      by (auto simp: in_br_conv)

    definition hm_length' :: "'v hma \<Rightarrow> nat" where "hm_length' \<equiv> \<lambda>(pq,ml). length pq"

    lemma hm_length'_refine: "(RETURN o hm_length',RETURN o hm_length) \<in> hm_impl1_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding hm_length'_def hm_length_def hm_impl1_rel_defs
      by (auto)
      
    term hm_key_of_op  
    definition "hm_key_of_op' \<equiv> \<lambda>(pq,ml) i. ASSERT (i>0) \<then> mop_list_get pq (i - 1)"
    lemma hm_key_of_op'_refine: "(hm_key_of_op', hm_key_of_op) \<in> hm_impl1_rel \<rightarrow> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding hm_key_of_op'_def hm_key_of_op_def hm_impl1_rel_defs
      by (auto)

    term hm_lookup  
    definition "hm_lookup_op' \<equiv> \<lambda>(pq,ml) k. do {
      if (k<maxsize) then do {    \<comment> \<open>TODO: This check can be eliminated, but this will complicate refinement of keys in basic ops\<close>
        let c = op_list_contains k pq;
        if c then do {
          v \<leftarrow> mop_list_get ml k;
          RETURN (Some v)
        } else RETURN None
      } else RETURN None  
    }"
      
    lemma hm_lookup_op'_refine: "(uncurry hm_lookup_op', uncurry (RETURN oo hm_lookup)) 
      \<in> (hm_impl1_rel \<times>\<^sub>r nat_rel) \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>option_rel\<rangle>nres_rel"
      apply (intro frefI nres_relI)
      unfolding hm_lookup_op_def hm_lookup_op'_def o_def uncurry_def
      apply refine_vcg
      apply (auto simp: hm_impl1_rel_defs heapmap_\<alpha>_def hmr_invar_def)
      done

    term hm_contains_key_op  
    definition "hm_contains_key_op' \<equiv> \<lambda>k (pq,ml). do {
      if (k<maxsize) then do {    \<comment> \<open>TODO: This check can be eliminated, but this will complicate refinement of keys in basic ops\<close>
        RETURN (op_list_contains k pq)
      } else RETURN False  
    }"
      
    lemma hm_contains_key_op'_refine: "(uncurry hm_contains_key_op', uncurry hm_contains_key_op) 
      \<in> (nat_rel \<times>\<^sub>r hm_impl1_rel) \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel"
      apply (intro frefI nres_relI)
      unfolding hm_contains_key_op_def hm_contains_key_op'_def o_def uncurry_def PR_CONST_def
      apply refine_vcg
      apply (auto simp: hm_impl1_rel_defs heapmap_\<alpha>_def hmr_invar_def)
      done


    term hm_valid 

    definition "hm_exch_op' \<equiv> \<lambda>(pq,ml) i j. do {
      ASSERT (hm_valid (hm_impl1_\<alpha> (pq,ml)) i);
      ASSERT (hm_valid (hm_impl1_\<alpha> (pq,ml)) j);
      pq \<leftarrow> mop_list_swap pq (i - 1) (j - 1);
      RETURN (pq,ml)
    }"

    lemma hm_impl1_relI:
      assumes "hmr_invar b"
      assumes "(a,b)\<in>hm_weak_impl'_rel"
      shows "(a,b)\<in>hm_impl1_rel"
      using assms
      unfolding hmr_rel_def hm_impl1_rel_def hm_weak_impl'_rel_def in_br_conv
        hm_impl1_weak_invar_def hm_impl1_invar_def
      by auto

    lemma hm_impl1_nres_relI:
      assumes "b \<le>\<^sub>n SPEC hmr_invar"
      assumes "(a,b)\<in>\<langle>hm_weak_impl'_rel\<rangle>nres_rel"
      shows "(a,b)\<in>\<langle>hm_impl1_rel\<rangle>nres_rel"
      using assms hm_impl1_relI
      apply (auto simp: pw_le_iff pw_leof_iff refine_pw_simps in_br_conv nres_rel_def)
      apply blast
      done


    lemma hm_exch_op'_refine: "(hm_exch_op', hm_exch_op) \<in> hm_impl1_rel \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>hm_impl1_rel\<rangle>nres_rel"
      apply (intro fun_relI hm_impl1_nres_relI[OF hm_exch_op_invar])
      unfolding hm_exch_op'_def hm_exch_op_def
      apply (auto simp: pw_le_iff refine_pw_simps nres_rel_def
          hm_impl1_rel_def in_br_conv split: prod.splits)
      apply (auto simp: hm_impl1_\<alpha>_def)
      unfolding hm_impl1_rel_defs
      apply auto
      done


    term hm_index_op  

    definition "hm_index_op' \<equiv> \<lambda>(pq,ml) k. 
      do {
        ASSERT (hm_impl1_invar (pq,ml) \<and> heapmap_\<alpha> (hm_impl1_\<alpha> (pq,ml)) k \<noteq> None \<and> k\<in>set pq);
        i \<leftarrow> mop_list_index pq k;
        RETURN (i+1)
      }"
    lemma hm_index_op'_refine: "(hm_index_op',hm_index_op) 
      \<in> hm_impl1_rel \<rightarrow> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"  
      apply (intro fun_relI nres_relI)
      unfolding hm_index_op'_def hm_index_op_def hm_impl1_rel_defs
      apply (auto simp: pw_le_iff refine_pw_simps heapmap_\<alpha>_def split: if_split_asm)
      done

    definition hm_update_op' where
      "hm_update_op' \<equiv> \<lambda>(pq,ml) i v. do {
        ASSERT (hm_valid (hm_impl1_\<alpha> (pq,ml)) i \<and> hm_impl1_invar (pq,ml));
        k \<leftarrow> mop_list_get pq (i - 1);
        ml \<leftarrow> mop_list_set ml k v;
        RETURN (pq, ml)
      }"
    lemma hm_update_op'_refine: "(hm_update_op', hm_update_op) \<in> hm_impl1_rel \<rightarrow> nat_rel \<rightarrow> Id \<rightarrow> \<langle>hm_impl1_rel\<rangle>nres_rel"  
      apply (intro fun_relI hm_impl1_nres_relI[OF hm_update_op_invar])
      unfolding hm_update_op'_def hm_update_op_def
      apply (auto simp: pw_le_iff refine_pw_simps nres_rel_def
          hm_impl1_rel_def in_br_conv split: prod.splits)
      apply (auto simp: hm_impl1_\<alpha>_def)
      unfolding hm_impl1_rel_defs
      apply (auto simp: subset_code(1))
      done
      
          
    term hm_butlast_op  

    lemma hm_butlast_op_invar: "hm_butlast_op hm \<le>\<^sub>n SPEC hmr_invar"
      unfolding hm_butlast_op_def h.butlast_op_def
      apply refine_vcg
      apply (clarsimp_all simp: hmr_rel_defs map_butlast distinct_butlast)
      apply safe

      apply (auto simp: in_set_conv_nth nth_butlast) []
      apply (metis Suc_pred len_greater_imp_nonempty length_greater_0_conv less_antisym)
      
      apply (auto dest: in_set_butlastD) []

      apply (metis One_nat_def append_butlast_last_id distinct_butlast last_conv_nth not_distinct_conv_prefix)
      done


    definition hm_butlast_op' where
      "hm_butlast_op' \<equiv> \<lambda>(pq,ml). do {
        ASSERT (hmr_invar (hm_impl1_\<alpha> (pq,ml)));
        pq \<leftarrow> mop_list_butlast pq;
        RETURN (pq,ml)
      }"

    lemma set_butlast_distinct_conv: 
      "\<lbrakk>distinct l\<rbrakk> \<Longrightarrow> set (butlast l) = set l - {last l}"  
      by (cases l rule: rev_cases; auto)

    lemma hm_butlast_op'_refine: "(hm_butlast_op', hm_butlast_op) \<in> hm_impl1_rel \<rightarrow> \<langle>hm_impl1_rel\<rangle>nres_rel"  
      apply (intro fun_relI hm_impl1_nres_relI[OF hm_butlast_op_invar])
      unfolding hm_butlast_op'_def hm_butlast_op_def
      apply (auto simp: pw_le_iff refine_pw_simps nres_rel_def
          hm_impl1_rel_def in_br_conv split: prod.splits)
      apply (auto simp: hm_impl1_\<alpha>_def)
      unfolding hm_impl1_rel_defs
      apply (auto simp: restrict_map_def) []

      defer

      apply (auto dest: in_set_butlastD) []
      apply (auto intro!: ext 
        simp: hmr_invar_def set_butlast_distinct_conv last_conv_nth
        dest: in_set_butlastD) []
      done

    definition hm_append_op' 
      where "hm_append_op' \<equiv> \<lambda>(pq,ml) k v. do {
        ASSERT (k \<notin> set pq \<and> k<maxsize);
        ASSERT (hm_impl1_invar (pq,ml));
        pq \<leftarrow> mop_list_append pq k;
        ml \<leftarrow> (if length ml = 0 then mop_list_replicate maxsize v else RETURN ml);
        ml \<leftarrow> mop_list_set ml k v;
        RETURN (pq,ml)
      }"

    lemma hm_append_op'_refine: "(uncurry2 hm_append_op', uncurry2 hm_append_op) 
      \<in> [\<lambda>((hm,k),v). k<maxsize]\<^sub>f (hm_impl1_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r Id \<rightarrow> \<langle>hm_impl1_rel\<rangle>nres_rel"  
      apply (intro frefI hm_impl1_nres_relI[OF hm_append_op_invar])
      unfolding hm_append_op'_def hm_append_op_def
      apply (auto simp: pw_le_iff refine_pw_simps nres_rel_def
          hm_impl1_rel_def in_br_conv split: prod.splits)
      unfolding hm_impl1_rel_defs
      apply (auto simp: restrict_map_def hmr_invar_def split: prod.splits if_split_asm) 
      done
      
    definition "hm_impl2_rel \<equiv> prod_assn (ial_assn maxsize id_assn) (array_assn id_assn)"
    definition "hm_impl_rel \<equiv> hr_comp hm_impl2_rel hm_impl1_rel"

    lemmas [fcomp_norm_unfold] = hm_impl_rel_def[symmetric]

    (*lemma hm_impl_rel_precise[constraint_rules]: "precise hm_impl_rel"
      unfolding hm_impl_rel_def hm_impl1_rel_def hm_impl2_rel_def
      by (constraint_rules)*)


    subsection \<open>Implement Basic Operations\<close>  


    lemma param_parent: "(efficient_nat_div2,h.parent) \<in> Id \<rightarrow> Id" 
      by (intro fun_relI) (simp add: h.parent_def)
    lemmas [sepref_import_param] = param_parent
    sepref_register h.parent

    lemma param_left: "(h.left,h.left) \<in> Id \<rightarrow> Id" by simp
    lemmas [sepref_import_param] = param_left
    sepref_register h.left

    lemma param_right: "(h.right,h.right) \<in> Id \<rightarrow> Id" by simp
    lemmas [sepref_import_param] = param_right
    sepref_register h.right

    abbreviation (input) "prio_rel \<equiv> (Id::('p\<times>'p) set)"

    lemma param_prio_le: "((\<le>), (\<le>)) \<in> prio_rel \<rightarrow> prio_rel \<rightarrow> bool_rel" by simp
    lemmas [sepref_import_param] = param_prio_le
    
    lemma param_prio_lt: "((<), (<)) \<in> prio_rel \<rightarrow> prio_rel \<rightarrow> bool_rel" by simp
    lemmas [sepref_import_param] = param_prio_lt

    abbreviation "I_HM_UNF \<equiv> TYPE(nat list \<times> 'v list)"

    sepref_definition hm_length_impl is "RETURN o hm_length'" :: "hm_impl2_rel\<^sup>k\<rightarrow>\<^sub>anat_assn"
      unfolding hm_length'_def hm_impl2_rel_def
      by sepref
    lemmas [sepref_fr_rules] = hm_length_impl.refine[FCOMP hm_length'_refine]
    sepref_register "hm_length::(nat,'v) ahm \<Rightarrow> _"

    sepref_definition hm_key_of_op_impl is "uncurry hm_key_of_op'" :: "hm_impl2_rel\<^sup>k*\<^sub>anat_assn\<^sup>k \<rightarrow>\<^sub>anat_assn"
      unfolding hm_key_of_op'_def hm_impl2_rel_def
      by sepref
    lemmas [sepref_fr_rules] = hm_key_of_op_impl.refine[FCOMP hm_key_of_op'_refine]
    sepref_register "hm_key_of_op::(nat,'v) ahm \<Rightarrow> _"

    context 
      notes [id_rules] = itypeI[Pure.of maxsize "TYPE(nat)"]
      notes [sepref_import_param] = IdI[of maxsize]
    begin


    sepref_definition hm_lookup_impl is "uncurry hm_lookup_op'" :: "(hm_impl2_rel\<^sup>k*\<^sub>anat_assn\<^sup>k \<rightarrow>\<^sub>aoption_assn id_assn)"
      unfolding hm_lookup_op'_def hm_impl2_rel_def
      by sepref
    lemmas [sepref_fr_rules] = 
      hm_lookup_impl.refine[FCOMP hm_lookup_op'_refine]
    sepref_register "hm_lookup::(nat,'v) ahm \<Rightarrow> _" 

    sepref_definition hm_exch_op_impl is "uncurry2 hm_exch_op'" :: "hm_impl2_rel\<^sup>d*\<^sub>anat_assn\<^sup>k*\<^sub>anat_assn\<^sup>k \<rightarrow>\<^sub>a hm_impl2_rel"
      unfolding hm_exch_op'_def hm_impl2_rel_def
      by sepref
    lemmas [sepref_fr_rules] = hm_exch_op_impl.refine[FCOMP hm_exch_op'_refine]
    sepref_register "hm_exch_op::(nat,'v) ahm \<Rightarrow> _" 

    sepref_definition hm_index_op_impl is "uncurry hm_index_op'" :: "hm_impl2_rel\<^sup>k*\<^sub>aid_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
      unfolding hm_index_op'_def hm_impl2_rel_def 
      by sepref
    lemmas [sepref_fr_rules] = hm_index_op_impl.refine[FCOMP hm_index_op'_refine]
    sepref_register "hm_index_op::(nat,'v) ahm \<Rightarrow> _" 

    sepref_definition hm_update_op_impl is "uncurry2 hm_update_op'" :: "hm_impl2_rel\<^sup>d*\<^sub>aid_assn\<^sup>k*\<^sub>aid_assn\<^sup>k \<rightarrow>\<^sub>a hm_impl2_rel"
      unfolding hm_update_op'_def hm_impl2_rel_def 
      by sepref
    lemmas [sepref_fr_rules] = hm_update_op_impl.refine[FCOMP hm_update_op'_refine]
    sepref_register "hm_update_op::(nat,'v) ahm \<Rightarrow> _" 


    sepref_definition hm_butlast_op_impl is "hm_butlast_op'" :: "hm_impl2_rel\<^sup>d \<rightarrow>\<^sub>a hm_impl2_rel"
      unfolding hm_butlast_op'_def hm_impl2_rel_def by sepref
    lemmas [sepref_fr_rules] = hm_butlast_op_impl.refine[FCOMP hm_butlast_op'_refine]
    sepref_register "hm_butlast_op::(nat,'v) ahm \<Rightarrow> _"

    sepref_definition hm_append_op_impl is "uncurry2 hm_append_op'" :: "hm_impl2_rel\<^sup>d *\<^sub>a id_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a hm_impl2_rel"
      unfolding hm_append_op'_def hm_impl2_rel_def 
      apply (rewrite array_fold_custom_replicate)
      by sepref
    lemmas [sepref_fr_rules] = hm_append_op_impl.refine[FCOMP hm_append_op'_refine]
    sepref_register "hm_append_op::(nat,'v) ahm \<Rightarrow> _" 


    subsection \<open>Auxiliary Operations\<close>

    lemmas [intf_of_assn] = intf_of_assnI[where R="hm_impl_rel :: (nat,'v) ahm \<Rightarrow> _" and 'a="'v i_hma"]

    sepref_definition hm_valid_impl is "uncurry (RETURN oo hm_valid)" :: "hm_impl_rel\<^sup>k*\<^sub>anat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn "
      unfolding hm_valid_def[abs_def]
      by sepref
    lemmas [sepref_fr_rules] = hm_valid_impl.refine
    sepref_register "hm_valid::(nat,'v) ahm \<Rightarrow> _"


    (* Optimization *)
    definition "hm_the_lookup_op' hm k \<equiv> do {
      let (pq,ml) = hm;
      ASSERT (heapmap_\<alpha> (hm_impl1_\<alpha> hm) k \<noteq> None \<and> hm_impl1_invar hm);
      v \<leftarrow> mop_list_get ml k;
      RETURN v
    }"
    lemma hm_the_lookup_op'_refine: 
      "(hm_the_lookup_op', hm_the_lookup_op) \<in> hm_impl1_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding hm_the_lookup_op'_def hm_the_lookup_op_def
      apply refine_vcg
      apply (auto simp: hm_impl1_rel_defs heapmap_\<alpha>_def hmr_invar_def split: if_split_asm)
      done

    sepref_definition hm_the_lookup_op_impl is "uncurry hm_the_lookup_op'" :: "hm_impl2_rel\<^sup>k*\<^sub>aid_assn\<^sup>k \<rightarrow>\<^sub>aid_assn"  
      unfolding hm_the_lookup_op'_def[abs_def] hm_impl2_rel_def
      by sepref
    lemmas hm_the_lookup_op_impl[sepref_fr_rules] = hm_the_lookup_op_impl.refine[FCOMP hm_the_lookup_op'_refine]
    sepref_register "hm_the_lookup_op::(nat,'v) ahm \<Rightarrow> _"

    sepref_definition hm_val_of_op_impl is "uncurry hm_val_of_op" :: "hm_impl_rel\<^sup>k*\<^sub>aid_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
      unfolding hm_val_of_op_def by sepref
    lemmas [sepref_fr_rules] = hm_val_of_op_impl.refine
    sepref_register "hm_val_of_op::(nat,'v) ahm \<Rightarrow> _"

    sepref_definition hm_prio_of_op_impl is "uncurry (PR_CONST hm_prio_of_op)" :: "hm_impl_rel\<^sup>k*\<^sub>aid_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
      unfolding hm_prio_of_op_def[abs_def] PR_CONST_def by sepref
    lemmas [sepref_fr_rules] = hm_prio_of_op_impl.refine
    sepref_register "PR_CONST hm_prio_of_op::(nat,'v) ahm \<Rightarrow> _"
    lemma [def_pat_rules]: "hmstruct.hm_prio_of_op$prio \<equiv> PR_CONST hm_prio_of_op"
      by simp

    text \<open>No code theorem preparation, as we define optimized version later\<close>  
    sepref_definition (no_prep_code) hm_swim_op_impl is "uncurry (PR_CONST hm_swim_op)" :: "hm_impl_rel\<^sup>d*\<^sub>anat_assn\<^sup>k \<rightarrow>\<^sub>a hm_impl_rel"
      unfolding hm_swim_op_def[abs_def] PR_CONST_def
      using [[goals_limit = 1]]
      by sepref
    lemmas [sepref_fr_rules] = hm_swim_op_impl.refine
    sepref_register "PR_CONST hm_swim_op::(nat,'v) ahm \<Rightarrow> _"
    lemma [def_pat_rules]: "hmstruct.hm_swim_op$prio \<equiv> PR_CONST hm_swim_op" by simp

    text \<open>No code theorem preparation, as we define optimized version later\<close>  
    sepref_definition (no_prep_code) hm_sink_op_impl is "uncurry (PR_CONST hm_sink_op)" :: "hm_impl_rel\<^sup>d*\<^sub>anat_assn\<^sup>k \<rightarrow>\<^sub>a hm_impl_rel"
      unfolding hm_sink_op_def[abs_def] PR_CONST_def
      by sepref
    lemmas [sepref_fr_rules] = hm_sink_op_impl.refine
    sepref_register "PR_CONST hm_sink_op::(nat,'v) ahm \<Rightarrow> _"
    lemma [def_pat_rules]: "hmstruct.hm_sink_op$prio \<equiv> PR_CONST hm_sink_op" by simp

    sepref_definition hm_repair_op_impl is "uncurry (PR_CONST hm_repair_op)" :: "hm_impl_rel\<^sup>d*\<^sub>anat_assn\<^sup>k \<rightarrow>\<^sub>a hm_impl_rel"
      unfolding hm_repair_op_def[abs_def] PR_CONST_def
      by sepref
    lemmas [sepref_fr_rules] = hm_repair_op_impl.refine
    sepref_register "PR_CONST hm_repair_op::(nat,'v) ahm \<Rightarrow> _"
    lemma [def_pat_rules]: "hmstruct.hm_repair_op$prio \<equiv> PR_CONST hm_repair_op" by simp

  subsection \<open>Interface Operations\<close>
  definition hm_rel_np where 
    "hm_rel_np \<equiv> hr_comp hm_impl_rel heapmap_rel"
  lemmas [fcomp_norm_unfold] = hm_rel_np_def[symmetric]  

  definition hm_rel where
    "hm_rel K V \<equiv> hr_comp hm_rel_np (\<langle>the_pure K,the_pure V\<rangle>map_rel)"
  lemmas [fcomp_norm_unfold] = hm_rel_def[symmetric]  

  lemmas [intf_of_assn] = intf_of_assnI[where R="hm_rel K V" and 'a="('kk,'vv) i_map" for K V]

  lemma hm_rel_id_conv: "hm_rel id_assn id_assn = hm_rel_np"
    \<comment> \<open>Used for generic algorithms: Unfold with this, then let decl-impl compose with \<open>map_rel\<close> again.\<close>
    unfolding hm_rel_def by simp


  subsubsection \<open>Synthesis\<close>
  definition op_hm_empty_sz :: "nat \<Rightarrow> 'kk\<rightharpoonup>'vv"
    where [simp]: "op_hm_empty_sz sz \<equiv> op_map_empty"
  sepref_register "PR_CONST (op_hm_empty_sz maxsize)" :: "('k,'v) i_map"
  lemma [def_pat_rules]: "op_hm_empty_sz$maxsize \<equiv> UNPROTECT (op_hm_empty_sz maxsize)" by simp

  lemma hm_fold_custom_empty_sz: 
    "op_map_empty = op_hm_empty_sz sz"
    "Map.empty = op_hm_empty_sz sz"
    by auto

  sepref_definition hm_empty_op_impl is "uncurry0 hm_empty_op'" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a hm_impl2_rel"  
    unfolding hm_empty_op'_def hm_impl2_rel_def array.fold_custom_empty
    by sepref
    
  sepref_definition hm_insert_op_impl is "uncurry2 hm_insert_op" :: "[\<lambda>((k,_),_). k<maxsize]\<^sub>a id_assn\<^sup>k*\<^sub>aid_assn\<^sup>k*\<^sub>ahm_impl_rel\<^sup>d \<rightarrow> hm_impl_rel"
    unfolding hm_insert_op_def
    by sepref

  sepref_definition hm_is_empty_op_impl is "hm_is_empty_op" :: "hm_impl_rel\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    unfolding hm_is_empty_op_def
    by sepref

  sepref_definition hm_lookup_op_impl is "uncurry hm_lookup_op" :: "id_assn\<^sup>k*\<^sub>ahm_impl_rel\<^sup>k \<rightarrow>\<^sub>a option_assn id_assn"
    unfolding hm_lookup_op_def by sepref

  sepref_definition hm_contains_key_impl is "uncurry hm_contains_key_op'" :: "id_assn\<^sup>k*\<^sub>ahm_impl2_rel\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    unfolding hm_contains_key_op'_def hm_impl2_rel_def
    by sepref

  sepref_definition hm_decrease_key_op_impl is "uncurry2 hm_decrease_key_op" :: "id_assn\<^sup>k*\<^sub>aid_assn\<^sup>k*\<^sub>ahm_impl_rel\<^sup>d \<rightarrow>\<^sub>a hm_impl_rel"
    unfolding hm_decrease_key_op_def by sepref

  sepref_definition hm_increase_key_op_impl is "uncurry2 hm_increase_key_op" :: "id_assn\<^sup>k*\<^sub>aid_assn\<^sup>k*\<^sub>ahm_impl_rel\<^sup>d \<rightarrow>\<^sub>a hm_impl_rel"
    unfolding hm_increase_key_op_def by sepref

  sepref_definition hm_change_key_op_impl is "uncurry2 hm_change_key_op" :: "id_assn\<^sup>k*\<^sub>aid_assn\<^sup>k*\<^sub>ahm_impl_rel\<^sup>d \<rightarrow>\<^sub>a hm_impl_rel"
    unfolding hm_change_key_op_def by sepref

  sepref_definition hm_pop_min_op_impl is hm_pop_min_op :: "hm_impl_rel\<^sup>d \<rightarrow>\<^sub>a prod_assn (prod_assn nat_assn id_assn) hm_impl_rel "
    unfolding hm_pop_min_op_def[abs_def]
    by sepref

  sepref_definition hm_remove_op_impl is "uncurry hm_remove_op" :: "id_assn\<^sup>k *\<^sub>a hm_impl_rel\<^sup>d \<rightarrow>\<^sub>a hm_impl_rel"
    unfolding hm_remove_op_def[abs_def] by sepref

  sepref_definition hm_peek_min_op_impl is "hm_peek_min_op" :: "hm_impl_rel\<^sup>k \<rightarrow>\<^sub>a prod_assn nat_assn id_assn"
    unfolding hm_peek_min_op_def[abs_def] hm_kv_of_op_def
    by sepref



  subsubsection \<open>Setup of Refinements\<close>

  sepref_decl_impl (no_register) hm_empty: 
    hm_empty_op_impl.refine[FCOMP hm_empty_op'_refine, FCOMP hm_empty_aref] .

  context fixes K assumes "IS_BELOW_ID K" begin
    lemmas mop_map_update_new_fref' = mop_map_update_new.fref[of K] 
    lemmas op_map_update_fref' = op_map_update.fref[of K] 
  end  

  sepref_decl_impl (ismop) hm_insert: hm_insert_op_impl.refine[FCOMP hm_insert_op_aref]
    uses mop_map_update_new_fref'
    unfolding IS_BELOW_ID_def
    apply (parametricity; auto simp: single_valued_below_Id)
    done

  sepref_decl_impl hm_is_empty: hm_is_empty_op_impl.refine[FCOMP hm_is_empty_op_aref] .
  sepref_decl_impl hm_lookup: hm_lookup_op_impl.refine[FCOMP hm_lookup_op_aref] .

  sepref_decl_impl hm_contains_key: 
    hm_contains_key_impl.refine[FCOMP hm_contains_key_op'_refine, FCOMP hm_contains_key_op_aref]
    .

  sepref_decl_impl (ismop) hm_decrease_key: hm_decrease_key_op_impl.refine[FCOMP hm_decrease_key_op_aref] .
  sepref_decl_impl (ismop) hm_increase_key: hm_increase_key_op_impl.refine[FCOMP hm_increase_key_op_aref] .
  sepref_decl_impl (ismop) hm_change_key: hm_change_key_op_impl.refine[FCOMP hm_change_key_op_aref] .
    
  sepref_decl_impl (ismop) hm_remove: hm_remove_op_impl.refine[FCOMP hm_remove_op_aref] .

  sepref_decl_impl (ismop) hm_pop_min: hm_pop_min_op_impl.refine[FCOMP hm_pop_min_op_aref] .
  sepref_decl_impl (ismop) hm_peek_min: hm_peek_min_op_impl.refine[FCOMP hm_peek_min_op_aref] .

  \<comment> \<open>Realized as generic algorithm. Note that we use @{term id_assn} for the elements.\<close>
  sepref_definition hm_upd_op_impl is "uncurry2 (RETURN ooo op_map_update)" :: "[\<lambda>((k,_),_). k<maxsize]\<^sub>a id_assn\<^sup>k *\<^sub>a id_assn\<^sup>k *\<^sub>a (hm_rel id_assn id_assn)\<^sup>d \<rightarrow> hm_rel id_assn id_assn"
    unfolding op_pm_set_gen_impl by sepref

  sepref_decl_impl hm_upd_op_impl.refine[unfolded hm_rel_id_conv] uses op_map_update_fref'
    unfolding IS_BELOW_ID_def
    apply (parametricity; auto simp: single_valued_below_Id)
    done

end  
end

interpretation hm: map_custom_empty "PR_CONST (op_hm_empty_sz maxsize)"
  apply unfold_locales by simp

lemma op_hm_empty_sz_hnr[sepref_fr_rules]:
  "(uncurry0 (hm_empty_op_impl maxsize), uncurry0 (RETURN (PR_CONST (op_hm_empty_sz maxsize)))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a hm_rel maxsize prio K V"
  using hm_empty_hnr by simp


subsection \<open>Manual fine-tuning of code-lemmas\<close>
(* TODO: Integrate into Sepref-tool optimization phase! *)

context
notes [simp del] = CNV_def efficient_nat_div2
begin

lemma nested_case_bind: 
  "(case p of (a,b) \<Rightarrow> bind (case a of (a1,a2) \<Rightarrow> m a b a1 a2) (f a b)) 
  = (case p of ((a1,a2),b) \<Rightarrow> bind (m (a1,a2) b a1 a2) (f (a1,a2) b))"
  "(case p of (a,b) \<Rightarrow> bind (case b of (b1,b2) \<Rightarrow> m a b b1 b2) (f a b)) 
  = (case p of (a,b1,b2) \<Rightarrow> bind (m a (b1,b2) b1 b2) (f a (b1,b2)))"
  by (simp_all split: prod.splits)

lemma it_case: "(case p of (a,b) \<Rightarrow> f p a b) = (case p of (a,b) \<Rightarrow> f (a,b) a b)"
  by (auto split: prod.split)

lemma c2l: "(case p of (a,b) \<Rightarrow> bind (m a b) (f a b)) = 
  do { let (a,b) = p; bind (m a b) (f a b)}" by simp

lemma bind_Let: "do { x \<leftarrow> do { let y = v; (f y :: 'a Heap)}; g x } = do { let y=v; x \<leftarrow> f y; g x }" by auto
lemma bind_case: "do { x \<leftarrow> (case y of (a,b) \<Rightarrow> f a b); (g x :: 'a Heap) } = do { let (a,b) = y; x \<leftarrow> f a b; g x }"
  by (auto split: prod.splits)

lemma bind_case_mvup: "do { x \<leftarrow> f; case y of (a,b) \<Rightarrow> g a b x } 
  = do { let (a,b) = y; x \<leftarrow> f; (g a b x :: 'a Heap) }"
  by (auto split: prod.splits)

lemma if_case_mvup: "(if b then case p of (x1,x2) \<Rightarrow> f x1 x2 else e)
  = (case p of (x1,x2) \<Rightarrow> if b then f x1 x2 else e)" by auto

lemma nested_case: "(case p of (a,b) \<Rightarrow> (case p of (c,d) \<Rightarrow> f a b c d)) =
  (case p of (a,b) \<Rightarrow> f a b a b)"
  by (auto split: prod.split)

lemma split_prod_bound: "(\<lambda>p. f p) = (\<lambda>(a,b). f (a,b))" by auto

lemma bpc_conv: "do { (a,b) \<leftarrow> (m::(_*_) Heap); f a b } = do {
  ab \<leftarrow> (m);
  f (fst ab) (snd ab)
}" 
  apply (subst (2) split_prod_bound)
  by simp

lemma it_case_pp: "(case p of ((p1,p2)) \<Rightarrow> case p of ((p1',p2')) \<Rightarrow> f p1 p2 p1' p2')
  = (case p of ((p1,p2)) \<Rightarrow> f p1 p2 p1 p2)"
  by (auto split: prod.split)


lemma it_case_ppp: "(case p of ((p1,p2),p3) \<Rightarrow> case p of ((p1',p2'),p3') \<Rightarrow> f p1 p2 p3 p1' p2' p3')
  = (case p of ((p1,p2),p3) \<Rightarrow> f p1 p2 p3 p1 p2 p3)"
  by (auto split: prod.split)

lemma it_case_pppp: "(case a1 of
              (((a, b), c), d) \<Rightarrow>
                case a1 of
                (((a', b'), c'), d') \<Rightarrow> f a b c d a' b' c' d') =
       (case a1 of
              (((a, b), c), d) \<Rightarrow> f a b c d a b c d)"
  by (auto split: prod.splits)

private lemmas inlines = hm_append_op_impl_def ial_append_def
    marl_length_def marl_append_def hm_length_impl_def ial_length_def
    hm_valid_impl_def hm_prio_of_op_impl_def hm_val_of_op_impl_def hm_key_of_op_impl_def
    ial_get_def hm_the_lookup_op_impl_def heap_array_set_def marl_get_def
    it_case_ppp it_case_pppp bind_case bind_case_mvup nested_case if_case_mvup
    it_case_pp

schematic_goal [code]: "hm_insert_op_impl maxsize prio hm k v = ?f"
  unfolding hm_insert_op_impl_def
  apply (rule CNV_eqD)
  apply (simp add: inlines  cong: if_cong)
  by (rule CNV_I)
  

schematic_goal "hm_swim_op_impl prio hm i \<equiv> ?f"
  unfolding hm_swim_op_impl_def 
  apply (rule eq_reflection)
  apply (rule CNV_eqD)
  apply (simp add: inlines efficient_nat_div2  
    cong: if_cong)
  by (rule CNV_I)


lemma hm_swim_op_impl_code[code]: "hm_swim_op_impl prio hm i \<equiv> ccpo.fixp (fun_lub Heap_lub) (fun_ord Heap_ord)
       (\<lambda>cf (a1, a2).
           case a1 of
           ((a1b, a2b), a2a) \<Rightarrow>
             case a1b of
             (a, b) \<Rightarrow> do {
               let d2 = efficient_nat_div2 a2; 
               if 0 < d2 \<and> d2 \<le> b
               then do {
                      x \<leftarrow> (case a1b of (a, n) \<Rightarrow> Array.nth a) (d2 - Suc 0);
                      x \<leftarrow> Array.nth a2a x;
                      xa \<leftarrow> (case a1b of (a, n) \<Rightarrow> Array.nth a) (a2 - Suc 0);
                      xa \<leftarrow> Array.nth a2a xa;
                      if prio x \<le> prio xa then return a1
                      else do {
                             x'g \<leftarrow> hm_exch_op_impl a1 a2 (d2);
                             cf (x'g, d2)
                           }
                    }
               else return a1
             })
       (hm, i)"
  unfolding hm_swim_op_impl_def 
  apply (rule eq_reflection)
  apply (simp add: inlines efficient_nat_div2 Let_def 
    cong: if_cong)
  done

prepare_code_thms hm_swim_op_impl_code

schematic_goal hm_sink_opt_impl_code[code]: "hm_sink_op_impl prio hm i \<equiv> ?f"
  unfolding hm_sink_op_impl_def 
  apply (rule eq_reflection)
  apply (rule CNV_eqD)
  apply (simp add: inlines 
    cong: if_cong)
  by (rule CNV_I)

prepare_code_thms hm_sink_opt_impl_code

export_code hm_swim_op_impl in SML_imp module_name Test


schematic_goal hm_change_key_opt_impl_code[code]: "
  hm_change_key_op_impl prio k v hm \<equiv> ?f"
  unfolding hm_change_key_op_impl_def 
  apply (rule eq_reflection)
  apply (rule CNV_eqD)
  apply (simp add: inlines hm_contains_key_impl_def ial_contains_def
    hm_change_key_op_impl_def hm_index_op_impl_def hm_update_op_impl_def
    ial_index_def
    cong: if_cong split: prod.splits)
  oops


schematic_goal hm_change_key_opt_impl_code[code]: "
  hm_change_key_op_impl prio k v hm \<equiv> case hm of (((a, b), ba), x2) \<Rightarrow>
       (do {
              x \<leftarrow> Array.nth ba k;
              xa \<leftarrow> Array.nth a x;
              xa \<leftarrow> Array.upd xa v x2;
              hm_repair_op_impl prio (((a, b), ba), xa) (Suc x)
            })"
  unfolding hm_change_key_op_impl_def 
  apply (rule eq_reflection)
  apply (simp add: inlines hm_contains_key_impl_def ial_contains_def
    hm_change_key_op_impl_def hm_index_op_impl_def hm_update_op_impl_def
    ial_index_def
    cong: if_cong split: prod.splits)
  done


schematic_goal hm_set_opt_impl_code[code]: "hm_upd_op_impl maxsize prio hm k v \<equiv> ?f"
  unfolding hm_upd_op_impl_def 
  apply (rule eq_reflection)
  apply (rule CNV_eqD)
  apply (simp add: inlines hm_contains_key_impl_def ial_contains_def
    hm_change_key_op_impl_def hm_index_op_impl_def hm_update_op_impl_def
    ial_index_def
    cong: if_cong)
  by (rule CNV_I)

schematic_goal hm_pop_min_opt_impl_code[code]: "hm_pop_min_op_impl prio hm \<equiv> ?f"
  unfolding hm_pop_min_op_impl_def 
  apply (rule eq_reflection)
  apply (rule CNV_eqD)
  apply (simp add: inlines hm_contains_key_impl_def ial_contains_def
    hm_change_key_op_impl_def hm_index_op_impl_def hm_update_op_impl_def
    hm_butlast_op_impl_def ial_butlast_def
    ial_index_def
    cong: if_cong)
  by (rule CNV_I)
  
end

export_code 
  hm_empty_op_impl 
  hm_insert_op_impl
  hm_is_empty_op_impl
  hm_lookup_op_impl
  hm_contains_key_impl
  hm_decrease_key_op_impl
  hm_increase_key_op_impl
  hm_change_key_op_impl
  hm_upd_op_impl
  hm_pop_min_op_impl
  hm_remove_op_impl
  hm_peek_min_op_impl
  checking SML_imp


end
