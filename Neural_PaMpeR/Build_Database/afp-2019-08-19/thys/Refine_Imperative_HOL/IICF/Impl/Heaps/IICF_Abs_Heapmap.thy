section \<open>Priority Maps implemented with List and Map\<close>
theory IICF_Abs_Heapmap
imports IICF_Abs_Heap "HOL-Library.Rewrite" "../../Intf/IICF_Prio_Map"
begin

  type_synonym ('k,'v) ahm = "'k list \<times> ('k \<rightharpoonup> 'v)"

  subsection \<open>Basic Setup\<close>

  text \<open>First, we define a mapping to list-based heaps\<close>
  definition hmr_\<alpha> :: "('k,'v) ahm \<Rightarrow> 'v heap" where
    "hmr_\<alpha> \<equiv> \<lambda>(pq,m). map (the o m) pq"

  definition "hmr_invar \<equiv> \<lambda>(pq,m). distinct pq \<and> dom m = set pq"

  definition "hmr_rel \<equiv> br hmr_\<alpha> hmr_invar"

  lemmas hmr_rel_defs = hmr_rel_def br_def hmr_\<alpha>_def hmr_invar_def

  lemma hmr_empty_invar[simp]: "hmr_invar ([],Map.empty)"
    by (auto simp: hmr_invar_def)


  locale hmstruct = h: heapstruct prio for prio :: "'v \<Rightarrow> 'b::linorder"
  begin

    text \<open>Next, we define a mapping to priority maps.\<close>

    definition heapmap_\<alpha> :: "('k,'v) ahm \<Rightarrow> ('k \<rightharpoonup> 'v)" where
      "heapmap_\<alpha> \<equiv> \<lambda>(pq,m). m"

    definition heapmap_invar :: "('k,'v) ahm \<Rightarrow> bool" where
      "heapmap_invar \<equiv> \<lambda>hm. hmr_invar hm \<and> h.heap_invar (hmr_\<alpha> hm)"
      
    definition "heapmap_rel \<equiv> br heapmap_\<alpha> heapmap_invar"

    lemmas heapmap_rel_defs = heapmap_rel_def br_def heapmap_\<alpha>_def heapmap_invar_def

    lemma [refine_dref_RELATES]: "RELATES hmr_rel" by (simp add: RELATES_def)


    lemma h_heap_invarI[simp]: "heapmap_invar hm \<Longrightarrow> h.heap_invar (hmr_\<alpha> hm)"  
      by (simp add: heapmap_invar_def)

    lemma hmr_invarI[simp]: "heapmap_invar hm \<Longrightarrow> hmr_invar hm"  
      unfolding heapmap_invar_def by blast



    lemma set_hmr_\<alpha>[simp]: "hmr_invar hm \<Longrightarrow> set (hmr_\<alpha> hm) = ran (heapmap_\<alpha> hm)"
      apply (clarsimp simp: hmr_\<alpha>_def hmr_invar_def heapmap_\<alpha>_def 
        eq_commute[of "dom _" "set _"] ran_def)
      apply force
      done

    lemma in_h_hmr_\<alpha>_conv[simp]: "hmr_invar hm \<Longrightarrow> x \<in># h.\<alpha> (hmr_\<alpha> hm) \<longleftrightarrow> x \<in> ran (heapmap_\<alpha> hm)"  
      by (force simp: hmr_\<alpha>_def hmr_invar_def heapmap_\<alpha>_def in_multiset_in_set ran_is_image)

    subsection \<open>Basic Operations\<close>
    (* length, val_of_op, update, butlast, append, empty *)

    text \<open>In this section, we define the basic operations on heapmaps, 
      and their relations to heaps and maps.\<close>

    subsubsection \<open>Length\<close>
    text \<open>Length of the list that represents the heap\<close>
    definition hm_length :: "('k,'v) ahm \<Rightarrow> nat" where
      "hm_length \<equiv> \<lambda>(pq,_). length pq"

    lemma hm_length_refine: "(hm_length, length) \<in> hmr_rel \<rightarrow> nat_rel"  
      apply (intro fun_relI)
      unfolding hm_length_def
      by (auto simp: hmr_rel_defs)
        
    lemma hm_length_hmr_\<alpha>[simp]: "length (hmr_\<alpha> hm) = hm_length hm"
      by (auto simp: hm_length_def hmr_\<alpha>_def split: prod.splits)

    lemmas [refine] = hm_length_refine[param_fo]

    subsubsection \<open>Valid\<close>
    text \<open>Check whether index is valid\<close>
    definition "hm_valid hm i \<equiv> i>0 \<and> i\<le> hm_length hm"

    lemma hm_valid_refine: "(hm_valid,h.valid)\<in>hmr_rel \<rightarrow> nat_rel \<rightarrow> bool_rel"
      apply (intro fun_relI)
      unfolding hm_valid_def h.valid_def
      by (parametricity add: hm_length_refine)

    lemma hm_valid_hmr_\<alpha>[simp]: "h.valid (hmr_\<alpha> hm) = hm_valid hm"
      by (intro ext) (auto simp: h.valid_def hm_valid_def)

    subsubsection \<open>Key-Of\<close>
    definition hm_key_of :: "('k,'v) ahm \<Rightarrow> nat \<Rightarrow> 'k" where  
      "hm_key_of \<equiv> \<lambda>(pq,m) i. pq!(i - 1)"

    definition hm_key_of_op :: "('k,'v) ahm \<Rightarrow> nat \<Rightarrow> 'k nres" where
      "hm_key_of_op \<equiv> \<lambda>(pq,m) i. ASSERT (i>0) \<then> mop_list_get pq (i - 1)"

    lemma hm_key_of_op_unfold:
      shows "hm_key_of_op hm i = ASSERT (hm_valid hm i) \<then> RETURN (hm_key_of hm i)"
      unfolding hm_valid_def hm_length_def hm_key_of_op_def hm_key_of_def
      by (auto split: prod.splits simp: pw_eq_iff refine_pw_simps)

    lemma val_of_hmr_\<alpha>[simp]: "hm_valid hm i \<Longrightarrow> h.val_of (hmr_\<alpha> hm) i 
      = the (heapmap_\<alpha> hm (hm_key_of hm i))"
      by (auto 
        simp: hmr_\<alpha>_def h.val_of_def heapmap_\<alpha>_def hm_key_of_def hm_valid_def hm_length_def
        split: prod.splits)
 
    lemma hm_\<alpha>_key_ex[simp]:
      "\<lbrakk>hmr_invar hm; hm_valid hm i\<rbrakk> \<Longrightarrow> (heapmap_\<alpha> hm (hm_key_of hm i) \<noteq> None)"
      unfolding heapmap_invar_def hmr_invar_def hm_valid_def heapmap_\<alpha>_def 
        hm_key_of_def hm_length_def
      by (auto split: prod.splits)  

    subsubsection \<open>Lookup\<close>
    abbreviation (input) hm_lookup where "hm_lookup \<equiv> heapmap_\<alpha>"

    definition "hm_the_lookup_op hm k \<equiv> 
      ASSERT (heapmap_\<alpha> hm k \<noteq> None \<and> hmr_invar hm) 
      \<then> RETURN (the (heapmap_\<alpha> hm k))"


    subsubsection \<open>Exchange\<close>  
    text \<open>Exchange two indices\<close>

    definition "hm_exch_op \<equiv> \<lambda>(pq,m) i j. do {
      ASSERT (hm_valid (pq,m) i);
      ASSERT (hm_valid (pq,m) j);
      ASSERT (hmr_invar (pq,m));
      pq \<leftarrow> mop_list_swap pq (i - 1) (j - 1);
      RETURN (pq,m)
    }"

    lemma hm_exch_op_invar: "hm_exch_op hm i j \<le>\<^sub>n SPEC hmr_invar"
      unfolding hm_exch_op_def h.exch_op_def h.val_of_op_def h.update_op_def
      apply simp
      apply refine_vcg
      apply (auto simp: hm_valid_def map_swap hm_length_def hmr_rel_defs)
      done

    lemma hm_exch_op_refine: "(hm_exch_op,h.exch_op) \<in> hmr_rel \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>hmr_rel\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding hm_exch_op_def h.exch_op_def h.val_of_op_def h.update_op_def
      apply simp
      apply refine_vcg
      apply (auto simp: hm_valid_def map_swap hm_length_def hmr_rel_defs)
      done
      
    lemmas hm_exch_op_refine'[refine] = hm_exch_op_refine[param_fo, THEN nres_relD]

    definition hm_exch :: "('k,'v) ahm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('k,'v) ahm"
      where "hm_exch \<equiv> \<lambda>(pq,m) i j. (swap pq (i-1) (j-1),m)"

      
    lemma hm_exch_op_\<alpha>_correct: "hm_exch_op hm i j \<le>\<^sub>n SPEC (\<lambda>hm'. 
      hm_valid hm i \<and> hm_valid hm j \<and> hm'=hm_exch hm i j
      )"
      unfolding hm_exch_op_def
      apply refine_vcg
      apply (vc_solve simp: hm_valid_def hm_length_def heapmap_\<alpha>_def solve: asm_rl)
      apply (auto simp add: hm_key_of_def hm_exch_def swap_def) []
      done

    lemma hm_exch_\<alpha>[simp]: "heapmap_\<alpha> (hm_exch hm i j) = (heapmap_\<alpha> hm)"
      by (auto simp: heapmap_\<alpha>_def hm_exch_def split: prod.splits)
    lemma hm_exch_valid[simp]: "hm_valid (hm_exch hm i j) = hm_valid hm"
      by (intro ext) (auto simp: hm_valid_def hm_length_def hm_exch_def split: prod.splits)
    lemma hm_exch_length[simp]: "hm_length (hm_exch hm i j) = hm_length hm"
      by (auto simp: hm_length_def hm_exch_def split: prod.splits)

    lemma hm_exch_same[simp]: "hm_exch hm i i = hm"  
      by (auto simp: hm_exch_def split: prod.splits)
      

    lemma hm_key_of_exch_conv[simp]:   
      "\<lbrakk>hm_valid hm i; hm_valid hm j; hm_valid hm k\<rbrakk> \<Longrightarrow> 
        hm_key_of (hm_exch hm i j) k = (
          if k=i then hm_key_of hm j
          else if k=j then hm_key_of hm i
          else hm_key_of hm k
          )"
      unfolding hm_exch_def hm_valid_def hm_length_def hm_key_of_def
      by (auto split: prod.splits)

    lemma hm_key_of_exch_matching[simp]:  
      "\<lbrakk>hm_valid hm i; hm_valid hm j\<rbrakk> \<Longrightarrow> hm_key_of (hm_exch hm i j) i = hm_key_of hm j"
      "\<lbrakk>hm_valid hm i; hm_valid hm j\<rbrakk> \<Longrightarrow> hm_key_of (hm_exch hm i j) j = hm_key_of hm i"
      by simp_all

    subsubsection \<open>Index\<close>
    text \<open>Obtaining the index of a key\<close>
    definition "hm_index \<equiv> \<lambda>(pq,m) k. index pq k + 1"

    lemma hm_index_valid[simp]: "\<lbrakk>hmr_invar hm; heapmap_\<alpha> hm k \<noteq> None\<rbrakk> \<Longrightarrow> hm_valid hm (hm_index hm k)"
      by (force simp: hm_valid_def heapmap_\<alpha>_def hmr_invar_def hm_index_def hm_length_def Suc_le_eq)

    lemma hm_index_key_of[simp]: "\<lbrakk>hmr_invar hm; heapmap_\<alpha> hm k \<noteq> None\<rbrakk> \<Longrightarrow> hm_key_of hm (hm_index hm k) = k"
      by (force 
          simp: hm_valid_def heapmap_\<alpha>_def hmr_invar_def hm_index_def hm_length_def hm_key_of_def Suc_le_eq)


    definition "hm_index_op \<equiv> \<lambda>(pq,m) k. 
      do {
        ASSERT (hmr_invar (pq,m) \<and> heapmap_\<alpha> (pq,m) k \<noteq> None);
        i \<leftarrow> mop_list_index pq k;
        RETURN (i+1)
      }"

    lemma hm_index_op_correct:
      assumes "hmr_invar hm"
      assumes "heapmap_\<alpha> hm k \<noteq> None"
      shows "hm_index_op hm k \<le> SPEC (\<lambda>r. r= hm_index hm k)"
      using assms unfolding hm_index_op_def
      apply refine_vcg
      apply (auto simp: heapmap_\<alpha>_def hmr_invar_def hm_index_def index_nth_id)
      done
    lemmas [refine_vcg] = hm_index_op_correct  
      

    subsubsection \<open>Update\<close>  
    text \<open>Updating the heap at an index\<close>
    definition hm_update_op :: "('k,'v) ahm \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> ('k,'v) ahm nres" where
      "hm_update_op \<equiv> \<lambda>(pq,m) i v. do {
        ASSERT (hm_valid (pq,m) i \<and> hmr_invar (pq,m));
        k \<leftarrow> mop_list_get pq (i - 1);
        RETURN (pq, m(k \<mapsto> v))
      }"
    
    lemma hm_update_op_invar: "hm_update_op hm k v \<le>\<^sub>n SPEC hmr_invar"
      unfolding hm_update_op_def h.update_op_def
      apply refine_vcg
      by (auto simp: hmr_rel_defs map_distinct_upd_conv hm_valid_def hm_length_def)

    lemma hm_update_op_refine: "(hm_update_op, h.update_op) \<in> hmr_rel \<rightarrow> nat_rel \<rightarrow> Id \<rightarrow> \<langle>hmr_rel\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding hm_update_op_def h.update_op_def mop_list_get_alt mop_list_set_alt
      apply refine_vcg
      apply (auto simp: hmr_rel_defs map_distinct_upd_conv hm_valid_def hm_length_def)
      done
      
    lemmas [refine] = hm_update_op_refine[param_fo, THEN nres_relD]

    lemma hm_update_op_\<alpha>_correct:
      assumes "hmr_invar hm"
      assumes "heapmap_\<alpha> hm k \<noteq> None"
      shows "hm_update_op hm (hm_index hm k) v \<le>\<^sub>n SPEC (\<lambda>hm'. heapmap_\<alpha> hm' = (heapmap_\<alpha> hm)(k\<mapsto>v))"  
      using assms
      unfolding hm_update_op_def
      apply refine_vcg
      apply (force simp: heapmap_rel_defs hmr_rel_defs hm_index_def)
      done

    subsubsection \<open>Butlast\<close>  
    text \<open>Remove last element\<close>  
    definition hm_butlast_op :: "('k,'v) ahm \<Rightarrow> ('k,'v) ahm nres" where
      "hm_butlast_op \<equiv> \<lambda>(pq,m). do {
        ASSERT (hmr_invar (pq,m));
        k \<leftarrow> mop_list_get pq (length pq - 1);
        pq \<leftarrow> mop_list_butlast pq;
        let m = m(k:=None);
        RETURN (pq,m)
      }"

    lemma hm_butlast_op_refine: "(hm_butlast_op, h.butlast_op) \<in> hmr_rel \<rightarrow> \<langle>hmr_rel\<rangle>nres_rel"
      supply [simp del] = map_upd_eq_restrict
      apply (intro fun_relI nres_relI)
      unfolding hm_butlast_op_def h.butlast_op_def
      apply simp
      apply refine_vcg
      apply (clarsimp_all simp: hmr_rel_defs map_butlast distinct_butlast)
      apply (auto simp: neq_Nil_rev_conv) []
      done

    lemmas [refine] = hm_butlast_op_refine[param_fo, THEN nres_relD]

    lemma hm_butlast_op_\<alpha>_correct: "hm_butlast_op hm \<le>\<^sub>n SPEC (
      \<lambda>hm'. heapmap_\<alpha> hm' = (heapmap_\<alpha> hm)( hm_key_of hm (hm_length hm) := None ))"
      unfolding hm_butlast_op_def
      apply refine_vcg
      apply (auto simp: heapmap_\<alpha>_def hm_key_of_def hm_length_def)
      done
      
    subsubsection \<open>Append\<close>
    text \<open>Append new element at end of heap\<close>

    definition hm_append_op :: "('k,'v) ahm \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k,'v) ahm nres"
      where "hm_append_op \<equiv> \<lambda>(pq,m) k v. do {
        ASSERT (k \<notin> dom m);
        ASSERT (hmr_invar (pq,m));
        pq \<leftarrow> mop_list_append pq k;
        let m = m (k \<mapsto> v);
        RETURN (pq,m)
      }"

    lemma hm_append_op_invar: "hm_append_op hm k v \<le>\<^sub>n SPEC hmr_invar"  
      unfolding hm_append_op_def h.append_op_def
      apply refine_vcg
      unfolding heapmap_\<alpha>_def hmr_rel_defs
      apply (auto simp: )
      done

    lemma hm_append_op_refine: "\<lbrakk> heapmap_\<alpha> hm k = None; (hm,h)\<in>hmr_rel \<rbrakk> 
      \<Longrightarrow> (hm_append_op hm k v, h.append_op h v) \<in> \<langle>hmr_rel\<rangle>nres_rel"  
      apply (intro fun_relI nres_relI)
      unfolding hm_append_op_def h.append_op_def
      apply refine_vcg
      unfolding heapmap_\<alpha>_def hmr_rel_defs
      apply (auto simp: )
      done

    lemmas hm_append_op_refine'[refine] = hm_append_op_refine[param_fo, THEN nres_relD]
    
    lemma hm_append_op_\<alpha>_correct: 
      "hm_append_op hm k v \<le>\<^sub>n SPEC (\<lambda>hm'. heapmap_\<alpha> hm' = (heapmap_\<alpha> hm) (k \<mapsto> v))"
      unfolding hm_append_op_def
      apply refine_vcg
      by (auto simp: heapmap_\<alpha>_def)


    subsection \<open>Auxiliary Operations\<close>  
    text \<open>Auxiliary operations on heapmaps, which are derived 
      from the basic operations, but do not correspond to 
      operations of the priority map interface\<close>
    

    text \<open>We start with some setup\<close>

    lemma heapmap_hmr_relI: "(hm,h)\<in>heapmap_rel \<Longrightarrow> (hm,hmr_\<alpha> hm) \<in> hmr_rel"  
      by (auto simp: heapmap_rel_defs hmr_rel_defs)

    lemma heapmap_hmr_relI': "heapmap_invar hm \<Longrightarrow> (hm,hmr_\<alpha> hm) \<in> hmr_rel"  
      by (auto simp: heapmap_rel_defs hmr_rel_defs)

    text \<open>The basic principle how we prove correctness of our operations:
      Invariant preservation is shown by relating the operations to 
      operations on heaps. Then, only correctness on the abstraction 
      remains to be shown, assuming the operation does not fail.
      \<close>  
    lemma heapmap_nres_relI':
      assumes "hm \<le> \<Down>hmr_rel h'"
      assumes "h' \<le> SPEC (h.heap_invar)"
      assumes "hm \<le>\<^sub>n SPEC (\<lambda>hm'. RETURN (heapmap_\<alpha> hm') \<le> h)"
      shows "hm \<le> \<Down>heapmap_rel h"
      using assms
      unfolding heapmap_rel_defs hmr_rel_def
      by (auto simp: pw_le_iff pw_leof_iff refine_pw_simps)

    lemma heapmap_nres_relI'':
      assumes "hm \<le> \<Down>hmr_rel h'"
      assumes "h' \<le> SPEC \<Phi>"
      assumes "\<And>h'. \<Phi> h' \<Longrightarrow> h.heap_invar h'"
      assumes "hm \<le>\<^sub>n SPEC (\<lambda>hm'. RETURN (heapmap_\<alpha> hm') \<le> h)"
      shows "hm \<le> \<Down>heapmap_rel h"
      apply (rule heapmap_nres_relI')
      apply fact
      apply (rule order_trans, fact)
      apply (clarsimp; fact)
      apply fact
      done

    subsubsection \<open>Val-of\<close>
    text \<open>Indexing into the heap\<close>
    definition hm_val_of_op :: "('k,'v) ahm \<Rightarrow> nat \<Rightarrow> 'v nres" where
      "hm_val_of_op \<equiv> \<lambda>hm i. do {
        k \<leftarrow> hm_key_of_op hm i;
        v \<leftarrow> hm_the_lookup_op hm k;
        RETURN v
      }"

    lemma hm_val_of_op_refine: "(hm_val_of_op,h.val_of_op) \<in> (hmr_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel)"  
      apply (intro fun_relI nres_relI)
      unfolding hm_val_of_op_def h.val_of_op_def 
        hm_key_of_op_def hm_key_of_def hm_valid_def hm_length_def
        hm_the_lookup_op_def
      apply clarsimp
      apply (rule refine_IdD)
      apply refine_vcg
      apply (auto simp: hmr_rel_defs heapmap_\<alpha>_def)
      done

    lemmas [refine] = hm_val_of_op_refine[param_fo, THEN nres_relD]

    subsubsection \<open>Prio-of\<close>  
    text \<open>Priority of key\<close>
    definition "hm_prio_of_op h i \<equiv> do {v \<leftarrow> hm_val_of_op h i; RETURN (prio v)}"
    
    lemma hm_prio_of_op_refine: "(hm_prio_of_op, h.prio_of_op) \<in> hmr_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding hm_prio_of_op_def h.prio_of_op_def
      apply refine_rcg
      by auto

    lemmas hm_prio_of_op_refine'[refine] = hm_prio_of_op_refine[param_fo, THEN nres_relD]

    subsubsection \<open>Swim\<close>

    definition hm_swim_op :: "('k,'v) ahm \<Rightarrow> nat \<Rightarrow> ('k,'v) ahm nres" where
      "hm_swim_op h i \<equiv> do {
        RECT (\<lambda>swim (h,i). do {
          ASSERT (hm_valid h i \<and> h.swim_invar (hmr_\<alpha> h) i);
          if hm_valid h (h.parent i) then do {
            ppi \<leftarrow> hm_prio_of_op h (h.parent i);
            pi \<leftarrow> hm_prio_of_op h i;
            if (\<not>ppi \<le> pi) then do {
              h \<leftarrow> hm_exch_op h i (h.parent i);
              swim (h, h.parent i)
            } else
              RETURN h
          } else 
            RETURN h
        }) (h,i)
      }"

    lemma hm_swim_op_refine: "(hm_swim_op, h.swim_op) \<in> hmr_rel \<rightarrow> nat_rel \<rightarrow> \<langle>hmr_rel\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding hm_swim_op_def h.swim_op_def
      apply refine_rcg
      apply refine_dref_type
      apply (clarsimp_all simp: hm_valid_refine[param_fo, THEN IdD])
      apply (simp add: hmr_rel_def in_br_conv)
      done

    lemmas hm_swim_op_refine'[refine] = hm_swim_op_refine[param_fo, THEN nres_relD]


    lemma hm_swim_op_nofail_imp_valid: 
      "nofail (hm_swim_op hm i) \<Longrightarrow> hm_valid hm i \<and> h.swim_invar (hmr_\<alpha> hm) i"
      unfolding hm_swim_op_def
      apply (subst (asm) RECT_unfold, refine_mono)
      by (auto simp: refine_pw_simps)

    lemma hm_swim_op_\<alpha>_correct: "hm_swim_op hm i \<le>\<^sub>n SPEC (\<lambda>hm'. heapmap_\<alpha> hm' = heapmap_\<alpha> hm)"
      apply (rule leof_add_nofailI)
      apply (drule hm_swim_op_nofail_imp_valid)
      unfolding hm_swim_op_def
      apply (rule RECT_rule_leof[where 
            pre="\<lambda>(hm',i). hm_valid hm' i \<and> heapmap_\<alpha> hm' = heapmap_\<alpha> hm"
            and V = "inv_image less_than snd"
            ])
      apply simp
      apply simp

      unfolding hm_prio_of_op_def hm_val_of_op_def 
        hm_exch_op_def hm_key_of_op_def hm_the_lookup_op_def
      apply (refine_vcg)
      apply (vc_solve simp add: hm_valid_def hm_length_def)
      apply rprems
      apply (vc_solve simp: heapmap_\<alpha>_def h.parent_def)
      done

    subsubsection \<open>Sink\<close>  
    definition hm_sink_op
    where   
      "hm_sink_op h k \<equiv> RECT (\<lambda>D (h,k). do {
        ASSERT (k>0 \<and> k\<le>hm_length h);
        let len = hm_length h;
        if (2*k \<le> len) then do {
          let j = 2*k;
          pj \<leftarrow> hm_prio_of_op h j;

          j \<leftarrow> (
            if j<len then do {
              psj \<leftarrow> hm_prio_of_op h (Suc j);
              if pj>psj then RETURN (j+1) else RETURN j
            } else RETURN j);

          pj \<leftarrow> hm_prio_of_op h j;
          pk \<leftarrow> hm_prio_of_op h k;
          if (pk > pj) then do {
            h \<leftarrow> hm_exch_op h k j;
            D (h,j)
          } else
            RETURN h
        } else RETURN h    
      }) (h,k)"
    
    lemma hm_sink_op_refine: "(hm_sink_op, h.sink_op) \<in> hmr_rel \<rightarrow> nat_rel \<rightarrow> \<langle>hmr_rel\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding hm_sink_op_def h.sink_op_opt_eq[symmetric] h.sink_op_opt_def
      apply refine_rcg
      apply refine_dref_type

      unfolding hmr_rel_def heapmap_rel_def 
      apply (clarsimp_all simp: in_br_conv)
      done

    lemmas hm_sink_op_refine'[refine] = hm_sink_op_refine[param_fo, THEN nres_relD]

    lemma hm_sink_op_nofail_imp_valid: "nofail (hm_sink_op hm i) \<Longrightarrow> hm_valid hm i"
      unfolding hm_sink_op_def
      apply (subst (asm) RECT_unfold, refine_mono)
      by (auto simp: refine_pw_simps hm_valid_def)
      
    lemma hm_sink_op_\<alpha>_correct: "hm_sink_op hm i \<le>\<^sub>n SPEC (\<lambda>hm'. heapmap_\<alpha> hm' = heapmap_\<alpha> hm)"
      apply (rule leof_add_nofailI)
      apply (drule hm_sink_op_nofail_imp_valid)
      unfolding hm_sink_op_def
      apply (rule RECT_rule_leof[where 
            pre="\<lambda>(hm',i). hm_valid hm' i \<and> heapmap_\<alpha> hm' = heapmap_\<alpha> hm \<and> hm_length hm' = hm_length hm"
            and V = "measure (\<lambda>(hm',i). hm_length hm' - i)"
            ])
      apply simp
      apply simp

      unfolding hm_prio_of_op_def hm_val_of_op_def hm_exch_op_def 
        hm_key_of_op_def hm_the_lookup_op_def
      apply (refine_vcg)
      apply (vc_solve simp add: hm_valid_def hm_length_def) (* Takes long *)
      apply rprems
      apply (vc_solve simp: heapmap_\<alpha>_def h.parent_def split: prod.splits)
      apply (auto)
      done

    subsubsection \<open>Repair\<close>
    definition "hm_repair_op hm i \<equiv> do {
      hm \<leftarrow> hm_sink_op hm i;
      hm \<leftarrow> hm_swim_op hm i;
      RETURN hm
    }"
    
    lemma hm_repair_op_refine: "(hm_repair_op, h.repair_op) \<in> hmr_rel \<rightarrow> nat_rel \<rightarrow> \<langle>hmr_rel\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding hm_repair_op_def h.repair_op_def
      by refine_rcg
      
    lemmas hm_repair_op_refine'[refine] = hm_repair_op_refine[param_fo, THEN nres_relD]

    lemma hm_repair_op_\<alpha>_correct: "hm_repair_op hm i \<le>\<^sub>n SPEC (\<lambda>hm'. heapmap_\<alpha> hm' = heapmap_\<alpha> hm)"
      unfolding hm_repair_op_def
      apply (refine_vcg 
        hm_swim_op_\<alpha>_correct[THEN leof_trans] 
        hm_sink_op_\<alpha>_correct[THEN leof_trans])
      by auto


    subsection \<open>Operations\<close>    
    text \<open>In this section, we define the operations that implement the priority-map interface\<close>

    subsubsection \<open>Empty\<close>
    definition hm_empty_op :: "('k,'v) ahm nres" 
      where "hm_empty_op \<equiv> RETURN ([],Map.empty)"

    lemma hm_empty_aref: "(hm_empty_op,RETURN op_map_empty) \<in> \<langle>heapmap_rel\<rangle>nres_rel"  
      unfolding hm_empty_op_def 
      by (auto simp: heapmap_rel_defs hmr_rel_defs intro: nres_relI)

    subsubsection \<open>Insert\<close>
    definition hm_insert_op :: "'k \<Rightarrow> 'v \<Rightarrow> ('k,'v) ahm \<Rightarrow> ('k,'v) ahm nres" where
      "hm_insert_op \<equiv> \<lambda>k v h. do {
        ASSERT (h.heap_invar (hmr_\<alpha> h));
        h \<leftarrow> hm_append_op h k v;
        let l = hm_length h;
        h \<leftarrow> hm_swim_op h l;
        RETURN h
      }"
      
    lemma hm_insert_op_refine[refine]: "\<lbrakk> heapmap_\<alpha> hm k = None; (hm,h)\<in>hmr_rel \<rbrakk> \<Longrightarrow>
      hm_insert_op k v hm \<le> \<Down>hmr_rel (h.insert_op v h)"
      unfolding hm_insert_op_def h.insert_op_def
      apply refine_rcg
      by (auto simp: hmr_rel_def br_def)

    lemma hm_insert_op_aref: 
      "(hm_insert_op,mop_map_update_new) \<in> Id \<rightarrow> Id \<rightarrow> heapmap_rel \<rightarrow> \<langle>heapmap_rel\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding mop_map_update_new_alt
      apply (rule ASSERT_refine_right)
      apply (rule heapmap_nres_relI''[OF hm_insert_op_refine h.insert_op_correct])
      apply (unfold heapmap_rel_def in_br_conv; clarsimp)
      apply (erule heapmap_hmr_relI)
      apply (unfold heapmap_rel_def in_br_conv; clarsimp)
      apply (unfold heapmap_rel_def in_br_conv; clarsimp)
      unfolding hm_insert_op_def
      apply (refine_vcg 
        hm_append_op_\<alpha>_correct[THEN leof_trans]
        hm_swim_op_\<alpha>_correct[THEN leof_trans])
      apply (unfold heapmap_rel_def in_br_conv; clarsimp)
      done

    subsubsection \<open>Is-Empty\<close>  

    lemma hmr_\<alpha>_empty_iff[simp]: 
      "hmr_invar hm \<Longrightarrow> hmr_\<alpha> hm = [] \<longleftrightarrow> heapmap_\<alpha> hm = Map.empty"  
      by (auto 
        simp: hmr_\<alpha>_def heapmap_invar_def heapmap_\<alpha>_def hmr_invar_def
        split: prod.split)  

    definition hm_is_empty_op :: "('k,'v) ahm \<Rightarrow> bool nres" where
      "hm_is_empty_op \<equiv> \<lambda>hm. do {
        ASSERT (hmr_invar hm);
        let l = hm_length hm;
        RETURN (l=0)
      }"

    lemma hm_is_empty_op_refine: "(hm_is_empty_op, h.is_empty_op) \<in> hmr_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"  
      apply (intro fun_relI nres_relI)
      unfolding hm_is_empty_op_def h.is_empty_op_def
      apply refine_rcg
      apply (auto simp: hmr_rel_defs) []
      apply (parametricity add: hm_length_refine)
      done


    lemma hm_is_empty_op_aref: "(hm_is_empty_op, RETURN o op_map_is_empty) \<in> heapmap_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding hm_is_empty_op_def
      apply refine_vcg
      apply (auto simp: hmr_rel_defs heapmap_rel_defs hm_length_def)
      done

    subsubsection \<open>Lookup\<close>  

    definition hm_lookup_op :: "'k \<Rightarrow> ('k,'v) ahm \<Rightarrow> 'v option nres"
      where "hm_lookup_op \<equiv> \<lambda>k hm. ASSERT (heapmap_invar hm) \<then> RETURN (hm_lookup hm k)"

    lemma hm_lookup_op_aref: "(hm_lookup_op,RETURN oo op_map_lookup) \<in> Id \<rightarrow> heapmap_rel \<rightarrow> \<langle>\<langle>Id\<rangle>option_rel\<rangle>nres_rel"  
      apply (intro fun_relI nres_relI)
      unfolding hm_lookup_op_def heapmap_rel_def in_br_conv
      apply refine_vcg
      apply simp_all
      done

    subsubsection \<open>Contains-Key\<close>  

    definition "hm_contains_key_op \<equiv> \<lambda>k (pq,m). ASSERT (heapmap_invar (pq,m)) \<then> RETURN (k\<in>dom m)"
    lemma hm_contains_key_op_aref: "(hm_contains_key_op,RETURN oo op_map_contains_key) \<in> Id \<rightarrow> heapmap_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"  
      apply (intro fun_relI nres_relI)
      unfolding hm_contains_key_op_def heapmap_rel_defs
      apply refine_vcg
      by (auto)

    subsubsection \<open>Decrease-Key\<close>  


    definition "hm_decrease_key_op \<equiv> \<lambda>k v hm. do {
      ASSERT (heapmap_invar hm);
      ASSERT (heapmap_\<alpha> hm k \<noteq> None \<and> prio v \<le> prio (the (heapmap_\<alpha> hm k)));
      i \<leftarrow> hm_index_op hm k;
      hm \<leftarrow> hm_update_op hm i v;
      hm_swim_op hm i
    }"

    definition (in heapstruct) "decrease_key_op i v h \<equiv> do {
      ASSERT (valid h i \<and> prio v \<le> prio_of h i);
      h \<leftarrow> update_op h i v;
      swim_op h i
    }"

    lemma (in heapstruct) decrease_key_op_invar: 
      "\<lbrakk>heap_invar h; valid h i; prio v \<le> prio_of h i\<rbrakk> \<Longrightarrow> decrease_key_op i v h \<le> SPEC heap_invar"
      unfolding decrease_key_op_def
      apply refine_vcg
      by (auto simp: swim_invar_decr)


    lemma index_op_inline_refine:
      assumes "heapmap_invar hm"
      assumes "heapmap_\<alpha> hm k \<noteq> None"
      assumes "f (hm_index hm k) \<le> m"
      shows "do {i \<leftarrow> hm_index_op hm k; f i} \<le> m"  
      using hm_index_op_correct[of hm k] assms
      by (auto simp: pw_le_iff refine_pw_simps)

    lemma hm_decrease_key_op_refine: 
      "\<lbrakk>(hm,h)\<in>hmr_rel; (hm,m)\<in>heapmap_rel; m k = Some v'\<rbrakk> 
        \<Longrightarrow> hm_decrease_key_op k v hm \<le>\<Down>hmr_rel (h.decrease_key_op (hm_index hm k) v h)"  
      unfolding hm_decrease_key_op_def h.decrease_key_op_def
      (*apply (rewrite at "Let (hm_index hm k) _" Let_def)*)
      apply (refine_rcg index_op_inline_refine)
      unfolding hmr_rel_def heapmap_rel_def in_br_conv
      apply (clarsimp_all)
      done

    lemma hm_index_op_inline_leof: 
      assumes "f (hm_index hm k) \<le>\<^sub>n m"
      shows "do {i \<leftarrow> hm_index_op hm k; f i} \<le>\<^sub>n m"
      using hm_index_op_correct[of hm k] assms unfolding hm_index_op_def
      by (auto simp: pw_le_iff pw_leof_iff refine_pw_simps split: prod.splits)

    lemma hm_decrease_key_op_\<alpha>_correct: 
      "heapmap_invar hm \<Longrightarrow> hm_decrease_key_op k v hm \<le>\<^sub>n SPEC (\<lambda>hm'. heapmap_\<alpha> hm' = heapmap_\<alpha> hm(k\<mapsto>v))"
      unfolding hm_decrease_key_op_def
      apply (refine_vcg 
        hm_update_op_\<alpha>_correct[THEN leof_trans] 
        hm_swim_op_\<alpha>_correct[THEN leof_trans]
        hm_index_op_inline_leof
        )
      apply simp_all
      done

    lemma hm_decrease_key_op_aref: 
      "(hm_decrease_key_op, PR_CONST (mop_pm_decrease_key prio)) \<in> Id \<rightarrow> Id \<rightarrow> heapmap_rel \<rightarrow> \<langle>heapmap_rel\<rangle>nres_rel"
      unfolding PR_CONST_def
      apply (intro fun_relI nres_relI)
      apply (frule heapmap_hmr_relI)
      unfolding mop_pm_decrease_key_alt
      apply (rule ASSERT_refine_right; clarsimp)
      apply (rule heapmap_nres_relI')
      apply (rule hm_decrease_key_op_refine; assumption)
      unfolding heapmap_rel_def hmr_rel_def in_br_conv
      apply (rule h.decrease_key_op_invar; simp; fail )
      apply (refine_vcg hm_decrease_key_op_\<alpha>_correct[THEN leof_trans]; simp; fail)
      done

    subsubsection \<open>Increase-Key\<close>  

    definition "hm_increase_key_op \<equiv> \<lambda>k v hm. do {
      ASSERT (heapmap_invar hm);
      ASSERT (heapmap_\<alpha> hm k \<noteq> None \<and> prio v \<ge> prio (the (heapmap_\<alpha> hm k)));
      i \<leftarrow> hm_index_op hm k;
      hm \<leftarrow> hm_update_op hm i v;
      hm_sink_op hm i
    }"

    definition (in heapstruct) "increase_key_op i v h \<equiv> do {
      ASSERT (valid h i \<and> prio v \<ge> prio_of h i);
      h \<leftarrow> update_op h i v;
      sink_op h i
    }"

    lemma (in heapstruct) increase_key_op_invar: 
      "\<lbrakk>heap_invar h; valid h i; prio v \<ge> prio_of h i\<rbrakk> \<Longrightarrow> increase_key_op i v h \<le> SPEC heap_invar"
      unfolding increase_key_op_def
      apply refine_vcg
      by (auto simp: sink_invar_incr)

    lemma hm_increase_key_op_refine: 
      "\<lbrakk>(hm,h)\<in>hmr_rel; (hm,m)\<in>heapmap_rel; m k = Some v'\<rbrakk> 
        \<Longrightarrow> hm_increase_key_op k v hm \<le>\<Down>hmr_rel (h.increase_key_op (hm_index hm k) v h)"  
      unfolding hm_increase_key_op_def h.increase_key_op_def
      (*apply (rewrite at "Let (hm_index hm k) _" Let_def)*)
      apply (refine_rcg index_op_inline_refine)
      unfolding hmr_rel_def heapmap_rel_def in_br_conv
      apply (clarsimp_all)
      done

    lemma hm_increase_key_op_\<alpha>_correct: 
      "heapmap_invar hm \<Longrightarrow> hm_increase_key_op k v hm \<le>\<^sub>n SPEC (\<lambda>hm'. heapmap_\<alpha> hm' = heapmap_\<alpha> hm(k\<mapsto>v))"
      unfolding hm_increase_key_op_def
      apply (refine_vcg 
        hm_update_op_\<alpha>_correct[THEN leof_trans] 
        hm_sink_op_\<alpha>_correct[THEN leof_trans]
        hm_index_op_inline_leof)
      apply simp_all
      done

    lemma hm_increase_key_op_aref: 
      "(hm_increase_key_op, PR_CONST (mop_pm_increase_key prio)) \<in> Id \<rightarrow> Id \<rightarrow> heapmap_rel \<rightarrow> \<langle>heapmap_rel\<rangle>nres_rel"
      unfolding PR_CONST_def
      apply (intro fun_relI nres_relI)
      apply (frule heapmap_hmr_relI)
      unfolding mop_pm_increase_key_alt
      apply (rule ASSERT_refine_right; clarsimp)
      apply (rule heapmap_nres_relI')
      apply (rule hm_increase_key_op_refine; assumption)
      unfolding heapmap_rel_def hmr_rel_def in_br_conv
      apply (rule h.increase_key_op_invar; simp; fail )
      apply (refine_vcg hm_increase_key_op_\<alpha>_correct[THEN leof_trans]; simp)
      done

    subsubsection \<open>Change-Key\<close>  

    definition "hm_change_key_op \<equiv> \<lambda>k v hm. do {
      ASSERT (heapmap_invar hm);
      ASSERT (heapmap_\<alpha> hm k \<noteq> None);
      i \<leftarrow> hm_index_op hm k;
      hm \<leftarrow> hm_update_op hm i v;
      hm_repair_op hm i
    }"

    definition (in heapstruct) "change_key_op i v h \<equiv> do {
      ASSERT (valid h i);
      h \<leftarrow> update_op h i v;
      repair_op h i
    }"

    lemma (in heapstruct) change_key_op_invar: 
      "\<lbrakk>heap_invar h; valid h i\<rbrakk> \<Longrightarrow> change_key_op i v h \<le> SPEC heap_invar"
      unfolding change_key_op_def
      apply (refine_vcg)
      apply hypsubst
      apply refine_vcg
      by (auto simp: sink_invar_incr)

    lemma hm_change_key_op_refine: 
      "\<lbrakk>(hm,h)\<in>hmr_rel; (hm,m)\<in>heapmap_rel; m k = Some v'\<rbrakk> 
        \<Longrightarrow> hm_change_key_op k v hm \<le>\<Down>hmr_rel (h.change_key_op (hm_index hm k) v h)"  
      unfolding hm_change_key_op_def h.change_key_op_def
      (*apply (rewrite at "Let (hm_index hm k) _" Let_def)*)
      apply (refine_rcg index_op_inline_refine)
      unfolding hmr_rel_def heapmap_rel_def in_br_conv
      apply (clarsimp_all)
      done

    lemma hm_change_key_op_\<alpha>_correct: 
      "heapmap_invar hm \<Longrightarrow> hm_change_key_op k v hm \<le>\<^sub>n SPEC (\<lambda>hm'. heapmap_\<alpha> hm' = heapmap_\<alpha> hm(k\<mapsto>v))"
      unfolding hm_change_key_op_def
      apply (refine_vcg 
        hm_update_op_\<alpha>_correct[THEN leof_trans] 
        hm_repair_op_\<alpha>_correct[THEN leof_trans]
        hm_index_op_inline_leof)
      unfolding heapmap_rel_def in_br_conv
      apply simp
      apply simp
      done

    lemma hm_change_key_op_aref: 
      "(hm_change_key_op, mop_map_update_ex) \<in> Id \<rightarrow> Id \<rightarrow> heapmap_rel \<rightarrow> \<langle>heapmap_rel\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      apply (frule heapmap_hmr_relI)
      unfolding mop_map_update_ex_alt
      apply (rule ASSERT_refine_right; clarsimp)
      apply (rule heapmap_nres_relI')
      apply (rule hm_change_key_op_refine; assumption)
      unfolding heapmap_rel_def hmr_rel_def in_br_conv
      apply (rule h.change_key_op_invar; simp; fail )
      apply ((refine_vcg hm_change_key_op_\<alpha>_correct[THEN leof_trans]; simp))
      done

    subsubsection \<open>Set\<close>  

    text \<open>Realized as generic algorithm!\<close> (* TODO: Implement as such! *)
    lemma (in -) op_pm_set_gen_impl: "RETURN ooo op_map_update = (\<lambda>k v m. do {
      c \<leftarrow> RETURN (op_map_contains_key k m);
      if c then 
        mop_map_update_ex k v m
      else
        mop_map_update_new k v m
    })"
      apply (intro ext)
      unfolding op_map_contains_key_def mop_map_update_ex_def mop_map_update_new_def
      by simp

    definition "hm_set_op k v hm \<equiv> do {
      c \<leftarrow> hm_contains_key_op k hm;
      if c then
        hm_change_key_op k v hm
      else
        hm_insert_op k v hm
    }"

    lemma hm_set_op_aref: 
      "(hm_set_op, RETURN ooo op_map_update) \<in> Id \<rightarrow> Id \<rightarrow> heapmap_rel \<rightarrow> \<langle>heapmap_rel\<rangle>nres_rel"
      unfolding op_pm_set_gen_impl
      apply (intro fun_relI nres_relI)
      unfolding hm_set_op_def o_def
      apply (refine_rcg 
        hm_contains_key_op_aref[param_fo, unfolded o_def, THEN nres_relD]
        hm_change_key_op_aref[param_fo, THEN nres_relD]
        hm_insert_op_aref[param_fo, THEN nres_relD]
        )
      by auto


 
    subsubsection \<open>Pop-Min\<close>  

    definition hm_pop_min_op :: "('k,'v) ahm \<Rightarrow> (('k\<times>'v) \<times> ('k,'v) ahm) nres" where
      "hm_pop_min_op hm \<equiv> do {
        ASSERT (heapmap_invar hm);
        ASSERT (hm_valid hm 1);
        k \<leftarrow> hm_key_of_op hm 1;
        v \<leftarrow> hm_the_lookup_op hm k;
        let l = hm_length hm;
        hm \<leftarrow> hm_exch_op hm 1 l;
        hm \<leftarrow> hm_butlast_op hm;
        
        if (l\<noteq>1) then do {
          hm \<leftarrow> hm_sink_op hm 1;
          RETURN ((k,v),hm)
        } else RETURN ((k,v),hm)
      }"

    lemma hm_pop_min_op_refine: 
      "(hm_pop_min_op, h.pop_min_op) \<in> hmr_rel \<rightarrow> \<langle>UNIV \<times>\<^sub>r hmr_rel\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding hm_pop_min_op_def h.pop_min_op_def
      (* Project away stuff of second component *)
      unfolding ignore_snd_refine_conv hm_the_lookup_op_def hm_key_of_op_unfold
      apply (simp cong: if_cong add: Let_def)
      apply (simp add: unused_bind_conv h.val_of_op_def refine_pw_simps)

      (* Prove refinement *)
      apply refine_rcg
      unfolding hmr_rel_def in_br_conv
      apply (unfold heapmap_invar_def;simp)
      apply (auto simp: in_br_conv)
      done

    text \<open>We demonstrate two different approaches for proving correctness 
      here.
      The first approach uses the relation to plain heaps only to establish
      the invariant. 

      The second approach also uses the relation to heaps to establish 
      correctness of the result.

      The first approach seems to be more robust against badly set 
      up simpsets, which may be the case in early stages of development.

      Assuming a working simpset, the second approach may be less work,
      and the proof may look more elegant.
      \<close>  

    text_raw \<open>\paragraph{First approach}\<close>
    text \<open>Transfer heapmin-property to heapmap-domain\<close>
    lemma heapmap_min_prop:
      assumes INV: "heapmap_invar hm"  
      assumes V': "heapmap_\<alpha> hm k = Some v'"
      assumes NE: "hm_valid hm (Suc 0)"
      shows "prio (the (heapmap_\<alpha> hm (hm_key_of hm (Suc 0)))) \<le> prio v'"
    proof -  
      \<comment> \<open>Transform into the domain of heaps\<close>
      obtain pq m where [simp]: "hm=(pq,m)" by (cases hm)

      from NE have [simp]: "pq\<noteq>[]" by (auto simp: hm_valid_def hm_length_def)

      have CNV_LHS: "prio (the (heapmap_\<alpha> hm (hm_key_of hm (Suc 0)))) 
        = h.prio_of (hmr_\<alpha> hm) (Suc 0)"
        by (auto simp: heapmap_\<alpha>_def hm_key_of_def hmr_\<alpha>_def h.val_of_def)
        
      from INV have INV': "h.heap_invar (hmr_\<alpha> hm)"  
        unfolding heapmap_invar_def by auto

      from V' INV obtain i where IDX: "h.valid (hmr_\<alpha> hm) i" 
        and CNV_RHS: "prio v' = h.prio_of (hmr_\<alpha> hm) i" 
        apply (clarsimp simp: heapmap_\<alpha>_def heapmap_invar_def hmr_invar_def hmr_\<alpha>_def
          h.valid_def h.val_of_def)
        by (metis (no_types, hide_lams) Suc_leI comp_apply diff_Suc_Suc 
          diff_zero domI index_less_size_conv neq0_conv nth_index nth_map 
          old.nat.distinct(2) option.sel)
        
      from h.heap_min_prop[OF INV' IDX] show ?thesis
        unfolding CNV_LHS CNV_RHS .
    qed    


    text \<open>With the above lemma, the correctness proof is straightforward\<close>
    lemma hm_pop_min_\<alpha>_correct: "hm_pop_min_op hm \<le>\<^sub>n SPEC (\<lambda>((k,v),hm'). 
        heapmap_\<alpha> hm k = Some v 
      \<and> heapmap_\<alpha> hm' = (heapmap_\<alpha> hm)(k:=None) 
      \<and> (\<forall>k' v'. heapmap_\<alpha> hm k' = Some v' \<longrightarrow> prio v \<le> prio v'))"  
      unfolding hm_pop_min_op_def hm_key_of_op_unfold hm_the_lookup_op_def
      apply (refine_vcg 
        hm_exch_op_\<alpha>_correct[THEN leof_trans]
        hm_butlast_op_\<alpha>_correct[THEN leof_trans]
        hm_sink_op_\<alpha>_correct[THEN leof_trans]
        )
      apply (auto simp: heapmap_min_prop)
      done  

    lemma heapmap_nres_rel_prodI:
      assumes "hmx \<le> \<Down>(UNIV \<times>\<^sub>r hmr_rel) h'x"
      assumes "h'x \<le> SPEC (\<lambda>(_,h'). h.heap_invar h')"
      assumes "hmx \<le>\<^sub>n SPEC (\<lambda>(r,hm'). RETURN (r,heapmap_\<alpha> hm') \<le> \<Down>(R\<times>\<^sub>rId) hx)"
      shows "hmx \<le> \<Down>(R\<times>\<^sub>rheapmap_rel) hx"
      using assms
      unfolding heapmap_rel_def hmr_rel_def br_def heapmap_invar_def
      apply (auto simp: pw_le_iff pw_leof_iff refine_pw_simps; blast)
      done
      

    lemma hm_pop_min_op_aref: "(hm_pop_min_op, PR_CONST (mop_pm_pop_min prio)) \<in> heapmap_rel \<rightarrow> \<langle>(Id\<times>\<^sub>rId)\<times>\<^sub>rheapmap_rel\<rangle>nres_rel"  
      unfolding PR_CONST_def
      apply (intro fun_relI nres_relI)
      apply (frule heapmap_hmr_relI)
      unfolding mop_pm_pop_min_alt
      apply (intro ASSERT_refine_right)
      apply (rule heapmap_nres_rel_prodI)
      apply (rule hm_pop_min_op_refine[param_fo, THEN nres_relD]; assumption)
      unfolding heapmap_rel_def hmr_rel_def in_br_conv
      apply (refine_vcg; simp)
      apply (refine_vcg hm_pop_min_\<alpha>_correct[THEN leof_trans]; simp split: prod.splits)
      done
      
    text_raw \<open>\paragraph{Second approach}\<close>

    (* Alternative approach: Also use knowledge about result
      in multiset domain. Obtaining property seems infeasible at first attempt! *)  

    definition "hm_kv_of_op hm i \<equiv> do {
      ASSERT (hm_valid hm i \<and> hmr_invar hm);
      k \<leftarrow> hm_key_of_op hm i;
      v \<leftarrow> hm_the_lookup_op hm k;
      RETURN (k, v)
    }"


    definition "kvi_rel hm i \<equiv> {((k,v),v) | k v. hm_key_of hm i = k}"

    lemma hm_kv_op_refine[refine]:
      assumes "(hm,h)\<in>hmr_rel"
      shows "hm_kv_of_op hm i \<le> \<Down>(kvi_rel hm i) (h.val_of_op h i)"
      unfolding hm_kv_of_op_def h.val_of_op_def kvi_rel_def 
        hm_key_of_op_unfold hm_the_lookup_op_def
      apply simp  
      apply refine_vcg
      using assms
      by (auto 
        simp: hm_valid_def hm_length_def hmr_rel_defs heapmap_\<alpha>_def hm_key_of_def
        split: prod.splits)

    definition hm_pop_min_op' :: "('k,'v) ahm \<Rightarrow> (('k\<times>'v) \<times> ('k,'v) ahm) nres" where
      "hm_pop_min_op' hm \<equiv> do {
        ASSERT (heapmap_invar hm);
        ASSERT (hm_valid hm 1);
        kv \<leftarrow> hm_kv_of_op hm 1;
        let l = hm_length hm;
        hm \<leftarrow> hm_exch_op hm 1 l;
        hm \<leftarrow> hm_butlast_op hm;
        
        if (l\<noteq>1) then do {
          hm \<leftarrow> hm_sink_op hm 1;
          RETURN (kv,hm)
        } else RETURN (kv,hm)
      }"


    lemma hm_pop_min_op_refine': 
      "\<lbrakk> (hm,h)\<in>hmr_rel \<rbrakk> \<Longrightarrow> hm_pop_min_op' hm \<le> \<Down>(kvi_rel hm 1 \<times>\<^sub>r hmr_rel) (h.pop_min_op h)"
      unfolding hm_pop_min_op'_def h.pop_min_op_def
      (* Project away stuff of second component *)
      unfolding ignore_snd_refine_conv
      (* Prove refinement *)
      apply refine_rcg
      unfolding hmr_rel_def heapmap_rel_def
      apply (unfold heapmap_invar_def; simp add: in_br_conv)
      apply (simp_all add: in_br_conv)
      done


    lemma heapmap_nres_rel_prodI':
      assumes "hmx \<le> \<Down>(S \<times>\<^sub>r hmr_rel) h'x"
      assumes "h'x \<le> SPEC \<Phi>"
      assumes "\<And>h' r. \<Phi> (r,h') \<Longrightarrow> h.heap_invar h'"
      assumes "hmx \<le>\<^sub>n SPEC (\<lambda>(r,hm'). (\<exists>r'. (r,r')\<in>S \<and> \<Phi> (r',hmr_\<alpha> hm')) \<and> hmr_invar hm' \<longrightarrow> RETURN (r,heapmap_\<alpha> hm') \<le> \<Down>(R\<times>\<^sub>rId) hx)"
      shows "hmx \<le> \<Down>(R\<times>\<^sub>rheapmap_rel) hx"
      using assms
      unfolding heapmap_rel_def hmr_rel_def heapmap_invar_def
      apply (auto 
        simp: pw_le_iff pw_leof_iff refine_pw_simps in_br_conv
        )
      by meson

    lemma ex_in_kvi_rel_conv:
      "(\<exists>r'. (r,r')\<in>kvi_rel hm i \<and> \<Phi> r') \<longleftrightarrow> (fst r = hm_key_of hm i \<and> \<Phi> (snd r))"  
      unfolding kvi_rel_def
      apply (cases r)
      apply auto
      done

      
    lemma hm_pop_min_aref': "(hm_pop_min_op', mop_pm_pop_min prio) \<in> heapmap_rel \<rightarrow> \<langle>(Id\<times>\<^sub>rId) \<times>\<^sub>r heapmap_rel\<rangle>nres_rel"  
      apply (intro fun_relI nres_relI)
      apply (frule heapmap_hmr_relI)
      unfolding mop_pm_pop_min_alt
      apply (intro ASSERT_refine_right)
      apply (rule heapmap_nres_rel_prodI')
        apply (erule hm_pop_min_op_refine')

        apply (unfold heapmap_rel_def hmr_rel_def in_br_conv) []
        apply (rule h.pop_min_op_correct)
        apply simp
        apply simp

        apply simp

        apply (clarsimp simp: ex_in_kvi_rel_conv split: prod.splits)
        unfolding hm_pop_min_op'_def hm_kv_of_op_def hm_key_of_op_unfold
          hm_the_lookup_op_def
        apply (refine_vcg 
          hm_exch_op_\<alpha>_correct[THEN leof_trans]
          hm_butlast_op_\<alpha>_correct[THEN leof_trans]
          hm_sink_op_\<alpha>_correct[THEN leof_trans]
          )
        unfolding heapmap_rel_def hmr_rel_def in_br_conv
        apply (auto intro: ranI) 
      done

    subsubsection \<open>Remove\<close>  

    definition "hm_remove_op k hm \<equiv> do {
      ASSERT (heapmap_invar hm);
      ASSERT (k \<in> dom (heapmap_\<alpha> hm));
      i \<leftarrow> hm_index_op hm k;
      let l = hm_length hm;
      hm \<leftarrow> hm_exch_op hm i l;
      hm \<leftarrow> hm_butlast_op hm;
      if i \<noteq> l then
        hm_repair_op hm i
      else  
        RETURN hm
    }"

    definition (in heapstruct) "remove_op i h \<equiv> do {
      ASSERT (heap_invar h);
      ASSERT (valid h i);
      let l = length h;
      h \<leftarrow> exch_op h i l;
      h \<leftarrow> butlast_op h;
      if i \<noteq> l then
        repair_op h i
      else  
        RETURN h
    }"

    lemma (in -) swap_empty_iff[iff]: "swap l i j = [] \<longleftrightarrow> l=[]"
      by (auto simp: swap_def)

    lemma (in heapstruct) 
      butlast_exch_last: "butlast (exch h i (length h)) = update (butlast h) i (last h)"  
      unfolding exch_def update_def
      apply (cases h rule: rev_cases)
      apply (auto simp: swap_def butlast_list_update)
      done

    lemma (in heapstruct) remove_op_invar: 
      "\<lbrakk> heap_invar h; valid h i \<rbrakk> \<Longrightarrow> remove_op i h \<le> SPEC heap_invar"
      unfolding remove_op_def
      apply refine_vcg
      apply (auto simp: valid_def) []
      apply (auto simp: valid_def exch_def) []
      apply (simp add: butlast_exch_last)
      apply refine_vcg
      apply auto []
      apply auto []
      apply (auto simp: valid_def) []
      apply auto []
      apply auto []
      done

    lemma hm_remove_op_refine[refine]: 
      "\<lbrakk> (hm,m)\<in>heapmap_rel; (hm,h)\<in>hmr_rel; heapmap_\<alpha> hm k \<noteq> None\<rbrakk> \<Longrightarrow> 
        hm_remove_op k hm \<le> \<Down>hmr_rel (h.remove_op (hm_index hm k) h)"
      unfolding hm_remove_op_def h.remove_op_def heapmap_rel_def
      (*apply (rewrite at "Let (hm_index hm k) _" Let_def)*)
      apply (refine_rcg index_op_inline_refine)
      unfolding hmr_rel_def
      apply (auto simp: in_br_conv)
      done

    lemma hm_remove_op_\<alpha>_correct: 
      "hm_remove_op k hm \<le>\<^sub>n SPEC (\<lambda>hm'. heapmap_\<alpha> hm' = (heapmap_\<alpha> hm)(k:=None))"  
      unfolding hm_remove_op_def
      apply (refine_vcg 
        hm_exch_op_\<alpha>_correct[THEN leof_trans]
        hm_butlast_op_\<alpha>_correct[THEN leof_trans]
        hm_repair_op_\<alpha>_correct[THEN leof_trans]
        hm_index_op_inline_leof
        )
      apply (auto; fail)
      
      apply clarsimp
      apply (rewrite at "hm_index _ k = hm_length _" in asm eq_commute)
      apply (auto; fail)
      done

    lemma hm_remove_op_aref:
      "(hm_remove_op,mop_map_delete_ex) \<in> Id \<rightarrow> heapmap_rel \<rightarrow> \<langle>heapmap_rel\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding mop_map_delete_ex_alt
      apply (rule ASSERT_refine_right)
      apply (frule heapmap_hmr_relI)
      apply (rule heapmap_nres_relI')
      apply (rule hm_remove_op_refine; assumption?)
      apply (unfold heapmap_rel_def in_br_conv; auto)

      unfolding heapmap_rel_def hmr_rel_def in_br_conv 
      apply (refine_vcg h.remove_op_invar; clarsimp; fail)
      apply (refine_vcg hm_remove_op_\<alpha>_correct[THEN leof_trans]; simp; fail)
      done
      
    subsubsection \<open>Peek-Min\<close> 


    definition hm_peek_min_op :: "('k,'v) ahm \<Rightarrow> ('k\<times>'v) nres" where
      "hm_peek_min_op hm \<equiv> hm_kv_of_op hm 1"

    lemma hm_peek_min_op_aref: 
      "(hm_peek_min_op, PR_CONST (mop_pm_peek_min prio)) \<in> heapmap_rel \<rightarrow> \<langle>Id\<times>\<^sub>rId\<rangle>nres_rel"  
      unfolding PR_CONST_def
      apply (intro fun_relI nres_relI)
    proof -  
      fix hm and m :: "'k \<rightharpoonup> 'v"
      assume A: "(hm,m)\<in>heapmap_rel"
      
      from A have [simp]: "h.heap_invar (hmr_\<alpha> hm)" "hmr_invar hm" "m=heapmap_\<alpha> hm"
        unfolding heapmap_rel_def in_br_conv heapmap_invar_def
        by simp_all

      have "hm_peek_min_op hm \<le> \<Down> (kvi_rel hm 1) (h.peek_min_op (hmr_\<alpha> hm))"
        unfolding hm_peek_min_op_def  h.peek_min_op_def
        apply (refine_rcg hm_kv_op_refine)
        using A
        apply (simp add: heapmap_hmr_relI)
        done
      also have "\<lbrakk>hmr_\<alpha> hm \<noteq> []\<rbrakk> \<Longrightarrow> (h.peek_min_op (hmr_\<alpha> hm)) 
        \<le> SPEC (\<lambda>v. v\<in>ran (heapmap_\<alpha> hm) \<and> (\<forall>v'\<in>ran (heapmap_\<alpha> hm). prio v \<le> prio v'))"  
        apply refine_vcg
        by simp_all
      finally show "hm_peek_min_op hm \<le> \<Down> (Id \<times>\<^sub>r Id) (mop_pm_peek_min prio m)"  
        unfolding mop_pm_peek_min_alt
        apply (simp add: pw_le_iff refine_pw_simps hm_peek_min_op_def hm_kv_of_op_def 
            hm_key_of_op_unfold hm_the_lookup_op_def)
        apply (fastforce simp: kvi_rel_def ran_def)
        done

    qed    


  end

end
