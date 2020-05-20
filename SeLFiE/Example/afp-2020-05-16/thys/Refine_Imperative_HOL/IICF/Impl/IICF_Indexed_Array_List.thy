theory IICF_Indexed_Array_List
imports 
  "HOL-Library.Rewrite"
  "../Intf/IICF_List"
  "List-Index.List_Index"
  IICF_Array
  IICF_MS_Array_List
begin

  text \<open>We implement distinct lists of natural numbers in the range \<open>{0..<N}\<close>
    by a length counter and two arrays of size \<open>N\<close>. 
    The first array stores the list, and the second array stores the positions of
    the elements in the list, or \<open>N\<close> if the element is not in the list.

    This allows for an efficient index query.

    The implementation is done in two steps: 
      First, we use a list and a fixed size list for the index mapping.
      Second, we refine the lists to arrays.
 \<close>

  type_synonym aial = "nat list \<times> nat list"

  locale ial_invar = fixes
         maxsize :: nat 
    and  l :: "nat list"
    and qp :: "nat list"
    assumes maxsize_eq[simp]: "maxsize = length qp"
    assumes l_distinct[simp]: "distinct l"
    assumes l_set: "set l \<subseteq> {0..<length qp}"
    assumes qp_def: "\<forall>k<length qp. qp!k = (if k\<in>set l then List_Index.index l k else length qp)"
  begin  
    lemma l_len: "length l \<le> length qp"
    proof -
      from card_mono[OF _ l_set] have "card (set l) \<le> length qp" by auto
      with distinct_card[OF l_distinct] show ?thesis by simp
    qed  

    lemma idx_len[simp]: "i<length l \<Longrightarrow> l!i < length qp"
      using l_set
      by (metis atLeastLessThan_iff nth_mem psubsetD psubsetI)

    lemma l_set_simp[simp]: "k\<in>set l \<Longrightarrow> k < length qp" 
      by (auto dest: subsetD[OF l_set])

    lemma qpk_idx: "k<length qp \<Longrightarrow> qp ! k < length l \<longleftrightarrow> k \<in> set l"
    proof (rule iffI)
      assume A: "k<length qp"
      {
        assume "qp!k < length l"
        hence "qp!k < length qp" using l_len by simp
        with spec[OF qp_def, of k] A show "k\<in>set l" 
          by (auto split: if_split_asm)
      }
      {
        assume "k\<in>set l"
        thus "qp!k<length l"
          using qp_def by (auto split: if_split_asm) []
      }
    qed 

    lemma lqpk[simp]: "k \<in> set l \<Longrightarrow> l ! (qp ! k) = k"
      using spec[OF qp_def, of k] by auto

    lemma "\<lbrakk>i<length l; j<length l; l!i=l!j\<rbrakk> \<Longrightarrow> i=j"
      by (simp add: nth_eq_iff_index_eq)
      
    lemmas index_swap[simp] = index_swap_if_distinct[folded swap_def, OF l_distinct]  

    lemma swap_invar:  
      assumes "i<length l" "j<length l"
      shows "ial_invar (length qp) (swap l i j) (qp[l ! j := i, l ! i := j])"
      using assms
      apply unfold_locales
      apply auto []
      apply auto []
      apply auto []
      apply (auto simp: simp: nth_list_update nth_eq_iff_index_eq index_nth_id) []
      using qp_def apply auto [2]
      done

  end

  definition "ial_rel1 maxsize \<equiv> br fst (uncurry (ial_invar maxsize))"

  definition ial_assn2 :: "nat \<Rightarrow> nat list * nat list \<Rightarrow> _" where
    "ial_assn2 maxsize \<equiv> prod_assn (marl_assn maxsize nat_assn) (array_assn nat_assn)"

(*  definition "ial_assn maxsize \<equiv> hr_comp (ial_assn2 maxsize) (ial_rel1 maxsize)"*)

  definition "ial_assn maxsize A \<equiv> hr_comp (hr_comp (ial_assn2 maxsize) (ial_rel1 maxsize)) (\<langle>the_pure A\<rangle>list_rel)"
  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "ial_assn maxsize A" for maxsize A]

(*  lemma ial_assn_precise[constraint_rules]: "precise (ial_assn maxsize)"
    unfolding ial_assn_def ial_rel1_def ial_assn2_def
    apply constraint_rules
*)



  subsection \<open>Empty\<close>

  definition op_ial_empty_sz :: "nat \<Rightarrow> 'a list" 
    where [simp]: "op_ial_empty_sz ms \<equiv> op_list_empty"

  lemma [def_pat_rules]: "op_ial_empty_sz$maxsize \<equiv> UNPROTECT (op_ial_empty_sz maxsize)"  
    by simp

  context fixes maxsize :: nat begin
  sepref_register "PR_CONST (op_ial_empty_sz maxsize)"
  end

  context 
    fixes maxsize :: nat (* If we do not fix maxsize here, the FCOMP-rule will 
      derive a more general rule with two different maxsizes! *)
    notes [fcomp_norm_unfold] = ial_assn_def[symmetric]  
    notes [simp] = hn_ctxt_def pure_def
  begin  
  
    definition "aial_empty \<equiv> do {
      let l = op_marl_empty_sz maxsize;
      let qp = op_array_replicate maxsize maxsize;
      RETURN (l,qp)
    }"

    lemma aial_empty_impl: "(aial_empty,RETURN op_list_empty) \<in> \<langle>ial_rel1 maxsize\<rangle>nres_rel"
      unfolding aial_empty_def
      apply (refine_vcg nres_relI)
      apply (clarsimp simp: ial_rel1_def br_def)
      apply unfold_locales
      apply auto
      done

    (* Note: This lemma requires some setup to handle maxsize simultaneously
      as a parameter, and as a constant. 
    *)
    context 
      notes [id_rules] = itypeI[Pure.of maxsize "TYPE(nat)"]
      notes [sepref_import_param] = IdI[of maxsize]
    begin
    sepref_definition ial_empty is "uncurry0 aial_empty" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a ial_assn2 maxsize"
      unfolding aial_empty_def ial_assn2_def
      using [[id_debug]]
      by sepref
    end  

    sepref_decl_impl (no_register) ial_empty: ial_empty.refine[FCOMP aial_empty_impl] .
    lemma ial_empty_sz_hnr[sepref_fr_rules]: 
      "(uncurry0 local.ial_empty, uncurry0 (RETURN (PR_CONST (op_ial_empty_sz maxsize)))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a ial_assn maxsize A"
      using ial_empty_hnr[of A] by simp
  
    subsection \<open>Swap\<close>
    definition "aial_swap \<equiv> \<lambda>(l,qp) i j. do {
      vi \<leftarrow> mop_list_get l i;
      vj \<leftarrow> mop_list_get l j;
      l \<leftarrow> mop_list_set l i vj;
      l \<leftarrow> mop_list_set l j vi;
      qp \<leftarrow> mop_list_set qp vj i;
      qp \<leftarrow> mop_list_set qp vi j;
      RETURN (l,qp)
    }"

    lemma in_ial_rel1_conv: 
      "((pq, qp), l) \<in> ial_rel1 ms \<longleftrightarrow> pq=l \<and> ial_invar ms l qp" 
      by (auto simp: ial_rel1_def in_br_conv)

    lemma aial_swap_impl: 
      "(aial_swap,mop_list_swap) \<in> ial_rel1 maxsize \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>ial_rel1 maxsize\<rangle>nres_rel"
    proof (intro fun_relI nres_relI; clarsimp simp: in_ial_rel1_conv; refine_vcg; clarsimp)
      fix l qp i j
      assume [simp]: "i<length l" "j<length l" and "ial_invar maxsize l qp"
      then interpret ial_invar maxsize l qp by simp

      show "aial_swap (l, qp) i j \<le> SPEC (\<lambda>c. (c, swap l i j) \<in> ial_rel1 maxsize)"
        unfolding aial_swap_def
        apply refine_vcg
        apply (vc_solve simp add: in_ial_rel1_conv swap_def[symmetric] swap_invar)
        done
    qed    
  
    sepref_definition ial_swap is
      "uncurry2 aial_swap" :: "(ial_assn2 maxsize)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a ial_assn2 maxsize"
      unfolding aial_swap_def ial_assn2_def
      by sepref

    sepref_decl_impl (ismop) test: ial_swap.refine[FCOMP aial_swap_impl] 
      uses mop_list_swap.fref .

    subsection \<open>Length\<close>
    definition aial_length :: "aial \<Rightarrow> nat nres" 
      where "aial_length \<equiv> \<lambda>(l,_). RETURN (op_list_length l)"
  
    lemma aial_length_impl: "(aial_length, mop_list_length) \<in> ial_rel1 maxsize \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding ial_rel1_def in_br_conv aial_length_def
      by auto

    sepref_definition ial_length is "aial_length" :: "(ial_assn2 maxsize)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
      unfolding aial_length_def ial_assn2_def
      by sepref

    sepref_decl_impl (ismop) ial_length: ial_length.refine[FCOMP aial_length_impl] .  
    
    subsection \<open>Index\<close>  
    
    definition aial_index :: "aial \<Rightarrow> nat \<Rightarrow> nat nres" where
      "aial_index \<equiv> \<lambda>(l,qp) k. do {
        ASSERT (k\<in>set l);
        i \<leftarrow> mop_list_get qp k;
        RETURN i
      }"
  
    lemma aial_index_impl: 
      "(uncurry aial_index, uncurry mop_list_index) \<in> 
        [\<lambda>(l,k). k\<in>set l]\<^sub>f ial_rel1 maxsize \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"  
      apply (intro fun_relI nres_relI frefI)
      unfolding ial_rel1_def
    proof (clarsimp simp:  in_br_conv)
      fix l qp k
      assume "ial_invar maxsize l qp"
      then interpret ial_invar maxsize l qp .
  
      assume "k\<in>set l"
      then show "aial_index (l,qp) k \<le> RETURN (index l k)"
        unfolding aial_index_def
        apply (refine_vcg)
        by (auto simp: qp_def)
    qed
  
    sepref_definition ial_index is "uncurry aial_index" :: "(ial_assn2 maxsize)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
      unfolding aial_index_def ial_assn2_def
      by sepref

    sepref_decl_impl (ismop) ial_index: ial_index.refine[FCOMP aial_index_impl] .

    subsection \<open>Butlast\<close>  
    definition aial_butlast :: "aial \<Rightarrow> aial nres" where
      "aial_butlast \<equiv> \<lambda>(l,qp). do {
        ASSERT (l\<noteq>[]);
        len \<leftarrow> mop_list_length l;
        k \<leftarrow> mop_list_get l (len - 1);
        l \<leftarrow> mop_list_butlast l;
        qp \<leftarrow> mop_list_set qp k (length qp);
        RETURN (l,qp)
      }"
  
    lemma aial_butlast_refine: "(aial_butlast, mop_list_butlast) \<in> ial_rel1 maxsize \<rightarrow> \<langle>ial_rel1 maxsize\<rangle>nres_rel"  
      apply (intro fun_relI nres_relI)
      unfolding ial_rel1_def
    proof (clarsimp simp: in_br_conv simp del: mop_list_butlast_alt)
      fix l qp
      assume "ial_invar maxsize l qp"
      then interpret ial_invar maxsize l qp .
  
      {
        assume A: "l\<noteq>[]"
        have "ial_invar (length qp) (butlast l) (qp[l ! (length l - Suc 0) := length qp])"
          apply standard
          apply clarsimp_all
          apply (auto simp: distinct_butlast) []
          using l_set apply (auto dest: in_set_butlastD) []
          using qp_def A l_distinct
          apply (auto simp: nth_list_update neq_Nil_rev_conv index_append simp del: l_distinct)
          done
      } note aux1=this
  
      show "aial_butlast (l, qp) \<le> \<Down> (br fst (uncurry (ial_invar maxsize))) (mop_list_butlast l)"
        unfolding aial_butlast_def mop_list_butlast_alt
        apply refine_vcg
        apply (clarsimp_all simp: in_br_conv aux1)
        done
    qed    

    sepref_definition ial_butlast is aial_butlast :: "(ial_assn2 maxsize)\<^sup>d \<rightarrow>\<^sub>a ial_assn2 maxsize"
      unfolding aial_butlast_def ial_assn2_def by sepref

    sepref_decl_impl (ismop) ial_butlast: ial_butlast.refine[FCOMP aial_butlast_refine] .

    subsection \<open>Append\<close>  
    definition aial_append :: "aial \<Rightarrow> nat \<Rightarrow> aial nres" where
      "aial_append \<equiv> \<lambda>(l,qp) k. do {
        ASSERT (k<length qp \<and> k\<notin>set l \<and> length l < length qp);
        len \<leftarrow> mop_list_length l;
        l \<leftarrow> mop_list_append l k;
        qp \<leftarrow> mop_list_set qp k len;
        RETURN (l,qp)
      }"

    lemma aial_append_refine: 
      "(uncurry aial_append,uncurry mop_list_append) \<in> 
        [\<lambda>(l,k). k<maxsize \<and> k\<notin>set l]\<^sub>f ial_rel1 maxsize \<times>\<^sub>r nat_rel \<rightarrow> \<langle>ial_rel1 maxsize\<rangle>nres_rel"
      apply (intro frefI nres_relI)  
      unfolding ial_rel1_def
    proof (clarsimp simp: in_br_conv)
      fix l qp k
      assume KLM: "k<maxsize" and KNL: "k\<notin>set l"
      assume "ial_invar maxsize l qp"
      then interpret ial_invar maxsize l qp .
    
      from KLM have KLL: "k<length qp" by simp
    
      note distinct_card[OF l_distinct, symmetric]
      also from KNL l_set have "set l \<subseteq> {0..<k} \<union> {Suc k..<length qp}"
        by (auto simp: nat_less_le)
      from card_mono[OF _ this] have "card (set l) \<le> card \<dots>"
        by simp
      also note card_Un_le
      also have "card {0..<k} + card {Suc k..<length qp} = k + (length qp - Suc k)" 
        by simp
      also have "\<dots> < length qp" using KLL by simp
      finally have LLEN: "length l < length qp" .
    
      have aux1[simp]: "ial_invar (length qp) (l @ [k]) (qp[k := length l])"
        apply standard
        apply (clarsimp_all simp: KNL KLL)
        using KLL apply (auto simp: Suc_le_eq LLEN) []
        apply (auto simp: index_append KNL nth_list_update')
        apply (simp add: qp_def)
        apply (simp add: qp_def)
        done
    
      show "aial_append (l, qp) k \<le> \<Down> (br fst (uncurry (ial_invar maxsize))) (RETURN (l@[k]))"
        unfolding aial_append_def mop_list_append_def
        apply refine_vcg
        apply (clarsimp_all simp: in_br_conv KLL KNL LLEN)
        done
    qed    

    private lemma aial_append_impl_aux: "((l, qp), l') \<in> ial_rel1 maxsize \<Longrightarrow> l'=l \<and> maxsize = length qp"
      unfolding ial_rel1_def
      by (clarsimp simp: in_br_conv ial_invar.maxsize_eq[symmetric])

    context      
      notes [dest!] = aial_append_impl_aux
    begin  
      (* TODO: Should we integrate the domain-condition, or some similar condition, 
        as assertion (relating length l and length qp) or into ial_assn2 ? *)
      sepref_definition ial_append is 
        "uncurry aial_append" :: "[\<lambda>(lqp,_). lqp\<in>Domain (ial_rel1 maxsize)]\<^sub>a (ial_assn2 maxsize)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> ial_assn2 maxsize"
        unfolding aial_append_def ial_assn2_def
        by sepref
    end    

    lemma "(\<lambda>b. b<maxsize, X) \<in> A \<rightarrow> bool_rel"
      apply auto
      oops

    context begin  
      (* TODO: Maybe inject additional restrictions on sepref_decl_impl command *)
      (* TODO: Maybe require Domain R \<subseteq> {0..<maxsize} instead ? *)
      private lemma append_fref': "\<lbrakk>IS_BELOW_ID R\<rbrakk> 
        \<Longrightarrow> (uncurry mop_list_append, uncurry mop_list_append) \<in> \<langle>R\<rangle>list_rel \<times>\<^sub>r R \<rightarrow>\<^sub>f \<langle>\<langle>R\<rangle>list_rel\<rangle>nres_rel"  
        by (rule mop_list_append.fref)
  
      sepref_decl_impl (ismop) ial_append: ial_append.refine[FCOMP aial_append_refine] uses append_fref'
        unfolding IS_BELOW_ID_def
        apply (parametricity; auto simp: single_valued_below_Id)
        done
    end    

    (*
    lemmas ial_append_hnr_mop[sepref_fr_rules] = ial_append.refine[FCOMP aial_append_refine]
    lemmas ial_append_hnr[sepref_fr_rules] = ial_append_hnr_mop[FCOMP mk_op_rl2_np[OF mop_list_append_alt]]
    *)

    subsection \<open>Get\<close>
    
    definition aial_get :: "aial \<Rightarrow> nat \<Rightarrow> nat nres" where
      "aial_get \<equiv> \<lambda>(l,qp) i. mop_list_get l i"
  
    lemma aial_get_refine: "(aial_get,mop_list_get) \<in> ial_rel1 maxsize \<rightarrow> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"  
      apply (intro fun_relI nres_relI)
      unfolding aial_get_def ial_rel1_def mop_list_get_def in_br_conv
      apply refine_vcg
      apply clarsimp_all
      done

    sepref_definition ial_get is "uncurry aial_get" :: "(ial_assn2 maxsize)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
      unfolding aial_get_def ial_assn2_def by sepref

    sepref_decl_impl (ismop) ial_get: ial_get.refine[FCOMP aial_get_refine] .  

    subsection \<open>Contains\<close>
    
    definition aial_contains :: "nat \<Rightarrow> aial \<Rightarrow> bool nres" where
      "aial_contains \<equiv> \<lambda>k (l,qp). do {
        if k<maxsize then do {
          i \<leftarrow> mop_list_get qp k;
          RETURN (i<maxsize)
        } else RETURN False  
      }"
  
    lemma aial_contains_refine: "(uncurry aial_contains,uncurry mop_list_contains) 
      \<in> (nat_rel \<times>\<^sub>r ial_rel1 maxsize) \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel"  
      apply (intro frefI nres_relI)
      unfolding ial_rel1_def
    proof (clarsimp simp: in_br_conv)
      fix l qp k
      (*assume A: "k<maxsize"*)
      assume "ial_invar maxsize l qp"
      then interpret ial_invar maxsize l qp .

      show "aial_contains k (l, qp) \<le> RETURN (k\<in>set l)"
        unfolding aial_contains_def
        apply refine_vcg
        by (auto simp: l_len qp_def split: if_split_asm)
    qed    
  
    context 
      notes [id_rules] = itypeI[Pure.of maxsize "TYPE(nat)"]
      notes [sepref_import_param] = IdI[of maxsize]
    begin
      sepref_definition ial_contains is "uncurry aial_contains" :: "nat_assn\<^sup>k *\<^sub>a (ial_assn2 maxsize)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
        unfolding aial_contains_def ial_assn2_def by sepref
    end  

    sepref_decl_impl (ismop) ial_contains: ial_contains.refine[FCOMP aial_contains_refine] .
  end

end
