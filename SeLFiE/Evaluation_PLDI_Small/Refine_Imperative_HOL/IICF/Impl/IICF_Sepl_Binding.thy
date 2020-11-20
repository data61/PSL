section \<open>Sepref Bindings for Imp/HOL Collections\<close>
theory IICF_Sepl_Binding
imports 
  Separation_Logic_Imperative_HOL.Imp_Map_Spec
  Separation_Logic_Imperative_HOL.Imp_Set_Spec
  Separation_Logic_Imperative_HOL.Imp_List_Spec

  Separation_Logic_Imperative_HOL.Hash_Map_Impl
  Separation_Logic_Imperative_HOL.Array_Map_Impl

  Separation_Logic_Imperative_HOL.To_List_GA
  Separation_Logic_Imperative_HOL.Hash_Set_Impl
  Separation_Logic_Imperative_HOL.Array_Set_Impl

  Separation_Logic_Imperative_HOL.Open_List
  Separation_Logic_Imperative_HOL.Circ_List

  "../Intf/IICF_Map"
  "../Intf/IICF_Set"
  "../Intf/IICF_List"

  Collections.Locale_Code
begin
  text \<open>This theory binds collection data structures from the 
    basic collection framework established in 
    \<open>AFP/Separation_Logic_Imperative_HOL\<close> for usage with Sepref.
  \<close>
  
  (* TODO: Move, addition to Imp_Map_Spec *)
  locale imp_map_contains_key = imp_map +
    constrains is_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> assn"
    fixes contains_key :: "'k \<Rightarrow> 'm \<Rightarrow> bool Heap"
    assumes contains_key_rule[sep_heap_rules]: 
      "<is_map m p> contains_key k p <\<lambda>r. is_map m p * \<up>(r\<longleftrightarrow>k\<in>dom m)>\<^sub>t"
    
  (* TODO: Move to Imp_Map_Spec *)    
  locale gen_contains_key_by_lookup = imp_map_lookup
  begin   
    definition "contains_key k m \<equiv> do {r \<leftarrow> lookup k m; return (\<not>is_None r)}"

    sublocale imp_map_contains_key is_map contains_key
      apply unfold_locales
      unfolding contains_key_def
      apply (sep_auto split: option.splits)
      done

  end

  (* TODO: Move to Imp_List_Spec *)
  locale imp_list_tail = imp_list +
    constrains is_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
    fixes tail :: "'l \<Rightarrow> 'l Heap"
    assumes tail_rule[sep_heap_rules]: 
      "l\<noteq>[] \<Longrightarrow> <is_list l p> tail p <is_list (tl l)>\<^sub>t"

  (* TODO: Move to Open_List *)  
  definition os_head :: "'a::heap os_list \<Rightarrow> ('a) Heap" where
    "os_head p \<equiv> case p of 
      None \<Rightarrow> raise STR ''os_Head: Empty list''
    | Some p \<Rightarrow> do { m \<leftarrow>!p; return (val m) }"

  primrec os_tl :: "'a::heap os_list \<Rightarrow> ('a os_list) Heap" where
    "os_tl None = raise STR ''os_tl: Empty list''"
  | "os_tl (Some p) = do { m \<leftarrow>!p; return (next m) }"  

  interpretation os: imp_list_head os_list os_head
    by unfold_locales (sep_auto simp: os_head_def neq_Nil_conv)

  interpretation os: imp_list_tail os_list os_tl
    by unfold_locales (sep_auto simp: os_tl_def neq_Nil_conv)


  (* TODO: Move to Circ_List *)
  definition cs_is_empty :: "'a::heap cs_list \<Rightarrow> bool Heap" where
    "cs_is_empty p \<equiv> return (is_None p)"  
  interpretation cs: imp_list_is_empty cs_list cs_is_empty  
    by unfold_locales (sep_auto simp: cs_is_empty_def split: option.splits)

  definition cs_head :: "'a::heap cs_list \<Rightarrow> 'a Heap" where
    "cs_head p \<equiv> case p of 
      None \<Rightarrow> raise STR ''cs_head: Empty list''
    | Some p \<Rightarrow> do { n \<leftarrow> !p; return (val n)}"
  interpretation cs: imp_list_head cs_list cs_head
    by unfold_locales (sep_auto simp: neq_Nil_conv cs_head_def)
    
  definition cs_tail :: "'a::heap cs_list \<Rightarrow> 'a cs_list Heap" where
    "cs_tail p \<equiv> do { (_,r) \<leftarrow> cs_pop p; return r }"
  interpretation cs: imp_list_tail cs_list cs_tail
    by unfold_locales (sep_auto simp: cs_tail_def)


  (* TODO: Move to hashmap/hashset *)  
  lemma is_hashmap_finite[simp]: "h \<Turnstile> is_hashmap m mi \<Longrightarrow> finite (dom m)"
    unfolding is_hashmap_def is_hashmap'_def
    by auto

  lemma is_hashset_finite[simp]: "h \<Turnstile> is_hashset s si \<Longrightarrow> finite s"
    unfolding is_hashset_def
    by (auto dest: is_hashmap_finite)


  (* TODO: Move to array-map/ array-set *)  
  definition "ias_is_it s a si \<equiv> \<lambda>(a',i).
    \<exists>\<^sub>Al. a\<mapsto>\<^sub>al * \<up>(a'=a \<and> s=ias_of_list l \<and> (i=length l \<and> si={} \<or> i<length l \<and> i\<in>s \<and> si=s \<inter> {x. x\<ge>i} ))
  "

  context begin  
  private function first_memb where 
    "first_memb lmax a i = do {
      if i<lmax then do {
        x \<leftarrow> Array.nth a i;
        if x then return i else first_memb lmax a (Suc i)
      } else 
        return i
    }"
    by pat_completeness auto
  termination by (relation "measure (\<lambda>(l,_,i). l-i)") auto
  declare first_memb.simps[simp del]
     
  private lemma first_memb_rl_aux:
    assumes "lmax \<le> length l" "i\<le>lmax" 
    shows 
      "< a \<mapsto>\<^sub>a l > 
        first_memb lmax a i 
      <\<lambda>k. a\<mapsto>\<^sub>a l * \<up>(k\<le>lmax \<and> (\<forall>j. i\<le>j \<and> j<k \<longrightarrow> \<not>l!j) \<and> i\<le>k \<and> (k=lmax \<or> l!k)) >"
    using assms  
  proof (induction lmax a i rule: first_memb.induct)
    case (1 lmax a i)
    show ?case
      apply (subst first_memb.simps)
      using "1.prems"
      apply (sep_auto heap: "1.IH"; ((sep_auto;fail) | metis eq_iff not_less_eq_eq))
      done
  qed  

  private lemma first_memb_rl[sep_heap_rules]:
    assumes "lmax \<le> length l" "i\<le>lmax" 
    shows "< a \<mapsto>\<^sub>a l > 
      first_memb lmax a i 
    <\<lambda>k. a\<mapsto>\<^sub>a l * \<up>(ias_of_list l \<inter> {i..<k} = {} \<and> i\<le>k \<and> (k<lmax \<and> k\<in>ias_of_list l \<or> k=lmax) ) >"
    using assms
    by (sep_auto simp: ias_of_list_def heap: first_memb_rl_aux)

  definition "ias_it_init a = do {
    l \<leftarrow> Array.len a;
    i \<leftarrow> first_memb l a 0;
    return (a,i)
  }"

  definition "ias_it_has_next \<equiv> \<lambda>(a,i). do {
    l \<leftarrow> Array.len a;
    return (i<l)
  }"

  definition "ias_it_next \<equiv> \<lambda>(a,i). do {
    l \<leftarrow> Array.len a;
    i' \<leftarrow> first_memb l a (Suc i);
    return (i,(a,i'))
  }"

  (* TODO: Move *)
  lemma ias_of_list_bound: "ias_of_list l \<subseteq> {0..<length l}" by (auto simp: ias_of_list_def)

  end  

  interpretation ias: imp_set_iterate is_ias ias_is_it ias_it_init ias_it_has_next ias_it_next
    apply unfold_locales
    unfolding is_ias_def ias_is_it_def
    unfolding ias_it_init_def using ias_of_list_bound
    apply (sep_auto)
    unfolding ias_it_next_def using ias_of_list_bound
    apply (sep_auto; fastforce) (* Takes long *)
    unfolding ias_it_has_next_def 
    apply sep_auto
    apply sep_auto
    done
    
  lemma ias_of_list_finite[simp, intro!]: "finite (ias_of_list l)"
    using finite_subset[OF ias_of_list_bound] by auto

  lemma is_ias_finite[simp]: "h \<Turnstile> is_ias S x \<Longrightarrow> finite S"  
    unfolding is_ias_def by auto


  (* TODO: Move, replace original rules by this stronger var! *)
  lemma to_list_ga_rec_rule:
    assumes "imp_set_iterate is_set is_it it_init it_has_next it_next"
    assumes "imp_list_prepend is_list l_prepend"
    assumes FIN: "finite it"
    assumes DIS: "distinct l" "set l \<inter> it = {}"
    shows "
    < is_it s si it iti * is_list l li > 
      to_list_ga_rec it_has_next it_next l_prepend iti li
    < \<lambda>r. \<exists>\<^sub>Al'. is_set s si 
      * is_list l' r
      * \<up>(distinct l' \<and> set l' = set l \<union> it) >\<^sub>t"
  proof -
    interpret imp_set_iterate is_set is_it it_init it_has_next it_next
      + imp_list_prepend is_list l_prepend
      by fact+

    from FIN DIS show ?thesis
    proof (induction arbitrary: l li iti rule: finite_psubset_induct)
      case (psubset it)
      show ?case
        apply (subst to_list_ga_rec.simps)
        using psubset.prems apply (sep_auto heap: psubset.IH)
        apply (rule ent_frame_fwd[OF quit_iteration])
        apply frame_inference
        apply solve_entails
        done
    qed
  qed
  lemma to_list_ga_rule:
    assumes IT: "imp_set_iterate is_set is_it it_init it_has_next it_next"
    assumes EM: "imp_list_empty is_list l_empty"
    assumes PREP: "imp_list_prepend is_list l_prepend"
    assumes FIN: "finite s"
    shows "
    <is_set s si>
    to_list_ga it_init it_has_next it_next
      l_empty l_prepend si
    <\<lambda>r. \<exists>\<^sub>Al. is_set s si * is_list l r * true * \<up>(distinct l \<and> set l = s)>"
  proof -
    interpret imp_list_empty is_list l_empty +
      imp_set_iterate is_set is_it it_init it_has_next it_next
      by fact+

    note [sep_heap_rules] = to_list_ga_rec_rule[OF IT PREP]
    show ?thesis
      unfolding to_list_ga_def
      by (sep_auto simp: FIN)
  qed




  subsection \<open>Binding Locales\<close>
  
  method solve_sepl_binding = (
    unfold_locales;
    (unfold option_assn_pure_conv)?;
    sep_auto 
      intro!: hfrefI hn_refineI[THEN hn_refine_preI]
      simp: invalid_assn_def hn_ctxt_def pure_def
  )


  subsubsection \<open>Map\<close>

  locale bind_map = imp_map is_map for is_map :: "('ki \<rightharpoonup> 'vi) \<Rightarrow> 'm \<Rightarrow> assn"
  begin
    definition "assn K V \<equiv> hr_comp is_map (\<langle>the_pure K,the_pure V\<rangle>map_rel)"
    lemmas [fcomp_norm_unfold] = assn_def[symmetric]
    lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "assn K V" for K V]

  end

  locale bind_map_empty = imp_map_empty + bind_map
  begin
    lemma empty_hnr_aux: "(uncurry0 empty,uncurry0 (RETURN op_map_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a is_map"
      by solve_sepl_binding

    sepref_decl_impl (no_register) empty: empty_hnr_aux .
  end  


  locale bind_map_is_empty = imp_map_is_empty + bind_map
  begin
    lemma is_empty_hnr_aux: "(is_empty,RETURN o op_map_is_empty) \<in> is_map\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      by solve_sepl_binding
      
    sepref_decl_impl is_empty: is_empty_hnr_aux .
  end
  

  locale bind_map_update = imp_map_update + bind_map
  begin
    lemma update_hnr_aux: "(uncurry2 update,uncurry2 (RETURN ooo op_map_update)) \<in> id_assn\<^sup>k *\<^sub>a id_assn\<^sup>k *\<^sub>a is_map\<^sup>d \<rightarrow>\<^sub>a is_map"
      by solve_sepl_binding

    sepref_decl_impl update: update_hnr_aux .
  end


  locale bind_map_delete = imp_map_delete + bind_map
  begin
    lemma delete_hnr_aux: "(uncurry delete,uncurry (RETURN oo op_map_delete)) \<in> id_assn\<^sup>k *\<^sub>a is_map\<^sup>d \<rightarrow>\<^sub>a is_map"
      by solve_sepl_binding

    sepref_decl_impl delete: delete_hnr_aux .
  end


  locale bind_map_lookup = imp_map_lookup + bind_map
  begin
    lemma lookup_hnr_aux: "(uncurry lookup,uncurry (RETURN oo op_map_lookup)) \<in> id_assn\<^sup>k *\<^sub>a is_map\<^sup>k \<rightarrow>\<^sub>a id_assn"
      by solve_sepl_binding

    sepref_decl_impl lookup: lookup_hnr_aux .
  end

  locale bind_map_contains_key = imp_map_contains_key + bind_map
  begin
    lemma contains_key_hnr_aux: "(uncurry contains_key,uncurry (RETURN oo op_map_contains_key)) \<in> id_assn\<^sup>k *\<^sub>a is_map\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      by solve_sepl_binding

    sepref_decl_impl contains_key: contains_key_hnr_aux .
  end

  subsubsection \<open>Set\<close>

  locale bind_set = imp_set is_set for is_set :: "('ai set) \<Rightarrow> 'm \<Rightarrow> assn" +
    fixes A :: "'a \<Rightarrow> 'ai \<Rightarrow> assn"
  begin
    definition "assn \<equiv> hr_comp is_set (\<langle>the_pure A\<rangle>set_rel)"
    lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "assn"]
  end

  locale bind_set_setup = bind_set 
  begin
    (* TODO: Use sepref_decl_impl (see map) *)
    lemmas [fcomp_norm_unfold] = assn_def[symmetric]
    lemma APA: "\<lbrakk>PROP Q; CONSTRAINT is_pure A\<rbrakk> \<Longrightarrow> PROP Q" .
    lemma APAlu: "\<lbrakk>PROP Q; CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) A\<rbrakk> \<Longrightarrow> PROP Q" .
    lemma APAru: "\<lbrakk>PROP Q; CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) A\<rbrakk> \<Longrightarrow> PROP Q" .
    lemma APAbu: "\<lbrakk>PROP Q; CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) A; CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) A\<rbrakk> \<Longrightarrow> PROP Q" .


  end  

  locale bind_set_empty = imp_set_empty + bind_set
  begin
    lemma hnr_empty_aux: "(uncurry0 empty,uncurry0 (RETURN op_set_empty))\<in>unit_assn\<^sup>k \<rightarrow>\<^sub>a is_set"
      by solve_sepl_binding

    interpretation bind_set_setup by standard  

    lemmas hnr_op_empty = hnr_empty_aux[FCOMP op_set_empty.fref[where A="the_pure A"]] 
    lemmas hnr_mop_empty = hnr_op_empty[FCOMP mk_mop_rl0_np[OF mop_set_empty_alt]]
  end  

  locale bind_set_is_empty = imp_set_is_empty + bind_set
  begin
    lemma hnr_is_empty_aux: "(is_empty, RETURN o op_set_is_empty)\<in>is_set\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      by solve_sepl_binding

    interpretation bind_set_setup by standard  
    lemmas hnr_op_is_empty[sepref_fr_rules] = hnr_is_empty_aux[THEN APA,FCOMP op_set_is_empty.fref[where A="the_pure A"]] 
    lemmas hnr_mop_is_empty[sepref_fr_rules] = hnr_op_is_empty[FCOMP mk_mop_rl1_np[OF mop_set_is_empty_alt]]
  end  

  locale bind_set_member = imp_set_memb + bind_set
  begin
    lemma hnr_member_aux: "(uncurry memb, uncurry (RETURN oo op_set_member))\<in>id_assn\<^sup>k *\<^sub>a is_set\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      by solve_sepl_binding

    interpretation bind_set_setup by standard  
    lemmas hnr_op_member[sepref_fr_rules] = hnr_member_aux[THEN APAbu,FCOMP op_set_member.fref[where A="the_pure A"]] 
    lemmas hnr_mop_member[sepref_fr_rules] = hnr_op_member[FCOMP mk_mop_rl2_np[OF mop_set_member_alt]]
  end  

  locale bind_set_insert = imp_set_ins + bind_set
  begin
    lemma hnr_insert_aux: "(uncurry ins, uncurry (RETURN oo op_set_insert))\<in>id_assn\<^sup>k *\<^sub>a is_set\<^sup>d \<rightarrow>\<^sub>a is_set"
      by solve_sepl_binding

    interpretation bind_set_setup by standard  
    lemmas hnr_op_insert[sepref_fr_rules] = hnr_insert_aux[THEN APAru,FCOMP op_set_insert.fref[where A="the_pure A"]] 
    lemmas hnr_mop_insert[sepref_fr_rules] = hnr_op_insert[FCOMP mk_mop_rl2_np[OF mop_set_insert_alt]]
  end  

  locale bind_set_delete = imp_set_delete + bind_set
  begin
    lemma hnr_delete_aux: "(uncurry delete, uncurry (RETURN oo op_set_delete))\<in>id_assn\<^sup>k *\<^sub>a is_set\<^sup>d \<rightarrow>\<^sub>a is_set"
      by solve_sepl_binding

    interpretation bind_set_setup by standard  
    lemmas hnr_op_delete[sepref_fr_rules] = hnr_delete_aux[THEN APAbu,FCOMP op_set_delete.fref[where A="the_pure A"]] 
    lemmas hnr_mop_delete[sepref_fr_rules] = hnr_op_delete[FCOMP mk_mop_rl2_np[OF mop_set_delete_alt]]
  end  

  primrec sorted_wrt' where
    "sorted_wrt' R [] \<longleftrightarrow> True"
  | "sorted_wrt' R (x#xs) \<longleftrightarrow> list_all (R x) xs \<and> sorted_wrt' R xs"  

  lemma sorted_wrt'_eq: "sorted_wrt' = sorted_wrt" 
  proof (intro ext iffI)
    fix R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and xs :: "'a list"
    {
      assume "sorted_wrt R xs"
      thus "sorted_wrt' R xs"
        by (induction xs)(auto simp: list_all_iff sorted_sorted_wrt[symmetric])
    }
    {
      assume "sorted_wrt' R xs"
      thus "sorted_wrt R xs"
        by (induction xs) (auto simp: list_all_iff)
    }
  qed    

  lemma param_sorted_wrt[param]: "(sorted_wrt, sorted_wrt) \<in> (A \<rightarrow> A \<rightarrow> bool_rel) \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel"
    unfolding sorted_wrt'_eq[symmetric] sorted_wrt'_def 
    by parametricity

  lemma obtain_list_from_setrel:
    assumes SV: "single_valued A"
    assumes "(set l,s) \<in> \<langle>A\<rangle>set_rel"
    obtains m where "s=set m" "(l,m)\<in>\<langle>A\<rangle>list_rel"
    using assms(2)
  proof (induction l arbitrary: s thesis)
    case Nil
    show ?case
      apply (rule Nil(1)[where m="[]"])
      using Nil(2)
      by auto
  next
    case (Cons x l) 
    obtain s' y where "s=insert y s'" "(x,y)\<in>A" "(set l,s')\<in>\<langle>A\<rangle>set_rel"
    proof -
      from Cons.prems(2) obtain y where X0: "y\<in>s" "(x,y)\<in>A"
        unfolding set_rel_def by auto
      from Cons.prems(2) have 
        X1: "\<forall>a\<in>set l. \<exists>b\<in>s. (a,b)\<in>A" and
        X2: "\<forall>b\<in>s. \<exists>a\<in>insert x (set l). (a,b)\<in>A"
        unfolding set_rel_def by auto
      show ?thesis proof (cases "\<exists>a\<in>set l. (a,y)\<in>A")
        case True 
        show ?thesis
          apply (rule that[of y s])
          subgoal using X0 by auto
          subgoal by fact
          subgoal 
            apply (rule set_relI)    
            subgoal using X1 by blast  
            subgoal by (metis IS_RIGHT_UNIQUED SV True X0(2) X2 insert_iff)  
            done
          done
      next
        case False
        show ?thesis
          apply (rule that[of y "s-{y}"])
          subgoal using X0 by auto
          subgoal by fact
          subgoal 
            apply (rule set_relI)    
            subgoal using False X1 by fastforce  
            subgoal using IS_RIGHT_UNIQUED SV X0(2) X2 by fastforce
            done
          done
      qed
    qed    
    moreover from Cons.IH[OF _ \<open>(set l,s')\<in>\<langle>A\<rangle>set_rel\<close>] obtain m where "s'=set m" "(l,m)\<in>\<langle>A\<rangle>list_rel" .
    ultimately show thesis
      apply -
      apply (rule Cons.prems(1)[of "y#m"])
      by auto
  qed      
    
  lemma param_it_to_sorted_list[param]: "\<lbrakk>IS_LEFT_UNIQUE A; IS_RIGHT_UNIQUE A\<rbrakk> \<Longrightarrow> (it_to_sorted_list, it_to_sorted_list) \<in> (A \<rightarrow> A \<rightarrow> bool_rel) \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>\<langle>A\<rangle>list_rel\<rangle>nres_rel"
    unfolding it_to_sorted_list_def[abs_def]
    apply (auto simp: it_to_sorted_list_def pw_nres_rel_iff refine_pw_simps)
    apply (rule obtain_list_from_setrel; assumption?; clarsimp)
    apply (intro exI conjI; assumption?)
    using param_distinct[param_fo] apply blast
    apply simp
    using param_sorted_wrt[param_fo] apply blast
    done



  locale bind_set_iterate = imp_set_iterate + bind_set +
    assumes is_set_finite: "h \<Turnstile> is_set S x \<Longrightarrow> finite S"
  begin
    context begin
      private lemma is_imp_set_iterate: "imp_set_iterate is_set is_it it_init it_has_next it_next" by unfold_locales
      
      private lemma is_imp_list_empty: "imp_list_empty (list_assn id_assn) (return [])"
        apply unfold_locales
        apply solve_constraint
        apply sep_auto
        done
        
      private lemma is_imp_list_prepend: "imp_list_prepend (list_assn id_assn) (return oo List.Cons)"  
        apply unfold_locales
        apply solve_constraint
        apply (sep_auto simp: pure_def)
        done

      definition "to_list \<equiv> to_list_ga it_init it_has_next it_next (return []) (return oo List.Cons)"
      private lemmas tl_rl = to_list_ga_rule[OF is_imp_set_iterate is_imp_list_empty is_imp_list_prepend, folded to_list_def]

      private lemma to_list_sorted1: "(to_list,PR_CONST (it_to_sorted_list (\<lambda>_ _. True))) \<in> is_set\<^sup>k \<rightarrow>\<^sub>a list_assn id_assn"
        unfolding PR_CONST_def
        apply (intro hfrefI)
        apply (rule hn_refine_preI)
        apply (rule hn_refineI)
        unfolding it_to_sorted_list_def
        apply (sep_auto intro: hfrefI hn_refineI intro: is_set_finite heap: tl_rl)
        done

      private lemma to_list_sorted2: "\<lbrakk>
        CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) A; 
        CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) A\<rbrakk> \<Longrightarrow> 
        (PR_CONST (it_to_sorted_list (\<lambda>_ _. True)), PR_CONST (it_to_sorted_list (\<lambda>_ _. True))) \<in> \<langle>the_pure A\<rangle>set_rel \<rightarrow> \<langle>\<langle>the_pure A\<rangle>list_rel\<rangle>nres_rel"  
        unfolding PR_CONST_def CONSTRAINT_def IS_PURE_def 
        by clarify parametricity
          
      lemmas to_list_hnr = to_list_sorted1[FCOMP to_list_sorted2, folded assn_def]  
      lemmas to_list_is_to_sorted_list = IS_TO_SORTED_LISTI[OF to_list_hnr]
      lemma to_list_gen[sepref_gen_algo_rules]: "\<lbrakk>CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) A; CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) A\<rbrakk> 
        \<Longrightarrow> GEN_ALGO to_list (IS_TO_SORTED_LIST (\<lambda>_ _. True) (bind_set.assn is_set A) A)"
        by (simp add: GEN_ALGO_def to_list_is_to_sorted_list)

    end  
  end

  subsubsection \<open>List\<close>
  locale bind_list = imp_list is_list for is_list :: "('ai list) \<Rightarrow> 'm \<Rightarrow> assn" +
    fixes A :: "'a \<Rightarrow> 'ai \<Rightarrow> assn"
  begin
    (*abbreviation "Ap \<equiv> the_pure A"*)
    definition "assn \<equiv> hr_comp is_list (\<langle>the_pure A\<rangle>list_rel)"
    lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "assn"]

  end  


  locale bind_list_empty = imp_list_empty + bind_list
  begin
    lemma hnr_aux: "(uncurry0 empty,uncurry0 (RETURN op_list_empty))\<in>(pure unit_rel)\<^sup>k \<rightarrow>\<^sub>a is_list"
      apply rule apply rule apply (sep_auto simp: pure_def) done

    lemmas hnr 
      = hnr_aux[FCOMP op_list_empty.fref[of "the_pure A"], folded assn_def]

    lemmas hnr_mop = hnr[FCOMP mk_mop_rl0_np[OF mop_list_empty_alt]]
  end

  locale bind_list_is_empty = imp_list_is_empty + bind_list
  begin
    lemma hnr_aux: "(is_empty,RETURN o op_list_is_empty)\<in>(is_list)\<^sup>k \<rightarrow>\<^sub>a pure bool_rel"
      apply rule apply rule apply (sep_auto simp: pure_def) done

    lemmas hnr[sepref_fr_rules] 
      = hnr_aux[FCOMP op_list_is_empty.fref, of "the_pure A", folded assn_def]
    lemmas hnr_mop[sepref_fr_rules] = hnr[FCOMP mk_mop_rl1_np[OF mop_list_is_empty_alt]]
  end

  locale bind_list_append = imp_list_append + bind_list
  begin
    lemma hnr_aux: "(uncurry (swap_args2 append),uncurry (RETURN oo op_list_append))
      \<in>(is_list)\<^sup>d *\<^sub>a (pure Id)\<^sup>k \<rightarrow>\<^sub>a is_list" by solve_sepl_binding

    lemmas hnr[sepref_fr_rules] 
      = hnr_aux[FCOMP op_list_append.fref,of A, folded assn_def]
    lemmas hnr_mop[sepref_fr_rules] = hnr[FCOMP mk_mop_rl2_np[OF mop_list_append_alt]]
  end

  locale bind_list_prepend = imp_list_prepend + bind_list
  begin
    lemma hnr_aux: "(uncurry prepend,uncurry (RETURN oo op_list_prepend))
      \<in>(pure Id)\<^sup>k *\<^sub>a (is_list)\<^sup>d \<rightarrow>\<^sub>a is_list" by solve_sepl_binding

    lemmas hnr[sepref_fr_rules] 
      = hnr_aux[FCOMP op_list_prepend.fref,of A, folded assn_def]
    lemmas hnr_mop[sepref_fr_rules] = hnr[FCOMP mk_mop_rl2_np[OF mop_list_prepend_alt]]
  end

  locale bind_list_hd = imp_list_head + bind_list
  begin
    lemma hnr_aux: "(head,RETURN o op_list_hd)
      \<in>[\<lambda>l. l\<noteq>[]]\<^sub>a (is_list)\<^sup>d \<rightarrow> pure Id"  by solve_sepl_binding

    lemmas hnr[sepref_fr_rules] = hnr_aux[FCOMP op_list_hd.fref,of A, folded assn_def]
    lemmas hnr_mop[sepref_fr_rules] = hnr[FCOMP mk_mop_rl1[OF mop_list_hd_alt]]
  end

  locale bind_list_tl = imp_list_tail + bind_list
  begin
    lemma hnr_aux: "(tail,RETURN o op_list_tl)
      \<in>[\<lambda>l. l\<noteq>[]]\<^sub>a (is_list)\<^sup>d \<rightarrow> is_list"
       by solve_sepl_binding

    lemmas hnr[sepref_fr_rules] = hnr_aux[FCOMP op_list_tl.fref,of "the_pure A", folded assn_def]
    lemmas hnr_mop[sepref_fr_rules] = hnr[FCOMP mk_mop_rl1[OF mop_list_tl_alt]]
  end

  locale bind_list_rotate1 = imp_list_rotate + bind_list
  begin
    lemma hnr_aux: "(rotate,RETURN o op_list_rotate1)
      \<in>(is_list)\<^sup>d \<rightarrow>\<^sub>a is_list"
       by solve_sepl_binding

    lemmas hnr[sepref_fr_rules] = hnr_aux[FCOMP op_list_rotate1.fref,of "the_pure A", folded assn_def]
    lemmas hnr_mop[sepref_fr_rules] = hnr[FCOMP mk_mop_rl1_np[OF mop_list_rotate1_alt]]
  end

  locale bind_list_rev = imp_list_reverse + bind_list
  begin
    lemma hnr_aux: "(reverse,RETURN o op_list_rev)
      \<in>(is_list)\<^sup>d \<rightarrow>\<^sub>a is_list"
       by solve_sepl_binding

    lemmas hnr[sepref_fr_rules] = hnr_aux[FCOMP op_list_rev.fref,of "the_pure A", folded assn_def]
    lemmas hnr_mop[sepref_fr_rules] = hnr[FCOMP mk_mop_rl1_np[OF mop_list_rev_alt]]
  end

  subsection \<open>Array Map (iam)\<close>
  definition "op_iam_empty \<equiv> IICF_Map.op_map_empty"
  interpretation iam: bind_map_empty is_iam iam_new
    by unfold_locales

  interpretation iam: map_custom_empty op_iam_empty
    by unfold_locales (simp add: op_iam_empty_def)
  lemmas [sepref_fr_rules] = iam.empty_hnr[folded op_iam_empty_def]


  definition [simp]: "op_iam_empty_sz (N::nat) \<equiv> IICF_Map.op_map_empty"
  lemma [def_pat_rules]: "op_iam_empty_sz$N \<equiv> UNPROTECT (op_iam_empty_sz N)"
    by simp

  interpretation iam_sz: map_custom_empty "PR_CONST (op_iam_empty_sz N)"
    apply unfold_locales 
    apply (simp)
    done
  lemma [sepref_fr_rules]: "(uncurry0 iam_new, uncurry0 (RETURN (PR_CONST (op_iam_empty_sz N)))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a iam.assn K V"  
    using iam.empty_hnr[of K V] by simp


  interpretation iam: bind_map_update is_iam Array_Map_Impl.iam_update
    by unfold_locales

  interpretation iam: bind_map_delete is_iam Array_Map_Impl.iam_delete
    by unfold_locales

  interpretation iam: bind_map_lookup is_iam Array_Map_Impl.iam_lookup
    by unfold_locales

  setup Locale_Code.open_block
  interpretation iam: gen_contains_key_by_lookup is_iam Array_Map_Impl.iam_lookup
    by unfold_locales
  setup Locale_Code.close_block

  interpretation iam: bind_map_contains_key is_iam iam.contains_key
    by unfold_locales

  subsection \<open>Array Set (ias)\<close>

  definition [simp]: "op_ias_empty \<equiv> op_set_empty"
  interpretation ias: bind_set_empty is_ias ias_new for A
    by unfold_locales

  interpretation ias: set_custom_empty ias_new op_ias_empty
    by unfold_locales simp
  lemmas [sepref_fr_rules] = ias.hnr_op_empty[folded op_ias_empty_def]


  definition [simp]: "op_ias_empty_sz (N::nat) \<equiv> op_set_empty"
  lemma [def_pat_rules]: "op_ias_empty_sz$N \<equiv> UNPROTECT (op_ias_empty_sz N)"
    by simp

  interpretation ias_sz: bind_set_empty is_ias "ias_new_sz N" for N A
    by unfold_locales

  interpretation ias_sz: set_custom_empty "ias_new_sz N" "PR_CONST (op_ias_empty_sz N)" for A
    by unfold_locales simp
  lemma [sepref_fr_rules]: 
    "(uncurry0 (ias_new_sz N), uncurry0 (RETURN (PR_CONST (op_ias_empty_sz N)))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a ias.assn A"
    using ias_sz.hnr_op_empty[of N A] by simp

  interpretation ias: bind_set_member is_ias Array_Set_Impl.ias_memb for A
    by unfold_locales

  interpretation ias: bind_set_insert is_ias Array_Set_Impl.ias_ins for A
    by unfold_locales

  interpretation ias: bind_set_delete is_ias Array_Set_Impl.ias_delete for A
    by unfold_locales

  setup Locale_Code.open_block  
  interpretation ias: bind_set_iterate is_ias ias_is_it ias_it_init ias_it_has_next ias_it_next for A
    by unfold_locales auto
  setup Locale_Code.close_block  

  subsection \<open>Hash Map (hm)\<close>
  interpretation hm: bind_map_empty is_hashmap hm_new
    by unfold_locales

  definition "op_hm_empty \<equiv> IICF_Map.op_map_empty"  
  interpretation hm: map_custom_empty op_hm_empty
    by unfold_locales (simp add: op_hm_empty_def)
  lemmas [sepref_fr_rules] = hm.empty_hnr[folded op_hm_empty_def]

  interpretation hm: bind_map_is_empty is_hashmap Hash_Map.hm_isEmpty
    by unfold_locales

  interpretation hm: bind_map_update is_hashmap Hash_Map.hm_update
    by unfold_locales

  interpretation hm: bind_map_delete is_hashmap Hash_Map.hm_delete
    by unfold_locales

  interpretation hm: bind_map_lookup is_hashmap Hash_Map.hm_lookup
    by unfold_locales

  setup Locale_Code.open_block
  interpretation hm: gen_contains_key_by_lookup is_hashmap Hash_Map.hm_lookup
    by unfold_locales
  setup Locale_Code.close_block

  interpretation hm: bind_map_contains_key is_hashmap hm.contains_key
    by unfold_locales


  subsection \<open>Hash Set (hs)\<close>
  interpretation hs: bind_set_empty is_hashset hs_new for A
    by unfold_locales

  definition "op_hs_empty \<equiv> IICF_Set.op_set_empty"  
  interpretation hs: set_custom_empty hs_new op_hs_empty for A
    by unfold_locales (simp add: op_hs_empty_def)
  lemmas [sepref_fr_rules] = hs.hnr_op_empty[folded op_hs_empty_def]

  interpretation hs: bind_set_is_empty is_hashset Hash_Set_Impl.hs_isEmpty for A
    by unfold_locales

  interpretation hs: bind_set_member is_hashset Hash_Set_Impl.hs_memb for A
    by unfold_locales

  interpretation hs: bind_set_insert is_hashset Hash_Set_Impl.hs_ins for A
    by unfold_locales

  interpretation hs: bind_set_delete is_hashset Hash_Set_Impl.hs_delete for A
    by unfold_locales

  setup Locale_Code.open_block  
  interpretation hs: bind_set_iterate is_hashset hs_is_it hs_it_init hs_it_has_next hs_it_next for A
    by unfold_locales simp
  setup Locale_Code.close_block  


  subsection \<open>Open Singly Linked List (osll)\<close>  
  interpretation osll: bind_list os_list for A by unfold_locales
  interpretation osll_empty: bind_list_empty os_list os_empty for A
    by unfold_locales

  definition "osll_empty \<equiv> op_list_empty"
  interpretation osll: list_custom_empty "osll.assn A" os_empty osll_empty
    apply unfold_locales
    apply (rule osll_empty.hnr)
    by (simp add: osll_empty_def)

  interpretation osll_is_empty: bind_list_is_empty os_list os_is_empty for A
    by unfold_locales

  interpretation osll_prepend: bind_list_prepend os_list os_prepend for A
    by unfold_locales
  
  interpretation osll_hd: bind_list_hd os_list os_head for A
    by unfold_locales

  interpretation osll_tl: bind_list_tl os_list os_tl for A
    by unfold_locales
    
  interpretation osll_rev: bind_list_rev os_list os_reverse for A
    by unfold_locales


  subsection \<open>Circular Singly Linked List (csll)\<close>  


  (* TODO: In-place reversal of circular list! *)  

  interpretation csll: bind_list cs_list for A by unfold_locales

  interpretation csll_empty: bind_list_empty cs_list cs_empty for A 
    by unfold_locales

  definition "csll_empty \<equiv> op_list_empty"
  interpretation csll: list_custom_empty "csll.assn A" cs_empty csll_empty
    apply unfold_locales
    apply (rule csll_empty.hnr)
    by (simp add: csll_empty_def)

  interpretation csll_is_empty: bind_list_is_empty cs_list cs_is_empty for A 
    by unfold_locales

  interpretation csll_prepend: bind_list_prepend cs_list cs_prepend for A 
    by unfold_locales
    
  interpretation csll_append: bind_list_append cs_list cs_append for A 
    by unfold_locales

  interpretation csll_hd: bind_list_hd cs_list cs_head for A 
    by unfold_locales
    
  interpretation csll_tl: bind_list_tl cs_list cs_tail for A 
    by unfold_locales

  interpretation csll_rotate1: bind_list_rotate1 cs_list cs_rotate for A 
    by unfold_locales

  schematic_goal "hn_refine (emp) (?c::?'c Heap) ?\<Gamma>' ?R (do {
    x \<leftarrow> mop_list_empty;
    RETURN (1 \<in> dom [1::nat \<mapsto> True, 2\<mapsto>False], {1,2::nat}, 1#(2::nat)#x)
  })"  
    apply (subst iam_sz.fold_custom_empty[where N=10])
    apply (subst hs.fold_custom_empty)
    apply (subst osll.fold_custom_empty)
    by sepref

end
