theory IICF_List_MsetO
imports "../Intf/IICF_Multiset"
begin

  definition "lmso_assn A \<equiv> hr_comp (list_assn A) (br mset (\<lambda>_. True))"
  lemmas [fcomp_norm_unfold] = lmso_assn_def[symmetric]

  lemma lmso_is_pure[safe_constraint_rules]: "is_pure A \<Longrightarrow> is_pure (lmso_assn A)"
    unfolding lmso_assn_def by safe_constraint

  lemma lmso_empty_aref: "(uncurry0 (RETURN []), uncurry0 (RETURN op_mset_empty)) \<in> unit_rel \<rightarrow>\<^sub>f \<langle>br mset (\<lambda>_. True)\<rangle>nres_rel"
    by (auto intro!: frefI nres_relI simp: in_br_conv)
    
  (*  
  definition [simp]: "list_single x \<equiv> [x]"
  lemma lmso_single_aref: "(RETURN o list_single,RETURN o op_mset_single) \<in> Id \<rightarrow>\<^sub>f \<langle>br mset (\<lambda>_. True)\<rangle>nres_rel"  
    by (auto intro!: frefI nres_relI simp: in_br_conv)
  *)  

  lemma lmso_is_empty_aref: "(RETURN o List.null, RETURN o op_mset_is_empty) \<in> br mset (\<lambda>_. True) \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel"  
    by (auto intro!: frefI nres_relI simp: in_br_conv List.null_def split: list.split)


  lemma lmso_insert_aref: "(uncurry (RETURN oo (#) ), uncurry (RETURN oo op_mset_insert)) \<in> (Id \<times>\<^sub>r br mset (\<lambda>_. True)) \<rightarrow>\<^sub>f \<langle>br mset (\<lambda>_. True)\<rangle>nres_rel"  
    by (auto intro!: frefI nres_relI simp: in_br_conv)
    
  (*  
  lemma list_single_hnr: "(return o list_single, RETURN o list_single) \<in> A\<^sup>d \<rightarrow>\<^sub>a list_assn A"  
    apply sepref_to_hoare
    apply sep_auto
    done  
  *)
    
  definition [simp]: "hd_tl l \<equiv> (hd l, tl l)"

  lemma hd_tl_opt[sepref_opt_simps]: "hd_tl l = (case l of (x#xs) \<Rightarrow> (x,xs) | _ \<Rightarrow> CODE_ABORT (\<lambda>_. (hd l, tl l)))"  
    by (auto split: list.split)

  lemma lmso_pick_aref: "(RETURN o hd_tl,op_mset_pick) \<in> [\<lambda>m. m\<noteq>{#}]\<^sub>f br mset (\<lambda>_. True) \<rightarrow> \<langle>Id \<times>\<^sub>r br mset (\<lambda>_. True)\<rangle>nres_rel"  
    by (auto intro!: frefI nres_relI simp: in_br_conv pw_le_iff refine_pw_simps neq_Nil_conv algebra_simps)
    
  lemma hd_tl_hnr: "(return o hd_tl,RETURN o hd_tl) \<in> [\<lambda>l. \<not>is_Nil l]\<^sub>a (list_assn A)\<^sup>d \<rightarrow> prod_assn A (list_assn A)"
    apply sepref_to_hoare
    subgoal for l li by (cases l; cases li; sep_auto)
    done  

  sepref_decl_impl (no_register) lmso_empty: hn_Nil[to_hfref] uses lmso_empty_aref .
  definition [simp]: "op_lmso_empty \<equiv> op_mset_empty"
  sepref_register op_lmso_empty
  lemma lmso_fold_custom_empty: 
    "{#} = op_lmso_empty"
    "op_mset_empty = op_lmso_empty"
    "mop_mset_empty = RETURN op_lmso_empty"
    by auto
  lemmas [sepref_fr_rules] = lmso_empty_hnr[folded op_lmso_empty_def]  

  (*
  sepref_decl_impl (no_register) lmso_single: list_single_hnr uses lmso_single_aref .
  definition [simp]: "op_lmso_single \<equiv> op_mset_single"
  sepref_register op_lmso_single
  lemma lmso_fold_custom_single: 
    "{#x#} = op_lmso_single x"
    "op_mset_single x = op_lmso_single x"
    "mop_mset_single x = RETURN (op_lmso_single x)"
    by auto
  lemmas [sepref_fr_rules] = lmso_single_hnr[folded op_lmso_single_def]  
 *) 

  lemma list_null_hnr: "(return o List.null,RETURN o List.null) \<in> (list_assn A)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    apply sepref_to_hoare
    subgoal for l li by (cases l; cases li; sep_auto simp: List.null_def)
    done

  sepref_decl_impl lmso_is_empty: list_null_hnr uses lmso_is_empty_aref .

  sepref_decl_impl lmso_insert: hn_Cons[to_hfref] uses lmso_insert_aref .

  (* As parametricity heuristics of sepref_decl_impl fails here,
    we use FCOMP and some dummy-lemma to still get the automation benefits of 
    sepref_decl_impl. *)
  context notes [simp] = in_br_conv and [split] = list.splits begin
    text \<open>Dummy lemma, to exloit \<open>sepref_decl_impl\<close> automation without parametricity stuff.\<close>
    private lemma op_mset_pick_dummy_param: "(op_mset_pick, op_mset_pick) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel" 
      by (auto intro!: frefI nres_relI)

    sepref_decl_impl lmso_pick: hd_tl_hnr[FCOMP lmso_pick_aref] uses op_mset_pick_dummy_param by simp
  end  

end
