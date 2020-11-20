theory Worklist_Subsumption_Impl
imports "../IICF/IICF" Worklist_Subsumption
begin

  locale Worklist2_Defs = Worklist1_Defs +
    fixes A :: "'a \<Rightarrow> 'ai \<Rightarrow> assn"
    fixes succsi :: "'ai \<Rightarrow> 'ai list Heap"
    fixes a\<^sub>0i :: "'ai Heap"
    fixes Fi :: "'ai \<Rightarrow> bool Heap"
    fixes Lei :: "'ai \<Rightarrow> 'ai \<Rightarrow> bool Heap"

  locale Worklist2 = Worklist2_Defs + Worklist1 +
    (* TODO: This is the easy variant: Operations cannot depend on additional heap. *)
    assumes [sepref_fr_rules]: "(uncurry0 a\<^sub>0i, uncurry0 (RETURN (PR_CONST a\<^sub>0))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a A"
    assumes [sepref_fr_rules]: "(Fi,RETURN o PR_CONST F) \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    assumes [sepref_fr_rules]: "(uncurry Lei,uncurry (RETURN oo PR_CONST (\<preceq>))) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    assumes [sepref_fr_rules]: "(succsi,RETURN o PR_CONST succs) \<in> A\<^sup>k \<rightarrow>\<^sub>a list_assn A"
  begin
    sepref_register "PR_CONST a\<^sub>0" "PR_CONST F" "PR_CONST (\<preceq>)" "PR_CONST succs"

    lemma [def_pat_rules]:
      "a\<^sub>0 \<equiv> UNPROTECT a\<^sub>0" "F \<equiv> UNPROTECT F" "(\<preceq>) \<equiv> UNPROTECT (\<preceq>)" "succs \<equiv> UNPROTECT succs"
      by simp_all
    
    lemma take_from_mset_as_mop_mset_pick: "take_from_mset = mop_mset_pick"
      apply (intro ext)
      unfolding take_from_mset_def[abs_def] 
      by (auto simp: pw_eq_iff refine_pw_simps)

    lemma [safe_constraint_rules]: "CN_FALSE is_pure A \<Longrightarrow> is_pure A" by simp

    sepref_thm worklist_algo2 is "uncurry0 worklist_algo1" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      unfolding worklist_algo1_def add_succ1_def
      supply [[goals_limit = 1]]
      apply (rewrite in "Let \<hole> _" lso_fold_custom_empty)
      apply (rewrite in "{#a\<^sub>0#}" lmso_fold_custom_empty)
      unfolding take_from_mset_as_mop_mset_pick fold_lso_bex
      by sepref

  end

  concrete_definition worklist_algo2 
    for Lei a\<^sub>0i Fi succsi
    uses Worklist2.worklist_algo2.refine_raw is "(uncurry0 ?f,_)\<in>_"
  thm worklist_algo2_def

  context Worklist2 begin
    lemma Worklist2_this: "Worklist2 E a\<^sub>0 F (\<preceq>) succs A succsi a\<^sub>0i Fi Lei" 
      by unfold_locales

    lemma hnr_F_reachable: "(uncurry0 (worklist_algo2 Lei a\<^sub>0i Fi succsi), uncurry0 (RETURN F_reachable)) 
      \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      using worklist_algo2.refine[OF Worklist2_this, 
        FCOMP worklist_algo1_ref[THEN nres_relI],
        FCOMP worklist_algo_correct[THEN Id_SPEC_refine, THEN nres_relI]]
      by (simp add: RETURN_def)

  end

  context Worklist1 begin
    sepref_decl_op F_reachable :: "bool_rel" .
    lemma [def_pat_rules]: "F_reachable \<equiv> op_F_reachable" by simp


    lemma hnr_op_F_reachable:
      assumes "GEN_ALGO a\<^sub>0i (\<lambda>a\<^sub>0i. (uncurry0 a\<^sub>0i, uncurry0 (RETURN a\<^sub>0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a A)"
      assumes "GEN_ALGO Fi (\<lambda>Fi. (Fi,RETURN o F) \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
      assumes "GEN_ALGO Lei (\<lambda>Lei. (uncurry Lei,uncurry (RETURN oo (\<preceq>))) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
      assumes "GEN_ALGO succsi (\<lambda>succsi. (succsi,RETURN o succs) \<in> A\<^sup>k \<rightarrow>\<^sub>a list_assn A)"
      shows "(uncurry0 (worklist_algo2 Lei a\<^sub>0i Fi succsi), uncurry0 (RETURN (PR_CONST op_F_reachable))) 
        \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    proof -
      from assms interpret Worklist2 E a\<^sub>0 F "(\<preceq>)" succs A succsi a\<^sub>0i Fi Lei 
        by (unfold_locales; simp add: GEN_ALGO_def)
    
      from hnr_F_reachable show ?thesis by simp    
    qed  

    sepref_decl_impl hnr_op_F_reachable .
  end

end
