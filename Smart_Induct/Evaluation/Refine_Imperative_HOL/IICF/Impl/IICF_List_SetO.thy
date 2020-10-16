section \<open>Sets by Lists that Own their Elements\<close>
theory IICF_List_SetO
imports "../Intf/IICF_Set"
begin
  text \<open>Minimal implementation, only supporting a few operations\<close>

  definition "lso_assn A \<equiv> hr_comp (list_assn A) (br set (\<lambda>_. True))"
  lemmas [fcomp_norm_unfold] = lso_assn_def[symmetric]
  lemma lso_is_pure[safe_constraint_rules]: "is_pure A \<Longrightarrow> is_pure (lso_assn A)"
    unfolding lso_assn_def by safe_constraint

  lemma lso_empty_aref: "(uncurry0 (RETURN []), uncurry0 (RETURN op_set_empty)) 
    \<in> unit_rel  \<rightarrow>\<^sub>f \<langle>br set (\<lambda>_. True)\<rangle>nres_rel"
    by (auto simp: in_br_conv intro!: frefI nres_relI)

  lemma lso_ins_aref: "(uncurry (RETURN oo ((#) )), uncurry (RETURN oo op_set_insert)) 
    \<in> Id \<times>\<^sub>r br set (\<lambda>_. True) \<rightarrow>\<^sub>f \<langle>br set (\<lambda>_. True)\<rangle>nres_rel"
    by (auto simp: in_br_conv intro!: frefI nres_relI)

  sepref_decl_impl (no_register) lso_empty: hn_Nil[to_hfref] uses lso_empty_aref .  
  definition [simp]: "op_lso_empty \<equiv> op_set_empty"
  lemma lso_fold_custom_empty:
    "{} = op_lso_empty"
    "op_set_empty = op_lso_empty"
    by auto
  lemmas [sepref_fr_rules] = lso_empty_hnr[folded op_lso_empty_def]

  sepref_decl_impl lso_insert: hn_Cons[to_hfref] uses lso_ins_aref .
    
  thm hn_Cons[FCOMP lso_ins_aref]  

  (* TODO: Allow (controlled) backtracking over comb-rules, then we can have a general list-bex operation! *)
  definition [simp]: "op_lso_bex P S \<equiv> \<exists>x\<in>S. P x"
  lemma fold_lso_bex: "Bex \<equiv> \<lambda>s P. op_lso_bex P s" by auto

  definition [simp]: "mop_lso_bex P S \<equiv> ASSERT (\<forall>x\<in>S. \<exists>y. P x = RETURN y) \<then> RETURN (\<exists>x\<in>S. P x = RETURN True)"

  lemma op_mop_lso_bex:  "RETURN (op_lso_bex P S) = mop_lso_bex (RETURN o P) S" by simp

  sepref_register op_lso_bex
  lemma lso_bex_arity[sepref_monadify_arity]: 
    "op_lso_bex \<equiv> \<lambda>\<^sub>2P s. SP op_lso_bex$(\<lambda>\<^sub>2x. P$x)$s" by (auto intro!: eq_reflection ext)
  lemma op_lso_bex_monadify[sepref_monadify_comb]:  
    "EVAL$(op_lso_bex$(\<lambda>\<^sub>2x. P x)$s) \<equiv> (\<bind>) $(EVAL$s)$(\<lambda>\<^sub>2s. mop_lso_bex$(\<lambda>\<^sub>2x. EVAL $ P x)$s)" by simp

  definition "lso_abex P l \<equiv> nfoldli l (Not) (\<lambda>x _. P x) False"
  lemma lso_abex_to_set: "lso_abex P l \<le> mop_lso_bex P (set l)"
  proof -
    { fix b
      have "nfoldli l (Not) (\<lambda>x _. P x) b \<le> ASSERT (\<forall>x\<in>set l. \<exists>y. P x = RETURN y) \<then> RETURN ((\<exists>x\<in>set l. P x = RETURN True) \<or> b)"
        apply (induction l arbitrary: b) 
        applyS simp
        applyS (clarsimp simp add: pw_le_iff refine_pw_simps; blast) 
        done
    } from this[of False] show ?thesis by (simp add: lso_abex_def)
  qed    



  locale lso_bex_impl_loc = 
    fixes Pi and P :: "'a \<Rightarrow> bool nres"
    fixes li :: "'c list" and l :: "'a list"
    fixes A :: "'a \<Rightarrow> 'c \<Rightarrow> assn"
    fixes F :: assn
    
    assumes Prl: "\<And>x xi. \<lbrakk>x\<in>set l\<rbrakk> \<Longrightarrow> hn_refine (F * hn_ctxt A x xi) (Pi xi) (F * hn_ctxt A x xi) bool_assn (P x)"
  begin  
    sepref_register l
    sepref_register P

    lemma [sepref_comb_rules]:
      assumes "\<Gamma> \<Longrightarrow>\<^sub>t F' * F * hn_ctxt A x xi"
      assumes "x\<in>set l"
      shows "hn_refine \<Gamma> (Pi xi) (F' * F * hn_ctxt A x xi) bool_assn (P$x)"
      using hn_refine_frame[OF Prl[OF assms(2)], of \<Gamma> F'] assms(1)
      by (simp add: assn_assoc)


    schematic_goal lso_bex_impl: 
      "hn_refine (hn_ctxt (list_assn A) l li * F) (?c) (F * hn_ctxt (list_assn A) l li) bool_assn (lso_abex P l)"
      unfolding lso_abex_def[abs_def]
      by sepref
  end    
  concrete_definition lso_bex_impl uses lso_bex_impl_loc.lso_bex_impl  
  
  lemma hn_lso_bex[sepref_prep_comb_rule,sepref_comb_rules]: 
    assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (lso_assn A) s li * F"
    assumes Prl: "\<And>x xi. \<lbrakk>x\<in>s\<rbrakk> \<Longrightarrow> hn_refine (F * hn_ctxt A x xi) (Pi xi) (F * hn_ctxt A x xi) bool_assn (P x)"
    notes [simp del] = mop_lso_bex_def
    shows "hn_refine \<Gamma> (lso_bex_impl Pi li) (F * hn_ctxt (lso_assn A) s li) bool_assn (mop_lso_bex$(\<lambda>\<^sub>2x. P x)$s)"
    apply (rule hn_refine_cons_pre[OF FR])
    apply (clarsimp simp: hn_ctxt_def lso_assn_def hr_comp_def in_br_conv hnr_pre_ex_conv)
    apply (rule hn_refine_preI)
    apply (drule mod_starD; clarsimp)
    apply (rule hn_refine_ref[OF lso_abex_to_set])
  proof -
    fix l assume [simp]: "s=set l"

    from Prl have Prl': "\<And>x xi. \<lbrakk>x\<in>set l\<rbrakk> \<Longrightarrow> hn_refine (F * hn_ctxt A x xi) (Pi xi) (F * hn_ctxt A x xi) bool_assn (P x)"
      by simp

    show "hn_refine (list_assn A l li * F) (lso_bex_impl Pi li) (\<exists>\<^sub>Aba. F * list_assn A ba li * \<up> (set l = set ba)) bool_assn
           (lso_abex P l)"
      apply (rule hn_refine_cons[OF _ lso_bex_impl.refine])
      applyS (simp add: hn_ctxt_def; rule entt_refl)
      apply1 unfold_locales apply1 (rule Prl') applyS simp
      applyS (sep_auto intro!: enttI simp: hn_ctxt_def)
      applyS (rule entt_refl)
      done
  qed    

end

