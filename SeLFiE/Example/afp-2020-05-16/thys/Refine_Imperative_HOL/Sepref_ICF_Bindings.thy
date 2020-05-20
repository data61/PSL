theory Sepref_ICF_Bindings
imports Sepref_Tool 
  Collections.Refine_Dflt_ICF
  "IICF/IICF"
begin
  subsection \<open>Miscellaneous\<close>
  lemma (in -) rev_append_hnr[param,sepref_import_param]:
    "(rev_append, rev_append) \<in> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel"
    unfolding rev_append_def by parametricity
  
  subsection \<open>Sets by List\<close>

  (* TODO: Move to Collections *)
  lemma lsr_finite[simp, intro]: "(l,s)\<in>\<langle>R\<rangle>list_set_rel \<Longrightarrow> finite s"
    by (auto simp: list_set_rel_def br_def)

  lemma it_to_sorted_list_triv:  
    assumes "distinct l"
    shows "RETURN l \<le> it_to_sorted_list (\<lambda>_ _. True) (set l)"
    using assms unfolding it_to_sorted_list_def
    by refine_vcg auto

  lemma [sepref_gen_algo_rules]: "GEN_ALGO (return) (IS_TO_SORTED_LIST (\<lambda>_ _. True) (pure (\<langle>A\<rangle>list_set_rel)) (pure A))"
    unfolding GEN_ALGO_def IS_TO_SORTED_LIST_def
    apply (simp add: list_assn_pure_conv)
    apply rule
    apply rule
    apply (sep_auto simp: pure_def intro: it_to_sorted_list_triv simp: list_set_rel_def br_def)
    done

  lemma list_set_rel_compp:
    assumes "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A"  
    shows "\<langle>Id\<rangle>list_set_rel O \<langle>A\<rangle>set_rel = \<langle>A\<rangle>list_set_rel"
    unfolding list_set_rel_def
  proof (safe; clarsimp simp: in_br_conv)  
    fix x z
    assume "(set x,z)\<in>\<langle>A\<rangle>set_rel" "distinct x"
    from obtain_list_from_setrel[OF \<open>IS_RIGHT_UNIQUE A\<close> this(1)] obtain zl where
      [simp]: "z = set zl" and X_ZL: "(x, zl) \<in> \<langle>A\<rangle>list_rel" .
        
    have "distinct zl" 
      using param_distinct[OF assms, THEN fun_relD, OF X_ZL] \<open>distinct x\<close>
      by auto  
    show "(x,z) \<in> \<langle>A\<rangle>list_rel O br set distinct"  
      apply (rule relcompI[OF X_ZL])
      by (auto simp: in_br_conv \<open>distinct zl\<close>)  
  next    
    fix x y
    assume XY: "(x, y) \<in> \<langle>A\<rangle>list_rel" and "distinct y"  

    have "distinct x" 
      using param_distinct[OF assms, THEN fun_relD, OF XY] \<open>distinct y\<close>
      by auto  
      
    show "(x, set y) \<in> br set distinct O \<langle>A\<rangle>set_rel"  
      apply (rule relcompI[where b="set x"])
      subgoal by (auto simp: in_br_conv \<open>distinct x\<close>)
      subgoal by (rule param_set[OF \<open>IS_RIGHT_UNIQUE A\<close>, THEN fun_relD, OF XY])
      done  
  qed

  lemma GEN_OP_EQ_Id: "GEN_OP (=) (=) (Id\<rightarrow>Id\<rightarrow>bool_rel)" by simp

  hide_const (open) Intf_Set.op_set_isEmpty Intf_Set.op_set_delete

  lemma autoref_import_set_unfolds:
    "{} = op_set_empty"
    "uncurry (RETURN oo (\<in>)) = uncurry (RETURN oo op_set_member)"
    "Intf_Set.op_set_isEmpty = IICF_Set.op_set_is_empty"
    "Intf_Set.op_set_delete = IICF_Set.op_set_delete"
    "insert = IICF_Set.op_set_insert"
    by (auto intro!: ext)


  context fixes A :: "'a \<Rightarrow> 'ai \<Rightarrow> assn" begin
    private lemma APA: "\<lbrakk>PROP Q; CONSTRAINT is_pure A\<rbrakk> \<Longrightarrow> PROP Q" .
    private lemma APAru: "\<lbrakk>PROP Q; CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) A\<rbrakk> \<Longrightarrow> PROP Q" .
    private lemma APAlu: "\<lbrakk>PROP Q; CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) A\<rbrakk> \<Longrightarrow> PROP Q" .
    private lemma APAbu: "\<lbrakk>PROP Q; CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) A; CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) A\<rbrakk> \<Longrightarrow> PROP Q" .
    definition "list_set_assn = pure (\<langle>Id\<rangle>list_set_rel O \<langle>the_pure A\<rangle>set_rel)"
    context
      notes [fcomp_norm_unfold] = list_set_assn_def[symmetric]
      notes [simp] = IS_LEFT_UNIQUE_def
    begin

      lemmas hnr_op_ls_empty = list_set_autoref_empty[of Id, sepref_param, unfolded autoref_import_set_unfolds,
        FCOMP op_set_empty.fref[of "the_pure A"]]
      lemmas hnr_mop_ls_empty = hnr_op_ls_empty[FCOMP mk_mop_rl0_np[OF mop_set_empty_alt]]

      definition [simp]: "op_ls_empty = op_set_empty"
      sepref_register op_ls_empty
    
      lemmas hnr_op_ls_is_empty[sepref_fr_rules] = list_set_autoref_isEmpty[of Id, sepref_param, THEN APA, unfolded autoref_import_set_unfolds,
        FCOMP op_set_is_empty.fref[of "the_pure A"]]
      lemmas hnr_mop_ls_is_empty[sepref_fr_rules] = hnr_op_ls_is_empty[FCOMP mk_mop_rl1_np[OF mop_set_is_empty_alt]]

      lemmas hnr_op_ls_member[sepref_fr_rules] = list_set_autoref_member[OF GEN_OP_EQ_Id, sepref_param, THEN APAlu, unfolded autoref_import_set_unfolds,
        FCOMP op_set_member.fref[of "the_pure A"]]
      lemmas hnr_mop_ls_member[sepref_fr_rules] = hnr_op_ls_member[FCOMP mk_mop_rl2_np[OF mop_set_member_alt]]

      lemmas hnr_op_ls_insert[sepref_fr_rules] = list_set_autoref_insert[OF GEN_OP_EQ_Id, sepref_param, THEN APAru, unfolded autoref_import_set_unfolds,
        FCOMP op_set_insert.fref[of "the_pure A"]]
      lemmas hnr_mop_ls_insert[sepref_fr_rules] = hnr_op_ls_insert[FCOMP mk_mop_rl2_np[OF mop_set_insert_alt]]

      lemmas hnr_op_ls_delete[sepref_fr_rules] = list_set_autoref_delete[OF GEN_OP_EQ_Id, sepref_param, THEN APAbu, unfolded autoref_import_set_unfolds,
        FCOMP op_set_delete.fref[of "the_pure A"]]
      lemmas hnr_mop_ls_delete[sepref_fr_rules] = hnr_op_ls_delete[FCOMP mk_mop_rl2_np[OF mop_set_delete_alt]]

      text \<open>Adapting this optimization from Autoref. \<close>
      sepref_decl_op set_insert_dj: "insert" :: "[\<lambda>(x,s). x\<notin>s]\<^sub>f K \<times>\<^sub>r \<langle>K\<rangle>set_rel \<rightarrow> \<langle>K\<rangle>set_rel" 
        where "IS_RIGHT_UNIQUE K" "IS_LEFT_UNIQUE K" .
  
      lemma fold_set_insert_dj: "Set.insert = op_set_insert_dj" by simp

      lemma ls_insert_dj_hnr_aux: 
        "(uncurry (return oo Cons), uncurry mop_set_insert_dj) \<in> (pure Id)\<^sup>k *\<^sub>a (pure (\<langle>Id\<rangle>list_set_rel))\<^sup>k \<rightarrow>\<^sub>a pure (\<langle>Id\<rangle>list_set_rel)"
        using list_set_autoref_insert_dj[where R=Id,param_fo]
        apply (sep_auto intro!: hfrefI hn_refineI simp: pure_def refine_pw_simps eintros del: exI)
        apply force
        done

      lemmas ls_insert_dj_hnr[sepref_fr_rules] = ls_insert_dj_hnr_aux[THEN APAbu, FCOMP mop_set_insert_dj.fref[of "the_pure A"]]  
      lemmas ls_insert_dj_hnr_mop[sepref_fr_rules] 
        = ls_insert_dj_hnr[FCOMP mk_op_rl2[OF mop_set_insert_dj_alt]]

      private lemma hd_in_set_conv: "hd l \<in> set l \<longleftrightarrow> l\<noteq>[]" by auto
    
      lemma ls_pick_hnr_aux: "(return o hd, mop_set_pick) \<in> (pure (\<langle>Id\<rangle>list_set_rel))\<^sup>k \<rightarrow>\<^sub>a id_assn"
        apply (sep_auto 
          intro!: hfrefI hn_refineI 
          simp: pure_def IS_PURE_def IS_ID_def list_set_rel_def refine_pw_simps
          eintros del: exI)
        apply (auto simp: in_br_conv hd_in_set_conv)
        done    

      lemmas ls_pick_hnr[sepref_fr_rules] = ls_pick_hnr_aux[THEN APA,FCOMP mop_set_pick.fref[of "the_pure A"]]
      lemma ls_pick_hnr_mop[sepref_fr_rules]: "CONSTRAINT is_pure A \<Longrightarrow> (return \<circ> hd, op_set_pick) \<in> [\<lambda>s. s\<noteq>{}]\<^sub>a list_set_assn\<^sup>k \<rightarrow> A"
        using ls_pick_hnr
        by (simp add: hfref_to_ASSERT_conv mop_set_pick_alt[abs_def])

    end
  end    

  interpretation ls: set_custom_empty "return []" op_ls_empty
    by unfold_locales simp
  lemmas [sepref_fr_rules] = hnr_op_ls_empty[folded op_ls_empty_def]
    

end

