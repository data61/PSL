section \<open>Tail-Recursive Implementation\<close>
theory Tailrec_Impl
imports General_DFS_Structure
begin

locale tailrec_impl_defs =
  graph_defs G + gen_dfs_defs gds V0
  for G :: "('v, 'more) graph_rec_scheme"
  and gds :: "('v,'s)gen_dfs_struct"
begin
  definition [DFS_code_unfold]: "tr_impl_while_body \<equiv> \<lambda>s. do {
    (u,Vs,s) \<leftarrow> gds_get_pending gds s;
    case Vs of 
      None \<Rightarrow> gds_finish gds u s 
    | Some v \<Rightarrow> do {
      if gds_is_discovered gds v s then do {
        if gds_is_finished gds v s then
          gds_cross_edge gds u v s
        else
          gds_back_edge gds u v s
      } else 
        gds_discover gds u v s
    }
  }"

  definition tailrec_implT where [DFS_code_unfold]: 
  "tailrec_implT \<equiv> do {
    s \<leftarrow> gds_init gds;

    FOREACHci 
      (\<lambda>it s. 
          gen_rwof s 
        \<and> (\<not>gds_is_break gds s \<longrightarrow> gds_is_empty_stack gds s )
        \<and> V0-it \<subseteq> gen_discovered s) 
      V0
      (Not o gds_is_break gds) 
      (\<lambda>v0 s. do {
        let \<comment> \<open>ghost:\<close> s0 = s;
        if gds_is_discovered gds v0 s then
          RETURN s
        else do {
          s \<leftarrow> gds_new_root gds v0 s;
          WHILEIT
            (\<lambda>s. gen_rwof s \<and> insert v0 (gen_discovered s0) \<subseteq> gen_discovered s)
            (\<lambda>s. \<not>gds_is_break gds s \<and> \<not>gds_is_empty_stack gds s) 
            tr_impl_while_body s
        }
      }) s
    }"

  definition tailrec_impl where [DFS_code_unfold]: 
  "tailrec_impl \<equiv> do {
    s \<leftarrow> gds_init gds;

    FOREACHci 
      (\<lambda>it s. 
          gen_rwof s 
        \<and> (\<not>gds_is_break gds s \<longrightarrow> gds_is_empty_stack gds s )
        \<and> V0-it \<subseteq> gen_discovered s) 
      V0
      (Not o gds_is_break gds) 
      (\<lambda>v0 s. do {
        let \<comment> \<open>ghost:\<close> s0 = s;
        if gds_is_discovered gds v0 s then
          RETURN s
        else do {
          s \<leftarrow> gds_new_root gds v0 s;
          WHILEI
            (\<lambda>s. gen_rwof s \<and> insert v0 (gen_discovered s0) \<subseteq> gen_discovered s)
            (\<lambda>s. \<not>gds_is_break gds s \<and> \<not>gds_is_empty_stack gds s) 
            (\<lambda>s. do {
              (u,Vs,s) \<leftarrow> gds_get_pending gds s;
              case Vs of 
                None \<Rightarrow> gds_finish gds u s 
              | Some v \<Rightarrow> do {
                if gds_is_discovered gds v s then do {
                  if gds_is_finished gds v s then
                    gds_cross_edge gds u v s
                  else
                    gds_back_edge gds u v s
                } else 
                  gds_discover gds u v s
              }
            }) s
        }
      }) s
    }"

end


text \<open> Implementation of general DFS with outer foreach-loop \<close>
locale tailrec_impl =
  fb_graph G + gen_dfs gds V0 + tailrec_impl_defs G gds
  for G :: "('v, 'more) graph_rec_scheme"
  and gds :: "('v,'s)gen_dfs_struct"
  +
  assumes init_empty_stack: 
    "gds_init gds \<le>\<^sub>n SPEC (gds_is_empty_stack gds)"
  assumes new_root_discovered: 
    "\<lbrakk>pre_new_root v0 s\<rbrakk> 
      \<Longrightarrow> gds_new_root gds v0 s \<le>\<^sub>n SPEC (\<lambda>s'. 
        insert v0 (gen_discovered s) \<subseteq> gen_discovered s')"
  assumes get_pending_incr:
    "\<lbrakk>pre_get_pending s\<rbrakk> \<Longrightarrow> gds_get_pending gds s \<le>\<^sub>n SPEC (\<lambda>(_,_,s'). 
        gen_discovered s \<subseteq> gen_discovered s' 
      \<^cancel>\<open>\<and> gds_is_break gds s' = gds_is_break gds s\<close>)"
  assumes finish_incr: "\<lbrakk>pre_finish u s0 s\<rbrakk> 
    \<Longrightarrow> gds_finish gds u s \<le>\<^sub>n SPEC (\<lambda>s'. 
      gen_discovered s \<subseteq> gen_discovered s')"
  assumes cross_edge_incr: "pre_cross_edge u v s0 s 
    \<Longrightarrow> gds_cross_edge gds u v s \<le>\<^sub>n SPEC (\<lambda>s'. 
      gen_discovered s \<subseteq> gen_discovered s')"
  assumes back_edge_incr: "pre_back_edge u v s0 s 
    \<Longrightarrow> gds_back_edge gds u v s \<le>\<^sub>n SPEC (\<lambda>s'. 
      gen_discovered s \<subseteq> gen_discovered s')"
  assumes discover_incr: "pre_discover u v s0 s 
    \<Longrightarrow> gds_discover gds u v s \<le>\<^sub>n SPEC (\<lambda>s'. 
      gen_discovered s \<subseteq> gen_discovered s')"
begin


  context
    assumes nofail: 
      "nofail (gds_init gds \<bind> WHILE gen_cond gen_step)"
  begin
    lemma gds_init_refine: "gds_init gds 
      \<le> SPEC (\<lambda>s. gen_rwof s \<and> gds_is_empty_stack gds s)"
      apply (rule SPEC_rule_conj_leofI1)
      apply (rule rwof_init[OF nofail])
      apply (rule init_empty_stack)
      done

    lemma gds_new_root_refine:
      assumes PNR: "pre_new_root v0 s"
      shows "gds_new_root gds v0 s 
        \<le> SPEC (\<lambda>s'. gen_rwof s' 
            \<and> insert v0 (gen_discovered s) \<subseteq> gen_discovered s' )"
      apply (rule SPEC_rule_conj_leofI1)
    
        apply (rule order_trans[OF _ rwof_step[OF nofail]])
          using PNR apply (unfold gen_step_def gen_cond_def pre_new_root_def) [3] 
          apply (simp add: pw_le_iff refine_pw_simps, blast)
          apply simp
          apply blast
  
        apply (rule new_root_discovered[OF PNR])
      done


    (* Establish state after get-pending *)
    lemma get_pending_nofail:
      assumes A: "pre_get_pending s"  
      shows "nofail (gds_get_pending gds s)"
    proof -
      (* Get-pending is executed as part of the next step. 
        As the next step does not fail, get_pending cannot fail, too. *)
      from A[unfolded pre_get_pending_def] have 
        RWOF: "gen_rwof s" and
        C: "\<not> gds_is_empty_stack gds s" "\<not> gds_is_break gds s" 
        by auto

      from C have COND: "gen_cond s" unfolding gen_cond_def by auto

      from rwof_step[OF nofail RWOF COND] 
      have "gen_step s \<le> SPEC gen_rwof" .
      hence "nofail (gen_step s)" by (simp add: pw_le_iff)

      with C show ?thesis unfolding gen_step_def by (simp add: refine_pw_simps)
    qed

    lemma gds_get_pending_refine: 
      assumes PRE: "pre_get_pending s"
      shows "gds_get_pending gds s \<le> SPEC (\<lambda>(u,Vs,s'). 
          post_get_pending u Vs s s' 
        \<and> gen_discovered s \<subseteq> gen_discovered s')"
    proof -    
      have "gds_get_pending gds s \<le> SPEC (\<lambda>(u,Vs,s'). post_get_pending u Vs s s')"
        unfolding post_get_pending_def
        apply (simp add: PRE)
        using get_pending_nofail[OF PRE]
        apply (simp add: pw_le_iff)
        done
      moreover note get_pending_incr[OF PRE]
      ultimately show ?thesis by (simp add: pw_le_iff pw_leof_iff)
    qed

    lemma gds_finish_refine:
      assumes PRE: "pre_finish u s0 s"
      shows "gds_finish gds u s \<le> SPEC (\<lambda>s'. gen_rwof s' 
            \<and> gen_discovered s \<subseteq> gen_discovered s')"
      apply (rule SPEC_rule_conj_leofI1)
    
        apply (rule order_trans[OF _ rwof_step[OF nofail]])
          using PRE 
          apply (unfold gen_step_def gen_cond_def pre_finish_def 
            post_get_pending_def pre_get_pending_def) [3] 
          apply (simp add: pw_le_iff refine_pw_simps split: option.split, blast) 
          apply simp
          apply blast
  
        apply (rule finish_incr[OF PRE])
      done

    lemma gds_cross_edge_refine:
      assumes PRE: "pre_cross_edge u v s0 s"
      shows "gds_cross_edge gds u v s \<le> SPEC (\<lambda>s'. gen_rwof s' 
            \<and> gen_discovered s \<subseteq> gen_discovered s')"
      apply (rule SPEC_rule_conj_leofI1)
    
        apply (rule order_trans[OF _ rwof_step[OF nofail]])
          using PRE 
          apply (unfold gen_step_def gen_cond_def pre_cross_edge_def 
            post_get_pending_def pre_get_pending_def) [3] 
          apply (simp add: pw_le_iff refine_pw_simps split: option.split, blast) 
          apply simp
          apply blast
  
        apply (rule cross_edge_incr[OF PRE])
      done

    lemma gds_back_edge_refine:
      assumes PRE: "pre_back_edge u v s0 s"
      shows "gds_back_edge gds u v s \<le> SPEC (\<lambda>s'. gen_rwof s' 
            \<and> gen_discovered s \<subseteq> gen_discovered s')"
      apply (rule SPEC_rule_conj_leofI1)
    
        apply (rule order_trans[OF _ rwof_step[OF nofail]])
          using PRE 
          apply (unfold gen_step_def gen_cond_def pre_back_edge_def 
            post_get_pending_def pre_get_pending_def) [3] 
          apply (simp add: pw_le_iff refine_pw_simps split: option.split, blast) 
          apply simp
          apply blast
  
        apply (rule back_edge_incr[OF PRE])
      done


    lemma gds_discover_refine:
      assumes PRE: "pre_discover u v s0 s"
      shows "gds_discover gds u v s \<le> SPEC (\<lambda>s'. gen_rwof s' 
            \<and> gen_discovered s \<subseteq> gen_discovered s')"
      apply (rule SPEC_rule_conj_leofI1)
    
        apply (rule order_trans[OF _ rwof_step[OF nofail]])
          using PRE 
          apply (unfold gen_step_def gen_cond_def pre_discover_def 
            post_get_pending_def pre_get_pending_def) [3] 
          apply (simp add: pw_le_iff refine_pw_simps split: option.split, blast) 
          apply simp
          apply blast
  
        apply (rule discover_incr[OF PRE])
      done

  end

  lemma gen_step_disc_incr:
    assumes "nofail gen_dfs"
    assumes "gen_rwof s" "insert v0 (gen_discovered s0) \<subseteq> gen_discovered s"
    assumes "\<not>gds_is_break gds s" "\<not>gds_is_empty_stack gds s"
    shows "gen_step s \<le> SPEC (\<lambda>s. insert v0 (gen_discovered s0) \<subseteq> gen_discovered s)"
    using assms
    apply (simp only: gen_step_def gen_dfs_def)
    apply (refine_rcg refine_vcg 
      order_trans[OF gds_init_refine]
      order_trans[OF gds_new_root_refine]
      order_trans[OF gds_get_pending_refine]
      order_trans[OF gds_finish_refine]
      order_trans[OF gds_cross_edge_refine]
      order_trans[OF gds_back_edge_refine]
      order_trans[OF gds_discover_refine]
      )
    apply (auto 
      simp: it_step_insert_iff gen_cond_def
      pre_new_root_def pre_get_pending_def pre_finish_def 
      pre_cross_edge_def pre_back_edge_def pre_discover_def)
    done
    

  theorem tailrec_impl: "tailrec_impl \<le> gen_dfs"
    unfolding gen_dfs_def
    apply (rule WHILE_refine_rwof)
    unfolding tailrec_impl_def
    apply (refine_rcg refine_vcg 
      order_trans[OF gds_init_refine]
      order_trans[OF gds_new_root_refine]
      order_trans[OF gds_get_pending_refine]
      order_trans[OF gds_finish_refine]
      order_trans[OF gds_cross_edge_refine]
      order_trans[OF gds_back_edge_refine]
      order_trans[OF gds_discover_refine]
      )
    apply (auto 
      simp: it_step_insert_iff gen_cond_def
      pre_new_root_def pre_get_pending_def pre_finish_def 
      pre_cross_edge_def pre_back_edge_def pre_discover_def)
    done

  lemma tr_impl_while_body_gen_step:
    assumes [simp]: "\<not>gds_is_empty_stack gds s"
    shows "tr_impl_while_body s \<le> gen_step s"
    unfolding tr_impl_while_body_def gen_step_def
    by simp

  lemma tailrecT_impl: "tailrec_implT \<le> gen_dfsT"
  proof (rule le_nofailI)
    let ?V = "rwof_rel (gds_init gds) gen_cond gen_step"
    assume NF: "nofail gen_dfsT"
    from nofail_WHILEIT_wf_rel[of "gds_init gds" "\<lambda>_. True" gen_cond gen_step]
      and this[unfolded gen_dfsT_def WHILET_def]
    have WF: "wf (?V\<inverse>)" by simp

    from NF have NF': "nofail gen_dfs" using gen_dfs_le_gen_dfsT
      by (auto simp: pw_le_iff)

    from rwof_rel_spec[of "gds_init gds" gen_cond gen_step] have
      "\<And>s. \<lbrakk>gen_rwof s; gen_cond s\<rbrakk> \<Longrightarrow> gen_step s \<le>\<^sub>n SPEC (\<lambda>s'. (s,s')\<in>?V)"
      .
    hence 
      aux: "\<And>s. \<lbrakk>gen_rwof s; gen_cond s\<rbrakk> \<Longrightarrow> gen_step s \<le> SPEC (\<lambda>s'. (s,s')\<in>?V)"
      apply (rule leofD[rotated])
      apply assumption
      apply assumption
      using NF[unfolded gen_dfsT_def]
      by (drule (1) WHILET_nofail_imp_rwof_nofail)

    show ?thesis
      apply (rule order_trans[OF _ gen_dfs_le_gen_dfsT])
      apply (rule order_trans[OF _ tailrec_impl])
      unfolding tailrec_implT_def tailrec_impl_def
      unfolding tr_impl_while_body_def[symmetric]
      apply (rule refine_IdD)
      apply (refine_rcg bind_refine' inj_on_id)
      apply refine_dref_type
      apply simp_all
      apply (subst WHILEIT_eq_WHILEI_tproof[where V="?V\<inverse>"])
        apply (rule WF; fail)
        subgoal
          apply clarsimp
          apply (rule order_trans[OF tr_impl_while_body_gen_step], assumption)
          apply (rule aux, assumption, (simp add: gen_cond_def; fail))
        done  
        apply (simp; fail)
      done      
  qed

end  
end

