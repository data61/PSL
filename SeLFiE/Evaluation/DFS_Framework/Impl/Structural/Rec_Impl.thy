section \<open>Recursive DFS Implementation\<close>
theory Rec_Impl
imports General_DFS_Structure
begin

locale rec_impl_defs =
  graph_defs G + gen_dfs_defs gds V0
  for G :: "('v, 'more) graph_rec_scheme"
  and gds :: "('v,'s)gen_dfs_struct"
  +
  fixes pending :: "'s \<Rightarrow> 'v rel"
  fixes stack :: "'s \<Rightarrow> 'v list"
  fixes choose_pending :: "'v \<Rightarrow> 'v option \<Rightarrow> 's \<Rightarrow> 's nres"
begin

  definition "gen_step' s \<equiv> do { ASSERT (gen_rwof s);
    if gds_is_empty_stack gds s then do {
      v0 \<leftarrow> SPEC (\<lambda>v0. v0 \<in> V0 \<and> \<not> gds_is_discovered gds v0 s);
      gds_new_root gds v0 s
    } else do {
      let u = hd (stack s);
      Vs \<leftarrow> SELECT (\<lambda>v. (u,v)\<in>pending s);
      s \<leftarrow> choose_pending u Vs s;
      case Vs of 
        None \<Rightarrow> gds_finish gds u s
      | Some v \<Rightarrow>
         if gds_is_discovered gds v s
         then if gds_is_finished gds v s then gds_cross_edge gds u v s
              else gds_back_edge gds u v s
         else gds_discover gds u v s
    }}"  

  definition "gen_dfs' \<equiv> gds_init gds \<bind> WHILE gen_cond gen_step'"
  abbreviation "gen_rwof' \<equiv> rwof (gds_init gds) gen_cond gen_step'"

  definition rec_impl where [DFS_code_unfold]:
  "rec_impl \<equiv> do {
    s \<leftarrow> gds_init gds;

    FOREACHci 
      (\<lambda>it s. 
          gen_rwof' s 
        \<and> (\<not>gds_is_break gds s \<longrightarrow> gds_is_empty_stack gds s
            \<and> V0-it \<subseteq> gen_discovered s))
      V0
      (Not o gds_is_break gds) 
      (\<lambda>v0 s. do {
        let s0 = GHOST s;
        if gds_is_discovered gds v0 s then
          RETURN s
        else do {
          s \<leftarrow> gds_new_root gds v0 s;
          if gds_is_break gds s then
            RETURN s
          else do {
            REC_annot
            (\<lambda>(u,s). gen_rwof' s \<and> \<not>gds_is_break gds s 
                \<and> (\<exists>stk. stack s = u#stk) 
                \<and> E \<inter> {u}\<times>UNIV \<subseteq> pending s)
            (\<lambda>(u,s) s'. 
                  gen_rwof' s' 
                \<and> (\<not>gds_is_break gds s' \<longrightarrow> 
                    stack s' = tl (stack s) 
                  \<and> pending s' = pending s - {u} \<times> UNIV
                  \<and> gen_discovered s' \<supseteq> gen_discovered s
                  ))
            (\<lambda>D (u,s). do {
              s \<leftarrow> FOREACHci 
                (\<lambda>it s'. gen_rwof' s'
                \<and> (\<not>gds_is_break gds s' \<longrightarrow>
                    stack s' = stack s 
                  \<and> pending s' = (pending s - {u}\<times>(E``{u} - it))
                  \<and> gen_discovered s' \<supseteq> gen_discovered s \<union> (E``{u} - it)
                  )) 
                (E``{u}) (\<lambda>s. \<not>gds_is_break gds s) 
                (\<lambda>v s. do {
                  s \<leftarrow> choose_pending u (Some v) s;
                  if gds_is_discovered gds v s then do {
                    if gds_is_finished gds v s then
                      gds_cross_edge gds u v s
                    else
                      gds_back_edge gds u v s
                  } else do {
                    s \<leftarrow> gds_discover gds u v s;
                    if gds_is_break gds s then RETURN s else D (v,s) 
                  }
                }) 
                s;
              if gds_is_break gds s then 
                RETURN s
              else do {
                s \<leftarrow> choose_pending u (None) s;
                s \<leftarrow> gds_finish gds u s;
                RETURN s
              } 
            }) (v0,s)
          }
        }
      }) s
    }"

  definition rec_impl_for_paper where "rec_impl_for_paper \<equiv> do {
    s \<leftarrow> gds_init gds;
    FOREACHc V0 (Not o gds_is_break gds) (\<lambda>v0 s. do {
      if gds_is_discovered gds v0 s then RETURN s
      else do {
        s \<leftarrow> gds_new_root gds v0 s;
        if gds_is_break gds s then RETURN s
        else do {
          REC (\<lambda>D (u,s). do {
            s \<leftarrow> FOREACHc (E``{u}) (\<lambda>s. \<not>gds_is_break gds s) (\<lambda>v s. do {
                s \<leftarrow> choose_pending u (Some v) s;
                if gds_is_discovered gds v s then do {
                  if gds_is_finished gds v s then gds_cross_edge gds u v s
                  else gds_back_edge gds u v s
                } else do {
                  s \<leftarrow> gds_discover gds u v s;
                  if gds_is_break gds s then RETURN s else D (v,s) 
                }
              }) 
              s;
            if gds_is_break gds s then RETURN s
            else do {
              s \<leftarrow> choose_pending u (None) s;
              gds_finish gds u s
            } 
          }) (v0,s)
        }
      }
    }) s
  }"

end

(* Recursive implementation of general DFS *)
locale rec_impl =
  fb_graph G + gen_dfs gds V0 + rec_impl_defs G gds pending stack choose_pending
  for G :: "('v, 'more) graph_rec_scheme"
  and gds :: "('v,'s)gen_dfs_struct"
  and pending :: "'s \<Rightarrow> 'v rel"
  and stack :: "'s \<Rightarrow> 'v list"
  and choose_pending :: "'v \<Rightarrow> 'v option \<Rightarrow> 's \<Rightarrow> 's nres"
  +
  assumes [simp]: "gds_is_empty_stack gds s \<longleftrightarrow> stack s = []"
  assumes init_spec: 
    "gds_init gds \<le>\<^sub>n SPEC (\<lambda>s. stack s = [] \<and> pending s = {})"
  assumes new_root_spec: 
    "\<lbrakk>pre_new_root v0 s\<rbrakk> 
      \<Longrightarrow> gds_new_root gds v0 s \<le>\<^sub>n SPEC (\<lambda>s'. 
        stack s' = [v0] \<and> pending s' = {v0}\<times>E``{v0} \<and>
        gen_discovered s' = insert v0 (gen_discovered s))"

  assumes get_pending_fmt: "\<lbrakk> pre_get_pending s \<rbrakk> \<Longrightarrow> 
    do {
      let u = hd (stack s);
      vo \<leftarrow> SELECT (\<lambda>v. (u,v)\<in>pending s);
      s \<leftarrow> choose_pending u vo s;
      RETURN (u,vo,s)
    } 
  \<le> gds_get_pending gds s" (* TODO: \<le>\<^sub>n should be enough here! *)

  assumes choose_pending_spec: "\<lbrakk>pre_get_pending s; u = hd (stack s); 
    case vo of 
      None \<Rightarrow> pending s `` {u} = {}
    | Some v \<Rightarrow> v\<in>pending s `` {u}
  \<rbrakk> \<Longrightarrow>
    choose_pending u vo s \<le>\<^sub>n SPEC (\<lambda>s'. 
      (case vo of
        None \<Rightarrow> pending s' = pending s
      | Some v \<Rightarrow> pending s' = pending s - {(u,v)}) \<and>
      stack s' = stack s \<and>
      (\<forall>x. gds_is_discovered gds x s' = gds_is_discovered gds x s) 
      \<^cancel>\<open>\<and> gds_is_break gds s' = gds_is_break gds s\<close>
    )"
  assumes finish_spec: "\<lbrakk>pre_finish u s0 s\<rbrakk> 
    \<Longrightarrow> gds_finish gds u s \<le>\<^sub>n SPEC (\<lambda>s'. 
      pending s' = pending s \<and>
      stack s' = tl (stack s) \<and>
      (\<forall>x. gds_is_discovered gds x s' = gds_is_discovered gds x s))"
  assumes cross_edge_spec: "pre_cross_edge u v s0 s 
    \<Longrightarrow> gds_cross_edge gds u v s \<le>\<^sub>n SPEC (\<lambda>s'. 
      pending s' = pending s \<and> stack s' = stack s \<and>
      (\<forall>x. gds_is_discovered gds x s' = gds_is_discovered gds x s))"
  assumes back_edge_spec: "pre_back_edge u v s0 s 
    \<Longrightarrow> gds_back_edge gds u v s \<le>\<^sub>n SPEC (\<lambda>s'. 
      pending s' = pending s \<and> stack s' = stack s \<and>
      (\<forall>x. gds_is_discovered gds x s' = gds_is_discovered gds x s))"
  assumes discover_spec: "pre_discover u v s0 s 
    \<Longrightarrow> gds_discover gds u v s \<le>\<^sub>n SPEC (\<lambda>s'. 
      pending s' = pending s \<union> ({v} \<times> E``{v}) \<and> stack s' = v#stack s \<and>
      gen_discovered s' = insert v (gen_discovered s))"



begin

    
  lemma gen_step'_refine: 
    "\<lbrakk>gen_rwof s; gen_cond s\<rbrakk> \<Longrightarrow> gen_step' s \<le> gen_step s"
    apply (simp only: gen_step'_def gen_step_def)
    apply (clarsimp)
    apply (rule order_trans[OF _ bind_mono(1)[OF get_pending_fmt order_refl]])
    apply (simp add: pw_le_iff refine_pw_simps
      split: option.splits if_split)
    apply (simp add: pre_defs gen_cond_def)
    done


  lemma gen_dfs'_refine: "gen_dfs' \<le> gen_dfs"
    unfolding gen_dfs'_def gen_dfs_def WHILE_eq_I_rwof[where f=gen_step]
    apply (rule refine_IdD)    
    apply (refine_rcg)
    by (simp_all add: gen_step'_refine)

  lemma gen_rwof'_imp_rwof:
    assumes NF: "nofail gen_dfs"
    assumes A: "gen_rwof' s"
    shows "gen_rwof s"
    apply (rule rwof_step_refine)
      apply (rule NF[unfolded gen_dfs_def])

      apply fact

      apply (rule leof_lift[OF gen_step'_refine], assumption+) []
    done


  lemma reachable_invar: 
    "gen_rwof' s \<Longrightarrow> set (stack s) \<subseteq> reachable \<and> pending s \<subseteq> E 
      \<and> set (stack s) \<subseteq> gen_discovered s \<and> distinct (stack s)
      \<and> pending s \<subseteq> set (stack s) \<times> UNIV"
    apply (erule establish_rwof_invar[rotated -1])    
    apply (rule leof_trans[OF init_spec], auto) []
    apply (subst gen_step'_def)
    apply (refine_rcg refine_vcg
      leof_trans[OF new_root_spec]
      SELECT_rule[THEN leof_lift]
      leof_trans[OF choose_pending_spec[THEN leof_strengthen_SPEC]]
      leof_trans[OF finish_spec]
      leof_trans[OF cross_edge_spec]
      leof_trans[OF back_edge_spec]
      leof_trans[OF discover_spec]
      )
    

    apply simp_all
    subgoal by (simp add: pre_defs, simp add: gen_cond_def)
    subgoal by auto    
    subgoal by auto    
    subgoal by auto    
    subgoal by (simp add: pre_defs, simp add: gen_cond_def)
        
        
    apply ((unfold pre_defs, intro conjI); assumption?) []
      subgoal by (clarsimp simp: gen_cond_def)
      subgoal by (clarsimp simp: gen_cond_def)
      subgoal    
        apply (rule pwD2[OF get_pending_fmt])
          subgoal by (simp add: pre_defs gen_cond_def)
          subgoal by (clarsimp simp: refine_pw_simps; blast)
        done      
      subgoal by (force simp: neq_Nil_conv) []
          
          
    subgoal by (clarsimp simp: neq_Nil_conv gen_cond_def, blast) [] 
    subgoal by (clarsimp simp: neq_Nil_conv gen_cond_def; auto)

    apply (unfold pre_defs, intro conjI, assumption) []
      subgoal by (clarsimp_all simp: gen_cond_def)
      subgoal by (clarsimp_all simp: gen_cond_def)
      apply (rule pwD2[OF get_pending_fmt])
        apply (simp add: pre_defs gen_cond_def; fail)
        apply (clarsimp simp: refine_pw_simps select_def, blast; fail)
        apply (simp; fail)
        apply (simp; fail)

    subgoal by auto
    subgoal by fast

    apply (unfold pre_defs, intro conjI, assumption) []
      apply (clarsimp simp: gen_cond_def; fail)
      apply (clarsimp simp: gen_cond_def; fail)
      apply (rule pwD2[OF get_pending_fmt])
        apply (simp add: pre_defs gen_cond_def; fail)
        apply (clarsimp simp: refine_pw_simps select_def, blast; fail)
        apply (simp; fail)

    subgoal  
      apply clarsimp  
      by (meson ImageI SigmaD1 rtrancl_image_unfold_right subset_eq)  

    subgoal  
      apply clarsimp  
      by blast  
        
    apply force
    apply force
    apply fast
    apply (auto simp: pre_defs gen_cond_def; fail)
    apply fast

    apply ((unfold pre_defs, intro conjI); assumption?)
      apply (clarsimp simp: gen_cond_def; fail)
      apply (clarsimp simp: gen_cond_def; fail)
      apply (rule pwD2[OF get_pending_fmt])
        apply (simp add: pre_defs gen_cond_def; fail)
        apply (clarsimp simp: refine_pw_simps; fail)

    apply (auto simp: neq_Nil_conv; fail)
    apply (auto simp: neq_Nil_conv; fail)
    apply (clarsimp simp: neq_Nil_conv; blast) 
    done

  lemma mk_spec_aux: 
    "\<lbrakk>m \<le>\<^sub>n SPEC \<Phi>; m\<le>SPEC gen_rwof' \<rbrakk> \<Longrightarrow> m \<le> SPEC (\<lambda>s. gen_rwof' s \<and> \<Phi> s)"  
    by (rule SPEC_rule_conj_leofI1)


  definition "post_choose_pending u vo s0 s \<equiv> 
    gen_rwof' s0 
  \<and> gen_cond s0
  \<and> stack s0 \<noteq> []
  \<and> u=hd (stack s0)  
  \<and> inres (choose_pending u vo s0) s 
  \<and> stack s = stack s0
  \<and> (\<forall>x. gds_is_discovered gds x s = gds_is_discovered gds x s0)
  \<^cancel>\<open>\<and> gds_is_break gds s = gds_is_break gds s0\<close>
  \<and> (case vo of
      None \<Rightarrow> pending s0``{u}={} \<and> pending s = pending s0
    | Some v \<Rightarrow> v \<in> pending s0``{u} \<and> pending s = pending s0 - {(u,v)})"

  context
    assumes nofail: 
      "nofail (gds_init gds \<bind> WHILE gen_cond gen_step')"
    assumes nofail2: 
      "nofail (gen_dfs)"
  begin
    lemma pcp_imp_pgp: 
      "post_choose_pending u vo s0 s \<Longrightarrow> post_get_pending u vo s0 s"
      unfolding post_choose_pending_def pre_defs
      apply (intro conjI)
      apply (simp add: gen_rwof'_imp_rwof[OF nofail2])
      apply simp
      apply (simp add: gen_cond_def)
      apply (rule pwD2[OF get_pending_fmt])
      apply (simp add: pre_defs gen_cond_def 
          gen_rwof'_imp_rwof[OF nofail2])
      apply (auto simp add: refine_pw_simps select_def split: option.splits) []
      done

    schematic_goal gds_init_refine: "?prop"
      apply (rule mk_spec_aux[OF init_spec])
      apply (rule rwof_init[OF nofail])
      done      

    schematic_goal gds_new_root_refine: 
      "\<lbrakk>pre_new_root v0 s; gen_rwof' s\<rbrakk> \<Longrightarrow> gds_new_root gds v0 s \<le> SPEC ?\<Phi>"
      apply (rule mk_spec_aux[OF new_root_spec], assumption)
      apply (rule order_trans[OF _ rwof_step[OF nofail, where s=s]])
      unfolding gen_step'_def pre_new_root_def gen_cond_def
      apply (auto simp: pw_le_iff refine_pw_simps)
      done      

    schematic_goal gds_choose_pending_refine: 
      assumes 1: "pre_get_pending s"
      assumes 2: "gen_rwof' s"
      assumes [simp]: "u=hd (stack s)"
      assumes 3: "case vo of 
          None \<Rightarrow> pending s `` {u} = {}
        | Some v \<Rightarrow> v \<in> pending s `` {u}"
      shows "choose_pending u vo s \<le> SPEC (post_choose_pending u vo s)"
    proof -
      from WHILE_nofail_imp_rwof_nofail[OF nofail 2] 1 3 have 
        "nofail (choose_pending u vo s)"
        unfolding pre_defs gen_step'_def gen_cond_def
        by (auto simp: refine_pw_simps select_def 
          split: option.splits if_split_asm)
      also have "choose_pending u vo s \<le>\<^sub>n SPEC (post_choose_pending u vo s)"
        apply (rule leof_trans[OF choose_pending_spec[OF 1 _ 3, THEN leof_strengthen_SPEC]])
        apply simp
        apply (rule leof_RES_rule)
        using 1
        apply (simp add: post_choose_pending_def 2 pre_defs gen_cond_def split: option.splits)
        using 3
        apply auto
        done
      finally (leofD) show ?thesis .
    qed

    schematic_goal gds_finish_refine: 
      "\<lbrakk>pre_finish u s0 s; post_choose_pending u None s0 s\<rbrakk> \<Longrightarrow> gds_finish gds u s \<le> SPEC ?\<Phi>"
      apply (rule mk_spec_aux[OF finish_spec], assumption)
      apply (rule order_trans[OF _ rwof_step[OF nofail, where s=s0]])
      unfolding gen_step'_def pre_defs gen_cond_def post_choose_pending_def
      apply (auto simp: pw_le_iff refine_pw_simps split: option.split)  
      done      

    schematic_goal gds_cross_edge_refine: 
      "\<lbrakk>pre_cross_edge u v s0 s; post_choose_pending u (Some v) s0 s\<rbrakk> \<Longrightarrow> gds_cross_edge gds u v s \<le> SPEC ?\<Phi>"
      apply (rule mk_spec_aux[OF cross_edge_spec], assumption)
      apply (rule order_trans[OF _ rwof_step[OF nofail, where s=s0]])
      unfolding gen_step'_def pre_defs gen_cond_def post_choose_pending_def
      apply (simp add: pw_le_iff refine_pw_simps select_def split: option.split, blast) 
      apply simp
      apply blast
      done      

    schematic_goal gds_back_edge_refine: 
      "\<lbrakk>pre_back_edge u v s0 s; post_choose_pending u (Some v) s0 s\<rbrakk> \<Longrightarrow> gds_back_edge gds u v s \<le> SPEC ?\<Phi>"
      apply (rule mk_spec_aux[OF back_edge_spec], assumption)
      apply (rule order_trans[OF _ rwof_step[OF nofail, where s=s0]])
      unfolding gen_step'_def pre_defs gen_cond_def post_choose_pending_def
      apply (simp add: pw_le_iff refine_pw_simps select_def split: option.split, blast) 
      apply simp
      apply blast
      done      

    schematic_goal gds_discover_refine: 
      "\<lbrakk>pre_discover u v s0 s; post_choose_pending u (Some v) s0 s\<rbrakk> \<Longrightarrow> gds_discover gds u v s \<le> SPEC ?\<Phi>"
      apply (rule mk_spec_aux[OF discover_spec], assumption)
      apply (rule order_trans[OF _ rwof_step[OF nofail, where s=s0]])
      unfolding gen_step'_def pre_defs gen_cond_def post_choose_pending_def
      apply (simp add: pw_le_iff refine_pw_simps select_def split: option.split, blast) 
      apply simp
      apply blast
      done      
  end

  
  lemma rec_impl_aux: "\<lbrakk> xd\<notin>Domain P \<rbrakk> \<Longrightarrow> P - {y} \<times> (succ y - ita) - {(y, xd)} - {xd} \<times> UNIV =
           P - insert (y, xd) ({y} \<times> (succ y - ita))"
    apply auto
    done
           

  lemma rec_impl: "rec_impl \<le> gen_dfs"
    apply (rule le_nofailI)
    apply (rule order_trans[OF _ gen_dfs'_refine])
    unfolding gen_dfs'_def
    apply (rule WHILE_refine_rwof)
    unfolding rec_impl_def
    apply (refine_rcg refine_vcg
      order_trans[OF gds_init_refine]
      order_trans[OF gds_choose_pending_refine]
      order_trans[OF gds_new_root_refine]
      order_trans[OF gds_finish_refine]
      order_trans[OF gds_back_edge_refine]
      order_trans[OF gds_cross_edge_refine]
      order_trans[OF gds_discover_refine]
    )
    apply (simp_all split: if_split_asm)

    using [[goals_limit = 1]]

    apply (auto simp add: pre_defs; fail)
    apply (auto simp add: pre_defs gen_rwof'_imp_rwof; fail)
    apply (auto; fail)
    apply (auto dest: reachable_invar; fail)
    apply (auto simp add: pre_defs gen_rwof'_imp_rwof; fail)
    apply (auto; fail)
    apply (auto; fail)

    apply ((drule pcp_imp_pgp, auto simp add: pre_defs gen_rwof'_imp_rwof); fail)

    apply (auto simp: post_choose_pending_def; fail)
    apply (auto simp: post_choose_pending_def; fail)
    apply (auto simp: post_choose_pending_def; fail)

    apply ((drule pcp_imp_pgp, auto simp add: pre_defs gen_rwof'_imp_rwof); fail)

    apply (auto simp: post_choose_pending_def; fail)
    apply (auto simp: post_choose_pending_def; fail)
    apply (auto simp: post_choose_pending_def; fail)

    apply ((drule pcp_imp_pgp, auto simp add: pre_defs gen_rwof'_imp_rwof); fail)

    apply (rule order_trans)
    apply rprems
    apply (auto; fail) []
    subgoal 
      apply (rule SPEC_rule)
      apply (simp add: post_choose_pending_def gen_rwof'_imp_rwof
        split: if_split_asm)
      apply (clarsimp 
        simp: gen_rwof'_imp_rwof Un_Diff
        split: if_split_asm) []
      apply (clarsimp simp: it_step_insert_iff neq_Nil_conv)
      apply (rule conjI)
      subgoal
        apply (rule rec_impl_aux)
        apply (drule reachable_invar)+
        apply (metis Domain.cases SigmaD1 mem_Collect_eq rev_subsetD)
      done
      subgoal
        apply (rule conjI)
        apply auto []
        apply (metis order_trans)
      done
    done

    apply (auto simp add: pre_defs gen_rwof'_imp_rwof; fail)
    apply (auto; fail)
    apply (auto dest: reachable_invar; fail)

    apply ((drule pcp_imp_pgp, auto simp add: pre_defs gen_rwof'_imp_rwof); fail)

    apply (auto simp: post_choose_pending_def; fail)
    apply (auto simp: post_choose_pending_def; fail)
    apply (auto simp: post_choose_pending_def; fail)

    apply (auto; fail)

    apply (auto simp: gen_cond_def; fail)

    apply (auto simp: gen_cond_def; fail)
    done

end

end
