theory SM_Pid
imports Pid_Scheduler SM_Visible
begin

  type_synonym pid_global_config = "(cmdc,local_state,global_state) pid_global_config"
  type_synonym global_action = "(cmdc,action) global_action"

  context cprog begin
    definition pid_init_gc :: "pid_global_config" where
      "pid_init_gc \<equiv> \<lparr>
        pid_global_config.processes = (map init_pc (program.processes prog)),
        pid_global_config.state = \<lparr>
          global_state.variables = init_valuation (program.global_vars prog)
        \<rparr>
      \<rparr>"
  end

  context visible_prog begin  

    definition pid_interp_gc :: "pid_global_config \<Rightarrow> exp set" where
      "pid_interp_gc gc \<equiv> interp_gs (pid_global_config.state gc)"
  
    sublocale Pid_Gen_Scheduler_linit 
      cfgc la_en' la_ex' 
      "{init_gc}" interp_gc
      pid_init_gc pid_interp_gc
      apply unfold_locales
      apply (auto simp: pid_init_gc_def pidgc_\<alpha>_def init_gc_def
          interp_gc_def pid_interp_gc_def)
      done

    lemma "pid.accept = lv.sa.accept"  
      by (rule pid_accept_eq)

    lemma pid_run_sim': "pid.g.is_run r \<Longrightarrow> 
      ref_is_run prog (Some o gc_\<alpha> o pidgc_\<alpha> o r)"
      apply (drule pid_run_sim)
      using lih'_is_run_sim
      unfolding lih'.sa.is_run_def
      unfolding li.sa.is_run_def
      unfolding lv.sa.is_run_def
      apply simp
      using comp_assoc
      by (metis (no_types, lifting) comp_eq_dest_lhs)
      
    lemma ga_accept_eq': "ga.accept = lv.sa.accept"
      unfolding ga_accept_eq ..
      

    lemma ga_run_sim': "ga.is_run r \<Longrightarrow> 
      ref_is_run prog (Some o gc_\<alpha> o pidgc_\<alpha> o r)"
      using pid_run_sim'
      unfolding ga_run_eq
      by simp
  
    lemma jsys_lang_eq: "snth ` jsys.language = Collect (lv.sa.accept)"
      by (rule accept_eq_lang)

    lemma pid_finite_reachable: "finite (pid.g.E\<^sup>* `` pid.g.V0)"
    proof -
      { fix lcs s
        have "{gc. 
          mset (pid_global_config.processes gc) = lcs 
          \<and> pid_global_config.state gc = s}
        = ((\<lambda>a. pid_global_config.make a s))`{a. mset a = lcs}"
          apply (auto simp: pid_global_config.make_def)
          apply (case_tac x, auto)
          done
      } note aux=this
  
      show ?thesis
        apply (rule bisim.s1.reachable_finite_sim)
        using lih'_finite_reachable apply simp
        apply (clarsimp simp: build_rel_def pidgc_\<alpha>_def)
        apply (case_tac b)
        apply clarsimp
        apply (subst aux)
        apply (rule finite_imageI)
        by simp
    qed
  
    sublocale jsys: transition_system_finite_nodes
      ga_ex "\<lambda> a p. a \<in> ga_en p" "\<lambda> p. p = pid_init_gc"
      apply unfold_locales
      unfolding reachable_alt
      unfolding ga_automaton_def
      apply simp
      unfolding ga_step_eq[abs_def]
      using pid_finite_reachable
      by simp


  end
end

