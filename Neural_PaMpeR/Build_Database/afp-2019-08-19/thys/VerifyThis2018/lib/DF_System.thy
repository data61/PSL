chapter \<open>Deadlock Free Transition Systems\<close>
theory DF_System
imports Main
begin
  text \<open>
    Theories to describe deadlock free transitions system and 
    simulations between them.
  
    We added these locales after the competition, in order to get a cleaner
    solution for Challenge~3. This theory provides not much more than what is 
    needed for solving the challenge.
  \<close>

  section \<open>Transition System\<close>
  locale system =
    fixes s\<^sub>0 :: 's
      and lstep :: "'l \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
  begin
    abbreviation "step s s' \<equiv> \<exists>l. lstep l s s'"
    definition "reachable \<equiv> (step\<^sup>*\<^sup>*) s\<^sub>0"

    lemma reachable0[simp]: "reachable s\<^sub>0"
      unfolding reachable_def by auto
    
    
    definition "is_invar I \<equiv> I s\<^sub>0 \<and> (\<forall>s s'. reachable s \<and> I s \<and> step s s' \<longrightarrow> I s')"
    
    lemma is_invarI[intro?]: 
      "\<lbrakk> I s\<^sub>0; \<And>s s'. \<lbrakk> reachable s; I s; step s s'\<rbrakk> \<Longrightarrow> I s' \<rbrakk> \<Longrightarrow> is_invar I"
      by (auto simp: is_invar_def)
    
    lemma invar_reachable: "is_invar I \<Longrightarrow> reachable s \<Longrightarrow> I s"  
      unfolding reachable_def
      apply (rotate_tac) (** Seriously? *)
      apply (induction rule: rtranclp_induct)
      unfolding is_invar_def reachable_def by auto

    definition "can_step l s \<equiv> \<exists>s'. lstep l s s'"
            
  end  

  section \<open>Deadlock Free Transition System\<close>
  locale df_system = system +
    assumes no_deadlock: "reachable s \<Longrightarrow> \<exists>s'. step s s'"
  begin
  
    paragraph \<open>Runs\<close>
    definition "is_lrun l s \<equiv> s 0 = s\<^sub>0 \<and> (\<forall>i. lstep (l i) (s i) (s (Suc i)))"
    definition "is_run s \<equiv> \<exists>l. is_lrun l s"
      
    paragraph \<open>Weak Fairness\<close>
    definition "is_lfair ls ss \<equiv> \<forall>l i. \<exists>j\<ge>i. \<not>can_step l (ss j) \<or> ls j = l"
    definition "is_fair_run s \<equiv> \<exists>l. is_lrun l s \<and> is_lfair l s"
      
    text \<open>Definitions of runs. Used e.g. to clarify TCB of lemmas over systems.\<close>
    lemmas run_definitions = is_lrun_def is_run_def is_lfair_def is_fair_run_def  
      
    lemma is_run_alt: "is_run s \<longleftrightarrow> s 0 = s\<^sub>0 \<and> (\<forall>i. step (s i) (s (Suc i)))"
      unfolding is_run_def is_lrun_def by metis 
      
    definition "rstep l s i \<equiv> lstep l (s i) (s (Suc i))"
    
    lemma fair_run_is_run: "is_fair_run s \<Longrightarrow> is_run s"
      using is_fair_run_def is_run_def by blast

    text \<open>Weaker fairness criterion, used internally in proofs only.\<close>
    definition "is_fair' s \<equiv> \<forall>l i. \<exists>j\<ge>i. \<not>can_step l (s j) \<or> rstep l s j"

    lemma fair_run_is_fair': "is_fair_run s \<Longrightarrow> is_fair' s"
      unfolding is_fair_run_def is_run_def is_lrun_def is_fair'_def is_lfair_def rstep_def
      by metis
      
  end

  subsection \<open>Run\<close>    
  locale run = df_system +
    fixes s
    assumes RUN: "is_run s"
  begin  
    lemma run0[simp]: "s 0 = s\<^sub>0" using RUN
      by (auto simp: is_run_alt)
    
    lemma run_reachable[simp]: "reachable (s i)"
      apply (induction i)
      using RUN
      apply simp_all
      unfolding is_run_alt reachable_def
      by (auto simp: rtranclp.rtrancl_into_rtrancl)
          
    lemma run_invar: "is_invar I \<Longrightarrow> I (s i)"
      using run_reachable invar_reachable by blast
      
    lemma stepE: obtains l where "lstep l (s i) (s (Suc i))"  
      using RUN by (auto simp: is_run_alt)
      
  end  
      
  subsection \<open>Fair Run\<close>    
  locale fair_run = df_system +
    fixes s
    assumes FAIR: "is_fair_run s"
  begin
    sublocale run
      apply unfold_locales
      using FAIR fair_run_is_run by blast
  
    definition "next_step_of l i \<equiv> LEAST j. j\<ge>i \<and> (\<not>can_step l (s j) \<or> rstep l s j)"
      
    lemma next_step_step: 
      fixes i l
      defines "j\<equiv>next_step_of l i" 
      shows "j \<ge> i \<and> (\<not>can_step l (s j) \<or> rstep l s j)"
      using fair_run_is_fair'[OF FAIR] unfolding is_fair'_def
      unfolding next_step_of_def j_def
      apply -
      using LeastI_ex[where P="\<lambda>j. j\<ge>i \<and> (\<not>can_step l (s j) \<or> rstep l s j)"]
      by (auto)

    definition "dist_step l i \<equiv> next_step_of l i - i"  
    
    lemma nso_nostep: "\<lbrakk> \<not>rstep l s i; can_step l (s i)\<rbrakk> 
      \<Longrightarrow> next_step_of l (Suc i) = next_step_of l i"
      unfolding next_step_of_def
      by (metis (full_types) Suc_leD dual_order.antisym not_less_eq_eq)
    
    lemma rstep_cases:
      assumes "can_step l (s i)" 
      obtains
        (other) l' where "l\<noteq>l'" "\<not>rstep l s i" "rstep l' s i" "dist_step l (Suc i) < dist_step l i"
      | (this) "rstep l s i"  
      apply (cases "rstep l s i"; clarsimp)
      apply (drule nso_nostep)
      unfolding dist_step_def using assms
      apply blast
      by (metis RUN diff_commute diff_diff_cancel is_run_alt less_Suc_eq next_step_step rstep_def that(2) zero_less_diff)
    
  end


  section \<open>Simulation\<close>  
  locale simulation =
    A: df_system as\<^sub>0 alstep + C: df_system cs\<^sub>0 clstep 
      for as\<^sub>0 :: 'a 
      and alstep :: "'l \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" 
      and cs\<^sub>0 :: 'c 
      and clstep :: "'l \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> bool"
  + fixes R
    assumes xfer_reachable_aux: "C.reachable c \<Longrightarrow> \<exists>a. R a c \<and> A.reachable a" (* TODO: Redundant, can be derived from xfer_run. *)
    assumes xfer_run_aux: "C.is_run cs \<Longrightarrow> \<exists>as. (\<forall>i. R (as i) (cs i)) \<and> A.is_run as"
    assumes xfer_fair_run_aux: "C.is_fair_run cs \<Longrightarrow> \<exists>as. (\<forall>i. R (as i) (cs i)) \<and> A.is_fair_run as"
  begin
    lemma xfer_reachable: 
      assumes "C.reachable cs"
      obtains as where "R as cs" "A.reachable as"
      using assms xfer_reachable_aux by auto
  
    lemma xfer_run:
      assumes CRUN: "C.is_run cs"
      obtains as where "A.is_run as" "\<forall>i. R (as i) (cs i)"
      using xfer_run_aux assms by blast
    
    lemma xfer_fair_run:
      assumes FAIR: "C.is_fair_run cs"
      obtains as where "A.is_fair_run as" "\<forall>i. R (as i) (cs i)"
      using xfer_fair_run_aux assms by blast
      
  end
  
  lemma sim_trans:
    assumes "simulation as\<^sub>0 alstep bs\<^sub>0 blstep R\<^sub>1"
    assumes "simulation bs\<^sub>0 blstep cs\<^sub>0 clstep R\<^sub>2"
    shows "simulation as\<^sub>0 alstep cs\<^sub>0 clstep (R\<^sub>1 OO R\<^sub>2)"
    using assms
    unfolding simulation_def simulation_axioms_def
    by (auto simp: OO_def; metis)
  
  (* Locale to introduce simulation by local argument *)  
  locale simulationI =
    A: df_system as\<^sub>0 alstep + C: system cs\<^sub>0 clstep 
      for as\<^sub>0 :: 'a 
      and alstep :: "'l \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" 
      and cs\<^sub>0 :: 'c 
      and clstep :: "'l \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> bool"
  + fixes R
    assumes sim0: "R as\<^sub>0 cs\<^sub>0"
    assumes sims: "\<lbrakk>A.reachable as; C.reachable cs; R as cs; clstep l cs cs'\<rbrakk> 
      \<Longrightarrow> \<exists>as'. R as' cs' \<and> alstep l as as'"
    assumes simb: "\<lbrakk>A.reachable as; C.reachable cs; R as cs; A.can_step l as\<rbrakk> \<Longrightarrow> C.can_step l cs"
  begin

    lemma simb': "\<lbrakk>A.reachable as; C.reachable cs; R as cs\<rbrakk> \<Longrightarrow> C.can_step l cs \<longleftrightarrow> A.can_step l as"
      using simb sims 
      by (fastforce simp: A.can_step_def C.can_step_def)

    lemma xfer_reachable_aux2: 
      assumes "C.reachable cs"
      obtains as where "R as cs" "A.reachable as"
    proof -
      from assms have "\<exists>as. R as cs \<and> A.reachable as"
        unfolding C.reachable_def
        apply (induction)
        subgoal using sim0 A.reachable0 by blast
        apply clarify
        subgoal for cs cs' l as
          using sims[of as cs l cs']
          by (auto simp: C.reachable_def A.reachable_def intro: rtranclp.rtrancl_into_rtrancl)
        done
      with that show ?thesis by blast
    qed  

    sublocale C: df_system cs\<^sub>0 clstep
      apply unfold_locales
      by (metis A.no_deadlock xfer_reachable_aux2 simb system.can_step_def)
    
    context begin
      private primrec arun where
        "arun cl cs 0 = as\<^sub>0"
      | "arun cl cs (Suc i) = (SOME as. C.rstep (cl i) cs i \<and> alstep (cl i) (arun cl cs i) as  \<and> R as (cs (Suc i)))"
    
      lemma xfer_lrun_aux2:
        assumes CRUN: "C.is_lrun cl cs"
        obtains as where "A.is_lrun cl as" "\<forall>i. R (as i) (cs i)"
      proof -
        from CRUN have "C.is_run cs" by (auto simp: C.is_run_def)
      
        interpret C: run cs\<^sub>0 clstep cs
          by unfold_locales fact
      
      
        have X1: "alstep (cl i) (arun cl cs i) (arun cl cs (Suc i)) \<and> A.reachable (arun cl cs i) \<and> R (arun cl cs (Suc i)) (cs (Suc i))" for i
        proof (induction i rule: nat_less_induct)
          case (1 i)
          
          have CR: "C.reachable (cs i)" using C.run_reachable .
          have CS: "clstep (cl i) (cs i) (cs (Suc i))"
            using CRUN by (auto simp: C.is_lrun_def)
          
          have AX: "A.reachable (arun cl cs i) \<and> R (arun cl cs i) (cs i)"
          proof (cases i)
            case 0
            then show ?thesis by (auto simp: CRUN sim0)
          next
            case [simp]: (Suc i')
            
            from "1.IH"[THEN spec, of i'] show ?thesis
              by (auto simp del: arun.simps simp: A.reachable_def 
                intro: rtranclp.rtrancl_into_rtrancl)
          qed
            
          from sims[OF _ CR _ CS, of "arun cl cs i"] AX obtain asi where
            "R asi (cs (Suc i))" "alstep (cl i) (arun cl cs i) asi" by auto
          
          then show ?case
            apply simp
            apply (rule someI2)
            using CS by (auto simp: C.rstep_def AX)
        qed        
        hence "R (arun cl cs i) (cs i)" for i
          apply (cases i) using sim0
          by (auto simp: CRUN)
        with X1 show ?thesis
          apply (rule_tac that[of "arun cl cs"])
          by (auto simp: A.is_lrun_def)
      qed    
    end
      
    lemma xfer_run_aux2:
      assumes CRUN: "C.is_run cs"
      obtains as where "A.is_run as" "\<forall>i. R (as i) (cs i)"
      by (meson A.is_run_def C.is_run_def assms xfer_lrun_aux2)
    
    lemma xfer_fair_run_aux2:
      assumes FAIR: "C.is_fair_run cs"
      obtains as where "A.is_fair_run as" "\<forall>i. R (as i) (cs i)"
    proof -
      from FAIR obtain cl where 
        CLRUN: "C.is_lrun cl cs" and 
        CFAIR: "C.is_lfair cl cs"
        by (auto simp: C.is_fair_run_def)
    
      from xfer_lrun_aux2[OF CLRUN] obtain as where 
        ALRUN: "A.is_lrun cl as" and SIM: "\<forall>i. R (as i) (cs i)" .

      interpret A: run as\<^sub>0 alstep as
              + C: run cs\<^sub>0 clstep cs
        apply (unfold_locales)        
        using ALRUN CLRUN
        by (auto simp: A.is_run_def C.is_run_def)
        
                
      have "A.is_lfair cl as"
        unfolding A.is_lfair_def 
        by (metis A.run_reachable C.is_lfair_def C.run_reachable CFAIR SIM simb')
      with ALRUN SIM that show ?thesis unfolding A.is_fair_run_def by blast
    qed    
    
    sublocale simulation
      apply unfold_locales
      using xfer_reachable_aux2 apply blast
      using xfer_run_aux2 apply blast
      using xfer_fair_run_aux2 apply blast
      done
    
  end
  
end

