theory Gen_Scheduler_Refine
imports "../RefPoint/Gen_Scheduler"
begin

  locale Gen_Scheduler' = cs: LTS cstep 
    for cstep :: "'c \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool" +
    fixes en :: "('ls\<times>'gs) \<Rightarrow> 'a \<Rightarrow> bool"
    fixes ex :: "('ls\<times>'gs) \<Rightarrow> 'a \<Rightarrow> ('ls\<times>'gs)"
  begin
    
    definition gstep_succ 
      :: "('c,'ls,'gs)global_config \<Rightarrow> ('c,'ls,'gs)global_config set" 
      where
      "gstep_succ gc \<equiv> do {
        \<comment> \<open> Select process \<close>
        let lcs = global_config.processes gc;
        (lc,lcs') \<leftarrow> {(lc,lcs'). lcs = {#lc#} + lcs'};
        \<comment> \<open> Focus state \<close>
        let gs = global_config.state gc;
        let ls = local_config.state lc;
  
        \<comment> \<open> Select action \<close>
        let cmd = local_config.command lc;
        (a,cmd') \<leftarrow> {(a,cmd'). cstep cmd a cmd'};
  
        case en (ls,gs) a of
          False \<Rightarrow> {} \<comment> \<open> Not enabled \<close>  
        | True \<Rightarrow> {do { \<comment> \<open> Enabled \<close>
            \<comment> \<open> Execute \<close>
            let (ls,gs) = ex (ls,gs) a;
            \<comment> \<open> Unfocus state. \<close>
            \<lparr> 
              global_config.processes = {# 
                \<lparr> local_config.command = cmd', local_config.state = ls\<rparr> 
              #} + lcs',
              global_config.state = gs  
            \<rparr>
          }}
      }"

    abbreviation "gstep \<equiv> rel_of_succ gstep_succ"
 
    text \<open>For the final step function, we apply stutter extension\<close>
    definition "step \<equiv> stutter_extend_edges UNIV gstep"

    lemma gstep_succE[cases set: gstep_succ, case_names succ]: 
      assumes "gc' \<in> gstep_succ gc"
      obtains lc lcs c' a ls' gs'
        where
        "processes gc = {#lc#} + lcs"
        "cstep (command lc) a c'"
        "en (local_config.state lc, global_config.state gc) a"
        "ex (local_config.state lc, global_config.state gc) a = (ls',gs')"
        "gc' = \<lparr>
          global_config.processes 
            = {#\<lparr> local_config.command = c', local_config.state = ls' \<rparr>#} + lcs,
          global_config.state 
            = gs'
        \<rparr>"
      using assms
      unfolding gstep_succ_def
      by (auto
        split: option.splits bool.splits Option.bind_splits prod.splits
        simp: all_conj_distrib
        elim!: neq_Some_bool_cases)

    lemma gstep_succI:
      assumes "processes gc = {#lc#} + lcs"
      assumes "cstep (command lc) a c'"
      assumes "en (local_config.state lc, global_config.state gc) a"
      assumes "ex (local_config.state lc, global_config.state gc) a = (ls',gs')"
      shows "\<lparr>
          global_config.processes 
            = {#\<lparr> local_config.command = c', local_config.state = ls' \<rparr>#} + lcs,
          global_config.state 
            = gs'
        \<rparr> \<in> gstep_succ gc"
      using assms unfolding gstep_succ_def
      by (fastforce)

  end    

  locale Gen_Scheduler'_linit = 
    Gen_Scheduler' cstep en ex
    for cstep :: "'c \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool"
    and en :: "('ls\<times>'gs) \<Rightarrow> 'a \<Rightarrow> bool"
    and ex :: "('ls\<times>'gs) \<Rightarrow> 'a \<Rightarrow> ('ls\<times>'gs)" +
    fixes init :: "('c,'ls,'gs) global_config set"
    fixes label :: "('c,'ls,'gs) global_config \<Rightarrow> 'l"
  begin

    definition system_automaton' :: "(('c,'ls,'gs) global_config, 'l) sa_rec"
      where "system_automaton' \<equiv> \<lparr> g_V = UNIV, g_E = gstep, g_V0 = init, sa_L = label \<rparr>"

    lemma system_automaton'_simps[simp]:
      "g_V system_automaton' = UNIV"
      "g_E system_automaton' = gstep"
      "g_V0 system_automaton' = init"
      "sa_L system_automaton' = label"
      unfolding system_automaton'_def by simp+

    definition system_automaton :: "(('c,'ls,'gs) global_config, 'l) sa_rec"
      where "system_automaton \<equiv> \<lparr> g_V = UNIV, g_E = step, g_V0 = init, sa_L = label \<rparr>"

    lemma system_automaton_simps[simp]:
      "g_V system_automaton = UNIV"
      "g_E system_automaton = step"
      "g_V0 system_automaton = init"
      "sa_L system_automaton = label"
      unfolding system_automaton_def by simp+

    lemma system_automaton_alt_def: "system_automaton = stutter_extend system_automaton'"
      unfolding step_def system_automaton'_def system_automaton_def stutter_extend_def by simp

    sublocale sa': sa system_automaton' by unfold_locales auto
    sublocale sa: sa system_automaton unfolding system_automaton_alt_def by (rule sa'.stutter_extend_sa)

  end

  locale sched_typing = 
    s1: Gen_Scheduler cstep1 en1 ex1 +
    s2: Gen_Scheduler' cstep2 en2 ex2
    for cstep1 :: "'c \<Rightarrow> 'a+'b \<Rightarrow> 'c \<Rightarrow> bool"
    and en1 :: "('ls\<times>'gs) \<Rightarrow> 'a \<rightharpoonup> bool"
    and ex1 :: "('ls\<times>'gs) \<Rightarrow> 'a \<rightharpoonup> ('ls\<times>'gs)"

    and cstep2 :: "'c \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool"
    and en2 :: "('ls\<times>'gs) \<Rightarrow> 'a \<Rightarrow> bool"
    and ex2 :: "('ls\<times>'gs) \<Rightarrow> 'a \<Rightarrow> ('ls\<times>'gs)" 

    +
    fixes wf_local :: "'c \<Rightarrow> 'ls \<Rightarrow> 'gs \<Rightarrow> bool"

    assumes wf_cstep: "wf_local c ls gs 
      \<Longrightarrow> cstep1 c aa c' \<longleftrightarrow> (\<exists>a. aa=Inl a \<and> cstep2 c a c')"
    assumes wf_en: "\<lbrakk>wf_local c ls gs; cstep1 c (Inl a) c'\<rbrakk> 
      \<Longrightarrow> en1 (ls,gs) a = Some (en2 (ls,gs) a)"  
    assumes wf_ex: "\<lbrakk>wf_local c ls gs; cstep1 c (Inl a) c'; en1 (ls,gs) a = Some True\<rbrakk>
      \<Longrightarrow> ex1 (ls,gs) a = Some (ex2 (ls,gs) a)"

    assumes wf_pres_this: "\<lbrakk> 
      wf_local c ls gs; cstep1 c (Inl a) c'; 
      en1 (ls,gs) a = Some True; ex1 (ls,gs) a = Some (ls',gs') \<rbrakk> 
      \<Longrightarrow> wf_local c' ls' gs'"  
    assumes wf_pres_other: "\<lbrakk> 
      wf_local c ls gs; cstep1 c (Inl a) c'; 
      en1 (ls,gs) a = Some True; ex1 (ls,gs) a = Some (ls',gs');
      wf_local co lso gs
    \<rbrakk> 
      \<Longrightarrow> wf_local co lso gs'"  

  begin
    definition wf_gglobal :: "('c,'ls,'gs) global_config \<Rightarrow> bool" where
      "wf_gglobal gc \<equiv> \<forall>lc. lc\<in>#global_config.processes gc
        \<longrightarrow> wf_local 
              (local_config.command lc) 
              (local_config.state lc) 
              (global_config.state gc)"
        
    primrec wf_global where
      "wf_global None = False"
    | "wf_global (Some gc) = wf_gglobal gc"          

    lemma wf_cstep_revI: 
      "\<lbrakk>wf_local c ls gs; cstep2 c a c'\<rbrakk> \<Longrightarrow> cstep1 c (Inl a) c'"
      using wf_cstep by auto

    lemma wf_en_revI: 
      "\<lbrakk>wf_local c ls gs; cstep1 c (Inl a) c'; en2 (ls,gs) a \<rbrakk> \<Longrightarrow> en1 (ls,gs) a = Some True"
      using wf_en by auto

    lemma wf_ex_revI: 
      "\<lbrakk>wf_local c ls gs; cstep1 c (Inl a) c'; en2 (ls,gs) a; ex2 (ls,gs) a = fs' \<rbrakk> 
      \<Longrightarrow> ex1 (ls,gs) a = Some fs'"
      using wf_en wf_ex by auto

    lemma wf_pres_step: "\<lbrakk>wf_global gc; (gc, gc') \<in> s1.step\<rbrakk> \<Longrightarrow> wf_global gc'"
      apply (cases gc, simp_all)
      unfolding s1.step_def s1.gstep_def
      apply (erule stutter_extend_edgesE)
        apply (clarsimp)
        apply (erule s1.gstep_succE)
        apply (auto 
          simp: wf_gglobal_def all_conj_distrib
          simp: wf_cstep
          ) []
        apply (auto 
          simp: wf_gglobal_def all_conj_distrib
          simp: wf_en wf_cstep
          ) []
        apply (auto 
          simp: wf_gglobal_def all_conj_distrib
          simp: wf_en wf_ex wf_cstep
          ) []
        apply (auto 
          simp: wf_gglobal_def all_conj_distrib
          intro: wf_pres_this wf_pres_other
          ) []
        
        apply clarsimp
      done

    lemma wf_gstep_eq: "wf_gglobal gc \<Longrightarrow>
      s1.gstep_succ gc = Some`s2.gstep_succ gc"
      apply safe
        apply (erule s1.gstep_succE, simp_all add: inj_image_mem_iff) []
        apply (auto 
          simp: wf_gglobal_def all_conj_distrib
          simp: wf_en wf_ex wf_cstep
          ) [3]
        apply (clarsimp
          simp: wf_gglobal_def all_conj_distrib
          simp: wf_en wf_ex wf_cstep
          ) []
        apply (auto intro!: s2.gstep_succI)
        apply (erule s2.gstep_succE, 
          clarsimp_all simp: wf_gglobal_def all_conj_distrib) []
        apply (rule s1.gstep_succ_succ, assumption)
        apply (rule wf_cstep_revI, assumption+)
        apply (rule wf_en_revI, assumption+, auto simp: wf_cstep) []
        apply (rule wf_ex_revI, assumption+, auto simp: wf_cstep) []
      done
      
    lemma wf_gstep_revI: 
      "\<lbrakk>wf_gglobal gc; gc'\<in>s2.gstep_succ gc\<rbrakk> 
      \<Longrightarrow> Some gc' \<in> s1.gstep_succ gc"
      by (auto simp: wf_gstep_eq)


    lemma wf_step_eq: "wf_global gco \<Longrightarrow> 
      (gco, gco') \<in> s1.step 
      \<longleftrightarrow> (\<exists>gc gc'. gco=Some gc \<and> gco'=Some gc' \<and> (gc, gc') \<in> s2.step)"
      apply (cases gco, simp_all)
      unfolding s1.step_def s2.step_def s1.gstep_def
      apply safe
      apply (erule stutter_extend_edgesE)
        apply (auto simp: wf_gstep_eq intro!: stutter_extend_edgesI_edge) []

        apply clarsimp
        apply (rule stutter_extend_edgesI_stutter, clarsimp)
        apply (auto dest!: wf_gstep_revI) []

      apply (erule stutter_extend_edgesE)
        apply (auto simp: wf_gstep_eq intro!: stutter_extend_edgesI_edge) []

        apply clarsimp
        apply (rule stutter_extend_edgesI_stutter, clarsimp)
        apply (force simp: wf_gstep_eq) []
      done

    lemma wf_pres_step2: "\<lbrakk> wf_gglobal gc; (gc, gc') \<in> s2.step \<rbrakk> \<Longrightarrow> wf_gglobal gc'"
      using wf_pres_step[of "Some gc" "Some gc'"]
      by (simp add: wf_step_eq)

  end

  locale sched_typing_init = 
    sched_typing cstep1 en1 ex1 cstep2 en2 ex2 wf_local +
    s1: Gen_Scheduler_linit cstep1 en1 ex1 ginit glabel +
    s2: Gen_Scheduler'_linit cstep2 en2 ex2 ginit glabel
    for cstep1 :: "'c \<Rightarrow> 'a+'b \<Rightarrow> 'c \<Rightarrow> bool"
    and en1 :: "('ls\<times>'gs) \<Rightarrow> 'a \<rightharpoonup> bool"
    and ex1 :: "('ls\<times>'gs) \<Rightarrow> 'a \<rightharpoonup> ('ls\<times>'gs)"

    and cstep2 :: "'c \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool"
    and en2 :: "('ls\<times>'gs) \<Rightarrow> 'a \<Rightarrow> bool"
    and ex2 :: "('ls\<times>'gs) \<Rightarrow> 'a \<Rightarrow> ('ls\<times>'gs)" 

    and ginit :: "('c,'ls,'gs) global_config set"
    and glabel :: "('c,'ls,'gs) global_config \<Rightarrow> 'l"
    and wf_local :: "'c \<Rightarrow> 'ls \<Rightarrow> 'gs \<Rightarrow> bool" +
    assumes wf_init: "gc \<in> ginit \<Longrightarrow> wf_gglobal gc"
  begin

    sublocale bisim: lbisimulation "br Some wf_gglobal"
      s2.system_automaton
      s1.system_automaton
      apply unfold_locales
      apply (auto simp: build_rel_def wf_init wf_step_eq wf_pres_step2 simp: s1.init_conv)
      done

    lemma accept_eq: "s2.sa.accept = s1.sa.accept"
      using bisim.accept_bisim .

    lemma is_run_conv: "s1.sa.g.is_run r \<longleftrightarrow> (\<exists>r'. r=Some o r' \<and> s2.sa.g.is_run r')"  
      using bisim.br_run_conv[OF refl] .

  end

end

