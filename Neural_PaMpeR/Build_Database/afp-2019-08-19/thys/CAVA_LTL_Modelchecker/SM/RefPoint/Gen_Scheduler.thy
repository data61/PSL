section \<open>Generic Scheduler\<close>
theory Gen_Scheduler
imports Main
  CAVA_Automata.Stuttering_Extension
  "../Lib/LTS" "../Lib/SOS_Misc_Add"
  "HOL-Library.Multiset"
begin

  lemmas [simp del] = union_mset_add_mset_left union_mset_add_mset_right

  text \<open>
    A generic scheduler, that is parameterized with local LTS and
    enabledness/effects of labels.
\<close>

  record ('c,'ls) local_config =
    command :: 'c
    state :: 'ls

  record ('c,'ls,'gs) global_config =
    processes :: "('c,'ls) local_config multiset"  
    state :: 'gs

  locale Gen_Scheduler = cs: LTS cstep 
    for cstep :: "'c \<Rightarrow> 'a+'b \<Rightarrow> 'c \<Rightarrow> bool" +
    fixes en :: "('ls\<times>'gs) \<Rightarrow> 'a \<rightharpoonup> bool"
    fixes ex :: "('ls\<times>'gs) \<Rightarrow> 'a \<rightharpoonup> ('ls\<times>'gs)"
  begin
    
    definition gstep_succ 
      :: "('c,'ls,'gs)global_config \<Rightarrow> ('c,'ls,'gs)global_config option set" 
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
        
        case a of
          Inl a \<Rightarrow> (
            case en (ls,gs) a of
              None \<Rightarrow> {None} \<comment> \<open> Error \<close>
            | Some False \<Rightarrow> {} \<comment> \<open> Not enabled \<close>
            | Some True \<Rightarrow> {do { \<comment> \<open> Enabled \<close>
                \<comment> \<open> Execute \<close>
                (ls,gs) \<leftarrow> ex (ls,gs) a;
                \<comment> \<open> Unfocus state. \<close>
                Some \<lparr> 
                  global_config.processes = {# 
                    \<lparr> local_config.command = cmd', local_config.state = ls\<rparr> 
                  #} + lcs',
                  global_config.state = gs  
                \<rparr>
              }}
          )
        | Inr _ \<Rightarrow> {None}
      }"
  
    definition gstep
      :: "(('c, 'ls, 'gs) global_config option \<times> ('c, 'ls, 'gs) global_config option) set"
      where "gstep \<equiv> {(Some c, c') |c c'. c' \<in> gstep_succ c}"

    text \<open>For the final step function, we apply stutter extension\<close>
    definition "step \<equiv> stutter_extend_edges UNIV gstep"

    lemma gstep_eq_pred_of_succ: "gstep = rel_of_succ (m2r_succ gstep_succ)"
      unfolding gstep_def by auto
  
    lemma gstep_eq_conv: "(c, c') \<in> gstep \<longleftrightarrow> (\<exists>cc. c=Some cc \<and> c'\<in>gstep_succ cc)"
      unfolding gstep_def by auto

    lemma [simp]: "(\<forall>x. a\<noteq>Inr x) \<longleftrightarrow> (\<exists>y. a=Inl y)"
      by (cases a) auto

    lemma [simp]: "\<not>(All Not)" by blast 

    lemma ne_Some_b_conv:
      "(a\<noteq>Some b) \<longleftrightarrow> (a=Some (\<not>b) \<or> a=None)"
      by (cases a) auto


    lemma gstep_succE[cases set: gstep_succ, case_names fail_cfg fail_en fail_ex succ]: 
      assumes "gc' \<in> gstep_succ gc"
      obtains 
        lc lcs c' b 
        where
        "processes gc = {#lc#} + lcs"
        "cstep (command lc) (Inr b) c'"
        "gc'=None"
      | lc lcs c' a 
        where
        "processes gc = {#lc#} + lcs"
        "cstep (command lc) (Inl a) c'"
        "en (local_config.state lc, global_config.state gc) a = None"
        "gc' = None"
      | lc lcs c' a 
        where
        "processes gc = {#lc#} + lcs"
        "cstep (command lc) (Inl a) c'"
        "en (local_config.state lc, global_config.state gc) a = Some True"
        "ex (local_config.state lc, global_config.state gc) a = None"
        "gc' = None"
      | lc lcs c' a ls' gs'
        where
        "processes gc = {#lc#} + lcs"
        "cstep (command lc) (Inl a) c'"
        "en (local_config.state lc, global_config.state gc) a = Some True"
        "ex (local_config.state lc, global_config.state gc) a = Some (ls',gs')"
        "gc' = Some \<lparr>
          global_config.processes 
            = {#\<lparr> local_config.command = c', local_config.state = ls' \<rparr>#} + lcs,
          global_config.state 
            = gs'
        \<rparr>"
      using assms
      unfolding gstep_succ_def
      apply (auto
        split: option.splits bool.splits Option.bind_splits sum.splits
        simp: all_conj_distrib 
        elim!: neq_Some_bool_cases)
      apply (case_tac aa)
      apply (auto simp: ne_Some_b_conv)
      done

    lemma gstep_succ_fail_cmd:
      assumes "processes gc = {#lc#} + lcs"
      assumes "cstep (command lc) (Inr b) c'"
      shows "None \<in> gstep_succ gc"
      using assms unfolding gstep_succ_def
      by (fastforce)


    lemma gstep_succ_fail_en:
      assumes "processes gc = {#lc#} + lcs"
      assumes "cstep (command lc) (Inl a) c'"
      assumes "en (local_config.state lc, global_config.state gc) a = None"
      shows "None \<in> gstep_succ gc"
      using assms unfolding gstep_succ_def
      by (fastforce)
      
    lemma gstep_succ_fail_ex:
      assumes "processes gc = {#lc#} + lcs"
      assumes "cstep (command lc) (Inl a) c'"
      assumes "en (local_config.state lc, global_config.state gc) a = Some True"
      assumes "ex (local_config.state lc, global_config.state gc) a = None"
      shows "None \<in> gstep_succ gc"
      using assms unfolding gstep_succ_def
      by (fastforce)

    lemma gstep_succ_succ:
      assumes "processes gc = {#lc#} + lcs"
      assumes "cstep (command lc) (Inl a) c'"
      assumes "en (local_config.state lc, global_config.state gc) a = Some True"
      assumes "ex (local_config.state lc, global_config.state gc) a = Some (ls',gs')"
      shows "Some \<lparr>
          global_config.processes 
            = {#\<lparr> local_config.command = c', local_config.state = ls' \<rparr>#} + lcs,
          global_config.state 
            = gs'
        \<rparr> \<in> gstep_succ gc"
      using assms unfolding gstep_succ_def
      by (fastforce)

  end    

  locale Gen_Scheduler_linit = 
    Gen_Scheduler cstep en ex
    for cstep :: "'c \<Rightarrow> 'a+'b \<Rightarrow> 'c \<Rightarrow> bool"
    and en :: "('ls\<times>'gs) \<Rightarrow> 'a \<rightharpoonup> bool"
    and ex :: "('ls\<times>'gs) \<Rightarrow> 'a \<rightharpoonup> ('ls\<times>'gs)" +
    fixes ginit :: "('c,'ls,'gs) global_config set"
    fixes glabel :: "('c,'ls,'gs) global_config \<Rightarrow> 'l"
  begin

    definition init where "init \<equiv> Some ` ginit"
    fun label where "label None = undefined" | "label (Some gc) = glabel gc"

    lemma init_conv: "gco \<in> init \<longleftrightarrow> (\<exists>gc. gco=Some gc \<and> gc \<in> ginit)"
      unfolding init_def by auto

    definition system_automaton' :: "(('c,'ls,'gs) global_config option, 'l) sa_rec"
      where "system_automaton' \<equiv> \<lparr> g_V = UNIV, g_E = gstep, g_V0 = init, sa_L = label \<rparr>"

    lemma system_automaton'_simps[simp]:
      "g_V system_automaton' = UNIV"
      "g_E system_automaton' = gstep"
      "g_V0 system_automaton' = init"
      "sa_L system_automaton' = label"
      unfolding system_automaton'_def by simp+

    definition system_automaton :: "(('c,'ls,'gs) global_config option, 'l) sa_rec"
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

end
