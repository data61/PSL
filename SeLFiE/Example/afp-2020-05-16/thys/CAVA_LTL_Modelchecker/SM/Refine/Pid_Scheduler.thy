theory Pid_Scheduler
imports Gen_Scheduler_Refine Partial_Order_Reduction.Transition_System_Extensions
begin

  lemma system_complete_language_eq_lsystem_accept:
    fixes ex en init int
    defines "S \<equiv> \<lparr> g_V = UNIV, g_E = rel_of_enex (en, ex), g_V0 = {init}, sa_L = int \<rparr>"
    assumes "sa S"
    shows "snth ` transition_system_complete.language ex (\<lambda> a p. a \<in> en p) (\<lambda> p. p = init) int = {w. sa.accept S w}"
  proof -
    interpret jsys?: transition_system_complete ex "\<lambda> a p. a \<in> en p" "\<lambda> p. p = init" int by this
    interpret psys?: sa S by fact
    show ?thesis
    unfolding jsys.language_def
    unfolding psys.accept_def
    proof safe
      fix p w
      assume 1: "run w init"
      show "\<exists> r. is_run r \<and> snth (smap int (init ## trace w init)) = L \<circ> r"
      unfolding is_run_def ipath_def
      unfolding S_def graph_rec.simps sa_rec.simps
      unfolding rel_of_enex_def Let_def prod.case
      proof (intro allI exI conjI)
        fix i
        show "(init ## trace w init) !! 0 \<in> {init}" by simp
        show "snth (smap int (init ## trace w init)) = int \<circ> snth (init ## trace w init)"
          by (metis (full_types) fun_comp_eq_conv smap_alt)
        have 10: "w = stake i w @- [w !! i] @- sdrop (Suc i) w" using id_stake_snth_sdrop by auto
        have 20: "run (stake i w @- [w !! i] @- sdrop (Suc i) w) init" using 1 10 by simp
        have 1: "w !! i \<in> en (target (stake i w) init)" using 20 by auto
        have 2: "ex (w !! i) (target (stake i w) init) = target (stake (Suc i) w) init"
          using 20 unfolding stake_Suc by auto
        show "((init ## trace w init) !! i, (init ## trace w init) !! Suc i) \<in>
          {(s, ex a s) |s a. a \<in> en s}" using 1 2 by force
      qed
    next
      fix r
      assume 1: "is_run r"
      obtain w where 2: "r 0 = init" "\<And> i. w i \<in> en (r i)" "\<And> i. r (Suc i) = ex (w i) (r i)"
        using 1
        unfolding is_run_def ipath_def
        unfolding S_def graph_rec.simps
        unfolding rel_of_enex_def Let_def prod.case
        by simp metis
      have 3: "L \<circ> r = snth (smap int (smap r nats))" unfolding assms(1) by auto
      have 4: "(init ## trace (smap w nats) init) !! i = smap r nats !! i" for i
        using 2 by (induct i) (auto)
      have 5: "smap r nats = init ## trace (smap w nats) init" using eqI_snth 4 by metis
      have 6: "target (stake k (smap w nats)) init = smap r nats !! k" for k
        unfolding sscan_scons_snth 5 by rule
      have 7: "run (smap w nats) init" using 2(2) 6 by (auto intro: snth_run)
      show "L \<circ> r \<in> (!!) ` {smap int (p ## trace w p) |p w. p = init \<and> run w p}"
        unfolding 3 using 5 7 by force
    qed
  qed

  (* TODO: Move *)  
  lemma prod_splitE:
    assumes "\<forall>a b. p=(a,b) \<longrightarrow> P a b"
    obtains a b where "p=(a,b)" "P a b"
    using assms
    by (cases p) auto

  lemma sngp_sym_conv: "(\<lambda>p. p=x) = (=) x" by auto  


  lemma in_multiset_of_conv_nth: "x \<in># mset l \<longleftrightarrow> (\<exists>i<length l. x = l!i)"
    by (metis in_multiset_in_set in_set_conv_nth)
    
  lemma multiset_of_em_conv_nth: "mset l = {#x#} + m' 
    \<longleftrightarrow> (\<exists>i<length l. x = l!i \<and> m' = mset l - {#x#})"
    by (metis add_diff_cancel_left' in_multiset_of_conv_nth 
      insert_DiffM multi_member_this)

  
  type_synonym pid = nat
  record ('c,'ls,'gs) pid_global_config =
    processes :: "('c,'ls) local_config list"  
    state :: 'gs

  definition pidgc_\<alpha> 
    :: "('c,'ls,'gs) pid_global_config \<Rightarrow> ('c,'ls,'gs) global_config" where
    "pidgc_\<alpha> pgc \<equiv> \<lparr>     
      global_config.processes = mset (pid_global_config.processes pgc),
      global_config.state = pid_global_config.state pgc
    \<rparr>"

  abbreviation pid_valid :: "('c,'ls,'gs) pid_global_config \<Rightarrow> pid \<Rightarrow> bool" 
    where
    "pid_valid gc pid \<equiv> pid < length (pid_global_config.processes gc)"
    
  abbreviation "lc_of_pid gc pid 
    \<equiv> pid_global_config.processes gc ! pid"
  
  abbreviation "cmd_of_pid gc pid 
    \<equiv> local_config.command (lc_of_pid gc pid)"
    
  abbreviation "ls_of_pid gc pid 
    \<equiv> local_config.state (lc_of_pid gc pid)"


  context Gen_Scheduler'
  begin

    definition pid_gstep_succ 
      :: "('c,'ls,'gs) pid_global_config \<Rightarrow> ('c,'ls,'gs) pid_global_config set" 
      where
      "pid_gstep_succ gc \<equiv> do {
        \<comment> \<open> Select process \<close>
        let lcs = pid_global_config.processes gc;
        pid \<leftarrow> {0..<length lcs};
        let lc = lcs!pid;
        \<comment> \<open> Focus state \<close>
        let gs = pid_global_config.state gc;
        let ls = local_config.state lc;
  
        \<comment> \<open> Select action \<close>
        let cmd = local_config.command lc;
        (a,cmd') \<leftarrow> {(a,cmd'). cstep cmd a cmd'};
  
        if en (ls,gs) a then {do { 
          \<comment> \<open> Execute \<close>
          let (ls,gs) = ex (ls,gs) a;
          \<comment> \<open> Unfocus state. \<close>
          let lc = \<lparr> local_config.command = cmd', local_config.state = ls\<rparr>;
          \<lparr> 
            pid_global_config.processes = lcs[pid:=lc],
            pid_global_config.state = gs  
          \<rparr>
        }}
      else {}
    }"

    lemma pid_gstep_succE:
      assumes "gc' \<in> pid_gstep_succ gc"
      obtains pid a c' ls' gs' where
        "pid_valid gc pid"
        "cstep (cmd_of_pid gc pid) a c'"
        "en (ls_of_pid gc pid, pid_global_config.state gc) a"
        "ex (ls_of_pid gc pid, pid_global_config.state gc) a = (ls',gs')"
        "gc' = \<lparr> 
          pid_global_config.processes = (pid_global_config.processes gc)
            [pid := 
              \<lparr> local_config.command = c', local_config.state = ls'\<rparr>
            ],
          pid_global_config.state = gs'\<rparr>"
      using assms
      unfolding pid_gstep_succ_def
      by (auto 
        split: if_split_asm prod.splits 
        elim!: prod_splitE
        simp: all_conj_distrib)

  lemma pid_gstep_succI:
    assumes
      "pid_valid gc pid"
      "cstep (cmd_of_pid gc pid) a c'"
      "en (ls_of_pid gc pid, pid_global_config.state gc) a"
      "ex (ls_of_pid gc pid, pid_global_config.state gc) a = (ls',gs')"
    shows "
      \<lparr> 
        pid_global_config.processes = (pid_global_config.processes gc)
          [pid := 
            \<lparr> local_config.command = c', local_config.state = ls'\<rparr>
          ],
        pid_global_config.state = gs'
      \<rparr> \<in> pid_gstep_succ gc"
    using assms
    unfolding pid_gstep_succ_def
    by fastforce

  lemma pid_gc_state_eq: 
    "pid_global_config.state pgc = global_config.state (pidgc_\<alpha> pgc)"
    unfolding pidgc_\<alpha>_def by auto  
    
  lemma pid_gc_proc_eq:
    assumes "pid_valid gc pid"  
    shows "
      global_config.processes (pidgc_\<alpha> gc) 
      = {#lc_of_pid gc pid#} 
      + (global_config.processes (pidgc_\<alpha> gc) - {#lc_of_pid gc pid#})"
    using assms
    by (auto simp: pidgc_\<alpha>_def multiset_of_em_conv_nth)


  lemma pid_gstep_correct: 
    "gstep_succ (pidgc_\<alpha> pgc) = pidgc_\<alpha>`pid_gstep_succ pgc"
    apply safe
    apply (erule gstep_succE)
    apply (clarsimp simp: pidgc_\<alpha>_def multiset_of_em_conv_nth)
    apply (frule (3) pid_gstep_succI)
    apply (erule image_eqI[rotated])
    apply (auto simp: pidgc_\<alpha>_def mset_update add_ac union_mset_add_mset_right) []

    apply (erule pid_gstep_succE)
    apply (clarsimp simp: pidgc_\<alpha>_def mset_update)
    apply (simp add: pid_gc_state_eq)
    apply (frule (2) gstep_succI[rotated])
    apply (rule pid_gc_proc_eq, assumption)
    apply (auto simp: add_ac pidgc_\<alpha>_def union_mset_add_mset_left) []
    done

  abbreviation "pid_gstep \<equiv> rel_of_succ pid_gstep_succ"
  definition "pid_step \<equiv> stutter_extend_edges UNIV pid_gstep"

end

locale Pid_Gen_Scheduler_linit = 
  Gen_Scheduler'_linit cstep en ex init label
  for cstep :: "'c \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool"
  and en :: "('ls\<times>'gs) \<Rightarrow> 'a \<Rightarrow> bool"
  and ex :: "('ls\<times>'gs) \<Rightarrow> 'a \<Rightarrow> ('ls\<times>'gs)"
  and init :: "('c,'ls,'gs) global_config set"
  and label :: "('c,'ls,'gs) global_config \<Rightarrow> 'l" +
  fixes pid_init :: "('c,'ls,'gs) pid_global_config"
  and pid_label :: "('c,'ls,'gs) pid_global_config \<Rightarrow> 'l"
  assumes pid_init_eq: "gc \<in> init \<longleftrightarrow> (gc=pidgc_\<alpha> pid_init)"
  assumes pid_label_eq: "label (pidgc_\<alpha> pgc) = pid_label pgc"
begin

  definition pid_system_automaton' :: "(('c,'ls,'gs) pid_global_config, 'l) sa_rec"
    where "pid_system_automaton' \<equiv>
      \<lparr> g_V = UNIV, g_E = pid_gstep, g_V0 = {pid_init}, sa_L = pid_label \<rparr>"

  lemma pid_system_automaton'_simps[simp]:
    "g_V pid_system_automaton' = UNIV"
    "g_E pid_system_automaton' = pid_gstep"
    "g_V0 pid_system_automaton' = {pid_init}"
    "sa_L pid_system_automaton' = pid_label"
    unfolding pid_system_automaton'_def by auto

  definition pid_system_automaton :: "(('c,'ls,'gs) pid_global_config, 'l) sa_rec"
    where "pid_system_automaton \<equiv>
      \<lparr> g_V = UNIV, g_E = pid_step, g_V0 = {pid_init}, sa_L = pid_label \<rparr>"

  lemma pid_system_automaton_simps[simp]:
    "g_V pid_system_automaton = UNIV"
    "g_E pid_system_automaton = pid_step"
    "g_V0 pid_system_automaton = {pid_init}"
    "sa_L pid_system_automaton = pid_label"
    unfolding pid_system_automaton_def by auto

  lemma pid_system_automaton_alt_def: "pid_system_automaton = stutter_extend pid_system_automaton'"
    unfolding pid_step_def pid_system_automaton'_def pid_system_automaton_def stutter_extend_def
    by simp

  sublocale pid': sa pid_system_automaton' by unfold_locales auto
  sublocale pid: sa pid_system_automaton
    unfolding pid_system_automaton_alt_def using pid'.stutter_extend_sa by this

  sublocale bisim: lbisimulation "br pidgc_\<alpha> (\<lambda>_. True)" pid_system_automaton system_automaton
  proof -
    interpret bisim: lbisimulation "br pidgc_\<alpha> (\<lambda>_. True)" pid_system_automaton' system_automaton'
      apply unfold_locales
      apply (auto simp: build_rel_def pid_init_eq pid_gstep_correct pid_label_eq)
      done
    interpret bisim: lbisimulation "br pidgc_\<alpha> (\<lambda>_. True)" pid_system_automaton system_automaton
      unfolding system_automaton_alt_def pid_system_automaton_alt_def
      using bisim.lstutter_extend by this
    show "lbisimulation (br pidgc_\<alpha> (\<lambda> _. True)) pid_system_automaton system_automaton"
      by unfold_locales
  qed

  lemma pid_accept_eq: "pid.accept = sa.accept" by (rule bisim.accept_bisim)

  lemma pid_run_conv: "sa.g.is_run r \<longleftrightarrow> (\<exists>r'. r=pidgc_\<alpha> o r' \<and> pid.g.is_run r')"
    by (rule bisim.br_run_conv[OF refl])   

  lemma pid_run_sim: "pid.g.is_run r \<Longrightarrow> sa.g.is_run (pidgc_\<alpha> o r)"
    by (rule bisim.s1.br_run_sim[OF refl])

section "Global Actions"

text \<open>
  A global action consists of a PID and a control flow graph edge
\<close>
type_synonym (in -) ('c,'a) global_action = "pid \<times> 'c \<times> 'a \<times> 'c"


abbreviation (in -) "fs_of_pid gc pid \<equiv> (ls_of_pid gc pid,pid_global_config.state gc)"

  definition ga_gen 
    :: "('c,'ls,'gs) pid_global_config \<Rightarrow> ('c,'a) global_action set"
  where
    "ga_gen gc \<equiv> { (pid,c,a,c') .
      cstep c a c' 
    \<and> pid_valid gc pid 
    \<and> c=cmd_of_pid gc pid
    \<and> en (fs_of_pid gc pid) a }"

  definition ga_gex
    :: "('c,'a) global_action \<Rightarrow> ('c,'ls,'gs) pid_global_config \<Rightarrow> ('c,'ls,'gs) pid_global_config"
  where
    "ga_gex ga gc \<equiv> let 
      (pid,c,a,c') = ga;
      fs = fs_of_pid gc pid;
      (ls',gs') = ex fs a;
      gc' = \<lparr> 
          pid_global_config.processes = (pid_global_config.processes gc)
            [pid := 
              \<lparr> local_config.command = c', local_config.state = ls'\<rparr>
            ],
          pid_global_config.state = gs'\<rparr>
    in
      gc'"

  definition "ga_gstep \<equiv> rel_of_enex (ga_gen,ga_gex)"
  definition "ga_en \<equiv> stutter_extend_en ga_gen"
  definition "ga_ex \<equiv> stutter_extend_ex ga_gex"
  definition "ga_step \<equiv> stutter_extend_edges UNIV ga_gstep"
  lemma ga_step_alt: "ga_step = rel_of_enex (ga_en,ga_ex)"
    unfolding ga_step_def ga_gstep_def ga_en_def ga_ex_def
    by (auto simp: stutter_extend_pred_of_enex_conv)

  lemma some_ga_en_eq: 
    "Some a \<in> ga_en gc \<longleftrightarrow> a \<in> ga_gen gc"
    by (auto simp: ga_en_def)
  lemma some_ga_ex_eq: 
    "ga_ex (Some a) gc = ga_gex a gc"
    "ga_ex \<circ> Some = ga_gex"
    by (auto simp: ga_ex_def intro!: ext)
  lemma none_ga_en_eq: "None \<in> ga_en gc \<longleftrightarrow> ga_gen gc = {}"
    by (auto simp: ga_en_def stutter_extend_en_def)
  lemma ga_ex_none[simp]: "ga_ex None = id"   
    by (auto simp: ga_ex_def)

  lemma ga_gstep_eq: "ga_gstep = pid_gstep"
    apply safe
    apply (auto 
      simp: ga_gstep_def ga_gen_def ga_gex_def 
      split: prod.splits elim!: prod_splitE
      intro: pid_gstep_succI) []
     
    apply (fastforce 
      simp: pred_of_succ_def ga_gstep_def ga_gen_def ga_gex_def
      split: prod.splits
      elim!: pid_gstep_succE)
    done

  lemma ga_step_eq: "ga_step = pid_step" 
    unfolding ga_step_def pid_step_def ga_gstep_eq by rule

  definition ga_automaton :: "(('c,'ls,'gs) pid_global_config, 'l) sa_rec"
    where "ga_automaton \<equiv> \<lparr> g_V = UNIV, g_E = ga_step, g_V0 = {pid_init}, sa_L = pid_label \<rparr>"

  lemma ga_automaton_simps[simp]:
    "g_V ga_automaton = UNIV"
    "g_E ga_automaton = ga_step"
    "g_V0 ga_automaton = {pid_init}"
    "sa_L ga_automaton = pid_label"
    unfolding ga_automaton_def by simp+

  lemma ga_pid_system_automaton: "ga_automaton = pid_system_automaton"
    unfolding ga_automaton_def pid_system_automaton_def ga_step_eq by rule

  sublocale jsys: transition_system ga_ex "\<lambda> a p. a \<in> ga_en p" .
  sublocale ga: sa ga_automaton unfolding ga_pid_system_automaton by unfold_locales

  sublocale ga_bisim: lbisimulation Id ga_automaton pid_system_automaton
    unfolding ga_pid_system_automaton by auto

  lemma ga_accept_eq: "ga.accept = sa.accept" 
    by (simp add: ga_bisim.accept_bisim pid_accept_eq) 

  lemma ga_run_eq: "pid.g.is_run r = ga.is_run r"
    using ga_bisim.br_run_conv[of id "\<lambda>_. True" r]
    by (auto simp: build_rel_def[abs_def])

  sublocale jsys: transition_system_initial ga_ex "\<lambda> a p. a \<in> ga_en p" "\<lambda> p. p = pid_init" . 

  lemma reachable_alt: "jsys.nodes = ga.E\<^sup>* `` ga.V0"
  proof safe
    fix gc
    assume "gc \<in> jsys.nodes"
    thus "gc \<in> ga.E\<^sup>* `` ga.V0"
      unfolding ga_automaton_def ga_step_alt rel_of_enex_def
      by (induct, auto intro: rtrancl_into_rtrancl)
  next
    fix gc gc'
    assume "(gc, gc') \<in> ga.E\<^sup>*" "gc \<in> ga.V0"
    thus "gc' \<in> jsys.nodes" unfolding ga_automaton_def ga_step_alt by induct auto
  qed

  lemma rtrancl_step_exec_word_conv:  
    "(gc, gc') \<in> ga_step\<^sup>* \<longleftrightarrow> (\<exists>w. jsys.path w gc \<and> gc' = jsys.target w gc)"
  proof safe
    assume "(gc, gc') \<in> ga_step\<^sup>*"
    thus "\<exists> w. jsys.path w gc \<and> gc' = jsys.target w gc"
      apply induction
      apply force
      apply (force simp: ga_step_alt pred_of_enex_def)
      done
  next
    fix w
    assume "jsys.path w gc"
    thus "(gc, jsys.target w gc) \<in> ga_step\<^sup>*"
      apply induction
      apply (auto simp: ga_step_alt rel_of_enex_def
        intro: converse_rtrancl_into_rtrancl)
      done
  qed

  sublocale jsys: transition_system_complete ga_ex "\<lambda> a p. a \<in> ga_en p" "\<lambda> p. p = pid_init" pid_label .

  lemma accept_eq_lang: "snth ` jsys.language = Collect sa.accept"
    unfolding ga_accept_eq[symmetric]
    unfolding ga_automaton_def
    unfolding ga_step_alt
    apply (rule system_complete_language_eq_lsystem_accept)
    unfolding ga_step_alt[symmetric]
    unfolding ga_automaton_def[symmetric]
    by unfold_locales

end

end

