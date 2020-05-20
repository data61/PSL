(*  Title:      JinjaThreads/Compiler/Correctness.thy
    Author:     Andreas Lochbihler
*)

section \<open>Correctness of both stages\<close>

theory Correctness 
imports
  J0Bisim
  J1Deadlock 
  "../Framework/FWBisimDeadlock"
  Correctness2
  Correctness1Threaded
  Correctness1 
  JJ1WellForm
  Compiler
begin

locale J_JVM_heap_conf_base = 
  J0_J1_heap_base
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
  +
  J1_JVM_heap_conf_base 
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    hconf "compP1 P"
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "'addr J_prog"
begin

definition bisimJ2JVM :: 
  "(('addr,'thread_id,'addr expr\<times>'addr locals,'heap,'addr) state, 
    ('addr,'thread_id,'addr option \<times> 'addr frame list,'heap,'addr) state) bisim"
where "bisimJ2JVM = red_red0.mbisim \<circ>\<^sub>B red0_Red1'.mbisim \<circ>\<^sub>B mbisim_Red1'_Red1 \<circ>\<^sub>B Red1_execd.mbisim"

definition tlsimJ2JVM ::
  "('thread_id \<times> ('addr, 'thread_id, 'heap) J_thread_action,
    'thread_id \<times> ('addr, 'thread_id, 'heap) jvm_thread_action) bisim"
where "tlsimJ2JVM = red_red0.mta_bisim \<circ>\<^sub>B red0_Red1'.mta_bisim \<circ>\<^sub>B (=) \<circ>\<^sub>B Red1_execd.mta_bisim"

end

lemma compP2_has_method [simp]: "compP2 P \<turnstile> C has M \<longleftrightarrow> P \<turnstile> C has M"
by(auto simp add: compP2_def compP_has_method)

locale J_JVM_conf_read = 
  J1_JVM_conf_read
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    hconf "compP1 P"
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "'addr J_prog"
begin

sublocale J_JVM_heap_conf_base by(unfold_locales)

theorem bisimJ2JVM_weak_bisim:
  assumes wf: "wf_J_prog P"
  shows "delay_bisimulation_diverge_final (mredT P) (execd_mthr.redT (J2JVM P)) bisimJ2JVM tlsimJ2JVM 
            (red_mthr.m\<tau>move P) (execd_mthr.m\<tau>move (J2JVM P)) red_mthr.mfinal exec_mthr.mfinal"
unfolding bisimJ2JVM_def tlsimJ2JVM_def J2JVM_def o_apply
apply(rule delay_bisimulation_diverge_final_compose)
 apply(rule FWdelay_bisimulation_diverge.mthr_delay_bisimulation_diverge_final)
 apply(rule red_red0_FWbisim[OF wf_prog_wwf_prog[OF wf]])
apply(rule delay_bisimulation_diverge_final_compose)
 apply(rule FWdelay_bisimulation_diverge.mthr_delay_bisimulation_diverge_final)
 apply(rule red0_Red1'_FWweak_bisim[OF wf])
apply(rule delay_bisimulation_diverge_final_compose)
 apply(rule delay_bisimulation_diverge_final.intro)
  apply(rule bisimulation_into_delay.delay_bisimulation)
  apply(rule Red1'_Red1_bisim_into_weak[OF compP1_pres_wf[OF wf]])
 apply(rule bisimulation_final.delay_bisimulation_final_base)
 apply(rule Red1'_Red1_bisimulation_final[OF compP1_pres_wf[OF wf]])
apply(rule FWdelay_bisimulation_diverge.mthr_delay_bisimulation_diverge_final)
apply(rule Red1_exec1_FWwbisim[OF compP1_pres_wf[OF wf]])
done


lemma bisimJ2JVM_start:
  assumes wf: "wf_J_prog P"
  and start: "wf_start_state P C M vs"
  shows "bisimJ2JVM (J_start_state P C M vs) (JVM_start_state (J2JVM P) C M vs)"
using assms
unfolding bisimJ2JVM_def J2JVM_def o_def
apply(intro bisim_composeI)
   apply(erule (1) bisim_J_J0_start[OF wf_prog_wwf_prog])
  apply(erule (1) bisim_J0_J1_start)
 apply(erule bisim_J1_J1_start[OF compP1_pres_wf])
 apply simp
apply(erule bisim_J1_JVM_start[OF compP1_pres_wf])
apply simp
done

end

fun exception :: "'addr expr \<times> 'addr locals \<Rightarrow> 'addr option \<times> 'addr frame list"
where "exception (Throw a, xs) = (\<lfloor>a\<rfloor>, [])"
| "exception _ = (None, [])"

definition mexception :: 
  "('addr,'thread_id,'addr expr\<times>'addr locals,'heap,'addr) state \<Rightarrow> 
   ('addr,'thread_id,'addr option\<times>'addr frame list,'heap,'addr) state"
where
  "\<And>ln. mexception s \<equiv> 
  (locks s, (\<lambda>t. case thr s t of \<lfloor>(e, ln)\<rfloor> \<Rightarrow> \<lfloor>(exception e, ln)\<rfloor> | None \<Rightarrow> None, shr s), wset s, interrupts s)"

declare compP1_def [simp del]

context J_JVM_heap_conf_base begin

lemma bisimJ2JVM_mfinal_mexception:
  assumes bisim: "bisimJ2JVM s s'"
  and fin: "exec_mthr.mfinal s'"
  and fin': "red_mthr.mfinal s"
  and tsNotEmpty: "thr s t \<noteq> None"
  shows "s' = mexception s"
proof -
  obtain ls ts m ws "is" where s: "s = (ls, (ts, m), ws, is)" by(cases s) fastforce
  from bisim obtain s0 s1 where bisimJ0: "red_red0.mbisim s s0"
    and bisim01: "red0_Red1'.mbisim s0 s1"
    and bisim1JVM: "Red1_execd.mbisim s1 s'"
    unfolding bisimJ2JVM_def by(fastforce simp add: mbisim_Red1'_Red1_def)
  from bisimJ0 s have [simp]: "locks s0 = ls" "wset s0 = ws" "interrupts s0 = is"
    and tbisimJ0: "\<And>t. red_red0.tbisim (ws t = None) t (ts t) m (thr s0 t) (shr s0)"
    by(auto simp add: red_red0.mbisim_def)
  from bisim01 have [simp]: "locks s1 = ls" "wset s1 = ws" "interrupts s1 = is"
    and tbisim01: "\<And>t. red0_Red1'.tbisim (ws t = None) t (thr s0 t) (shr s0) (thr s1 t) (shr s1)"
    by(auto simp add: red0_Red1'.mbisim_def)
  from bisim1JVM have "locks s' = ls" "wset s' = ws" "interrupts s' = is"
    and tbisim1JVM: "\<And>t. Red1_execd.tbisim (ws t = None) t (thr s1 t) (shr s1) (thr s' t) (shr s')"
    by(auto simp add: Red1_execd.mbisim_def)
  then obtain ts' m' where s': "s' = (ls, (ts', m'), ws, is)" by(cases s') fastforce
  { fix t e x ln
    assume tst: "ts t = \<lfloor>((e, x), ln)\<rfloor>"
    from tbisimJ0[of t] tst obtain e' exs' where ts0t: "thr s0 t = \<lfloor>((e', exs'), ln)\<rfloor>"
      and bisimtJ0: "bisim_red_red0 ((e, x), m) ((e', exs'), shr s0)"
      by(auto simp add: red_red0.tbisim_def)
    from tbisim01[of t] ts0t obtain e'' xs'' exs''
      where ts1t: "thr s1 t = \<lfloor>(((e'', xs''), exs''), ln)\<rfloor>"
      and bisimt01: "bisim_red0_Red1 ((e', exs'), shr s0) (((e'', xs''), exs''), shr s1)"
      by(auto simp add: red0_Red1'.tbisim_def)
    from tbisim1JVM[of t] ts1t s' obtain xcp frs
      where ts't: "ts' t = \<lfloor>((xcp, frs), ln)\<rfloor>" and [simp]: "m' = shr s1"
      and bisimt1JVM: "bisim1_list1 t m' (e'', xs'') exs'' xcp frs"
      by(fastforce simp add: Red1_execd.tbisim_def)

    from fin ts't s s' have [simp]: "frs = []" by(auto dest: exec_mthr.mfinalD)
    from bisimt1JVM have [simp]: "exs'' = []" by(auto elim: bisim1_list1.cases)
    from bisimt01 have [simp]: "exs' = []"
      by(auto simp add: bisim_red0_Red1_def elim!: bisim_list1E elim: bisim_list.cases)
    from tst fin' s have fine: "final e" by(auto dest: red_mthr.mfinalD)
    hence "exception (e, x) = (xcp, frs)"
    proof(cases)
      fix v
      assume [simp]: "e = Val v"
      from bisimtJ0 have "e' = Val v" by(auto elim!: bisim_red_red0.cases)
      with bisimt01 have "e'' = Val v" by(auto simp add: bisim_red0_Red1_def elim: bisim_list1E)
      with bisimt1JVM have "xcp = None" by(auto elim: bisim1_list1.cases)
      thus ?thesis by simp
    next
      fix a
      assume [simp]: "e = Throw a"
      from bisimtJ0 have "e' = Throw a" by(auto elim!: bisim_red_red0.cases)
      with bisimt01 have "e'' = Throw a" by(auto simp add: bisim_red0_Red1_def elim: bisim_list1E)
      with bisimt1JVM have "xcp = \<lfloor>a\<rfloor>" by(auto elim: bisim1_list1.cases)
      thus ?thesis by simp
    qed
    moreover from bisimtJ0 have "shr s0 = m" by(auto elim: bisim_red_red0.cases)
    moreover from bisimt01 have "shr s1 = shr s0" by(auto simp add: bisim_red0_Red1_def)
    ultimately have "ts' t = \<lfloor>(exception (e, x), ln)\<rfloor>" "m' = m" using ts't by simp_all }
  moreover {
    fix t
    assume "ts t = None"
    with red_red0.mbisim_thrNone_eq[OF bisimJ0, of t] s have "thr s0 t = None" by simp
    with bisim01 have "thr s1 t = None" by(auto simp add: red0_Red1'.mbisim_thrNone_eq)
    with bisim1JVM s' have "ts' t = None" by(simp add: Red1_execd.mbisim_thrNone_eq) }
  ultimately show ?thesis using s s' tsNotEmpty by(auto simp add: mexception_def fun_eq_iff)
qed

end

context J_JVM_conf_read begin

theorem J2JVM_correct1:
  fixes C M vs
  defines s: "s \<equiv> J_start_state P C M vs"
  and comps: "cs \<equiv> JVM_start_state (J2JVM P) C M vs"
  assumes wf: "wf_J_prog P"
  and wf_start: "wf_start_state P C M vs"
  and red: "red_mthr.mthr.\<tau>Runs P s \<xi>"
  obtains \<xi>' 
  where "execd_mthr.mthr.\<tau>Runs (J2JVM P) cs \<xi>'" "tllist_all2 tlsimJ2JVM (rel_option bisimJ2JVM) \<xi> \<xi>'"
  and "\<And>s'. \<lbrakk> tfinite \<xi>; terminal \<xi> = \<lfloor>s'\<rfloor>; red_mthr.mfinal s' \<rbrakk>
      \<Longrightarrow> tfinite \<xi>' \<and> terminal \<xi>' = \<lfloor>mexception s'\<rfloor>"
  and "\<And>s'. \<lbrakk> tfinite \<xi>; terminal \<xi> = \<lfloor>s'\<rfloor>; red_mthr.deadlock P s' \<rbrakk>
      \<Longrightarrow> \<exists>cs'. tfinite \<xi>' \<and> terminal \<xi>' = \<lfloor>cs'\<rfloor> \<and> execd_mthr.deadlock (J2JVM P) cs' \<and> bisimJ2JVM s' cs'"
  and "\<lbrakk> tfinite \<xi>; terminal \<xi> = None \<rbrakk> \<Longrightarrow> tfinite \<xi>' \<and> terminal \<xi>' = None"
  and "\<not> tfinite \<xi> \<Longrightarrow> \<not> tfinite \<xi>'"
proof -
  from wf wf_start have bisim: "bisimJ2JVM s cs" unfolding s comps by(rule bisimJ2JVM_start)

  note divfin = delay_bisimulation_diverge_final.delay_bisimulation_diverge[OF bisimJ2JVM_weak_bisim[OF wf]]
  note divfin2 = delay_bisimulation_diverge_final.delay_bisimulation_final_base[OF bisimJ2JVM_weak_bisim[OF wf]]

  from delay_bisimulation_diverge.simulation_\<tau>Runs1[OF divfin, OF bisim red] obtain \<xi>' 
    where exec: "execd_mthr.mthr.\<tau>Runs (J2JVM P) cs \<xi>'" 
    and tlsim: "tllist_all2 tlsimJ2JVM (rel_option bisimJ2JVM) \<xi> \<xi>'" by blast
  moreover {
    fix s'
    assume fin: "tfinite \<xi>" and s': "terminal \<xi> = \<lfloor>s'\<rfloor>" and final: "red_mthr.mfinal s'"
    from delay_bisimulation_final_base.\<tau>Runs_terminate_final1[OF divfin2, OF red exec tlsim fin s' final]
    obtain cs' where fin': "tfinite \<xi>'" and cs': "terminal \<xi>' = \<lfloor>cs'\<rfloor>"
      and final': "exec_mthr.mfinal cs'" by blast
    from tlsim fin s' cs' have bisim': "bisimJ2JVM s' cs'" by(auto dest: tllist_all2_tfinite1_terminalD)
    from red_mthr.mthr.\<tau>Runs_into_\<tau>rtrancl3p[OF red fin s'] 
    have "thr s' start_tid \<noteq> None" unfolding s
      by(rule red_mthr.\<tau>rtrancl3p_redT_thread_not_disappear)(simp add: start_state_def)
    with bisim' final final' have [simp]: "cs' = mexception s'"
      by(intro bisimJ2JVM_mfinal_mexception disjI1)
    with fin' cs' have "tfinite \<xi>' \<and> terminal \<xi>' = \<lfloor>mexception s'\<rfloor>" by simp }
  moreover {
    fix s'
    assume fin: "tfinite \<xi>" and s': "terminal \<xi> = \<lfloor>s'\<rfloor>" and dead: "red_mthr.deadlock P s'"
    from tlsim fin s'
    obtain cs' where "tfinite \<xi>'" and cs': "terminal \<xi>' = \<lfloor>cs'\<rfloor>"
      and bisim': "bisimJ2JVM s' cs'"
      by(cases "terminal \<xi>'")(fastforce dest: tllist_all2_tfinite1_terminalD tllist_all2_tfiniteD)+
    from bisim' obtain s0' s1' S1' where bisim0: "red_red0.mbisim s' s0'"
      and bisim01: "red0_Red1'.mbisim s0' s1'"
      and bisim11: "mbisim_Red1'_Red1 s1' S1'"
      and bisim12: "Red1_execd.mbisim S1' cs'"
      unfolding bisimJ2JVM_def by auto

    note b0 = red_red0_FWbisim[OF wf_prog_wwf_prog[OF wf]]
    note b01 = red0_Red1'_FWweak_bisim[OF wf]
    note b01mthr = FWdelay_bisimulation_diverge.mbisim_delay_bisimulation[OF b01]
    note b11 = Red1'_Red1_bisim_into_weak[OF compP1_pres_wf[OF wf]]
    note b11delay = bisimulation_into_delay.delay_bisimulation[OF b11]
    note b12 = Red1_exec1_FWwbisim[OF compP1_pres_wf[OF wf]]
    note b12mthr = FWdelay_bisimulation_diverge.mbisim_delay_bisimulation[OF b12]

    from FWdelay_bisimulation_diverge.deadlock1_imp_\<tau>s_deadlock2[OF b0, OF bisim0 dead, of convert_RA]
    obtain s0'' where "red0_mthr.mthr.silent_moves P s0' s0''"
      and bisim0': "red_red0.mbisim s' s0''"
      and dead0: "red0_mthr.deadlock P s0''" by auto
    
    from delay_bisimulation_diverge.simulation_silents1[OF b01mthr, OF bisim01 \<open>red0_mthr.mthr.silent_moves P s0' s0''\<close>]
    obtain s1'' where "Red1_mthr.mthr.silent_moves False (compP1 P) s1' s1''"
      and "red0_Red1'.mbisim s0'' s1''" by auto
    from FWdelay_bisimulation_diverge.deadlock1_imp_\<tau>s_deadlock2[OF b01, OF \<open>red0_Red1'.mbisim s0'' s1''\<close> dead0, of convert_RA]
    obtain s1''' where "Red1_mthr.mthr.silent_moves False (compP1 P) s1'' s1'''"
      and dead1: "Red1_mthr.deadlock False (compP1 P) s1'''"
      and bisim01': "red0_Red1'.mbisim s0'' s1'''" by auto
    from \<open>Red1_mthr.mthr.silent_moves False (compP1 P) s1' s1''\<close> \<open>Red1_mthr.mthr.silent_moves False (compP1 P) s1'' s1'''\<close>
    have "Red1_mthr.mthr.silent_moves False (compP1 P) s1' s1'''" by(rule rtranclp_trans)

    from delay_bisimulation_diverge.simulation_silents1[OF b11delay, OF bisim11 this]
    obtain S1'' where "Red1_mthr.mthr.silent_moves True (compP1 P) S1' S1''"
      and bisim11': "mbisim_Red1'_Red1 s1''' S1''" by auto
    from bisim11' have "s1''' = S1''" by(simp add: mbisim_Red1'_Red1_def)
    with dead1 have dead1': "Red1_mthr.deadlock True (compP1 P) S1''"
      by(simp add: Red1_Red1'_deadlock_inv)

    from delay_bisimulation_diverge.simulation_silents1[OF b12mthr, OF bisim12 \<open>Red1_mthr.mthr.silent_moves True (compP1 P) S1' S1''\<close>]
    obtain cs'' where "execd_mthr.mthr.silent_moves (compP2 (compP1 P)) cs' cs''"
      and "Red1_execd.mbisim S1'' cs''" by auto
    from FWdelay_bisimulation_diverge.deadlock1_imp_\<tau>s_deadlock2[OF b12 \<open>Red1_execd.mbisim S1'' cs''\<close> dead1', of convert_RA]
    obtain cs''' where "execd_mthr.mthr.silent_moves (compP2 (compP1 P)) cs'' cs'''"
      and bisim12': "Red1_execd.mbisim S1'' cs'''"
      and dead': "execd_mthr.deadlock (compP2 (compP1 P)) cs'''" by auto
    from \<open>execd_mthr.mthr.silent_moves (compP2 (compP1 P)) cs' cs''\<close> \<open>execd_mthr.mthr.silent_moves (compP2 (compP1 P)) cs'' cs'''\<close>
    have "execd_mthr.mthr.silent_moves (compP2 (compP1 P)) cs' cs'''" by(rule rtranclp_trans)
    hence "cs''' = cs'" using execd_mthr.mthr.\<tau>Runs_terminal_stuck[OF exec \<open>tfinite \<xi>'\<close> \<open>terminal \<xi>' = \<lfloor>cs'\<rfloor>\<close>]
      by(cases rule: converse_rtranclpE)(fastforce simp add: J2JVM_def)+
    with dead' have "execd_mthr.deadlock (J2JVM P) cs'" by(simp add: J2JVM_def)
    hence "\<exists>cs'. tfinite \<xi>' \<and> terminal \<xi>' = \<lfloor>cs'\<rfloor> \<and> execd_mthr.deadlock (J2JVM P) cs' \<and> bisimJ2JVM s' cs'"
      using \<open>tfinite \<xi>'\<close> \<open>terminal \<xi>' = \<lfloor>cs'\<rfloor>\<close> bisim' by blast }
  moreover {
    assume "tfinite \<xi>" and "terminal \<xi> = None"
    hence "tfinite \<xi>' \<and> terminal \<xi>' = None" using tlsim tllist_all2_tfiniteD[OF tlsim]
      by(cases "terminal \<xi>'")(auto dest: tllist_all2_tfinite1_terminalD) }
  moreover {
    assume "\<not> tfinite \<xi>"
      hence "\<not> tfinite \<xi>'" using tlsim by(blast dest: tllist_all2_tfiniteD) }
  ultimately show thesis by(rule that)
qed

theorem J2JVM_correct2:
  fixes C M vs
  defines s: "s \<equiv> J_start_state P C M vs"
  and comps: "cs \<equiv> JVM_start_state (J2JVM P) C M vs"
  assumes wf: "wf_J_prog P"
  and wf_start: "wf_start_state P C M vs"
  and exec: "execd_mthr.mthr.\<tau>Runs (J2JVM P) cs \<xi>'"
  obtains \<xi> 
  where "red_mthr.mthr.\<tau>Runs P s \<xi>" "tllist_all2 tlsimJ2JVM (rel_option bisimJ2JVM) \<xi> \<xi>'"
  and "\<And>cs'. \<lbrakk> tfinite \<xi>'; terminal \<xi>' = \<lfloor>cs'\<rfloor>; exec_mthr.mfinal cs' \<rbrakk>
      \<Longrightarrow> \<exists>s'. tfinite \<xi> \<and> terminal \<xi> = \<lfloor>s'\<rfloor> \<and> cs' = mexception s' \<and> bisimJ2JVM s' cs'"
  and "\<And>cs'. \<lbrakk> tfinite \<xi>'; terminal \<xi>' = \<lfloor>cs'\<rfloor>; execd_mthr.deadlock (J2JVM P) cs' \<rbrakk>
      \<Longrightarrow> \<exists>s'. tfinite \<xi> \<and> terminal \<xi> = \<lfloor>s'\<rfloor> \<and> red_mthr.deadlock P s' \<and> bisimJ2JVM s' cs'"
  and "\<lbrakk> tfinite \<xi>'; terminal \<xi>' = None \<rbrakk> \<Longrightarrow> tfinite \<xi> \<and> terminal \<xi> = None"
  and "\<not> tfinite \<xi>' \<Longrightarrow> \<not> tfinite \<xi>"
proof -
  from wf wf_start have bisim: "bisimJ2JVM s cs" unfolding s comps by(rule bisimJ2JVM_start)

  note divfin = delay_bisimulation_diverge_final.delay_bisimulation_diverge[OF bisimJ2JVM_weak_bisim[OF wf]]
  note divfin2 = delay_bisimulation_diverge_final.delay_bisimulation_final_base[OF bisimJ2JVM_weak_bisim[OF wf]]

  from delay_bisimulation_diverge.simulation_\<tau>Runs2[OF divfin, OF bisim exec] obtain \<xi>
    where red: "red_mthr.mthr.\<tau>Runs P s \<xi>" 
    and tlsim: "tllist_all2 tlsimJ2JVM (rel_option bisimJ2JVM) \<xi> \<xi>'" by blast
  moreover {
    fix cs'
    assume fin: "tfinite \<xi>'" and cs': "terminal \<xi>' = \<lfloor>cs'\<rfloor>" and final: "exec_mthr.mfinal cs'"
    from delay_bisimulation_final_base.\<tau>Runs_terminate_final2[OF divfin2, OF red exec tlsim fin cs' final]
    obtain s' where fin': "tfinite \<xi>" and s': "terminal \<xi> = \<lfloor>s'\<rfloor>"
      and final': "red_mthr.mfinal s'" by blast
    from tlsim fin s' cs' have bisim': "bisimJ2JVM s' cs'" by(auto dest: tllist_all2_tfinite2_terminalD)
    from red_mthr.mthr.\<tau>Runs_into_\<tau>rtrancl3p[OF red fin' s'] 
    have "thr s' start_tid \<noteq> None" unfolding s
      by(rule red_mthr.\<tau>rtrancl3p_redT_thread_not_disappear)(simp add: start_state_def)
    with bisim' final final' have [simp]: "cs' = mexception s'"
      by(intro bisimJ2JVM_mfinal_mexception)
    with fin' s' bisim' have "\<exists>s'. tfinite \<xi> \<and> terminal \<xi> = \<lfloor>s'\<rfloor> \<and> cs' = mexception s' \<and> bisimJ2JVM s' cs'" by simp }
  moreover {
    fix cs'
    assume fin: "tfinite \<xi>'" and cs': "terminal \<xi>' = \<lfloor>cs'\<rfloor>" and dead': "execd_mthr.deadlock (J2JVM P) cs'"
    from tlsim fin cs'
    obtain s' where "tfinite \<xi>" and s': "terminal \<xi> = \<lfloor>s'\<rfloor>"
      and bisim': "bisimJ2JVM s' cs'"
      by(cases "terminal \<xi>")(fastforce dest: tllist_all2_tfinite2_terminalD tllist_all2_tfiniteD)+
    from bisim' obtain s0' s1' S1' where bisim0: "red_red0.mbisim s' s0'"
      and bisim01: "red0_Red1'.mbisim s0' s1'"
      and bisim11: "mbisim_Red1'_Red1 s1' S1'"
      and bisim12: "Red1_execd.mbisim S1' cs'"
      unfolding bisimJ2JVM_def by auto

    note b0 = red_red0_FWbisim[OF wf_prog_wwf_prog[OF wf]]
    note b0mthr = FWdelay_bisimulation_diverge.mbisim_delay_bisimulation[OF b0]
    note b01 = red0_Red1'_FWweak_bisim[OF wf]
    note b01mthr = FWdelay_bisimulation_diverge.mbisim_delay_bisimulation[OF b01]
    note b11 = Red1'_Red1_bisim_into_weak[OF compP1_pres_wf[OF wf]]
    note b11delay = bisimulation_into_delay.delay_bisimulation[OF b11]
    note b12 = Red1_exec1_FWwbisim[OF compP1_pres_wf[OF wf]]

    from FWdelay_bisimulation_diverge.deadlock2_imp_\<tau>s_deadlock1[OF b12 bisim12, of convert_RA] dead'
    obtain S1'' where "Red1_mthr.mthr.silent_moves True (compP1 P) S1' S1''"
      and bisim12': "Red1_execd.mbisim S1'' cs'"
      and dead': "Red1_mthr.deadlock True (compP1 P) S1''" by(auto simp add: J2JVM_def)
    from delay_bisimulation_diverge.simulation_silents2[OF b11delay, OF bisim11 \<open>Red1_mthr.mthr.silent_moves True (compP1 P) S1' S1''\<close>]
    obtain s1'' where "Red1_mthr.mthr.silent_moves False (compP1 P) s1' s1''"
      and bisim11': "mbisim_Red1'_Red1 s1'' S1''" by blast
    from bisim11' have "s1'' = S1''" by(simp add: mbisim_Red1'_Red1_def)
    with dead' have dead1: "Red1_mthr.deadlock False (compP1 P) s1''"
      by(simp add: Red1_Red1'_deadlock_inv)
    from delay_bisimulation_diverge.simulation_silents2[OF b01mthr, OF bisim01 \<open>Red1_mthr.mthr.silent_moves False (compP1 P) s1' s1''\<close>]
    obtain s0'' where "red0_mthr.mthr.silent_moves P s0' s0''"
      and bisim01': "red0_Red1'.mbisim s0'' s1''" by auto
    from FWdelay_bisimulation_diverge.deadlock2_imp_\<tau>s_deadlock1[OF b01 bisim01' dead1, of convert_RA]
    obtain s0''' where "red0_mthr.mthr.silent_moves P s0'' s0'''"
      and bisim01'': "red0_Red1'.mbisim s0''' s1''"
      and dead0: "red0_mthr.deadlock P s0'''" by auto
    from \<open>red0_mthr.mthr.silent_moves P s0' s0''\<close> \<open>red0_mthr.mthr.silent_moves P s0'' s0'''\<close>
    have "red0_mthr.mthr.silent_moves P s0' s0'''" by(rule rtranclp_trans)
    from delay_bisimulation_diverge.simulation_silents2[OF b0mthr, OF bisim0 this]
    obtain s'' where "red_mthr.mthr.silent_moves P s' s''" 
      and "red_red0.mbisim s'' s0'''" by blast
    from FWdelay_bisimulation_diverge.deadlock2_imp_\<tau>s_deadlock1[OF b0 \<open>red_red0.mbisim s'' s0'''\<close> dead0, of convert_RA]
    obtain s''' where "red_mthr.mthr.silent_moves P s'' s'''" 
      and "red_red0.mbisim s''' s0'''"
      and dead: "red_mthr.deadlock P s'''" by blast
    from \<open>red_mthr.mthr.silent_moves P s' s''\<close> \<open>red_mthr.mthr.silent_moves P s'' s'''\<close>
    have "red_mthr.mthr.silent_moves P s' s'''" by(rule rtranclp_trans)
    hence "s''' = s'" using red_mthr.mthr.\<tau>Runs_terminal_stuck[OF red \<open>tfinite \<xi>\<close> \<open>terminal \<xi> = \<lfloor>s'\<rfloor>\<close>]
      by(cases rule: converse_rtranclpE) fastforce+
    with dead have "red_mthr.deadlock P s'" by(simp)
    hence "\<exists>s'. tfinite \<xi> \<and> terminal \<xi> = \<lfloor>s'\<rfloor> \<and> red_mthr.deadlock P s' \<and> bisimJ2JVM s' cs'"
      using \<open>tfinite \<xi>\<close> \<open>terminal \<xi> = \<lfloor>s'\<rfloor>\<close> bisim' by blast }
  moreover {
    assume "tfinite \<xi>'" and "terminal \<xi>' = None"
    hence "tfinite \<xi> \<and> terminal \<xi> = None" using tlsim tllist_all2_tfiniteD[OF tlsim]
      by(cases "terminal \<xi>")(auto dest: tllist_all2_tfinite2_terminalD) }
  moreover {
    assume "\<not> tfinite \<xi>'"
      hence "\<not> tfinite \<xi>" using tlsim by(blast dest: tllist_all2_tfiniteD) }
  ultimately show thesis by(rule that)
qed

end

declare compP1_def [simp]

theorem wt_J2JVM: "wf_J_prog P \<Longrightarrow> wf_jvm_prog (J2JVM P)"
unfolding J2JVM_def o_def
by(rule wt_compP2)(rule compP1_pres_wf)

end
