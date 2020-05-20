(*  Title:      JinjaThreads/Execute/JVM_Execute2.thy
    Author:     Andreas Lochbihler
*)

theory JVM_Execute2
imports
  SC_Schedulers
  JVMExec_Execute2
  "../BV/BVProgressThreaded"
begin

abbreviation sc_heap_read_cset :: "heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> addr val set"
where "sc_heap_read_cset h ad al \<equiv> set_of_pred (sc_heap_read_i_i_i_o h ad al)"

abbreviation sc_heap_write_cset :: "heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> addr val \<Rightarrow> heap set"
where "sc_heap_write_cset h ad al v \<equiv> set_of_pred (sc_heap_write_i_i_i_i_o h ad al v)"

interpretation sc: 
  JVM_heap_execute
    "addr2thread_id"
    "thread_id2addr"
    "sc_spurious_wakeups"
    "sc_empty"
    "sc_allocate P"
    "sc_typeof_addr"
    "sc_heap_read_cset"
    "sc_heap_write_cset"
  rewrites "\<And>h ad al v. v \<in> sc_heap_read_cset h ad al \<equiv> sc_heap_read h ad al v"
  and "\<And>h ad al v h'. h' \<in> sc_heap_write_cset h ad al v \<equiv> sc_heap_write h ad al v h'"
  for P
apply(simp_all add: eval_sc_heap_read_i_i_i_o eval_sc_heap_write_i_i_i_i_o)
done

interpretation sc: 
  JVM_heap_execute_conf_read
    "addr2thread_id"
    "thread_id2addr"
    "sc_spurious_wakeups"
    "sc_empty"
    "sc_allocate P"
    "sc_typeof_addr"
    "sc_heap_read_cset"
    "sc_heap_write_cset"
    "sc_hconf P"
    "P"
  rewrites "\<And>h ad al v. v \<in> sc_heap_read_cset h ad al \<equiv> sc_heap_read h ad al v"
  and "\<And>h ad al v h'. h' \<in> sc_heap_write_cset h ad al v \<equiv> sc_heap_write h ad al v h'"
  for P
proof -
  show unfolds: "\<And>h ad al v. v \<in> sc_heap_read_cset h ad al \<equiv> sc_heap_read h ad al v"
    "\<And>h ad al v h'. h' \<in> sc_heap_write_cset h ad al v \<equiv> sc_heap_write h ad al v h'"
    by(simp_all add: eval_sc_heap_read_i_i_i_o eval_sc_heap_write_i_i_i_i_o)
  show "JVM_heap_execute_conf_read
    addr2thread_id thread_id2addr
    sc_empty (sc_allocate P)
    sc_typeof_addr sc_heap_read_cset sc_heap_write_cset
    (sc_hconf P) P"
    apply(rule JVM_heap_execute_conf_read.intro)
    apply(unfold unfolds)
    apply(unfold_locales)
    done
qed

abbreviation sc_JVM_start_state :: "addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> (addr,thread_id,addr jvm_thread_state,heap,addr) state"
where "sc_JVM_start_state P \<equiv> sc.execute.JVM_start_state TYPE(addr jvm_method) P P"

abbreviation sc_exec :: "addr jvm_prog \<Rightarrow> thread_id \<Rightarrow> (addr, heap) jvm_state' \<Rightarrow> (addr, thread_id, heap) jvm_ta_state' set"
where "sc_exec P \<equiv> sc.exec TYPE(addr jvm_method) P P"

abbreviation sc_execute_mexec :: "addr jvm_prog \<Rightarrow> thread_id \<Rightarrow> (addr jvm_thread_state \<times> heap)
  \<Rightarrow> (addr, thread_id, heap) jvm_thread_action \<Rightarrow> (addr jvm_thread_state \<times> heap) \<Rightarrow> bool"
where "sc_execute_mexec P \<equiv> sc.execute.mexec TYPE(addr jvm_method) P P"

fun sc_mexec :: 
  "addr jvm_prog \<Rightarrow> thread_id \<Rightarrow> (addr jvm_thread_state' \<times> heap) 
  \<Rightarrow> ((addr, thread_id, heap) jvm_thread_action' \<times> addr jvm_thread_state' \<times> heap) Predicate.pred"
where 
  "sc_mexec P t ((xcp, frs), h) =
   sc.exec_1 (TYPE(addr jvm_method)) P P t (xcp, h, frs) \<bind> (\<lambda>(ta, xcp, h, frs). Predicate.single (ta, (xcp, frs), h))"

abbreviation sc_jvm_start_state_refine :: 
  "addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> 
  (addr, thread_id, heap, (thread_id, (addr jvm_thread_state') \<times> addr released_locks) rbt, (thread_id, addr wait_set_status) rbt, thread_id rs) state_refine"
where
  "sc_jvm_start_state_refine \<equiv> 
   sc_start_state_refine (rm_empty ()) rm_update (rm_empty ()) (rs_empty ()) (\<lambda>C M Ts T (mxs, mxl0, ins, xt) vs. (None, [((ins, ins, xt), [], Null # vs @ replicate mxl0 undefined_value, C, M, 0)]))"

fun jvm_mstate_of_jvm_mstate' :: 
  "(addr,thread_id,addr jvm_thread_state',heap,addr) state \<Rightarrow> (addr,thread_id,addr jvm_thread_state,heap,addr) state"
where
  "jvm_mstate_of_jvm_mstate' (ls, (ts, m), ws) = (ls, (\<lambda>t. map_option (map_prod jvm_thread_state_of_jvm_thread_state' id) (ts t), m), ws)"

definition sc_jvm_state_invar :: "addr jvm_prog \<Rightarrow> ty\<^sub>P \<Rightarrow> (addr,thread_id,addr jvm_thread_state',heap,addr) state set"
where
  "sc_jvm_state_invar P \<Phi> \<equiv> 
   {s. jvm_mstate_of_jvm_mstate' s \<in> sc.execute.correct_jvm_state P \<Phi>} \<inter> 
   {s. ts_ok (\<lambda>t (xcp, frs) h. jvm_state'_ok P (xcp, h, frs)) (thr s) (shr s)}"

fun JVM_final' :: "'addr jvm_thread_state' \<Rightarrow> bool"
where "JVM_final' (xcp, frs) \<longleftrightarrow> frs = []"

lemma shr_jvm_mstate_of_jvm_mstate' [simp]: "shr (jvm_mstate_of_jvm_mstate' s) = shr s"
by(cases s) clarsimp

lemma jvm_mstate_of_jvm_mstate'_sc_start_state [simp]:
  "jvm_mstate_of_jvm_mstate'
  (sc_start_state (\<lambda>C M Ts T (mxs, mxl0, ins, xt) vs. (None, [((ins, ins, xt), [], Null # vs @ replicate mxl0 undefined_value, C, M, 0)])) P C M vs) = sc_JVM_start_state P C M vs"
by(simp add: sc.start_state_def split_beta fun_eq_iff)

lemma sc_jvm_start_state_invar:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and "sc_wf_start_state P C M vs"
  shows "sc_state_\<alpha> (sc_jvm_start_state_refine P C M vs) \<in> sc_jvm_state_invar P \<Phi>"
unfolding sc_jvm_state_invar_def Int_iff mem_Collect_eq
apply(rule conjI)
 apply(simp add: sc.execute.correct_jvm_state_initial[OF assms])
apply(rule ts_okI)
using \<open>sc_wf_start_state P C M vs\<close>
apply(auto simp add: sc.start_state_def split_beta sc_wf_start_state_iff split: if_split_asm dest: sees_method_idemp)
done

lemma invariant3p_sc_jvm_state_invar:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows "invariant3p (multithreaded_base.redT JVM_final' (\<lambda>t xm ta x'm'. Predicate.eval (sc_mexec P t xm) (ta, x'm')) convert_RA) (sc_jvm_state_invar P \<Phi>)"
proof(rule invariant3pI)
  fix s tl s'
  assume red: "multithreaded_base.redT JVM_final' (\<lambda>t xm ta x'm'. Predicate.eval (sc_mexec P t xm) (ta, x'm')) convert_RA s tl s'"
    and invar: "s \<in> sc_jvm_state_invar P \<Phi>"
  obtain t ta where tl: "tl = (t, ta)" by(cases tl)
  from red have red': "multithreaded_base.redT JVM_final (sc_execute_mexec P) convert_RA (jvm_mstate_of_jvm_mstate' s) (t, jvm_thread_action_of_jvm_thread_action' ta) (jvm_mstate_of_jvm_mstate' s')"
  proof(cases rule: multithreaded_base.redT.cases[consumes 1, case_names normal acquire])
    case (acquire s t x ln n s')
    thus ?thesis using tl by(cases s)(auto intro!: multithreaded_base.redT.redT_acquire)
  next
    case (normal t x s ta x' m' s')
    obtain xcp frs where x: "x = (xcp, frs)" by(cases x)
    with invar normal tl
    have correct: "sc.execute.correct_state P \<Phi> t (jvm_state_of_jvm_state' (xcp, shr s, frs))"
      and ok: "jvm_state'_ok P (xcp, shr s, frs)"
      apply -
      apply(case_tac [!] s)
      apply(fastforce simp add: sc_jvm_state_invar_def sc.execute.correct_jvm_state_def dest: ts_okD)+
      done
    note eq = sc.exec_correct_state(1)[OF assms this]
    with normal x tl
    have "sc_execute_mexec P t (jvm_thread_state_of_jvm_thread_state' x, shr (jvm_mstate_of_jvm_mstate' s)) (jvm_thread_action_of_jvm_thread_action' ta) (jvm_thread_state_of_jvm_thread_state' x', m')" 
      by(auto simp add: sc.exec_1_def eq jvm_thread_action'_of_jvm_thread_action_def sc.execute.exec_1_iff)
    with normal tl show ?thesis
      by(cases s)(fastforce intro!: multithreaded_base.redT.redT_normal simp add: final_thread.actions_ok_iff fun_eq_iff map_redT_updTs elim: rev_iffD1[OF _ thread_oks_ts_change] cond_action_oks_final_change)
  qed
  moreover from invar
  have "sc.execute.correct_state_ts P \<Phi> (thr (jvm_mstate_of_jvm_mstate' s)) (shr (jvm_mstate_of_jvm_mstate' s))"
    and "lock_thread_ok (locks (jvm_mstate_of_jvm_mstate' s)) (thr (jvm_mstate_of_jvm_mstate' s))"
    by(simp_all add: sc_jvm_state_invar_def sc.execute.correct_jvm_state_def)
  ultimately have "sc.execute.correct_state_ts P \<Phi> (thr (jvm_mstate_of_jvm_mstate' s')) (shr (jvm_mstate_of_jvm_mstate' s'))"
    and "lock_thread_ok (locks (jvm_mstate_of_jvm_mstate' s')) (thr (jvm_mstate_of_jvm_mstate' s'))"
    by(blast intro: lifting_wf.redT_preserves[OF sc.execute.lifting_wf_correct_state, OF assms] sc.execute.exec_mthr.redT_preserves_lock_thread_ok)+
  hence "jvm_mstate_of_jvm_mstate' s' \<in> sc.execute.correct_jvm_state P \<Phi>"
    by(simp add: sc.execute.correct_jvm_state_def)
  moreover from red have "ts_ok (\<lambda>t (xcp, frs) h. \<forall>f\<in>set frs. frame'_ok P f) (thr s') (shr s')" unfolding tl 
  proof(cases rule: multithreaded_base.redT.cases[consumes 1, case_names normal acquire])
    case acquire thus ?thesis using invar
      by(fastforce simp add: sc_jvm_state_invar_def intro!: ts_okI dest: ts_okD bspec split: if_split_asm)
  next
    case (normal t x s ta x' m' s')
    obtain xcp frs where x: "x = (xcp, frs)" by(cases x)
    with invar normal tl
    have correct: "sc.execute.correct_state P \<Phi> t (jvm_state_of_jvm_state' (xcp, shr s, frs))"
      and ok: "jvm_state'_ok P (xcp, shr s, frs)"
      apply -
      apply(case_tac [!] s)
      apply(fastforce simp add: sc_jvm_state_invar_def sc.execute.correct_jvm_state_def dest: ts_okD)+
      done
    from normal x invar show ?thesis
      apply(auto simp add: sc.exec_1_def final_thread.actions_ok_iff jvm_thread_action'_ok_def sc_jvm_state_invar_def)
      apply hypsubst_thin
      apply(drule sc.exec_correct_state(3)[OF assms correct ok])
      apply(rule ts_okI)
      apply(clarsimp split: if_split_asm simp add: jvm_thread_action'_ok_def)
      apply(drule (1) bspec)
      apply simp
      apply(case_tac "thr s t")
       apply(drule (2) redT_updTs_new_thread)
       apply clarsimp
       apply(drule (1) bspec)
       apply simp
       apply(drule (1) bspec)
       apply simp
      apply(erule thin_rl)
      apply(frule (1) redT_updTs_Some)
      apply(fastforce dest: ts_okD)
      done
  qed
  ultimately show "s' \<in> sc_jvm_state_invar P \<Phi>" by(simp add: sc_jvm_state_invar_def)
qed

lemma sc_exec_deterministic:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows "multithreaded_base.deterministic JVM_final' (\<lambda>t xm ta x'm'. Predicate.eval (sc_mexec P t xm) (ta, x'm')) convert_RA
     (sc_jvm_state_invar P \<Phi>)"
proof -
  from assms sc_deterministic_heap_ops
  have det: "multithreaded_base.deterministic JVM_final (sc_execute_mexec P) convert_RA {s. sc.execute.correct_state_ts P \<Phi> (thr s) (shr s)}"
    by(rule sc.execute.mexec_deterministic)(simp add: sc_spurious_wakeups)
  show ?thesis
  proof(rule multithreaded_base.determisticI)
    fix s t x ta' x' m' ta'' x'' m''
    assume inv: "s \<in> sc_jvm_state_invar P \<Phi>"
      and tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and exec1: "Predicate.eval (sc_mexec P t (x, shr s)) (ta', x', m')"
      and exec2: "Predicate.eval (sc_mexec P t (x, shr s)) (ta'', x'', m'')"
      and aok1: "final_thread.actions_ok JVM_final' s t ta'"
      and aok2: "final_thread.actions_ok JVM_final' s t ta''"
    obtain xcp frs where x: "x = (xcp, frs)" by(cases x)
    from inv tst x have correct: "sc.execute.correct_state P \<Phi> t (jvm_state_of_jvm_state' (xcp, shr s, frs))"
      and ok: "jvm_state'_ok P (xcp, shr s, frs)"
      by(cases s, fastforce simp add: sc_jvm_state_invar_def sc.execute.correct_jvm_state_def dest: ts_okD)+
    note eq = sc.exec_correct_state(1)[OF assms this]
    
    from exec1 exec2 x
    have "sc_execute_mexec P t (jvm_thread_state_of_jvm_thread_state' x, shr (jvm_mstate_of_jvm_mstate' s)) (jvm_thread_action_of_jvm_thread_action' ta') (jvm_thread_state_of_jvm_thread_state' x', m')" 
      and "sc_execute_mexec P t (jvm_thread_state_of_jvm_thread_state' x, shr (jvm_mstate_of_jvm_mstate' s)) (jvm_thread_action_of_jvm_thread_action' ta'') (jvm_thread_state_of_jvm_thread_state' x'', m'')"
      by(auto simp add: sc.exec_1_def eq jvm_thread_action'_of_jvm_thread_action_def sc.execute.exec_1_iff)
    moreover have "thr (jvm_mstate_of_jvm_mstate' s) t = \<lfloor>(jvm_thread_state_of_jvm_thread_state' x, no_wait_locks)\<rfloor>"
      using tst by(cases s) clarsimp
    moreover have "final_thread.actions_ok JVM_final (jvm_mstate_of_jvm_mstate' s) t (jvm_thread_action_of_jvm_thread_action' ta')"
      and "final_thread.actions_ok JVM_final (jvm_mstate_of_jvm_mstate' s) t (jvm_thread_action_of_jvm_thread_action' ta'')"
      using aok1 aok2
      by -(case_tac [!] s,auto simp add: final_thread.actions_ok_iff elim: rev_iffD1[OF _ thread_oks_ts_change] cond_action_oks_final_change)
    moreover have "sc.execute.correct_state_ts P \<Phi> (thr (jvm_mstate_of_jvm_mstate' s)) (shr (jvm_mstate_of_jvm_mstate' s))"
      using inv
      by(cases s)(auto intro!: ts_okI simp add: sc_jvm_state_invar_def sc.execute.correct_jvm_state_def dest: ts_okD)
    ultimately
    have "jvm_thread_action_of_jvm_thread_action' ta' = jvm_thread_action_of_jvm_thread_action' ta'' \<and>
          jvm_thread_state_of_jvm_thread_state' x' = jvm_thread_state_of_jvm_thread_state' x'' \<and>
          m' = m''"
      by-(drule (4) multithreaded_base.deterministicD[OF det], simp_all)
    moreover from exec1 exec2 x
    have "(ta', (fst x', m', snd x')) \<in> sc_exec P t (xcp, shr s, frs)" 
      and "(ta'', (fst x'', m'', snd x'')) \<in> sc_exec P t (xcp, shr s, frs)"
      by(auto simp add: sc.exec_1_def)
    hence "jvm_ta_state'_ok P (ta', (fst x', m', snd x'))"
      and "jvm_ta_state'_ok P (ta'', (fst x'', m'', snd x''))"
      by(blast intro: sc.exec_correct_state[OF assms correct ok])+
    hence "ta' = jvm_thread_action'_of_jvm_thread_action P (jvm_thread_action_of_jvm_thread_action' ta')"
      and "ta'' = jvm_thread_action'_of_jvm_thread_action P (jvm_thread_action_of_jvm_thread_action' ta'')"
      and "x' = jvm_thread_state'_of_jvm_thread_state P (jvm_thread_state_of_jvm_thread_state' x')"
      and "x'' = jvm_thread_state'_of_jvm_thread_state P (jvm_thread_state_of_jvm_thread_state' x'')"
      apply -
      apply(case_tac [!] ta')
      apply(case_tac [!] ta'')
      apply(case_tac [!] x')
      apply(case_tac [!] x'')
      apply(fastforce simp add: jvm_thread_action'_of_jvm_thread_action_def jvm_thread_action'_ok_def intro!: map_idI[symmetric] convert_new_thread_action_eqI dest: bspec)+
      done
    ultimately
    show "ta' = ta'' \<and> x' = x'' \<and> m' = m''" by simp
  qed(rule invariant3p_sc_jvm_state_invar[OF assms])
qed

subsection \<open>Round-robin scheduler\<close>

interpretation JVM_rr: 
  sc_round_robin_base
    JVM_final' "sc_mexec P" convert_RA Jinja_output
  for P
.

definition sc_rr_JVM_start_state :: "nat \<Rightarrow> 'm prog \<Rightarrow> thread_id fifo round_robin"
where "sc_rr_JVM_start_state n0 P = JVM_rr.round_robin_start n0 (sc_start_tid P)"

definition exec_JVM_rr ::
  "nat \<Rightarrow> addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> 
  (thread_id \<times> (addr, thread_id) obs_event list, 
   (addr, thread_id) locks \<times> ((thread_id, addr jvm_thread_state' \<times> addr released_locks) RBT.rbt \<times> heap) \<times>
   (thread_id, addr wait_set_status) RBT.rbt \<times> thread_id rs) tllist"
where
  "exec_JVM_rr n0 P C M vs = JVM_rr.exec P n0 (sc_rr_JVM_start_state n0 P) (sc_jvm_start_state_refine P C M vs)"

interpretation JVM_rr:
  sc_round_robin 
    JVM_final' "sc_mexec P" convert_RA Jinja_output
  for P
by(unfold_locales)

lemma JVM_rr:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows
  "sc_scheduler 
     JVM_final' (sc_mexec P) convert_RA
     (JVM_rr.round_robin P n0) (pick_wakeup_via_sel (\<lambda>s P. rm_sel s (\<lambda>(k,v). P k v))) JVM_rr.round_robin_invar
     (sc_jvm_state_invar P \<Phi>)"
unfolding sc_scheduler_def
apply(rule JVM_rr.round_robin_scheduler)
apply(rule sc_exec_deterministic[OF assms])
done

subsection \<open>Random scheduler\<close>

interpretation JVM_rnd: 
  sc_random_scheduler_base
    JVM_final' "sc_mexec P" convert_RA Jinja_output
  for P
.

definition sc_rnd_JVM_start_state :: "Random.seed \<Rightarrow> random_scheduler"
where "sc_rnd_JVM_start_state seed = seed"

definition exec_JVM_rnd ::
  "Random.seed \<Rightarrow> addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> 
  (thread_id \<times> (addr, thread_id) obs_event list,
   (addr, thread_id) locks \<times> ((thread_id, addr jvm_thread_state' \<times> addr released_locks) RBT.rbt \<times> heap) \<times>
   (thread_id, addr wait_set_status) RBT.rbt \<times> thread_id rs) tllist"
where "exec_JVM_rnd seed P C M vs = JVM_rnd.exec P (sc_rnd_JVM_start_state seed) (sc_jvm_start_state_refine P C M vs)"

interpretation JVM_rnd:
  sc_random_scheduler
    JVM_final' "sc_mexec P" convert_RA Jinja_output
  for P
by(unfold_locales)

lemma JVM_rnd:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows 
  "sc_scheduler
    JVM_final' (sc_mexec P) convert_RA
    (JVM_rnd.random_scheduler P) (pick_wakeup_via_sel (\<lambda>s P. rm_sel s (\<lambda>(k,v). P k v))) (\<lambda>_ _. True)
    (sc_jvm_state_invar P \<Phi>)"
unfolding sc_scheduler_def
apply(rule JVM_rnd.random_scheduler_scheduler)
apply(rule sc_exec_deterministic[OF assms])
done

ML_val \<open>@{code exec_JVM_rr}\<close>

ML_val \<open>@{code exec_JVM_rnd}\<close>

end
