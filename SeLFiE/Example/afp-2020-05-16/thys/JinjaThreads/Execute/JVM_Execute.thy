(*  Title:      JinjaThreads/Execute/JVM_Execute.thy
    Author:     Andreas Lochbihler
*)

theory JVM_Execute
imports
  SC_Schedulers
  JVMExec_Execute
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

interpretation sc_execute: 
  JVM_conf_read
    "addr2thread_id"
    "thread_id2addr"
    "sc_spurious_wakeups"
    "sc_empty"
    "sc_allocate P"
    "sc_typeof_addr"
    "sc_heap_read"
    "sc_heap_write"
    "sc_hconf P"
  for P
by(unfold_locales)

fun sc_mexec :: 
  "addr jvm_prog \<Rightarrow> thread_id \<Rightarrow> (addr jvm_thread_state \<times> heap) 
  \<Rightarrow> ((addr, thread_id, heap) jvm_thread_action \<times> addr jvm_thread_state \<times> heap) Predicate.pred"
where 
  "sc_mexec P t ((xcp, frs), h) =
   sc.exec_1 (TYPE(addr jvm_method)) P P t (xcp, h, frs) \<bind> (\<lambda>(ta, xcp, h, frs). Predicate.single (ta, (xcp, frs), h))"

abbreviation sc_jvm_start_state_refine :: 
  "addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> 
  (addr, thread_id, heap, (thread_id, (addr jvm_thread_state) \<times> addr released_locks) rm, (thread_id, addr wait_set_status) rm, thread_id rs) state_refine"
where
  "sc_jvm_start_state_refine \<equiv> 
   sc_start_state_refine (rm_empty ()) rm_update (rm_empty ()) (rs_empty ()) (\<lambda>C M Ts T (mxs, mxl0, b) vs. (None, [([], Null # vs @ replicate mxl0 undefined_value, C, M, 0)]))"

abbreviation sc_jvm_state_invar :: "addr jvm_prog \<Rightarrow> ty\<^sub>P \<Rightarrow> (addr,thread_id,addr jvm_thread_state,heap,addr) state set"
where "sc_jvm_state_invar P \<Phi> \<equiv> {s. sc_execute.correct_state_ts P \<Phi> (thr s) (shr s)}"

lemma eval_sc_mexec:
  "(\<lambda>t xm ta x'm'. Predicate.eval (sc_mexec P t xm) (ta, x'm')) = 
  (\<lambda>t ((xcp, frs), h) ta ((xcp', frs'), h'). sc.execute.exec_1 (TYPE(addr jvm_method)) P P t (xcp, h, frs) ta (xcp', h', frs'))"
by(rule ext)+(fastforce intro!: SUP1_I simp add: sc.exec_1_eq')

lemma sc_jvm_start_state_invar: 
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and "sc_wf_start_state P C M vs"
  shows "sc_state_\<alpha> (sc_jvm_start_state_refine P C M vs) \<in> sc_jvm_state_invar P \<Phi>"
using sc_execute.correct_jvm_state_initial[OF assms]
by(simp add: sc_execute.correct_jvm_state_def)

subsection \<open>Round-robin scheduler\<close>

interpretation JVM_rr: 
  sc_round_robin_base
    JVM_final "sc_mexec P" convert_RA Jinja_output
  for P
.

definition sc_rr_JVM_start_state :: "nat \<Rightarrow> 'm prog \<Rightarrow> thread_id fifo round_robin"
where "sc_rr_JVM_start_state n0 P = JVM_rr.round_robin_start n0 (sc_start_tid P)"

definition exec_JVM_rr ::
  "nat \<Rightarrow> addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> 
  (thread_id \<times> (addr, thread_id) obs_event list, 
   (addr, thread_id) locks \<times> ((thread_id, addr jvm_thread_state \<times> addr released_locks) rm \<times> heap) \<times>
   (thread_id, addr wait_set_status) rm \<times> thread_id rs) tllist"
where
  "exec_JVM_rr n0 P C M vs = JVM_rr.exec P n0 (sc_rr_JVM_start_state n0 P) (sc_jvm_start_state_refine P C M vs)"

interpretation JVM_rr:
  sc_round_robin 
    JVM_final "sc_mexec P" convert_RA Jinja_output
  for P
by(unfold_locales)

lemma JVM_rr:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows
  "sc_scheduler 
     JVM_final (sc_mexec P) convert_RA
     (JVM_rr.round_robin P n0) (pick_wakeup_via_sel (\<lambda>s P. rm_sel s (\<lambda>(k,v). P k v))) JVM_rr.round_robin_invar
     (sc_jvm_state_invar P \<Phi>)"
unfolding sc_scheduler_def
apply(rule JVM_rr.round_robin_scheduler)
apply(unfold eval_sc_mexec)
apply(rule sc_execute.mexec_deterministic[OF assms sc_deterministic_heap_ops])
apply(simp add: sc_spurious_wakeups)
done

subsection \<open>Random scheduler\<close>

interpretation JVM_rnd: 
  sc_random_scheduler_base
    JVM_final "sc_mexec P" convert_RA Jinja_output
  for P
.

definition sc_rnd_JVM_start_state :: "Random.seed \<Rightarrow> random_scheduler"
where "sc_rnd_JVM_start_state seed = seed"

definition exec_JVM_rnd ::
  "Random.seed \<Rightarrow> addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> 
  (thread_id \<times> (addr, thread_id) obs_event list,
   (addr, thread_id) locks \<times> ((thread_id, addr jvm_thread_state \<times> addr released_locks) rm \<times> heap) \<times>
   (thread_id, addr wait_set_status) rm \<times> thread_id rs) tllist"
where "exec_JVM_rnd seed P C M vs = JVM_rnd.exec P (sc_rnd_JVM_start_state seed) (sc_jvm_start_state_refine P C M vs)"

interpretation JVM_rnd:
  sc_random_scheduler
    JVM_final "sc_mexec P" convert_RA Jinja_output
  for P
by(unfold_locales)

lemma JVM_rnd:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows 
  "sc_scheduler
    JVM_final (sc_mexec P) convert_RA
    (JVM_rnd.random_scheduler P) (pick_wakeup_via_sel (\<lambda>s P. rm_sel s (\<lambda>(k,v). P k v))) (\<lambda>_ _. True)
    (sc_jvm_state_invar P \<Phi>)"
unfolding sc_scheduler_def
apply(rule JVM_rnd.random_scheduler_scheduler)
apply(unfold eval_sc_mexec)
apply(rule sc_execute.mexec_deterministic[OF assms sc_deterministic_heap_ops])
apply(simp add: sc_spurious_wakeups)
done

ML_val \<open>@{code exec_JVM_rr}\<close>

ML_val \<open>@{code exec_JVM_rnd}\<close>

end
