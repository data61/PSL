(*  Title:      JinjaThreads/Execute/J_Execute.thy
    Author:     Andreas Lochbihler
*)

section \<open>Executable semantics for J\<close>

theory J_Execute
imports
  SC_Schedulers
  "../J/Threaded"
begin

interpretation sc:
  J_heap_base
    "addr2thread_id"
    "thread_id2addr"
    "sc_spurious_wakeups"
    "sc_empty"
    "sc_allocate P"
    "sc_typeof_addr"
    "sc_heap_read"
    "sc_heap_write"
  for P .

abbreviation sc_red ::
  "((addr, thread_id, heap) external_thread_action \<Rightarrow> (addr, thread_id, 'o, heap) Jinja_thread_action)
  \<Rightarrow> addr J_prog \<Rightarrow> thread_id \<Rightarrow> addr expr \<Rightarrow> heap \<times> addr locals
  \<Rightarrow> (addr, thread_id, 'o, heap) Jinja_thread_action \<Rightarrow> addr expr \<Rightarrow> heap \<times> addr locals \<Rightarrow> bool"
  ("_,_,_ \<turnstile>sc ((1\<langle>_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,51,0,0,0,0,0,0] 81)
where
  "sc_red extTA P \<equiv> sc.red (TYPE(addr J_mb)) P extTA P"

fun sc_red_i_i_i_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o
where
  "sc_red_i_i_i_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P t ((e, xs), h) =
  red_i_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o
    addr2thread_id thread_id2addr sc_spurious_wakeups
    sc_empty (sc_allocate P) sc_typeof_addr sc_heap_read_i_i_i_o sc_heap_write_i_i_i_i_o
    (extTA2J P) P t e (h, xs)
  \<bind> (\<lambda>(ta, e, h, xs). Predicate.single (ta, (e, xs), h))"

abbreviation sc_J_start_state_refine ::
  "addr J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow>
  (addr, thread_id, heap, (thread_id, (addr expr \<times> addr locals) \<times> addr released_locks) rm, (thread_id, addr wait_set_status) rm, thread_id rs) state_refine"
where
  "sc_J_start_state_refine \<equiv>
   sc_start_state_refine
     (rm_empty ()) rm_update (rm_empty ()) (rs_empty ())
     (\<lambda>C M Ts T (pns, body) vs. (blocks (this # pns) (Class C # Ts) (Null # vs) body, Map.empty))"

lemma eval_sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o:
  "(\<lambda>t xm ta x'm'. Predicate.eval (sc_red_i_i_i_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P t xm) (ta, x'm')) =
  (\<lambda>t ((e, xs), h) ta ((e', xs'), h'). extTA2J P,P,t \<turnstile>sc \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle>)"
by(auto elim!: red_i_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_oE intro!: red_i_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_oI ext SUP1_I simp add: eval_sc_heap_write_i_i_i_i_o eval_sc_heap_read_i_i_i_o)

lemma sc_J_start_state_invar: "(\<lambda>_. True) (sc_state_\<alpha> (sc_J_start_state_refine P C M vs))"
by simp

subsection \<open>Round-robin scheduler\<close>

interpretation J_rr:
  sc_round_robin_base
    final_expr "sc_red_i_i_i_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P" convert_RA Jinja_output
  for P
.

definition sc_rr_J_start_state :: "nat \<Rightarrow> 'm prog \<Rightarrow> thread_id fifo round_robin"
where "sc_rr_J_start_state n0 P = J_rr.round_robin_start n0 (sc_start_tid P)"

definition exec_J_rr ::
  "nat \<Rightarrow> addr J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow>
  (thread_id \<times> (addr, thread_id) obs_event list,
   (addr, thread_id) locks \<times> ((thread_id, (addr expr \<times> addr locals) \<times> addr released_locks) rm \<times> heap) \<times>
   (thread_id, addr wait_set_status) rm \<times> thread_id rs) tllist"
where
  "exec_J_rr n0 P C M vs = J_rr.exec P n0 (sc_rr_J_start_state n0 P) (sc_J_start_state_refine P C M vs)"

interpretation J_rr:
  sc_round_robin
    final_expr "sc_red_i_i_i_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P" convert_RA Jinja_output
  for P
by(unfold_locales)

interpretation J_rr:
  sc_scheduler
    final_expr "sc_red_i_i_i_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P" convert_RA
    "J_rr.round_robin P n0" Jinja_output "pick_wakeup_via_sel (\<lambda>s P. rm_sel s (\<lambda>(k,v). P k v))" J_rr.round_robin_invar
    UNIV
  for P n0
unfolding sc_scheduler_def
apply(rule J_rr.round_robin_scheduler)
apply(unfold eval_sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o)
apply(rule sc.red_mthr_deterministic[OF sc_deterministic_heap_ops])
apply(simp add: sc_spurious_wakeups)
done

subsection \<open>Random scheduler\<close>

interpretation J_rnd:
  sc_random_scheduler_base
    final_expr "sc_red_i_i_i_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P" convert_RA Jinja_output
  for P
.

definition sc_rnd_J_start_state :: "Random.seed \<Rightarrow> random_scheduler"
where "sc_rnd_J_start_state seed = seed"

definition exec_J_rnd ::
  "Random.seed \<Rightarrow> addr J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow>
  (thread_id \<times> (addr, thread_id) obs_event list,
   (addr, thread_id) locks \<times> ((thread_id, (addr expr \<times> addr locals) \<times> addr released_locks) rm \<times> heap) \<times>
   (thread_id, addr wait_set_status) rm \<times> thread_id rs) tllist"
where
  "exec_J_rnd seed P C M vs = J_rnd.exec P (sc_rnd_J_start_state seed) (sc_J_start_state_refine P C M vs)"

interpretation J_rnd:
  sc_random_scheduler
    final_expr "sc_red_i_i_i_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P" convert_RA Jinja_output
  for P
by(unfold_locales)

interpretation J_rnd:
  sc_scheduler
    final_expr "sc_red_i_i_i_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P" convert_RA
    "J_rnd.random_scheduler P" Jinja_output "pick_wakeup_via_sel (\<lambda>s P. rm_sel s (\<lambda>(k,v). P k v))" "\<lambda>_ _. True"
    UNIV
  for P
unfolding sc_scheduler_def
apply(rule J_rnd.random_scheduler_scheduler)
apply(unfold eval_sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o)
apply(rule sc.red_mthr_deterministic[OF sc_deterministic_heap_ops])
apply(simp add: sc_spurious_wakeups)
done

ML_val \<open>@{code exec_J_rr}\<close>

ML_val \<open>@{code exec_J_rnd}\<close>

end
