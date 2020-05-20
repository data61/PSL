(*  Title:      JinjaThreads/Execute/State_Refinement.thy
    Author:     Andreas Lochbihler
*)

chapter \<open>Schedulers\<close>

section \<open>Refinement for multithreaded states\<close>

theory State_Refinement
imports
  "../Framework/FWSemantics"
  "../Common/StartConfig"
begin

type_synonym
  ('l,'t,'m,'m_t,'m_w,'s_i) state_refine = "('l,'t) locks \<times> ('m_t \<times> 'm) \<times> 'm_w \<times> 's_i"

locale state_refine_base =
  fixes final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
begin

fun state_\<alpha> :: "('l,'t,'m,'m_t,'m_w, 's_i) state_refine \<Rightarrow> ('l,'t,'x,'m,'w) state"
where "state_\<alpha> (ls, (ts, m), ws, is) = (ls, (thr_\<alpha> ts, m), ws_\<alpha> ws, is_\<alpha> is)"

lemma state_\<alpha>_conv [simp]:
  "locks (state_\<alpha> s) = locks s"
  "thr (state_\<alpha> s) = thr_\<alpha> (thr s)"
  "shr (state_\<alpha> s) = shr s"
  "wset (state_\<alpha> s) = ws_\<alpha> (wset s)"
  "interrupts (state_\<alpha> s) = is_\<alpha> (interrupts s)"
by(case_tac [!] s) auto

inductive state_invar :: "('l,'t,'m,'m_t,'m_w,'s_i) state_refine \<Rightarrow> bool"
where "\<lbrakk> thr_invar ts; ws_invar ws; is_invar is \<rbrakk> \<Longrightarrow> state_invar (ls, (ts, m), ws, is)"

inductive_simps state_invar_simps [simp]:
  "state_invar (ls, (ts, m), ws, is)"

lemma state_invarD [simp]:
  assumes "state_invar s"
  shows "thr_invar (thr s)" "ws_invar (wset s)" "is_invar (interrupts s)"
using assms by(case_tac [!] s) auto

end

sublocale state_refine_base < \<alpha>: final_thread final .
sublocale state_refine_base < \<alpha>:
  multithreaded_base
    final
    "\<lambda>t xm ta x'm'. Predicate.eval (r t xm) (ta, x'm')"
.

definition (in heap_base) start_state_refine :: 
  "'m_t \<Rightarrow> ('thread_id \<Rightarrow> ('x \<times> 'addr released_locks) \<Rightarrow> 'm_t \<Rightarrow> 'm_t) \<Rightarrow> 'm_w \<Rightarrow> 's_i
  \<Rightarrow> (cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'md \<Rightarrow> 'addr val list \<Rightarrow> 'x) \<Rightarrow> 'md prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> 'addr val list
  \<Rightarrow> ('addr, 'thread_id, 'heap, 'm_t, 'm_w, 's_i) state_refine"
where
  "\<And>is_empty.
  start_state_refine thr_empty thr_update ws_empty is_empty f P C M vs =
  (let (D, Ts, T, m) = method P C M
   in (K$ None, (thr_update start_tid (f D M Ts T (the m) vs, no_wait_locks) thr_empty, start_heap), ws_empty, is_empty))"

definition Jinja_output :: 
  "'s \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'thread_id, 'x, 'heap, 'addr, ('addr, 'thread_id) obs_event) thread_action 
  \<Rightarrow> ('thread_id \<times> ('addr, 'thread_id) obs_event list) option"
where "Jinja_output \<sigma> t ta = (if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = [] then None else Some (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"

lemmas [code] =
  heap_base.start_state_refine_def

end
