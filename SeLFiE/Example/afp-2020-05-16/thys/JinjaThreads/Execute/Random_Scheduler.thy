(*  Title:      JinjaThreads/Execute/Random_Scheduler.thy
    Author:     Andreas Lochbihler
*)

section \<open>Random scheduler\<close>

theory Random_Scheduler
imports
  Scheduler
begin

type_synonym random_scheduler = Random.seed

abbreviation (input)
  random_scheduler_invar :: "random_scheduler \<Rightarrow> 't set \<Rightarrow> bool"
where "random_scheduler_invar \<equiv> \<lambda>_ _. True"

locale random_scheduler_base =
  scheduler_ext_base
    final r convert_RA
    thr_\<alpha> thr_invar thr_lookup thr_update thr_iterate
    ws_\<alpha> ws_invar ws_lookup ws_update ws_sel
    is_\<alpha> is_invar is_memb is_ins is_delete
    thr'_\<alpha> thr'_invar thr'_empty thr'_ins_dj
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and "output" :: "random_scheduler \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'q option"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and thr_lookup :: "'t \<Rightarrow> 'm_t \<rightharpoonup> ('x \<times> 'l released_locks)"
  and thr_update :: "'t \<Rightarrow> 'x \<times> 'l released_locks \<Rightarrow> 'm_t \<Rightarrow> 'm_t"
  and thr_iterate :: "'m_t \<Rightarrow> ('t \<times> ('x \<times> 'l released_locks), 's_t) set_iterator"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and ws_lookup :: "'t \<Rightarrow> 'm_w \<rightharpoonup> 'w wait_set_status"
  and ws_update :: "'t \<Rightarrow> 'w wait_set_status \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_delete :: "'t \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_iterate :: "'m_w \<Rightarrow> ('t \<times> 'w wait_set_status, 'm_w) set_iterator"
  and ws_sel :: "'m_w \<Rightarrow> ('t \<times> 'w wait_set_status \<Rightarrow> bool) \<rightharpoonup> ('t \<times> 'w wait_set_status)"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
  and is_memb :: "'t \<Rightarrow> 's_i \<Rightarrow> bool"
  and is_ins :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and is_delete :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and thr'_\<alpha> :: "'s_t \<Rightarrow> 't set"
  and thr'_invar :: "'s_t \<Rightarrow> bool"
  and thr'_empty :: "unit \<Rightarrow> 's_t"
  and thr'_ins_dj :: "'t \<Rightarrow> 's_t \<Rightarrow> 's_t"
  +
  fixes thr'_to_list :: "'s_t \<Rightarrow> 't list"
begin

definition next_thread :: "random_scheduler \<Rightarrow> 's_t \<Rightarrow> ('t \<times> random_scheduler) option"
where
  "next_thread seed active = 
  (let ts = thr'_to_list active
   in if ts = [] then None else Some (Random.select (thr'_to_list active) seed))"

definition random_scheduler :: "('l,'t,'x,'m,'w,'o,'m_t,'m_w,'s_i,random_scheduler) scheduler"
where
  "random_scheduler seed s =
   (do {
      (t, seed') \<leftarrow> next_thread seed (active_threads s);
      step_thread (\<lambda>ta. seed') s t
   })"

end

locale random_scheduler =
  random_scheduler_base
    final r convert_RA "output"
    thr_\<alpha> thr_invar thr_lookup thr_update thr_iterate
    ws_\<alpha> ws_invar ws_lookup ws_update ws_delete ws_iterate ws_sel
    is_\<alpha> is_invar is_memb is_ins is_delete
    thr'_\<alpha> thr'_invar thr'_empty thr'_ins_dj thr'_to_list
  +
  scheduler_ext_aux
    final r convert_RA
    thr_\<alpha> thr_invar thr_lookup thr_update thr_iterate
    ws_\<alpha> ws_invar ws_lookup ws_update ws_sel
    is_\<alpha> is_invar is_memb is_ins is_delete
    thr'_\<alpha> thr'_invar thr'_empty thr'_ins_dj
  +
  ws: map_delete ws_\<alpha> ws_invar ws_delete +
  ws: map_iteratei ws_\<alpha> ws_invar ws_iterate +
  thr': set_to_list thr'_\<alpha> thr'_invar thr'_to_list 
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and "output" :: "random_scheduler \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'q option"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and thr_lookup :: "'t \<Rightarrow> 'm_t \<rightharpoonup> ('x \<times> 'l released_locks)"
  and thr_update :: "'t \<Rightarrow> 'x \<times> 'l released_locks \<Rightarrow> 'm_t \<Rightarrow> 'm_t"
  and thr_iterate :: "'m_t \<Rightarrow> ('t \<times> ('x \<times> 'l released_locks), 's_t) set_iterator"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and ws_lookup :: "'t \<Rightarrow> 'm_w \<rightharpoonup> 'w wait_set_status"
  and ws_update :: "'t \<Rightarrow> 'w wait_set_status \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_delete :: "'t \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_iterate :: "'m_w \<Rightarrow> ('t \<times> 'w wait_set_status, 'm_w) set_iterator"
  and ws_sel :: "'m_w \<Rightarrow> ('t \<times> 'w wait_set_status \<Rightarrow> bool) \<rightharpoonup> ('t \<times> 'w wait_set_status)"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
  and is_memb :: "'t \<Rightarrow> 's_i \<Rightarrow> bool"
  and is_ins :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and is_delete :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and thr'_\<alpha> :: "'s_t \<Rightarrow> 't set"
  and thr'_invar :: "'s_t \<Rightarrow> bool"
  and thr'_empty :: "unit \<Rightarrow> 's_t"
  and thr'_ins_dj :: "'t \<Rightarrow> 's_t \<Rightarrow> 's_t"
  and thr'_to_list :: "'s_t \<Rightarrow> 't list"
begin

lemma next_thread_eq_None_iff:
  assumes "thr'_invar active" "random_scheduler_invar seed T"
  shows "next_thread seed active = None \<longleftrightarrow> thr'_\<alpha> active = {}"
using thr'.to_list_correct[OF assms(1)]
by(auto simp add: next_thread_def neq_Nil_conv)

lemma next_thread_eq_SomeD:
  assumes "next_thread seed active = Some (t, seed')"
  and "thr'_invar active" "random_scheduler_invar seed T"
  shows "t \<in> thr'_\<alpha> active"
using assms
by(auto simp add: next_thread_def thr'.to_list_correct split: if_split_asm dest: select[of _ seed])

lemma random_scheduler_spec:
  assumes det: "\<alpha>.deterministic I"
  shows "scheduler_spec final r random_scheduler random_scheduler_invar thr_\<alpha> thr_invar ws_\<alpha> ws_invar is_\<alpha> is_invar I"
proof
  fix \<sigma> s
  assume rr: "random_scheduler \<sigma> s = None"
    and invar: "random_scheduler_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_invar s" "state_\<alpha> s \<in> I"
  from invar(2) have "thr'_invar (active_threads s)" by(rule active_threads_correct)
  thus "\<alpha>.active_threads (state_\<alpha> s) = {}" using rr invar
    by(auto simp add: random_scheduler_def Option_bind_eq_None_conv next_thread_eq_None_iff step_thread_eq_None_conv[OF det] dest: next_thread_eq_SomeD)
next
  fix \<sigma> s t \<sigma>'
  assume rr: "random_scheduler \<sigma> s = \<lfloor>(t, None, \<sigma>')\<rfloor>"
    and invar: "random_scheduler_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_invar s" "state_\<alpha> s \<in> I"
  thus "\<exists>x ln n. thr_\<alpha> (thr s) t = \<lfloor>(x, ln)\<rfloor> \<and> 0 < ln $ n \<and> \<not> waiting (ws_\<alpha> (wset s) t) \<and> may_acquire_all (locks s) t ln"
    by(fastforce simp add: random_scheduler_def Option_bind_eq_Some_conv dest: step_thread_Some_NoneD[OF det])
next
  fix \<sigma> s t ta x' m' \<sigma>'
  assume rr: "random_scheduler \<sigma> s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
    and invar: "random_scheduler_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_invar s" "state_\<alpha> s \<in> I"
  thus "\<exists>x. thr_\<alpha> (thr s) t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> Predicate.eval (r t (x, shr s)) (ta, x', m') \<and> \<alpha>.actions_ok (state_\<alpha> s) t ta"
    by(auto simp add: random_scheduler_def Option_bind_eq_Some_conv dest: step_thread_Some_SomeD[OF det])
qed simp_all

end

sublocale random_scheduler_base <
  scheduler_base
    final r convert_RA
    "random_scheduler" "output" "pick_wakeup_via_sel (\<lambda>s P. ws_sel s (\<lambda>(k,v). P k v))" random_scheduler_invar
    thr_\<alpha> thr_invar thr_lookup thr_update
    ws_\<alpha> ws_invar ws_lookup ws_update ws_delete ws_iterate
    is_\<alpha> is_invar is_memb is_ins is_delete
  for n0 .

sublocale random_scheduler <
  pick_wakeup_spec
    final r convert_RA
    "pick_wakeup_via_sel (\<lambda>s P. ws_sel s (\<lambda>(k,v). P k v))" random_scheduler_invar
    thr_\<alpha> thr_invar
    ws_\<alpha> ws_invar
    is_\<alpha> is_invar
by(rule pick_wakeup_spec_via_sel)(unfold_locales)

context random_scheduler begin

lemma random_scheduler_scheduler:
  assumes det: "\<alpha>.deterministic I"
  shows 
  "scheduler
     final r convert_RA
     random_scheduler (pick_wakeup_via_sel (\<lambda>s P. ws_sel s (\<lambda>(k,v). P k v))) random_scheduler_invar
     thr_\<alpha> thr_invar thr_lookup thr_update 
     ws_\<alpha> ws_invar ws_lookup ws_update ws_delete ws_iterate
     is_\<alpha> is_invar is_memb is_ins is_delete
     I"
proof -
  interpret scheduler_spec
      final r convert_RA
      random_scheduler random_scheduler_invar
      thr_\<alpha> thr_invar
      ws_\<alpha> ws_invar
      is_\<alpha> is_invar
      I
    using det by(rule random_scheduler_spec)

  show ?thesis by(unfold_locales)(rule \<alpha>.deterministic_invariant3p[OF det])
qed

end

subsection \<open>Code generator setup\<close>

lemmas [code] =
  random_scheduler_base.next_thread_def
  random_scheduler_base.random_scheduler_def

end
