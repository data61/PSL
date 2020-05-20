theory SC_Schedulers
imports
  Random_Scheduler
  Round_Robin
  "../MM/SC_Collections"
  (*
  "../../Collections/impl/RBTMapImpl"
  "../../Collections/impl/RBTSetImpl"
  "../../Collections/impl/Fifo"
  "../../Collections/impl/ListSetImpl_Invar"
  *)
  "../Basic/JT_ICF"
  
begin

abbreviation sc_start_state_refine ::
  "'m_t \<Rightarrow> (thread_id \<Rightarrow> ('x \<times> addr released_locks) \<Rightarrow> 'm_t \<Rightarrow> 'm_t) \<Rightarrow> 'm_w \<Rightarrow> 's_i
  \<Rightarrow> (cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'md \<Rightarrow> addr val list \<Rightarrow> 'x) \<Rightarrow> 'md prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list
  \<Rightarrow> (addr, thread_id, heap, 'm_t, 'm_w, 's_i) state_refine"
where
  "\<And>is_empty.
   sc_start_state_refine thr_empty thr_update ws_empty is_empty f P \<equiv>
   heap_base.start_state_refine addr2thread_id sc_empty (sc_allocate P) thr_empty thr_update ws_empty is_empty f P"

abbreviation sc_state_\<alpha> ::
  "('l, 't :: linorder, 'm, ('t, 'x \<times> 'l \<Rightarrow>f nat) rm, ('t, 'w wait_set_status) rm, 't rs) state_refine
  \<Rightarrow> ('l,'t,'x,'m,'w) state"
where "sc_state_\<alpha> \<equiv> state_refine_base.state_\<alpha> rm_\<alpha> rm_\<alpha> rs_\<alpha>"

lemma sc_state_\<alpha>_sc_start_state_refine [simp]:
  "sc_state_\<alpha> (sc_start_state_refine (rm_empty ()) rm_update (rm_empty ()) (rs_empty ()) f P C M vs) = sc_start_state f P C M vs"
by(simp add: heap_base.start_state_refine_def state_refine_base.state_\<alpha>.simps split_beta sc.start_state_def rm_correct rs_correct)

locale sc_scheduler =
  scheduler
    final r convert_RA 
    schedule "output" pick_wakeup \<sigma>_invar
    rm_\<alpha> rm_invar rm_lookup rm_update
    rm_\<alpha> rm_invar rm_lookup rm_update rm_delete rm_iteratei
    rs_\<alpha> rs_invar rs_memb rs_ins rs_delete
    invariant
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t :: linorder,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and schedule :: "('l,'t,'x,'m,'w,'o,('t, 'x \<times> 'l \<Rightarrow>f nat) rm,('t, 'w wait_set_status) rm, 't rs, 's) scheduler"
  and "output" :: "'s \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'q option"
  and pick_wakeup :: "'s \<Rightarrow> 't \<Rightarrow> 'w \<Rightarrow> ('t, 'w wait_set_status) RBT.rbt \<Rightarrow> 't option"
  and \<sigma>_invar :: "'s \<Rightarrow> 't set \<Rightarrow> bool"
  and invariant :: "('l,'t,'x,'m,'w) state set"

locale sc_round_robin_base =
  round_robin_base
    final r convert_RA "output"
    rm_\<alpha> rm_invar rm_lookup rm_update 
    rm_\<alpha> rm_invar rm_lookup rm_update rm_delete rm_iteratei rm_sel
    rs_\<alpha> rs_invar rs_memb rs_ins rs_delete
    fifo_\<alpha> fifo_invar fifo_empty fifo_isEmpty fifo_enqueue fifo_dequeue fifo_push
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t :: linorder,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and "output" :: "'t fifo round_robin \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'q option"

locale sc_round_robin =
  round_robin 
    final r convert_RA "output"
    rm_\<alpha> rm_invar rm_lookup rm_update 
    rm_\<alpha> rm_invar rm_lookup rm_update rm_delete rm_iteratei rm_sel
    rs_\<alpha> rs_invar rs_memb rs_ins rs_delete
    fifo_\<alpha> fifo_invar fifo_empty fifo_isEmpty fifo_enqueue fifo_dequeue fifo_push
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t :: linorder,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and "output" :: "'t fifo round_robin \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'q option"

sublocale sc_round_robin < sc_round_robin_base .

locale sc_random_scheduler_base =
  random_scheduler_base
    final r convert_RA "output"
    rm_\<alpha> rm_invar rm_lookup rm_update rm_iteratei 
    rm_\<alpha> rm_invar rm_lookup rm_update rm_delete rm_iteratei rm_sel
    rs_\<alpha> rs_invar rs_memb rs_ins rs_delete
    lsi_\<alpha> lsi_invar lsi_empty lsi_ins_dj lsi_to_list
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t :: linorder,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and "output" :: "random_scheduler \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'q option"

locale sc_random_scheduler =
  random_scheduler
    final r convert_RA "output"
    rm_\<alpha> rm_invar rm_lookup rm_update rm_iteratei 
    rm_\<alpha> rm_invar rm_lookup rm_update rm_delete rm_iteratei rm_sel
    rs_\<alpha> rs_invar rs_memb rs_ins rs_delete
    lsi_\<alpha> lsi_invar lsi_empty lsi_ins_dj lsi_to_list
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t :: linorder,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and "output" :: "random_scheduler \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'q option"

sublocale sc_random_scheduler < sc_random_scheduler_base .

text \<open>No spurious wake-ups in generated code\<close>
overloading sc_spurious_wakeups \<equiv> sc_spurious_wakeups
begin
  definition sc_spurious_wakeups [code]: "sc_spurious_wakeups \<equiv> False"
end

end
