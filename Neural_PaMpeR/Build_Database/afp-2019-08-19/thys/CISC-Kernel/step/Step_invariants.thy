subsection \<open>Preconditions and invariants for the atomic step \label{sect:step_invariants}\<close>

theory Step_invariants
  imports Step
begin

text \<open>The dynamic/implementation policies have to be compatible with the static configuration.\<close>

definition "sp_subset s \<equiv>
   (\<forall> p1 p2 . sp_impl_subj_subj s p1 p2 \<longrightarrow> Policy.sp_spec_subj_subj p1 p2)
   \<and> (\<forall> p1 p2 m. sp_impl_subj_obj s p1 p2 m \<longrightarrow> Policy.sp_spec_subj_obj p1 p2 m)"

text \<open>The following predicate expresses the precondition for the atomic step. The precondition depends on the type of the atomic action.\<close>
(*
[SK_IPC dir PREP partner page,SK_IPC dir WAIT partner page,SK_IPC dir (BUF page') partner page]
*)
definition atomic_step_precondition :: "state_t \<Rightarrow> thread_id_t \<Rightarrow> int_point_t \<Rightarrow> bool" where
  "atomic_step_precondition s tid ipt \<equiv>
    case ipt of
       SK_IPC dir WAIT partner page \<Rightarrow>
         \<comment> \<open>the thread managed it past PREP stage\<close>
         ipc_precondition tid dir partner page s
     | SK_IPC dir (BUF page') partner page \<Rightarrow>
         \<comment> \<open>both the calling thread and its communication partner managed it past PREP and WAIT stages\<close>
         ipc_precondition tid dir partner page s
         \<and> ipc_precondition partner (opposite_ipc_direction dir) tid page' s
     | SK_EV_SIGNAL EV_SIGNAL_FINISH partner \<Rightarrow>
        ev_signal_precondition tid partner s 
     | _ \<Rightarrow>
         \<comment> \<open>No precondition for other interrupt points.\<close>
         True"

text \<open>The invariant to be preserved by the atomic step function. The invariant is independent from the type of the atomic action.\<close>

definition atomic_step_invariant :: "state_t \<Rightarrow> bool" where
  "atomic_step_invariant s \<equiv>
     sp_subset s"

subsubsection \<open>Atomic steps of SK\_IPC preserve invariants\<close>


lemma set_object_value_invariant:
  shows "atomic_step_invariant s = atomic_step_invariant (set_object_value ob va s)"
proof -
  show ?thesis
    unfolding atomic_step_invariant_def atomic_step_precondition_def ipc_precondition_def
      sp_subset_def set_object_value_def Let_def
    by (simp split: int_point_t.splits ipc_stage_t.splits ipc_direction_t.splits)
qed

lemma set_thread_value_invariant:
  shows "atomic_step_invariant s = atomic_step_invariant (s \<lparr> thread := thrst \<rparr>)"
proof -
  show ?thesis
    unfolding atomic_step_invariant_def atomic_step_precondition_def ipc_precondition_def
      sp_subset_def set_object_value_def Let_def
    by (simp split: int_point_t.splits ipc_stage_t.splits ipc_direction_t.splits)
qed

lemma atomic_ipc_preserves_invariants:
  fixes s :: state_t
    and tid :: thread_id_t
  assumes "atomic_step_invariant s"
  shows "atomic_step_invariant (atomic_step_ipc tid dir stage partner page s)"
proof -
  show ?thesis
    proof (cases stage)
    case PREP
      from this assms show ?thesis
        unfolding atomic_step_ipc_def atomic_step_invariant_def by auto
    next
    case WAIT
      from this assms show ?thesis
        unfolding atomic_step_ipc_def atomic_step_invariant_def by auto
    next
    case BUF
      show ?thesis
        using assms BUF set_object_value_invariant
        unfolding atomic_step_ipc_def
        by (simp split: ipc_direction_t.splits)
    qed
qed

lemma atomic_ev_wait_one_preserves_invariants:
  fixes s :: state_t
    and tid :: thread_id_t
  assumes "atomic_step_invariant s"
  shows "atomic_step_invariant (atomic_step_ev_wait_one tid s)"
  proof -
   from assms show ?thesis
   unfolding atomic_step_ev_wait_one_def atomic_step_invariant_def sp_subset_def
   by auto  
 qed

lemma atomic_ev_wait_all_preserves_invariants:
  fixes s :: state_t
    and tid :: thread_id_t
  assumes "atomic_step_invariant s"
  shows "atomic_step_invariant (atomic_step_ev_wait_all tid s)"
  proof -
   from assms show ?thesis
   unfolding atomic_step_ev_wait_all_def atomic_step_invariant_def sp_subset_def
   by auto  
 qed

lemma atomic_ev_signal_preserves_invariants:
  fixes s :: state_t
    and tid :: thread_id_t
  assumes "atomic_step_invariant s"
  shows "atomic_step_invariant (atomic_step_ev_signal tid  partner s)"
  proof -
   from assms show ?thesis
   unfolding atomic_step_ev_signal_def atomic_step_invariant_def sp_subset_def
   by auto  
 qed

subsubsection \<open>Summary theorems on atomic step invariants\<close>

text \<open>Now we are ready to show that an atomic step from the current interrupt point
        in any thread preserves invariants.\<close>

theorem atomic_step_preserves_invariants:
  fixes s :: state_t
    and tid :: thread_id_t
  assumes "atomic_step_invariant s"
  shows "atomic_step_invariant (atomic_step s a)"
proof (cases a)
  case SK_IPC 
    then show ?thesis unfolding atomic_step_def
    using assms atomic_ipc_preserves_invariants
    by simp
  next  case (SK_EV_WAIT ev_wait_stage consume)
    then show ?thesis 
    proof (cases consume)
     case EV_CONSUME_ALL
      then show ?thesis unfolding atomic_step_def
      using SK_EV_WAIT assms atomic_ev_wait_all_preserves_invariants
      by (simp split: ev_wait_stage_t.splits)
     next case EV_CONSUME_ONE
      then show ?thesis unfolding atomic_step_def
      using SK_EV_WAIT assms atomic_ev_wait_one_preserves_invariants
      by (simp split: ev_wait_stage_t.splits)
    qed
  next case SK_EV_SIGNAL
   then show ?thesis unfolding atomic_step_def
   using assms atomic_ev_signal_preserves_invariants  
   by (simp add: ev_signal_stage_t.splits)
  next case NONE
   then show ?thesis unfolding atomic_step_def
   using assms
   by auto  
qed

text \<open>Finally, the invariants do not depend on the current thread. That is, 
the context switch preserves the invariants, and an atomic step that is 
not a context switch does not change the current thread.\<close>

theorem cswitch_preserves_invariants:
  fixes s :: state_t
    and new_current :: thread_id_t
  assumes "atomic_step_invariant s"
  shows "atomic_step_invariant (s \<lparr> current := new_current \<rparr>)"
proof -
  let ?s1 = "s \<lparr> current := new_current \<rparr>"
  have "sp_subset s = sp_subset ?s1"
    unfolding sp_subset_def by auto
  from assms this show ?thesis
    unfolding atomic_step_invariant_def by metis
qed

theorem atomic_step_does_not_change_current_thread:
  shows "current (atomic_step s ipt) = current s"
proof -
  show ?thesis
    unfolding atomic_step_def
          and atomic_step_ipc_def
          and set_object_value_def Let_def
          and atomic_step_ev_wait_one_def atomic_step_ev_wait_all_def
          and atomic_step_ev_signal_def
    by (simp split: int_point_t.splits ipc_stage_t.splits ipc_direction_t.splits 
                        ev_consume_t.splits ev_wait_stage_t.splits ev_signal_stage_t.splits)
qed

end

