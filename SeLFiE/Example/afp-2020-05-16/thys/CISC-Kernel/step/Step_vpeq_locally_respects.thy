subsection \<open>Atomic step locally respects the information flow policy\<close>

theory Step_vpeq_locally_respects
  imports Step Step_invariants Step_vpeq
begin

text \<open>The notion of locally respects is common usage. We augment it by assuming that the @{term atomic_step_invariant} holds (see~\cite{Verbeek2013}).\<close>

subsubsection \<open>Locally respects of atomic step functions\<close>
lemma ipc_respects_policy:
  assumes no: "\<not> Policy.ifp (partition tid) u"
    and inv: "atomic_step_invariant s"
    and prec: "atomic_step_precondition s tid (SK_IPC dir stage partner pag)"
    and ipt_case: "ipt = SK_IPC dir stage partner page"
  shows "vpeq u s (atomic_step_ipc tid dir stage partner page s)"
  proof(cases stage)
   case PREP
    thus ?thesis
    unfolding atomic_step_ipc_def
    using vpeq_refl by simp
   next
    case WAIT
    thus ?thesis
    unfolding atomic_step_ipc_def
    using vpeq_refl by simp
   next case (BUF mypage)
    show ?thesis
    proof(cases dir)
    case RECV
     thus ?thesis
     unfolding atomic_step_ipc_def
     using vpeq_refl BUF by simp
    next
    case SEND
      have "Policy.sp_spec_subj_subj (partition tid) (partition partner)"
       and "Policy.sp_spec_subj_obj (partition partner) (PAGE mypage) WRITE"
        using BUF SEND inv prec ipt_case
        unfolding atomic_step_invariant_def sp_subset_def
        unfolding atomic_step_precondition_def ipc_precondition_def opposite_ipc_direction_def
        by auto
      hence "\<not> Policy.sp_spec_subj_obj u (PAGE mypage) READ"
        using no Policy_properties.ifp_compatible_with_ipc
        by auto
      thus ?thesis
        using BUF SEND assms
        unfolding atomic_step_ipc_def set_object_value_def
        unfolding vpeq_def vpeq_obj_def vpeq_subj_obj_def vpeq_subj_subj_def vpeq_local_def
        by auto
    qed
   qed

lemma ev_signal_respects_policy:
  assumes no: "\<not> Policy.ifp (partition tid) u"
    and inv: "atomic_step_invariant s"
    and prec: "atomic_step_precondition s tid (SK_EV_SIGNAL EV_SIGNAL_FINISH partner)"
    and ipt_case: "ipt = SK_EV_SIGNAL EV_SIGNAL_FINISH partner"
  shows "vpeq u s (atomic_step_ev_signal tid partner s)"
 proof -
  from inv no have "\<not> sp_impl_subj_subj s (partition tid) u"
   unfolding Policy.ifp_def atomic_step_invariant_def sp_subset_def
   by auto
  with prec have 1:"(partition partner) \<noteq> u"
  unfolding atomic_step_precondition_def ev_signal_precondition_def
    by (auto simp add: ev_signal_stage_t.splits)
  then have 2:"vpeq_local u s (atomic_step_ev_signal tid partner s)"
  unfolding vpeq_local_def atomic_step_ev_signal_def
   by simp
  have 3:"vpeq_obj u s (atomic_step_ev_signal tid partner s)"
  unfolding vpeq_obj_def atomic_step_ev_signal_def
   by simp
  have 4:"vpeq_subj_subj u s (atomic_step_ev_signal tid partner s)"
  unfolding vpeq_subj_subj_def atomic_step_ev_signal_def
   by simp
  have 5:"vpeq_subj_obj u s (atomic_step_ev_signal tid partner s)"
  unfolding vpeq_subj_obj_def atomic_step_ev_signal_def
   by simp
  with 2 3 4 5 show ?thesis
  unfolding vpeq_def 
   by simp
qed

lemma ev_wait_all_respects_policy:
  assumes no: "\<not> Policy.ifp (partition tid) u"
    and inv: "atomic_step_invariant s"
    and prec: "atomic_step_precondition s tid ipt"
    and ipt_case: "ipt = SK_EV_WAIT ev_wait_stage EV_CONSUME_ALL"
  shows "vpeq u s (atomic_step_ev_wait_all tid s)"
  proof -
  from assms have 1:"(partition tid) \<noteq> u"
  unfolding Policy.ifp_def
   by simp
  then have 2:"vpeq_local u s (atomic_step_ev_wait_all tid s)"
  unfolding vpeq_local_def atomic_step_ev_wait_all_def
   by simp
  have 3:"vpeq_obj u s (atomic_step_ev_wait_all tid s)"
  unfolding vpeq_obj_def atomic_step_ev_wait_all_def
   by simp
  have 4:"vpeq_subj_subj u s (atomic_step_ev_wait_all tid s)"
  unfolding vpeq_subj_subj_def atomic_step_ev_wait_all_def
   by simp
  have 5:"vpeq_subj_obj u s (atomic_step_ev_wait_all tid s)"
  unfolding vpeq_subj_obj_def atomic_step_ev_wait_all_def
   by simp
  with 2 3 4 5 show ?thesis
  unfolding vpeq_def 
   by simp
qed

lemma ev_wait_one_respects_policy:
  assumes no: "\<not> Policy.ifp (partition tid) u"
    and inv: "atomic_step_invariant s"
    and prec: "atomic_step_precondition s tid ipt"
    and ipt_case: "ipt = SK_EV_WAIT ev_wait_stage EV_CONSUME_ONE"
  shows "vpeq u s (atomic_step_ev_wait_one tid s)"
 proof -
  from assms have 1:"(partition tid) \<noteq> u"
  unfolding Policy.ifp_def
   by simp
  then have 2:"vpeq_local u s (atomic_step_ev_wait_one tid s)"
  unfolding vpeq_local_def atomic_step_ev_wait_one_def
   by simp
  have 3:"vpeq_obj u s (atomic_step_ev_wait_one tid s)"
  unfolding vpeq_obj_def atomic_step_ev_wait_one_def
   by simp
  have 4:"vpeq_subj_subj u s (atomic_step_ev_wait_one tid s)"
  unfolding vpeq_subj_subj_def atomic_step_ev_wait_one_def
   by simp
  have 5:"vpeq_subj_obj u s (atomic_step_ev_wait_one tid s)"
  unfolding vpeq_subj_obj_def atomic_step_ev_wait_one_def
   by simp
  with 2 3 4 5 show ?thesis
  unfolding vpeq_def 
   by simp
qed


subsubsection \<open>Summary theorems on view-partitioning locally respects\<close>

text \<open>Atomic step locally respects the information flow policy (ifp). The policy ifp is not necessarily the same
  as sp\_spec\_subj\_subj.\<close>

theorem atomic_step_respects_policy:
  assumes no: "\<not> Policy.ifp (partition (current s)) u"
      and inv: "atomic_step_invariant s"
      and prec: "atomic_step_precondition s (current s) ipt"
   shows "vpeq u s (atomic_step s ipt)"
proof -
  show ?thesis
    using assms ipc_respects_policy vpeq_refl
                ev_signal_respects_policy ev_wait_one_respects_policy
                ev_wait_all_respects_policy
    unfolding atomic_step_def
    by (auto split: int_point_t.splits ev_consume_t.splits ev_wait_stage_t.splits ev_signal_stage_t.splits)
qed

end

