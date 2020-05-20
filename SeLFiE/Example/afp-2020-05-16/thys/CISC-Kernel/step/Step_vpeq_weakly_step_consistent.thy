subsection \<open>Weak step consistency\<close>

theory Step_vpeq_weakly_step_consistent
  imports Step Step_invariants Step_vpeq
begin


text \<open>The notion of weak step consistency is common usage. We augment it by assuming that the @{term atomic_step_invariant} holds (see~\cite{Verbeek2013}).\<close>

subsubsection \<open>Weak step consistency of auxiliary functions\<close>

lemma ipc_precondition_weakly_step_consistent:
  assumes eq_tid: "vpeq (partition tid) s1 s2"
      and inv1: "atomic_step_invariant s1"
      and inv2: "atomic_step_invariant s2"
    shows "ipc_precondition tid dir partner page s1 = ipc_precondition tid dir partner page s2"
proof -
  let ?sender = "case dir of SEND \<Rightarrow> tid | RECV \<Rightarrow> partner"
  let ?receiver = "case dir of SEND \<Rightarrow> partner | RECV \<Rightarrow> tid"
  let ?local_access_mode = "case dir of SEND \<Rightarrow> READ | RECV \<Rightarrow> WRITE"
  let ?A = "sp_impl_subj_subj s1 (partition ?sender) (partition ?receiver)
             = sp_impl_subj_subj s2 (partition ?sender) (partition ?receiver)"
  let ?B = "sp_impl_subj_obj s1 (partition tid) (PAGE page) ?local_access_mode
         = sp_impl_subj_obj s2 (partition tid) (PAGE page) ?local_access_mode"
 
  have A: "?A"
    proof (cases "Policy.sp_spec_subj_subj (partition ?sender) (partition ?receiver)")
      case True
        thus ?A
          using eq_tid unfolding vpeq_def vpeq_subj_subj_def
          by (simp split: ipc_direction_t.splits)
      next case False
        have "sp_subset s1" and "sp_subset s2"
          using inv1 inv2 unfolding atomic_step_invariant_def sp_subset_def by auto
        hence "\<not> sp_impl_subj_subj s1 (partition ?sender) (partition ?receiver)"
          and "\<not> sp_impl_subj_subj s2 (partition ?sender) (partition ?receiver)"
          using False unfolding sp_subset_def by auto 
        thus ?A by auto
    qed
  have B: "?B"
    proof (cases "Policy.sp_spec_subj_obj (partition tid) (PAGE page) ?local_access_mode")
      case True
        thus ?B
          using eq_tid unfolding vpeq_def vpeq_subj_obj_def
          by (simp split: ipc_direction_t.splits)
      next case False
        have "sp_subset s1" and "sp_subset s2"
          using inv1 inv2 unfolding atomic_step_invariant_def sp_subset_def by auto
        hence "\<not> sp_impl_subj_obj s1 (partition tid) (PAGE page) ?local_access_mode"
          and "\<not> sp_impl_subj_obj s2 (partition tid) (PAGE page) ?local_access_mode"
          using False unfolding sp_subset_def by auto 
        thus ?B by auto
    qed
  show ?thesis using A B unfolding ipc_precondition_def by auto
qed

lemma ev_signal_precondition_weakly_step_consistent:
  assumes eq_tid: "vpeq (partition tid) s1 s2"
      and inv1: "atomic_step_invariant s1"
      and inv2: "atomic_step_invariant s2"
    shows "ev_signal_precondition tid partner s1 = ev_signal_precondition tid partner s2"
proof -
  let ?A = "sp_impl_subj_subj s1 (partition tid) (partition partner)
             = sp_impl_subj_subj s2 (partition tid) (partition partner)"
  have A: "?A"
    proof (cases "Policy.sp_spec_subj_subj (partition tid) (partition partner)")
      case True
        thus ?A
          using eq_tid unfolding vpeq_def vpeq_subj_subj_def
          by (simp split: ipc_direction_t.splits)
      next case False
        have "sp_subset s1" and "sp_subset s2"
          using inv1 inv2 unfolding atomic_step_invariant_def sp_subset_def by auto
        hence "\<not> sp_impl_subj_subj s1 (partition tid) (partition partner)"
          and "\<not> sp_impl_subj_subj s2 (partition tid) (partition partner)"
          using False unfolding sp_subset_def by auto 
        thus ?A by auto
    qed
  show ?thesis using A unfolding ev_signal_precondition_def by auto
qed


lemma set_object_value_consistent:
  assumes eq_obs: "vpeq u s1 s2"
    shows "vpeq u (set_object_value x y s1) (set_object_value x y s2)"
proof -
  let ?s1' = "set_object_value x y s1" and ?s2' = "set_object_value x y s2"
  have E1: "vpeq_obj u ?s1' ?s2'"
    proof -
      { fix x'
        assume 1: "Policy.sp_spec_subj_obj u x' READ"
        have "obj ?s1' x' = obj ?s2' x'" proof (cases "x = x'")
          case True
            thus "obj ?s1' x' = obj ?s2' x'" unfolding set_object_value_def by auto
          next case False
            hence 2: "obj ?s1' x' = obj s1 x'"
              and 3: "obj ?s2' x' = obj s2 x'"
              unfolding set_object_value_def by auto
            have 4: "obj s1 x' = obj s2 x'"
              using 1 eq_obs unfolding vpeq_def vpeq_obj_def by auto
            from 2 3 4 show "obj ?s1' x' = obj ?s2' x'"
              by simp
          qed }
      thus "vpeq_obj u ?s1' ?s2'" unfolding vpeq_obj_def by auto
    qed
  have E4: "vpeq_subj_subj u ?s1' ?s2'"
    proof -
      have "sp_impl_subj_subj ?s1' = sp_impl_subj_subj s1"
       and "sp_impl_subj_subj ?s2' = sp_impl_subj_subj s2"
        unfolding set_object_value_def by auto
      thus "vpeq_subj_subj u ?s1' ?s2'"
        using eq_obs unfolding vpeq_def vpeq_subj_subj_def by auto
    qed
  have E5: "vpeq_subj_obj u ?s1' ?s2'"
    proof -
      have "sp_impl_subj_obj ?s1' = sp_impl_subj_obj s1"
       and "sp_impl_subj_obj ?s2' = sp_impl_subj_obj s2"
        unfolding set_object_value_def by auto
      thus "vpeq_subj_obj u ?s1' ?s2'"
        using eq_obs unfolding vpeq_def vpeq_subj_obj_def by auto
    qed
  from eq_obs have E6: "vpeq_local u ?s1' ?s2'"
  unfolding vpeq_def vpeq_local_def set_object_value_def
   by simp
  from E1 E4 E5 E6
    show ?thesis unfolding vpeq_def 
    by auto
qed

subsubsection \<open>Weak step consistency of atomic step functions\<close>

lemma ipc_weakly_step_consistent:
  assumes eq_obs: "vpeq u s1 s2"
      and eq_act: "vpeq (partition tid) s1 s2"
      and inv1:   "atomic_step_invariant s1"
      and inv2:   "atomic_step_invariant s2"
      and prec1: "atomic_step_precondition s1 tid ipt"
      and prec2: "atomic_step_precondition s1 tid ipt"
      and ipt_case: "ipt = SK_IPC dir stage partner page"
    shows "vpeq u
                (atomic_step_ipc tid dir stage partner page s1)
                (atomic_step_ipc tid dir stage partner page s2)"
proof -
  have "\<And> mypage . \<lbrakk> dir = SEND; stage = BUF mypage \<rbrakk> \<Longrightarrow> ?thesis"
    proof -
      fix mypage
      assume dir_send: "dir = SEND"
      assume stage_buf: "stage = BUF mypage"
      have "Policy.sp_spec_subj_obj (partition tid) (PAGE page) READ"
        using inv1 prec1 dir_send stage_buf ipt_case
        unfolding atomic_step_invariant_def sp_subset_def
        unfolding atomic_step_precondition_def ipc_precondition_def opposite_ipc_direction_def
        by auto
      hence "obj s1 (PAGE page) = obj s2 (PAGE page)"
        using eq_act unfolding vpeq_def vpeq_obj_def vpeq_local_def
        by auto        
      thus "vpeq u
                (atomic_step_ipc tid dir stage partner page s1)
                (atomic_step_ipc tid dir stage partner page s2)"
        using dir_send stage_buf eq_obs set_object_value_consistent
        unfolding atomic_step_ipc_def
        by auto
    qed
  thus ?thesis
    using eq_obs unfolding atomic_step_ipc_def
    by (cases "stage", auto, cases "dir", auto)
qed

lemma ev_wait_one_weakly_step_consistent:
  assumes eq_obs: "vpeq u s1 s2"
      and eq_act: "vpeq (partition tid) s1 s2"
      and inv1:   "atomic_step_invariant s1"
      and inv2:   "atomic_step_invariant s2"
      and prec1: "atomic_step_precondition s1 (current s1) ipt"
      and prec2: "atomic_step_precondition s1 (current s1) ipt"
    shows "vpeq u
                (atomic_step_ev_wait_one tid  s1)
                (atomic_step_ev_wait_one tid  s2)"
    using assms
    unfolding vpeq_def vpeq_subj_subj_def vpeq_obj_def vpeq_subj_obj_def vpeq_local_def
              atomic_step_ev_wait_one_def
    by simp
    
lemma ev_wait_all_weakly_step_consistent:
  assumes eq_obs: "vpeq u s1 s2"
      and eq_act: "vpeq (partition tid) s1 s2"
      and inv1:   "atomic_step_invariant s1"
      and inv2:   "atomic_step_invariant s2"
      and prec1: "atomic_step_precondition s1 (current s1) ipt"
      and prec2: "atomic_step_precondition s1 (current s1) ipt"
    shows "vpeq u
                (atomic_step_ev_wait_all tid  s1)
                (atomic_step_ev_wait_all tid  s2)"
    using assms
    unfolding vpeq_def vpeq_subj_subj_def vpeq_obj_def vpeq_subj_obj_def vpeq_local_def
              atomic_step_ev_wait_all_def
    by simp
   

lemma ev_signal_weakly_step_consistent:
  assumes eq_obs: "vpeq u s1 s2"
      and eq_act: "vpeq (partition tid) s1 s2"
      and inv1:   "atomic_step_invariant s1"
      and inv2:   "atomic_step_invariant s2"
      and prec1: "atomic_step_precondition s1 (current s1) ipt"
      and prec2: "atomic_step_precondition s1 (current s1) ipt"
    shows "vpeq u
                (atomic_step_ev_signal tid partner s1)
                (atomic_step_ev_signal tid partner s2)"
    using assms
    unfolding vpeq_def vpeq_subj_subj_def vpeq_obj_def vpeq_subj_obj_def vpeq_local_def
              atomic_step_ev_signal_def
    by simp

text \<open>The use of @{term extend_f} is to provide infrastructure to support use in dynamic policies, currently not used.\<close>
 
definition extend_f :: "(partition_id_t \<Rightarrow> partition_id_t \<Rightarrow> bool) \<Rightarrow> (partition_id_t \<Rightarrow> partition_id_t \<Rightarrow> bool) \<Rightarrow> (partition_id_t \<Rightarrow> partition_id_t \<Rightarrow> bool)" where
  "extend_f f g \<equiv> \<lambda> p1 p2 . f p1 p2 \<or> g p1 p2"

definition extend_subj_subj :: "(partition_id_t \<Rightarrow> partition_id_t \<Rightarrow> bool) \<Rightarrow> state_t \<Rightarrow> state_t" where
  "extend_subj_subj f s \<equiv> s \<lparr> sp_impl_subj_subj := extend_f f (sp_impl_subj_subj s) \<rparr>"
  
lemma extend_subj_subj_consistent:
  fixes f :: "partition_id_t \<Rightarrow> partition_id_t \<Rightarrow> bool"
  assumes "vpeq u s1 s2"
  shows "vpeq u (extend_subj_subj f s1) (extend_subj_subj f s2)"
proof -
  let ?g1 = "sp_impl_subj_subj s1" and ?g2 = "sp_impl_subj_subj s2"
  have "\<forall> v . Policy.sp_spec_subj_subj u v \<longrightarrow> ?g1 u v = ?g2 u v"
   and "\<forall> v . Policy.sp_spec_subj_subj v u \<longrightarrow> ?g1 v u = ?g2 v u"
    using assms unfolding vpeq_def vpeq_subj_subj_def by auto
  hence "\<forall> v . Policy.sp_spec_subj_subj u v \<longrightarrow> extend_f f ?g1 u v = extend_f f ?g2 u v"
    and "\<forall> v . Policy.sp_spec_subj_subj v u \<longrightarrow> extend_f f ?g1 v u = extend_f f ?g2 v u"
    unfolding extend_f_def by auto
  hence 1: "vpeq_subj_subj u (extend_subj_subj f s1) (extend_subj_subj f s2)"
    unfolding vpeq_subj_subj_def extend_subj_subj_def
    by auto
  have 2: "vpeq_obj u (extend_subj_subj f s1) (extend_subj_subj f s2)"
    using assms unfolding vpeq_def vpeq_obj_def extend_subj_subj_def by fastforce
  have 3: "vpeq_subj_obj u (extend_subj_subj f s1) (extend_subj_subj f s2)"
    using assms unfolding vpeq_def vpeq_subj_obj_def extend_subj_subj_def by fastforce
 have 4: "vpeq_local u (extend_subj_subj f s1) (extend_subj_subj f s2)"
    using assms unfolding vpeq_def vpeq_local_def extend_subj_subj_def by fastforce
  from 1 2 3 4 show ?thesis
    using assms unfolding vpeq_def by fast
qed


subsubsection \<open>Summary theorems on view-partitioning weak step consistency\<close>

text \<open>The atomic step is weakly step consistent with view partitioning.
 Here, the ``weakness'' is that we assume that the two states are vp-equivalent
 not only w.r.t. the observer domain @{term u}, but also w.r.t. the caller
 domain @{term "partition tid"}).\<close>

theorem atomic_step_weakly_step_consistent:
  assumes eq_obs: "vpeq u s1 s2"
      and eq_act: "vpeq (partition (current s1)) s1 s2"
      and inv1:   "atomic_step_invariant s1"
      and inv2:   "atomic_step_invariant s2"
      and prec1: "atomic_step_precondition s1 (current s1) ipt"
      and prec2: "atomic_step_precondition s2 (current s2) ipt"
      and eq_curr: "current s1 = current s2"
  shows "vpeq u (atomic_step s1 ipt) (atomic_step s2 ipt)"
proof -
  show ?thesis
    using assms 
          ipc_weakly_step_consistent
          ev_wait_all_weakly_step_consistent
          ev_wait_one_weakly_step_consistent
          ev_signal_weakly_step_consistent
          vpeq_refl
    unfolding atomic_step_def
    apply (cases ipt, auto)
    apply  (simp split: ev_consume_t.splits ev_wait_stage_t.splits)
    by  (simp split: ev_signal_stage_t.splits)
   qed
end
