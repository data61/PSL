subsection \<open>Separation kernel model \label{sect:separation_kernel_model}\<close>

theory Separation_kernel_model
  imports "../../step/Step"
          "../../step/Step_invariants"
          "../../step/Step_vpeq"
          "../../step/Step_vpeq_locally_respects"
          "../../step/Step_vpeq_weakly_step_consistent"
          CISK
begin

text \<open>
 First (Section~\ref{sect:initial_state}) we instantiate the CISK generic model.
 Functions that instantiate a generic function of the CISK model are prefixed with an `r',
 `r' standing for ``Rushby';, as CISK is derived originally from a model
  by Rushby~\cite{Verbeek2013}.
 For example, `rifp' is the instantiation of the generic `ifp'.
 
 Later (Section~\ref{sect:discharging}) all CISK proof obligations are discharged, e.g., 
 weak step consistency, output consistency, etc. These will be used in 
 Section~\ref{sect:link_to_CISK}.
\<close>

subsubsection \<open>Initial state of separation kernel model\label{sect:initial_state}\<close>

text \<open>We assume that the initial state of threads and memory is given.
  The initial state of threads is arbitrary, but the threads are not
  executing the system call. The purpose of the following definitions
  is to obtain the initial state without potentially dangerous axioms.
  The only axioms we admit without proof are formulated using the
  ``consts'' syntax and thus safe.\<close>

consts
  initial_current :: "thread_id_t"
  initial_obj :: "obj_id_t \<Rightarrow> obj_t"

definition s0 :: state_t where
  "s0 \<equiv> \<lparr> sp_impl_subj_subj = Policy.sp_spec_subj_subj,
          sp_impl_subj_obj = Policy.sp_spec_subj_obj,
          current = initial_current,
          obj = initial_obj,
          thread = \<lambda> _ . (| ev_counter = 0 |) 
          \<rparr>"

lemma initial_invariant:
  shows "atomic_step_invariant s0"
proof -
  have "sp_subset s0"
    unfolding sp_subset_def s0_def by auto
  thus ?thesis
    unfolding atomic_step_invariant_def by auto
qed

subsubsection \<open>Types for instantiation of the generic model\<close>

text \<open>To simplify formulations, we include the state invariant
 @{term "atomic_step_invariant"} in the state data type. The 
 initial state @{term s0} serves at witness that @{term rstate_t} 
 is non-empty.\<close>

typedef (overloaded) rstate_t = "{ s . atomic_step_invariant s }"
  using initial_invariant by auto

definition abs :: "state_t \<Rightarrow> rstate_t" ("\<up> _") where "abs = Abs_rstate_t"
definition rep :: "rstate_t \<Rightarrow> state_t" ("\<down> _") where "rep = Rep_rstate_t"

lemma rstate_invariant:
  shows "atomic_step_invariant (\<down>s)"
  unfolding rep_def by (metis Rep_rstate_t mem_Collect_eq)

lemma rstate_down_up[simp]:
  shows "(\<up>\<down>s) = s"
  unfolding rep_def abs_def using Rep_rstate_t_inverse by auto

lemma rstate_up_down[simp]:
  assumes "atomic_step_invariant s"
  shows "(\<down>\<up>s) = s"
  using assms Abs_rstate_t_inverse unfolding rep_def abs_def by auto 

text \<open>A CISK action is identified with an interrupt point.\<close>

type_synonym raction_t = int_point_t

definition rcurrent :: "rstate_t \<Rightarrow> thread_id_t" where
  "rcurrent s = current \<down>s"

definition rstep :: "rstate_t \<Rightarrow> raction_t \<Rightarrow> rstate_t" where
  "rstep s a \<equiv> \<up>(atomic_step (\<down>s) a)"

text \<open>Each CISK domain is identified with a thread id.\<close>

type_synonym rdom_t = "thread_id_t"

text \<open>The output function returns the contents of all memory accessible
  to the subject. The action argument of the output function is ignored.\<close>

datatype visible_obj_t = VALUE obj_t | EXCEPTION
type_synonym routput_t = "page_t \<Rightarrow> visible_obj_t"

definition routput_f :: "rstate_t \<Rightarrow> raction_t \<Rightarrow> routput_t" where
  "routput_f s a p \<equiv>
    if sp_impl_subj_obj (\<down>s) (partition (rcurrent s)) (PAGE p) READ then
      VALUE (obj (\<down>s) (PAGE p))
    else
      EXCEPTION"

text \<open>The precondition for the generic model. Note that @{term atomic_step_invariant}
  is already part of the state.\<close>

definition rprecondition :: "rstate_t \<Rightarrow> rdom_t \<Rightarrow> raction_t \<Rightarrow> bool" where
  "rprecondition s d a \<equiv> atomic_step_precondition (\<down>s) d a"
abbreviation rinvariant
where "rinvariant s \<equiv> True" \<comment> \<open>The invariant is already in the state type.\<close>

text \<open>Translate view-partitioning and interaction-allowed relations.\<close>

definition rvpeq :: "rdom_t \<Rightarrow> rstate_t \<Rightarrow> rstate_t \<Rightarrow> bool" where
  "rvpeq u s1 s2 \<equiv> vpeq (partition u) (\<down>s1) (\<down>s2)"

  
definition rifp :: "rdom_t \<Rightarrow> rdom_t \<Rightarrow> bool" where
  "rifp u v = Policy.ifp (partition u) (partition v)"

text \<open>Context Switches\<close>
definition rcswitch :: "nat \<Rightarrow> rstate_t \<Rightarrow> rstate_t" where
  "rcswitch n s \<equiv> \<up>((\<down>s) \<lparr> current := (SOME t . True) \<rparr>)"
  
subsubsection  \<open>Possible action sequences\<close>

text \<open>
An @{term SK_IPC} consists of three atomic actions @{term PREP}, @{term WAIT} and @{term BUF} with the same parameters. 
\<close>
definition is_SK_IPC :: "raction_t list \<Rightarrow> bool"
where "is_SK_IPC aseq \<equiv> \<exists> dir partner page .
                    aseq = [SK_IPC dir PREP partner page,SK_IPC dir WAIT partner page,SK_IPC dir (BUF (SOME page' . True)) partner page]"
text \<open>
An @{term SK_EV_WAIT} consists of three atomic actions, one for each of the stages @{term EV_PREP}, @{term EV_WAIT} and @{term EV_FINISH} 
with the same parameters. 
\<close>
definition is_SK_EV_WAIT :: "raction_t list \<Rightarrow> bool"
where "is_SK_EV_WAIT aseq \<equiv> \<exists> consume .
                     aseq = [SK_EV_WAIT EV_PREP consume , 
                             SK_EV_WAIT EV_WAIT consume , 
                             SK_EV_WAIT EV_FINISH consume ]"
                    
text \<open>
An @{term SK_EV_SIGNAL} consists of two atomic actions, one for each of the stages @{term EV_SIGNAL_PREP} and 
@{term EV_SIGNAL_FINISH} with the same parameters. 
\<close>
definition is_SK_EV_SIGNAL :: "raction_t list \<Rightarrow> bool"
where "is_SK_EV_SIGNAL aseq \<equiv> \<exists> partner .
                     aseq = [SK_EV_SIGNAL EV_SIGNAL_PREP partner, 
                             SK_EV_SIGNAL EV_SIGNAL_FINISH partner]"
                    

text \<open>
  The complete attack surface consists of IPC calls, events, and noops.
\<close>
definition rAS_set :: "raction_t list set"
  where "rAS_set \<equiv> { aseq . is_SK_IPC aseq \<or> is_SK_EV_WAIT aseq \<or> is_SK_EV_SIGNAL aseq } \<union> {[]}"

subsubsection \<open>Control\<close>
text \<open>
  When are actions aborting, and when are actions waiting.
  We do not currently use the @{term set_error_code} function yet.
\<close>
abbreviation raborting
  where "raborting s \<equiv> aborting (\<down>s)"
abbreviation rwaiting
  where "rwaiting s \<equiv> waiting (\<down>s)"
definition rset_error_code :: "rstate_t \<Rightarrow> raction_t \<Rightarrow> rstate_t"
  where "rset_error_code s a \<equiv> s"
text \<open>
  Returns the set of threads that are involved in a certain action.
  For example, for an IPC call, the @{term WAIT} stage synchronizes with the partner.
  This partner is involved in that action.
\<close>
definition rkinvolved :: "int_point_t \<Rightarrow> rdom_t set"
  where "rkinvolved a \<equiv> 
  case a of SK_IPC dir WAIT partner page \<Rightarrow> {partner}
   | SK_EV_SIGNAL EV_SIGNAL_FINISH partner => {partner}
   | _ \<Rightarrow> {}"
abbreviation rinvolved :: "int_point_t option \<Rightarrow> rdom_t set"
  where "rinvolved \<equiv> Kernel.involved rkinvolved"



subsubsection \<open>Discharging the proof obligations\label{sect:discharging}\<close>

lemma inst_vpeq_rel:
  shows rvpeq_refl: "rvpeq u s s"
    and rvpeq_sym: "rvpeq u s1 s2 \<Longrightarrow> rvpeq u s2 s1"
    and rvpeq_trans: "\<lbrakk> rvpeq u s1 s2; rvpeq u s2 s3 \<rbrakk> \<Longrightarrow> rvpeq u s1 s3"
    unfolding rvpeq_def using vpeq_rel by metis+

lemma inst_ifp_refl:
  shows "\<forall> u . rifp u u"
unfolding rifp_def using Policy_properties.ifp_reflexive by fast    
    
(* Original definition 
  definition step_atomicity::bool where "step_atomicity 
  \<equiv> \<forall> s a . current (step s a) = current s"    
*)  
lemma inst_step_atomicity [simp]:
  shows "\<forall> s a . rcurrent (rstep s a) = rcurrent s"
unfolding rstep_def rcurrent_def
using atomic_step_does_not_change_current_thread rstate_up_down rstate_invariant atomic_step_preserves_invariants
    by auto

(* Original definition 
definition weakly_step_consistent::bool where "weakly_step_consistent 
  \<equiv> \<forall> s t u a. 
    vpeq u s t \<and> vpeq (current s) s t 
  \<and> current s = current t 
  \<and> precondition s a \<and> precondition t a 
  \<longrightarrow> 
  vpeq u (step s a) (step t a)"
*)


lemma inst_weakly_step_consistent:
  assumes "rvpeq u s t"
      and "rvpeq (rcurrent s) s t"
      and "rcurrent s = rcurrent t"
      and "rprecondition s (rcurrent s) a"
      and "rprecondition t (rcurrent t) a"
    shows "rvpeq u (rstep s a) (rstep t a)"
using assms atomic_step_weakly_step_consistent rstate_invariant atomic_step_preserves_invariants
unfolding rcurrent_def rstep_def rvpeq_def rprecondition_def
by auto


(* Original definition 

definition locally_respects::bool where "locally_respects 
  \<equiv> \<forall> a s u. 
    \<not>ifp (current s) u  
  \<and> precondition s a 
  \<longrightarrow> 
  vpeq u s (step s a)"
*)

lemma inst_local_respect:
  assumes not_ifp: "\<not>rifp (rcurrent s) u"
      and prec: "rprecondition s (rcurrent s) a"
    shows "rvpeq u s (rstep s a)"
using assms atomic_step_respects_policy rstate_invariant atomic_step_preserves_invariants
unfolding rifp_def rprecondition_def rvpeq_def rstep_def rcurrent_def
by auto

(*

definition output_consistent::bool where "output_consistent 
  \<equiv> \<forall> a s t. 
   vpeq (current s) s t 
 \<and> current s = current t 
 \<longrightarrow> 
 (output_f s a) = (output_f t a)"
*)

lemma inst_output_consistency:
  assumes rvpeq: "rvpeq (rcurrent s) s t"
  and     current_eq: "rcurrent s = rcurrent t"
  shows   "routput_f s a = routput_f t a"
proof-
  have "\<forall> a s t. rvpeq (rcurrent s) s t \<and> rcurrent s = rcurrent t \<longrightarrow> routput_f s a = routput_f t a"
    proof-
      { fix a :: raction_t
        fix s t :: rstate_t
        fix p :: page_t
        assume 1: "rvpeq (rcurrent s) s t"
           and 2: "rcurrent s = rcurrent t"
        let ?part = "partition (rcurrent s)"
        have "routput_f s a p = routput_f t a p"
          proof (cases "Policy.sp_spec_subj_obj ?part (PAGE p) READ"
                 rule: case_split [case_names Allowed Denied])
            case Allowed
              have 5: "obj (\<down>s) (PAGE p) = obj (\<down>t) (PAGE p)"
                using 1 Allowed unfolding rvpeq_def vpeq_def vpeq_obj_def  by auto
              have 6: "sp_impl_subj_obj (\<down>s) ?part (PAGE p) READ = sp_impl_subj_obj (\<down>t) ?part (PAGE p) READ"
                using 1 2 Allowed unfolding rvpeq_def vpeq_def vpeq_subj_obj_def by auto
              show "routput_f s a p = routput_f t a p"
                unfolding routput_f_def using 2 5 6 by auto
            next case Denied
              hence "sp_impl_subj_obj (\<down>s) ?part (PAGE p) READ = False"
                and "sp_impl_subj_obj (\<down>t) ?part (PAGE p) READ = False"
                using rstate_invariant unfolding atomic_step_invariant_def sp_subset_def
                by auto
              thus "routput_f s a p = routput_f t a p"
                using 2 unfolding routput_f_def by simp
          qed }
        thus "\<forall> a s t. rvpeq (rcurrent s) s t \<and> rcurrent s = rcurrent t \<longrightarrow> routput_f s a = routput_f t a"
          by auto
    qed
  thus ?thesis using assms by auto
qed

(*
definition cswitch_independent_of_state::bool where "cswitch_independent_of_state
  \<equiv> \<forall> n s t . current s = current t \<longrightarrow> current (cswitch n s) = current (cswitch n t)"
*)
lemma inst_cswitch_independent_of_state:
  assumes "rcurrent s = rcurrent t"
  shows "rcurrent (rcswitch n s) = rcurrent (rcswitch n t)"
using rstate_invariant cswitch_preserves_invariants unfolding rcurrent_def rcswitch_def by simp

(*
definition cswitch_consistency::bool where "cswitch_consistency
  \<equiv> \<forall> u s t n . vpeq u s t \<longrightarrow> vpeq u (cswitch n s) (cswitch n t)"
  *)
lemma inst_cswitch_consistency:
  assumes "rvpeq u s t"
  shows "rvpeq u (rcswitch n s) (rcswitch n t)"
proof-
  have 1: "vpeq (partition u) (\<down>s) \<down>(rcswitch n s)"
  using rstate_invariant cswitch_consistency_and_respect cswitch_preserves_invariants
  unfolding rcswitch_def 
    by auto
  have 2: "vpeq (partition u) (\<down>t) \<down>(rcswitch n t)"
  using rstate_invariant cswitch_consistency_and_respect cswitch_preserves_invariants
  unfolding rcswitch_def 
    by auto
  from 1 2 assms show ?thesis unfolding rvpeq_def using vpeq_rel by metis
qed

text \<open>
For the @{term PREP} stage (the first stage of the IPC action sequence) the precondition is True.
\<close>
lemma prec_first_IPC_action:
assumes "is_SK_IPC aseq"
  shows "rprecondition s d (hd aseq)"
using assms
unfolding is_SK_IPC_def rprecondition_def atomic_step_precondition_def
by auto

text \<open>
For the the first stage of the @{term EV_WAIT} action sequence the precondition is True.
\<close>
lemma prec_first_EV_WAIT_action:
assumes "is_SK_EV_WAIT aseq"
  shows "rprecondition s d (hd aseq)"
using assms
unfolding is_SK_EV_WAIT_def rprecondition_def atomic_step_precondition_def
by auto

text \<open>
For the first stage of the @{term EV_SIGNAL} action sequence the precondition is True.
\<close>
lemma prec_first_EV_SIGNAL_action:
assumes "is_SK_EV_SIGNAL aseq"
  shows "rprecondition s d (hd aseq)"
using assms
unfolding is_SK_EV_SIGNAL_def rprecondition_def atomic_step_precondition_def
          ev_signal_precondition_def
  by auto

text \<open>
When not waiting or aborting, the precondition is ``1-step inductive'', that is at all times
the precondition holds initially (for the first step of an action sequence) and after doing 
one step.
\<close>
lemma prec_after_IPC_step:
assumes prec: "rprecondition s (rcurrent s) (aseq ! n)" 
    and n_bound: "Suc n < length aseq"
    and IPC: "is_SK_IPC aseq"
    and not_aborting: "\<not>raborting s (rcurrent s) (aseq ! n)"
    and not_waiting: "\<not>rwaiting s (rcurrent s) (aseq ! n)"
shows "rprecondition (rstep s (aseq ! n)) (rcurrent s) (aseq ! Suc n)"    
proof-
{
  fix dir partner page
  let ?page' = "(SOME page' . True)"
  assume IPC: "aseq = [SK_IPC dir PREP partner page,SK_IPC dir WAIT partner page,SK_IPC dir (BUF ?page') partner page]"
  {
    assume 0: "n=0"
    from 0 IPC prec not_aborting
      have ?thesis
      unfolding rprecondition_def atomic_step_precondition_def rstep_def rcurrent_def atomic_step_def atomic_step_ipc_def aborting_def
      by(auto)
  }
  moreover
  {
    assume 1: "n=1"
    from 1 IPC prec not_waiting
      have ?thesis
      unfolding rprecondition_def atomic_step_precondition_def rstep_def rcurrent_def atomic_step_def atomic_step_ipc_def waiting_def
      by(auto)
  } 
  moreover
  from IPC 
    have "length aseq = 3"
    by auto
  ultimately
    have ?thesis
    using n_bound
    by arith
}
thus ?thesis
  using IPC
  unfolding is_SK_IPC_def
  by(auto)
qed

text \<open>
When not waiting or aborting, the precondition is 1-step inductive.
\<close>
lemma prec_after_EV_WAIT_step:
assumes prec: "rprecondition s (rcurrent s) (aseq ! n)" 
    and n_bound: "Suc n < length aseq"
    and IPC: "is_SK_EV_WAIT aseq"
    and not_aborting: "\<not>raborting s (rcurrent s) (aseq ! n)"
    and not_waiting: "\<not>rwaiting s (rcurrent s) (aseq ! n)"
shows "rprecondition (rstep s (aseq ! n)) (rcurrent s) (aseq ! Suc n)"    
proof-
{
  fix consume

  assume WAIT: "aseq = [SK_EV_WAIT EV_PREP consume,
                        SK_EV_WAIT EV_WAIT consume,
                        SK_EV_WAIT EV_FINISH consume]"
  {
    assume 0: "n=0"
    from 0 WAIT prec not_aborting
      have ?thesis
      unfolding rprecondition_def atomic_step_precondition_def 
      by(auto)
  }
  moreover
  {
    assume 1: "n=1"
    from 1 WAIT prec not_waiting
      have ?thesis
      unfolding rprecondition_def atomic_step_precondition_def 
      by(auto)
  } 
  moreover
  from WAIT
    have "length aseq = 3"
    by auto
  ultimately
    have ?thesis
    using n_bound
    by arith
}
thus ?thesis
  using assms
  unfolding is_SK_EV_WAIT_def
  by auto
qed


text \<open>
When not waiting or aborting, the precondition is 1-step inductive.
\<close>
lemma prec_after_EV_SIGNAL_step:
assumes prec: "rprecondition s (rcurrent s) (aseq ! n)" 
    and n_bound: "Suc n < length aseq"
    and SIGNAL: "is_SK_EV_SIGNAL aseq"
    and not_aborting: "\<not>raborting s (rcurrent s) (aseq ! n)"
    and not_waiting: "\<not>rwaiting s (rcurrent s) (aseq ! n)"
shows "rprecondition (rstep s (aseq ! n)) (rcurrent s) (aseq ! Suc n)"    
proof-
{   fix partner
    assume SIGNAL1: "aseq = [SK_EV_SIGNAL EV_SIGNAL_PREP partner,
                            SK_EV_SIGNAL EV_SIGNAL_FINISH partner]"
  {
    assume 0: "n=0"
    from 0 SIGNAL1 prec not_aborting 
      have ?thesis
      unfolding rprecondition_def atomic_step_precondition_def ev_signal_precondition_def
                aborting_def rstep_def atomic_step_def
      by auto
  }
  moreover
  from SIGNAL1
    have "length aseq = 2"
    by auto 
  ultimately
    have ?thesis
    using n_bound
    by arith
}
thus ?thesis
  using assms
  unfolding is_SK_EV_SIGNAL_def
  by auto
qed

lemma on_set_object_value:
  shows "sp_impl_subj_subj (set_object_value ob val s) = sp_impl_subj_subj s"
    and "sp_impl_subj_obj (set_object_value ob val s) = sp_impl_subj_obj s"
  unfolding set_object_value_def apply simp+ done

lemma prec_IPC_dom_independent:
assumes "current s \<noteq> d"
    and "atomic_step_invariant s"
    and "atomic_step_precondition s d a"
shows "atomic_step_precondition (atomic_step_ipc (current s) dir stage partner page s) d a"
using assms on_set_object_value
unfolding atomic_step_precondition_def atomic_step_ipc_def ipc_precondition_def
          ev_signal_precondition_def set_object_value_def
          by (auto split: int_point_t.splits ipc_stage_t.splits ipc_direction_t.splits
                   ev_consume_t.splits ev_wait_stage_t.splits ev_signal_stage_t.splits)

lemma prec_ev_signal_dom_independent:
assumes "current s \<noteq> d"
    and "atomic_step_invariant s"
    and "atomic_step_precondition s d a"
shows "atomic_step_precondition (atomic_step_ev_signal (current s) partner s) d a"
using assms on_set_object_value
unfolding atomic_step_precondition_def atomic_step_ev_signal_def ipc_precondition_def
          ev_signal_precondition_def set_object_value_def
          by (auto split: int_point_t.splits ipc_stage_t.splits ipc_direction_t.splits
                   ev_consume_t.splits ev_wait_stage_t.splits ev_signal_stage_t.splits)

lemma prec_ev_wait_one_dom_independent:
assumes "current s \<noteq> d"
    and "atomic_step_invariant s"
    and "atomic_step_precondition s d a"
shows "atomic_step_precondition (atomic_step_ev_wait_one (current s) s) d a"
using assms on_set_object_value
unfolding atomic_step_precondition_def atomic_step_ev_wait_one_def ipc_precondition_def
          ev_signal_precondition_def set_object_value_def
          by (auto split: int_point_t.splits ipc_stage_t.splits ipc_direction_t.splits
                   ev_consume_t.splits ev_wait_stage_t.splits ev_signal_stage_t.splits)

lemma prec_ev_wait_all_dom_independent:
assumes "current s \<noteq> d"
    and "atomic_step_invariant s"
    and "atomic_step_precondition s d a"
shows "atomic_step_precondition (atomic_step_ev_wait_all (current s) s) d a"
using assms on_set_object_value
unfolding atomic_step_precondition_def atomic_step_ev_wait_all_def ipc_precondition_def
          ev_signal_precondition_def set_object_value_def
          by (auto split: int_point_t.splits ipc_stage_t.splits ipc_direction_t.splits
                   ev_consume_t.splits ev_wait_stage_t.splits ev_signal_stage_t.splits)

lemma prec_dom_independent:
shows "\<forall> s d a a' . rcurrent s \<noteq> d \<and> rprecondition s d a \<longrightarrow> rprecondition (rstep s a') d a"
using atomic_step_preserves_invariants 
rstate_invariant prec_IPC_dom_independent prec_ev_signal_dom_independent
prec_ev_wait_all_dom_independent prec_ev_wait_one_dom_independent
unfolding rcurrent_def rprecondition_def rstep_def atomic_step_def 
by(auto split: int_point_t.splits  ev_consume_t.splits ev_wait_stage_t.splits ev_signal_stage_t.splits)

lemma ipc_precondition_after_cswitch[simp]:
shows "ipc_precondition d dir partner page ((\<down> s)\<lparr>current := new_current\<rparr>) 
          = ipc_precondition d dir partner page (\<down> s)"
unfolding ipc_precondition_def
by(auto split: ipc_direction_t.splits)

lemma precondition_after_cswitch:
shows "\<forall>s d n a. rprecondition s d a \<longrightarrow> rprecondition (rcswitch n s) d a"
using cswitch_preserves_invariants rstate_invariant
unfolding rprecondition_def rcswitch_def atomic_step_precondition_def
          ev_signal_precondition_def
by (auto split: int_point_t.splits ipc_stage_t.splits  ev_signal_stage_t.splits)

lemma aborting_switch_independent:
shows "\<forall>n s. raborting (rcswitch n s) = raborting s"
proof-
{
  fix n s
  {
    fix tid a
    have "raborting (rcswitch n s) tid a = raborting s tid a"
      using rstate_invariant cswitch_preserves_invariants ev_signal_precondition_weakly_step_consistent
            cswitch_consistency_and_respect
      unfolding aborting_def rcswitch_def 
      apply (auto split: int_point_t.splits ipc_stage_t.splits
                         ev_wait_stage_t.splits ev_signal_stage_t.splits)
      apply (metis (full_types))
      by blast 
  }
  hence "raborting (rcswitch n s) = raborting s" by auto
}
thus ?thesis by auto
qed
lemma waiting_switch_independent:
shows "\<forall>n s. rwaiting (rcswitch n s) = rwaiting s"
proof-
{
  fix n s
  {
    fix tid a
    have "rwaiting (rcswitch n s) tid a = rwaiting s tid a"
      using rstate_invariant cswitch_preserves_invariants
      unfolding waiting_def rcswitch_def
      by(auto split: int_point_t.splits ipc_stage_t.splits ev_wait_stage_t.splits)
  }
  hence "rwaiting (rcswitch n s) = rwaiting s" by auto
}
thus ?thesis by auto
qed

lemma aborting_after_IPC_step:
assumes "d1 \<noteq> d2"
shows "aborting (atomic_step_ipc d1 dir stage partner page s) d2 a = aborting s d2 a"
unfolding atomic_step_ipc_def aborting_def set_object_value_def ipc_precondition_def
          ev_signal_precondition_def
by(auto split: int_point_t.splits ipc_stage_t.splits ipc_direction_t.splits
                   ev_signal_stage_t.splits)

lemma waiting_after_IPC_step:
assumes "d1 \<noteq> d2"
shows "waiting (atomic_step_ipc d1 dir stage partner page s) d2 a = waiting s d2 a"
unfolding atomic_step_ipc_def waiting_def set_object_value_def ipc_precondition_def
by(auto split: int_point_t.splits ipc_stage_t.splits ipc_direction_t.splits
                   ev_wait_stage_t.splits)
(*
lemma raborting_after_step:
shows "\<forall>s a d. rcurrent s \<noteq> d \<longrightarrow> raborting (rstep s a) d = raborting s d"
proof-
{
  fix s a d
  assume not_curr: "rcurrent s \<noteq> d"
  {
    fix a
    have "raborting (rstep s a) d = raborting s d"
      using not_curr aborting_after_IPC_step
            rstate_invariant atomic_ipc_preserves_invariants
      unfolding rcurrent_def  rstep_def atomic_step_def
      by(auto split: int_point_t.splits)
  }
  hence "raborting (rstep s a) d = raborting s d" by auto
}
thus ?thesis by auto
qed
*)
(*
lemma rwaiting_after_step:
shows "\<forall>s a d. rcurrent s \<noteq> d \<longrightarrow> rwaiting (rstep s a) d = rwaiting s d"
proof-
{
  fix s a d
  assume not_curr: "rcurrent s \<noteq> d"
  {
    fix a
    have "rwaiting (rstep s a) d = rwaiting s d"
      using not_curr waiting_after_IPC_step
            rstate_invariant atomic_ipc_preserves_invariants
      unfolding rcurrent_def  rstep_def atomic_step_def
      by(auto split: int_point_t.splits)
  }
  hence "rwaiting (rstep s a) d = rwaiting s d" by auto
}
thus ?thesis by auto
qed
*)

lemma raborting_consistent:
shows "\<forall>s t u. rvpeq u s t \<longrightarrow> raborting s u = raborting t u"
proof-
{
  fix s t u 
  assume vpeq: "rvpeq u s t"
  {
    fix a
    from vpeq ipc_precondition_weakly_step_consistent rstate_invariant
      have "\<And> tid dir partner page . ipc_precondition u dir partner page (\<down>s) 
                                    = ipc_precondition u dir partner page (\<down>t)"
      unfolding rvpeq_def
      by auto
    with vpeq rstate_invariant have "raborting s u a = raborting t u a"
      unfolding aborting_def rvpeq_def vpeq_def vpeq_local_def ev_signal_precondition_def
               vpeq_subj_subj_def atomic_step_invariant_def sp_subset_def rep_def
      apply (auto split: int_point_t.splits ipc_stage_t.splits ev_signal_stage_t.splits)
      by blast
  }
  hence "raborting s u = raborting t u" by auto
}
thus ?thesis by auto
qed

lemma aborting_dom_independent:
  assumes "rcurrent s \<noteq> d"
    shows "raborting (rstep s a) d a' = raborting s d a'"
proof -
  have "\<And> tid dir partner page s . ipc_precondition tid dir partner page s = ipc_precondition tid dir partner page (atomic_step s a)
                                   \<and> ev_signal_precondition tid partner  s = ev_signal_precondition tid partner (atomic_step s a)
       "
    proof -
    fix tid dir partner page s
    let ?s = "atomic_step s a"
    have "(\<forall> p q . sp_impl_subj_subj s p q = sp_impl_subj_subj ?s p q)
       \<and> (\<forall> p x m . sp_impl_subj_obj s p x m = sp_impl_subj_obj ?s p x m)"
      unfolding atomic_step_def atomic_step_ipc_def
               atomic_step_ev_wait_all_def atomic_step_ev_wait_one_def
               atomic_step_ev_signal_def set_object_value_def
      by (auto split: int_point_t.splits ipc_stage_t.splits ipc_direction_t.splits
          ev_wait_stage_t.splits ev_consume_t.splits  ev_signal_stage_t.splits)
    thus "ipc_precondition tid dir partner page s = ipc_precondition tid dir partner page (atomic_step s a)
         \<and> ev_signal_precondition tid partner  s = ev_signal_precondition tid partner (atomic_step s a)"
      unfolding ipc_precondition_def ev_signal_precondition_def by simp
    qed
  moreover have "\<And> b . (\<down>(\<up>(atomic_step (\<down>s) b))) = atomic_step (\<down>s) b"
    using rstate_invariant atomic_step_preserves_invariants rstate_up_down by auto
  ultimately show ?thesis
    unfolding aborting_def rstep_def ev_signal_precondition_def
              
    by (simp split: int_point_t.splits ipc_stage_t.splits ev_wait_stage_t.splits
                        ev_signal_stage_t.splits)
qed

lemma ipc_precondition_of_partner_consistent:
assumes vpeq: "\<forall> d \<in> rkinvolved (SK_IPC dir WAIT partner page) . rvpeq d s t"
shows "ipc_precondition partner dir' u page' (\<down> s) =  ipc_precondition partner dir' u page' \<down> t"
proof-
  from assms ipc_precondition_weakly_step_consistent rstate_invariant
    show ?thesis
    unfolding rvpeq_def rkinvolved_def
    by auto
qed 

lemma ev_signal_precondition_of_partner_consistent:
assumes vpeq: "\<forall> d \<in> rkinvolved (SK_EV_SIGNAL EV_SIGNAL_FINISH partner) . rvpeq d s t"
shows "ev_signal_precondition partner u (\<down> s) =  ev_signal_precondition partner u (\<down> t)"
proof-
  from assms ev_signal_precondition_weakly_step_consistent rstate_invariant
    show ?thesis 
    unfolding rvpeq_def rkinvolved_def
    by auto
qed 
 
lemma waiting_consistent:
shows "\<forall>s t u a . rvpeq (rcurrent s) s t \<and> (\<forall> d \<in> rkinvolved a . rvpeq d s t) 
        \<and> rvpeq u s t
        \<longrightarrow> rwaiting s u a = rwaiting t u a"
proof-
{
  fix s t u a
  assume vpeq: "rvpeq (rcurrent s) s t"
  assume vpeq_involved: "\<forall> d \<in> rkinvolved a . rvpeq d s t"
  assume vpeq_u: "rvpeq u s t"
  have "rwaiting s u a = rwaiting t u a" proof (cases a)
    case SK_IPC
      thus "rwaiting s u a = rwaiting t u a"
      using ipc_precondition_of_partner_consistent vpeq_involved
      unfolding waiting_def by (auto split: ipc_stage_t.splits)
    next case SK_EV_WAIT
      thus "rwaiting s u a = rwaiting t u a"
        using ev_signal_precondition_of_partner_consistent
        vpeq_involved vpeq vpeq_u
        unfolding waiting_def rkinvolved_def ev_signal_precondition_def
                  rvpeq_def vpeq_def vpeq_local_def
        by (auto split: ipc_stage_t.splits ev_wait_stage_t.splits ev_consume_t.splits)      
    qed (simp add: waiting_def, simp add: waiting_def) 
}
thus ?thesis by auto
qed

lemma ipc_precondition_ensures_ifp:
assumes "ipc_precondition (current s) dir partner page s"
    and "atomic_step_invariant s"
shows "rifp partner (current s)"
proof -
  let ?sp = "\<lambda> t1 t2 . Policy.sp_spec_subj_subj (partition t1) (partition t2)" 
  have "?sp (current s) partner \<or> ?sp partner (current s)"
    using assms unfolding ipc_precondition_def atomic_step_invariant_def sp_subset_def
    by (cases dir, auto)
  thus ?thesis
    unfolding rifp_def using Policy_properties.ifp_compatible_with_sp_spec by auto
qed

lemma ev_signal_precondition_ensures_ifp:
assumes "ev_signal_precondition (current s) partner s"
    and "atomic_step_invariant s"
shows "rifp partner (current s)"
proof -
  let ?sp = "\<lambda> t1 t2 . Policy.sp_spec_subj_subj (partition t1) (partition t2)" 
  have "?sp (current s) partner \<or> ?sp partner (current s)"
    using assms unfolding ev_signal_precondition_def atomic_step_invariant_def sp_subset_def
    by (auto)
  thus ?thesis
    unfolding rifp_def using Policy_properties.ifp_compatible_with_sp_spec by auto
qed

lemma involved_ifp:
shows "\<forall> s a . \<forall> d \<in> rkinvolved a . rprecondition s (rcurrent s) a \<longrightarrow> rifp d (rcurrent s)"
proof-
{
  fix s a d
  assume d_involved: "d \<in> rkinvolved a"
  assume prec: "rprecondition s (rcurrent s) a"
  from d_involved prec have "rifp d (rcurrent s)"
    using ipc_precondition_ensures_ifp ev_signal_precondition_ensures_ifp rstate_invariant
    unfolding rkinvolved_def rprecondition_def atomic_step_precondition_def rcurrent_def Kernel.involved_def
    by(cases a,simp,auto split: int_point_t.splits ipc_stage_t.splits ev_signal_stage_t.splits)
}
thus ?thesis by auto
qed

lemma spec_of_waiting_ev:
shows "\<forall>s a. rwaiting s (rcurrent s) (SK_EV_WAIT EV_FINISH EV_CONSUME_ALL) 
               \<longrightarrow> rstep s a = s"
 unfolding waiting_def
 by auto

lemma spec_of_waiting_ev_w:
shows "\<forall>s a. rwaiting s (rcurrent s) (SK_EV_WAIT EV_WAIT EV_CONSUME_ALL) 
               \<longrightarrow> rstep s (SK_EV_WAIT EV_WAIT EV_CONSUME_ALL) = s"
 unfolding rstep_def atomic_step_def
 by (auto split: int_point_t.splits ipc_stage_t.splits ev_wait_stage_t.splits)

lemma spec_of_waiting:
shows "\<forall>s a. rwaiting s (rcurrent s) a \<longrightarrow> rstep s a = s"
unfolding waiting_def rstep_def atomic_step_def atomic_step_ipc_def
          atomic_step_ev_signal_def atomic_step_ev_wait_all_def
          atomic_step_ev_wait_one_def
  by(auto split: int_point_t.splits ipc_stage_t.splits ev_wait_stage_t.splits)
end

