subsection \<open>Link implementation to CISK: the specific separation kernel is an interpretation of the generic model.\label{sect:link_to_CISK}\<close>

theory Link_separation_kernel_model_to_CISK
  imports Separation_kernel_model         
begin

text \<open>We show that the separation kernel instantiation satisfies the 
specification of CISK.
\<close>

theorem CISK_proof_obligations_satisfied:
  shows
    "Controllable_Interruptible_Separation_Kernel
      rstep
      routput_f
      (\<up>s0)
      rcurrent
      rcswitch
      rkinvolved
      rifp
      rvpeq
      rAS_set
      rinvariant
      rprecondition
      raborting
      rwaiting
      rset_error_code"
proof (unfold_locales)
  \<comment> \<open>show that rvpeq is equivalence relation\<close>
  show "\<forall> a b c u. (rvpeq u a b \<and> rvpeq u b c) \<longrightarrow> rvpeq u a c"
   and "\<forall> a b u. rvpeq u a b \<longrightarrow> rvpeq u b a"
   and "\<forall> a u. rvpeq u a a"
    using inst_vpeq_rel by metis+
  \<comment> \<open>show output consistency\<close>
  show "\<forall> a s t. rvpeq (rcurrent s) s t \<and> rcurrent s = rcurrent t \<longrightarrow> routput_f s a = routput_f t a"
    using inst_output_consistency by metis
  \<comment> \<open>show reflexivity of ifp\<close>
  show "\<forall> u . rifp u u"
    using inst_ifp_refl by metis
  \<comment> \<open>show step consistency\<close>
  show "\<forall>s t u a. rvpeq u s t \<and> rvpeq (rcurrent s) s t \<and> True \<and> rprecondition s (rcurrent s) a \<and> True \<and> rprecondition t (rcurrent t) a \<and> rcurrent s = rcurrent t \<longrightarrow>
              rvpeq u (rstep s a) (rstep t a)"
    using inst_weakly_step_consistent by blast
  \<comment> \<open>show step atomicity\<close>
  show "\<forall> s a . rcurrent (rstep s a) = rcurrent s"
    using inst_step_atomicity by metis
  show " \<forall>a s u. \<not> rifp (rcurrent s) u \<and> True \<and> rprecondition s (rcurrent s) a \<longrightarrow> rvpeq u s (rstep s a)"
    using inst_local_respect by blast
  \<comment> \<open>show cswitch is independent of state\<close>
  show "\<forall>n s t. rcurrent s = rcurrent t \<longrightarrow> rcurrent (rcswitch n s) = rcurrent (rcswitch n t)"
    using inst_cswitch_independent_of_state by metis
  \<comment> \<open>show cswitch consistency\<close>
  show "\<forall>u s t n. rvpeq u s t \<longrightarrow> rvpeq u (rcswitch n s) (rcswitch n t)"
    using inst_cswitch_consistency by metis
  \<comment> \<open>Show the empt action sequence is in @{term AS_set}\<close>
  show "[] \<in> rAS_set"
    unfolding rAS_set_def
    by auto
  \<comment> \<open>The invariant for the initial state, already encoded in @{term rstate_t}\<close>
  show "True"
    by auto
  \<comment> \<open>Step function of the invariant, already encoded in @{term rstate_t}\<close>
  show "\<forall>s n. True \<longrightarrow> True"
    by auto
  \<comment> \<open>The precondition does not change with a context switch\<close>
  show "\<forall>s d n a. rprecondition s d a \<longrightarrow> rprecondition (rcswitch n s) d a"
    using precondition_after_cswitch by blast
  \<comment> \<open>The precondition holds for the first action of each action sequence\<close>
  show "\<forall>s d aseq. True \<and> aseq \<in> rAS_set \<and> aseq \<noteq> [] \<longrightarrow> rprecondition s d (hd aseq)"
    using prec_first_IPC_action prec_first_EV_WAIT_action prec_first_EV_SIGNAL_action
    unfolding rAS_set_def is_sub_seq_def 
    by auto
  \<comment> \<open>The precondition holds for the next action in an action sequence, assuming the sequence is not aborted or delayed\<close>
  show "\<forall>s a a'. (\<exists>aseq\<in>rAS_set. is_sub_seq a a' aseq) \<and> True \<and> rprecondition s (rcurrent s) a \<and> \<not> raborting s (rcurrent s) a \<and> \<not> rwaiting s (rcurrent s) a \<longrightarrow>
             rprecondition (rstep s a) (rcurrent s) a'"
    using prec_after_IPC_step prec_after_EV_SIGNAL_step prec_after_EV_WAIT_step
    unfolding rAS_set_def is_sub_seq_def
    by auto
  \<comment> \<open>Steps of other domains do not influence the precondition\<close>
  show "\<forall>s d a a'. rcurrent s \<noteq> d \<and> rprecondition s d a \<longrightarrow> rprecondition (rstep s a') d a"
    using prec_dom_independent by blast
  \<comment> \<open>The invariant\<close>
  show "\<forall>s a. True \<longrightarrow> True"
    by auto
  \<comment> \<open>Aborting does not depend on a context switch\<close>
  show "\<forall>n s. raborting (rcswitch n s) = raborting s"
    using aborting_switch_independent by auto
  \<comment> \<open>Aborting does not depend on actions of other domains\<close>
  show "\<forall>s a d. rcurrent s \<noteq> d \<longrightarrow> raborting (rstep s a) d = raborting s d"
    using aborting_dom_independent by auto
  \<comment> \<open>Aborting is consistent\<close>
  show "\<forall>s t u. rvpeq u s t \<longrightarrow> raborting s u = raborting t u"
    using raborting_consistent by auto
  \<comment> \<open>Waiting does not depend on a context switch\<close>
  show "\<forall>n s. rwaiting (rcswitch n s) = rwaiting s"
    using waiting_switch_independent by auto
  \<comment> \<open>Waiting is consistent\<close>
  show "\<forall>s t u a. rvpeq (rcurrent s) s t \<and> (\<forall> d \<in> rkinvolved a . rvpeq d s t) 
         \<and> rvpeq u s t  
         \<longrightarrow> rwaiting s u a = rwaiting t u a"
    unfolding Kernel.involved_def
    using waiting_consistent by auto
  \<comment> \<open>Domains that are involved in an action may influence the domain of the action\<close>
  show "\<forall>s a. \<forall> d \<in> rkinvolved a. rprecondition s (rcurrent s) a \<longrightarrow> rifp d (rcurrent s)"
    using involved_ifp by blast
  \<comment> \<open>An action that is waiting does not change the state\<close>
  show "\<forall>s a. rwaiting s (rcurrent s) a \<longrightarrow> rstep s a = s"
    using spec_of_waiting by blast
  \<comment> \<open>Proof obligations for @{term set_error_code}. Right now, they are all trivial\<close>
  show "\<forall>s d a' a. rcurrent s \<noteq> d \<and> raborting s d a \<longrightarrow> raborting (rset_error_code s a') d a"
    unfolding rset_error_code_def
    by auto
  show "\<forall>s t u a. rvpeq u s t \<longrightarrow> rvpeq u (rset_error_code s a) (rset_error_code t a)"
    unfolding rset_error_code_def
    by auto
  show "\<forall>s u a. \<not> rifp (rcurrent s) u \<longrightarrow> rvpeq u s (rset_error_code s a)"
    unfolding rset_error_code_def
    by (metis \<open>\<forall>a u. rvpeq u a a\<close>)
  show "\<forall>s a. rcurrent (rset_error_code s a) = rcurrent s"
    unfolding rset_error_code_def
    by auto
  show "\<forall>s d a a'. rprecondition s d a \<and> raborting s (rcurrent s) a' \<longrightarrow> rprecondition (rset_error_code s a') d a"
    unfolding rset_error_code_def
    by auto
  show "\<forall>s d a' a. rcurrent s \<noteq> d \<and> rwaiting s d a \<longrightarrow> rwaiting (rset_error_code s a') d a"
    unfolding rset_error_code_def
    by auto
qed

text \<open>Now we can instantiate CISK with some initial state, interrupt function, etc.\<close>

interpretation Inst:
  Controllable_Interruptible_Separation_Kernel
    rstep           \<comment> \<open>step function, without program stack\<close>
    routput_f       \<comment> \<open>output function\<close>
    "\<up>s0"           \<comment> \<open>initial state\<close>
    rcurrent        \<comment> \<open>returns the currently active domain\<close>
    rcswitch        \<comment> \<open>switches the currently active domain\<close>
    "(=) 42"     \<comment> \<open>interrupt function (yet unspecified)\<close>
    rkinvolved      \<comment> \<open>returns a set of threads involved in the give action\<close>
    rifp            \<comment> \<open>information flow policy\<close>
    rvpeq           \<comment> \<open>view partitioning\<close>
    rAS_set         \<comment> \<open>the set of valid action sequences\<close>
    rinvariant      \<comment> \<open>the state invariant\<close>
    rprecondition   \<comment> \<open>the precondition for doing an action\<close>
    raborting       \<comment> \<open>condition under which an action is aborted\<close>
    rwaiting        \<comment> \<open>condition under which an action is delayed\<close>
    rset_error_code \<comment> \<open>updates the state. Has no meaning in the current model.\<close>
using CISK_proof_obligations_satisfied by auto

text \<open>The main theorem: the instantiation implements the information flow policy @{term ifp}.\<close>
theorem risecure:
  "Inst.isecure"
using Inst.unwinding_implies_isecure_CISK
by blast
      
end
