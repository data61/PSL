subsection \<open>SK (Separation Kernel) \label{sec:sep_kernel}\<close>

theory SK
  imports K
begin



text \<open>
  Locale Kernel is now refined to a generic model of a separation kernel.
  The security policy is represented using function \emph{ia}.
  Function \emph{vpeq} is adopted from Rushby and is an equivalence relation represeting whether two states are equivalent from the point of view of the given domain.   
  
  We assume constraints similar to Rushby, i.e., weak step consistency, locally respects, and output consistency.
  Additional assumptions are:
  \begin{description}
  \item[Step Atomicity] Each atomic kernel step can be executed within one time slot. Therefore, the domain that is currently active does not change by executing one action.
  \item[Time-based Interrupts] As interrupts occur according to a prefixed time-based schedule, the domain that is active after a call of switch depends on the currently active domain only (cswitch\_consistency).
  Also, cswitch can \emph{only} change which domain is currently active (cswitch\_consistency).
  \item[Control Consistency] States that are equivalent yield the same control. That is, the next action and the updated execution depend on the currently active domain only (next\_action\_consistent, next\_execs\_consistent),
  the state as updated by the control function remains in vpeq (next\_state\_consistent, locally\_respects\_next\_state).
  Finally, function control cannot change which domain is active (current\_next\_state).
  \end{description}
\<close>
definition actions_in_execution:: "'action_t execution \<Rightarrow> 'action_t set"
where "actions_in_execution exec \<equiv> { a . \<exists> aseq \<in> set exec . a \<in> set aseq }"


locale Separation_Kernel = Kernel kstep output_f s0 current cswitch interrupt kprecondition realistic_execution control kinvolved
  for kstep :: "'state_t \<Rightarrow> 'action_t \<Rightarrow> 'state_t"
  and output_f :: "'state_t \<Rightarrow> 'action_t \<Rightarrow> 'output_t"
  and s0 :: 'state_t
  and current :: "'state_t => 'dom_t" \<comment> \<open>Returns the currently active domain\<close>
  and cswitch :: "time_t \<Rightarrow> 'state_t \<Rightarrow> 'state_t" \<comment> \<open>Switches the current domain\<close>
  and interrupt :: "time_t \<Rightarrow> bool" \<comment> \<open>Returns t iff an interrupt occurs in the given state at the given time\<close>
  and kprecondition :: "'state_t \<Rightarrow> 'action_t \<Rightarrow> bool" \<comment> \<open>Returns t if an precondition holds that relates the current action to the state\<close>
  and realistic_execution :: "'action_t execution \<Rightarrow> bool" \<comment> \<open>In this locale, this function is completely unconstrained.\<close>
  and control :: "'state_t \<Rightarrow> 'dom_t \<Rightarrow> 'action_t execution \<Rightarrow> (('action_t option) \<times> 'action_t execution \<times> 'state_t)"
  and kinvolved :: "'action_t \<Rightarrow> 'dom_t set"  
+
  fixes ifp :: "'dom_t \<Rightarrow> 'dom_t \<Rightarrow> bool"
    and vpeq :: "'dom_t \<Rightarrow> 'state_t \<Rightarrow> 'state_t \<Rightarrow> bool"
assumes vpeq_transitive: " \<forall> a b c u. (vpeq u a b \<and> vpeq u b c) \<longrightarrow> vpeq u a c"
    and vpeq_symmetric: "\<forall> a b u. vpeq u a b \<longrightarrow> vpeq u b a"
    and vpeq_reflexive: "\<forall> a u. vpeq u a a"
    and ifp_reflexive: "\<forall> u . ifp u u"     
    and weakly_step_consistent: "\<forall> s t u a. vpeq u s t \<and> vpeq (current s) s t \<and> kprecondition s a \<and> kprecondition t a \<and> current s = current t  \<longrightarrow> vpeq u (kstep s a) (kstep t a)"
    and locally_respects: "\<forall> a s u. \<not>ifp (current s) u  \<and> kprecondition s a \<longrightarrow> vpeq u s (kstep s a)"
    and output_consistent: "\<forall> a s t. vpeq (current s) s t \<and> current s = current t \<longrightarrow> (output_f s a) = (output_f t a)"
    and step_atomicity: "\<forall> s a . current (kstep s a) = current s"
    and cswitch_independent_of_state: "\<forall> n s t . current s = current t \<longrightarrow> current (cswitch n s) = current (cswitch n t)"
    and cswitch_consistency: "\<forall> u s t n . vpeq u s t \<longrightarrow> vpeq u (cswitch n s) (cswitch n t)"
    and next_action_consistent: "\<forall> s t execs . vpeq (current s) s t \<and> (\<forall> d \<in> involved (next_action s execs) . vpeq d s t) \<and> current s = current t \<longrightarrow> next_action s execs = next_action t execs"
    and next_execs_consistent: "\<forall> s t execs . vpeq (current s) s t \<and> (\<forall> d \<in> involved (next_action s execs) . vpeq d s t) \<and> current s = current t \<longrightarrow> fst (snd (control s (current s) (execs (current s)))) = fst (snd (control t (current s) (execs (current s))))"
    and next_state_consistent: "\<forall> s t u execs . vpeq (current s) s t \<and> vpeq u s t \<and> current s = current t \<longrightarrow> vpeq u (next_state s execs) (next_state t execs)"
    and current_next_state: "\<forall> s execs . current (next_state s execs) = current s" 
    and locally_respects_next_state: "\<forall> s u execs. \<not>ifp (current s) u \<longrightarrow> vpeq u s (next_state s execs)"
    and involved_ifp: "\<forall> s a . \<forall> d \<in> (involved a) . kprecondition s (the a) \<longrightarrow> ifp d (current s)"    
    and next_action_from_execs: "\<forall> s execs . next_action s execs \<rightharpoonup> (\<lambda> a . a \<in> actions_in_execution (execs (current s)))"
    and next_execs_subset: "\<forall>s execs u . actions_in_execution (next_execs s execs u) \<subseteq> actions_in_execution (execs u)"
begin


text \<open>
  Note that there are no proof obligations on function ``interrupt''.
  Its typing enforces the assumptions that switching is based on time and not on state.
  This assumption is sufficient for these proofs, i.e., no further assumptions are required.
\<close>

subsubsection \<open>Security for non-interfering domains\<close>
text \<open>
  We define security for domains that are completely non-interfering.
  That is, for all domains $u$ and $v$ such that $v$ may not interfere in any way with domain $u$, we prove that the behavior of domain $u$ is independent of the actions performed by $v$.
  In other words, the output of domain $u$ in some run is at all times equivalent to the output of domain $u$ when the actions of domain $v$ are replaced by some other set actions.
\<close>

text \<open>
  A domain is unrelated to $u$ if and only if the security policy dictates that there is no path from the domain to $u$.
\<close>
abbreviation unrelated :: "'dom_t \<Rightarrow> 'dom_t \<Rightarrow> bool"
where "unrelated d u \<equiv> \<not>ifp^** d u"
text \<open>
  To formulate the new theorem to prove, we redefine purging: all domains that may not influence domain u are replaced by arbitrary action sequences.
\<close>
definition purge ::
  "('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> 'dom_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution)"
where "purge execs u \<equiv> \<lambda> d . (if unrelated d u then
                                (SOME alpha . realistic_execution alpha)
                              else execs d)"
text \<open>
  A normal run from initial state $s0$ ending in state $s\_f$ is equivalent to a run purged for domain $(\mbox{current} s\_f)$.
\<close>
definition NI_unrelated where "NI_unrelated
  \<equiv> \<forall> execs a n . run n (Some s0) execs \<rightharpoonup>
                   (\<lambda> s_f . run n (Some s0) (purge execs (current s_f)) \<rightharpoonup>
                                  (\<lambda> s_f2 . output_f s_f a = output_f s_f2 a \<and> current s_f = current s_f2))"


text \<open>The following properties are proven inductive over states $s$ and $t$:
\begin{enumerate}
\item Invariably, states $s$ and $t$ are equivalent for any domain $v$ that may influence the purged domain $u$.
This is more general than proving that ``vpeq u s t'' is inductive. The reason we need to prove equivalence
over all domains $v$ is so that we can use \emph{weak} step consistency.
\item Invariably, states $s$ and $t$ have the same active domain.\
\end{enumerate}
\<close>
abbreviation equivalent_states :: "'state_t option  \<Rightarrow> 'state_t option \<Rightarrow> 'dom_t \<Rightarrow> bool"
where "equivalent_states s t u \<equiv> s \<parallel> t \<rightharpoonup> (\<lambda> s t . (\<forall> v . ifp^** v u \<longrightarrow> vpeq v s t) \<and> current s = current t)"

text \<open>
  Rushby's view partitioning is redefined.
  Two states that are initially $u$-equivalent are $u$-equivalent after performing respectively a realistic run and a realistic purged run.
\<close>
definition view_partitioned::bool where "view_partitioned
  \<equiv> \<forall> execs ms mt n u . equivalent_states ms mt u  \<longrightarrow>
        (run n ms execs \<parallel>
         run n mt (purge execs u) \<rightharpoonup>
         (\<lambda> rs rt . vpeq u rs rt \<and> current rs = current rt))"
text \<open>
  We formulate a version of predicate view\_partitioned that is on one hand more general, but on the other hand easier to prove inductive over function run. 
  Instead of reasoning over execs and (purge execs u), we reason over any two executions execs1 and execs2 for which the following relation holds:
\<close>
definition purged_relation :: "'dom_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> bool"
where "purged_relation u execs1 execs2 \<equiv> \<forall> d . ifp^** d u \<longrightarrow> execs1 d = execs2 d"
text\<open>
  The inductive version of view partitioning says that runs on two states that are $u$-equivalent and on two executions that are purged\_related yield $u$-equivalent states.
\<close>
definition view_partitioned_ind::bool where "view_partitioned_ind
  \<equiv> \<forall> execs1 execs2 s t n u . equivalent_states s t u \<and> purged_relation u execs1 execs2 \<longrightarrow> equivalent_states (run n s execs1) (run n t execs2) u"


text \<open>
  A proof that when state $t$ performs a step but state $s$ not, the states remain equivalent for any domain $v$ that may interfere with $u$.
\<close>
lemma vpeq_s_nt:
  assumes prec_t: "precondition (next_state t execs2) (next_action t execs2)"
  assumes not_ifp_curr_u: "\<not> ifp^** (current t) u"
  assumes vpeq_s_t: "\<forall> v . ifp^** v u \<longrightarrow> vpeq v s t"
  shows "(\<forall> v . ifp^** v u \<longrightarrow> vpeq v s (step (next_state t execs2) (next_action t execs2)))"
proof-
  {
    fix v
    assume ifp_v_u: "ifp^** v u"
    
    from ifp_v_u not_ifp_curr_u have unrelated: "\<not>ifp^** (current t) v" using rtranclp_trans by metis
    from this current_next_state[THEN spec,THEN spec,where x1=t]
         locally_respects[THEN spec,THEN spec,THEN spec,where x1="next_state t execs2"] vpeq_reflexive
         prec_t have "vpeq v (next_state t execs2) (step (next_state t execs2) (next_action t execs2))"
         unfolding step_def precondition_def B_def
         by (cases "next_action t execs2",auto)
    from unrelated this locally_respects_next_state vpeq_transitive have "vpeq v t (step (next_state t execs2) (next_action t execs2))" by blast
    from this and ifp_v_u and vpeq_s_t and vpeq_symmetric and vpeq_transitive have "vpeq v s (step (next_state t execs2) (next_action t execs2))" by metis
  }
thus ?thesis by auto
qed
text \<open>
  A proof that when state $s$ performs a step but state $t$ not, the states remain equivalent for any domain $v$ that may interfere with $u$.
\<close>
lemma vpeq_ns_t:
  assumes prec_s: "precondition (next_state s execs) (next_action s execs)"
  assumes not_ifp_curr_u: "\<not> ifp^** (current s) u"
  assumes vpeq_s_t: "\<forall> v . ifp^** v u \<longrightarrow> vpeq v s t"
  shows "\<forall> v . ifp^** v u \<longrightarrow> vpeq v (step (next_state s execs) (next_action s execs)) t"
proof-
  {
    fix v
    assume ifp_v_u: "ifp^** v u"
    
    from ifp_v_u and not_ifp_curr_u have unrelated: "\<not>ifp^** (current s) v" using rtranclp_trans by metis
    from this current_next_state[THEN spec,THEN spec,where x1=s] vpeq_reflexive
         unrelated locally_respects[THEN spec,THEN spec,THEN spec,where x1="next_state s execs" and x=v and x2="the (next_action s execs)"] prec_s
      have "vpeq v (next_state s execs) (step (next_state s execs) (next_action s execs))"
      unfolding step_def precondition_def B_def
      by (cases "next_action s execs",auto)
    from unrelated this locally_respects_next_state vpeq_transitive have "vpeq v s (step (next_state s execs) (next_action s execs))" by blast
    from this and ifp_v_u and vpeq_s_t and vpeq_symmetric and vpeq_transitive have "vpeq v (step (next_state s execs) (next_action s execs)) t" by metis
  }
thus ?thesis by auto
qed   

text \<open>
  A proof that when both states $s$ and $t$ perform a step, the states remain equivalent for any domain $v$ that may interfere with $u$.
  It assumes that the current domain \emph{can} interact with $u$ (the domain for which is purged).
\<close>
lemma vpeq_ns_nt_ifp_u:
assumes vpeq_s_t: "\<forall> v . ifp^** v u \<longrightarrow> vpeq v s t'"
    and current_s_t: "current s = current t'"
shows "precondition (next_state s execs) a \<and> precondition (next_state t' execs) a \<Longrightarrow> (ifp^** (current s) u \<Longrightarrow>  (\<forall> v . ifp^** v u \<longrightarrow> vpeq v (step (next_state s execs) a) (step (next_state t' execs) a)))"
proof-
  fix a
  assume precs: "precondition (next_state s execs) a \<and> precondition (next_state t' execs) a"
  assume ifp_curr: "ifp^** (current s) u"
  from vpeq_s_t have vpeq_curr_s_t: "ifp^** (current s) u \<longrightarrow> vpeq (current s) s t'" by auto
  from ifp_curr precs
    next_state_consistent[THEN spec,THEN spec,where x1=s and x=t'] vpeq_curr_s_t vpeq_s_t
    current_next_state current_s_t weakly_step_consistent[THEN spec,THEN spec,THEN spec,THEN spec,where x3="next_state s execs" and x2="next_state t' execs" and x="the a"]
  show "\<forall> v . ifp^** v u \<longrightarrow> vpeq v (step (next_state s execs) a) (step (next_state t' execs) a)"
    unfolding step_def precondition_def B_def
    by (cases a,auto)
qed
      
text \<open>
  A proof that when both states $s$ and $t$ perform a step, the states remain equivalent for any domain $v$ that may interfere with $u$.
  It assumes that the current domain \emph{cannot} interact with $u$ (the domain for which is purged).
\<close>
lemma vpeq_ns_nt_not_ifp_u:
assumes purged_a_a2: "purged_relation u execs execs2"
    and prec_s: "precondition (next_state s execs) (next_action s execs)"
    and current_s_t: "current s = current t'"
    and vpeq_s_t: "\<forall> v . ifp^** v u \<longrightarrow> vpeq v s t'"
shows "\<not>ifp^** (current s) u \<and> precondition (next_state t' execs2) (next_action t' execs2) \<longrightarrow> (\<forall> v . ifp^** v u \<longrightarrow> vpeq v (step (next_state s execs) (next_action s execs)) (step (next_state t' execs2) (next_action t' execs2)))"
proof-
  {
    assume not_ifp: "\<not>ifp^** (current s) u"
    assume prec_t: "precondition (next_state t' execs2) (next_action t' execs2)"
    fix a a' v
    assume ifp_v_u: "ifp^** v u"
    from not_ifp and purged_a_a2 have "\<not>ifp^** (current s) u" unfolding purged_relation_def by auto
    from this and ifp_v_u have not_ifp_curr_v: "\<not>ifp^** (current s) v" using rtranclp_trans by metis
    from this current_next_state[THEN spec,THEN spec,where x1=s and x=execs] prec_s vpeq_reflexive
       locally_respects[THEN spec,THEN spec,THEN spec,where x1="next_state s execs" and x2="the (next_action s execs)" and x=v]
       have "vpeq v (next_state s execs) (step (next_state s execs) (next_action s execs))"
       unfolding step_def precondition_def B_def
       by (cases "next_action s execs",auto)
    from not_ifp_curr_v this locally_respects_next_state vpeq_transitive
      have vpeq_s_ns: "vpeq v s (step (next_state s execs) (next_action s execs))"
      by blast
    from not_ifp_curr_v current_s_t current_next_state[THEN spec,THEN spec,where x1=t' and x=execs2] prec_t
       locally_respects[THEN spec,THEN spec,where x="next_state t' execs2"] vpeq_reflexive
       have 0: "vpeq v (next_state t' execs2) (step (next_state t' execs2) (next_action t' execs2))"
       unfolding step_def precondition_def B_def
       by (cases "next_action t' execs2",auto)
    from not_ifp_curr_v current_s_t current_next_state have 1: "\<not>ifp^** (current t') v"
      using rtranclp_trans by auto
    from 0 1 locally_respects_next_state vpeq_transitive 
       have vpeq_t_nt: "vpeq v t' (step (next_state t' execs2) (next_action t' execs2))"
       by blast
    from vpeq_s_ns and vpeq_t_nt and vpeq_s_t and ifp_v_u and vpeq_symmetric and vpeq_transitive
      have vpeq_ns_nt: "vpeq v (step (next_state s execs) (next_action s execs)) (step (next_state t' execs2) (next_action t' execs2))"
      by blast
  }
  thus ?thesis by auto
qed


text \<open>
  A run with a purged list of actions appears identical to a run without purging, when starting from two states that appear identical.
\<close>
lemma unwinding_implies_view_partitioned_ind: 
shows view_partitioned_ind
proof-
{
  fix execs execs2 s t n u
  have "equivalent_states s t u \<and> purged_relation u execs execs2 \<longrightarrow> equivalent_states (run n s execs) (run n t execs2) u"
  proof (induct n s execs arbitrary: t u execs2 rule: run.induct)
    case (1 s execs t u execs2)
      show ?case by auto
    next
    case (2 n execs t u execs2)
      show ?case by simp
    next
    case (3 n s execs t u execs2)
    assume interrupt_s: "interrupt (Suc n)"
    assume IH: "(\<And>t u execs2.
           equivalent_states (Some (cswitch (Suc n) s)) t u \<and> purged_relation u execs execs2 \<longrightarrow>
           equivalent_states (run n (Some (cswitch (Suc n) s)) execs) (run n t execs2) u)"
    {
      fix t'
      assume "t = Some t'"
      fix rs
      assume rs: "run (Suc n) (Some s) execs = Some rs"
      fix rt
      assume rt: "run (Suc n) (Some t') execs2 = Some rt"
      
      assume vpeq_s_t: "\<forall> v . ifp^** v u \<longrightarrow> vpeq v s t'"
      assume current_s_t: "current s = current t'"
      assume purged_a_a2: "purged_relation u execs execs2"

      \<comment> \<open>The following terminology is used: states rs and rt (for: run-s and run-t) are the states after a run.
         States ns and nt (for: next-s and next-t) are the states after one step.\<close>
      \<comment> \<open>We prove two properties: the states rs and rt have equal active domains (current-rs-rt) and are vpeq for all domains v that may influence u (vpeq-rs-rt).
          Both are proven using the IH.
          To use the IH, we have to prove that the properties hold for the next step (in this case, a context switch).
          Statement current-ns-nt states that after one step states ns and nt have the same active domain.
          Statement vpeq-ns-nt states that after one step states ns and nt are vpeq for all domains v that may influence u (vpeq-rs-rt).\<close>
      from current_s_t cswitch_independent_of_state
        have current_ns_nt: "current (cswitch (Suc n) s) = current (cswitch (Suc n) t')" by blast
      from cswitch_consistency vpeq_s_t
        have vpeq_ns_nt: "\<forall> v . ifp^** v u \<longrightarrow> vpeq v (cswitch (Suc n) s) (cswitch (Suc n) t')" by auto
      from current_ns_nt vpeq_ns_nt interrupt_s vpeq_reflexive purged_a_a2 current_s_t IH[where u=u and t="Some (cswitch (Suc n) t')" and ?execs2.0=execs2]
      have current_rs_rt: "current rs = current rt" using rs rt by(auto)
      {
        fix v
        assume ia: "ifp^** v u"
        from current_ns_nt vpeq_ns_nt ia interrupt_s vpeq_reflexive purged_a_a2 IH[where u=u and t="Some (cswitch (Suc n) t')" and ?execs2.0=execs2]
        have vpeq_rs_rt: "vpeq v rs rt" using rs rt by(auto)
      }
      from current_rs_rt and this have "equivalent_states (Some rs) (Some rt) u" by auto
    }
    thus ?case by(simp add:option.splits,cases t,simp+)
    next
    case (4 n execs s t u execs2)
    assume not_interrupt: "\<not>interrupt (Suc n)"
    assume thread_empty_s: "thread_empty(execs (current s))"
    assume IH: "(\<And>t u execs2. equivalent_states (Some s) t u \<and> purged_relation u execs execs2 \<longrightarrow> equivalent_states (run n (Some s) execs) (run n t execs2) u)"
    {
      fix t'
      assume t: "t = Some t'"
      fix rs
      assume rs: "run (Suc n) (Some s) execs = Some rs"
      fix rt
      assume rt: "run (Suc n) (Some t') execs2 = Some rt"
    
      assume vpeq_s_t: "\<forall> v . ifp^** v u \<longrightarrow> vpeq v s t'"
      assume current_s_t: "current s = current t'"
      assume purged_a_a2: "purged_relation u execs execs2"
      
      \<comment> \<open>The following terminology is used: states rs and rt (for: run-s and run-t) are the states after a run.
         States ns and nt (for: next-s and next-t) are the states after one step.\<close>
      \<comment> \<open>We prove two properties: the states rs and rt have equal active domains (current-rs-rt) and are vpeq for all domains v that may influence u (vpeq-rs-rt).
          Both are proven using the IH.
          To use the IH, we have to prove that the properties hold for the next step (in this case, nothing happens in s as the thread is empty).
          Statement current-ns-nt states that after one step states ns and nt have the same active domain.
          Statement $vpeq\_ns\_nt$ states that after one step states ns and nt are vpeq for all domains v that may influence u (vpeq-rs-rt).\<close>
          
      from ifp_reflexive and vpeq_s_t have vpeq_s_t_u: "vpeq u s t'" by auto
      from thread_empty_s and purged_a_a2 and current_s_t have purged_a_na2: "\<not>ifp^** (current t') u \<longrightarrow> purged_relation u execs (next_execs t' execs2)"
        by(unfold next_execs_def,unfold purged_relation_def,auto)
      from step_atomicity current_next_state current_s_t have current_s_nt: "current s = current (step (next_state t' execs2) (next_action t' execs2))"
        unfolding step_def
        by (cases "next_action t' execs2",auto)

      \<comment> \<open>The proof is by case distinction. If the current thread is empty in state t as well (case t-empty), then nothing happens and the proof is trivial.
          Otherwise (case t-not-empty), since the current thread has different executions in states s and t, we now show that it cannot influence u (statement not-ifp-curr-t).
          If in state t the precondition holds (case t-prec), locally respects shows that the states remain vpeq.
          Otherwise, (case t-not-prec), everything holds vacuously.\<close>
      have current_rs_rt: "current rs = current rt"
      proof (cases "thread_empty(execs2 (current t'))" rule :case_split[case_names t_empty t_not_empty])
      case t_empty
        from purged_a_a2 and vpeq_s_t and current_s_t IH[where t="Some t'" and u=u and ?execs2.0=execs2]
          have "equivalent_states (run n (Some s) execs) (run n (Some t') execs2) u" using rs rt by(auto)        
        from this not_interrupt t_empty thread_empty_s
          show ?thesis using rs rt by(auto)
      next
      case t_not_empty
        from t_not_empty current_next_state and vpeq_s_t_u and thread_empty_s and purged_a_a2 and current_s_t
          have not_ifp_curr_t: "\<not>ifp^** (current (next_state t' execs2)) u" unfolding purged_relation_def by auto
        show ?thesis
        proof (cases "precondition (next_state t' execs2) (next_action t' execs2)" rule :case_split[case_names t_prec t_not_prec])
        case t_prec
          from locally_respects_next_state current_next_state t_prec not_ifp_curr_t vpeq_s_t locally_respects vpeq_s_nt 
            have vpeq_s_nt: "(\<forall> v . ifp^** v u \<longrightarrow> vpeq v s (step (next_state t' execs2) (next_action t' execs2)))" by auto
          from vpeq_s_nt purged_a_na2 this current_s_nt not_ifp_curr_t current_next_state
                IH[where t="Some (step (next_state t' execs2) (next_action t' execs2))" and u=u and ?execs2.0="next_execs t' execs2"]
            have "equivalent_states (run n (Some s) execs) (run n (Some (step (next_state t' execs2) (next_action t' execs2))) (next_execs t' execs2)) u"
            using rs rt by auto
          from t_not_empty t_prec vpeq_s_nt this thread_empty_s not_interrupt 
            show ?thesis using rs rt  by auto
        next
        case t_not_prec
          thus ?thesis using rt t_not_empty not_interrupt by(auto)
        qed
      qed
      {
        fix v
        assume ia: "ifp^** v u"
        have "vpeq v rs rt"
        proof (cases "thread_empty(execs2 (current t'))" rule :case_split[case_names t_empty t_not_empty])
          case t_empty
            from purged_a_a2 and vpeq_s_t and current_s_t IH[where t="Some t'" and u=u and ?execs2.0=execs2]
              have "equivalent_states (run n (Some s) execs) (run n (Some t') execs2) u" using rs rt by(auto)        
            from ia this not_interrupt t_empty thread_empty_s
              show ?thesis using rs rt by(auto)
          next
          case t_not_empty
            show ?thesis
            proof (cases "precondition (next_state t' execs2) (next_action t' execs2)" rule :case_split[case_names t_prec t_not_prec])
            case t_prec
              from t_not_empty current_next_state and vpeq_s_t_u and thread_empty_s and purged_a_a2 and current_s_t
                have not_ifp_curr_t: "\<not>ifp^** (current (next_state t' execs2)) u" unfolding purged_relation_def
                by auto
              from t_prec current_next_state locally_respects_next_state this and vpeq_s_t and locally_respects and vpeq_s_nt
                have vpeq_s_nt: "(\<forall> v . ifp^** v u \<longrightarrow> vpeq v s (step (next_state t' execs2) (next_action t' execs2)))" by auto
              from purged_a_na2 this current_s_nt not_ifp_curr_t current_next_state
                   IH[where t="Some (step (next_state t' execs2) (next_action t' execs2))" and u=u and ?execs2.0="next_execs t' execs2"]
                have "equivalent_states (run n (Some s) execs) (run n (Some (step (next_state t' execs2) (next_action t' execs2))) (next_execs t' execs2)) u"
                using rs rt by(auto)
              from ia t_not_empty t_prec vpeq_s_nt this thread_empty_s not_interrupt 
              show ?thesis using rs rt by auto
            next
            case t_not_prec
              thus ?thesis using rt t_not_empty not_interrupt by(auto)
            qed
        qed
      }
      from current_rs_rt and this have "equivalent_states (Some rs) (Some rt) u" by auto
    }
    thus ?case by(simp add:option.splits,cases t,simp+)
    next
    case (5 n execs s t u execs2)
    assume not_interrupt: "\<not>interrupt (Suc n)"
    assume thread_not_empty_s: "\<not>thread_empty(execs (current s))"
    assume not_prec_s: "\<not> precondition (next_state s execs) (next_action s execs)"
    \<comment> \<open>Whenever the precondition does not hold, the entire theorem flattens to True and everything holds vacuously.\<close>
    hence "run (Suc n) (Some s) execs = None" using not_interrupt thread_not_empty_s by simp
    thus ?case by(simp add:option.splits)
    next
    case (6 n execs s t u execs2)
    assume not_interrupt: "\<not>interrupt (Suc n)"
    assume thread_not_empty_s: "\<not>thread_empty(execs (current s))"
    assume prec_s: "precondition (next_state s execs) (next_action s execs)"
    assume IH: "(\<And>t u execs2.
           equivalent_states (Some (step (next_state s execs) (next_action s execs))) t u \<and>
           purged_relation u (next_execs s execs) execs2 \<longrightarrow>
           equivalent_states
            (run n (Some (step (next_state s execs) (next_action s execs))) (next_execs s execs))
            (run n t execs2) u)"
    {
      fix t'
      assume t: "t = Some t'"
      fix rs
      assume rs: "run (Suc n) (Some s) execs = Some rs"
      fix rt
      assume rt: "run (Suc n) (Some t') execs2 = Some rt"
      
      assume vpeq_s_t: "\<forall> v . ifp^** v u \<longrightarrow> vpeq v s t'"
      assume current_s_t: "current s = current t'"
      assume purged_a_a2: "purged_relation u execs execs2"

      \<comment> \<open>The following terminology is used: states rs and rt (for: run-s and run-t) are the states after a run.
         States ns and nt (for: next-s and next-t) are the states after one step.\<close>
      \<comment> \<open>We prove two properties: the states rs and rt have equal active domains (current-rs-rt) and are vpeq for all domains v that may influence u (vpeq-rs-rt).
          Both are proven using the IH.
          To use the IH, we have to prove that the properties hold for the next step (in this case, state s executes an action).
          Statement current-ns-nt states that after one step states ns and nt have the same active domain.
          Statement vpeq-ns-nt states that after one step states ns and nt are vpeq for all domains v that may influence u (vpeq-rs-rt).\<close>
          
      \<comment> \<open>Some lemma's used in the remainder of this case.\<close>
      from ifp_reflexive and vpeq_s_t have vpeq_s_t_u: "vpeq u s t'" by auto
      from step_atomicity and current_s_t current_next_state
        have current_ns_nt: "current (step (next_state s execs) (next_action s execs)) = current (step (next_state t' execs2) (next_action t' execs2))"
        unfolding step_def
        by (cases "next_action s execs",cases "next_action t' execs2",simp,simp,cases "next_action t' execs2",simp,simp) 
      from vpeq_s_t have vpeq_curr_s_t: "ifp^** (current s) u \<longrightarrow> vpeq (current s) s t'" by auto
      from prec_s involved_ifp[THEN spec,THEN spec,where x1="next_state s execs" and x="next_action s execs"] vpeq_s_t have vpeq_involved: "ifp^** (current s) u \<longrightarrow> (\<forall> d \<in> involved (next_action s execs) . vpeq d s t')"
        using current_next_state
        unfolding involved_def precondition_def B_def
        by(cases "next_action s execs",simp,auto,metis converse_rtranclp_into_rtranclp)
      from current_s_t next_execs_consistent vpeq_curr_s_t vpeq_involved
        have next_execs_t: "ifp^** (current s) u \<longrightarrow> next_execs t' execs = next_execs s execs"
        unfolding next_execs_def
        by(auto)
      from current_s_t purged_a_a2  thread_not_empty_s next_action_consistent[THEN spec,THEN spec,where x1=s and x=t'] vpeq_curr_s_t vpeq_involved
        have next_action_s_t: "ifp^** (current s) u \<longrightarrow> next_action t' execs2 = next_action s execs"
        by(unfold next_action_def,unfold purged_relation_def,auto)
      from purged_a_a2 current_s_t next_execs_consistent[THEN spec,THEN spec,THEN spec,where x2=s and x1=t' and x="execs"]
           vpeq_curr_s_t vpeq_involved
        have purged_na_na2: "purged_relation u (next_execs s execs) (next_execs t' execs2)"
        unfolding next_execs_def purged_relation_def
        by(auto)
      from purged_a_a2 and purged_relation_def and thread_not_empty_s and current_s_t have thread_not_empty_t: "ifp^** (current s) u \<longrightarrow> \<not>thread_empty(execs2 (current t'))" by auto
      from step_atomicity current_s_t current_next_state have current_ns_t: "current (step (next_state s execs) (next_action s execs)) = current t'"
        unfolding step_def
        by (cases "next_action s execs",auto)
      from step_atomicity and current_s_t have current_s_nt: "current s = current (step t' (next_action t' execs2))"
        unfolding step_def
        by (cases "next_action t' execs2",auto)      
      from purged_a_a2 have purged_na_a: "\<not>ifp^** (current s) u \<longrightarrow> purged_relation u (next_execs s execs) execs2"
         by(unfold next_execs_def,unfold purged_relation_def,auto)

      \<comment> \<open>The proof is by case distinction. If the current domain can interact with u (case curr-ifp-u), then either in state t the precondition holds (case t-prec) or not.
          If it holds, then lemma vpeq-ns-nt-ifp-u applies. Otherwise, the proof is trivial as the theorem holds vacuously.
          If the domain cannot interact with u, (case curr-not-ifp-u), then lemma vpeq-ns-nt-not-ifp-u applies.\<close>
      have current_rs_rt: "current rs = current rt"
      proof (cases "ifp^** (current s) u" rule :case_split[case_names curr_ifp_u curr_not_ifp_u])
      case curr_ifp_u
        show ?thesis
        proof (cases "precondition (next_state t' execs2) (next_action t' execs2)" rule :case_split[case_names prec_t prec_not_t])
        case prec_t
          have thread_not_empty_t: "\<not>thread_empty(execs2 (current t'))" using thread_not_empty_t curr_ifp_u by auto
          from
            current_ns_nt next_execs_t next_action_s_t purged_a_a2
            curr_ifp_u prec_t prec_s vpeq_ns_nt_ifp_u[where a="(next_action s execs)"] vpeq_s_t current_s_t
            have "equivalent_states (Some (step (next_state s execs) (next_action s execs))) (Some (step (next_state t' execs2) (next_action t' execs2))) u"
            unfolding purged_relation_def next_state_def 
            by auto
          from this
            IH[where u=u and ?execs2.0="(next_execs t' execs2)" and t="Some (step (next_state t' execs2) (next_action t' execs2))"] 
            current_ns_nt purged_na_na2
            have "equivalent_states (run n (Some (step (next_state s execs) (next_action s execs))) (next_execs s execs))
                                    (run n (Some (step (next_state t' execs2) (next_action t' execs2))) (next_execs t' execs2)) u"
            by auto
            from prec_t thread_not_empty_t prec_s and this and not_interrupt and thread_not_empty_s and next_action_s_t
              show ?thesis using rs rt by auto
        next
        case prec_not_t
          from curr_ifp_u prec_not_t thread_not_empty_t not_interrupt show ?thesis using rt by simp
        qed
      next
      case curr_not_ifp_u
        show ?thesis
        proof (cases "thread_empty(execs2 (current t'))" rule :case_split[case_names t_empty t_not_empty])
        case t_not_empty
          show ?thesis
          proof (cases "precondition (next_state t' execs2) (next_action t' execs2)" rule :case_split[case_names t_prec t_not_prec])
          case t_prec
            from curr_not_ifp_u t_prec IH[where u=u and ?execs2.0="(next_execs t' execs2)" and t="Some (step (next_state t' execs2) (next_action t' execs2))"]
                 current_ns_nt next_execs_t purged_na_na2 vpeq_ns_nt_not_ifp_u current_s_t vpeq_s_t prec_s purged_a_a2
             have "equivalent_states (run n (Some (step (next_state s execs) (next_action s execs))) (next_execs s execs))
                                     (run n (Some (step (next_state t' execs2) (next_action t' execs2))) (next_execs t' execs2)) u" by auto  
            from this t_prec curr_not_ifp_u t_not_empty prec_s not_interrupt thread_not_empty_s show ?thesis using rs rt by auto
          next
          case t_not_prec
            from t_not_prec t_not_empty not_interrupt show ?thesis using rt by simp
          qed
        next
        case t_empty
          from curr_not_ifp_u and prec_s and vpeq_s_t and locally_respects and vpeq_ns_t current_next_state locally_respects_next_state
            have vpeq_ns_t: "(\<forall> v . ifp^** v u \<longrightarrow> vpeq v (step (next_state s execs) (next_action s execs)) t')"
            by blast
          from curr_not_ifp_u IH[where t="Some t'" and u=u and ?execs2.0=execs2] and current_ns_t and next_execs_t and purged_na_a and vpeq_ns_t and this
          have "equivalent_states (run n (Some (step (next_state s execs) (next_action s execs))) (next_execs s execs)) 
                                  (run n (Some t')  execs2) u" by auto
          from this not_interrupt thread_not_empty_s t_empty prec_s show ?thesis using rs rt by auto
        qed
      qed
      {
        fix v
        assume ia: "ifp^** v u"

        have "vpeq v rs rt"
        proof (cases "ifp^** (current s) u" rule :case_split[case_names curr_ifp_u curr_not_ifp_u])
        case curr_ifp_u
        show ?thesis
        proof (cases "precondition (next_state t' execs2) (next_action t' execs2)" rule :case_split[case_names t_prec t_not_prec])
          case t_prec
            have thread_not_empty_t: "\<not>thread_empty(execs2 (current t'))" using thread_not_empty_t curr_ifp_u by auto
            from
              current_ns_nt next_execs_t next_action_s_t purged_a_a2
              curr_ifp_u t_prec  prec_s vpeq_ns_nt_ifp_u[where a="(next_action s execs)"] vpeq_s_t current_s_t
              have "equivalent_states (Some (step (next_state s execs) (next_action s execs))) (Some (step (next_state t' execs2) (next_action t' execs2))) u"
              unfolding purged_relation_def next_state_def 
              by auto
            from this
              IH[where u=u and ?execs2.0="(next_execs t' execs2)" and t="Some (step (next_state t' execs2) (next_action t' execs2))"] 
              current_ns_nt purged_na_na2
              have "equivalent_states (run n (Some (step (next_state s execs) (next_action s execs))) (next_execs s execs))
                                      (run n (Some (step (next_state t' execs2) (next_action t' execs2))) (next_execs t' execs2)) u"
              by auto
              from ia curr_ifp_u t_prec thread_not_empty_t prec_s and this and not_interrupt and thread_not_empty_s and next_action_s_t
                show ?thesis using rs rt by auto
          next
          case t_not_prec
            from curr_ifp_u t_not_prec thread_not_empty_t not_interrupt show ?thesis using rt by simp
          qed
        next
        case curr_not_ifp_u
          show ?thesis
          proof (cases "thread_empty(execs2 (current t'))" rule :case_split[case_names t_empty t_not_empty])
          case t_not_empty
            show ?thesis
            proof (cases "precondition (next_state t' execs2) (next_action t' execs2)" rule :case_split[case_names t_prec t_not_prec])
            case t_prec
              from curr_not_ifp_u t_prec IH[where u=u and ?execs2.0="(next_execs t' execs2)" and t="Some (step (next_state t' execs2) (next_action t' execs2))"]
                   current_ns_nt next_execs_t purged_na_na2 vpeq_ns_nt_not_ifp_u current_s_t vpeq_s_t prec_s purged_a_a2
               have "equivalent_states (run n (Some (step (next_state s execs) (next_action s execs))) (next_execs s execs))
                                       (run n (Some (step (next_state t' execs2) (next_action t' execs2))) (next_execs t' execs2)) u" by auto  
              from ia this t_prec curr_not_ifp_u t_not_empty prec_s not_interrupt thread_not_empty_s show ?thesis using rs rt by auto
            next
            case t_not_prec
              from t_not_prec t_not_empty not_interrupt show ?thesis using rt by simp
            qed
          next
          case t_empty
            from curr_not_ifp_u prec_s and vpeq_s_t and locally_respects and vpeq_ns_t current_next_state locally_respects_next_state
              have vpeq_ns_t: "(\<forall> v . ifp^** v u \<longrightarrow> vpeq v (step (next_state s execs) (next_action s execs)) t')"
              by blast
            from curr_not_ifp_u IH[where t="Some t'" and u=u and ?execs2.0=execs2] and current_ns_t and next_execs_t and purged_na_a and vpeq_ns_t and this
            have "equivalent_states (run n (Some (step (next_state s execs) (next_action s execs))) (next_execs s execs)) 
                                    (run n (Some t')  execs2) u" by auto
            from ia this not_interrupt thread_not_empty_s t_empty prec_s show ?thesis using rs rt by auto
          qed
        qed
      }
      from current_rs_rt and this have "equivalent_states (Some rs) (Some rt) u" by auto
    }
    thus ?case by(simp add:option.splits,cases t,simp+)
  qed
}
thus ?thesis
  unfolding view_partitioned_ind_def by auto
qed

text \<open>
  From the previous lemma, we can prove that the system is view partitioned.
  The previous lemma was inductive, this lemma just instantiates the previous lemma replacing s and t by the initial state.
\<close>
lemma unwinding_implies_view_partitioned: 
shows view_partitioned
proof-
from unwinding_implies_view_partitioned_ind have view_partitioned_inductive: "view_partitioned_ind"
  by blast
have purged_relation: "\<forall> u execs . purged_relation u execs (purge execs u)"
  by(unfold purged_relation_def, unfold purge_def, auto)
{
  fix execs s t n u
  assume 1: "equivalent_states s t u"
  from this view_partitioned_inductive purged_relation
    have "equivalent_states (run n s execs) (run n t (purge execs u)) u" 
    unfolding view_partitioned_ind_def by auto
  from this ifp_reflexive
    have "run n s execs \<parallel> run n t (purge execs u) \<rightharpoonup> (\<lambda>rs rt. vpeq u rs rt \<and> current rs = current rt)"
    using r_into_rtranclp unfolding B_def
    by(cases "run n s execs",simp,cases "run n t (purge execs u)",simp,auto)
}
thus ?thesis unfolding view_partitioned_def Let_def by auto
qed

text \<open>
  Domains that many not interfere with each other, do not interfere with each other.
\<close>
theorem unwinding_implies_NI_unrelated: 
shows NI_unrelated
proof-
  {
    fix execs a n
    from unwinding_implies_view_partitioned
      have vp: view_partitioned by blast
    from vp and vpeq_reflexive
      have 1: "\<forall> u . (run n (Some s0) execs 
                      \<parallel> run n (Some s0) (purge execs u) 
                          \<rightharpoonup> (\<lambda>rs rt. vpeq u rs rt \<and> current rs = current rt))"
      unfolding view_partitioned_def by auto
    have "run n (Some s0) execs \<rightharpoonup> (\<lambda>s_f. run n (Some s0) (purge execs (current s_f)) \<rightharpoonup> (\<lambda>s_f2. output_f s_f a = output_f s_f2 a \<and> current s_f = current s_f2))"
    proof(cases "run n (Some s0) execs")
    case None
      thus ?thesis unfolding B_def by simp
    next
    case (Some rs)
      thus ?thesis
      proof(cases "run n (Some s0) (purge execs (current rs))")
      case None
        from Some this show ?thesis unfolding B_def by simp
      next
      case (Some rt)
        from \<open>run n (Some s0) execs = Some rs\<close> Some 1[THEN spec,where x="current rs"]
          have vpeq: "vpeq (current rs) rs rt \<and> current rs = current rt"
          unfolding B_def by auto
        from this output_consistent have "output_f rs a = output_f rt a"
           by auto
        from this vpeq \<open>run n (Some s0) execs = Some rs\<close> Some
          show ?thesis unfolding B_def by auto
      qed
    qed
  }
  thus ?thesis unfolding NI_unrelated_def by auto
qed  




subsubsection \<open>Security for indirectly interfering domains\<close>

text \<open>
Consider the following security policy over three domains $A$, $B$ and $C$: $A \leadsto B \leadsto C$,
but $A \not\leadsto C$.
The semantics of this policy is that $A$ may communicate with $C$, but \emph{only} via $B$. No direct communication from $A$ to $C$ is allowed.
We formalize these semantics as follows:
without intermediate domain $B$, domain $A$ cannot flow information to $C$.
In other words, from the point of view of domain $C$ the run where domain $B$ is inactive must be equivalent to the run where domain $B$ is inactive and domain $A$ is replaced by an attacker.
Domain $C$ must be independent of domain $A$, when domain $B$ is inactive.

The aim of this subsection is to formalize the semantics where $A$ can write to $C$ via $B$ \emph{only}.
We define to two ipurge functions. The first purges all domains $d$ that are \emph{intermediary} for some other domain $v$.
An intermediary for $u$ is defined as a domain $d$ for which there exists an information flow from some domain $v$ to $u$ via $d$, but no direct information flow from $v$ to $u$ is allowed.
\<close>
definition intermediary :: "'dom_t \<Rightarrow> 'dom_t \<Rightarrow> bool"
where "intermediary d u \<equiv> \<exists> v . ifp^** v d \<and> ifp d u \<and> \<not>ifp v u \<and> d \<noteq> u"
primrec remove_gateway_communications :: "'dom_t \<Rightarrow> 'action_t execution \<Rightarrow> 'action_t execution"
where "remove_gateway_communications u [] = []"
    | "remove_gateway_communications u (aseq#exec) = (if \<exists> a \<in> set aseq . \<exists> v . intermediary v u \<and> v \<in> involved (Some a) then [] else aseq)#(remove_gateway_communications u exec)"
  
definition ipurge_l ::
  "('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> 'dom_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution)" where
  "ipurge_l execs u \<equiv> \<lambda> d . if intermediary d u then
                              []
                            else if d = u then
                              remove_gateway_communications u (execs u)
                            else execs d"
text \<open>
The second ipurge removes both the intermediaries and the \emph{indirect sources}.
An indirect source for $u$ is defined as a domain that may indirectly flow information to $u$, but not directly.
\<close>
abbreviation ind_source :: "'dom_t \<Rightarrow> 'dom_t \<Rightarrow> bool"
where "ind_source d u \<equiv> ifp^** d u \<and> \<not>ifp d u"
definition ipurge_r ::
  "('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> 'dom_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution)" where
  "ipurge_r execs u \<equiv> \<lambda> d . if intermediary d u then
                              []
                            else if ind_source d u then
                              SOME alpha . realistic_execution alpha
                            else if d = u then
                              remove_gateway_communications u (execs u)
                            else
                              execs d"
text \<open>
For a system with an intransitive policy to be called secure for domain $u$ any indirect source may not flow information towards $u$ when the intermediaries are purged out.
This definition of security allows the information flow $A \leadsto B \leadsto C$, but prohibits $A \leadsto C$.
\<close>
definition NI_indirect_sources ::bool
where "NI_indirect_sources 
  \<equiv> \<forall> execs a n. run n (Some s0) execs \<rightharpoonup>
                   (\<lambda> s_f . (run n (Some s0) (ipurge_l execs (current s_f)) \<parallel>
                             run n (Some s0) (ipurge_r execs  (current s_f)) \<rightharpoonup>
                                 (\<lambda> s_l s_r . output_f s_l a = output_f s_r a)))"
text \<open>
This definition concerns indirect sources only. It does not enforce that an \emph{unrelated} domain may not flow information to $u$.
This is expressed by ``secure''.
\<close>

text \<open>This allows us to define security over intransitive policies.
\<close>
definition isecure::bool
where "isecure \<equiv> NI_indirect_sources  \<and> NI_unrelated"

abbreviation iequivalent_states :: "'state_t option  \<Rightarrow> 'state_t option \<Rightarrow> 'dom_t \<Rightarrow> bool"
where "iequivalent_states s t u \<equiv> s \<parallel> t \<rightharpoonup> (\<lambda> s t . (\<forall> v . ifp v u \<and> \<not>intermediary v u \<longrightarrow> vpeq v s t) \<and> current s = current t)"

definition does_not_communicate_with_gateway
where "does_not_communicate_with_gateway u execs \<equiv> \<forall> a . a \<in> actions_in_execution (execs u) \<longrightarrow> (\<forall> v . intermediary v u \<longrightarrow> v \<notin> involved (Some a))"

definition iview_partitioned::bool where "iview_partitioned
  \<equiv> \<forall> execs ms mt n u . iequivalent_states ms mt u  \<longrightarrow>
        (run n ms (ipurge_l execs u) \<parallel>
         run n mt (ipurge_r execs u) \<rightharpoonup>
         (\<lambda> rs rt . vpeq u rs rt \<and> current rs = current rt))"


definition ipurged_relation1 :: "'dom_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> bool"
where "ipurged_relation1 u execs1 execs2 \<equiv> \<forall> d . (ifp d u \<longrightarrow> execs1 d = execs2 d) \<and> (intermediary d u \<longrightarrow> execs1 d = [])"


text \<open>
  Proof that if the current is not an intermediary for u, then all domains involved in the next action are vpeq.
\<close>
lemma vpeq_involved_domains:
assumes ifp_curr: "ifp (current s) u"
    and not_intermediary_curr: "\<not>intermediary (current s) u"
    and no_gateway_comm: "does_not_communicate_with_gateway u execs"
    and vpeq_s_t: "\<forall> v . ifp v u \<and> \<not>intermediary v u \<longrightarrow> vpeq v s t'"
    and prec_s: "precondition (next_state s execs) (next_action s execs)"
  shows "\<forall> d \<in> involved (next_action s execs) . vpeq d s t'"
proof-
{
  fix v
  assume involved: "v \<in> involved (next_action s execs)"  
  from this prec_s involved_ifp[THEN spec,THEN spec,where x1="next_state s execs" and x="next_action s execs"]
    have ifp_v_curr: "ifp v (current s)" 
    using current_next_state
    unfolding involved_def precondition_def B_def
     by(cases "next_action s execs",auto)
  have "vpeq v s t'"
  proof-
  {
    assume "ifp v u \<and> \<not>intermediary v u"
    from this vpeq_s_t
      have "vpeq v s t'" by (auto)
  }
  moreover
  {
    assume not_intermediary_v: "intermediary v u"
    from ifp_curr not_intermediary_curr ifp_v_curr not_intermediary_v have curr_is_u: "current s = u"
      using rtranclp_trans r_into_rtranclp
      by (metis intermediary_def)
    from curr_is_u next_action_from_execs[THEN spec,THEN spec,where x=execs and x1=s] not_intermediary_v involved
         no_gateway_comm[unfolded does_not_communicate_with_gateway_def,THEN spec,where x="the (next_action s execs)"] 
      have False
      unfolding involved_def B_def
      by (cases "next_action s execs",auto)
    hence "vpeq v s t'" by auto
  }
  moreover
  {
    assume intermediary_v: "\<not> ifp v u"
    from ifp_curr not_intermediary_curr ifp_v_curr intermediary_v
      have "False" unfolding intermediary_def by auto
    hence "vpeq v s t'" by auto
  }
  ultimately
  show "vpeq v s t'" unfolding intermediary_def by auto
  qed
}
thus ?thesis by auto  
qed

text \<open>
  Proof that purging removes communications of the gateway to domain u.
\<close>
lemma ipurge_l_removes_gateway_communications:
shows "does_not_communicate_with_gateway u (ipurge_l execs u)"
proof-
{
  fix aseq u execs a v
  assume 1: "aseq \<in> set (remove_gateway_communications u (execs u))"
  assume 2: "a \<in> set aseq"
  assume 3: "intermediary v u"
  have 4: "v \<notin> involved (Some a)"
  proof-
  {
    fix a::'action_t
    fix aseq u exec v
    have "aseq \<in> set (remove_gateway_communications u exec) \<and> a \<in> set aseq \<and> intermediary v u \<longrightarrow> v \<notin> involved (Some a)"
      by(induct exec,auto)
  }
  from 1 2 3 this show ?thesis by metis
  qed
} 
from this
show ?thesis
  unfolding does_not_communicate_with_gateway_def ipurge_l_def actions_in_execution_def
  by auto
qed

text \<open>
  Proof of view partitioning. The lemma is structured exactly as lemma unwinding\_implies\_view\_partitioned\_ind and uses the same convention for naming.
\<close>
lemma iunwinding_implies_view_partitioned1:
shows iview_partitioned
proof-
{
  fix u execs execs2 s t n
  have "does_not_communicate_with_gateway u execs \<and> iequivalent_states s t u \<and> ipurged_relation1 u execs execs2 \<longrightarrow> iequivalent_states (run n s execs) (run n t execs2) u"
  proof (induct n s execs arbitrary: t u execs2 rule: run.induct)
  case (1 s execs t u execs2)
    show ?case by auto
  next
  case (2 n execs t u execs2)
    show ?case by simp
  next
  case (3 n s execs t u execs2)
    assume interrupt_s: "interrupt (Suc n)"
    assume IH: "(\<And>t u execs2. does_not_communicate_with_gateway u execs \<and>
           iequivalent_states (Some (cswitch (Suc n) s)) t u \<and> ipurged_relation1 u execs execs2 \<longrightarrow>
           iequivalent_states (run n (Some (cswitch (Suc n) s)) execs) (run n t execs2) u)"
    {
      fix t' :: 'state_t
      assume "t = Some t'"
      fix rs
      assume rs: "run (Suc n) (Some s) execs = Some rs"
      fix rt
      assume rt: "run (Suc n) (Some t') execs2 = Some rt"
      
      assume no_gateway_comm: "does_not_communicate_with_gateway u execs"
      assume vpeq_s_t: "\<forall> v . ifp v u \<and> \<not>intermediary v u \<longrightarrow> vpeq v s t'"
      assume current_s_t: "current s = current t'"
      assume purged_a_a2: "ipurged_relation1 u execs execs2"
      
      from current_s_t cswitch_independent_of_state
        have current_ns_nt: "current (cswitch (Suc n) s) = current (cswitch (Suc n) t')"
        by blast
      from cswitch_consistency vpeq_s_t
        have vpeq_ns_nt: "\<forall> v . ifp v u \<and> \<not>intermediary v u \<longrightarrow> vpeq v (cswitch (Suc n) s) (cswitch (Suc n) t')"
        by auto
      from no_gateway_comm current_ns_nt vpeq_ns_nt interrupt_s vpeq_reflexive current_s_t purged_a_a2 IH[where u=u and t="Some (cswitch (Suc n) t')" and ?execs2.0=execs2]
        have current_rs_rt: "current rs = current rt" using rs rt by(auto)
      {
        fix v
        assume ia: "ifp v u \<and> \<not>intermediary v u"
        from no_gateway_comm interrupt_s current_ns_nt vpeq_ns_nt vpeq_reflexive ia current_s_t purged_a_a2 IH[where u=u and t="Some (cswitch (Suc n) t')" and ?execs2.0=execs2]
          have "vpeq v rs rt" using rs rt by(auto)
      }
      from current_rs_rt and this have "iequivalent_states (Some rs) (Some rt) u" by auto
    }
    thus ?case by(simp add:option.splits,cases t,simp+)      
  next
  case (4 n execs s t u execs2)
    assume not_interrupt: "\<not>interrupt (Suc n)"
    assume thread_empty_s: "thread_empty(execs (current s))"
    
    assume IH: "(\<And>t u execs2. does_not_communicate_with_gateway u execs \<and> iequivalent_states (Some s) t u \<and> ipurged_relation1 u execs execs2 \<longrightarrow> iequivalent_states (run n (Some s) execs) (run n t execs2) u)"
    {                                     
      fix t'
      
      assume t: "t = Some t'"
      fix rs
      assume rs: "run (Suc n) (Some s) execs = Some rs"
      fix rt
      assume rt: "run (Suc n) (Some t') execs2 = Some rt"
         
      assume no_gateway_comm: "does_not_communicate_with_gateway u execs"
      assume vpeq_s_t: "\<forall> v . ifp v u \<and> \<not>intermediary v u \<longrightarrow> vpeq v s t'"
      assume current_s_t: "current s = current t'"
      assume purged_a_a2: "ipurged_relation1 u execs execs2"
      
      from ifp_reflexive vpeq_s_t have vpeq_u_s_t: "vpeq u s t'" unfolding intermediary_def by auto
      from step_atomicity current_next_state current_s_t have current_s_nt: "current s = current (step (next_state t' execs2) (next_action t' execs2))"
        unfolding step_def
        by (cases "next_action s execs",cases "next_action t' execs2",simp,simp,cases "next_action t' execs2",simp,simp) 
      from vpeq_s_t have vpeq_curr_s_t: "ifp (current s) u \<and> \<not>intermediary (current s) u \<longrightarrow> vpeq (current s) s t'" by auto        
      have "iequivalent_states (run (Suc n) (Some s) execs) (run (Suc n) (Some t') execs2) u"
      proof(cases "thread_empty(execs2 (current t'))")
      case True
        from purged_a_a2 and vpeq_s_t and current_s_t IH[where t="Some t'" and u=u and ?execs2.0=execs2] no_gateway_comm
          have "iequivalent_states (run n (Some s) execs) (run n (Some t') execs2) u" using rs rt by(auto)
        from this not_interrupt True thread_empty_s
          show ?thesis using rs rt by(auto)
      next
      case False
        have prec_t: "precondition (next_state t' execs2) (next_action t' execs2)" 
        proof-
          {
            assume not_prec_t: "\<not>precondition (next_state t' execs2) (next_action t' execs2)"
            hence "run (Suc n) (Some t') execs2 = None" using not_interrupt False not_prec_t by (simp)
            from this have "False" using rt by(simp add:option.splits)
          }
          thus ?thesis by auto
        qed
        
        from False purged_a_a2 thread_empty_s current_s_t
          have 1: "ind_source (current t') u \<or> unrelated (current t') u" unfolding ipurged_relation1_def intermediary_def by auto
        {
          fix v
          assume ifp_v: "ifp v u"
          assume v_not_intermediary: "\<not>intermediary v u"                    
          
          from 1 ifp_v v_not_intermediary have not_ifp_curr_v: "\<not>ifp (current t') v" unfolding intermediary_def by auto
          from not_ifp_curr_v prec_t locally_respects[THEN spec,THEN spec,THEN spec,where x1="next_state t' execs2" and x=v and x2="the (next_action t' execs2)"]
               current_next_state  vpeq_reflexive
            have "vpeq v (next_state t' execs2) (step (next_state t' execs2) (next_action t' execs2))"
            unfolding step_def precondition_def B_def
            by (cases "next_action t' execs2",auto)
          from this vpeq_transitive not_ifp_curr_v locally_respects_next_state
            have vpeq_t_nt: "vpeq v t' (step (next_state t' execs2) (next_action t' execs2))"
            by blast
          from vpeq_s_t ifp_v v_not_intermediary vpeq_t_nt vpeq_transitive vpeq_symmetric vpeq_reflexive 
            have "vpeq v s (step (next_state t' execs2) (next_action t' execs2))"
            by (metis)
        }
        hence vpeq_ns_nt: "\<forall> v . ifp v u \<and> \<not>intermediary v u \<longrightarrow> vpeq v s (step (next_state t' execs2) (next_action t' execs2))" by auto
        from False purged_a_a2 current_s_t thread_empty_s have purged_a_na2: "ipurged_relation1 u execs (next_execs t' execs2)"
          unfolding ipurged_relation1_def next_execs_def by(auto)
        from vpeq_ns_nt no_gateway_comm
          and IH[where t="Some (step (next_state t' execs2) (next_action t' execs2))" and ?execs2.0="(next_execs t' execs2)" and u=u]
          and current_s_nt purged_a_na2 
          have eq_ns_nt: "iequivalent_states (run n (Some s) execs)
                                             (run n (Some (step (next_state t' execs2) (next_action t' execs2))) (next_execs t' execs2)) u" by auto
        from prec_t  eq_ns_nt not_interrupt False thread_empty_s 
          show ?thesis using t rs rt by(auto)
      qed      
    }
    thus ?case by(simp add:option.splits,cases t,simp+)
  next
  case (5 n execs s t u execs2)
    assume not_interrupt: "\<not>interrupt (Suc n)"
    assume thread_not_empty_s: "\<not>thread_empty(execs (current s))"
    assume not_prec_s: "\<not> precondition (next_state s execs) (next_action s execs)"
    hence "run (Suc n) (Some s) execs = None" using not_interrupt thread_not_empty_s by simp
    thus ?case by(simp add:option.splits)
  next
  case (6 n execs s t u execs2)
    assume not_interrupt: "\<not>interrupt (Suc n)"
    assume thread_not_empty_s: "\<not>thread_empty(execs (current s))"
    assume prec_s: "precondition (next_state s execs) (next_action s execs)"
    assume IH: "(\<And>t u execs2. does_not_communicate_with_gateway u (next_execs s execs) \<and>
           iequivalent_states (Some (step (next_state s execs) (next_action s execs))) t u \<and>
           ipurged_relation1 u (next_execs s execs) execs2 \<longrightarrow>
           iequivalent_states
            (run n (Some (step (next_state s execs) (next_action s execs))) (next_execs s execs))
            (run n t execs2) u)"
    {
      fix t'
      assume t: "t = Some t'"
      fix rs
      assume rs: "run (Suc n) (Some s) execs = Some rs"
      fix rt
      assume rt: "run (Suc n) (Some t') execs2 = Some rt"
      
      assume no_gateway_comm: "does_not_communicate_with_gateway u execs"
      assume vpeq_s_t: "\<forall> v . ifp v u \<and> \<not>intermediary v u \<longrightarrow> vpeq v s t'"
      assume current_s_t: "current s = current t'"
      assume purged_a_a2: "ipurged_relation1 u execs execs2"
      
      from ifp_reflexive vpeq_s_t have vpeq_u_s_t: "vpeq u s t'" unfolding intermediary_def by auto
      from step_atomicity and current_s_t current_next_state
        have current_ns_nt: "current (step (next_state s execs) (next_action s execs)) = current (step (next_state t' execs2) (next_action t' execs2))"
        unfolding step_def
        by (cases "next_action s execs",cases "next_action t' execs2",simp,simp,cases "next_action t' execs2",simp,simp)        
      from step_atomicity current_next_state current_s_t have current_ns_t: "current (step (next_state s execs) (next_action s execs)) = current t'"
        unfolding step_def
        by (cases "next_action s execs",auto)      
      from vpeq_s_t have vpeq_curr_s_t: "ifp (current s) u \<and> \<not>intermediary (current s) u \<longrightarrow> vpeq (current s) s t'" unfolding intermediary_def by auto        
      from current_s_t purged_a_a2
        have eq_execs: "ifp (current s) u \<and> \<not>intermediary (current s) u \<longrightarrow> execs (current s) = execs2 (current s)"
        by(auto simp add: ipurged_relation1_def)
      from vpeq_involved_domains no_gateway_comm vpeq_s_t vpeq_involved_domains prec_s
        have vpeq_involved: "ifp (current s) u \<and> \<not>intermediary (current s) u \<longrightarrow> (\<forall> d \<in> involved (next_action s execs) . vpeq d s t')"
        by blast
      from current_s_t next_execs_consistent[THEN spec,THEN spec,THEN spec,where x2=s and x1=t' and x=execs] vpeq_curr_s_t vpeq_involved
        have next_execs_t: "ifp (current s) u \<and> \<not>intermediary (current s) u \<longrightarrow> next_execs t' execs = next_execs s execs"
        by(auto simp add: next_execs_def)
      from current_s_t and purged_a_a2 and thread_not_empty_s next_action_consistent[THEN spec,THEN spec,where x1=s and x=t'] vpeq_curr_s_t vpeq_involved
        have next_action_s_t: "ifp (current s) u \<and> \<not>intermediary (current s) u \<longrightarrow> next_action t' execs2 = next_action s execs"
        by(unfold next_action_def,unfold ipurged_relation1_def,auto)
      from purged_a_a2 and thread_not_empty_s and current_s_t
        have thread_not_empty_t: "ifp (current s) u \<and> \<not>intermediary (current s) u \<longrightarrow> \<not>thread_empty(execs2 (current t'))"
        unfolding ipurged_relation1_def by auto
      have vpeq_ns_nt_1: "\<And> a . precondition (next_state s execs) a \<and> precondition (next_state t' execs) a \<Longrightarrow> ifp (current s) u \<and> \<not>intermediary (current s) u \<Longrightarrow>  (\<forall> v . ifp v u \<and> \<not>intermediary v u \<longrightarrow> vpeq v (step (next_state s execs) a) (step (next_state t' execs) a))"
      proof-
        fix a
        assume precs: "precondition (next_state s execs) a \<and> precondition (next_state t' execs) a"
        assume ifp_curr: "ifp (current s) u \<and> \<not>intermediary (current s) u"
        from ifp_curr precs
          next_state_consistent[THEN spec,THEN spec,where x1=s and x=t'] vpeq_curr_s_t vpeq_s_t
          current_next_state current_s_t weakly_step_consistent[THEN spec,THEN spec,THEN spec,THEN spec,where x3="next_state s execs" and x2="next_state t' execs" and x="the a"]
        show "\<forall> v . ifp v u \<and> \<not>intermediary v u \<longrightarrow> vpeq v (step (next_state s execs) a) (step (next_state t' execs) a)"
          unfolding step_def precondition_def B_def
          by (cases a,auto)
      qed
      have no_gateway_comm_na: "does_not_communicate_with_gateway u (next_execs s execs)"
        proof-
        {
          fix a
          assume "a \<in> actions_in_execution (next_execs s execs u)"
          from this no_gateway_comm[unfolded does_not_communicate_with_gateway_def,THEN spec,where x=a]
               next_execs_subset[THEN spec,THEN spec,THEN spec,where x2=s and x1=execs and x0=u]
            have "\<forall>v. intermediary v u \<longrightarrow> v \<notin> involved (Some a)"
            unfolding  actions_in_execution_def
            by(auto)
        }
        thus ?thesis unfolding does_not_communicate_with_gateway_def by auto
        qed
      have "iequivalent_states (run (Suc n) (Some s) execs) (run (Suc n) (Some t') execs2) u"      
      proof (cases "ifp (current s) u \<and> \<not>intermediary (current s) u" rule :case_split[case_names T F])
      case T
        show ?thesis
        proof (cases "thread_empty(execs2 (current t'))" rule :case_split[case_names T2 F2])
        case F2
          show ?thesis
          proof (cases "precondition (next_state t' execs2) (next_action t' execs2)" rule :case_split[case_names T3 F3])        
          case T3
            from T purged_a_a2 current_s_t
              next_execs_consistent[THEN spec,THEN spec,where x1=s and x=t'] vpeq_curr_s_t vpeq_involved
              have purged_na_na2: "ipurged_relation1 u (next_execs s execs) (next_execs t' execs2)"
              unfolding ipurged_relation1_def next_execs_def
              by auto     
            from IH[where t="Some (step (next_state t' execs2) (next_action t' execs2))" and ?execs2.0="next_execs t' execs2" and u=u]
              purged_na_na2 current_ns_nt vpeq_ns_nt_1[where a="(next_action s execs)"] T T3 prec_s
              next_action_s_t  eq_execs current_s_t no_gateway_comm_na
              have eq_ns_nt: "iequivalent_states (run n (Some (step (next_state s execs) (next_action s execs))) (next_execs s execs))
                                                 (run n (Some (step (next_state t' execs2) (next_action t' execs2))) (next_execs t' execs2)) u"
              unfolding next_state_def                                                 
              by (auto,metis)
            from this not_interrupt thread_not_empty_s prec_s F2 T3
              have current_rs_rt: "current rs = current rt" using rs rt by auto
            {
              fix v
              assume ia: "ifp v u \<and> \<not>intermediary v u"
              from this eq_ns_nt not_interrupt thread_not_empty_s prec_s F2 T3
                have "vpeq v rs rt" using rs rt by auto
            }
            from this and current_rs_rt show ?thesis using rs rt by auto
          next
          case F3
            from F3 F2 not_interrupt show ?thesis using rt by simp
          qed
        next        
        case T2
          from T2 T purged_a_a2 thread_not_empty_s current_s_t prec_s next_action_s_t vpeq_u_s_t 
            have ind_source: "False" unfolding  ipurged_relation1_def by auto
          thus ?thesis by auto        
        qed
      next
      case F
        hence 1: "ind_source (current s) u \<or> unrelated (current s) u \<or> intermediary (current s) u"
          unfolding intermediary_def
          by auto
        from purged_a_a2 and thread_not_empty_s
          have 2: "\<not>intermediary (current s) u" unfolding ipurged_relation1_def by auto
         
        let ?nt = "if thread_empty(execs2 (current t'))  then t' else step (next_state t' execs2) (next_action t' execs2)"
        let ?na2 = "if thread_empty(execs2 (current t')) then execs2 else next_execs t' execs2"

        have prec_t: "\<not>thread_empty(execs2 (current t')) \<Longrightarrow> precondition (next_state t' execs2) (next_action t' execs2)"
        proof-
          assume thread_not_empty_t: "\<not>thread_empty(execs2 (current t'))"
          {
            assume not_prec_t: "\<not>precondition (next_state t' execs2) (next_action t' execs2)"
            hence "run (Suc n) (Some t') execs2 = None" using not_interrupt thread_not_empty_t not_prec_t by (simp)
            from this  have "False" using rt by(simp add:option.splits)
          }
          thus ?thesis by auto
        qed
        
        show ?thesis
        proof-
          {
          fix v
          assume ifp_v: "ifp v u"
          assume v_not_intermediary: "\<not>intermediary v u"                    
          
          have not_ifp_curr_v: "\<not>ifp (current s) v"
          proof
            assume ifp_curr_v: "ifp (current s) v"
            thus False
            proof-
              {
                assume "ind_source (current s) u"
                from this ifp_curr_v ifp_v have "intermediary v u" unfolding intermediary_def by auto
                from this v_not_intermediary have False unfolding intermediary_def by auto
              }
              moreover
              {
                assume unrelated: "unrelated (current s) u"
                from this ifp_v ifp_curr_v have "False" using rtranclp_trans r_into_rtranclp by metis
              }
              ultimately show ?thesis using 1 2 by auto
            qed
          qed
          from this current_next_state[THEN spec,THEN spec,where x1=s and x=execs] prec_s
             locally_respects[THEN spec,THEN spec,where x="next_state s execs"] vpeq_reflexive
             have "vpeq v (next_state s execs) (step (next_state s execs) (next_action s execs))"
             unfolding step_def precondition_def B_def
             by (cases "next_action s execs",auto)
          from not_ifp_curr_v this locally_respects_next_state vpeq_transitive
            have vpeq_s_ns: "vpeq v s (step (next_state s execs) (next_action s execs))"
            by blast
          from not_ifp_curr_v current_s_t current_next_state[THEN spec,THEN spec,where x1=t' and x=execs2] prec_t
             locally_respects[THEN spec,THEN spec,where x="next_state t' execs2"]
             F vpeq_reflexive
             have 0: "\<not> thread_empty (execs2 (current t')) \<longrightarrow> vpeq v (next_state t' execs2) (step (next_state t' execs2) (next_action t' execs2))"              
             unfolding step_def precondition_def B_def
             by (cases "next_action t' execs2",auto)
           from 0 not_ifp_curr_v current_s_t locally_respects_next_state[THEN spec,THEN spec,THEN spec,where x2="t'" and x1=v and x="execs2"]
             vpeq_transitive 
             have vpeq_t_nt: "\<not> thread_empty (execs2 (current t')) \<longrightarrow> vpeq v t' (step (next_state t' execs2) (next_action t' execs2))" by metis
          from this vpeq_reflexive
            have vpeq_t_nt: "vpeq v t' ?nt"
            by auto
          from vpeq_s_t ifp_v v_not_intermediary
            have "vpeq v s t'" by auto 
          from this vpeq_s_ns vpeq_t_nt vpeq_transitive vpeq_symmetric vpeq_reflexive
            have "vpeq v (step (next_state s execs) (next_action s execs)) ?nt"
            by (metis (hide_lams, no_types))
          }
          hence vpeq_ns_nt: "\<forall> v . ifp v u \<and> \<not>intermediary v u \<longrightarrow> vpeq v (step (next_state s execs) (next_action s execs)) ?nt" by auto
          from vpeq_s_t 2 F purged_a_a2 current_s_t thread_not_empty_s have purged_na_na2: "ipurged_relation1 u (next_execs s execs) ?na2"
            unfolding ipurged_relation1_def next_execs_def intermediary_def by(auto)
          from current_ns_nt current_ns_t current_next_state have current_ns_nt:
            "current (step (next_state s execs) (next_action s execs)) = current ?nt"
             by auto
          from prec_s vpeq_ns_nt no_gateway_comm_na
            and IH[where t="Some ?nt" and ?execs2.0="?na2" and u=u]
            and current_ns_nt purged_na_na2
            have eq_ns_nt: "iequivalent_states (run n (Some (step (next_state s execs) (next_action s execs))) (next_execs s execs))
                                               (run n (Some ?nt) ?na2) u" by auto
                                             
          from this not_interrupt thread_not_empty_s prec_t prec_s
            have current_rs_rt: "current rs = current rt" using rs rt by (cases "thread_empty (execs2 (current t'))",simp,simp) 
          {
            fix v
            assume ia: "ifp v u \<and> \<not>intermediary v u"
            from this eq_ns_nt not_interrupt thread_not_empty_s prec_s prec_t
              have "vpeq v rs rt"
              using rs rt by (cases "thread_empty(execs2 (current t'))",simp,simp) 
          }
          from current_rs_rt and this show ?thesis using rs rt by auto
        qed
      qed
    }
    thus ?case by(simp add:option.splits,cases t,simp+)    
  qed
}
hence iview_partitioned_inductive: "\<forall> u s t execs execs2 n. does_not_communicate_with_gateway u execs \<and> iequivalent_states s t u \<and> ipurged_relation1 u execs execs2 \<longrightarrow> iequivalent_states (run n s execs) (run n t execs2) u"
  by blast
have ipurged_relation: "\<forall> u execs . ipurged_relation1 u (ipurge_l execs u) (ipurge_r execs u)"
  by(unfold ipurged_relation1_def,unfold ipurge_l_def,unfold ipurge_r_def,auto)
{
  fix execs s t n u
  assume 1: "iequivalent_states s t u"
  from ifp_reflexive 
    have dir_source: "\<forall> u . ifp u u \<and> \<not>intermediary u u" unfolding intermediary_def by auto  
  from ipurge_l_removes_gateway_communications
    have "does_not_communicate_with_gateway u (ipurge_l execs u)"
    by auto
  from 1 this iview_partitioned_inductive ipurged_relation
    have "iequivalent_states (run n s (ipurge_l execs u)) (run n t (ipurge_r execs u)) u" by auto
  from this dir_source
    have "run n s (ipurge_l execs u) \<parallel> run n t (ipurge_r execs u) \<rightharpoonup> (\<lambda>rs rt. vpeq u rs rt \<and> current rs = current rt)"
    using r_into_rtranclp unfolding B_def
    by(cases "run n s (ipurge_l execs u)",simp,cases "run n t (ipurge_r execs u)",simp,auto)
}
thus ?thesis unfolding iview_partitioned_def Let_def by auto
qed


text \<open>
  Returns True iff and only if the two states have the same active domain, \emph{or} if one of the states is None.
\<close>
definition mcurrents :: "'state_t option \<Rightarrow> 'state_t option \<Rightarrow> bool"
  where "mcurrents m1 m2 \<equiv> m1 \<parallel> m2 \<rightharpoonup> (\<lambda> s t . current s = current t)"
  
text \<open>
  Proof that switching/interrupts are purely time-based and happen independent of the actions done by the domains.
  As all theorems in this locale, it holds vacuously whenever one of the states is None, i.e., whenver at some point a precondition does not hold.
\<close>
lemma current_independent_of_domain_actions:
assumes current_s_t: "mcurrents s t"
  shows "mcurrents (run n s execs) (run n t execs2)"
proof-
{
  fix n s execs t execs2
  have "mcurrents s t \<longrightarrow> mcurrents (run n s execs) (run n t execs2)"
  proof (induct n s execs arbitrary: t execs2 rule: run.induct)
  case (1 s execs t execs2)
    from this show ?case using current_s_t unfolding B_def by auto
  next
  case (2 n execs t execs2)
    show ?case unfolding mcurrents_def by(auto)
  next
  case (3 n s execs t execs2)
    assume interrupt: "interrupt (Suc n)"
    assume IH: "(\<And>t execs2. mcurrents (Some (cswitch (Suc n) s)) t \<longrightarrow> mcurrents (run n (Some (cswitch (Suc n) s)) execs) (run n t execs2))"
    {
      fix t'
      assume t: "t = (Some t')"
      assume curr: "mcurrents (Some s) t"
      from t curr cswitch_independent_of_state[THEN spec,THEN spec,THEN spec,where x1=s]  have current_ns_nt: "current (cswitch (Suc n) s) = current (cswitch (Suc n) t')"
         unfolding mcurrents_def by simp      
      from current_ns_nt IH[where t="Some (cswitch (Suc n) t')" and ?execs2.0=execs2]
        have mcurrents_ns_nt: "mcurrents (run n (Some (cswitch (Suc n) s)) execs) (run n (Some (cswitch (Suc n) t')) execs2)"
        unfolding mcurrents_def by(auto)
      from mcurrents_ns_nt interrupt t
        have "mcurrents (run (Suc n) (Some s) execs) (run (Suc n) t execs2)"
        unfolding mcurrents_def B2_def B_def by(cases "run n (Some (cswitch (Suc n) s)) execs", cases "run (Suc n) t execs2",auto)
    }
    thus ?case unfolding mcurrents_def B2_def by(cases t,auto)    
  next
  case (4 n execs s t execs2)
    assume not_interrupt: "\<not>interrupt (Suc n)"
    assume thread_empty_s: "thread_empty(execs (current s))"
    assume IH: "(\<And>t execs2. mcurrents (Some s) t \<longrightarrow> mcurrents (run n (Some s) execs) (run n t execs2))"
    {
      fix t'
      assume t: "t = (Some t')"
      assume curr: "mcurrents (Some s) t"
      {
        assume thread_empty_t: "thread_empty(execs2 (current t'))"
        from t curr not_interrupt thread_empty_s this IH[where ?execs2.0=execs2 and t="Some t'"]
          have "mcurrents (run (Suc n) (Some s) execs) (run (Suc n) t execs2)"
          by auto
      }
      moreover
      {
        assume not_prec_t: "\<not>thread_empty(execs2 (current t')) \<and> \<not>precondition (next_state t' execs2) (next_action t' execs2)"
        from t this not_interrupt
          have "mcurrents (run (Suc n) (Some s) execs) (run (Suc n) t execs2)"
          unfolding mcurrents_def by (simp add: rewrite_B2_cases)
      }
      moreover
      {
        assume step_t: "\<not>thread_empty(execs2 (current t')) \<and> precondition (next_state t' execs2) (next_action t' execs2)"
        have "mcurrents (Some s) (Some (step (next_state t' execs2) (next_action t' execs2)))"
          using step_atomicity curr t current_next_state unfolding mcurrents_def
          unfolding step_def
          by (cases "next_action t' execs2",auto)
        from t step_t curr not_interrupt thread_empty_s this IH[where ?execs2.0="next_execs t' execs2" and t="Some (step (next_state t' execs2) (next_action t' execs2))"]
          have "mcurrents (run (Suc n) (Some s) execs) (run (Suc n) t execs2)"
          by auto
      }
      ultimately have "mcurrents (run (Suc n) (Some s) execs) (run (Suc n) t execs2)" by blast
    }
    thus ?case unfolding mcurrents_def B2_def by(cases t,auto)
  next
  case (5 n execs s t execs2)
    assume not_interrupt_s: "\<not>interrupt (Suc n)"
    assume thread_not_empty_s: "\<not>thread_empty(execs (current s))"
    assume not_prec_s: "\<not> precondition (next_state s execs) (next_action s execs)"
    hence "run (Suc n) (Some s) execs = None" using not_interrupt_s thread_not_empty_s by simp
    thus ?case unfolding mcurrents_def by(simp add:option.splits)
  next
  case (6 n execs s t execs2)
    assume not_interrupt: "\<not>interrupt (Suc n)"
    assume thread_not_empty_s: "\<not>thread_empty(execs (current s))"
    assume prec_s: "precondition (next_state s execs) (next_action s execs)"
    assume IH: "(\<And>t execs2.
           mcurrents (Some (step (next_state s execs) (next_action s execs))) t \<longrightarrow>
           mcurrents (run n (Some (step (next_state s execs) (next_action s execs))) (next_execs s execs)) (run n t execs2))"
    {
      fix t'
      assume t: "t = (Some t')"
      assume curr: "mcurrents (Some s) t"
      {
        assume thread_empty_t: "thread_empty(execs2 (current t'))"
        have "mcurrents (Some (step (next_state s execs) (next_action s execs))) (Some t')"
          using step_atomicity curr t current_next_state unfolding mcurrents_def
          unfolding step_def
          by (cases "next_action s execs",auto)
        from t curr not_interrupt thread_not_empty_s prec_s thread_empty_t this IH[where ?execs2.0=execs2 and t="Some t'"]
          have "mcurrents (run (Suc n) (Some s) execs) (run (Suc n) t execs2)"
          by auto
      }
      moreover
      {
        assume not_prec_t: "\<not>thread_empty(execs2 (current t')) \<and> \<not>precondition (next_state t' execs2) (next_action t' execs2)"
        from t this not_interrupt
          have "mcurrents (run (Suc n) (Some s) execs) (run (Suc n) t execs2)"
          unfolding mcurrents_def B2_def by (auto)
      }
      moreover
      {
        assume step_t: "\<not>thread_empty(execs2 (current t')) \<and> precondition (next_state t' execs2) (next_action t' execs2)"
        have "mcurrents (Some (step (next_state s execs) (next_action s execs))) (Some (step (next_state t' execs2) (next_action t' execs2)))"
          using step_atomicity curr t current_next_state unfolding mcurrents_def
          unfolding step_def
          by (cases "next_action s execs",simp,cases "next_action t' execs2",simp,simp,cases "next_action t' execs2",simp,simp)
        from current_next_state t step_t curr not_interrupt thread_not_empty_s prec_s this IH[where ?execs2.0="next_execs t' execs2" and t="Some (step (next_state t' execs2) (next_action t' execs2))"]
          have "mcurrents (run (Suc n) (Some s) execs) (run (Suc n) t execs2)"
          by auto
      }
      ultimately have "mcurrents (run (Suc n) (Some s) execs) (run (Suc n) t execs2)" by blast
    }
    thus ?case unfolding mcurrents_def B2_def by(cases t,auto)
  qed
}
thus ?thesis using current_s_t by auto
qed

theorem unwinding_implies_NI_indirect_sources: 
shows NI_indirect_sources 
proof-
  {
    fix execs a n
    from iunwinding_implies_view_partitioned1
      have vp: iview_partitioned by blast
    from vp and vpeq_reflexive
      have 1: "\<forall> u . run n (Some s0) (ipurge_l execs u) \<parallel> run n (Some s0) (ipurge_r execs u)  \<rightharpoonup> (\<lambda>rs rt. vpeq u rs rt \<and> current rs = current rt)"
      unfolding iview_partitioned_def by auto
      
    have "run n (Some s0) execs \<rightharpoonup> (\<lambda>s_f. run n (Some s0) (ipurge_l execs (current s_f))  \<parallel>
                                           run n (Some s0) (ipurge_r execs (current s_f)) \<rightharpoonup>
                                           (\<lambda>s_l s_r. output_f s_l a = output_f s_r a))"
    proof(cases "run n (Some s0) execs")
    case None
      thus ?thesis unfolding B_def by simp
    next
    case (Some s_f)
      thus ?thesis
      proof(cases "run n (Some s0) (ipurge_l execs (current s_f))")
      case None
        from Some this show ?thesis unfolding B_def by simp
      next
      case (Some s_ipurge_l)
        show ?thesis
        proof(cases "run n (Some s0) (ipurge_r execs (current s_f))")
        case None
          from \<open>run n (Some s0) execs = Some s_f\<close> Some this show ?thesis unfolding B_def by simp
        next
        case (Some s_ipurge_r)
           from cswitch_independent_of_state
                \<open>run n (Some s0) execs = Some s_f\<close> \<open>run n (Some s0) (ipurge_l execs (current s_f)) = Some s_ipurge_l\<close>
                current_independent_of_domain_actions[where n=n and s="Some s0" and t="Some s0" and execs=execs and ?execs2.0="(ipurge_l execs (current s_f))"]
             have 2: "current s_ipurge_l = current s_f" 
             unfolding mcurrents_def B_def by auto
           from \<open>run n (Some s0) execs = Some s_f\<close>  \<open>run n (Some s0) (ipurge_l execs (current s_f)) = Some s_ipurge_l\<close>
                Some 1[THEN spec,where x="current s_f"]
             have "vpeq (current s_f) s_ipurge_l s_ipurge_r \<and> current s_ipurge_l = current s_ipurge_r"
             unfolding B_def by auto
           from this 2 have "output_f s_ipurge_l a = output_f s_ipurge_r a"
             using output_consistent by auto
           from \<open>run n (Some s0) execs = Some s_f\<close>  \<open>run n (Some s0) (ipurge_l execs (current s_f)) = Some s_ipurge_l\<close>
                this Some
             show ?thesis unfolding B_def by auto
        qed
      qed
    qed
  }
  thus ?thesis unfolding NI_indirect_sources_def by auto
qed 


theorem unwinding_implies_isecure: 
shows isecure
using unwinding_implies_NI_indirect_sources  unwinding_implies_NI_unrelated unfolding isecure_def by(auto)

end
end

