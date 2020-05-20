subsection \<open>CISK (Controlled Interruptible Separation Kernel)\<close>

theory CISK
  imports ISK
begin

text \<open>
  This section presents a generic model of a Controlled Interruptible Separation Kernel (CISK).
  It formulates security, i.e., intransitive noninterference.
  For a presentation of this model, see Section 2 of~\cite{Verbeek2013}.
\<close>

text \<open>
  First, a locale is defined that defines all generic functions and all proof obligations (see Section 2.3 of ~\cite{Verbeek2013}).
\<close>
locale Controllable_Interruptible_Separation_Kernel = \<comment> \<open>CISK\<close>
fixes kstep :: "'state_t \<Rightarrow> 'action_t \<Rightarrow> 'state_t" \<comment> \<open>Executes one atomic kernel action\<close>
  and output_f :: "'state_t \<Rightarrow> 'action_t \<Rightarrow> 'output_t" \<comment> \<open>Returns the observable behavior\<close>
  and s0 :: "'state_t" \<comment> \<open>The initial state\<close>
  and current :: "'state_t => 'dom_t" \<comment> \<open>Returns the currently active domain\<close>
  and cswitch :: "time_t \<Rightarrow> 'state_t \<Rightarrow> 'state_t" \<comment> \<open>Performs a context switch\<close>
  and interrupt :: "time_t \<Rightarrow> bool" \<comment> \<open>Returns t iff an interrupt occurs in the given state at the given time\<close>
  and kinvolved :: "'action_t \<Rightarrow> 'dom_t set" \<comment> \<open>Returns the set of domains that are involved in the given action\<close>
  and ifp :: "'dom_t \<Rightarrow> 'dom_t \<Rightarrow> bool" \<comment> \<open>The security policy.\<close>
  and vpeq :: "'dom_t \<Rightarrow> 'state_t \<Rightarrow> 'state_t \<Rightarrow> bool" \<comment> \<open>View partitioning equivalence\<close>
  and AS_set :: "('action_t list) set" \<comment> \<open>Returns a set of valid action sequences, i.e., the attack surface\<close>
  and invariant :: "'state_t \<Rightarrow> bool" \<comment> \<open>Returns an inductive state-invariant\<close>
  and AS_precondition :: "'state_t \<Rightarrow> 'dom_t \<Rightarrow> 'action_t \<Rightarrow> bool" \<comment> \<open>Returns the preconditions under which the given action can be executed.\<close>  
  and aborting :: "'state_t \<Rightarrow> 'dom_t \<Rightarrow> 'action_t \<Rightarrow> bool" \<comment> \<open>Returns true iff the action is aborted.\<close>
  and waiting :: "'state_t \<Rightarrow> 'dom_t \<Rightarrow> 'action_t \<Rightarrow> bool" \<comment> \<open>Returns true iff execution of the given action is delayed.\<close>
  and set_error_code :: "'state_t \<Rightarrow> 'action_t \<Rightarrow> 'state_t" \<comment> \<open>Sets an error code when actions are aborted.\<close>
assumes vpeq_transitive: " \<forall> a b c u. (vpeq u a b \<and> vpeq u b c) \<longrightarrow> vpeq u a c"
    and vpeq_symmetric: "\<forall> a b u. vpeq u a b \<longrightarrow> vpeq u b a"
    and vpeq_reflexive: "\<forall> a u. vpeq u a a"
    and ifp_reflexive: "\<forall> u . ifp u u"     
    and weakly_step_consistent: "\<forall> s t u a. vpeq u s t \<and> vpeq (current s) s t \<and> invariant s \<and> AS_precondition s (current s) a \<and> invariant t \<and> AS_precondition t (current t) a \<and> current s = current t  \<longrightarrow> vpeq u (kstep s a) (kstep t a)"
    and locally_respects: "\<forall> a s u. \<not>ifp (current s) u  \<and> invariant s \<and> AS_precondition s (current s) a \<longrightarrow> vpeq u s (kstep s a)"
    and output_consistent: "\<forall> a s t. vpeq (current s) s t \<and> current s = current t \<longrightarrow> (output_f s a) = (output_f t a)"
    and step_atomicity: "\<forall> s a . current (kstep s a) = current s"
    and cswitch_independent_of_state: "\<forall> n s t . current s = current t \<longrightarrow> current (cswitch n s) = current (cswitch n t)"
    and cswitch_consistency: "\<forall> u s t n . vpeq u s t \<longrightarrow> vpeq u (cswitch n s) (cswitch n t)"
    and empty_in_AS_set: "[] \<in> AS_set"
    and invariant_s0: "invariant s0"
    and invariant_after_cswitch: "\<forall> s n . invariant s \<longrightarrow> invariant (cswitch n s)"
    and precondition_after_cswitch: "\<forall> s d n a. AS_precondition s d a \<longrightarrow> AS_precondition (cswitch n s) d a"
    and AS_prec_first_action: "\<forall> s d aseq . invariant s \<and> aseq \<in> AS_set \<and> aseq \<noteq> [] \<longrightarrow> AS_precondition s d (hd aseq)"
    and AS_prec_after_step: "\<forall> s a a' . (\<exists> aseq \<in> AS_set . is_sub_seq a a' aseq) \<and> invariant s \<and> AS_precondition s (current s) a \<and> \<not>aborting s (current s) a \<and> \<not> waiting s (current s) a\<longrightarrow> AS_precondition (kstep s a) (current s) a'"
    and AS_prec_dom_independent: "\<forall> s d a a' . current s \<noteq> d \<and> AS_precondition s d a \<longrightarrow> AS_precondition (kstep s a') d a"
    and spec_of_invariant: "\<forall> s a . invariant s \<longrightarrow> invariant (kstep s a)"
    and aborting_switch_independent: "\<forall> n s . aborting (cswitch n s) = aborting s"
    and aborting_error_update: "\<forall> s d a' a . current s \<noteq> d \<and> aborting s d a \<longrightarrow> aborting (set_error_code s a') d a"
    and aborting_after_step: "\<forall> s a d . current s \<noteq> d \<longrightarrow> aborting (kstep s a) d = aborting s d" (* TODO: I think this PO can be removed *)
    and aborting_consistent: "\<forall> s t u . vpeq u s t \<longrightarrow> aborting s u = aborting t u"
    and waiting_switch_independent: "\<forall> n s . waiting (cswitch n s) = waiting s"
    and waiting_error_update: "\<forall> s d a' a . current s \<noteq> d \<and> waiting s d a \<longrightarrow> waiting (set_error_code s a') d a"
    and waiting_consistent: "\<forall>s t u a . vpeq (current s) s t \<and> (\<forall> d \<in> kinvolved a . vpeq d s t) \<and> vpeq u s t \<longrightarrow> waiting s u a = waiting t u a"
    and spec_of_waiting: "\<forall> s a . waiting s (current s) a \<longrightarrow> kstep s a = s"
    and set_error_consistent: "\<forall> s t u a . vpeq u s t \<longrightarrow> vpeq u (set_error_code s a) (set_error_code t a)"
    and set_error_locally_respects: "\<forall> s u a . \<not>ifp (current s) u \<longrightarrow> vpeq u s (set_error_code s a)"
    and current_set_error_code: "\<forall> s a . current (set_error_code s a) = current s"
    and precondition_after_set_error_code: "\<forall> s d a a'. AS_precondition s d a \<and> aborting s (current s) a' \<longrightarrow> AS_precondition (set_error_code s a') d a"
    and invariant_after_set_error_code: "\<forall> s a . invariant s \<longrightarrow> invariant (set_error_code s a)"
    and involved_ifp: "\<forall> s a . \<forall> d \<in> (kinvolved a) . AS_precondition s (current s) a \<longrightarrow> ifp d (current s)"  
begin  

subsubsection\<open>Execution semantics\<close>

text\<open>
  Control is based on generic functions \emph{aborting}, \emph{waiting} and \emph{set\_error\_code}.
  Function \emph{aborting} decides whether a certain action is aborting, given its domain and the state.
  If so, then function set\_error\_code will be used to update the state, possibly communicating to other domains that an action has been aborted.
  Function \emph{waiting} can delay the execution of an action.
  This behavior is implemented in function CISK\_control.
\<close>
function CISK_control :: "'state_t \<Rightarrow> 'dom_t \<Rightarrow> 'action_t execution \<Rightarrow> ('action_t option \<times> 'action_t execution \<times> 'state_t)"
where "CISK_control s d []                = (None,[],s)" \<comment> \<open>The thread is empty\<close>
    | "CISK_control s d ([]#[])           = (None,[],s)" \<comment> \<open>The current action sequence has been finished and the thread has no next action sequences to execute\<close>
    | "CISK_control s d ([]#(as'#execs')) = (None,as'#execs',s)" \<comment> \<open>The current action sequence has been finished. Skip to the next sequence\<close>
    | "CISK_control s d ((a#as)#execs')   = (if aborting s d a then 
                                                  (None, execs',set_error_code s a)
                                               else if waiting s d a then
                                                  (Some a, (a#as)#execs',s)
                                               else
                                                  (Some a, as#execs',s))" \<comment> \<open>Executing an action sequence\<close>
by pat_completeness auto
termination by lexicographic_order

text\<open>
  Function \emph{run} defines the execution semantics.
  This function is presented in ~\cite{Verbeek2013} by pseudo code (see Algorithm 1).
  Before defining the run function, we define accessor functions for the control mechanism.
  Functions next\_action, next\_execs and next\_state correspond to ``control.a'', ``control.x'' and ``control.s'' in ~\cite{Verbeek2013}.
\<close>
abbreviation next_action::"'state_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> 'action_t option"
where "next_action \<equiv> Kernel.next_action current CISK_control"
abbreviation next_execs::"'state_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution)"
where "next_execs  \<equiv> Kernel.next_execs current CISK_control"
abbreviation next_state::"'state_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> 'state_t"
where "next_state  \<equiv> Kernel.next_state current CISK_control"
text \<open>
\<close>
text \<open>
  A thread is empty iff either it has no further action sequences to execute, or when the current action sequence is finished and there are no further action sequences to execute.
\<close>
abbreviation thread_empty::"'action_t execution \<Rightarrow> bool"
where "thread_empty exec \<equiv> exec = [] \<or> exec = [[]]"

text\<open>
  The following function defines the execution semantics of CISK, using function CISK\_control.
\<close>
function run :: "time_t \<Rightarrow> 'state_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> 'state_t"
where "run 0 s execs = s"
| "interrupt (Suc n) \<Longrightarrow> run (Suc n) s execs = run n (cswitch (Suc n) s) execs"
| "\<not>interrupt (Suc n) \<Longrightarrow> thread_empty(execs (current s)) \<Longrightarrow> run (Suc n) s execs = run n s execs"
| "\<not>interrupt (Suc n) \<Longrightarrow> \<not>thread_empty(execs (current s)) \<Longrightarrow>
      run (Suc n) s execs = (let control_a = next_action s execs;
                                 control_s = next_state s execs;
                                 control_x = next_execs s execs in
                             case control_a of None \<Rightarrow> run n control_s control_x
                                         | (Some a) \<Rightarrow> run n (kstep control_s a) control_x)"
using not0_implies_Suc by (metis prod_cases3,auto)
termination by lexicographic_order

subsubsection \<open>Formulations of security\<close>

text\<open>
  The definitions of security as presented in Section 2.2 of~\cite{Verbeek2013}.
\<close>

abbreviation kprecondition
  where "kprecondition s a \<equiv> invariant s \<and> AS_precondition s (current s) a"
definition realistic_execution
where "realistic_execution aseq \<equiv> set aseq \<subseteq> AS_set"
definition realistic_executions :: "('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> bool"
where "realistic_executions execs \<equiv> \<forall>d. realistic_execution (execs d)"
abbreviation involved where "involved \<equiv> Kernel.involved kinvolved"
abbreviation step where "step \<equiv> Kernel.step kstep"
abbreviation purge where "purge \<equiv> Separation_Kernel.purge realistic_execution ifp"
abbreviation ipurge_l where "ipurge_l \<equiv> Separation_Kernel.ipurge_l kinvolved ifp"
abbreviation ipurge_r where "ipurge_r \<equiv> Separation_Kernel.ipurge_r realistic_execution kinvolved ifp"

definition NI_unrelated::bool
where "NI_unrelated
  \<equiv> \<forall> execs a n . realistic_executions execs \<longrightarrow>
                      (let s_f = run n s0 execs in
                         output_f s_f a = output_f (run n s0 (purge execs (current s_f))) a)"
definition NI_indirect_sources::bool
where "NI_indirect_sources
  \<equiv> \<forall> execs a n. realistic_executions execs \<longrightarrow>
                    (let s_f = run n s0 execs in
                      output_f (run n s0 (ipurge_l execs (current s_f))) a =
                      output_f (run n s0 (ipurge_r execs (current s_f))) a)"
definition isecure::bool
where "isecure \<equiv> NI_unrelated \<and> NI_indirect_sources"


subsubsection \<open>Proofs\<close>
text\<open>
  The final theorem is unwinding\_implies\_isecure\_CISK.
  This theorem shows that any interpretation of locale CISK is secure.

  To prove this theorem, the refinement framework is used.
  CISK is a refinement of ISK, as the only idfference is the control function.
  In ISK, this function is a generic function called \emph{control}, in CISK it is interpreted in function \emph{CISK\_control}.
  It is proven that function \emph{CISK\_control} satisfies all the proof obligations concerning generic function \emph{control}.
  In other words, \emph{CISK\_control} is proven to be an interpretation of control.
  Therefore, all theorems on run\_total apply to the run function of CISK as well.
\<close>

lemma next_action_consistent: 
shows "\<forall> s t execs . vpeq (current s) s t \<and> (\<forall> d \<in>  involved (next_action s execs) . vpeq d s t) \<and> current s = current t  \<longrightarrow> next_action s execs = next_action t execs"
proof-
{
  fix s t execs
  assume vpeq: "vpeq (current s) s t"
  assume vpeq_involved: "\<forall> d \<in>  involved (next_action s execs) . vpeq d s t"
  assume current_s_t: "current s = current t"
  from aborting_consistent current_s_t vpeq
   have "aborting t (current s) = aborting s (current s)" by auto
  from current_s_t this waiting_consistent vpeq_involved
    have "next_action s execs = next_action t execs"
    unfolding Kernel.next_action_def 
    by(cases "(s,(current s),execs (current s))" rule: CISK_control.cases,auto)
}
thus ?thesis by auto
qed

lemma next_execs_consistent:
shows "\<forall> s t execs . vpeq (current s) s t \<and> (\<forall> d \<in> involved (next_action s execs) . vpeq d s t) \<and> current s = current t \<longrightarrow> fst (snd (CISK_control s (current s) (execs (current s)))) = fst (snd (CISK_control t (current s) (execs (current s))))"
proof-
{
  fix s t execs
  assume vpeq: "vpeq (current s) s t"
  assume vpeq_involved: "\<forall> d \<in> involved (next_action s execs) . vpeq d s t"
  assume current_s_t: "current s = current t"
  from aborting_consistent current_s_t vpeq
     have 1: "aborting t (current s) = aborting s (current s)" by auto
  from 1 vpeq current_s_t vpeq_involved waiting_consistent[THEN spec,THEN spec,THEN spec,THEN spec,where x3=s and x2=t and x1="current s" and x="the (next_action s execs)"]
    have "fst (snd (CISK_control s (current s) (execs (current s)))) = fst (snd (CISK_control t (current s) (execs (current s))))"
    unfolding Kernel.next_action_def Kernel.involved_def
    by(cases "(s,(current s),execs (current s))" rule: CISK_control.cases,auto split: if_split_asm)
}
thus ?thesis by auto
qed

lemma next_state_consistent:
shows "\<forall> s t u execs . vpeq (current s) s t \<and> vpeq u s t \<and> current s = current t \<longrightarrow> vpeq u (next_state s execs) (next_state t execs)"
proof-
{
  fix s t u execs
  assume vpeq_s_t: "vpeq (current s) s t \<and> vpeq u s t"
  assume current_s_t: "current s = current t"
  from vpeq_s_t current_s_t
    have "vpeq u (next_state s execs) (next_state t execs)"
    unfolding Kernel.next_state_def
    using aborting_consistent set_error_consistent
    by(cases "(s,(current s),execs (current s))" rule: CISK_control.cases,auto)
}
thus ?thesis by auto
qed

lemma current_next_state:
shows "\<forall> s execs . current (next_state s execs) = current s" 
proof-
{
  fix s execs
  have "current (next_state s execs) = current s"
    unfolding Kernel.next_state_def
    using current_set_error_code
    by(cases "(s,(current s),execs (current s))" rule: CISK_control.cases,auto)
}
thus ?thesis by auto
qed

lemma locally_respects_next_state:
shows "\<forall> s u execs. \<not>ifp (current s) u \<longrightarrow> vpeq u s (next_state s execs)"
proof-
{
  fix s u execs
  assume "\<not>ifp (current s) u"
  hence "vpeq u s (next_state s execs)"
    unfolding Kernel.next_state_def
    using vpeq_reflexive set_error_locally_respects
    by(cases "(s,(current s),execs (current s))" rule: CISK_control.cases,auto)
}
thus ?thesis by auto
qed

lemma CISK_control_spec:
shows "\<forall>s d aseqs.
       case CISK_control s d aseqs of
       (a, aseqs', s') \<Rightarrow>
         thread_empty aseqs \<and> (a, aseqs') = (None, []) \<or>
         aseqs \<noteq> [] \<and> hd aseqs \<noteq> [] \<and> \<not> aborting s' d (the a) \<and> \<not> waiting s' d (the a) \<and> (a, aseqs') = (Some (hd (hd aseqs)), tl (hd aseqs) # tl aseqs) \<or>
         aseqs \<noteq> [] \<and> hd aseqs \<noteq> [] \<and> waiting s' d (the a) \<and> (a, aseqs', s') = (Some (hd (hd aseqs)), aseqs, s) \<or> (a, aseqs') = (None, tl aseqs)"
proof-
{
  fix s d aseqs
  have "case CISK_control s d aseqs of
       (a, aseqs', s') \<Rightarrow>
         thread_empty aseqs \<and> (a, aseqs') = (None, []) \<or>
         aseqs \<noteq> [] \<and> hd aseqs \<noteq> [] \<and> \<not> aborting s' d (the a) \<and> \<not> waiting s' d (the a) \<and> (a, aseqs') = (Some (hd (hd aseqs)), tl (hd aseqs) # tl aseqs) \<or>
         aseqs \<noteq> [] \<and> hd aseqs \<noteq> [] \<and> waiting s' d (the a) \<and> (a, aseqs', s') = (Some (hd (hd aseqs)), aseqs, s) \<or> (a, aseqs') = (None, tl aseqs)"
  by(cases "(s,d,aseqs)" rule: CISK_control.cases,auto)
}
thus ?thesis by auto
qed

lemma next_action_after_cswitch:
shows "\<forall> s n d aseqs . fst (CISK_control (cswitch n s) d aseqs) = fst (CISK_control s d aseqs)"
proof-
{
  fix s n d aseqs
  have "fst (CISK_control (cswitch n s) d aseqs) = fst (CISK_control s d aseqs)"
  using aborting_switch_independent waiting_switch_independent
  by(cases "(s,d,aseqs)" rule: CISK_control.cases,auto)
}
thus ?thesis by auto
qed


lemma next_action_after_next_state:
shows "\<forall> s execs d . current s \<noteq> d \<longrightarrow> fst (CISK_control (next_state s execs) d (execs d)) = None \<or> fst (CISK_control (next_state s execs) d (execs d)) = fst (CISK_control s d (execs d))"
proof-
{
  fix s execs d aseqs
  assume 1: "current s \<noteq> d"
  have "fst (CISK_control (next_state s execs) d aseqs) = None \<or> fst (CISK_control (next_state s execs) d aseqs) = fst (CISK_control s d aseqs)"
    proof(cases "(s,d,aseqs)" rule: CISK_control.cases,simp,simp,simp)
    case (4 sa da a as execs')
      thus ?thesis
          unfolding Kernel.next_state_def
          using aborting_error_update waiting_error_update 1
          by(cases "(sa,current sa,execs (current sa))" rule: CISK_control.cases,auto split: if_split_asm)
    qed
}
thus ?thesis by auto
qed

lemma next_action_after_step:
shows "\<forall> s a d aseqs . current s \<noteq> d \<longrightarrow> fst (CISK_control (step s a) d aseqs) = fst (CISK_control s d aseqs)"
proof-
{
  fix s a d aseqs
  assume 1: "current s \<noteq> d"
  from this aborting_after_step 
    have  "fst (CISK_control (step s a) d aseqs) = fst (CISK_control s d aseqs)"
    unfolding Kernel.step_def 
    by(cases "(s,d,aseqs)" rule: CISK_control.cases,simp,simp,simp,cases a,auto)
}
thus ?thesis by auto
qed

lemma next_state_precondition:
shows "\<forall>s d a execs. AS_precondition s d a \<longrightarrow> AS_precondition (next_state s execs) d a"
proof-
{
  fix s a d execs
  assume "AS_precondition s d a"
  hence "AS_precondition (next_state s execs) d a"
    unfolding Kernel.next_state_def
    using precondition_after_set_error_code
    by(cases "(s,(current s),execs (current s))" rule: CISK_control.cases,auto)
}
thus ?thesis by auto
qed

lemma next_state_invariant:
shows "\<forall>s execs. invariant s \<longrightarrow> invariant (next_state s execs)"
proof-
{
  fix s execs
  assume "invariant s"
  hence "invariant (next_state s execs)"
    unfolding Kernel.next_state_def
    using invariant_after_set_error_code
    by(cases "(s,(current s),execs (current s))" rule: CISK_control.cases,auto)
}
thus ?thesis by auto
qed

lemma next_action_from_execs:
shows "\<forall> s execs . next_action s execs \<rightharpoonup> (\<lambda> a . a \<in> actions_in_execution (execs (current s)))"
proof-
{
  fix s execs
  {
    fix a
    assume 1: "next_action s execs = Some a"
    from 1 have "a \<in> actions_in_execution (execs (current s))"
      unfolding Kernel.next_action_def actions_in_execution_def
      by (cases "(s,(current s),execs (current s))" rule: CISK_control.cases,auto split: if_split_asm)
  }
  hence "next_action s execs \<rightharpoonup> (\<lambda> a . a \<in> actions_in_execution (execs (current s)))"
    unfolding B_def
    by (cases "next_action s execs",auto)
}
thus ?thesis unfolding B_def by (auto)
qed

lemma next_execs_subset:
shows "\<forall>s execs u . actions_in_execution (next_execs s execs u) \<subseteq> actions_in_execution (execs u)"
proof-
{
  fix s execs u
  have "actions_in_execution (next_execs s execs u) \<subseteq> actions_in_execution (execs u)"
    unfolding Kernel.next_execs_def actions_in_execution_def
    by (cases "(s,(current s),execs (current s))" rule: CISK_control.cases,auto split: if_split_asm)
}
thus ?thesis by auto
qed


theorem unwinding_implies_isecure_CISK:
shows isecure
proof-
  interpret int: Interruptible_Separation_Kernel kstep output_f s0 current cswitch interrupt kprecondition realistic_execution CISK_control kinvolved ifp vpeq AS_set invariant AS_precondition aborting waiting
    proof (unfold_locales)
      show "\<forall>a b c u. vpeq u a b \<and> vpeq u b c \<longrightarrow> vpeq u a c"
        using vpeq_transitive by blast
      show "\<forall>a b u. vpeq u a b \<longrightarrow> vpeq u b a"
        using vpeq_symmetric by blast
      show "\<forall>a u. vpeq u a a"
        using vpeq_reflexive by blast
      show "\<forall>u. ifp u u"
        using ifp_reflexive by blast
      show "\<forall> s t u a. vpeq u s t \<and> vpeq (current s) s t \<and> kprecondition s a \<and> kprecondition t a \<and> current s = current t  \<longrightarrow> vpeq u (kstep s a) (kstep t a)"
        using weakly_step_consistent by blast
      show "\<forall> a s u. \<not>ifp (current s) u  \<and> kprecondition s a \<longrightarrow> vpeq u s (kstep s a)"
        using locally_respects by blast
      show "\<forall> a s t. vpeq (current s) s t \<and> current s = current t \<longrightarrow> (output_f s a) = (output_f t a)"
        using output_consistent by blast        
      show "\<forall> s a . current (kstep s a) = current s"
        using step_atomicity by blast        
      show "\<forall> n s t . current s = current t \<longrightarrow> current (cswitch n s) = current (cswitch n t)"
        using cswitch_independent_of_state by blast                                                    
      show "\<forall> u s t n . vpeq u s t \<longrightarrow> vpeq u (cswitch n s) (cswitch n t)"
        using cswitch_consistency by blast
      show "\<forall>s t execs. vpeq (current s) s t \<and> (\<forall> d \<in> involved (next_action s execs) . vpeq d s t) \<and> current s = current t \<longrightarrow> next_action s execs = next_action t execs"
        using next_action_consistent by blast
      show "\<forall>s t execs.
        vpeq (current s) s t \<and> (\<forall> d \<in> involved (next_action s execs) . vpeq d s t) \<and> current s = current t \<longrightarrow>
        fst (snd (CISK_control s (current s) (execs (current s)))) = fst (snd (CISK_control t (current s) (execs (current s))))"
        using next_execs_consistent by blast
      show " \<forall>s t u execs. vpeq (current s) s t \<and> vpeq u s t \<and> current s = current t \<longrightarrow> vpeq u (next_state s execs) (next_state t execs)"
        using next_state_consistent by auto
      show " \<forall>s execs. current (next_state s execs) = current s"
        using current_next_state by auto
      show "\<forall>s u execs. \<not> ifp (current s) u \<longrightarrow> vpeq u s (next_state s execs)"
        using locally_respects_next_state by auto
      show "[] \<in> AS_set"
        using empty_in_AS_set by blast
      show "\<forall> s n . invariant s \<longrightarrow> invariant (cswitch n s)"
        using invariant_after_cswitch by blast
      show "\<forall> s d n a. AS_precondition s d a \<longrightarrow> AS_precondition (cswitch n s) d a"
        using precondition_after_cswitch by blast
      show "invariant s0"
        using invariant_s0 by blast
      show "\<forall> s d aseq . invariant s \<and> aseq \<in> AS_set \<and> aseq \<noteq> [] \<longrightarrow> AS_precondition s d (hd aseq)"
        using AS_prec_first_action by blast
      show "\<forall>s a a'. (\<exists>aseq\<in>AS_set. is_sub_seq a a' aseq) \<and> invariant s \<and> AS_precondition s (current s) a \<and> \<not> aborting s (current s) a \<and> \<not> waiting s (current s) a \<longrightarrow>
             AS_precondition (kstep s a) (current s) a'"
        using AS_prec_after_step by blast       
      show "\<forall> s d a a' . current s \<noteq> d \<and> AS_precondition s d a \<longrightarrow> AS_precondition (kstep s a') d a"
        using AS_prec_dom_independent by blast  
      show "\<forall> s a . invariant s \<longrightarrow> invariant (kstep s a)"
        using spec_of_invariant by blast
      show "\<And>s a. kprecondition s a \<equiv> kprecondition s a"
        by auto         
      show "\<And>aseq. realistic_execution aseq \<equiv> set aseq \<subseteq> AS_set"
        unfolding realistic_execution_def
        by auto
      show "\<forall>s a. \<forall> d \<in> involved a. kprecondition s (the a) \<longrightarrow> ifp d (current s)"
        using involved_ifp unfolding Kernel.involved_def by (auto split: option.splits)
      show "\<forall>s execs. next_action s execs \<rightharpoonup> (\<lambda>a. a \<in> actions_in_execution (execs (current s)))"
        using next_action_from_execs by blast 
      show "\<forall>s execs u. actions_in_execution (next_execs s execs u) \<subseteq> actions_in_execution (execs u)"
        using next_execs_subset by blast        
      show "\<forall>s d aseqs.
       case CISK_control s d aseqs of
       (a, aseqs', s') \<Rightarrow>
         thread_empty aseqs \<and> (a, aseqs') = (None, []) \<or>
         aseqs \<noteq> [] \<and> hd aseqs \<noteq> [] \<and> \<not> aborting s' d (the a) \<and> \<not> waiting s' d (the a) \<and> (a, aseqs') = (Some (hd (hd aseqs)), tl (hd aseqs) # tl aseqs) \<or>
         aseqs \<noteq> [] \<and> hd aseqs \<noteq> [] \<and> waiting s' d (the a) \<and> (a, aseqs', s') = (Some (hd (hd aseqs)), aseqs, s) \<or> (a, aseqs') = (None, tl aseqs)"
        using CISK_control_spec by blast
      show "\<forall>s n d aseqs. fst (CISK_control (cswitch n s) d aseqs) = fst (CISK_control s d aseqs)"
        using next_action_after_cswitch by auto
      show "\<forall>s execs d.
       current s \<noteq> d \<longrightarrow>
       fst (CISK_control (next_state s execs) d (execs d)) = None \<or> fst (CISK_control (next_state s execs) d (execs d)) = fst (CISK_control s d (execs d))"
        using next_action_after_next_state by auto
      show "\<forall>s a d aseqs. current s \<noteq> d \<longrightarrow> fst (CISK_control (step s a) d aseqs) = fst (CISK_control s d aseqs)"
        using next_action_after_step by auto
      show "\<forall>s d a execs. AS_precondition s d a \<longrightarrow> AS_precondition (next_state s execs) d a"
        using next_state_precondition by auto
      show "\<forall>s execs. invariant s \<longrightarrow> invariant (next_state s execs)"
        using next_state_invariant by auto
      show "\<forall>s a. waiting s (current s) a \<longrightarrow> kstep s a = s"
        using spec_of_waiting by blast
  qed
  
  note interpreted = int.Interruptible_Separation_Kernel_axioms
  note run_total_induct = Interruptible_Separation_Kernel.run_total.induct[of kstep output_f s0 current cswitch kprecondition realistic_execution
                                                                             CISK_control kinvolved ifp vpeq AS_set invariant AS_precondition aborting waiting _ interrupt]
  have run_equals_run_total:
     "\<And> n s execs . run n s execs \<equiv> Interruptible_Separation_Kernel.run_total kstep current cswitch interrupt CISK_control n s execs"
     proof-
        fix n s execs
        show "run n s execs \<equiv> Interruptible_Separation_Kernel.run_total kstep current cswitch interrupt CISK_control n s execs"
          using interpreted int.step_def
          by(induct n s execs rule: run_total_induct,auto split: option.splits)
     qed
  from interpreted
    have 0: "Interruptible_Separation_Kernel.isecure_total kstep output_f s0 current cswitch interrupt realistic_execution CISK_control kinvolved ifp"
    by (metis int.unwinding_implies_isecure_total)
  from 0 run_equals_run_total
    have 1: "NI_unrelated"
    by (metis realistic_executions_def int.isecure_total_def int.realistic_executions_def int.NI_unrelated_total_def NI_unrelated_def)
  from 0 run_equals_run_total
    have 2: "NI_indirect_sources"
    by (metis realistic_executions_def int.NI_indirect_sources_total_def int.isecure_total_def int.realistic_executions_def NI_indirect_sources_def)
  from 1 2 show ?thesis unfolding isecure_def by auto
qed

end
end

