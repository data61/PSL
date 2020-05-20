subsection \<open>ISK (Interruptible Separation Kernel)\<close>

theory ISK
  imports SK
begin


text \<open>

At this point, the precondition linking action to state is generic and highly unconstrained.
We refine the previous locale by given generic functions ``precondition'' and ``realistic\_trace'' a definiton.
This yields a total run function, instead of the partial one of locale Separation\_Kernel.

This definition is based on a set of valid action sequences AS\_set.
Consider for example the following action sequence:
\[\gamma = [COPY\_INIT,COPY\_CHECK,COPY\_COPY]\]
If action sequence $\gamma$ is a member of AS\_set, this means that the attack surface contains an action COPY, which consists of three consecutive atomic kernel actions.
Interrupts can occur anywhere between these atomic actions.

Given a set of valid action sequences such as $\gamma$, generic function precondition can be defined. 
It now consists of 1.) a generic invariant and 2.) more refined preconditions for the current action.

These preconditions need to be proven inductive only according to action sequences.
Assume, e.g., that $\gamma \in \mbox{AS\_set}$ and that $d$ is the currently active domain in state $s$.
The following constraints are assumed and must therefore be proven for the instantiation:
     \begin{itemize}
       \item ``AS\_precondition s d COPY\_INIT''\\ since COPY\_INIT is the start of an action sequence.
      \item ``AS\_precondition (step s COPY\_INIT) d COPY\_CHECK''\\ since (COPY\_INIT, COPY\_CHECK) is a sub sequence.
      \item ``AS\_precondition (step s COPY\_CHECK) d COPY\_COPY''\\ since (COPY\_CHECK, COPY\_COPY) is a sub sequence.
     \end{itemize}      
    Additionally, the precondition for domain $d$ must be consistent when a context switch occurs, or when ever some other domain $d'$ performs an action.
       
    Locale Interruptible\_Separation\_Kernel refines locale Separation\_Kernel in two ways.
    First, there is a definition of realistic executions.
    A realistic trace consists of action sequences from AS\_set.
 
    Secondly, the generic @{term control} function has been refined by additional assumptions.
    It is now assumed that control conforms to one of four possibilities:
    \begin{enumerate}
    \item The execution of the currently active domain is empty and the control function returns no action.
    \item The currently active domain is executing the action sequence at the head of the execution. It returns the next kernel action of this sequence and updates the execution accordingly.
    \item The action sequence is delayed.
    \item The action sequence that is at the head of the execution is skipped and the execution is updated accordingly.
    \end{enumerate}    
    As for the state update, this is still completely unconstrained and generic as long as it respects the generic invariant and the precondition.
\<close>

locale Interruptible_Separation_Kernel = Separation_Kernel kstep output_f s0 current cswitch interrupt kprecondition realistic_execution control kinvolved ifp vpeq
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
  and ifp :: "'dom_t \<Rightarrow> 'dom_t \<Rightarrow> bool"
  and vpeq :: "'dom_t \<Rightarrow> 'state_t \<Rightarrow> 'state_t \<Rightarrow> bool"
+
  fixes AS_set :: "('action_t list) set" \<comment> \<open>Returns a set of valid action sequences, i.e., the attack surface\<close>
    and invariant :: "'state_t \<Rightarrow> bool"
    and AS_precondition :: "'state_t \<Rightarrow> 'dom_t \<Rightarrow> 'action_t \<Rightarrow> bool"
    and aborting :: "'state_t \<Rightarrow> 'dom_t \<Rightarrow> 'action_t \<Rightarrow> bool"
    and waiting :: "'state_t \<Rightarrow> 'dom_t \<Rightarrow> 'action_t \<Rightarrow> bool"
assumes empty_in_AS_set: "[] \<in> AS_set"
    and invariant_s0: "invariant s0"
    and invariant_after_cswitch: "\<forall> s n . invariant s \<longrightarrow> invariant (cswitch n s)"
    and precondition_after_cswitch: "\<forall> s d n a. AS_precondition s d a \<longrightarrow> AS_precondition (cswitch n s) d a"
    and AS_prec_first_action: "\<forall> s d aseq . invariant s \<and> aseq \<in> AS_set \<and> aseq \<noteq> [] \<longrightarrow> AS_precondition s d (hd aseq)"
    and AS_prec_after_step: "\<forall> s a a' . (\<exists> aseq \<in> AS_set . is_sub_seq a a' aseq) \<and> invariant s \<and> AS_precondition s (current s) a \<and> \<not>aborting s (current s) a \<and> \<not> waiting s (current s) a \<longrightarrow> AS_precondition (kstep s a) (current s) a'"
    and AS_prec_dom_independent: "\<forall> s d a a' . current s \<noteq> d \<and> AS_precondition s d a \<longrightarrow> AS_precondition (kstep s a') d a"
    and spec_of_invariant: "\<forall> s a . invariant s \<longrightarrow> invariant (kstep s a)"
    (* The refinement: functions precondition and realistic trace now have a definition. Control has been refined to four cases. *)
    and kprecondition_def: "kprecondition s a \<equiv> invariant s \<and> AS_precondition s (current s) a"
    and realistic_execution_def: "realistic_execution aseq \<equiv> set aseq \<subseteq> AS_set"
    and control_spec: "\<forall> s d aseqs . case control s d aseqs of (a,aseqs',s') \<Rightarrow>
                                 (thread_empty aseqs \<and> (a,aseqs') = (None,[])) \<or> \<comment> \<open>Nothing happens\<close>
                                 (aseqs \<noteq> [] \<and> hd aseqs \<noteq> [] \<and> \<not>aborting s' d (the a) \<and> \<not> waiting s' d (the a) \<and> (a,aseqs') = (Some (hd (hd aseqs)), (tl (hd aseqs))#(tl aseqs))) \<or> \<comment> \<open>Execute the first action of the current action sequence\<close>
                                 (aseqs \<noteq> [] \<and> hd aseqs \<noteq> [] \<and> waiting s' d (the a) \<and> (a,aseqs',s') = (Some (hd (hd aseqs)),aseqs,s)) \<or> \<comment> \<open>Nothing happens, waiting to execute the next action\<close>
                                 (a,aseqs') = (None,tl aseqs)" (* The current action sequence is skipped *)
    and next_action_after_cswitch: "\<forall> s n d aseqs . fst (control (cswitch n s) d aseqs) = fst (control s d aseqs)"
    and next_action_after_next_state: "\<forall> s execs d  . current s \<noteq> d \<longrightarrow>  fst (control (next_state s execs) d (execs d)) = None \<or> fst (control (next_state s execs) d (execs d)) = fst (control s d (execs d))"
    and next_action_after_step: "\<forall> s a d aseqs . current s \<noteq> d \<longrightarrow> fst (control (step s a) d aseqs) = fst (control s d aseqs)"
    and next_state_precondition: "\<forall> s d a execs. AS_precondition s d a \<longrightarrow> AS_precondition (next_state s execs) d a"
    and next_state_invariant: "\<forall> s execs . invariant s \<longrightarrow> invariant (next_state s execs)"
    and spec_of_waiting: "\<forall> s a . waiting s (current s) a \<longrightarrow> kstep s a = s"
begin

text \<open>
  We can now formulate a total run function, since based on the new assumptions the case where the precondition does not hold, will never occur.
\<close>
function run_total :: "time_t \<Rightarrow> 'state_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> 'state_t"
where "run_total 0 s execs = s"
| "interrupt (Suc n) \<Longrightarrow> run_total (Suc n) s execs = run_total n (cswitch (Suc n) s) execs"
| "\<not>interrupt (Suc n) \<Longrightarrow> thread_empty(execs (current s)) \<Longrightarrow> run_total (Suc n) s execs = run_total n s execs"
| "\<not>interrupt (Suc n) \<Longrightarrow> \<not>thread_empty(execs (current s)) \<Longrightarrow>
      run_total (Suc n) s execs = run_total n (step (next_state s execs) (next_action s execs)) (next_execs s execs)"
using not0_implies_Suc by (metis prod_cases3,auto)
termination by lexicographic_order

text \<open>
  The major part of the proofs in this locale consist of proving that function run\_total is equivalent to function run, i.e., that the precondition does always hold.
  This assumes that the executions are \emph{realistic}.
  This means that the execution of each domain contains action sequences that are from AS\_set.
  This ensures, e.g, that a COPY\_CHECK is always preceded by a COPY\_INIT.
\<close>
definition realistic_executions :: "('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> bool"
where "realistic_executions execs \<equiv> \<forall> d . realistic_execution (execs d)"

text \<open>
  Lemma run\_total\_equals\_run is proven by doing induction.
  It is however not inductive and can therefore not be proven directly: a realistic execution is not necessarily realistic after performing one action.
  We generalize to do induction.
  Predicate realistic\_executions\_ind is the inductive version of realistic\_executions. All action sequences in the tail of the executions must be complete action sequences (i.e., they must be from AS\_set).
  The first action sequence, however, is being executed and is therefore not necessarily an action sequence from AS\_set, but it is \emph{the last part}
  of some action sequence from AS\_set.
\<close>
definition realistic_AS_partial :: "'action_t list \<Rightarrow> bool"
where "realistic_AS_partial aseq \<equiv> \<exists> n aseq' .  n \<le> length aseq' \<and> aseq' \<in> AS_set \<and> aseq = lastn n aseq'"
definition realistic_executions_ind :: "('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> bool"
where "realistic_executions_ind execs \<equiv> \<forall> d . (case execs d of [] \<Rightarrow> True | (aseq#aseqs) \<Rightarrow> realistic_AS_partial aseq \<and> set aseqs \<subseteq> AS_set)"
text \<open>
  We need to know that invariably, the precondition holds.
  As this precondition consists of 1.) a generic invariant and 2.) more refined preconditions for the current action, we have to know that these two are invariably true.
\<close>
definition precondition_ind :: "'state_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> bool"
where "precondition_ind s execs \<equiv> invariant s \<and> (\<forall> d . fst(control s d (execs d)) \<rightharpoonup> AS_precondition s d)"

text \<open>
  Proof that ``execution is realistic" is inductive, i.e., 
  assuming the current execution is realistic, the execution returned by the control mechanism is realistic.
\<close>
lemma next_execution_is_realistic_partial:
assumes na_def: "next_execs s execs d = aseq # aseqs"
    and d_is_curr: "d = current s"
    and realistic: "realistic_executions_ind execs"
    and thread_not_empty: "\<not>thread_empty(execs (current s))"
shows "realistic_AS_partial aseq \<and> set aseqs \<subseteq> AS_set"
proof-
let ?c = "control s (current s) (execs (current s))"
{
  assume c_empty: "let (a,aseqs',s') = ?c in
              (a,aseqs') = (None,[])"
 from na_def d_is_curr c_empty
   have ?thesis
   unfolding realistic_executions_ind_def next_execs_def by (auto) 
}
moreover
{
  let ?ct= "execs (current s)"
  let ?execs' = "(tl (hd ?ct))#(tl ?ct)"
  let ?a' = "Some (hd (hd ?ct))"
  assume hd_thread_not_empty: "hd (execs (current s)) \<noteq> []"
  assume c_executing: "let (a,aseqs',s') = ?c in
                            (a,aseqs') = (?a', ?execs')"
  from na_def c_executing d_is_curr
    have as_defs: "aseq = tl (hd ?ct) \<and> aseqs = tl ?ct"
    unfolding next_execs_def by (auto)                                        
  from realistic[unfolded realistic_executions_ind_def,THEN spec,where x=d] d_is_curr
    have subset: "set (tl ?execs') \<subseteq> AS_set"
    unfolding Let_def realistic_AS_partial_def 
    by (cases "execs d",auto)
  from d_is_curr thread_not_empty hd_thread_not_empty realistic[unfolded realistic_executions_ind_def,THEN spec,where x=d] 
    obtain n aseq' where n_aseq': "n \<le> length aseq' \<and> aseq' \<in> AS_set \<and> hd ?ct = lastn n aseq'"
    unfolding realistic_AS_partial_def
    by (cases "execs d",auto)
  from this hd_thread_not_empty have "n > 0" unfolding lastn_def by(cases n,auto)
  from this n_aseq' lastn_one_less[where n=n and x=aseq' and a="hd (hd ?ct)" and y="tl (hd ?ct)"] hd_thread_not_empty
    have "n - 1 \<le> length aseq' \<and> aseq' \<in> AS_set \<and> tl (hd ?ct) = lastn (n - 1) aseq'"
    by auto
  from this as_defs subset have ?thesis
    unfolding realistic_AS_partial_def
    by auto 
}
moreover
{
  let ?ct= "execs (current s)"
  let ?execs' = "?ct"
  let ?a' = "Some (hd (hd ?ct))"
  assume c_waiting: "let (a,aseqs',s') = ?c in
                            (a,aseqs') = (?a', ?execs')"
  from na_def c_waiting d_is_curr
    have as_defs: "aseq = hd ?execs' \<and> aseqs = tl ?execs'"
    unfolding next_execs_def by (auto)                                        
  from realistic[unfolded realistic_executions_ind_def,THEN spec,where x=d] d_is_curr set_tl_is_subset[where x="?execs'"]
    have subset: "set (tl ?execs') \<subseteq> AS_set"
    unfolding Let_def realistic_AS_partial_def 
    by (cases "execs d",auto)
  from na_def c_waiting d_is_curr
    have "?execs' \<noteq> []" unfolding next_execs_def by auto
  from realistic[unfolded realistic_executions_ind_def,THEN spec,where x=d] d_is_curr thread_not_empty
    obtain n aseq' where witness: "n \<le> length aseq' \<and> aseq' \<in> AS_set \<and> hd(execs d) = lastn n aseq'"
    unfolding realistic_AS_partial_def by (cases "execs d",auto)
  from d_is_curr this subset as_defs have ?thesis
    unfolding realistic_AS_partial_def
    by auto
}            
moreover
{
  let ?ct= "execs (current s)"
  let ?execs' = "tl ?ct"
  let ?a' = "None"
  assume c_aborting: "let (a,aseqs',s') = ?c in
                            (a,aseqs') = (?a', ?execs')"
  from na_def c_aborting d_is_curr
    have as_defs: "aseq = hd ?execs' \<and> aseqs = tl ?execs'"
    unfolding next_execs_def by (auto)                                        
  from realistic[unfolded realistic_executions_ind_def,THEN spec,where x=d] d_is_curr set_tl_is_subset[where x="?execs'"]
    have subset: "set (tl ?execs') \<subseteq> AS_set"
    unfolding Let_def realistic_AS_partial_def 
    by (cases "execs d",auto)
  from na_def c_aborting d_is_curr
    have "?execs' \<noteq> []" unfolding next_execs_def by auto
  from empty_in_AS_set this
    realistic[unfolded realistic_executions_ind_def,THEN spec,where x=d] d_is_curr
    have "length (hd ?execs') \<le> length (hd ?execs') \<and> (hd ?execs') \<in> AS_set \<and> hd ?execs' = lastn (length (hd ?execs')) (hd ?execs')"
    unfolding lastn_def
    by (cases "execs (current s)",auto)
  from this subset as_defs have ?thesis
    unfolding realistic_AS_partial_def
    by auto
}
ultimately
show ?thesis
  using control_spec[THEN spec,THEN spec,THEN spec,where x2=s and x1="current s" and x="execs (current s)"]
        d_is_curr thread_not_empty
  by (auto simp add: Let_def)
qed
            
text \<open>
  The lemma that proves that the total run function is equivalent to the partial run function, i.e., that in this refinement the case of the run function where the precondition is False will never occur.
\<close>
lemma run_total_equals_run:
  assumes realistic_exec: "realistic_executions execs"
      and invariant: "invariant s"      
    shows "strict_equal (run n (Some s) execs) (run_total n s execs)"
proof-
{
  fix n ms s execs
  have "strict_equal ms s \<and> realistic_executions_ind execs \<and> precondition_ind s execs \<longrightarrow> strict_equal (run n ms execs) (run_total n s execs)"
  proof (induct n ms execs arbitrary: s rule: run.induct)
  case (1 s execs sa)
    show ?case by auto
  next
  case (2 n execs s)
    show ?case unfolding strict_equal_def by auto
  next
  case (3 n s execs sa)
    assume interrupt: "interrupt (Suc n)"
    assume IH: "(\<And>sa. strict_equal (Some (cswitch (Suc n) s)) sa \<and> realistic_executions_ind execs \<and> precondition_ind sa execs \<longrightarrow>
             strict_equal (run n (Some (cswitch (Suc n) s)) execs) (run_total n sa execs))"
    {
      assume equal_s_sa: "strict_equal (Some s) sa"
      assume realistic: "realistic_executions_ind execs"
      assume inv_sa: "precondition_ind sa execs"
      have inv_nsa: "precondition_ind (cswitch (Suc n) sa) execs"
      proof-
        {
          fix d
          have "fst (control (cswitch (Suc n) sa) d (execs d)) \<rightharpoonup> AS_precondition (cswitch (Suc n) sa) d"
            using next_action_after_cswitch inv_sa[unfolded precondition_ind_def,THEN conjunct2,THEN spec,where x=d]
                  precondition_after_cswitch 
            unfolding Let_def B_def precondition_ind_def 
            by(cases "fst (control (cswitch (Suc n) sa) d (execs d))",auto)
        }
        thus ?thesis using inv_sa invariant_after_cswitch unfolding precondition_ind_def by auto
      qed          
      from equal_s_sa realistic inv_nsa inv_sa IH[where sa="cswitch (Suc n) sa"]
        have equal_ns_nt: "strict_equal (run n (Some (cswitch (Suc n) s)) execs) (run_total n (cswitch (Suc n) sa) execs)"
        unfolding strict_equal_def by(auto)
    }
    from this interrupt show ?case by auto
  next
  case (4 n execs s sa)
    assume not_interrupt: "\<not>interrupt (Suc n)"
    assume thread_empty: "thread_empty(execs (current s))"
    assume IH: "(\<And>sa. strict_equal (Some s) sa \<and> realistic_executions_ind execs \<and> precondition_ind sa execs \<longrightarrow> strict_equal (run n (Some s) execs) (run_total n sa execs))"
    have current_s_sa: "strict_equal (Some s) sa \<longrightarrow> current s = current sa" unfolding strict_equal_def by auto
    {
      assume equal_s_sa: "strict_equal (Some s) sa"
      assume realistic: "realistic_executions_ind execs"
      assume inv_sa: "precondition_ind sa execs"
      from equal_s_sa realistic inv_sa IH[where sa="sa"]
        have equal_ns_nt: "strict_equal (run n (Some s) execs) (run_total n sa execs)"
        unfolding strict_equal_def by(auto)
    }
    from this current_s_sa thread_empty not_interrupt show ?case by auto
  next
  case (5 n execs s sa)
    assume not_interrupt: "\<not>interrupt (Suc n)"
    assume thread_not_empty: "\<not>thread_empty(execs (current s))"
    assume not_prec: "\<not> precondition (next_state s execs) (next_action s execs)"
    \<comment> \<open>In locale ISK, the precondition can be proven to hold at all times. This case cannot happen, and we can prove False.\<close>
    {
      assume equal_s_sa: "strict_equal (Some s) sa"
      assume realistic: "realistic_executions_ind execs"
      assume inv_sa: "precondition_ind sa execs"
      from equal_s_sa have s_sa: "s = sa" unfolding strict_equal_def by auto
      from inv_sa have
        "next_action sa execs \<rightharpoonup> AS_precondition sa (current sa)"
        unfolding precondition_ind_def B_def next_action_def
        by (cases "next_action sa execs",auto)
      from this next_state_precondition
        have "next_action sa execs \<rightharpoonup> AS_precondition (next_state sa execs) (current sa)"
        unfolding precondition_ind_def B_def
        by (cases "next_action sa execs",auto)
      from inv_sa this s_sa next_state_invariant current_next_state
        have prec_s: "precondition (next_state s execs) (next_action s execs)"
        unfolding precondition_ind_def kprecondition_def precondition_def B_def
        by (cases "next_action sa execs",auto)
      from this not_prec have False by auto
    }
    thus ?case by auto
  next
  case (6 n execs s sa)
    assume not_interrupt: "\<not>interrupt (Suc n)"
    assume thread_not_empty: "\<not>thread_empty(execs (current s))"
    assume prec: "precondition (next_state s execs) (next_action s execs)"
    assume IH: "(\<And>sa. strict_equal (Some (step (next_state s execs) (next_action s execs))) sa \<and>
             realistic_executions_ind (next_execs s execs) \<and> precondition_ind sa (next_execs s execs) \<longrightarrow>
             strict_equal (run n (Some (step (next_state s execs) (next_action s execs))) (next_execs s execs)) (run_total n sa (next_execs s execs)))"
    have current_s_sa: "strict_equal (Some s) sa \<longrightarrow> current s = current sa" unfolding strict_equal_def by auto            
    {
      assume equal_s_sa: "strict_equal (Some s) sa"
      assume realistic: "realistic_executions_ind execs"
      assume inv_sa: "precondition_ind sa execs"
     
      from equal_s_sa have s_sa: "s = sa" unfolding strict_equal_def by auto
     
      let ?a = "next_action s execs"
      let ?ns = "step (next_state s execs) ?a"
      let ?na = "next_execs s execs"
      let ?c = "control s (current s) (execs (current s))"

      have equal_ns_nsa: "strict_equal (Some ?ns) ?ns" unfolding strict_equal_def by auto
      from inv_sa equal_s_sa have inv_s: "invariant s" unfolding strict_equal_def precondition_ind_def by auto

      \<comment> \<open>Two things are proven inductive. First, the assumptions that the execution is realistic (statement realistic-na). This proof uses lemma next-execution-is-realistic-partial.
          Secondly, the precondition: if the precondition holds for the current action, then it holds for the next action (statement invariant-na).\<close>
      have realistic_na: "realistic_executions_ind ?na"
      proof-
        {
          fix d
          have "case ?na d of [] \<Rightarrow> True | aseq # aseqs \<Rightarrow> realistic_AS_partial aseq \<and> set aseqs \<subseteq> AS_set"
          proof(cases "?na d",simp,rename_tac aseq aseqs,simp,cases "d = current s")
          case False
            fix aseq aseqs
            assume "next_execs s execs d = aseq # aseqs"
            from False this realistic[unfolded realistic_executions_ind_def,THEN spec,where x=d]
              show "realistic_AS_partial aseq \<and> set aseqs \<subseteq> AS_set"
              unfolding next_execs_def by simp
          next
          case True
            fix aseq aseqs
            assume na_def: "next_execs s execs d = aseq # aseqs"
            from next_execution_is_realistic_partial na_def True realistic thread_not_empty
              show "realistic_AS_partial aseq \<and> set aseqs \<subseteq> AS_set" by blast
          qed
        }
        thus ?thesis unfolding realistic_executions_ind_def by auto
      qed
      have invariant_na: "precondition_ind ?ns ?na"
      proof-
        from spec_of_invariant inv_sa next_state_invariant s_sa have inv_ns: "invariant ?ns"
          unfolding precondition_ind_def step_def
          by (cases "next_action sa execs",auto)
        have "\<forall>d. fst (control ?ns d (?na d)) \<rightharpoonup> AS_precondition ?ns d"
        proof-
        {
          fix d
          {
          let ?a' = "fst (control ?ns d (?na d))"
          assume snd_action_not_none: "?a' \<noteq> None"
          have "AS_precondition ?ns d (the ?a')"
          proof (cases "d = current s")
          case True
            {
              have ?thesis
              proof (cases "?a")
              case (Some a)
                \<comment> \<open>Assuming that the current domain executes some action a, and assuming that the action a' after that is not None (statement snd-action-not-none),
                    we prove that the precondition is inductive, i.e., it will hold for a'.
                    Two cases arise: either action a is delayed (case waiting) or not (case executing).\<close>
                show ?thesis
                proof(cases "?na d = execs (current s)" rule :case_split[case_names waiting executing])
                case executing \<comment> \<open>The kernel is executing two consecutive actions a and a'. We show that [a,a'] is a subsequence in some action in AS-set.
                                   The PO's ensure that the precondition is inductive.\<close> 
                  from executing True Some control_spec[THEN spec,THEN spec,THEN spec,where x2=s and x1=d and x="execs d"]
                    have a_def: "a = hd (hd (execs (current s))) \<and> ?na d = (tl (hd (execs (current s))))#(tl (execs (current s)))"
                    unfolding next_action_def next_execs_def Let_def
                    by(auto)
                  from a_def True snd_action_not_none control_spec[THEN spec,THEN spec,THEN spec,where x2="?ns" and x1=d and x="?na d"]
                    second_elt_is_hd_tl[where x=" hd (execs (current s))" and a="hd(tl(hd (execs (current s))))" and x'="tl (tl(hd (execs (current s))))"]
                    have na_def: "the ?a' = (hd (execs (current s)))!1"
                    unfolding next_execs_def
                    by(auto)                    
                  from Some realistic[unfolded realistic_executions_ind_def,THEN spec,where x=d] True thread_not_empty
                    obtain n aseq' where witness: "n \<le> length aseq' \<and> aseq' \<in> AS_set \<and> hd(execs d) = lastn n aseq'"
                    unfolding realistic_AS_partial_def by (cases "execs d",auto)
                  from True executing length_lt_2_implies_tl_empty[where x="hd (execs (current s))"]
                    Some control_spec[THEN spec,THEN spec,THEN spec,where x2=s and x1=d and x="execs d"]
                    snd_action_not_none control_spec[THEN spec,THEN spec,THEN spec,where x2="?ns" and x1=d and x="?na d"]
                    have in_action_sequence: "length (hd (execs (current s))) \<ge> 2"
                    unfolding next_action_def next_execs_def
                    by auto
                  from this witness consecutive_is_sub_seq[where a=a and b="the ?a'" and n=n and y=aseq' and x="tl (tl (hd (execs (current s))))"] 
                    a_def na_def True in_action_sequence
                    x_is_hd_snd_tl[where x="hd (execs (current s))"]
                    have 1: "\<exists> aseq' \<in> AS_set . is_sub_seq a (the ?a') aseq'"
                    by(auto)
                  from True Some inv_sa[unfolded precondition_ind_def,THEN conjunct2,THEN spec,where x="current s"] s_sa 
                    have 2: "AS_precondition s (current s) a"
                    unfolding strict_equal_def next_action_def B_def by auto
                  from executing True Some control_spec[THEN spec,THEN spec,THEN spec,where x2=s and x1=d and x="execs d"]
                    have not_aborting: "\<not>aborting (next_state s execs) (current s) (the ?a)"
                    unfolding next_action_def next_state_def next_execs_def
                    by auto
                  from executing True Some control_spec[THEN spec,THEN spec,THEN spec,where x2=s and x1=d and x="execs d"]
                    have not_waiting: "\<not>waiting (next_state s execs) (current s) (the ?a)"
                    unfolding next_action_def next_state_def next_execs_def
                    by auto                  
                  from True this
                    1 2 inv_s
                    sub_seq_in_prefixes[where X=AS_set] Some next_state_invariant
                    current_next_state[THEN spec,THEN spec,where x1=s and x=execs]
                    AS_prec_after_step[THEN spec,THEN spec,THEN spec,where x2="next_state s execs" and x1="a" and x="the ?a'"]
                    next_state_precondition not_aborting not_waiting 
                    show ?thesis
                    unfolding step_def
                    by auto
                  next
                  case waiting \<comment> \<open>The kernel is delaying action a. Thus the action after a, which is a', is equal to a.\<close>
                    from tl_hd_x_not_tl_x[where x="execs d"] True waiting control_spec[THEN spec,THEN spec,THEN spec,where x2=s and x1=d and x="execs d"] Some
                      have a_def: "?na d = execs (current s) \<and> next_state s execs = s \<and> waiting s d (the ?a)"
                      unfolding next_action_def next_execs_def next_state_def
                      by(auto)
                    from Some waiting a_def True snd_action_not_none control_spec[THEN spec,THEN spec,THEN spec,where x2="?ns" and x1=d and x="?na d"]
                      have na_def: "the ?a' = hd (hd (execs (current s)))"
                      unfolding next_action_def next_execs_def
                      by(auto)
                    from spec_of_waiting a_def True
                      have no_step: "step s ?a = s" unfolding step_def by (cases "next_action s execs",auto)
                    from no_step Some True a_def 
                          inv_sa[unfolded precondition_ind_def,THEN conjunct2,THEN spec,where x="current s"] s_sa
                      have 2: "AS_precondition s (current s) (the ?a')"
                      unfolding next_action_def B_def 
                      by(auto)
                    from a_def na_def this True Some no_step
                      show ?thesis
                      unfolding step_def
                      by(auto)
                  qed
              next
              case None
                \<comment> \<open>Assuming that the current domain does not execute an action, and assuming that the action a' after that is not None (statement snd-action-not-none),
                    we prove that the precondition is inductive, i.e., it will hold for a'.
                    This holds, since the control mechanism will ensure that action a' is the start of a new action sequence in AS-set.\<close>              
                from None True snd_action_not_none control_spec[THEN spec,THEN spec,THEN spec,where x2="?ns" and x1=d and x="?na d"]
                     control_spec[THEN spec,THEN spec,THEN spec,where x2=s and x1=d and x="execs d"]
                  have na_def: "the ?a' = hd (hd (tl (execs (current s)))) \<and> ?na d = tl (execs (current s))"
                  unfolding next_action_def next_execs_def
                  by(auto)
                from True None snd_action_not_none control_spec[THEN spec,THEN spec,THEN spec,where x2="?ns" and x1=d and x="?na d"]
                     this
                  have 1: "tl (execs (current s)) \<noteq> [] \<and> hd (tl (execs (current s))) \<noteq> []"
                  by auto
                from this realistic[unfolded realistic_executions_ind_def,THEN spec,where x=d] True thread_not_empty
                  have "hd (tl (execs (current s))) \<in> AS_set"
                  by (cases "execs d",auto)
                from True snd_action_not_none this
                  inv_ns this na_def 1
                  AS_prec_first_action[THEN spec,THEN spec,THEN spec,where x2="?ns" and x="hd (tl (execs (current s)))" and x1=d]
                  show ?thesis by auto
              qed
            }
            thus ?thesis
              using control_spec[THEN spec,THEN spec,THEN spec,where x2="?ns" and x1="current s" and x="?na (current s)"]
                    thread_not_empty True snd_action_not_none
              by (auto simp add: Let_def)
          next
          case False
            from False have equal_na_a: "?na d = execs d"
              unfolding next_execs_def by auto
            from this False current_next_state next_action_after_step
              have "?a' = fst (control (next_state s execs) d (next_execs s execs d))"
              unfolding next_action_def by auto
            from inv_sa[unfolded precondition_ind_def,THEN conjunct2,THEN spec,where x=d] s_sa equal_na_a  this
                 next_action_after_next_state[THEN spec,THEN spec,THEN spec,where x=d and x2=s and x1=execs]
                 snd_action_not_none False
              have "AS_precondition s d (the ?a')"
              unfolding precondition_ind_def next_action_def B_def by (cases "fst (control sa d (execs d))",auto)
            from equal_na_a False this next_state_precondition current_next_state
              AS_prec_dom_independent[THEN spec,THEN spec,THEN spec,THEN spec,where x3="next_state s execs" and x2=d and x="the ?a" and x1="the ?a'"]
              show ?thesis 
              unfolding step_def
              by (cases "next_action s execs",auto)
          qed
          }
          hence "fst (control ?ns d (?na d)) \<rightharpoonup> AS_precondition ?ns d" unfolding B_def
            by (cases "fst (control ?ns d (?na d))",auto)
        }
        thus ?thesis by auto
      qed
      from this inv_ns show ?thesis
        unfolding precondition_ind_def B_def Let_def
        by (auto)
      qed
      from equal_ns_nsa realistic_na invariant_na s_sa IH[where sa="?ns"]
        have equal_ns_nt: "strict_equal (run n (Some ?ns) ?na) (run_total n (step (next_state sa execs) (next_action sa execs)) (next_execs sa execs))"
        by(auto)
    }
    from this current_s_sa thread_not_empty not_interrupt prec show ?case by auto
  qed
}
hence thm_inductive: "\<forall> m s execs n . strict_equal m s \<and> realistic_executions_ind execs \<and> precondition_ind s execs \<longrightarrow> strict_equal (run n m execs) (run_total n s execs)" by blast
have 1: "strict_equal (Some s) s" unfolding strict_equal_def by simp
have 2: "realistic_executions_ind execs"
  proof-
  {
    fix d
    have "case execs d of [] \<Rightarrow> True | aseq # aseqs \<Rightarrow> realistic_AS_partial aseq \<and> set aseqs \<subseteq> AS_set"
    proof(cases "execs d",simp)
    case (Cons aseq aseqs)
      from Cons realistic_exec[unfolded realistic_executions_def,THEN spec,where x=d]
        have 0: "length aseq \<le> length aseq \<and> aseq \<in> AS_set \<and> aseq = lastn (length aseq) aseq"
        unfolding lastn_def realistic_execution_def by auto
      hence 1: "realistic_AS_partial aseq" unfolding realistic_AS_partial_def by auto
      from Cons realistic_exec[unfolded realistic_executions_def,THEN spec,where x=d]
        have 2: "set aseqs \<subseteq> AS_set"
        unfolding realistic_execution_def by auto
      from Cons 1 2 show ?thesis by auto
    qed
  }
  thus ?thesis unfolding realistic_executions_ind_def by auto
  qed   
have 3: "precondition_ind s execs"
  proof-
    {
      fix d
      {
      assume not_empty: "fst (control s d (execs d)) \<noteq> None"
      from not_empty realistic_exec[unfolded realistic_executions_def,THEN spec,where x=d]
        have current_aseq_is_realistic: "hd (execs d) \<in> AS_set"
        using control_spec[THEN spec,THEN spec,THEN spec,where x="execs d" and x1=d and x2=s]
        unfolding realistic_execution_def by(cases "execs d",auto)
      from not_empty current_aseq_is_realistic invariant AS_prec_first_action[THEN spec,THEN spec,THEN spec, where x2=s and x1=d and x="hd (execs d)"]
        have "AS_precondition s d (the (fst (control s d (execs d))))"
        using control_spec[THEN spec,THEN spec,THEN spec,where x="execs d" and x1=d and x2=s]
        by auto
      }
      hence "fst (control s d (execs d)) \<rightharpoonup> AS_precondition s d"
        unfolding B_def
        by (cases " fst (control s d (execs d))",auto)
    }
    from this invariant show ?thesis unfolding precondition_ind_def by auto
  qed
from thm_inductive 1 2 3 show ?thesis by auto   
qed

text \<open>
  Theorem unwinding\_implies\_isecure gives security for all realistic executions.
  For unrealistic executions, it holds vacuously and therefore does not tell us anything.
  In order to prove security for this refinement (i.e., for function run\_total), we have to prove that purging yields realistic runs.
\<close>

lemma realistic_purge:
  shows "\<forall> execs d . realistic_executions execs \<longrightarrow> realistic_executions (purge execs d)"
proof-
{
  fix execs d
  assume "realistic_executions execs"
  hence "realistic_executions (purge execs d)"
    using someI[where P=realistic_execution and x="execs d"]
    unfolding realistic_executions_def purge_def by(simp)
}
thus ?thesis by auto
qed

lemma remove_gateway_comm_subset:
shows "set (remove_gateway_communications d exec) \<subseteq> set exec \<union> {[]}"
by(induct exec,auto)

lemma realistic_ipurge_l:
  shows "\<forall> execs d . realistic_executions execs \<longrightarrow> realistic_executions (ipurge_l execs d)"
proof-
{
  fix execs d
  assume 1: "realistic_executions execs"
  from empty_in_AS_set remove_gateway_comm_subset[where d=d and exec="execs d"] 1 have "realistic_executions (ipurge_l execs d)"
    unfolding realistic_execution_def realistic_executions_def ipurge_l_def by(auto)
}
thus ?thesis by auto
qed

lemma realistic_ipurge_r:
  shows "\<forall> execs d . realistic_executions execs \<longrightarrow> realistic_executions (ipurge_r execs d)"
proof-
{
  fix execs d
  assume 1: "realistic_executions execs"
  from empty_in_AS_set remove_gateway_comm_subset[where d=d and exec="execs d"] 1 have "realistic_executions (ipurge_r execs d)"
    using someI[where P="\<lambda> x . realistic_execution x" and x="execs d"]
    unfolding realistic_execution_def realistic_executions_def ipurge_r_def by(auto)
}
thus ?thesis by auto
qed

text \<open>
  We now have sufficient lemma's to prove security for run\_total.
  The definition of security is similar to that in Section~\ref{sec:sep_kernel}.
  It now assumes that the executions are realistic and concerns function run\_total instead of function run.
\<close>

definition NI_unrelated_total::bool
where "NI_unrelated_total
  \<equiv> \<forall> execs a n . realistic_executions execs \<longrightarrow>
                     (let s_f = run_total n s0 execs in
                       output_f s_f a = output_f (run_total n s0 (purge execs (current s_f))) a
                        \<and> current s_f = current (run_total n s0 (purge execs (current s_f))))"

definition NI_indirect_sources_total::bool
where "NI_indirect_sources_total
  \<equiv> \<forall> execs a n. realistic_executions execs \<longrightarrow>
                    (let s_f = run_total n s0 execs in
                      output_f (run_total n s0 (ipurge_l execs (current s_f))) a =
                      output_f (run_total n s0 (ipurge_r execs (current s_f))) a)"

definition isecure_total::bool
where "isecure_total \<equiv> NI_unrelated_total \<and> NI_indirect_sources_total"

theorem unwinding_implies_isecure_total:
shows isecure_total
proof-
  from unwinding_implies_isecure have secure_partial: "NI_unrelated" unfolding isecure_def by blast
  from unwinding_implies_isecure have isecure1_partial: "NI_indirect_sources" unfolding isecure_def by blast

  have NI_unrelated_total: NI_unrelated_total
  proof-
    {
    fix execs a n
    assume realistic: "realistic_executions execs"
    from invariant_s0 realistic run_total_equals_run[where n=n and s=s0 and execs=execs]
      have 1: "strict_equal (run n (Some s0) execs) (run_total n s0 execs)" by auto

    have "let s_f = run_total n s0 execs in output_f s_f a = output_f (run_total n s0 (purge execs (current s_f))) a \<and> current s_f = current (run_total n s0 (purge execs (current s_f)))"
    proof (cases "run n (Some s0) execs")
    case None
      thus ?thesis using 1 unfolding NI_unrelated_total_def strict_equal_def by auto
    next
    case (Some s_f)
      from realistic_purge invariant_s0 realistic run_total_equals_run[where n=n and s=s0 and execs="purge execs (current s_f)"]
        have 2: "strict_equal (run n (Some s0) (purge execs (current s_f))) (run_total n s0 (purge execs (current s_f)))"
        by auto
      show ?thesis proof(cases "run n (Some s0) (purge execs (current s_f))")
      case None
        from 2 None show ?thesis using 2 unfolding NI_unrelated_total_def strict_equal_def by auto
      next
      case (Some s_f2)
        from \<open>run n (Some s0) execs = Some s_f\<close> Some 1 2  secure_partial[unfolded NI_unrelated_def,THEN spec,THEN spec,THEN spec,where x=n and x2=execs]
          show ?thesis
          unfolding strict_equal_def NI_unrelated_def
          by(simp add: Let_def B_def B2_def)
      qed
    qed
    }
    thus ?thesis unfolding NI_unrelated_total_def by auto
  qed
  have NI_indirect_sources_total: NI_indirect_sources_total
  proof-
    {
    fix execs a n
    assume realistic: "realistic_executions execs"
    from invariant_s0 realistic run_total_equals_run[where n=n and s=s0 and execs=execs]
      have 1: "strict_equal (run n (Some s0) execs) (run_total n s0 execs)" by auto

    have "let s_f = run_total n s0 execs in output_f (run_total n s0 (ipurge_l execs (current s_f))) a = output_f (run_total n s0 (ipurge_r execs (current s_f))) a"
    proof (cases "run n (Some s0) execs")
    case None
      thus ?thesis using 1 unfolding NI_unrelated_total_def strict_equal_def by auto
    next
    case (Some s_f)
      from realistic_ipurge_l invariant_s0 realistic run_total_equals_run[where n=n and s=s0 and execs="ipurge_l execs (current s_f)"]
        have 2: "strict_equal (run n (Some s0) (ipurge_l execs (current s_f))) (run_total n s0 (ipurge_l execs (current s_f)))"
        by auto
      from realistic_ipurge_r invariant_s0 realistic run_total_equals_run[where n=n and s=s0 and execs="ipurge_r execs (current s_f)"]
        have 3: "strict_equal (run n (Some s0) (ipurge_r execs (current s_f))) (run_total n s0 (ipurge_r execs (current s_f)))"
        by auto
       
      show ?thesis proof(cases "run n (Some s0) (ipurge_l execs (current s_f))")
      case None
        from 2 None show ?thesis using 2 unfolding NI_unrelated_total_def strict_equal_def by auto
      next
      case (Some s_ipurge_l)
        show ?thesis
        proof(cases "run n (Some s0) (ipurge_r execs (current s_f))")
        case None
          from 3 None show ?thesis using 2 unfolding NI_unrelated_total_def strict_equal_def by auto
          next
          case (Some s_ipurge_r)
            from \<open>run n (Some s0) execs = Some s_f\<close> \<open>run n (Some s0) (ipurge_l execs (current s_f)) = Some s_ipurge_l\<close>
                  Some 1 2 3 isecure1_partial[unfolded NI_indirect_sources_def,THEN spec,THEN spec,THEN spec,where x=n and x2=execs]
            show ?thesis
              unfolding strict_equal_def NI_unrelated_def
              by(simp add: Let_def B_def B2_def)
        qed
      qed
    qed
    }
    thus ?thesis unfolding NI_indirect_sources_total_def by auto
  qed
  from NI_unrelated_total NI_indirect_sources_total show ?thesis unfolding isecure_total_def by auto 
qed

end
end
