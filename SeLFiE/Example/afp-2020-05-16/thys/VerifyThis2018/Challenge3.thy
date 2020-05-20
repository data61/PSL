chapter \<open>Array-Based Queuing Lock\<close>
section \<open>Challenge\<close>
text_raw \<open>{\upshape
Array-Based Queuing Lock (ABQL)
is a variation of the Ticket Lock algorithm with a bounded number
of concurrent threads and improved scalability due to better cache
behaviour.
%(\url{https://en.wikipedia.org/wiki/Array_Based_Queuing_Locks})

We assume that there are \texttt{N} threads and we
allocate a shared Boolean array \texttt{pass[]} of length \texttt{N}.
We also allocate a shared integer value \texttt{next}.
In practice, \texttt{next} is an unsigned bounded
integer that wraps to 0 on overflow, and
we assume that the maximal value of \texttt{next} is
of the form $k\mathtt{N} - 1$.
Finally, we assume at our disposal
an atomic \texttt{fetch\_and\_add} instruction,
such that \texttt{fetch\_and\_add(next,1)} increments the value
of \texttt{next} by 1 and returns the original value of \texttt{next}.

The elements of \texttt{pass[]} are spinlocks, assigned
individually to each thread in the waiting queue.
Initially, each element of \texttt{pass[]} is set to
\texttt{false}, except \texttt{pass[0]} which is set to
\texttt{true}, allowing the first coming thread to acquire
the lock.
Variable \texttt{next} contains the number of the first available
place in the waiting queue and is initialized to 0.

Here is an implementation of the locking algorithm in pseudocode:
\begin{lstlisting}[language=C,morekeywords={procedure,function,end,to,in,var,then,not,mod}]
procedure abql_init()
    for i = 1 to N - 1 do
        pass[i] := false
    end-for
    pass[0] := true
    next := 0
end-procedure

function abql_acquire()
    var my_ticket := fetch_and_add(next,1) mod N
    while not pass[my_ticket] do
    end-while
    return my_ticket
end-function

procedure abql_release(my_ticket)
    pass[my_ticket] := false
    pass[(my_ticket + 1) mod N] := true
end-procedure
\end{lstlisting}
Each thread that acquires the lock must eventually release it
by calling \texttt{abql\_release(my\_ticket)}, where \texttt{my\_ticket}
is the return value of the earlier call of \texttt{abql\_acquire()}.
We assume that no thread tries to re-acquire the lock while already
holding it, neither it attempts to release the lock which it does not possess.

Notice that the first
assignment in \texttt{abql\_release()} can be moved at the end
of \texttt{abql\_acquire()}.

\bigskip
\noindent\textbf{Verification task~1.}~Verify
the safety of ABQL
under the given assumptions. Specifically, you should prove that no two
threads can hold the lock at any given time.

\bigskip
\noindent\textbf{Verification task~2.}~Verify
the fairness, namely that the threads acquire the lock
in order of request.

\bigskip
\noindent\textbf{Verification task~3.}~Verify
the liveness under a fair scheduler, namely that
each thread requesting the lock will eventually acquire it.

\bigskip
You have liberty of adapting the implementation and specification
of the concurrent setting as best suited for your verification tool.
In particular, solutions with a fixed value of \texttt{N} are acceptable.
We expect, however, that the general idea of the algorithm and
the non-deterministic behaviour of the scheduler shall be preserved.
}
\clearpage
\<close>

section \<open>Solution\<close>
theory Challenge3
imports "lib/VTcomp" "lib/DF_System"
begin
  text \<open>The Isabelle Refinement Framework does not support concurrency.
    However, Isabelle is a general purpose theorem prover, thus we can model
    the problem as a state machine, and prove properties over runs.
    
    For this polished solution, we make use of a small library for
    transition systems and simulations: @{theory VerifyThis2018.DF_System}.
    Note, however, that our definitions are still quite ad-hoc, 
    and there are lots of opportunities to define libraries that make similar 
    proofs simpler and more canonical.
    
    
    We approach the final ABQL with three refinement steps:
      \<^enum> We model a ticket lock with unbounded counters, and prove safety, fairness, and liveness.
      \<^enum> We bound the counters by \<open>mod N\<close> and \<open>mod (k*N) respectively\<close>
      \<^enum> We implement the current counter by an array, 
        yielding exactly the algorithm described in the challenge.

    With a simulation argument, we transfer the properties of the abstract 
    system over the refinements.
    
    The final theorems proving safety, fairness, and liveness can be found at 
    the end of this chapter, in Subsection~\ref{sec:main_theorems}.
  \<close>  

  subsection \<open>General Definitions\<close>
  text \<open>We fix a positive number \<open>N\<close> of threads\<close>
  consts N :: nat
  specification (N) N_not0[simp, intro!]: "N\<noteq>0" by auto
  lemma N_gt0[simp, intro!]: "0<N" by (cases N) auto 

  text \<open>A thread's state, representing the sequence points in the given algorithm.
    This will not change over the refinements.\<close>
  datatype thread = 
    INIT 
  | is_WAIT: WAIT (ticket: nat) 
  | is_HOLD: HOLD (ticket: nat) 
  | is_REL: REL (ticket: nat)
  
  
    
  subsection \<open>Refinement 1: Ticket Lock with Unbounded Counters\<close>
  
  text \<open>System's state: Current ticket, next ticket, thread states\<close>
  type_synonym astate = "nat \<times> nat \<times> (nat \<Rightarrow> thread)"

  abbreviation "cc \<equiv> fst"
  abbreviation "nn s \<equiv> fst (snd s)"
  abbreviation "tts s \<equiv> snd (snd s)"
  
  
  text \<open>The step relation of a single thread\<close>  
  inductive astep_sng where
    enter_wait: "astep_sng (c,n,INIT) (c,(n+1),WAIT n)"
  | loop_wait: "c\<noteq>k \<Longrightarrow> astep_sng (c,n,WAIT k) (c,n,WAIT k)"
  | exit_wait: "astep_sng (c,n,WAIT c) (c,n,HOLD c)"
  | start_release: "astep_sng (c,n,HOLD k) (c,n,REL k)"
  | release: "astep_sng (c,n,REL k) (k+1,n,INIT)"

  text \<open>The step relation of the system\<close>
  inductive alstep for t where
    "\<lbrakk> t<N; astep_sng (c,n,ts t) (c',n',s') \<rbrakk> 
      \<Longrightarrow> alstep t (c,n,ts) (c',n',ts(t:=s'))"
      
  text \<open>Initial state of the system\<close>
  definition "as\<^sub>0 \<equiv> (0, 0, \<lambda>_. INIT)"
    
  interpretation A: system as\<^sub>0 alstep .
  
  text \<open>In our system, each thread can always perform a step\<close>
  lemma never_blocked: "A.can_step l s \<longleftrightarrow> l<N"
    apply (cases s; cases "tts s l"; simp)
    unfolding A.can_step_def
    apply (clarsimp simp: alstep.simps astep_sng.simps; blast)+
    done
  
  text \<open>Thus, our system is in particular deadlock free\<close>
  interpretation A: df_system as\<^sub>0 alstep 
    apply unfold_locales
    subgoal for s
      using never_blocked[of 0 s]
      unfolding A.can_step_def
      by auto
    done
    
    
  subsubsection \<open>Safety: Mutual Exclusion\<close>  
    
  text \<open>Predicates to express that a thread uses or holds a ticket\<close>
  definition "has_ticket s k \<equiv> s=WAIT k \<or> s=HOLD k \<or> s=REL k"
  lemma has_ticket_simps[simp]: 
    "\<not>has_ticket INIT k"
    "has_ticket (WAIT k) k'\<longleftrightarrow> k'=k"
    "has_ticket (HOLD k) k'\<longleftrightarrow> k'=k"
    "has_ticket (REL k) k'\<longleftrightarrow> k'=k"
    unfolding has_ticket_def by auto
    
  definition "locks_ticket s k \<equiv> s=HOLD k \<or> s=REL k"  
  lemma locks_ticket_simps[simp]: 
    "\<not>locks_ticket INIT k"
    "\<not>locks_ticket (WAIT k) k'"
    "locks_ticket (HOLD k) k'\<longleftrightarrow> k'=k"
    "locks_ticket (REL k) k'\<longleftrightarrow> k'=k"
    unfolding locks_ticket_def by auto

  lemma holds_imp_uses: "locks_ticket s k \<Longrightarrow> has_ticket s k"
    unfolding locks_ticket_def by auto
    
  text \<open>We show the following invariant.
    Intuitively, it can be read as follows:
      \<^item> Current lock is less than or equal next lock
      \<^item> For all threads that use a ticket (i.e., are waiting, holding, or releasing):
        \<^item> The ticket is in between current and next
        \<^item> No other thread has the same ticket
        \<^item> Only the current ticket can be held (or released)
  \<close>    

  definition "invar1 \<equiv> \<lambda>(c,n,ts).
    c \<le> n
  \<and> (\<forall>t k. t<N \<and> has_ticket (ts t) k \<longrightarrow> 
      c \<le> k \<and> k < n
    \<and> (\<forall>t' k'. t'<N \<and> has_ticket (ts t') k' \<and> t\<noteq>t' \<longrightarrow> k\<noteq>k')  
    \<and> (\<forall>k. k\<noteq>c \<longrightarrow> \<not>locks_ticket (ts t) k)
    )
  "  
    
  lemma is_invar1: "A.is_invar invar1"
    apply rule
    subgoal by (auto simp: invar1_def as\<^sub>0_def)
    subgoal for s s'
      apply (clarify)
      apply (erule alstep.cases)
      apply (erule astep_sng.cases)
      apply (clarsimp_all simp: invar1_def)
      apply fastforce
      apply fastforce
      apply fastforce
      apply fastforce
      by (metis Suc_le_eq holds_imp_uses locks_ticket_def le_neq_implies_less)
    done

  text \<open>From the above invariant, it's straightforward to show mutual exclusion\<close>
  theorem mutual_exclusion: "\<lbrakk>A.reachable s; 
      t<N; t'<N; t\<noteq>t'; is_HOLD (tts s t); is_HOLD (tts s t')
    \<rbrakk> \<Longrightarrow> False" 
    apply (cases "tts s t"; simp)
    apply (cases "tts s t'"; simp)
    using A.invar_reachable[OF is_invar1, of s]
    apply (auto simp: invar1_def)
    by (metis locks_ticket_simps(3) has_ticket_simps(3))
      
  lemma mutual_exclusion': "\<lbrakk>A.reachable s; 
      t<N; t'<N; t\<noteq>t'; 
      locks_ticket (tts s t) tk; locks_ticket (tts s t') tk'
    \<rbrakk> \<Longrightarrow> False" 
    apply (cases "tts s t"; simp; cases "tts s t'"; simp)
    apply (cases "tts s t'"; simp)
    using A.invar_reachable[OF is_invar1, of s]
    apply (clarsimp_all simp: invar1_def)
    unfolding locks_ticket_def has_ticket_def
    apply metis+
    done

  subsubsection \<open>Fairness: Ordered Lock Acquisition\<close>      
  text \<open>We first show an auxiliary lemma: 
    Consider a segment of a run from \<open>i\<close> to \<open>j\<close>. Every thread that waits for
    a ticket in between the current ticket at \<open>i\<close> and the current ticket at \<open>j\<close>
    will be granted the lock in between \<open>i\<close> and \<open>j\<close>.
  \<close>      
  
  lemma fair_aux:  
    assumes R: "A.is_run s"
    assumes A: "i<j" "cc (s i) \<le> k" "k < cc (s j)" "t<N" "tts (s i) t=WAIT k"
    shows "\<exists>l. i\<le>l \<and> l<j \<and> tts (s l) t = HOLD k"
  proof -
    interpret A: run as\<^sub>0 alstep s by unfold_locales fact
  
    from A show ?thesis
    proof (induction "j-i" arbitrary: i)
      case 0
      then show ?case by auto
    next
      case (Suc i')
      
      hence [simp]: "i'=j - Suc i" by auto
      note IH=Suc.hyps(1)[OF this]
      
      obtain t' where "alstep t' (s i) (s (Suc i))" by (rule A.stepE)
      then show ?case using Suc.prems
      proof cases
        case (1 c n ts c' n' s')
        note [simp] = "1"(1,2,3)
        
        from A.run_invar[OF is_invar1, of i] have "invar1 (c,n,ts)" by auto
        note I1 = this[unfolded invar1_def, simplified]
        
        from "1"(4) show ?thesis
        proof (cases rule: astep_sng.cases)
          case enter_wait
          then show ?thesis 
            using IH Suc.prems apply (auto)
            by (metis "1"(2) Suc_leD Suc_lessI fst_conv leD thread.distinct(1))
        next
          case (loop_wait k)
          then show ?thesis  
            using IH Suc.prems apply (auto)
            by (metis "1"(2) Suc_leD Suc_lessI fst_conv leD)
          
        next
          case exit_wait
          then show ?thesis
            apply (cases "t'=t")
            subgoal
              using Suc.prems apply clarsimp 
              by (metis "1"(2) Suc_leD Suc_lessI fst_conv fun_upd_same leD 
                less_or_eq_imp_le snd_conv)
            subgoal
              using Suc.prems IH
              apply auto
              by (metis "1"(2) Suc_leD Suc_lessI fst_conv leD)
            done  
        next
          case (start_release k)
          then show ?thesis
            using IH Suc.prems apply (auto)
            by (metis "1"(2) Suc_leD Suc_lessI fst_conv leD thread.distinct(7))
        next
          case (release k)
          then show ?thesis
            apply (cases "t'=t")
            using I1 IH Suc.prems apply (auto)
            by (metis "1"(2) "1"(3) Suc_leD Suc_leI Suc_lessI fst_conv 
              locks_ticket_simps(4) le_antisym not_less_eq_eq 
              has_ticket_simps(2) has_ticket_simps(4))
        qed
      qed
    qed
  qed  
  
  lemma s_case_expand: 
    "(case s of (c, n, ts) \<Rightarrow> P c n ts) = P (cc s) (nn s) (tts s)"
    by (auto split: prod.splits)
  
  
  text \<open>
    A version of the fairness lemma which is very detailed on the 
    actual ticket numbers. We will weaken this later.
  \<close>  
  lemma fair_aux2:
    assumes RUN: "A.is_run s"
    assumes ACQ: "t<N" "tts (s i) t=INIT" "tts (s (Suc i)) t=WAIT k" 
    assumes HOLD: "i<j" "tts (s j) t = HOLD k" 
    assumes WAIT: "t'<N" "tts (s i) t' = WAIT k'" 
    obtains l where "i<l" "l<j" "tts (s l) t' = HOLD k'" 
  proof -
    interpret A: run as\<^sub>0 alstep s by unfold_locales fact
  
    from ACQ WAIT have [simp]: "t\<noteq>t'" "t'\<noteq>t" by auto
    from ACQ have [simp]: 
      "nn (s i) = k \<and> nn (s (Suc i)) = Suc k 
    \<and> cc (s (Suc i)) = cc (s i) \<and> tts (s (Suc i)) = (tts (s i))(t:=WAIT k)"
      apply (rule_tac A.stepE[of i])
      apply (erule alstep.cases)
      apply (erule astep_sng.cases)
      by (auto simp: nth_list_update split: if_splits)
      
    from A.run_invar[OF is_invar1, of i] have "invar1 (s i)" by auto
    note I1 = this[unfolded invar1_def, unfolded s_case_expand, simplified]
    
    from WAIT I1 have "k' < k" by fastforce
    from ACQ HOLD have "Suc i \<noteq> j" by auto with HOLD have "Suc i < j" by auto
      
    have X1: "cc (s i) \<le> k'" using I1 WAIT by fastforce
    have X2: "k' < cc (s j)" 
      using A.run_invar[OF is_invar1, of j, unfolded invar1_def s_case_expand]
      using \<open>k' < k\<close> \<open>t<N\<close> HOLD(2)
      apply clarsimp 
      by (metis locks_ticket_simps(3) has_ticket_simps(3))
    
    from fair_aux[OF RUN \<open>Suc i < j\<close>, of k' t', simplified] obtain l where
      "l\<ge>Suc i" "l<j" "tts (s l) t' = HOLD k'"
      using WAIT X1 X2 by auto
      
    thus ?thesis
      apply (rule_tac that[of l])
      by auto
      
  qed        

  lemma find_hold_position:
    assumes RUN: "A.is_run s"
    assumes WAIT: "t<N" "tts (s i) t = WAIT tk"
    assumes NWAIT: "i<j" "tts (s j) t \<noteq> WAIT tk"
    obtains l where "i<l" "l\<le>j" "tts (s l) t = HOLD tk"
  proof -
    interpret A: run as\<^sub>0 alstep s by unfold_locales fact
  
    from WAIT(2) NWAIT have "\<exists>l. i<l \<and> l\<le>j \<and> tts (s l) t = HOLD tk"
    proof (induction "j-i" arbitrary: i)
      case 0
      then show ?case by auto
    next
      case (Suc i')
      
      hence [simp]: "i'=j - Suc i" by auto
      note IH=Suc.hyps(1)[OF this]
      
      obtain t' where "alstep t' (s i) (s (Suc i))" by (rule A.stepE)
      then show ?case
        apply -
        apply (cases "t=t'";erule alstep.cases; erule astep_sng.cases)
        apply auto
        using IH Suc.prems Suc.hyps(2)
        apply (auto)
        apply (metis Suc_lessD Suc_lessI fun_upd_same snd_conv)
        apply (metis Suc_lessD Suc_lessI fun_upd_other snd_conv)
        apply (metis Suc.prems(1) Suc_lessD Suc_lessI fun_upd_triv)
        apply (metis Suc_lessD Suc_lessI fun_upd_other snd_conv)
        apply (metis Suc_lessD Suc_lessI fun_upd_other snd_conv)
        apply (metis Suc_lessD Suc_lessI fun_upd_other snd_conv)
        done
    qed
    thus ?thesis using that by blast
  qed    
  
  
  text \<open>
    Finally we can show fairness, which we state as follows:
      Whenever a thread \<open>t\<close> gets a ticket, all other threads \<open>t'\<close> waiting for the lock
      will be granted the lock before \<open>t\<close>.
  \<close>  
  theorem fair:
    assumes RUN: "A.is_run s"
    assumes ACQ: "t<N" "tts (s i) t=INIT" "is_WAIT (tts (s (Suc i)) t)" 
      \<comment> \<open>Thread \<open>t\<close> calls \<open>acquire\<close> in step \<open>i\<close>\<close>
    assumes HOLD: "i<j" "is_HOLD (tts (s j) t)" 
      \<comment> \<open>Thread \<open>t\<close> holds lock in step \<open>j\<close>\<close>
    assumes WAIT: "t'<N" "is_WAIT (tts (s i) t')" 
      \<comment> \<open>Thread \<open>t'\<close> waits for lock at step \<open>i\<close>\<close>
    obtains l where "i<l" "l<j" "is_HOLD (tts (s l) t')" 
      \<comment> \<open>Then, \<open>t'\<close> gets lock earlier\<close>
  proof -  
    obtain k where Wk: "tts (s (Suc i)) t = WAIT k" using ACQ
      by (cases "tts (s (Suc i)) t") auto
    
    obtain k' where Wk': "tts (s i) t' = WAIT k'" using WAIT
      by (cases "tts (s i) t'") auto
      
    from ACQ HOLD have "Suc i \<noteq> j" by auto with HOLD have "Suc i < j" by auto

      
    obtain j' where H': "Suc i < j'" "j' \<le> j" "tts (s j') t = HOLD k"
      apply (rule find_hold_position[OF RUN \<open>t<N\<close> Wk \<open>Suc i < j\<close>])
      using HOLD(2) by auto

    show ?thesis  
      apply (rule fair_aux2[OF RUN ACQ(1,2) Wk _ H'(3) WAIT(1) Wk'])
      subgoal using H'(1) by simp
      subgoal apply (erule that) using H'(2) by auto
      done
  qed    
  
  subsubsection \<open>Liveness\<close>
  
  text \<open>For all tickets in between the current and the next ticket, 
    there is a thread that has this ticket\<close>
  definition "invar2 
    \<equiv> \<lambda>(c,n,ts). \<forall>k. c\<le>k \<and> k<n \<longrightarrow> (\<exists>t<N. has_ticket (ts t) k)"
  
  lemma is_invar2: "A.is_invar invar2"
    apply rule
    subgoal by (auto simp: invar2_def as\<^sub>0_def)
    subgoal for s s'
      apply (clarsimp simp: invar2_def)
      apply (erule alstep.cases; erule astep_sng.cases; clarsimp)
      apply (metis less_antisym has_ticket_simps(1))
      subgoal by (metis has_ticket_simps(2))
      subgoal by (metis has_ticket_simps(2))
      subgoal by (metis has_ticket_simps(3))
      subgoal
        apply (frule A.invar_reachable[OF is_invar1])
        unfolding invar1_def 
        apply clarsimp 
        by (metis Suc_leD locks_ticket_simps(4) 
          not_less_eq_eq has_ticket_simps(4))
      done
    done  
    
  text \<open>If a thread t is waiting for a lock, the current lock is also used by a thread\<close> 
  corollary current_lock_used:
    assumes R: "A.reachable (c,n,ts)"
    assumes WAIT: "t<N" "ts t = WAIT k" 
    obtains t' where "t'<N"  "has_ticket (ts t') c"
    using A.invar_reachable[OF is_invar2 R] 
      and A.invar_reachable[OF is_invar1 R] WAIT
    unfolding invar1_def invar2_def apply auto
    by (metis (full_types) le_neq_implies_less not_le order_mono_setup.refl 
      has_ticket_simps(2))
    
  text \<open>Used tickets are unique (Corollary from invariant 1)\<close>  
  lemma has_ticket_unique: "\<lbrakk>A.reachable (c,n,ts); 
      t<N; has_ticket (ts t) k; t'<N; has_ticket (ts t') k
    \<rbrakk> \<Longrightarrow> t'=t"
    apply (drule A.invar_reachable[OF is_invar1])
    by (auto simp: invar1_def) 
    
  text \<open>We define the thread that holds a specified ticket\<close>
  definition "tkt_thread \<equiv> \<lambda>ts k. THE t. t<N \<and> has_ticket (ts t) k"
  lemma tkt_thread_eq: 
    assumes R: "A.reachable (c,n,ts)"  
    assumes A: "t<N" "has_ticket (ts t) k"
    shows "tkt_thread ts k = t"
    using has_ticket_unique[OF R]
    unfolding tkt_thread_def
    using A by auto
  
  lemma holds_only_current:
    assumes R: "A.reachable (c,n,ts)"  
    assumes A: "t<N" "locks_ticket (ts t) k"
    shows "k=c"
    using A.invar_reachable[OF is_invar1 R] A unfolding invar1_def
    using holds_imp_uses by blast
    
  text \<open>For the inductive argument, we will use this measure, that decreases as a
    single thread progresses through its phases.
  \<close>  
  definition "tweight s \<equiv> 
    case s of WAIT _ \<Rightarrow> 3::nat | HOLD _ \<Rightarrow> 2 | REL _ \<Rightarrow> 1 | INIT \<Rightarrow> 0"  

  
  text \<open>We show progress: Every thread that waits for the lock
    will eventually hold the lock.\<close>
  theorem progress:
    assumes FRUN: "A.is_fair_run s"
    assumes A: "t<N" "is_WAIT (tts (s i) t)"
    shows "\<exists>j>i. is_HOLD (tts (s j) t)"
  proof -
    interpret A: fair_run as\<^sub>0 alstep s by unfold_locales fact
  
    from A obtain k where Wk: "tts (s i) t = WAIT k"
      by (cases "tts (s i) t") auto
    
    text \<open>We use the following induction scheme:
      \<^item> Either the current thread increases (if we reach \<open>k\<close>, we are done)
      \<^item> (lex) the thread using the current ticket makes a step
      \<^item> (lex) another thread makes a step
    \<close>
    define lrel where "lrel \<equiv> 
      inv_image (measure id <*lex*> measure id <*lex*> measure id) (\<lambda>i. (
        k-cc (s i),
        tweight (tts (s i) (tkt_thread (tts (s i)) (cc (s i)))),
        A.dist_step (tkt_thread (tts (s i)) (cc (s i))) i
      ))"
  
    have "wf lrel" unfolding lrel_def by auto
    then show ?thesis using A(1) Wk   
    proof (induction i)
      case (less i)

      text \<open>We name the components of this and the next state\<close>
      obtain c n ts where [simp]: "s i = (c,n,ts)" by (cases "s i")
      from A.run_reachable[of i] have R: "A.reachable (c,n,ts)" by simp
      
      obtain c' n' ts' where [simp]: "s (Suc i) = (c',n',ts')" 
        by (cases "s (Suc i)")
      from A.run_reachable[of "Suc i"] have R': "A.reachable (c',n',ts')" 
        by simp
            
      from less.prems have WAIT[simp]: "ts t = WAIT k" by simp
      
      {
        text \<open>If thread \<open>t\<close> left waiting state, we are done\<close>
        assume "ts' t \<noteq> WAIT k"
        hence "ts' t = HOLD k" using less.prems
          apply (rule_tac A.stepE[of i])
          apply (auto elim!: alstep.cases astep_sng.cases split: if_splits)
          done
        hence ?case by auto
      } moreover {
        assume [simp]: "ts' t = WAIT k"
        text \<open>Otherwise, we obtain the thread \<open>tt\<close> that holds the current lock\<close>
        obtain tt where UTT: "tt<N" "has_ticket (ts tt) c"
          using current_lock_used[of c n ts t k] 
            and less.prems A.run_reachable[of i]
          by auto
        
        have [simp]: "tkt_thread ts c = tt" using tkt_thread_eq[OF R UTT] .
        note [simp] = \<open>tt<N\<close>
          
        
        have "A.can_step tt (s i)" by (simp add: never_blocked)
        hence ?case proof (cases rule: A.rstep_cases)
          case (other t') \<comment> \<open>Another thread than \<open>tt\<close> makes a step.\<close>
          
          text \<open>The current ticket and \<open>tt\<close>'s state remain the same\<close>
          hence [simp]: "c' = c \<and> ts' tt = ts tt"
            using has_ticket_unique[OF R UTT, of t']
            unfolding A.rstep_def
            using holds_only_current[OF R, of t']
            by (force elim!: alstep.cases astep_sng.cases)

          text \<open>Thus, \<open>tt\<close> is still using the current ticket\<close>
          have [simp]: "tkt_thread ts' c = tt"
            using UTT tkt_thread_eq[OF R', of tt c] by auto

          text \<open>Only the distance to \<open>tt\<close>'s next step has decreased\<close>
          have "(Suc i, i) \<in> lrel"
            unfolding lrel_def tweight_def by (simp add: other)
          
          text \<open>And we can apply the induction hypothesis\<close>
          with less.IH[of "Suc i"] \<open>t<N\<close> show ?thesis
            apply (auto) using Suc_lessD by blast
        next
          case THIS: this \<comment> \<open>The thread \<open>tt\<close> that uses the current ticket makes a step\<close>

          show ?thesis 
          proof (cases "\<exists>k'. ts tt = REL k'")
            case True \<comment> \<open>\<open>tt\<close> has finished releasing the lock \<close>
            then have [simp]: "ts tt = REL c"
              using UTT by auto
            
            text \<open>Thus, current increases\<close>  
            have [simp]: "c' = Suc c"
              using THIS apply -
              unfolding A.rstep_def
              apply (erule alstep.cases, erule astep_sng.cases)
              by auto
        
            text \<open>But is still less than \<open>k\<close>\<close>  
            from A.invar_reachable[OF is_invar1 R] have "k>c"
              apply (auto simp: invar1_def)
              by (metis UTT WAIT \<open>ts tt = REL c\<close> le_neq_implies_less 
                less.prems(1) thread.distinct(9) has_ticket_simps(2))
              
            text \<open>And we can apply the induction hypothesis\<close>  
            hence "(Suc i, i) \<in> lrel"
              unfolding lrel_def by auto
            with less.IH[of "Suc i"] \<open>t<N\<close> show ?thesis
              apply (auto) using Suc_lessD by blast
          next
            case False \<comment> \<open>\<open>tt\<close> has acquired the lock, or started releasing it\<close>
            
            text \<open>Hence, current remains the same, but the weight of \<open>tt\<close> decreases\<close>
            hence [simp]: "
              c' = c 
            \<and> tweight (ts tt) > tweight (ts' tt) 
            \<and> has_ticket (ts' tt) c"
              using THIS UTT apply -
              unfolding A.rstep_def
              apply (erule alstep.cases, erule astep_sng.cases)
              by (auto simp: has_ticket_def tweight_def)
            
            text \<open>\<open>tt\<close> still holds the current lock\<close>    
            have [simp]: "tkt_thread ts' c = tt"
              using tkt_thread_eq[OF R' \<open>tt<N\<close>, of c] by simp

            text \<open>And we can apply the IH\<close>
            have "(Suc i, i) \<in> lrel" unfolding lrel_def by auto
            with less.IH[of "Suc i"] \<open>t<N\<close> show ?thesis
              apply (auto) using Suc_lessD by blast
          qed
        qed  
      }
      ultimately show ?case by blast
    qed
  qed      
  
  
      
subsection \<open>Refinement 2: Bounding the Counters\<close>  
  text \<open>We fix the \<open>k\<close> from the task description, which must be positive\<close>
  consts k::nat
  specification (k) k_not0[simp]: "k\<noteq>0" by auto
  lemma k_gt0[simp]: "0<k" by (cases k) auto  

  
  text \<open>System's state: Current ticket, next ticket, thread states\<close>
  type_synonym bstate = "nat \<times> nat \<times> (nat \<Rightarrow> thread)" 
  
  text \<open>The step relation of a single thread\<close>  
  inductive bstep_sng where
    enter_wait: "bstep_sng (c,n,INIT) (c,(n+1) mod (k*N),WAIT (n mod N))"
  | loop_wait: "c\<noteq>tk \<Longrightarrow> bstep_sng (c,n,WAIT tk) (c,n,WAIT tk)"
  | exit_wait: "bstep_sng (c,n,WAIT c) (c,n,HOLD c)"
  | start_release: "bstep_sng (c,n,HOLD tk) (c,n,REL tk)"
  | release: "bstep_sng (c,n,REL tk) ((tk+1) mod N,n,INIT)"

  text \<open>The step relation of the system, labeled with the thread \<open>t\<close> that performs the step\<close>
  inductive blstep for t where
    "\<lbrakk> t<N; bstep_sng (c,n,ts t) (c',n',s') \<rbrakk> 
      \<Longrightarrow> blstep t (c,n,ts) (c',n',ts(t:=s'))"
  
  text \<open>Initial state of the system\<close>
  definition "bs\<^sub>0 \<equiv> (0, 0, \<lambda>_. INIT)"
  
  interpretation B: system bs\<^sub>0 blstep .
        
  lemma b_never_blocked: "B.can_step l s \<longleftrightarrow> l<N"
    apply (cases s; cases "tts s l"; simp)
    unfolding B.can_step_def
    apply (clarsimp simp: blstep.simps bstep_sng.simps; blast)+
    done
  
  interpretation B: df_system bs\<^sub>0 blstep 
    apply unfold_locales
    subgoal for s
      using b_never_blocked[of 0 s]
      unfolding B.can_step_def
      by auto
    done
  
subsubsection \<open>Simulation\<close>  
  text \<open>We show that the abstract system simulates the concrete one.\<close>
    
  text \<open>A few lemmas to ease the automation further below\<close>  
  lemma nat_sum_gtZ_iff[simp]: 
    "finite s \<Longrightarrow> sum f s \<noteq> (0::nat) \<longleftrightarrow> (\<exists>x\<in>s. f x \<noteq> 0)"    
    by simp
    
  lemma n_eq_Suc_sub1_conv[simp]: "n = Suc (n - Suc 0) \<longleftrightarrow> n\<noteq>0" by auto
    
  lemma mod_mult_mod_eq[mod_simps]: "x mod (k * N) mod N = x mod N"  
    by (meson dvd_eq_mod_eq_0 mod_mod_cancel mod_mult_self2_is_0)

  lemma mod_eq_imp_eq_aux: "b mod N = (a::nat) mod N \<Longrightarrow> a\<le>b \<Longrightarrow> b<a+N \<Longrightarrow> b=a"  
    by (metis Groups.add_ac add_0_right 
      le_add_diff_inverse less_diff_conv2 nat_minus_mod 
      nat_minus_mod_plus_right mod_if)
    
  lemma mod_eq_imp_eq: 
    "\<lbrakk>b \<le> x; x < b + N; b \<le> y; y < b + N; x mod N = y mod N \<rbrakk> \<Longrightarrow> x=y"
  proof -
    assume a1: "b \<le> y"
    assume a2: "y < b + N"
    assume a3: "b \<le> x"
    assume a4: "x < b + N"
    assume a5: "x mod N = y mod N"
    have f6: "x < y + N"
      using a4 a1 by linarith
    have "y < x + N"
      using a3 a2 by linarith
    then show ?thesis
      using f6 a5 by (metis (no_types) mod_eq_imp_eq_aux nat_le_linear)
  qed
    

  text \<open>Map the ticket of a thread\<close>  
  fun map_ticket where
    "map_ticket f INIT = INIT"
  | "map_ticket f (WAIT tk) = WAIT (f tk)"
  | "map_ticket f (HOLD tk) = HOLD (f tk)"
  | "map_ticket f (REL tk) = REL (f tk)"
  
  lemma map_ticket_addsimps[simp]:
    "map_ticket f t = INIT \<longleftrightarrow> t=INIT"  
    "map_ticket f t = WAIT tk \<longleftrightarrow> (\<exists>tk'. tk=f tk' \<and> t=WAIT tk')"
    "map_ticket f t = HOLD tk \<longleftrightarrow> (\<exists>tk'. tk=f tk' \<and> t=HOLD tk')"
    "map_ticket f t = REL tk \<longleftrightarrow> (\<exists>tk'. tk=f tk' \<and> t=REL tk')"
    by (cases t; auto)+
  
  text \<open>We define the number of threads that use a ticket\<close>  
    
  fun ni_weight :: "thread \<Rightarrow> nat" where
    "ni_weight INIT = 0" | "ni_weight _ = 1"
  
  lemma ni_weight_le1[simp]: "ni_weight s \<le> Suc 0"
    by (cases s) auto
      
  definition "num_ni ts \<equiv> \<Sum> i=0..<N. ni_weight (ts i)"
  lemma num_ni_init[simp]: "num_ni (\<lambda>_. INIT) = 0" by (auto simp: num_ni_def)
  
  lemma num_ni_upd: 
    "t<N \<Longrightarrow> num_ni (ts(t:=s)) = num_ni ts - ni_weight (ts t) + ni_weight s"
    by (auto 
      simp: num_ni_def if_distrib[of ni_weight] sum.If_cases algebra_simps
      simp: sum_diff1_nat
      )
      
  lemma num_ni_nz_if[simp]: "\<lbrakk>t < N; ts t \<noteq> INIT\<rbrakk> \<Longrightarrow> num_ni ts \<noteq> 0"
    apply (cases "ts t")
    by (simp_all add: num_ni_def) force+

  lemma num_ni_leN: "num_ni ts \<le> N"
    apply (clarsimp simp: num_ni_def)
    apply (rule order_trans)
    apply (rule sum_bounded_above[where K=1])
    apply auto
    done

  text \<open>We provide an additional invariant, considering the distance of 
    \<open>c\<close> and \<open>n\<close>. Although we could probably get this from the previous 
    invariants, it is easy enough to prove directly.
  \<close>        
  definition "invar3 \<equiv> \<lambda>(c,n,ts). n = c + num_ni ts"
  
  lemma is_invar3: "A.is_invar invar3"
    apply (rule)
    subgoal by (auto simp: invar3_def as\<^sub>0_def)
    subgoal for s s'
      apply clarify
      apply (erule alstep.cases, erule astep_sng.cases)
      apply (auto simp: invar3_def num_ni_upd)
      using holds_only_current by fastforce
    done  

  text \<open>We establish a simulation relation: The concrete counters are 
    the abstract ones, wrapped around.
  \<close>  
      
  definition "sim_rel1 \<equiv> \<lambda>(c,n,ts) (ci,ni,tsi). 
    ci = c mod N
  \<and> ni = n mod (k*N)
  \<and> tsi = (map_ticket (\<lambda>t. t mod N)) o ts
  "

  lemma sraux: 
    "sim_rel1 (c,n,ts) (ci,ni,tsi) \<Longrightarrow> ci = c mod N \<and> ni = n mod (k*N)"
    by (auto simp: sim_rel1_def Let_def)
    
  lemma sraux2: "\<lbrakk>sim_rel1 (c,n,ts) (ci,ni,tsi); t<N\<rbrakk> 
    \<Longrightarrow> tsi t = map_ticket (\<lambda>x. x mod N) (ts t)"  
    by (auto simp: sim_rel1_def Let_def)
    
    
  interpretation sim1: simulationI as\<^sub>0 alstep bs\<^sub>0 blstep sim_rel1
  proof unfold_locales
    show "sim_rel1 as\<^sub>0 bs\<^sub>0"
      by (auto simp: sim_rel1_def as\<^sub>0_def bs\<^sub>0_def)
  next
    fix as bs t bs'  
    assume Ra_aux: "A.reachable as" 
       and Rc_aux: "B.reachable bs" 
       and SIM: "sim_rel1 as bs" 
       and CS: "blstep t bs bs'"
  
    obtain c n ts where [simp]: "as=(c,n,ts)" by (cases as)
    obtain ci ni tsi where [simp]: "bs=(ci,ni,tsi)" by (cases bs)
    obtain ci' ni' tsi' where [simp]: "bs'=(ci',ni',tsi')" by (cases bs')
    from Ra_aux have Ra: "A.reachable (c,n,ts)" by simp
    from Rc_aux have Rc: "B.reachable (ci,ni,tsi)" by simp
       
    from CS have "t<N" by cases auto
    
    have [simp]: "n = c + num_ni ts"
      using A.invar_reachable[OF is_invar3 Ra, unfolded invar3_def] by simp
    
    have AUX1: "c\<le>tk" "tk<c+N" if "ts t = WAIT tk" for tk
      using that A.invar_reachable[OF is_invar1 Ra]
      apply (auto simp: invar1_def)
      using \<open>t<N\<close> apply fastforce
      using \<open>t<N\<close> num_ni_leN[of ts] by fastforce
      
    from SIM CS have "\<exists>as'. alstep t as as' \<and> sim_rel1 as' bs'"
      apply simp
      apply (erule blstep.cases)
      apply (erule bstep_sng.cases)
      apply clarsimp_all
    subgoal
      apply (intro exI conjI)
      apply (rule alstep.intros)
      apply (simp add: sim_rel1_def Let_def)
      apply (simp add: sraux sraux2)
      apply (rule astep_sng.enter_wait)
      apply (simp add: sim_rel1_def; intro conjI ext)
      apply (auto simp: sim_rel1_def Let_def mod_simps)  
      done
    subgoal
      apply (clarsimp simp: sraux sraux2)
      apply (intro exI conjI)
      apply (rule alstep.intros)
      apply (simp add: sim_rel1_def Let_def)
      apply clarsimp
      apply (rule astep_sng.loop_wait)
      apply (auto simp: sim_rel1_def Let_def mod_simps)  
      done
    subgoal
      apply (clarsimp simp: sraux sraux2)
      subgoal for tk'
        apply (subgoal_tac "tk'=c")
        apply (intro exI conjI)
        apply (rule alstep.intros)
        apply (simp add: sim_rel1_def Let_def)
        apply clarsimp
        apply (rule astep_sng.exit_wait)
        apply (auto simp: sim_rel1_def Let_def mod_simps) []
        apply (clarsimp simp: sim_rel1_def)
        apply (erule mod_eq_imp_eq_aux)
        apply (auto simp: AUX1)
        done
      done
    subgoal
      apply (clarsimp simp: sraux sraux2)
      apply (intro exI conjI)
      apply (rule alstep.intros)
      apply (simp add: sim_rel1_def Let_def)
      apply clarsimp
      apply (rule astep_sng.start_release)
      apply (auto simp: sim_rel1_def Let_def mod_simps)  
      done
    subgoal
      apply (clarsimp simp: sraux sraux2)
      apply (intro exI conjI)
      apply (rule alstep.intros)
      apply (simp add: sim_rel1_def Let_def)
      apply clarsimp
      apply (rule astep_sng.release)
      apply (auto simp: sim_rel1_def Let_def mod_simps)
      done
    done  
    then show "\<exists>as'. sim_rel1 as' bs' \<and> alstep t as as'" by blast
  next  
    fix as bs l
    assume "A.reachable as" "B.reachable bs" "sim_rel1 as bs" "A.can_step l as"
    then show "B.can_step l bs" using b_never_blocked never_blocked by simp
  qed      


  subsubsection \<open>Transfer of Properties\<close>
    
  text \<open>We transfer a few properties over the simulation,
    which we need for the next refinement step.
  \<close>
  
  lemma xfer_locks_ticket:
    assumes "locks_ticket (map_ticket (\<lambda>t. t mod N) (ts t)) tki"  
    obtains tk where "tki=tk mod N" "locks_ticket (ts t) tk"
    using assms unfolding locks_ticket_def
    by auto
  
  
  lemma b_holds_only_current: 
    "\<lbrakk>B.reachable (c, n, ts); t < N; locks_ticket (ts t) tk\<rbrakk> \<Longrightarrow> tk = c"
    apply (rule sim1.xfer_reachable, assumption)
    apply (clarsimp simp: sim_rel1_def)
    apply (erule xfer_locks_ticket)+
    using holds_only_current 
    by blast
  
  lemma b_mutual_exclusion': "\<lbrakk>B.reachable s; 
      t<N; t'<N; t\<noteq>t'; locks_ticket (tts s t) tk; locks_ticket (tts s t') tk'
    \<rbrakk> \<Longrightarrow> False" 
    apply (rule sim1.xfer_reachable, assumption)
    apply (clarsimp simp: sim_rel1_def)
    apply (erule xfer_locks_ticket)+
    apply (drule (3) mutual_exclusion'; simp)
    done
    
  lemma xfer_has_ticket:
    assumes "has_ticket (map_ticket (\<lambda>t. t mod N) (ts t)) tki"  
    obtains tk where "tki=tk mod N" "has_ticket (ts t) tk"
    using assms unfolding has_ticket_def
    by auto
    
  lemma has_ticket_in_range:
    assumes Ra: "A.reachable (c,n,ts)" and "t<N" and U: "has_ticket (ts t) tk" 
    shows "c\<le>tk \<and> tk<c+N"  
  proof -
    
    have [simp]: "n=c + num_ni ts"
      using A.invar_reachable[OF is_invar3 Ra, unfolded invar3_def] by simp
    
    show "c\<le>tk \<and> tk<c+N" 
      using A.invar_reachable[OF is_invar1 Ra] U
      apply (auto simp: invar1_def)
      using \<open>t<N\<close> apply fastforce
      using \<open>t<N\<close> num_ni_leN[of ts] by fastforce
  qed  
    
  lemma b_has_ticket_unique: "\<lbrakk>B.reachable (ci,ni,tsi); 
      t<N; has_ticket (tsi t) tki; t'<N; has_ticket (tsi t') tki
    \<rbrakk> \<Longrightarrow> t'=t"
    apply (rule sim1.xfer_reachable, assumption)
    apply (auto simp: sim_rel1_def)
    subgoal for c n ts
      apply (erule xfer_has_ticket)+
      apply simp
      subgoal for tk tk'
        apply (subgoal_tac "tk=tk'")
        apply simp
        apply (frule (4) has_ticket_unique, assumption)
        apply (frule (2) has_ticket_in_range[where tk=tk])
        apply (frule (2) has_ticket_in_range[where tk=tk'])
        apply (auto simp: mod_simps)
        apply (rule mod_eq_imp_eq; (assumption|simp))
        done
      done
    done  
        
        
  
  
  
subsection \<open>Refinement 3: Using an Array\<close>text_raw \<open>\label{sec:refine3}\<close>
  text \<open>Finally, we use an array instead of a counter, thus obtaining
    the exact data structures from the challenge assignment.
    
    Note that we model the array by a list of Booleans here.
  \<close>
  
  text \<open>System's state: Current ticket array, next ticket, thread states\<close>
  type_synonym cstate = "bool list \<times> nat \<times> (nat \<Rightarrow> thread)" 
  
  text \<open>The step relation of a single thread\<close>  
  inductive cstep_sng where
    enter_wait: "cstep_sng (p,n,INIT) (p,(n+1) mod (k*N),WAIT (n mod N))"
  | loop_wait: "\<not>p!tk \<Longrightarrow> cstep_sng (p,n,WAIT tk) (p,n,WAIT tk)"
  | exit_wait: "p!tk \<Longrightarrow> cstep_sng (p,n,WAIT tk) (p,n,HOLD tk)"
  | start_release: "cstep_sng (p,n,HOLD tk) (p[tk:=False],n,REL tk)"
  | release: "cstep_sng (p,n,REL tk) (p[(tk+1) mod N := True],n,INIT)"

  text \<open>The step relation of the system, labeled with the thread \<open>t\<close> that performs the step\<close>
  inductive clstep for t where
    "\<lbrakk> t<N; cstep_sng (c,n,ts t) (c',n',s') \<rbrakk> 
      \<Longrightarrow> clstep t (c,n,ts) (c',n',ts(t:=s'))"
  
  text \<open>Initial state of the system\<close>
  definition "cs\<^sub>0 \<equiv> ((replicate N False)[0:=True], 0, \<lambda>_. INIT)"
  
  interpretation C: system cs\<^sub>0 clstep .
        
  lemma c_never_blocked: "C.can_step l s \<longleftrightarrow> l<N"
    apply (cases s; cases "tts s l"; simp)
    unfolding C.can_step_def
    apply (clarsimp_all simp: clstep.simps cstep_sng.simps)
    by metis
  
  interpretation C: df_system cs\<^sub>0 clstep 
    apply unfold_locales
    subgoal for s
      using c_never_blocked[of 0 s]
      unfolding C.can_step_def
      by auto
    done
  
  text \<open>We establish another invariant that states that the ticket numbers are bounded.\<close>  
  definition "invar4 
    \<equiv> \<lambda>(c,n,ts). c<N \<and> (\<forall>t<N. \<forall>tk. has_ticket (ts t) tk \<longrightarrow> tk<N)"
  
  lemma is_invar4: "B.is_invar invar4"
    apply (rule)
    subgoal by (auto simp: invar4_def bs\<^sub>0_def)
    subgoal for s s'
      apply clarify
      apply (erule blstep.cases, erule bstep_sng.cases)
      unfolding invar4_def
      apply safe
      apply (metis N_gt0 fun_upd_other fun_upd_same mod_mod_trivial 
        nat_mod_lem has_ticket_simps(2))
        apply (metis fun_upd_triv)
        apply (metis fun_upd_other fun_upd_same has_ticket_simps(3))
        apply (metis fun_upd_other fun_upd_same has_ticket_def has_ticket_simps(4))
        using mod_less_divisor apply blast  
        apply (metis fun_upd_apply thread.distinct(1) thread.distinct(3) 
          thread.distinct(5) has_ticket_def) 
      done
    done  
    
  text \<open>We define a predicate that describes that
    a thread of the system is at the release sequence point --- in this case,
    the array does not have a set bit, otherwise, the set bit corresponds to the 
    current ticket.\<close>
      
  definition "is_REL_state \<equiv> \<lambda>ts. \<exists>t<N. \<exists>tk. ts t = REL tk"  
    
  lemma is_REL_state_simps[simp]:
    "t<N \<Longrightarrow> is_REL_state (ts(t:=REL tk))"
    "t<N \<Longrightarrow> \<not>is_REL (ts t) \<Longrightarrow> \<not>is_REL s' 
      \<Longrightarrow> is_REL_state (ts(t:=s')) \<longleftrightarrow> is_REL_state ts"
    unfolding is_REL_state_def
    apply (auto; fail) []
    apply auto []
    by (metis thread.disc(12))
  
  lemma is_REL_state_aux1:  
    assumes R: "B.reachable (c,n,ts)"
    assumes REL: "is_REL_state ts"
    assumes "t<N" and [simp]: "ts t = WAIT tk"
    shows "tk\<noteq>c"
    using REL unfolding is_REL_state_def
    apply clarify
    subgoal for t' tk'
      using b_has_ticket_unique[OF R \<open>t<N\<close>, of tk t']
      using b_holds_only_current[OF R, of t' tk']
      by (auto)
    done
  
  lemma is_REL_state_aux2:
    assumes R: "B.reachable (c,n,ts)"
    assumes A: "t<N" "ts t = REL tk"
    shows "\<not>is_REL_state (ts(t:=INIT))"
    using b_holds_only_current[OF R] A
    using b_mutual_exclusion'[OF R]
    apply (clarsimp simp: is_REL_state_def)
    by fastforce
    

  text \<open>Simulation relation that implements current ticket by array\<close>      
  definition "sim_rel2 \<equiv> \<lambda>(c,n,ts) (ci,ni,tsi). 
    (if is_REL_state ts then 
      ci = replicate N False 
    else   
      ci = (replicate N False)[c:=True]
    )
  \<and> ni = n
  \<and> tsi = ts
  "
  
  interpretation sim2: simulationI bs\<^sub>0 blstep cs\<^sub>0 clstep sim_rel2
  proof unfold_locales
    show "sim_rel2 bs\<^sub>0 cs\<^sub>0"
      by (auto simp: sim_rel2_def bs\<^sub>0_def cs\<^sub>0_def is_REL_state_def)
  next
    fix bs cs t cs'  
    assume Rc_aux: "B.reachable bs" 
       and Rd_aux: "C.reachable cs" 
       and SIM: "sim_rel2 bs cs" 
       and CS: "clstep t cs cs'"
  
    obtain c n ts where [simp]: "bs=(c,n,ts)" by (cases bs)
    obtain ci ni tsi where [simp]: "cs=(ci,ni,tsi)" by (cases cs)
    obtain ci' ni' tsi' where [simp]: "cs'=(ci',ni',tsi')" by (cases cs')
    from Rc_aux have Rc: "B.reachable (c,n,ts)" by simp
    from Rd_aux have Rd: "C.reachable (ci,ni,tsi)" by simp
       
    from CS have "t<N" by cases auto
  
    have [simp]: "tk<N" if "ts t = WAIT tk" for tk
      using B.invar_reachable[OF is_invar4 Rc] that \<open>t<N\<close> 
      by (auto simp: invar4_def)
    have HOLD_AUX: "tk=c" if "ts t = HOLD tk" for tk
      using b_holds_only_current[OF Rc \<open>t<N\<close>, of tk] that by auto
    have REL_AUX: "tk=c" if "ts t = REL tk" "t<N" for t tk
      using b_holds_only_current[OF Rc \<open>t<N\<close>, of tk] that by auto
      
    have [simp]: "c<N" using B.invar_reachable[OF is_invar4 Rc] 
      by (auto simp: invar4_def)
      
    have [simp]: 
      "replicate N False \<noteq> (replicate N False)[c := True]"  
      "(replicate N False)[c := True] \<noteq> replicate N False"  
      apply (auto simp: list_eq_iff_nth_eq nth_list_update) 
      using \<open>c < N\<close> by blast+
    
    have [simp]:
      "(replicate N False)[c := True] ! d \<longleftrightarrow> d=c" if "d<N" for d
      using that
      by (auto simp: list_eq_iff_nth_eq nth_list_update) 
      
    have [simp]: "(replicate N False)[tk := False] = replicate N False" for tk
      by (auto simp: list_eq_iff_nth_eq nth_list_update') 
      
    from SIM CS have "\<exists>bs'. blstep t bs bs' \<and> sim_rel2 bs' cs'"
      apply simp
      apply (subst (asm) sim_rel2_def)
      apply (erule clstep.cases)
      apply (erule cstep_sng.cases)
      apply clarsimp_all
      subgoal 
        apply (intro exI conjI)
        apply (rule blstep.intros)
        apply (simp)
        apply clarsimp
        apply (rule bstep_sng.enter_wait)
        apply (auto simp: sim_rel2_def split: if_splits)
        done
      subgoal for tk'
        apply (intro exI conjI)
        apply (rule blstep.intros)
        apply (simp)
        apply clarsimp
        apply (rule bstep_sng.loop_wait)
        subgoal
          apply (clarsimp simp: sim_rel2_def split: if_splits)
          apply (frule (2) is_REL_state_aux1[OF Rc])
          by simp
        subgoal by (auto simp: sim_rel2_def split: if_splits)
        done  
      subgoal 
        apply (intro exI conjI)
        apply (rule blstep.intros)
        apply (simp)
        apply (clarsimp split: if_splits)
        apply (rule bstep_sng.exit_wait)
        apply (auto simp: sim_rel2_def split: if_splits)
        done
      subgoal 
        apply (intro exI conjI)
        apply (rule blstep.intros)
        apply (simp)
        apply clarsimp
        apply (rule bstep_sng.start_release)
        apply (auto simp: sim_rel2_def dest: HOLD_AUX split: if_splits)
        done
      subgoal 
        apply (intro exI conjI)
        apply (rule blstep.intros)
        apply (simp)
        apply clarsimp
        apply (rule bstep_sng.release)
        apply (auto 
          simp: sim_rel2_def 
          dest: is_REL_state_aux2[OF Rc] 
          split: if_splits)
        by (metis fun_upd_triv is_REL_state_simps(1))
      done
      then show "\<exists>bs'. sim_rel2 bs' cs' \<and> blstep t bs bs'" by blast
      
  next  
    fix bs cs l
    assume "B.reachable bs" "C.reachable cs" "sim_rel2 bs cs" "B.can_step l bs"
    then show "C.can_step l cs" using c_never_blocked b_never_blocked by simp
  qed        

subsection \<open>Transfer Setup\<close>
  text \<open>We set up the final simulation relation, and the transfer of the 
    concepts used in the correctness statements. \<close>
  
  definition "sim_rel \<equiv> sim_rel1 OO sim_rel2"
  interpretation sim: simulation as\<^sub>0 alstep cs\<^sub>0 clstep sim_rel
    unfolding sim_rel_def
    by (rule sim_trans) unfold_locales
  

  lemma xfer_holds:
    assumes "sim_rel s cs"
    shows "is_HOLD (tts cs t) \<longleftrightarrow> is_HOLD (tts s t)" 
    using assms unfolding sim_rel_def sim_rel1_def sim_rel2_def
    by (cases "tts cs t") auto

  lemma xfer_waits:
    assumes "sim_rel s cs"
    shows "is_WAIT (tts cs t) \<longleftrightarrow> is_WAIT (tts s t)" 
    using assms unfolding sim_rel_def sim_rel1_def sim_rel2_def 
    by (cases "tts cs t") auto
    
  lemma xfer_init:
    assumes "sim_rel s cs"  
    shows "tts cs t = INIT \<longleftrightarrow> tts s t = INIT"
    using assms unfolding sim_rel_def sim_rel1_def sim_rel2_def 
    by auto
  
subsection \<open>Main Theorems\<close> text_raw \<open>\label{sec:main_theorems}\<close> 

  subsubsection \<open>Trusted Code Base\<close>
  text \<open>  
    Note that the trusted code base for these theorems is only the 
    formalization of the concrete system as defined in Section~\ref{sec:refine3}. 
    The simulation setup and the 
    abstract systems are only auxiliary constructions for the proof.
    
    For completeness, we display the relevant definitions of
    reachability, runs, and fairness here:
    
    @{lemma [display, source] "C.step s s' = (\<exists>l. clstep l s s')" by simp}
    @{thm [display] C.reachable_def[no_vars] C.run_definitions[no_vars]}
  \<close>
  
  
  subsubsection \<open>Safety\<close>
  text \<open>We show that there is no reachable state in which two different 
    threads hold the lock.\<close>
  (* ALWAYS (NOT (HOLD ** HOLD)) *)
  theorem final_mutual_exclusion: "\<lbrakk>C.reachable s; 
      t<N; t'<N; t\<noteq>t'; is_HOLD (tts s t); is_HOLD (tts s t')
    \<rbrakk> \<Longrightarrow> False" 
    apply (erule sim.xfer_reachable)
    apply (simp add: xfer_holds)
    by (erule (5) mutual_exclusion)

  subsubsection \<open>Fairness\<close>
  text \<open>We show that, whenever a thread \<open>t\<close> draws a ticket, all other 
    threads \<open>t'\<close> waiting for the lock will be granted the lock before \<open>t\<close>. \<close>  
    
  (* ALWAYS (INIT t\<^sub>1 \<and> WAIT t\<^sub>2 \<and> X (WAIT t\<^sub>1) \<longrightarrow> HOLD t\<^sub>2 BEFORE HOLD t\<^sub>1 ) *)  
  theorem final_fair:
    assumes RUN: "C.is_run s"
    assumes ACQ: "t<N" and "tts (s i) t=INIT" and "is_WAIT (tts (s (Suc i)) t)" 
      \<comment> \<open>Thread \<open>t\<close> draws ticket in step \<open>i\<close>\<close>
    assumes HOLD: "i<j" and "is_HOLD (tts (s j) t)" 
      \<comment> \<open>Thread \<open>t\<close> holds lock in step \<open>j\<close>\<close>
    assumes WAIT: "t'<N" and "is_WAIT (tts (s i) t')" 
      \<comment> \<open>Thread \<open>t'\<close> waits for lock at step \<open>i\<close>\<close>
    obtains l where "i<l" and "l<j" and "is_HOLD (tts (s l) t')" 
      \<comment> \<open>Then, \<open>t'\<close> gets lock earlier\<close>
    using RUN
  proof (rule sim.xfer_run)
    fix as
    assume Ra: "A.is_run as" and SIM[rule_format]: "\<forall>i. sim_rel (as i) (s i)"
    
    note XFER = xfer_init[OF SIM] xfer_holds[OF SIM] xfer_waits[OF SIM]
    
    show ?thesis
      using assms
      apply (simp add: XFER)
      apply (erule (6) fair[OF Ra])
      apply (erule (1) that) 
      apply (simp add: XFER)
      done
  qed
    
  subsubsection \<open>Liveness\<close>
  text \<open>We show that, for a fair run, every thread that waits for the lock 
    will eventually hold the lock.\<close>
  (* ALWAYS (WAIT  \<longrightarrow> EVENTUALLY HOLD) *)  
  theorem final_progress:
    assumes FRUN: "C.is_fair_run s"
    assumes WAIT: "t<N" and "is_WAIT (tts (s i) t)"
    shows "\<exists>j>i. is_HOLD (tts (s j) t)"
    using FRUN
  proof (rule sim.xfer_fair_run)
    fix as
    assume Ra: "A.is_fair_run as" 
       and SIM[rule_format]: "\<forall>i. sim_rel (as i) (s i)"
    
    note XFER = xfer_init[OF SIM] xfer_holds[OF SIM] xfer_waits[OF SIM]
    
    show ?thesis
      using assms
      apply (simp add: XFER)
      apply (erule (1) progress[OF Ra])
      done
  qed  

end
