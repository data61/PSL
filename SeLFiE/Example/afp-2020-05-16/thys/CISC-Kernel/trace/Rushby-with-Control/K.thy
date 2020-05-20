section \<open>A generic model for separation kernels \label{sect:generic}\<close>

theory K
  imports List_Theorems Option_Binders
begin

text \<open>
{\em
  This section defines a detailed generic model of separation kernels
  called CISK (Controlled Interruptible Separation Kernel).  It
  contains a generic functional model of the behaviour of a separation kernel
  as a transition system, definitions of
  the security property and proofs that the functional model satisfies 
  security properties. It is based on Rushby's approach \cite{Rushby1992noninterference}
  for  noninterference.  For an explanation of the model, its structure and
  an overview of the proofs, we refer to the document entitled ``A New
  Theory of Intransitive Noninterference for Separation Kernels with
  Control''~\cite{Verbeek2013}.

  The structure of the model is based on locales and refinement:
  \begin{itemize}
  \item locale ``Kernel" defines a highly generic model for a kernel, with execution semantics. 
        It defines a state transition system with some extensions to the one
        used in \cite{Rushby1992noninterference}.
        The transition system defined here stores the currently active
        domain in the state, and has transitions for explicit
        context switches and interrupts and provides a notion of control.
        As each operation of the system will be split into atomic actions 
        in our model, only certain sequences of actions will correspond to a run on a
        real system. Therefore, 
        the function $run$, which applies an execution on a state and computes the resulting
        new state, is partial and defined for realistic traces only.
        Later, but not in this locale, we will define a predicate to distinguish 
        realistic traces from other traces.
        Security properties are also not part of this locale, but will
        be introduced in the locales to be described next.
  \item locale ``Separation\_Kernel" extends "Kernel" with constraints concerning non-interference.
        The theorem is only sensical for realistic traces; for unrealistic trace it will hold vacuously.
  \item locale ``Interruptible\_Separation\_Kernel" refines ``Separation\_Kernel" with interruptible action sequences.
        It defines function ``realistic\_trace'' based on these action sequences.
        Therefore, we can formulate a total run function.
  \item locale ``Controlled\_Interruptible\_Separation\_Kernel" refines ``Interruptible\_Separation\_Kernel" with abortable action sequences.
        It refines function ``control'' which now uses a generic predicate ``aborting'' and a generic function ``set\_error\_code''
        to manage aborting of action sequences.
  \end{itemize}
  }
\<close>
  
subsection \<open>K (Kernel)\<close>

text \<open>
The model makes use of the following types:
\begin{description}
\item['state\_t] A state  contains information about the resources of the system, 
                 as well as which domain is currently active.
We decided that a state does \emph{not} need to include a program stack, as in this model the actions that are executed are modelled separately. 
\item['dom\_t] A domain is an entity executing actions and making calls to the kernel. 
               This type represents the names of all domains.
               Later on, we define security policies in terms of domains. 
\item['action\_t] Actions of type 'action\_t represent atomic instructions that are executed by the kernel.
As kernel actions are assumed to be atomic, we assume that after each kernel action an interrupt point can occur.
\item['action\_t execution] An execution of some domain is the code or the program that is executed by the domain.
One call from a domain to the kernel will typically trigger a succession of one or more kernel actions.
Therefore, an execution is represented as a list of \emph{sequences} of kernel actions.
Non-kernel actions are not take into account. 
\item['output\_t] Given the current state and an action an output can be computed deterministically.
\item[time\_t] Time is modelled using natural numbers. Each atomic kernel action can be executed within one time unit.
\end{description}
\<close>

type_synonym ('action_t) execution = "'action_t list list"
type_synonym time_t = nat

text \<open>
  Function \emph{kstep} (for kernel step) computes the next state based on the current state $s$ and a given action $a$.
  It may assume that it makes sense to perform this action, i.e., that any precondition that is necessary for execution of action $a$ in state $s$ is met.
  If not, it may return any result. This precondition is represented by generic predicate \emph{kprecondition} (for kernel precondition).
  Only realistic traces are considered. Predicate \emph{realistic\_execution} decides whether a given execution is realistic.
  
  Function \emph{current} returns given the state the domain that is currently executing actions. The model assumes a single-core setting, i.e., at all times only one domain is active.
  Interrupt behavior is modelled using functions \emph{interrupt} and \emph{cswitch} (for context switch) that dictate respectively  when interrupts occur and how interrupts occur.
  Interrupts are solely time-based, meaning that there is an at beforehand fixed schedule dictating which domain is active at which time.
  
  Finally, we add function \emph{control}.
  This function represents control of the kernel over the execution as performed by the domains.
  Given the current state $s$, the currently active domain $d$ and the execution $\alpha$ of that domain,
  it returns three objects.
  First, it returns the next action that domain $d$ will perform. Commonly, this is the next action in execution $\alpha$. It may also return None, indicating that no action is done.
  Secondly, it returns the updated execution. When executing action $a$, typically, this action will be removed from the current execution (i.e., updating the program stack).
  Thirdly, it can update the state to set, e.g., error codes.
\<close>

locale Kernel =
  fixes kstep :: "'state_t \<Rightarrow> 'action_t \<Rightarrow> 'state_t"
    and output_f :: "'state_t \<Rightarrow> 'action_t \<Rightarrow> 'output_t"
    and s0 :: 'state_t
    and current :: "'state_t => 'dom_t" (* "Returns the currently active domain"*)
    and cswitch :: "time_t \<Rightarrow> 'state_t \<Rightarrow> 'state_t" (* "Switches the current domain" *)
    and interrupt :: "time_t \<Rightarrow> bool" (* "Returns t iff an interrupt occurs in the given state at the given time"*)
    and kprecondition :: "'state_t \<Rightarrow> 'action_t \<Rightarrow> bool" (* "Returns t if an precondition holds that relates the current action to the state" *)
    and realistic_execution :: "'action_t execution \<Rightarrow> bool" (* "In this locale, this function is completely unconstrained." *)
    and control :: "'state_t \<Rightarrow> 'dom_t \<Rightarrow> 'action_t execution \<Rightarrow>
                              (('action_t option) \<times> 'action_t execution \<times> 'state_t)" 
    and kinvolved :: "'action_t \<Rightarrow> 'dom_t set"
begin

subsubsection \<open>Execution semantics\<close>

text \<open>
  Short hand notations for using function control.
\<close>
definition next_action::"'state_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> 'action_t option"
where "next_action s execs = fst (control s (current s) (execs (current s)))"
definition next_execs::"'state_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution)"
where "next_execs s execs = (fun_upd execs (current s) (fst (snd (control s  (current s) (execs (current s))))))"
definition next_state::"'state_t \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> 'state_t"
where "next_state s execs = snd (snd (control s  (current s) (execs (current s))))"

text \<open>
  A thread is empty iff either it has no further action sequences to execute, or when the current action sequence is finished and there are no further action sequences to execute.
\<close>
abbreviation thread_empty::"'action_t execution \<Rightarrow> bool"
where "thread_empty exec \<equiv> exec = [] \<or> exec = [[]]"

text \<open>
  Wrappers for function kstep and kprecondition that deal with the case where the given action is None.
\<close>
definition step where "step s oa \<equiv> case oa of None \<Rightarrow> s | (Some a) \<Rightarrow> kstep s a"
definition precondition :: "'state_t \<Rightarrow> 'action_t option \<Rightarrow> bool"
where "precondition s a \<equiv> a \<rightharpoonup> kprecondition s"
definition involved
where "involved oa \<equiv> case oa of None \<Rightarrow> {} | (Some a) \<Rightarrow> kinvolved a"


text \<open>
  Execution semantics are defined as follows: a run consists of consecutively running sequences of actions.
  These sequences are interruptable.
  Run first checks whether an interrupt occurs.
  When this happens, function cswitch may switch the context.
  Otherwise, function control is used to determine the next action $a$, which also yields a new state $s'$.
  Action $a$ is executed by executing (step $s'$ $a$).
  The current execution of the current domain is updated. 
  
  Note that run is a partial function, i.e., it computes results only when at all times the preconditions hold.
  Such runs are the realistic ones. For other runs, we do not need to -- and cannot -- prove security.
  All the theorems are formulated in such a way that they hold vacuously for unrealistic runs.
\<close> 
function run :: "time_t \<Rightarrow> 'state_t option \<Rightarrow> ('dom_t \<Rightarrow> 'action_t execution) \<Rightarrow> 'state_t option"
where "run 0 s execs = s"
| "run (Suc n) None execs = None"
| "interrupt (Suc n) \<Longrightarrow> run (Suc n) (Some s) execs = run n (Some (cswitch (Suc n) s)) execs"
| "\<not>interrupt (Suc n) \<Longrightarrow> thread_empty(execs (current s)) \<Longrightarrow> run (Suc n) (Some s) execs = run n (Some s) execs"
| "\<not>interrupt (Suc n) \<Longrightarrow> \<not>thread_empty(execs (current s)) \<Longrightarrow> \<not>precondition (next_state s execs) (next_action s execs) \<Longrightarrow> run (Suc n) (Some s) execs = None"
| "\<not>interrupt (Suc n) \<Longrightarrow> \<not>thread_empty(execs (current s)) \<Longrightarrow> precondition (next_state s execs) (next_action s execs) \<Longrightarrow>
      run (Suc n) (Some s) execs = run n (Some (step (next_state s execs)  (next_action s execs))) (next_execs s execs)"
using not0_implies_Suc by (metis option.exhaust prod_cases3,auto) 
termination by lexicographic_order
end


end
