subsection \<open>Separation kernel state and atomic step function\<close>

theory Step
  imports Step_policies
begin


subsubsection \<open>Interrupt points\<close>

text \<open>To model concurrency, each system call is split into several atomic steps,
        while allowing interrupts between the steps. The state of a thread is
        represented by an ``interrupt point" (which corresponds to the value of the program counter
        saved by the system when a thread is interrupted).\<close>

datatype ipc_direction_t = SEND | RECV
datatype ipc_stage_t = PREP | WAIT | BUF page_t

datatype ev_consume_t = EV_CONSUME_ALL | EV_CONSUME_ONE
datatype ev_wait_stage_t = EV_PREP | EV_WAIT | EV_FINISH
datatype ev_signal_stage_t = EV_SIGNAL_PREP | EV_SIGNAL_FINISH

datatype int_point_t =
   SK_IPC ipc_direction_t ipc_stage_t thread_id_t page_t \<comment> \<open>The thread is executing a sending / receiving IPC.\<close>
 | SK_EV_WAIT ev_wait_stage_t ev_consume_t \<comment> \<open>The thread is waiting for an event.\<close>
 | SK_EV_SIGNAL ev_signal_stage_t thread_id_t \<comment> \<open>The thread is sending an event.\<close>
 | NONE \<comment> \<open>The thread is not executing any system call.\<close>

subsubsection \<open>System state\<close>

typedecl obj_t \<comment> \<open>value of an object\<close>

text \<open>Each thread belongs to a partition. The relation is fixed (in this instantiation of a separation kernel).\<close>

consts
  partition :: "thread_id_t \<Rightarrow> partition_id_t"

text \<open>The state contains the dynamic policy (the communication rights in the current state
  of the system, for example).\<close>

record thread_t =
  (* 
  id :: thread_id_t           -- {* thread identifier *}
  int_point :: int_point_t    -- {* interrupt point *}*)
  ev_counter :: nat           \<comment> \<open>event counter\<close>
  
record state_t =  
  sp_impl_subj_subj :: sp_subj_subj_t    \<comment> \<open>current subject-subject policy\<close>
  sp_impl_subj_obj :: sp_subj_obj_t      \<comment> \<open>current subject-object policy\<close>
  current :: "thread_id_t"               \<comment> \<open>current thread\<close>
  obj :: "obj_id_t \<Rightarrow> obj_t"             \<comment> \<open>values of all objects\<close>
  thread :: "thread_id_t \<Rightarrow> thread_t"    \<comment> \<open>internal state of threads\<close>

text \<open>Later (Section~\ref{sect:step_invariants}), the system invariant @{term sp_subset} will be used to ensure that the dynamic policies (sp\_impl\_...)
are a subset of the corresponding static policies (sp\_spec\_...).\<close>

subsubsection \<open>Atomic step\<close>

text_raw \<open>\paragraph{Helper functions}\<close>

text \<open>Set new value for an object.\<close>

definition set_object_value :: "obj_id_t \<Rightarrow> obj_t \<Rightarrow> state_t \<Rightarrow> state_t" where
  "set_object_value obj_id val s =
    s \<lparr> obj := fun_upd (obj s) obj_id val \<rparr>"

text \<open>Return a representation of the opposite direction of IPC communication.\<close>

definition opposite_ipc_direction :: "ipc_direction_t \<Rightarrow> ipc_direction_t" where
  "opposite_ipc_direction dir \<equiv> case dir of SEND \<Rightarrow> RECV | RECV \<Rightarrow> SEND"

text \<open>Add an access right from one partition to an object. In this model, not 
available from the API, but shows how dynamic changes of access rights could be implemented.\<close>

definition add_access_right :: "partition_id_t => obj_id_t => mode_t => state_t => state_t" where
  "add_access_right part_id obj_id m s = 
    s \<lparr> sp_impl_subj_obj := \<lambda> q q' q''. (part_id = q \<and> obj_id = q' \<and> m = q'') 
     \<or> sp_impl_subj_obj s q q' q''\<rparr>"

text \<open>Add a communication right from one partition to another. In this model, not
available from the API.\<close>

definition add_comm_right :: "partition_id_t \<Rightarrow> partition_id_t \<Rightarrow> state_t \<Rightarrow> state_t" where
  "add_comm_right p p' s \<equiv>
    s \<lparr> sp_impl_subj_subj := \<lambda> q q' . (p = q \<and> p' = q') \<or> sp_impl_subj_subj s q q' \<rparr>"

text_raw \<open>\paragraph{Model of IPC system call}\<close>

text \<open>We model IPC with the following simplifications:

\begin{enumerate}
\item The model contains the system calls for sending 
      an IPC (SEND) and receiving an IPC (RECV), often implementations
      have a richer API (e.g. combining SEND and RECV in one invocation). 
\item We model only a copying (``BUF") mode, not a memory-mapping mode.
\item The model always copies one page per syscall.
\end{enumerate}
\<close>

definition ipc_precondition :: "thread_id_t \<Rightarrow> ipc_direction_t \<Rightarrow> thread_id_t \<Rightarrow> page_t \<Rightarrow> state_t \<Rightarrow> bool" where
  "ipc_precondition tid dir partner page s \<equiv>
    let sender = (case dir of SEND \<Rightarrow> tid | RECV \<Rightarrow> partner) in
    let receiver = (case dir of SEND \<Rightarrow> partner | RECV \<Rightarrow> tid) in
    let local_access_mode = (case dir of SEND \<Rightarrow> READ | RECV \<Rightarrow> WRITE) in
    (sp_impl_subj_subj s (partition sender) (partition receiver)
      \<and> sp_impl_subj_obj s (partition tid) (PAGE page) local_access_mode)"

definition atomic_step_ipc :: "thread_id_t \<Rightarrow> ipc_direction_t \<Rightarrow> ipc_stage_t \<Rightarrow> thread_id_t \<Rightarrow> page_t \<Rightarrow> state_t \<Rightarrow> state_t" where
  "atomic_step_ipc tid dir stage partner page s \<equiv>
    case stage of
      PREP \<Rightarrow>
         s
    | WAIT \<Rightarrow>
         s
    | BUF page' \<Rightarrow>
       (case dir of
          SEND \<Rightarrow>
             (set_object_value (PAGE page') (obj s (PAGE page)) s)
        | RECV \<Rightarrow> s)"

text_raw \<open>\paragraph{Model of event syscalls}\<close>

(*The maximum allowed event counter*)
(* outcommented, as currently not used consts EV_CTR_MAX :: nat *)

(* Needs to be adapted, if wildcards for masks are defined *)
definition ev_signal_precondition :: "thread_id_t \<Rightarrow> thread_id_t \<Rightarrow> state_t \<Rightarrow> bool" where
 "ev_signal_precondition tid partner s \<equiv>
    (sp_impl_subj_subj s (partition tid) (partition partner))"

(* Assumes error checks have been successful:
   tid is in the event mask of the partner and
   communication rights between tid an partner have been granted *)
definition atomic_step_ev_signal :: "thread_id_t \<Rightarrow> thread_id_t \<Rightarrow> state_t \<Rightarrow> state_t" where
 "atomic_step_ev_signal tid partner s =
    s \<lparr> thread := fun_upd (thread s) partner (thread s partner \<lparr> ev_counter := Suc (ev_counter (thread s partner) ) \<rparr> )   \<rparr>"

definition atomic_step_ev_wait_one :: "thread_id_t \<Rightarrow> state_t \<Rightarrow> state_t" where
 "atomic_step_ev_wait_one tid s =
    s \<lparr> thread := fun_upd (thread s) tid (thread s tid \<lparr> ev_counter := (ev_counter (thread s tid) - 1) \<rparr> )   \<rparr>"

definition atomic_step_ev_wait_all :: "thread_id_t \<Rightarrow> state_t \<Rightarrow> state_t" where
 "atomic_step_ev_wait_all tid  s =
    s \<lparr> thread := fun_upd (thread s) tid (thread s tid \<lparr> ev_counter := 0 \<rparr> )   \<rparr>"

text_raw \<open>\paragraph{Instantiation of CISK aborting and waiting}\<close>

text \<open>
  In this instantiation of CISK, the @{term aborting} function is used to indicate security policy enforcement.
  An IPC call aborts in its @{term PREP} stage if the precondition for the calling thread does 
  not hold. An event signal call aborts in its @{term EV_SIGNAL_PREP} stage if the 
  precondition for the calling thread does not hold. 
\<close>
definition aborting :: "state_t \<Rightarrow> thread_id_t \<Rightarrow> int_point_t \<Rightarrow> bool"
where "aborting s tid a \<equiv> case a of SK_IPC dir PREP partner page \<Rightarrow>
                            \<not>ipc_precondition tid dir partner page s
                           | SK_EV_SIGNAL EV_SIGNAL_PREP partner \<Rightarrow>
                            \<not>ev_signal_precondition tid partner s
                           | _ => False"
text \<open>
  The @{term waiting} function is used to indicate synchronization.
  An IPC call waits in its @{term WAIT} stage while the precondition for the partner thread does not hold.
  An EV\_WAIT call waits until the event counter is not zero.
\<close>
definition waiting :: "state_t \<Rightarrow> thread_id_t \<Rightarrow> int_point_t \<Rightarrow> bool"
where "waiting s tid a \<equiv> 
           case a of SK_IPC dir WAIT partner page \<Rightarrow> 
                                   \<not>ipc_precondition partner (opposite_ipc_direction dir) tid (SOME page' . True) s
                   | SK_EV_WAIT EV_PREP _ \<Rightarrow> False
                   | SK_EV_WAIT EV_WAIT _ \<Rightarrow> ev_counter (thread s tid) = 0
                   | SK_EV_WAIT EV_FINISH _ \<Rightarrow> False
                   | _ \<Rightarrow> False"

text_raw \<open>\paragraph{The atomic step function.}\<close>

text \<open>In the definition of @{term atomic_step} the arguments to an interrupt point are
 not taken from the thread state -- the argument given to @{term atomic_step} could have an 
 arbitrary value.
 So, seen in isolation, @{term atomic_step} allows more transitions than actually occur in the 
 separation kernel. However, the CISK framework (1) restricts the atomic step function by
 the @{term waiting} and @{term aborting} functions as well (2) the set of realistic traces as
 attack sequences @{term rAS_set} (Section~\ref{sect:separation_kernel_model}). 
 An additional condition is that (3) the dynamic policy used in @{term aborting} 
 is a subset of the static policy. This is ensured by the invariant @{term sp_subset}.
\<close>

definition atomic_step :: "state_t \<Rightarrow> int_point_t \<Rightarrow> state_t" where
  "atomic_step s ipt \<equiv>
    case ipt of
      SK_IPC dir stage partner page \<Rightarrow>
        atomic_step_ipc (current s) dir stage partner page s
    |  SK_EV_WAIT EV_PREP consume \<Rightarrow> s
    |  SK_EV_WAIT EV_WAIT consume \<Rightarrow> s
    |  SK_EV_WAIT EV_FINISH consume \<Rightarrow>
      case consume of
          EV_CONSUME_ONE \<Rightarrow> atomic_step_ev_wait_one (current s) s   
        | EV_CONSUME_ALL \<Rightarrow> atomic_step_ev_wait_all (current s) s  
    | SK_EV_SIGNAL EV_SIGNAL_PREP partner \<Rightarrow> s
    | SK_EV_SIGNAL EV_SIGNAL_FINISH partner \<Rightarrow>
      atomic_step_ev_signal (current s) partner s
    | NONE \<Rightarrow> s"

end
