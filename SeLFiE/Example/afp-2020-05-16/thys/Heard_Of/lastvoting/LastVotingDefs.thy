theory LastVotingDefs
imports "../HOModel"
begin

section \<open>Verification of the \emph{LastVoting} Consensus Algorithm\<close>

text \<open>
  The \emph{LastVoting} algorithm can be considered as a representation of
  Lamport's Paxos consensus algorithm~\cite{lamport:part-time}
  in the Heard-Of model. It is a coordinated algorithm designed to
  tolerate benign failures. Following~\cite{charron:heardof}, we formalize
  its proof of correctness in Isabelle, using the framework of theory \<open>HOModel\<close>.
\<close>


subsection \<open>Model of the Algorithm\<close>

text \<open>
  We begin by introducing an anonymous type of processes of finite
  cardinality that will instantiate the type variable \<open>'proc\<close>
  of the generic CHO model.
\<close>

typedecl Proc \<comment> \<open>the set of processes\<close>
axiomatization where Proc_finite: "OFCLASS(Proc, finite_class)"
instance Proc :: finite by (rule Proc_finite)

abbreviation
  "N \<equiv> card (UNIV::Proc set)"   \<comment> \<open>number of processes\<close>

text \<open>
  The algorithm proceeds in \emph{phases} of $4$ rounds each (we call
  \emph{steps} the individual rounds that constitute a phase).
  The following utility functions compute the phase and step of a round,
  given the round number.
\<close>

definition phase where "phase (r::nat) \<equiv> r div 4"

definition step where "step (r::nat) \<equiv> r mod 4"

lemma phase_zero [simp]: "phase 0 = 0"
by (simp add: phase_def)

lemma step_zero [simp]: "step 0 = 0"
by (simp add: step_def)

lemma phase_step: "(phase r * 4) + step r = r"
  by (auto simp add: phase_def step_def)

text \<open>
  The following record models the local state of a process.
\<close>

record 'val pstate =
  x :: 'val                \<comment> \<open>current value held by process\<close>
  vote :: "'val option"    \<comment> \<open>value the process voted for, if any\<close>
  commt :: bool            \<comment> \<open>did the process commit to the vote?\<close>
  ready :: bool            \<comment> \<open>for coordinators: did the round finish successfully?\<close>
  timestamp :: nat         \<comment> \<open>time stamp of current value\<close>
  decide :: "'val option"  \<comment> \<open>value the process has decided on, if any\<close>
  coord\<Phi> :: Proc           \<comment> \<open>coordinator for current phase\<close>

text \<open>
  Possible messages sent during the execution of the algorithm.
\<close>

datatype 'val msg =
  ValStamp "'val" "nat"
| Vote "'val"
| Ack
| Null  \<comment> \<open>dummy message in case nothing needs to be sent\<close>

text \<open>
  Characteristic predicates on messages.
\<close>

definition isValStamp where "isValStamp m \<equiv> \<exists>v ts. m = ValStamp v ts"

definition isVote where "isVote m \<equiv> \<exists>v. m = Vote v"

definition isAck where "isAck m \<equiv> m = Ack"

text \<open>
  Selector functions to retrieve components of messages. These functions
  have a meaningful result only when the message is of an appropriate kind.
\<close>

fun val where
  "val (ValStamp v ts) = v"
| "val (Vote v) = v"

fun stamp where
  "stamp (ValStamp v ts) = ts"

text \<open>
  The \<open>x\<close> field of the initial state is unconstrained, all other
  fields are initialized appropriately.
\<close>

definition LV_initState where
  "LV_initState p st crd \<equiv>
     vote st = None
   \<and> \<not>(commt st)
   \<and> \<not>(ready st)
   \<and> timestamp st = 0
   \<and> decide st = None
   \<and> coord\<Phi> st = crd"

text \<open>
  We separately define the transition predicates and the send functions
  for each step and later combine them to define the overall next-state relation.
\<close>

\<comment> \<open>processes from which values and timestamps were received\<close>
definition valStampsRcvd where
  "valStampsRcvd (msgs :: Proc \<rightharpoonup> 'val msg) \<equiv>
   {q . \<exists>v ts. msgs q = Some (ValStamp v ts)}"

definition highestStampRcvd where
  "highestStampRcvd msgs \<equiv> 
   Max {ts . \<exists>q v. (msgs::Proc \<rightharpoonup> 'val msg) q = Some (ValStamp v ts)}"

text \<open>
  In step 0, each process sends its current \<open>x\<close> and \<open>timestamp\<close>
  values to its coordinator.

  A process that considers itself to be a coordinator updates its
  \<open>vote\<close> field if it has received messages from a majority of processes.
  It then sets its \<open>commt\<close> field to true.
\<close>

definition send0 where
  "send0 r p q st \<equiv>
   if q = coord\<Phi> st then ValStamp (x st) (timestamp st) else Null"

definition next0 where
  "next0 r p st msgs crd st' \<equiv>
      if p = coord\<Phi> st \<and> card (valStampsRcvd msgs) > N div 2
      then (\<exists>p v. msgs p = Some (ValStamp v (highestStampRcvd msgs))
                \<and> st' = st \<lparr> vote := Some v, commt := True \<rparr> )
      else st' = st"

text \<open>
  In step 1, coordinators that have committed send their vote to all
  processes.

  Processes update their \<open>x\<close> and \<open>timestamp\<close> fields if they
  have received a vote from their coordinator.
\<close>

definition send1 where
  "send1 r p q st \<equiv>
   if p = coord\<Phi> st \<and> commt st then Vote (the (vote st)) else Null"

definition next1 where
  "next1 r p st msgs crd st' \<equiv>
   if msgs (coord\<Phi> st) \<noteq> None \<and> isVote (the (msgs (coord\<Phi> st)))
   then st' = st \<lparr> x := val (the (msgs (coord\<Phi> st))), timestamp := Suc(phase r) \<rparr>
   else st' = st"

text \<open>
  In step 2, processes that have current timestamps send an acknowledgement
  to their coordinator.

  A coordinator sets its \<open>ready\<close> field to true if it receives a majority
  of acknowledgements.
\<close>

definition send2 where
  "send2 r p q st \<equiv>
   if timestamp st = Suc(phase r) \<and> q = coord\<Phi> st then Ack else Null"

\<comment> \<open>processes from which an acknowledgement was received\<close>
definition acksRcvd where
  "acksRcvd (msgs :: Proc \<rightharpoonup> 'val msg) \<equiv>
   { q . msgs q \<noteq> None \<and> isAck (the (msgs q)) }"

definition next2 where
  "next2 r p st msgs crd st' \<equiv>
   if p = coord\<Phi> st \<and> card (acksRcvd msgs) > N div 2
   then st' = st \<lparr> ready := True \<rparr>
   else st' = st"

text \<open>
  In step 3, coordinators that are ready send their vote to all processes.

  Processes that received a vote from their coordinator decide on that value.
  Coordinators reset their \<open>ready\<close> and \<open>commt\<close> fields to false.
  All processes reset the coordinators as indicated by the parameter of
  the operator.
\<close>

definition send3 where
  "send3 r p q st \<equiv>
   if p = coord\<Phi> st \<and> ready st then Vote (the (vote st)) else Null"

definition next3 where
  "next3 r p st msgs crd st' \<equiv>
      (if msgs (coord\<Phi> st) \<noteq> None \<and> isVote (the (msgs (coord\<Phi> st)))
       then decide st' = Some (val (the (msgs (coord\<Phi> st))))
       else decide st' = decide st)
   \<and> (if p = coord\<Phi> st
      then \<not>(ready st') \<and> \<not>(commt st')
      else ready st' = ready st \<and> commt st' = commt st)
   \<and> x st' = x st
   \<and> vote st' = vote st
   \<and> timestamp st' = timestamp st
   \<and> coord\<Phi> st' = crd"

text \<open>
  The overall send function and next-state relation are simply obtained as
  the composition of the individual relations defined above.
\<close>

definition LV_sendMsg :: "nat \<Rightarrow> Proc \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> 'val msg" where
  "LV_sendMsg (r::nat) \<equiv>
   if step r = 0 then send0 r
   else if step r = 1 then send1 r
   else if step r = 2 then send2 r
   else send3 r"


definition
  LV_nextState :: "nat \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> (Proc \<rightharpoonup> 'val msg) 
                       \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> bool"
  where
  "LV_nextState r \<equiv>
   if step r = 0 then next0 r
   else if step r = 1 then next1 r
   else if step r = 2 then next2 r
   else next3 r"


subsection \<open>Communication Predicate for \emph{LastVoting}\<close>

text \<open>
  We now define the communication predicate that will be assumed for the
  correctness proof of the \emph{LastVoting} algorithm.
  The ``per-round'' part is trivial: integrity and agreement are always ensured.

  For the ``global'' part, Charron-Bost and Schiper propose a predicate
  that requires the existence of infinitely many phases \<open>ph\<close> such that:
  \begin{itemize}
  \item all processes agree on the same coordinator \<open>c\<close>,
  \item \<open>c\<close> hears from a strict majority of processes in steps 0 and 2
    of phase \<open>ph\<close>, and
  \item every process hears from \<open>c\<close> in steps 1 and 3 (this is slightly
    weaker than the predicate that appears in~\cite{charron:heardof}, but
    obviously sufficient).
  \end{itemize}

  Instead of requiring infinitely many such phases, we only assume the
  existence of one such phase (Charron-Bost and Schiper note that this is enough.)
\<close>

definition
  LV_commPerRd where
  "LV_commPerRd r (HO::Proc HO) (coord::Proc coord) \<equiv> True"

definition
  LV_commGlobal where
  "LV_commGlobal HOs coords \<equiv>
      \<exists>ph::nat. \<exists>c::Proc.
           (\<forall>p. coords (4*ph) p = c)
         \<and> card (HOs (4*ph) c) > N div 2
         \<and> card (HOs (4*ph+2) c) > N div 2
         \<and> (\<forall>p. c \<in> HOs (4*ph+1) p \<inter> HOs (4*ph+3) p)"


subsection \<open>The \emph{LastVoting} Heard-Of Machine\<close>

text \<open>
  We now define the coordinated HO machine for the \emph{LastVoting} algorithm
  by assembling the algorithm definition and its communication-predicate.
\<close>

definition LV_CHOMachine where
  "LV_CHOMachine \<equiv>
    \<lparr> CinitState = LV_initState,
      sendMsg = LV_sendMsg,
      CnextState = LV_nextState,
      CHOcommPerRd = LV_commPerRd,
      CHOcommGlobal = LV_commGlobal \<rparr>"

abbreviation 
  "LV_M \<equiv> (LV_CHOMachine::(Proc, 'val pstate, 'val msg) CHOMachine)"

end
