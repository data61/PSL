section \<open>The Paxos Algorithm\<close>

theory Paxos_Defs
imports Heard_Of.HOModel "../Consensus_Types" "../Consensus_Misc" Three_Steps
begin

text \<open>
  This is a modified version (closer to the original Paxos) of PaxosDefs from the Heard Of 
  entry in the AFP.\<close>

subsection \<open>Model of the algorithm\<close>

text \<open>
  The following record models the local state of a process.
\<close>

record 'val pstate =
  x :: 'val                \<comment> \<open>current value held by process\<close>
  mru_vote :: "(nat \<times> 'val) option"
  commt :: "'val option"   \<comment> \<open>for coordinators: the value processes are asked to commit to\<close>
  decide :: "'val option"  \<comment> \<open>value the process has decided on, if any\<close>

text \<open>The algorithm relies on a coordinator for each phase of the algorithm.
  A phase lasts three rounds. The HO model formalization already provides the 
  infrastructure for this, but unfortunately the coordinator is not passed to
  the @{term sendMsg} function. Using the infrastructure would thus require 
  additional invariants and proofs; for simplicity, we use a global 
  constant instead.\<close>

consts coord :: "nat \<Rightarrow> process"
specification (coord)
  coord_phase[rule_format]: "\<forall>r r'. three_phase r = three_phase r' \<longrightarrow> coord r = coord r'"
  by(auto)

text \<open>
  Possible messages sent during the execution of the algorithm.
\<close>

datatype 'val msg =
  ValStamp "'val" "nat"
| NeverVoted
| Vote "'val"
| Null  \<comment> \<open>dummy message in case nothing needs to be sent\<close>

text \<open>
  Characteristic predicates on messages.
\<close>

definition isValStamp where "isValStamp m \<equiv> \<exists>v ts. m = ValStamp v ts"

definition isVote where "isVote m \<equiv> \<exists>v. m = Vote v"

text \<open>
  Selector functions to retrieve components of messages. These functions
  have a meaningful result only when the message is of an appropriate kind.
\<close>

fun val where
  "val (ValStamp v ts) = v"
| "val (Vote v) = v"

text \<open>
  The \<open>x\<close> field of the initial state is unconstrained, all other
  fields are initialized appropriately.
\<close>

definition Paxos_initState where
  "Paxos_initState p st crd \<equiv>
   mru_vote st = None
   \<and> commt st = None
   \<and> decide st = None
  "

definition mru_vote_to_msg :: "'val pstate \<Rightarrow> 'val msg" where
  "mru_vote_to_msg st \<equiv> case mru_vote st of
    Some (ts, v) \<Rightarrow> ValStamp v ts
    | None \<Rightarrow> NeverVoted"

fun msg_to_val_stamp :: "'val msg \<Rightarrow> (round \<times> 'val)option" where
  "msg_to_val_stamp (ValStamp v ts) = Some (ts, v)"
  | "msg_to_val_stamp _ = None"

definition msgs_to_lvs ::
  "(process \<rightharpoonup> 'val msg)
  \<Rightarrow> (process, round \<times> 'val) map"
where
  "msgs_to_lvs msgs \<equiv> msg_to_val_stamp \<circ>\<^sub>m msgs"

definition send0 where
  "send0 r p q st \<equiv>
   if q = coord r then mru_vote_to_msg st else Null"

definition next0 
  :: "nat 
  \<Rightarrow> process 
  \<Rightarrow> 'val pstate 
  \<Rightarrow> (process \<rightharpoonup> 'val msg)
  \<Rightarrow> process
  \<Rightarrow> 'val pstate
  \<Rightarrow> bool"
where
  "next0 r p st msgs crd st' \<equiv> let Q = dom msgs; lvs = msgs_to_lvs msgs in
      if p = coord r \<and> card Q > N div 2
      then (st' = st \<lparr> commt := Some (case_option (x st) snd (option_Max_by fst (ran (lvs |` Q)))) \<rparr> )
      else st' = st\<lparr> commt := None \<rparr>"

definition send1 where
  "send1 r p q st \<equiv>
   if p = coord r \<and> commt st \<noteq> None then Vote (the (commt st)) else Null"

definition next1 
  :: "nat 
  \<Rightarrow> process 
  \<Rightarrow> 'val pstate 
  \<Rightarrow> (process \<rightharpoonup> 'val msg)
  \<Rightarrow> process
  \<Rightarrow> 'val pstate
  \<Rightarrow> bool"
where
  "next1 r p st msgs crd st' \<equiv>
   if msgs (coord r) \<noteq> None \<and> isVote (the (msgs (coord r)))
   then st' = st \<lparr> mru_vote := Some (three_phase r, val (the (msgs (coord r))))  \<rparr>
   else st' = st"

definition send2 where
  "send2 r p q st \<equiv> (case mru_vote st of
    Some (phs, v) \<Rightarrow> (if phs = three_phase r then Vote v else Null)
    | _ \<Rightarrow> Null
  )"

\<comment> \<open>processes from which a vote was received\<close>
definition votes_rcvd where
  "votes_rcvd (msgs :: process \<rightharpoonup> 'val msg) \<equiv>
   { (q, v) . msgs q = Some (Vote v) }"

definition the_rcvd_vote where
  "the_rcvd_vote (msgs :: process \<rightharpoonup> 'val msg) \<equiv> SOME v. v \<in> snd ` votes_rcvd msgs"

definition next2 where
  "next2 r p st msgs crd st' \<equiv>
   if card (votes_rcvd msgs) > N div 2
   then st' = st \<lparr> decide := Some (the_rcvd_vote msgs) \<rparr>
   else st' = st
 "

text \<open>
  The overall send function and next-state relation are simply obtained as
  the composition of the individual relations defined above.
\<close>

definition Paxos_sendMsg :: "nat \<Rightarrow> process \<Rightarrow> process \<Rightarrow> 'val pstate \<Rightarrow> 'val msg" where
  "Paxos_sendMsg (r::nat) \<equiv>
   if three_step r = 0 then send0 r
   else if three_step r = 1 then send1 r
   else send2 r"

definition
  Paxos_nextState :: "nat \<Rightarrow> process \<Rightarrow> 'val pstate \<Rightarrow> (process \<rightharpoonup> 'val msg) 
                       \<Rightarrow> process \<Rightarrow> 'val pstate \<Rightarrow> bool"
  where
  "Paxos_nextState r \<equiv>
   if three_step r = 0 then next0 r
   else if three_step r = 1 then next1 r
   else next2 r"

definition
  Paxos_commPerRd where
  "Paxos_commPerRd r (HO::process HO) (crd::process coord) \<equiv> True"

definition
  Paxos_commGlobal where
  "Paxos_commGlobal HOs coords \<equiv>
      \<exists>ph::nat. \<exists>c::process.
           coord (nr_steps*ph) = c
         \<and> card (HOs (nr_steps*ph) c) > N div 2
         \<and> (\<forall>p. c \<in> HOs (nr_steps*ph+1) p)
         \<and> (\<forall>p. card (HOs (nr_steps*ph+2) p) > N div 2)"

subsection \<open>The \emph{Paxos} Heard-Of machine\<close>

text \<open>
  We now define the coordinated HO machine for the \emph{Paxos} algorithm
  by assembling the algorithm definition and its communication-predicate.
\<close>

definition Paxos_Alg where
  "Paxos_Alg \<equiv>
    \<lparr> CinitState = Paxos_initState,
      sendMsg = Paxos_sendMsg,
      CnextState = Paxos_nextState \<rparr>"

definition Paxos_CHOMachine where
  "Paxos_CHOMachine \<equiv>
    \<lparr> CinitState = Paxos_initState,
      sendMsg = Paxos_sendMsg,
      CnextState = Paxos_nextState,
      CHOcommPerRd = Paxos_commPerRd,
      CHOcommGlobal = Paxos_commGlobal \<rparr>"

abbreviation 
  "Paxos_M \<equiv> (Paxos_CHOMachine::(process, 'val pstate, 'val msg) CHOMachine)"

end
