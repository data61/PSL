section \<open>The UniformVoting Algorithm\<close>
theory Uv_Defs
imports Heard_Of.HOModel "../Consensus_Types" "../Quorums"
begin

text \<open>The contents of this file have been taken almost verbatim from the
  Heard Of Model AFP entry. The only difference is that the types have been
  changed.\<close>

subsection \<open>Model of the algorithm\<close>

abbreviation "nSteps \<equiv> 2"

definition phase where "phase (r::nat) \<equiv> r div nSteps"

definition step where "step (r::nat) \<equiv> r mod nSteps"

text \<open>
  The following record models the local state of a process.
\<close>

record 'val pstate =
  last_obs :: 'val                \<comment> \<open>current value held by process\<close>
  agreed_vote :: "'val option"    \<comment> \<open>value the process voted for, if any\<close>
  decide :: "'val option"  \<comment> \<open>value the process has decided on, if any\<close>

text \<open>
  Possible messages sent during the execution of the algorithm, and characteristic
  predicates to distinguish types of messages.
\<close>

datatype 'val msg =
  Val 'val
| ValVote 'val "'val option"
| Null  \<comment> \<open>dummy message in case nothing needs to be sent\<close>

definition isValVote where "isValVote m \<equiv> \<exists>z v. m = ValVote z v"

definition isVal where "isVal m \<equiv> \<exists>v. m = Val v"

text \<open>
  Selector functions to retrieve components of messages. These functions
  have a meaningful result only when the message is of appropriate kind.
\<close>

fun getvote where
  "getvote (ValVote z v) = v"

fun getval where
  "getval (ValVote z v) = z"
| "getval (Val z) = z"


definition UV_initState where
  "UV_initState p st \<equiv> (agreed_vote st = None) \<and> (decide st = None)"

text \<open>
  We separately define the transition predicates and the send functions
  for each step and later combine them to define the overall next-state relation.
\<close>

definition msgRcvd where  \<comment> \<open>processes from which some message was received\<close>
  "msgRcvd (msgs:: process \<rightharpoonup> 'val msg) = {q . msgs q \<noteq> None}"

definition smallestValRcvd where
  "smallestValRcvd (msgs::process \<rightharpoonup> ('val::linorder) msg) \<equiv>
   Min {v. \<exists>q. msgs q = Some (Val v)}"

text \<open>
  In step 0, each process sends its current \<open>last_obs\<close> value.

  It updates its \<open>last_obs\<close> field to the smallest value it has received.
  If the process has received the same value \<open>v\<close> from all processes
  from which it has heard, it updates its \<open>agreed_vote\<close> field to \<open>v\<close>.
\<close>

definition send0 where
  "send0 r p q st \<equiv> Val (last_obs st)"

definition next0 where
  "next0 r p st (msgs::process \<rightharpoonup> ('val::linorder) msg) st' \<equiv>
       (\<exists>v. (\<forall>q \<in> msgRcvd msgs. msgs q = Some (Val v))
           \<and> st' = st \<lparr> agreed_vote := Some v, last_obs := smallestValRcvd msgs \<rparr>)
    \<or> \<not>(\<exists>v. \<forall>q \<in> msgRcvd msgs. msgs q = Some (Val v))
       \<and> st' = st \<lparr> last_obs := smallestValRcvd msgs \<rparr>"

text \<open>
  In step 1, each process sends its current \<open>last_obs\<close> and \<open>agreed_vote\<close> values.
\<close>

definition send1 where
  "send1 r p q st \<equiv> ValVote (last_obs st) (agreed_vote st)"

definition valVoteRcvd where
  \<comment> \<open>processes from which values and votes were received\<close>
  "valVoteRcvd (msgs :: process \<rightharpoonup> 'val msg) \<equiv> 
   {q . \<exists>z v. msgs q = Some (ValVote z v)}"

definition smallestValNoVoteRcvd where
  "smallestValNoVoteRcvd (msgs::process \<rightharpoonup> ('val::linorder) msg) \<equiv>
   Min {v. \<exists>q. msgs q = Some (ValVote v None)}"

definition someVoteRcvd where
  \<comment> \<open>set of processes from which some vote was received\<close>
  "someVoteRcvd (msgs :: process \<rightharpoonup> 'val msg) \<equiv>
   { q . q \<in> msgRcvd msgs \<and> isValVote (the (msgs q)) \<and> getvote (the (msgs q)) \<noteq> None }"

definition identicalVoteRcvd where
  "identicalVoteRcvd (msgs :: process \<rightharpoonup> 'val msg) v \<equiv>
   \<forall>q \<in> msgRcvd msgs. isValVote (the (msgs q)) \<and> getvote (the (msgs q)) = Some v"

definition x_update where
 "x_update st msgs st' \<equiv>
   (\<exists>q \<in> someVoteRcvd msgs . last_obs st' = the (getvote (the (msgs q))))
 \<or> someVoteRcvd msgs = {} \<and> last_obs st' = smallestValNoVoteRcvd msgs"

definition dec_update where
  "dec_update st msgs st' \<equiv>
    (\<exists>v. identicalVoteRcvd msgs v \<and> decide st' = Some v)
  \<or> \<not>(\<exists>v. identicalVoteRcvd msgs v) \<and> decide st' = decide st"

definition next1 where
  "next1 r p st msgs st' \<equiv>
     x_update st msgs st'
   \<and> dec_update st msgs st'
   \<and> agreed_vote st' = None"

text \<open>
  The overall send function and next-state relation are simply obtained as 
  the composition of the individual relations defined above.
\<close>

definition UV_sendMsg where
  "UV_sendMsg (r::nat) \<equiv> if step r = 0 then send0 r else send1 r"

definition UV_nextState where
  "UV_nextState r \<equiv> if step r = 0 then next0 r else next1 r"


definition (in quorum_process) UV_commPerRd where
  "UV_commPerRd HOrs \<equiv> \<forall>p. HOrs p \<in> Quorum"

definition UV_commGlobal where
  "UV_commGlobal HOs \<equiv> \<exists>r. \<forall>p q. HOs r p = HOs r q"


subsection \<open>The \emph{UniformVoting} Heard-Of machine\<close>

text \<open>
  We now define the HO machine for \emph{Uniform Voting} by assembling the
  algorithm definition and its communication predicate. Notice that the
  coordinator arguments for the initialization and transition functions are
  unused since \emph{UniformVoting} is not a coordinated algorithm.
\<close>

definition (in quorum_process) UV_HOMachine where
  "UV_HOMachine = \<lparr> 
    CinitState =  (\<lambda>p st crd. UV_initState p st),
    sendMsg =  UV_sendMsg,
    CnextState = (\<lambda>r p st msgs crd st'. UV_nextState r p st msgs st'),
    HOcommPerRd = UV_commPerRd,
    HOcommGlobal = UV_commGlobal
  \<rparr>"

abbreviation (in quorum_process)
  "UV_M \<equiv> (UV_HOMachine::(process, 'val::linorder pstate, 'val msg) HOMachine)"

end
