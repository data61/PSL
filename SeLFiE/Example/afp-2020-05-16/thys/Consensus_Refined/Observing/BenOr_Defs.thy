section \<open>The Ben-Or Algorithm\<close>

theory BenOr_Defs
imports Heard_Of.HOModel "../Consensus_Types" "../Quorums" "../Two_Steps"
begin

consts coin :: "round \<Rightarrow> process \<Rightarrow> val"

record 'val pstate =
  x :: 'val                \<comment> \<open>current value held by process\<close>
  vote :: "'val option"    \<comment> \<open>value the process voted for, if any\<close>
  decide :: "'val option"  \<comment> \<open>value the process has decided on, if any\<close>

datatype 'val msg =
  Val 'val
| Vote "'val option"
| Null  \<comment> \<open>dummy message in case nothing needs to be sent\<close>

definition isVote where "isVote m \<equiv> \<exists>v. m = Vote v"

definition isVal where "isVal m \<equiv> \<exists>v. m = Val v"

fun getvote where
  "getvote (Vote v) = v"

fun getval where
  "getval (Val z) = z"

definition BenOr_initState where
  "BenOr_initState p st \<equiv> (vote st = None) \<and> (decide st = None)"

definition msgRcvd where  \<comment> \<open>processes from which some message was received\<close>
  "msgRcvd (msgs:: process \<rightharpoonup> 'val msg) = {q . msgs q \<noteq> None}"

definition send0 where
  "send0 r p q st \<equiv> Val (x st)"

definition next0 where
  "next0 r p st (msgs::process \<rightharpoonup> 'val msg) st' \<equiv>
       (\<exists>v. (\<forall>q \<in> msgRcvd msgs. msgs q = Some (Val v))
           \<and> st' = st \<lparr> vote := Some v \<rparr>)
    \<or> \<not>(\<exists>v. \<forall>q \<in> msgRcvd msgs. msgs q = Some (Val v))
       \<and> st' = st \<lparr> vote := None \<rparr>"

definition send1 where
  "send1 r p q st \<equiv> Vote (vote st)"

definition someVoteRcvd where
  \<comment> \<open>set of processes from which some vote was received\<close>
  "someVoteRcvd (msgs :: process \<rightharpoonup> 'val msg) \<equiv>
   { q . q \<in> msgRcvd msgs \<and> isVote (the (msgs q)) \<and> getvote (the (msgs q)) \<noteq> None }"

definition identicalVoteRcvd where
  "identicalVoteRcvd (msgs :: process \<rightharpoonup> 'val msg) v \<equiv>
   \<forall>q \<in> msgRcvd msgs. isVote (the (msgs q)) \<and> getvote (the (msgs q)) = Some v"

definition x_update where
 "x_update r p msgs st' \<equiv>
   (\<exists>q \<in> someVoteRcvd msgs . x st' = the (getvote (the (msgs q))))
 \<or> someVoteRcvd msgs = {} \<and> x st' = coin r p"

definition dec_update where
  "dec_update st msgs st' \<equiv>
    (\<exists>v. identicalVoteRcvd msgs v \<and> decide st' = Some v)
  \<or> \<not>(\<exists>v. identicalVoteRcvd msgs v) \<and> decide st' = decide st"

definition next1 where
  "next1 r p st msgs st' \<equiv>
     x_update r p msgs st'
   \<and> dec_update st msgs st'
   \<and> vote st' = None"

definition BenOr_sendMsg where
  "BenOr_sendMsg (r::nat) \<equiv> if two_step r = 0 then send0 r else send1 r"

definition BenOr_nextState where
  "BenOr_nextState r \<equiv> if two_step r = 0 then next0 r else next1 r"

subsection \<open>The \emph{Ben-Or} Heard-Of machine\<close>
(******************************************************************************)

definition (in quorum_process) BenOr_commPerRd where
  "BenOr_commPerRd HOrs \<equiv> \<forall>p. HOrs p \<in> Quorum"

definition BenOr_commGlobal where
  "BenOr_commGlobal HOs \<equiv> \<exists>r. two_step r = 1
    \<and> (\<forall>p q. HOs r p = HOs r q \<and> (coin r p :: val) = coin r q)"



definition (in quorum_process) BenOr_HOMachine where
  "BenOr_HOMachine = \<lparr> 
    CinitState =  (\<lambda>p st crd. BenOr_initState p st),
    sendMsg =  BenOr_sendMsg,
    CnextState = (\<lambda>r p st msgs crd st'. BenOr_nextState r p st msgs st'),
    HOcommPerRd = BenOr_commPerRd,
    HOcommGlobal = BenOr_commGlobal
  \<rparr>"

abbreviation (in quorum_process)
  "BenOr_M \<equiv> (BenOr_HOMachine::(process, val pstate, val msg) HOMachine)"

end
