section \<open>The New Algorithm\<close>

theory New_Algorithm_Defs
imports Heard_Of.HOModel "../Consensus_Types" "../Consensus_Misc" Three_Steps
begin

subsection \<open>Model of the algorithm\<close>
text \<open>We assume that the values are linearly ordered, to be able to have each process
  select the smallest value.\<close>
axiomatization where val_linorder: 
  "OFCLASS(val, linorder_class)"

instance val :: linorder by (rule val_linorder)

record pstate =
  x :: val                \<comment> \<open>current value held by process\<close>
  prop_vote :: "val option"
  mru_vote :: "(nat \<times> val) option"
  decide :: "val option"  \<comment> \<open>value the process has decided on, if any\<close>

datatype msg =
  MruVote "(nat \<times> val) option" "val"
| PreVote "val"
| Vote val
| Null  \<comment> \<open>dummy message in case nothing needs to be sent\<close>

text \<open>
  Characteristic predicates on messages.
\<close>

definition isLV where "isLV m \<equiv> \<exists>rv. m = Vote rv"

definition isPreVote where "isPreVote m \<equiv> \<exists>px. m = PreVote px"

definition NA_initState where
  "NA_initState p st _ \<equiv>
   mru_vote st = None
   \<and> prop_vote st = None
   \<and> decide st = None
  "

definition send0 where
  "send0 r p q st \<equiv> MruVote (mru_vote st) (x st)"

fun msg_to_val_stamp :: "msg \<Rightarrow> (round \<times> val)option" where
  "msg_to_val_stamp (MruVote rv _) = rv"

definition msgs_to_lvs ::
  "(process \<rightharpoonup> msg)
  \<Rightarrow> (process, round \<times> val) map"
where
  "msgs_to_lvs msgs \<equiv> msg_to_val_stamp \<circ>\<^sub>m msgs"

definition smallest_proposal where
  "smallest_proposal (msgs::process \<rightharpoonup> msg) \<equiv>
   Min {v. \<exists>q mv. msgs q = Some (MruVote mv v)}"

definition next0
  :: "nat 
  \<Rightarrow> process 
  \<Rightarrow> pstate 
  \<Rightarrow> (process \<rightharpoonup> msg)
  \<Rightarrow> process
  \<Rightarrow> pstate
  \<Rightarrow> bool"
where
  "next0 r p st msgs crd st' \<equiv> let 
      Q = dom msgs; 
      lvs = msgs_to_lvs msgs;
      smallest = if Q = {} then x st else smallest_proposal msgs
    in
    st' = st \<lparr>
      prop_vote := if card Q > N div 2
        then Some (case_option smallest snd (option_Max_by fst (ran (lvs |` Q))))
        else None
    \<rparr>"

definition send1 where
  "send1 r p q st \<equiv> case prop_vote st of
    None \<Rightarrow> Null
    | Some v \<Rightarrow> PreVote v"

definition Q_prevotes_v where
  "Q_prevotes_v msgs Q v \<equiv> let D = dom msgs in
    Q \<subseteq> D \<and> card Q > N div 2 \<and> (\<forall>q \<in> Q. msgs q = Some (PreVote v))"

definition next1 
  :: "nat 
  \<Rightarrow> process 
  \<Rightarrow> pstate 
  \<Rightarrow> (process \<rightharpoonup> msg)
  \<Rightarrow> process
  \<Rightarrow> pstate
  \<Rightarrow> bool"
where
  "next1 r p st msgs crd st' \<equiv> 
      decide st' = decide st
      \<and> x st' = x st 
      \<and> (\<forall>Q v. Q_prevotes_v msgs Q v
        \<longrightarrow> mru_vote st' = Some (three_phase r, v))
      \<and> (\<not> (\<exists>Q v. Q_prevotes_v msgs Q v)
        \<longrightarrow> mru_vote st' = mru_vote st)
  "

definition send2 where
  "send2 r p q st \<equiv> case mru_vote st of
    None \<Rightarrow> Null
    | Some (\<Phi>, v) \<Rightarrow> if \<Phi> = three_phase r then Vote v else Null"

definition Q'_votes_v where
  "Q'_votes_v r msgs Q Q' v \<equiv> 
    Q' \<subseteq> Q \<and> card Q' > N div 2 \<and> (\<forall>q \<in> Q'. msgs q = Some (Vote v))"

definition next2 
  :: "nat 
  \<Rightarrow> process 
  \<Rightarrow> pstate 
  \<Rightarrow> (process \<rightharpoonup> msg)
  \<Rightarrow> process
  \<Rightarrow> pstate
  \<Rightarrow> bool"
where
  "next2 r p st msgs crd st' \<equiv> let Q = dom msgs; lvs = msgs_to_lvs msgs in
    x st' = x st
    \<and> mru_vote st' = mru_vote st
    \<and> (\<forall>Q' v. Q'_votes_v r msgs Q Q' v \<longrightarrow> decide st' = Some v)
    \<and> (\<not>(\<exists>Q' v. Q'_votes_v r msgs Q Q' v \<longrightarrow> decide st' = decide st))
  "
    
definition NA_sendMsg :: "nat \<Rightarrow> process \<Rightarrow> process \<Rightarrow> pstate \<Rightarrow> msg" where
  "NA_sendMsg (r::nat) \<equiv>
   if three_step r = 0 then send0 r
   else if three_step r = 1 then send1 r
   else send2 r"

definition
  NA_nextState :: "nat \<Rightarrow> process \<Rightarrow> pstate \<Rightarrow> (process \<rightharpoonup> msg) 
                       \<Rightarrow> process \<Rightarrow> pstate \<Rightarrow> bool"
  where
  "NA_nextState r \<equiv>
   if three_step r = 0 then next0 r
   else if three_step r = 1 then next1 r
   else next2 r"

subsection \<open>The Heard-Of machine\<close>
definition
  NA_commPerRd where
  "NA_commPerRd (HOrs::process HO)  \<equiv> True"

definition
  NA_commGlobal where
  "NA_commGlobal HOs  \<equiv>
      \<exists>ph::nat. \<forall>i \<in> {0..2}. 
        (\<forall>p. card (HOs (nr_steps*ph+i) p) > N div 2)
        \<and> (\<forall>p q. HOs (nr_steps*ph+i) p = HOs (nr_steps*ph) q)
    "

definition New_Algo_Alg where
  "New_Algo_Alg \<equiv>
    \<lparr> CinitState = NA_initState,
      sendMsg = NA_sendMsg,
      CnextState = NA_nextState \<rparr>"

definition New_Algo_HOMachine where
  "New_Algo_HOMachine \<equiv>
    \<lparr> CinitState = NA_initState,
      sendMsg = NA_sendMsg,
      CnextState = NA_nextState,
      HOcommPerRd = NA_commPerRd,
      HOcommGlobal = NA_commGlobal \<rparr>"

abbreviation 
  "New_Algo_M \<equiv> (New_Algo_HOMachine::(process, pstate, msg) HOMachine)"

end
