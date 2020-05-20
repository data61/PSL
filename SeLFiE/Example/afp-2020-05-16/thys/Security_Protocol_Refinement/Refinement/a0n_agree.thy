(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Refinement/a0n_agree.thy (Isabelle/HOL 2016-1)
  ID:      $Id: a0n_agree.thy 134924 2017-05-24 17:23:15Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  One-Way authentication protocols
  Initial Model: Non-injective agreement 

  Copyright (c) 2009-2016 Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Non-injective Agreement\<close>

theory a0n_agree imports Refinement Agents
begin

text \<open>The initial model abstractly specifies entity authentication, where 
one agent/role authenticates another. More precisely, this property corresponds 
to non-injective agreement on a data set \<open>ds\<close>. We use Running and Commit 
signals to obtain a protocol-independent extensional specification.\<close>

text \<open>Proof tool configuration. Avoid annoying automatic unfolding of
\<open>dom\<close>.\<close>

declare domIff [simp, iff del]


(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>Signals. At this stage there are no protocol runs yet. All we model
are the signals that indicate a certain progress of a protocol run by one 
agent/role (Commit signal) and the other role (Running signal). The signals 
contain a list of agents that are assumed to be honest and a polymorphic data 
set to be agreed upon, which is instantiated later. 

Usually, the agent list will contain the names of the two agents who want to
agree on the data, but sometimes one of the agents is honest by assumption 
(e.g., the server) or the honesty of additional agents needs to be assumed
for the agreement to hold.\<close>

datatype 'ds signal =
  Running "agent list" "'ds" 
| Commit "agent list" "'ds"

record 'ds a0n_state = 
  signals :: "'ds signal \<Rightarrow> nat"    \<comment> \<open>multi-set of signals\<close>
  corrupted :: "'ds set"            \<comment> \<open>set of corrupted data\<close>

type_synonym 
  'ds a0n_obs = "'ds a0n_state"


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

definition 
  a0n_init :: "'ds a0n_state set"
where
  "a0n_init \<equiv> {s. \<exists>ds. s = \<lparr>
     signals = \<lambda>s. 0,
     corrupted = ds
  \<rparr> }"

text \<open>Running signal, indicating end of responder run.\<close>

definition 
  a0n_running :: "[agent list, 'ds] \<Rightarrow> ('ds a0n_state \<times> 'ds a0n_state) set"
where 
  "a0n_running h d \<equiv> {(s, s').
    \<comment> \<open>actions:\<close>
    s' = s\<lparr> 
      signals := (signals s)(Running h d := signals s (Running h d) + 1) 
    \<rparr>
  }"


text \<open>Commit signal, marking end of initiator run.\<close>

definition 
  a0n_commit :: "[agent list, 'ds] \<Rightarrow> ('ds a0n_state \<times> 'ds a0n_state) set"
where 
  "a0n_commit h d \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    (set h \<subseteq> good \<longrightarrow> d \<notin> corrupted s \<longrightarrow> signals s (Running h d) > 0) \<and>

    \<comment> \<open>actions:\<close>
    s' = s\<lparr> 
      signals := (signals s)(Commit h d := signals s (Commit h d) + 1) 
    \<rparr>
  }"

text \<open>Data corruption.\<close>

definition 
  a0n_corrupt :: "'ds set \<Rightarrow> ('ds a0n_state \<times> 'ds a0n_state) set"
where
  "a0n_corrupt ds \<equiv> {(s, s').
    \<comment> \<open>actions:\<close>
    s' = s\<lparr> 
      corrupted := corrupted s \<union> ds 
    \<rparr>   
  }"


text \<open>Transition system.\<close>

definition 
  a0n_trans :: "('ds a0n_state \<times> 'ds a0n_state) set" where
  "a0n_trans \<equiv> (\<Union>h d ds.
     a0n_running h d \<union>
     a0n_commit h d \<union> 
     a0n_corrupt ds \<union> 
     Id
  )"

definition 
  a0n :: "('ds a0n_state, 'ds a0n_obs) spec" where
  "a0n \<equiv> \<lparr>
    init = a0n_init,
    trans = a0n_trans, 
    obs = id
  \<rparr>"

lemmas a0n_defs = 
  a0n_def a0n_init_def a0n_trans_def 
  a0n_running_def a0n_commit_def a0n_corrupt_def


text \<open>Any property is trivially observable.\<close>

lemma a0n_obs [simp]: "obs a0n= id"
by (simp add: a0n_def)  

lemma a0n_anyP_observable [iff]: "observable (obs a0n) P"
by (auto)  


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

subsection \<open>inv1: non-injective agreement\<close>
(******************************************************************************)

text \<open>This is an extensional variant of Lowe's \emph{non-injective agreement}
of the first with the second agent (by convention) in \<open>h\<close> on data 
\<open>d\<close> [Lowe97]. 
\<close>

definition 
  a0n_inv1_niagree :: "'ds a0n_state set" 
where
  "a0n_inv1_niagree \<equiv> {s. \<forall>h d.
     set h \<subseteq> good \<longrightarrow> d \<notin> corrupted s \<longrightarrow>
       signals s (Commit h d) > 0 \<longrightarrow> signals s (Running h d) > 0
  }"

lemmas a0n_inv1_niagreeI = 
  a0n_inv1_niagree_def [THEN setc_def_to_intro, rule_format]
lemmas a0n_inv1_niagreeE [elim] = 
  a0n_inv1_niagree_def [THEN setc_def_to_elim, rule_format]
lemmas a0n_inv1_niagreeD = 
  a0n_inv1_niagree_def [THEN setc_def_to_dest, rule_format, rotated 2]


text \<open>Invariance proof.\<close>

lemma PO_a0n_inv1_niagree_init [iff]:
  "init a0n \<subseteq> a0n_inv1_niagree"
by (auto simp add: a0n_defs intro!: a0n_inv1_niagreeI)

lemma PO_a0n_inv1_niagree_trans [iff]:
  "{a0n_inv1_niagree} trans a0n {> a0n_inv1_niagree}"
apply (auto simp add: PO_hoare_defs a0n_defs intro!: a0n_inv1_niagreeI)
apply (auto dest!: a0n_inv1_niagreeD dest: dom_lemmas)
done

lemma PO_a0n_inv1_niagree [iff]: "reach a0n \<subseteq> a0n_inv1_niagree"
by (rule inv_rule_basic) (auto)


text \<open>This is also an external invariant.\<close>

lemma a0n_obs_inv1_niagree [iff]:
  "oreach a0n \<subseteq> a0n_inv1_niagree"
apply (rule external_from_internal_invariant, fast) 
apply (subst a0n_def, auto)
done


end
