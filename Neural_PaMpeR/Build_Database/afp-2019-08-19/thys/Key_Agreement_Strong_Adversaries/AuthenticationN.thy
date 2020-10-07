(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  AuthenticationN.thy (Isabelle/HOL 2016-1)
  ID:      $Id: AuthenticationN.thy 133008 2017-01-17 13:53:14Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Simple abstract model of non-injective agreement based on a multiset 
  of signals. Two events: running and commit.

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Non-injective Agreement (L0)\<close>

theory AuthenticationN imports Refinement Messages
begin

declare domIff [simp, iff del]

(**************************************************************************************************)
subsection \<open>Signals\<close>
(**************************************************************************************************)

text \<open>signals\<close>
datatype signal =
  Running agent agent msg
| Commit agent agent msg

fun
  addSignal :: "(signal \<Rightarrow> nat) \<Rightarrow> signal \<Rightarrow> signal \<Rightarrow> nat"
where
  "addSignal sigs s = sigs (s := sigs s + 1)"


(**************************************************************************************************)
subsection \<open>State and events\<close>
(**************************************************************************************************)

text \<open>level 0 non-injective agreement\<close>
record a0n_state = 
  signals :: "signal \<Rightarrow> nat"    \<comment> \<open>multi-set of signals\<close>

type_synonym 
  a0n_obs = a0n_state


text \<open>Events\<close>

definition 
  a0n_running :: "agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> (a0n_state \<times> a0n_state) set"
where 
  "a0n_running A B M \<equiv> {(s,s').
     \<comment> \<open>action\<close>
     s' = s\<lparr>signals := addSignal (signals s) (Running A B M)\<rparr>
  }"

definition 
  a0n_commit :: "agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> (a0n_state \<times> a0n_state) set"
where 
  "a0n_commit A B M \<equiv> {(s, s').
  \<comment> \<open>guard\<close>
    signals s (Running A B M) > 0 \<and>
  \<comment> \<open>action\<close>
    s' = s\<lparr>signals := addSignal (signals s) (Commit A B M)\<rparr>
  }"


definition 
  a0n_trans :: "(a0n_state \<times> a0n_state) set" where
  "a0n_trans \<equiv> (\<Union>A B M. a0n_running A B M) \<union> (\<Union>A B M. a0n_commit A B M) \<union> Id"


text \<open>Level 0 state\<close>

definition
  a0n_init :: "a0n_state set"
where
  "a0n_init \<equiv> {\<lparr>signals = \<lambda>s. 0\<rparr>}"


definition 
  a0n :: "(a0n_state, a0n_obs) spec" where
  "a0n \<equiv> \<lparr>
    init = a0n_init,
    trans = a0n_trans, 
    obs = id
  \<rparr>"

lemmas a0n_defs = 
  a0n_def a0n_init_def a0n_trans_def 
  a0n_running_def a0n_commit_def

lemma a0n_obs_id [simp]: "obs a0n = id"
by (simp add: a0n_def)  

lemma a0n_anyP_observable [iff]: "observable (obs a0n) P"
by (auto)  


(**************************************************************************************************)
subsection \<open>Non injective agreement invariant\<close>
(**************************************************************************************************)

text \<open>Invariant: non injective agreement\<close>

definition 
  a0n_agreement :: "a0n_state set" 
where
  "a0n_agreement \<equiv> {s. \<forall>A B M.
     signals s (Commit A B M) > 0 \<longrightarrow> signals s (Running A B M) > 0
  }"

lemmas a0n_agreementI = a0n_agreement_def [THEN setc_def_to_intro, rule_format]
lemmas a0n_agreementE [elim] = a0n_agreement_def [THEN setc_def_to_elim, rule_format]
lemmas a0n_agreementD = a0n_agreement_def [THEN setc_def_to_dest, rule_format, rotated 2]


lemma a0n_agreement_init [iff]:
  "init a0n \<subseteq> a0n_agreement"
by (auto simp add: a0n_defs intro!: a0n_agreementI)

lemma a0n_agreement_trans [iff]:
  "{a0n_agreement} trans a0n {> a0n_agreement}"
by (auto simp add: PO_hoare_defs a0n_defs intro!: a0n_agreementI)

lemma a0n_agreement [iff]: "reach a0n \<subseteq> a0n_agreement"
by (rule inv_rule_basic) (auto)


lemma a0n_obs_agreement [iff]:
  "oreach a0n \<subseteq> a0n_agreement"
apply (rule external_from_internal_invariant, fast) 
apply (subst a0n_def, auto)
done


end
