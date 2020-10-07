(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  Secrecy.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Secrecy.thy 133008 2017-01-17 13:53:14Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  A simple model of secrecy with a set of secrets and the intruder knowledge.
  Secrecy = disjointness of secret messages and intruder knowledge
  Two events: (1) secret declaration (later by protocols)
              (2) intruder learns a message

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Secrecy Model (L0)\<close>

theory Secrecy 
imports Refinement IK
begin

declare domIff [simp, iff del] 

(**************************************************************************************************)
subsection \<open>State and events\<close>
(**************************************************************************************************)

text \<open>Level 0 secrecy state: extend intruder knowledge with set of secrets.\<close>

record s0_state = ik_state + 
  secret :: "msg set"


text \<open>Definition of the secrecy invariant: DY closure of intruder knowledge and set of
secrets are disjoint.\<close>

definition
  s0_secrecy :: "'a s0_state_scheme set"
where
  "s0_secrecy \<equiv> {s. synth (analz (ik s)) \<inter> secret s = {}}"

lemmas s0_secrecyI = s0_secrecy_def [THEN setc_def_to_intro, rule_format]
lemmas s0_secrecyE [elim] = s0_secrecy_def [THEN setc_def_to_elim, rule_format]


text \<open>Two events: add/declare a message as a secret and learn a (non-secret) message.\<close>

definition
  s0_add_secret :: "msg \<Rightarrow> ('a s0_state_scheme * 'a s0_state_scheme) set"
where
  "s0_add_secret m \<equiv> {(s,s').
    \<comment> \<open>guard\<close>
    m \<notin> synth (analz (ik s)) \<and>
    
    \<comment> \<open>action\<close>
    s' = s\<lparr>secret := insert m (secret s)\<rparr>
  }"

definition
  s0_learn :: "msg \<Rightarrow> ('a s0_state_scheme * 'a s0_state_scheme) set"
where
  "s0_learn m \<equiv> {(s,s').
    \<comment> \<open>guard\<close>
    s\<lparr>ik := insert m (ik s)\<rparr> \<in> s0_secrecy \<and> 

    \<comment> \<open>action\<close>
    s' = s\<lparr>ik := insert m (ik s)\<rparr>
  }"

definition
  s0_learn' :: "msg \<Rightarrow> ('a s0_state_scheme * 'a s0_state_scheme) set"
where
  "s0_learn' m \<equiv> {(s,s').
    \<comment> \<open>guard\<close>
    synth (analz (insert m (ik s))) \<inter> secret s = {} \<and> 

    \<comment> \<open>action\<close>
    s' = s\<lparr>ik := insert m (ik s)\<rparr>
  }"


definition
  s0_trans :: "('a s0_state_scheme * 'a s0_state_scheme) set"
where
  "s0_trans \<equiv> (\<Union>m. s0_add_secret m) \<union> (\<Union>m. s0_learn m) \<union> Id"


text \<open>Initial state is any state satisfying the invariant. The whole state is
observable. Put all together to define the L0 specification.\<close>

definition
  s0_init :: "'a s0_state_scheme set"
where
  "s0_init \<equiv> s0_secrecy"

type_synonym
  s0_obs = "s0_state"

definition 
  s0 :: "(s0_state, s0_obs) spec" where
  "s0 \<equiv> \<lparr>
    init = s0_init,
    trans = s0_trans,
    obs = id
  \<rparr>"

lemmas s0_defs = s0_def s0_init_def s0_trans_def s0_add_secret_def s0_learn_def 
lemmas s0_all_defs = s0_defs ik_trans_defs

lemma s0_obs_id [simp]: "obs s0 = id"
by (simp add: s0_def)


(**************************************************************************************************)
subsection \<open>Proof of secrecy invariant\<close>
(**************************************************************************************************)

lemma s0_secrecy_init [iff]: "init s0 \<subseteq> s0_secrecy"
by (simp add: s0_defs)

lemma s0_secrecy_trans [simp, intro]: "{s0_secrecy} trans s0 {> s0_secrecy}"
apply (auto simp add: s0_all_defs PO_hoare_defs intro!: s0_secrecyI)
apply (auto)
done

lemma s0_secrecy [iff]:"reach s0 \<subseteq> s0_secrecy"
by (rule inv_rule_basic, auto)


lemma s0_obs_secrecy [iff]:"oreach s0 \<subseteq> s0_secrecy"
by (rule external_from_internal_invariant) (auto del: subsetI)


lemma s0_anyP_observable [iff]: "observable (obs s0) P"
by (auto)


end


