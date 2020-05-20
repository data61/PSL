(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Refinement/s0g_secrecy.thy (Isabelle/HOL 2016-1)
  ID:      $Id: s0g_secrecy.thy 134924 2017-05-24 17:23:15Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Key distribution protocols
  Initial Model: Secrecy (global version)

  Copyright (c) 2009-2016 Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Secrecy with Leaking (global version)\<close>

theory s0g_secrecy imports Refinement Agents
begin

text \<open>This model extends the global secrecy model by adding a \<open>leak\<close> 
event, which models that the adversary can learn messages through leaks of 
some (unspecified) kind.\<close>

text \<open>Proof tool configuration. Avoid annoying automatic unfolding of
\<open>dom\<close>.\<close>

declare domIff [simp, iff del] 


(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>The only state variable is a knowledge relation, an authorization 
relation, and a leakage relation. 

@{term "(d, A) \<in> kn s"} means that the agent @{term "A"} knows data @{term "d"}.
@{term "(d, A) \<in> az s"} means that the agent @{term "A"} is authorized to 
know data @{term "d"}. 
@{term "(d, A) \<in> lk s"} means that data @{term "d"} has leaked to agent 
@{term "A"}. Leakage models potential unauthorized knowledge.
\<close>

record 'd s0g_state = 
  kn :: "('d \<times> agent) set"
  az :: "('d \<times> agent) set"
  lk :: "'d set"                         \<comment> \<open>leaked data\<close>

type_synonym
  'd s0g_obs = "'d s0g_state"

abbreviation
  "lkr s \<equiv> lk s \<times> UNIV"

(******************************************************************************)
subsection \<open>Invariant definitions\<close>
(******************************************************************************)

text \<open>Global secrecy is stated as an invariant.\<close>

definition 
  s0g_secrecy :: "'d s0g_state set"
where 
  "s0g_secrecy \<equiv> {s. kn s \<subseteq> az s \<union> lkr s}"

lemmas s0g_secrecyI = s0g_secrecy_def [THEN setc_def_to_intro, rule_format]
lemmas s0g_secrecyE [elim] = 
  s0g_secrecy_def [THEN setc_def_to_elim, rule_format]


text \<open>Data that someone is authorized to know and leaked data is known 
by someone.\<close>

definition 
  s0g_dom :: "'d s0g_state set"
where 
  "s0g_dom \<equiv> {s. Domain (az s \<union> lkr s) \<subseteq> Domain (kn s)}"

lemmas s0g_domI = s0g_dom_def [THEN setc_def_to_intro, rule_format]
lemmas s0g_domE [elim] = s0g_dom_def [THEN setc_def_to_elim, rule_format]


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

text \<open>New secrets may be generated anytime.\<close>

definition 
  s0g_gen :: "['d, agent, agent set] \<Rightarrow> ('d s0g_state \<times> 'd s0g_state) set"
where 
  "s0g_gen d A G \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    A \<in> G \<and>    
    d \<notin> Domain (kn s) \<and>                      \<comment> \<open>fresh item\<close>
 
    \<comment> \<open>actions:\<close>
    s1 = s\<lparr> 
      kn := insert (d, A) (kn s), 
      az := az s \<union> {d} \<times> (if G \<inter> bad = {} then G else UNIV)
    \<rparr>
  }"


text \<open>Learning secrets.\<close>

definition 
  s0g_learn :: 
    "['d, agent] \<Rightarrow> ('d s0g_state \<times> 'd s0g_state) set"
where 
  "s0g_learn d B \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    \<comment> \<open>\<open>d \<in> Domain (kn s) \<and>\<close> someone knows \<open>d\<close> (follows from authorization)\<close>

    \<comment> \<open>check authorization or leakage to preserve secrecy\<close>
    (d, B) \<in> az s \<union> lkr s \<and>

    \<comment> \<open>actions:\<close>
    s1 = s\<lparr> kn := insert (d, B) (kn s) \<rparr>
  }"


text \<open>Leaking secrets.\<close>

definition 
  s0g_leak :: 
    "'d \<Rightarrow> ('d s0g_state \<times> 'd s0g_state) set"
where 
  "s0g_leak d \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    d \<in> Domain (kn s) \<and>       \<comment> \<open>someone knows \<open>d\<close>\<close>

    \<comment> \<open>actions:\<close>
    s1 = s\<lparr> lk := insert d (lk s) \<rparr>
  }"


(******************************************************************************)
subsection \<open>Specification\<close>
(******************************************************************************)

definition 
  s0g_init :: "'d s0g_state set"
where
  "s0g_init \<equiv> s0g_secrecy \<inter> s0g_dom"   \<comment> \<open>any state satisfying invariants\<close>

definition 
  s0g_trans :: "('d s0g_state \<times> 'd s0g_state) set" where
  "s0g_trans \<equiv> (\<Union>d A B G.
     s0g_gen d A G \<union>  
     s0g_learn d B \<union> 
     s0g_leak d \<union> 
     Id
  )"

definition 
  s0g :: "('d s0g_state, 'd s0g_obs) spec" where
  "s0g \<equiv> \<lparr>
    init = s0g_init,
    trans = s0g_trans,
    obs = id
  \<rparr>"

lemmas s0g_defs = 
  s0g_def s0g_init_def s0g_trans_def
  s0g_gen_def s0g_learn_def s0g_leak_def

lemma s0g_obs_id [simp]: "obs s0g = id"
by (simp add: s0g_def)


text \<open>All state predicates are trivially observable.\<close>

lemma s0g_anyP_observable [iff]: "observable (obs s0g) P"
by (auto)


(******************************************************************************)
subsection \<open>Invariant proofs\<close>
(******************************************************************************)

subsection \<open>inv1: Secrecy\<close>
(******************************************************************************)

lemma PO_s0g_secrecy_init [iff]:
  "init s0g \<subseteq> s0g_secrecy"
by (auto simp add: s0g_defs intro!: s0g_secrecyI)

lemma PO_s0g_secrecy_trans [iff]:
  "{s0g_secrecy} trans s0g {> s0g_secrecy}"
apply (auto simp add: s0g_defs PO_hoare_defs intro!: s0g_secrecyI)
apply (auto)
done

lemma PO_s0g_secrecy [iff]:"reach s0g \<subseteq> s0g_secrecy"
by (rule inv_rule_basic, auto)

text \<open>As en external invariant.\<close>

lemma PO_s0g_obs_secrecy [iff]:"oreach s0g \<subseteq> s0g_secrecy"
by (rule external_from_internal_invariant) (auto del: subsetI)


subsection \<open>inv2: Authorized and leaked data is known to someone\<close>
(******************************************************************************)

lemma PO_s0g_dom_init [iff]:
  "init s0g \<subseteq> s0g_dom"
by (auto simp add: s0g_defs intro!: s0g_domI)

lemma PO_s0g_dom_trans [iff]:
  "{s0g_dom} trans s0g {> s0g_dom}"
apply (auto simp add: s0g_defs PO_hoare_defs intro!: s0g_domI)
apply (blast)+
done

lemma PO_s0g_dom [iff]: "reach s0g \<subseteq> s0g_dom"
by (rule inv_rule_basic, auto)

text \<open>As en external invariant.\<close>

lemma PO_s0g_obs_dom [iff]: "oreach s0g \<subseteq> s0g_dom"
by (rule external_from_internal_invariant) (auto del: subsetI)


end

