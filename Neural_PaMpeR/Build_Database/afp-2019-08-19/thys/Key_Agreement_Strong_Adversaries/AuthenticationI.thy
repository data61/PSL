(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  AuthenticationI.thy (Isabelle/HOL 2016-1)
  ID:      $Id: AuthenticationI.thy 132844 2016-12-19 15:21:54Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Simple abstract model of injective agreement based on a multiset of signals. 
  Two events: running and commit. Refines model for non-injective agreement.

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Injective Agreement (L0)\<close>

theory AuthenticationI
imports AuthenticationN
begin

(**************************************************************************************************)
subsection \<open>State and events\<close>
(**************************************************************************************************)

type_synonym
  a0i_state = a0n_state

type_synonym
  a0i_obs = a0n_obs

abbreviation
  a0i_init :: "a0n_state set"
where
  "a0i_init \<equiv> a0n_init"

abbreviation
  a0i_running :: "agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> (a0i_state \<times> a0i_state) set"
where
  "a0i_running \<equiv> a0n_running"

lemmas a0i_running_def = a0n_running_def

definition 
  a0i_commit :: "agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> (a0i_state \<times> a0i_state) set"
where 
  "a0i_commit A B M \<equiv> {(s, s').
   \<comment> \<open>guard\<close>
     signals s (Commit A B M) < signals s (Running A B M) \<and>
   \<comment> \<open>actions:\<close>
     s' = s\<lparr>signals := addSignal (signals s) (Commit A B M)\<rparr>
  }"


definition 
  a0i_trans :: "(a0i_state \<times> a0i_state) set" where
  "a0i_trans \<equiv> (\<Union> A B M. a0i_running A B M) \<union> (\<Union> A B M. a0i_commit A B M) \<union> Id"


definition 
  a0i :: "(a0i_state,a0i_obs) spec" where
  "a0i \<equiv> \<lparr>
    init = a0i_init,
    trans = a0i_trans, 
    obs = id
  \<rparr>"

lemmas a0i_defs = a0n_defs a0i_def a0i_trans_def a0i_commit_def

lemma a0i_obs [simp]: "obs a0i = id"
by (simp add: a0i_def)

lemma a0i_anyP_observable [iff]: "observable (obs a0i) P"
by (auto)  


(**************************************************************************************************)
subsection \<open>Injective agreement invariant\<close>
(**************************************************************************************************)

definition 
  a0i_agreement :: "a0i_state set" 
where
  "a0i_agreement \<equiv> {s. \<forall>A B M.
    signals s (Commit A B M) \<le> signals s (Running A B M)
  }"

lemmas a0i_agreementI = 
  a0i_agreement_def [THEN setc_def_to_intro, rule_format]
lemmas a0i_agreementE [elim] = 
  a0i_agreement_def [THEN setc_def_to_elim, rule_format]
lemmas a0i_agreementD = 
  a0i_agreement_def [THEN setc_def_to_dest, rule_format, rotated 1]


lemma PO_a0i_agreement_init [iff]:
  "init a0i \<subseteq> a0i_agreement"
by (auto simp add: a0i_defs intro!: a0i_agreementI)

lemma PO_a0i_agreement_trans [iff]:
  "{a0i_agreement} trans a0i {> a0i_agreement}"
apply (auto simp add: PO_hoare_defs a0i_defs intro!: a0i_agreementI)
apply (auto dest: a0i_agreementD intro: le_SucI)
done

lemma PO_a0i_agreement [iff]: "reach a0i \<subseteq> a0i_agreement"
by (rule inv_rule_basic) (auto)


lemma PO_a0i_obs_agreement [iff]: "oreach a0i \<subseteq> a0i_agreement"
apply (rule external_from_internal_invariant, fast) 
apply (subst a0i_def, auto)
done


(**************************************************************************************************)
subsection \<open>Refinement\<close>
(**************************************************************************************************)

definition
  med0n0i :: "a0i_obs \<Rightarrow> a0i_obs"
where
  "med0n0i \<equiv> id"

definition
  R0n0i :: "(a0n_state \<times> a0i_state) set"
where
  "R0n0i \<equiv> Id"

lemma PO_a0i_running_refines_a0n_running:
  "{R0n0i} a0n_running A B M, a0i_running A B M {> R0n0i}"
by (unfold R0n0i_def) (rule relhoare_refl)

lemma PO_a0i_commit_refines_a0n_commit:
  "{R0n0i} a0n_commit A B M, a0i_commit A B M {> R0n0i}"
by (auto simp add: PO_rhoare_defs R0n0i_def a0i_defs)


lemmas PO_a0i_trans_refines_a0n_trans = 
  PO_a0i_running_refines_a0n_running
  PO_a0i_commit_refines_a0n_commit


lemma PO_a0i_refines_init_a0n [iff]:
  "init a0i \<subseteq> R0n0i``(init a0n)"
by (auto simp add: R0n0i_def a0i_defs)

lemma PO_a0i_refines_trans_a0n [iff]:
  "{R0n0i} trans a0n, trans a0i {> R0n0i}"
by (auto simp add: a0n_def a0n_trans_def a0i_def a0i_trans_def
         intro!: PO_a0i_trans_refines_a0n_trans relhoare_abstract_UN)

lemma PO_obs_consistent [iff]:
  "obs_consistent R0n0i med0n0i a0n a0i"
by (auto simp add: obs_consistent_def R0n0i_def med0n0i_def a0i_def a0n_def)

lemma PO_a0i_refines_a0n:
  "refines R0n0i med0n0i a0n a0i"
by (rule Refinement_basic) (auto)


(**************************************************************************************************)
subsection \<open>Derived invariant\<close>
(**************************************************************************************************)

lemma iagreement_implies_niagreement [iff]: "a0i_agreement \<subseteq> a0n_agreement"
apply (auto intro!: a0n_agreementI)
apply (drule a0i_agreementD, drule order.strict_trans2, auto)
done


lemma PO_a0i_a0n_agreement [iff]: "reach a0i \<subseteq> a0n_agreement"
by (rule subset_trans, rule, rule)

lemma PO_a0i_obs_a0n_agreement [iff]: "oreach a0i \<subseteq> a0n_agreement"
by (rule subset_trans, rule, rule)


end
