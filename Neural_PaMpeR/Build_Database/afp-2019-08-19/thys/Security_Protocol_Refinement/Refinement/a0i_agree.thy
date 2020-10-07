(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Refinement/a0i_agree.thy (Isabelle/HOL 2016-1)
  ID:      $Id: a0i_agree.thy 134924 2017-05-24 17:23:15Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  One-Way authentication protocols
  Initial Model: Injective agreement

  Copyright (c) 2009-2016 Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Injective Agreement\<close>

theory a0i_agree imports a0n_agree
begin

text \<open>This refinement adds injectiveness to the agreement property.\<close>


(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>The state and observations are the same as in the previous model.\<close>

type_synonym
  'd a0i_state = "'d a0n_state"

type_synonym
  'd a0i_obs = "'d a0n_obs"


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

text \<open>We just refine the commit event. Everything else remains the same.\<close>

abbreviation
  a0i_init :: "'ds a0n_state set"
where
  "a0i_init \<equiv> a0n_init"

abbreviation
  a0i_running :: "[agent list, 'ds] \<Rightarrow> ('ds a0i_state \<times> 'ds a0i_state) set"
where 
  "a0i_running \<equiv> a0n_running"

definition 
  a0i_commit :: 
    "[agent list, 'ds] \<Rightarrow> ('ds a0i_state \<times> 'ds a0i_state) set"
where 
  "a0i_commit h d \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    (set h \<subseteq> good \<longrightarrow> d \<notin> corrupted s \<longrightarrow>
       signals s (Commit h d) < signals s (Running h d)) \<and>

    \<comment> \<open>actions:\<close>
    s' = s\<lparr> 
      signals := (signals s)(Commit h d := signals s (Commit h d) + 1) 
    \<rparr>
  }"

abbreviation
  a0i_corrupt :: "'ds set \<Rightarrow> ('ds a0i_state \<times> 'ds a0i_state) set"
where 
  "a0i_corrupt \<equiv> a0n_corrupt"


text \<open>Transition system.\<close>

definition 
  a0i_trans :: "('ds a0i_state \<times> 'ds a0i_state) set" where
  "a0i_trans \<equiv> (\<Union> h d ds.
     a0i_running h d \<union>
     a0i_commit h d \<union> 
     a0i_corrupt ds \<union> 
     Id
  )"

definition 
  a0i :: "('ds a0i_state, 'ds a0i_obs) spec" where
  "a0i \<equiv> \<lparr>
    init = a0i_init,
    trans = a0i_trans, 
    obs = id
  \<rparr>"

lemmas a0i_defs = 
  a0n_defs a0i_def a0i_trans_def a0i_commit_def


text \<open>Any property is trivially observable.\<close>

lemma a0i_obs [simp]: "obs a0i = id"
by (simp add: a0i_def)

lemma a0i_anyP_observable [iff]: "observable (obs a0i) P"
by (auto)  


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

subsubsection \<open>Injective agreement.\<close>
(******************************************************************************)

definition 
  a0i_inv1_iagree :: "'ds a0i_state set" 
where
  "a0i_inv1_iagree \<equiv> {s. \<forall>h d.
     set h \<subseteq> good \<longrightarrow> d \<notin> corrupted s \<longrightarrow>
       signals s (Commit h d) \<le> signals s (Running h d)
  }"

lemmas a0i_inv1_iagreeI = 
  a0i_inv1_iagree_def [THEN setc_def_to_intro, rule_format]
lemmas a0i_inv1_iagreeE [elim] = 
  a0i_inv1_iagree_def [THEN setc_def_to_elim, rule_format]
lemmas a0i_inv1_iagreeD = 
  a0i_inv1_iagree_def [THEN setc_def_to_dest, rule_format, rotated 1]


lemma PO_a0i_inv1_iagree_init [iff]:
  "init a0i \<subseteq> a0i_inv1_iagree"
by (auto simp add: a0i_defs intro!: a0i_inv1_iagreeI)

lemma PO_a0i_inv1_iagree_trans [iff]:
  "{a0i_inv1_iagree} trans a0i {> a0i_inv1_iagree}"
apply (auto simp add: PO_hoare_defs a0i_defs intro!: a0i_inv1_iagreeI)
apply (auto dest: a0i_inv1_iagreeD intro: le_SucI)
done

lemma PO_a0i_inv1_iagree [iff]: "reach a0i \<subseteq> a0i_inv1_iagree"
by (rule inv_rule_basic) (auto)


text \<open>As an external invariant.\<close>

lemma PO_a0i_obs_inv1_iagree [iff]: "oreach a0i \<subseteq> a0i_inv1_iagree"
apply (rule external_from_internal_invariant, fast) 
apply (subst a0i_def, auto)
done


(******************************************************************************)
subsection \<open>Refinement\<close>
(******************************************************************************)

definition
  med0n0i :: "'d a0i_obs \<Rightarrow> 'd a0i_obs"
where
  "med0n0i \<equiv> id"

definition
  R0n0i :: "('d a0n_state \<times> 'd a0i_state) set"
where
  "R0n0i \<equiv> Id"

lemma PO_a0i_running_refines_a0n_running:
  "{R0n0i} 
     (a0n_running h d), (a0i_running h d) 
   {> R0n0i}"
by (unfold R0n0i_def) (rule relhoare_refl)

lemma PO_a0i_commit_refines_a0n_commit:
  "{R0n0i} 
     (a0n_commit h d), (a0i_commit h d) 
   {> R0n0i}"
by (auto simp add: PO_rhoare_defs R0n0i_def a0i_defs)

lemma PO_a0i_corrupt_refines_a0n_corrupt:
  "{R0n0i} 
     (a0n_corrupt d), (a0i_corrupt d) 
   {> R0n0i}"
by (unfold R0n0i_def) (rule relhoare_refl)

lemmas PO_a0i_trans_refines_a0n_trans = 
  PO_a0i_running_refines_a0n_running
  PO_a0i_commit_refines_a0n_commit
  PO_a0i_corrupt_refines_a0n_corrupt


text \<open>All together now...\<close>

lemma PO_m1_refines_init_a0n [iff]:
  "init a0i \<subseteq> R0n0i``(init a0n)"
by (auto simp add: R0n0i_def a0i_defs)

lemma PO_m1_refines_trans_a0n [iff]:
  "{R0n0i} 
     (trans a0n), (trans a0i) 
   {> R0n0i}"
by (auto simp add: a0n_def a0n_trans_def a0i_def a0i_trans_def
         intro!: PO_a0i_trans_refines_a0n_trans)


lemma PO_obs_consistent [iff]:
  "obs_consistent R0n0i med0n0i a0n a0i"
by (auto simp add: obs_consistent_def R0n0i_def med0n0i_def a0i_def a0n_def)

lemma PO_a0i_refines_a0n:
  "refines R0n0i med0n0i a0n a0i"
by (rule Refinement_basic) (auto)


(******************************************************************************)
subsection \<open>Derived invariants\<close>
(******************************************************************************)

lemma iagree_implies_niagree [iff]: "a0i_inv1_iagree \<subseteq> a0n_inv1_niagree"
apply (auto intro!: a0n_inv1_niagreeI)
apply (drule_tac d=d in a0i_inv1_iagreeD, auto) 
done


text \<open>Non-injective agreeement as internal and external invariants.\<close>

lemma PO_a0i_a0n_inv1_niagree [iff]: "reach a0i \<subseteq> a0n_inv1_niagree"
by (rule subset_trans, rule, rule)

lemma PO_a0i_obs_a0n_inv1_niagree [iff]: "oreach a0i \<subseteq> a0n_inv1_niagree"
by (rule subset_trans, rule, rule)


end
