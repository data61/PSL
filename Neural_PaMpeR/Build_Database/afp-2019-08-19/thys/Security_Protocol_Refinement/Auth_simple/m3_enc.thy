(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Auth_simple/m3_enc.thy (Isabelle/HOL 2016-1)
  ID:      $Id: m3_enc.thy 133852 2017-03-20 15:59:33Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  One-Way authentication protocols
  Refinement 3: protocol using public-key encryption and Dolev-Yao intruder

  Copyright (c) 2009-2016 Christoph Sprenger 
  Licence: LGPL

*******************************************************************************)

section \<open>Refinement 3b: Encryption-based Dolev-Yao Protocol (Variant A)\<close>

theory m3_enc imports m2_confid_chan "../Refinement/Message"
begin

text \<open>This refines the channel protocol using public-key encryption and
adds a full-fledged Dolev-Yao adversary.  In this variant, the adversary is 
realized using Paulson's message derivation closure operators (as opposed to
a collection of one-step message construction and decomposition events a la 
Strand spaces).\<close>

text \<open>Proof tool configuration. Avoid annoying automatic unfolding of
\<open>dom\<close> (again).\<close>

declare domIff [simp, iff del]


text \<open>A general lemma about \<open>parts\<close> (move?!).\<close>

lemmas parts_insertD = parts_insert [THEN equalityD1, THEN subsetD]


(******************************************************************************)
subsection \<open>State and observations\<close>
(******************************************************************************)

text \<open>We extend the state of @{term m1} with two confidential channels
between each pair of agents, one channel for each protocol message.\<close>

record m3_state = m1_state +
  IK :: "msg set"                                 \<comment> \<open>intruder knowledge\<close>


text \<open>Observations: local agent states.\<close>

type_synonym 
  m3_obs = m1_obs

definition 
  m3_obs :: "m3_state \<Rightarrow> m3_obs" where
  "m3_obs s \<equiv> \<lparr> 
     runs = runs s
  \<rparr>"


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

definition
  m3_step1 :: "[rid_t, agent, agent, nonce] \<Rightarrow> (m3_state \<times> m3_state) set"
where
  "m3_step1 Ra A B Na \<equiv> {(s, s1).

     \<comment> \<open>guards:\<close>
     Ra \<notin> dom (runs s) \<and>
     Na = Ra$0 \<and>

     \<comment> \<open>actions:\<close>
     s1 = s\<lparr>
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [])), 
       IK := insert (Crypt (pubK B) \<lbrace>Nonce Na, Agent A\<rbrace>)  (IK s)
     \<rparr>
  }"

definition
  m3_step2 :: 
    "[rid_t, agent, agent, nonce, nonce] \<Rightarrow> (m3_state \<times> m3_state) set"
where
  "m3_step2 Rb A B Na Nb \<equiv> {(s, s1).

     \<comment> \<open>guards\<close>
     Rb \<notin> dom (runs s) \<and>
     Nb = Rb$0 \<and>

     Crypt (pubK B) \<lbrace>Nonce Na, Agent A\<rbrace> \<in> IK s \<and>      \<comment> \<open>receive msg 1\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [aNon Na])), 
       IK := insert (Crypt (pubK A) \<lbrace>Nonce Na, Nonce Nb, Agent B\<rbrace>) (IK s) 
     \<rparr>  
  }"

definition
  m3_step3 :: "[rid_t, agent, agent, nonce, nonce] \<Rightarrow> (m3_state \<times> m3_state) set"
where
  "m3_step3 Ra A B Na Nb \<equiv> {(s, s1).

     \<comment> \<open>guards\<close>
     runs s Ra = Some (Init, [A, B], []) \<and>
     Na = Ra$0 \<and>

     Crypt (pubK A) \<lbrace>Nonce Na, Nonce Nb, Agent B\<rbrace> \<in> IK s \<and>   \<comment> \<open>recv msg2\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aNon Nb]))
     \<rparr>  
  }"


text \<open>Standard Dolev-Yao intruder.\<close>

definition 
  m3_DY_fake :: "(m3_state \<times> m3_state) set"
where
  "m3_DY_fake \<equiv> {(s, s1).

     \<comment> \<open>actions:\<close>
     s1 = s\<lparr> IK := synth (analz (IK s)) \<rparr>  
  }"


text \<open>Transition system.\<close>

definition 
  m3_init :: "m3_state set" 
where
  "m3_init \<equiv> { \<lparr> 
     runs = Map.empty, 
     IK = (Key`priK`bad) \<union> (Key`range pubK) \<union> (Key`shrK`bad) 
  \<rparr> }"

definition 
  m3_trans :: "(m3_state \<times> m3_state) set" where
  "m3_trans \<equiv> (\<Union> A B Ra Rb Na Nb.
     m3_step1 Ra A B Na    \<union>
     m3_step2 Rb A B Na Nb \<union>
     m3_step3 Ra A B Na Nb \<union>
     m3_DY_fake \<union>
     Id
  )"

definition
  m3 :: "(m3_state, m3_obs) spec" where
  "m3 \<equiv> \<lparr>
    init = m3_init,
    trans = m3_trans, 
    obs = m3_obs
  \<rparr>"

lemmas m3_defs = 
  m3_def m3_init_def m3_trans_def m3_obs_def
  m3_step1_def m3_step2_def m3_step3_def 
  m3_DY_fake_def 


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

text \<open>Automatic tool tuning. Tame too-agressive pair decomposition, which is
declared as a safe elim rule ([elim!]).\<close>

lemmas MPair_parts [rule del, elim]
lemmas MPair_analz [rule del, elim]

text \<open>Specialize injectiveness of @{term "parts"} and @{term "analz"} to 
enable aggressive application.\<close>

lemmas parts_Inj_IK = parts.Inj [where H="IK s" for s]
lemmas analz_Inj_IK = analz.Inj [where H="IK s" for s]

declare analz_into_parts [dest]


subsubsection \<open>inv1: Key secrecy\<close>
(******************************************************************************)
 
text \<open>Decryption keys are secret, that is, the intruder only knows private 
keys of corrupted agents.\<close>

definition
  m3_inv1_keys :: "m3_state set" where
  "m3_inv1_keys \<equiv> {s. \<forall> A. 
     Key (priK A) \<in> parts (IK s) \<longrightarrow> A \<in> bad
  }"

lemmas m3_inv1_keysI = m3_inv1_keys_def [THEN setc_def_to_intro, rule_format]
lemmas m3_inv1_keysE [elim] = 
  m3_inv1_keys_def [THEN setc_def_to_elim, rule_format]
lemmas m3_inv1_keysD [dest] = 
  m3_inv1_keys_def [THEN setc_def_to_dest, rule_format, rotated 1]


lemma PO_m3_inv1_keys_init [iff]:
  "init m3 \<subseteq> m3_inv1_keys"
by (auto simp add: PO_hoare_def m3_defs intro!: m3_inv1_keysI) 

lemma PO_m3_inv1_keys_trans [iff]:
  "{m3_inv1_keys} trans m3 {> m3_inv1_keys}"
by (auto simp add: PO_hoare_def m3_defs intro!: m3_inv1_keysI) 
   (auto)

lemma PO_m3_inv1_keys [iff]: "reach m3 \<subseteq> m3_inv1_keys"
by (rule inv_rule_basic, auto)


(******************************************************************************)
subsection \<open>Simulation relation\<close>
(******************************************************************************)

text \<open>Simulation relation is canonical. It states that the protocol messages
appearing in the intruder knowledge refine those occurring on the abstract
confidential channels. Moreover, if the concrete intruder knows a nonce then so 
does the abstract one (as defined by \<open>ink\<close>).\<close>


text \<open>Abstraction function on sets of messages.\<close>

inductive_set 
  abs_msg :: "msg set \<Rightarrow> chmsg set"
  for H :: "msg set"
where 
  am_msg1: 
    "Crypt (pubK B) \<lbrace>Nonce Na, Agent A\<rbrace> \<in> H
  \<Longrightarrow> Confid A B (Msg [aNon Na]) \<in> abs_msg H"

| am_msg2:
    "Crypt (pubK A) \<lbrace>Nonce Na, Nonce Nb, Agent B\<rbrace> \<in> H 
  \<Longrightarrow> Confid B A (Msg [aNon Na, aNon Nb]) \<in> abs_msg H"

declare abs_msg.intros [intro!]
declare abs_msg.cases [elim!]


text \<open>The simulation relation is canonical. It states that the protocol 
messages in the intruder knowledge refine the abstract messages appearing on
the confidential channels.\<close>

definition
  R23_msgs :: "(m2_state \<times> m3_state) set" where
  "R23_msgs \<equiv> {(s, t). abs_msg (parts (IK t)) \<subseteq> chan s}"   \<comment> \<open>with \<open>parts\<close>!\<close>

definition 
  R23_non :: "(m2_state \<times> m3_state) set" where
  "R23_non \<equiv> {(s, t). \<forall>N. Nonce N \<in> analz (IK t) \<longrightarrow> aNon N \<in> extr ik0 (chan s)}"

definition 
  R23_pres :: "(m2_state \<times> m3_state) set" where
  "R23_pres \<equiv> {(s, t). runs s = runs t}"

definition 
  R23 :: "(m2_state \<times> m3_state) set" where
  "R23 \<equiv> R23_msgs \<inter> R23_non \<inter> R23_pres"

lemmas R23_defs =
  R23_def R23_msgs_def R23_non_def R23_pres_def

lemmas R23_msgsI = 
  R23_msgs_def [THEN rel_def_to_intro, simplified, rule_format]
lemmas R23_msgsE [elim] = 
  R23_msgs_def [THEN rel_def_to_elim, simplified, rule_format]
lemmas R23_msgsE' [elim] = 
  R23_msgs_def [THEN rel_def_to_dest, simplified, rule_format, THEN subsetD]

lemmas R23_nonI = 
  R23_non_def [THEN rel_def_to_intro, simplified, rule_format]
lemmas R23_nonE [elim] = 
  R23_non_def [THEN rel_def_to_elim, simplified, rule_format]

lemmas R23_presI = 
  R23_pres_def [THEN rel_def_to_intro, simplified, rule_format]
lemmas R23_presE [elim] = 
  R23_pres_def [THEN rel_def_to_elim, simplified, rule_format]

lemmas R23_intros = R23_msgsI R23_nonI R23_presI


text \<open>Mediator function.\<close>

abbreviation
  med32 :: "m3_obs \<Rightarrow> m2_obs" where
  "med32 \<equiv> id"


(******************************************************************************)
subsection \<open>Misc lemmas\<close>
(******************************************************************************)

text \<open>General facts about @{term "abs_msg"}\<close>

lemma abs_msg_empty: "abs_msg {} = {}"
by (auto)

lemma abs_msg_Un [simp]: 
  "abs_msg (G \<union> H) = abs_msg G \<union> abs_msg H"
by (auto)

lemma abs_msg_mono [elim]: 
  "\<lbrakk> m \<in> abs_msg G; G \<subseteq> H \<rbrakk> \<Longrightarrow> m \<in> abs_msg H"
by (auto)

lemma abs_msg_insert_mono [intro]: 
  "\<lbrakk> m \<in> abs_msg H \<rbrakk> \<Longrightarrow> m \<in> abs_msg (insert m' H)"
by (auto)


text \<open>Abstraction of concretely fakeable message yields abstractly fakeable 
messages. This is the key lemma for the refinement of the intruder.\<close>

lemma abs_msg_DY_subset_fake:
  "\<lbrakk> (s, t) \<in> R23_msgs; (s, t) \<in> R23_non; t \<in> m3_inv1_keys \<rbrakk>
  \<Longrightarrow> abs_msg (synth (analz (IK t))) \<subseteq> fake ik0 (dom (runs s)) (chan s)"
apply (auto)
  apply (rule fake_Inj, fastforce)
  apply (rule fake_intros, auto)
  apply (rule fake_Inj, fastforce)  
  apply (rule fake_intros, auto)
done

lemma abs_msg_parts_subset_fake:
  "\<lbrakk> (s, t) \<in> R23_msgs \<rbrakk>
  \<Longrightarrow> abs_msg (parts (IK t)) \<subseteq> fake ik0 (-dom (runs s)) (chan s)"
by (rule_tac B="chan s" in subset_trans) (auto)

declare abs_msg_DY_subset_fake [simp, intro!]
declare abs_msg_parts_subset_fake [simp, intro!]


(******************************************************************************)
subsection \<open>Refinement proof\<close>
(******************************************************************************)

text \<open>Proofs obligations.\<close>

lemma PO_m3_step1_refines_m2_step1:
  "{R23 \<inter> UNIV \<times> m3_inv1_keys} 
     (m2_step1 Ra A B Na), (m3_step1 Ra A B Na) 
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m2_defs m3_defs intro!: R23_intros)
   (auto)

lemma PO_m3_step2_refines_m2_step2:
  "{R23 \<inter> UNIV \<times> m3_inv1_keys} 
     (m2_step2 Rb A B Na Nb), (m3_step2 Rb A B Na Nb) 
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m2_defs m3_defs intro!: R23_intros)
   (auto)

lemma PO_m3_step3_refines_m2_step3:
  "{R23} 
     (m2_step3 Ra A B Na Nb), (m3_step3 Ra A B Na Nb) 
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m2_defs m3_defs intro!: R23_intros)


text \<open>Dolev-Yao fake event refines abstract fake event.\<close>

lemma PO_m3_DY_fake_refines_m2_fake:
  "{R23 \<inter> UNIV \<times> m3_inv1_keys} 
     (m2_fake), (m3_DY_fake) 
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m2_defs m3_defs) 
   (rule R23_intros, auto)+


text \<open>All together now...\<close>

lemmas PO_m3_trans_refines_m2_trans = 
  PO_m3_step1_refines_m2_step1 PO_m3_step2_refines_m2_step2 
  PO_m3_step3_refines_m2_step3 PO_m3_DY_fake_refines_m2_fake 

lemma PO_m3_refines_init_m2 [iff]:
  "init m3 \<subseteq> R23``(init m2)"
by (auto simp add: R23_defs m2_defs m3_defs)

lemma PO_m3_refines_trans_m2 [iff]:
  "{R23 \<inter> UNIV \<times> m3_inv1_keys} 
     (trans m2), (trans m3) 
   {> R23}"
apply (auto simp add: m3_def m3_trans_def m2_def m2_trans_def)
apply (blast intro!: PO_m3_trans_refines_m2_trans)+
done

lemma PO_R23_obs_consistent [iff]: 
  "obs_consistent R23 med32 m2 m3"
by (auto simp add: obs_consistent_def R23_def m2_defs m3_defs)

lemma PO_m3_refines_m2 [iff]:
  "refines 
     (R23 \<inter> UNIV \<times> m3_inv1_keys)
     med32 m2 m3"
by (rule Refinement_using_invariants) (auto)


end

