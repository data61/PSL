(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Auth_simple/m2_confid_chan.thy (Isabelle/HOL 2016-1)
  ID:      $Id: m2_confid_chan.thy 133854 2017-03-20 17:53:50Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  One-Way authentication protocols
  Refinement 2: protocol using confidential channels

  Copyright (c) 2009-2016 Christoph Sprenger 
  Licence: LGPL

*******************************************************************************)

section \<open>Refinement 2b: Confidential Channel Protocol\<close>

theory m2_confid_chan imports m1_auth "../Refinement/Channels"
begin

text \<open>We refine the abstract authentication protocol to the first two
steps of the Needham-Schroeder-Lowe protocol, which we call NSL/2.
In standard protocol notation, the original protocol is specified as follows.
\[
\begin{array}{llll}
  \mathrm{M1.} & A \rightarrow B & : & \{N_A, A\}_{K(B)} \\
  \mathrm{M2.} & B \rightarrow A & : & \{N_A, N_B, B\}_{K(A)} 
\end{array}
\]
At this refinement level, we abstract the encrypted messages to 
non-cryptographic messages transmitted on confidential channels.\<close>

declare domIff [simp, iff del]


(******************************************************************************)
subsection \<open>State and observations\<close>
(******************************************************************************)

record m2_state = m1_state +
  chan :: "chmsg set"                     \<comment> \<open>channels\<close>

type_synonym 
  m2_obs = m1_state 

definition 
  m2_obs :: "m2_state \<Rightarrow> m2_obs" where
  "m2_obs s \<equiv> \<lparr> 
     runs = runs s
  \<rparr>"


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

definition 
  m2_init :: "m2_state set"
where
  "m2_init \<equiv> { \<lparr> 
     runs = Map.empty, 
     chan = {}
  \<rparr> }"


definition
  m2_step1 :: "[rid_t, agent, agent, nonce] \<Rightarrow> (m2_state \<times> m2_state) set"
where
  "m2_step1 Ra A B Na \<equiv> {(s, s1).

     \<comment> \<open>guards:\<close>
     Ra \<notin> dom (runs s) \<and>
     Na = Ra$0 \<and>

     \<comment> \<open>actions:\<close>
     s1 = s\<lparr>
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [])), 
       \<comment> \<open>send \<open>Na\<close> on confidential channel 1\<close>
       chan := insert (Confid A B (Msg [aNon Na])) (chan s)
     \<rparr>
  }"


definition
  m2_step2 :: "[rid_t, agent, agent, nonce, nonce] \<Rightarrow> (m2_state \<times> m2_state) set"
where
  "m2_step2 Rb A B Na Nb \<equiv> {(s, s1).

     \<comment> \<open>guards\<close>
     Rb \<notin> dom (runs s) \<and>
     Nb = Rb$0 \<and>

     Confid A B (Msg [aNon Na]) \<in> chan s \<and>           \<comment> \<open>receive M1\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [aNon Na])), 
       chan := insert (Confid B A (Msg [aNon Na, aNon Nb])) (chan s)
     \<rparr>  
  }"


definition
  m2_step3 :: "[rid_t, agent, agent, nonce, nonce] \<Rightarrow> (m2_state \<times> m2_state) set"
where
  "m2_step3 Ra A B Na Nb \<equiv> {(s, s1).

     \<comment> \<open>guards\<close>
     runs s Ra = Some (Init, [A, B], []) \<and>
     Na = Ra$0 \<and>

     Confid B A (Msg [aNon Na, aNon Nb]) \<in> chan s \<and>  \<comment> \<open>receive M2\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aNon Nb]))
     \<rparr>  
  }"


text \<open>Intruder fake event.\<close>

definition     \<comment> \<open>refines @{term Id}\<close> 
  m2_fake :: "(m2_state \<times> m2_state) set"
where
  "m2_fake \<equiv> {(s, s1). 
    \<comment> \<open>actions:\<close>
    s1 = s\<lparr> chan := fake ik0 (dom (runs s)) (chan s) \<rparr>
  }"


text \<open>Transition system.\<close>

definition 
  m2_trans :: "(m2_state \<times> m2_state) set" where
  "m2_trans \<equiv> (\<Union> A B Ra Rb Na Nb.
     m2_step1 Ra A B Na    \<union>
     m2_step2 Rb A B Na Nb \<union>
     m2_step3 Ra A B Na Nb \<union>
     m2_fake \<union>
     Id
  )"

definition
  m2 :: "(m2_state, m2_obs) spec" where
  "m2 \<equiv> \<lparr>
    init = m2_init,
    trans = m2_trans, 
    obs = m2_obs
  \<rparr>"

lemmas m2_defs = 
  m2_def m2_init_def m2_trans_def m2_obs_def
  m2_step1_def m2_step2_def m2_step3_def m2_fake_def 


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

subsubsection \<open>Invariant 1: Messages only contains generated nonces.\<close>
(******************************************************************************)

definition 
  m2_inv1_nonces :: "m2_state set" where
  "m2_inv1_nonces \<equiv> {s. \<forall>R. 
     aNon (R$0) \<in> atoms (chan s) \<longrightarrow> R \<in> dom (runs s) 
  }"

lemmas m2_inv1_noncesI = 
  m2_inv1_nonces_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv1_noncesE [elim] = 
  m2_inv1_nonces_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv1_noncesD = 
  m2_inv1_nonces_def [THEN setc_def_to_dest, rule_format, rotated 1]


lemma PO_m2_inv1_init [iff]: "init m2 \<subseteq> m2_inv1_nonces"
by (auto simp add: PO_hoare_def m2_defs intro!: m2_inv1_noncesI) 

lemma PO_m2_inv1_trans [iff]:
  "{m2_inv1_nonces} trans m2 {> m2_inv1_nonces}"
apply (auto simp add: PO_hoare_def m2_defs intro!: m2_inv1_noncesI) 
apply (auto dest: m2_inv1_noncesD)
\<comment> \<open>1 subgoal\<close>
apply (subgoal_tac "aNon (R$0) \<in> atoms (chan xa)", auto)
done

lemma PO_m2_inv012 [iff]: 
  "reach m2 \<subseteq> m2_inv1_nonces"
by (rule inv_rule_basic) (auto)


subsubsection \<open>Invariant 3: relates message 2 with the responder run\<close>
(******************************************************************************)
(*
 1. \<And>a y. \<lbrakk>runs a = runs y; runs y Ra = Some (Init, [A, B], []);
           Confid A B (Msg [aNon (Ra$0), aNon Nb]) \<in> chan y; A \<notin> bad; B \<notin> bad\<rbrakk>
          \<Longrightarrow> \<exists>Rb. Nb = Rb $ 0 \<and> runs y Rb = Some (Resp, [A, B], [aNon (Ra $ 0)])
*)
text \<open>It is needed, together with initiator nonce secrecy, in proof 
obligation REF/@{term m2_step2}.\<close>

definition 
  m2_inv3_msg2 :: "m2_state set" where
  "m2_inv3_msg2 \<equiv> {s. \<forall>A B Na Nb. 
     Confid B A (Msg [aNon Na, aNon Nb]) \<in> chan s \<longrightarrow> 
     aNon Na \<notin> extr ik0 (chan s) \<longrightarrow>
       (\<exists>Rb. Nb = Rb$0 \<and> runs s Rb = Some (Resp, [A, B], [aNon Na]))
  }"

lemmas m2_inv3_msg2I = m2_inv3_msg2_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv3_msg2E [elim] = m2_inv3_msg2_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv3_msg2D = m2_inv3_msg2_def [THEN setc_def_to_dest, rule_format, rotated 1]


lemma PO_m2_inv4_init [iff]:
  "init m2 \<subseteq> m2_inv3_msg2"
by (auto simp add: PO_hoare_def m2_defs intro!: m2_inv3_msg2I) 

lemma PO_m2_inv4_trans [iff]:
  "{m2_inv3_msg2} trans m2 {> m2_inv3_msg2}"
apply (auto simp add: PO_hoare_def m2_defs intro!: m2_inv3_msg2I)
apply (auto dest: m2_inv3_msg2D dom_lemmas)
\<comment> \<open>2 subgoals\<close>
  apply (drule m2_inv3_msg2D, auto dest: dom_lemmas)
  apply (drule m2_inv3_msg2D, auto, force)
done

lemma PO_m2_inv4 [iff]: "reach m2 \<subseteq> m2_inv3_msg2"
by (rule inv_rule_incr) (auto del: subsetI)


subsubsection \<open>Invariant 4: Initiator nonce secrecy.\<close>
(******************************************************************************)

text \<open>It is needed in the proof 
obligation REF/@{term m2_step2}. It would be sufficient to prove the invariant 
for the case @{term "x=None"}, but we have generalized it here.\<close>

definition 
  m2_inv4_inon_secret :: "m2_state set" where
  "m2_inv4_inon_secret \<equiv> {s. \<forall>A B Ra al.
     runs s Ra = Some (Init, [A, B], al) \<longrightarrow>
     A \<notin> bad \<longrightarrow> B \<notin> bad \<longrightarrow> 
       aNon (Ra$0) \<notin> extr ik0 (chan s)
  }"

lemmas m2_inv4_inon_secretI = 
  m2_inv4_inon_secret_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv4_inon_secretE [elim] = 
  m2_inv4_inon_secret_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv4_inon_secretD = 
  m2_inv4_inon_secret_def [THEN setc_def_to_dest, rule_format, rotated 1]


lemma PO_m2_inv3_init [iff]:
  "init m2 \<subseteq> m2_inv4_inon_secret"
by (auto simp add: PO_hoare_def m2_defs intro!: m2_inv4_inon_secretI)
 
lemma PO_m2_inv3_trans [iff]:
  "{m2_inv4_inon_secret \<inter> m2_inv1_nonces} 
     trans m2 
   {> m2_inv4_inon_secret}"
apply (auto simp add: PO_hoare_def m2_defs intro!: m2_inv4_inon_secretI)  
apply (auto dest: m2_inv4_inon_secretD) 
\<comment> \<open>3 subgoals\<close>
  apply (fastforce)                \<comment> \<open>requires @{text "m2_inv1_nonces"}\<close>
  apply (fastforce)                \<comment> \<open>requires ind hyp\<close>
  apply (fastforce)                \<comment> \<open>requires ind hyp\<close>
done 

lemma PO_m2_inv3 [iff]: "reach m2 \<subseteq> m2_inv4_inon_secret"
by (rule inv_rule_incr [where J="m2_inv1_nonces"]) (auto)


(******************************************************************************)
subsection \<open>Refinement\<close>
(******************************************************************************)

definition
  R12 :: "(m1_state \<times> m2_state) set" where
  "R12 \<equiv> {(s, t). runs s = runs t}"  

abbreviation
  med21 :: "m2_obs \<Rightarrow> m1_obs" where
  "med21 \<equiv> id"


text \<open>Proof obligations.\<close>

lemma PO_m2_step1_refines_m1_step1:
  "{R12} 
     (m1_step1 Ra A B Na), (m2_step1 Ra A B Na) 
   {> R12}"
by (auto simp add: PO_rhoare_defs R12_def m1_defs m2_defs)

lemma PO_m2_step2_refines_m1_step2:
  "{R12} 
     (m1_step2 Rb A B Na Nb), (m2_step2 Rb A B Na Nb) 
   {> R12}"
by (auto simp add: PO_rhoare_defs R12_def m1_defs m2_defs)

lemma PO_m2_step3_refines_m1_step3:
  "{R12 \<inter> UNIV \<times> (m2_inv4_inon_secret \<inter> m2_inv3_msg2)} 
     (m1_step3 Ra A B Na Nb), (m2_step3 Ra A B Na Nb) 
   {> R12}"
by (auto simp add: PO_rhoare_defs R12_def m1_defs m2_defs)
   (blast)

text \<open>New fake events refine skip.\<close>

lemma PO_m2_fake_refines_skip:
  "{R12} Id, m2_fake {> R12}"
by (auto simp add: PO_rhoare_def R12_def m1_defs m2_defs)

lemmas PO_m2_trans_refines_m1_trans = 
  PO_m2_step1_refines_m1_step1 PO_m2_step2_refines_m1_step2
  PO_m2_step3_refines_m1_step3 PO_m2_fake_refines_skip 


text \<open>All together now...\<close>

lemma PO_m2_refines_init_m1 [iff]:
  "init m2 \<subseteq> R12``(init m1)"
by (auto simp add: R12_def m1_defs m2_defs)

lemma PO_m2_refines_trans_m1 [iff]:
  "{R12 \<inter> 
    UNIV \<times> (m2_inv4_inon_secret \<inter> m2_inv3_msg2)} 
     (trans m1), (trans m2) 
   {> R12}"
apply (auto simp add: m2_def m2_trans_def m1_def m1_trans_def)
apply (blast intro!: PO_m2_trans_refines_m1_trans)+
done

lemma PO_R12_obs_consistent [iff]:
  "obs_consistent R12 med21 m1 m2"
by (auto simp add: obs_consistent_def R12_def m1_defs m2_defs)

lemma PO_m3_refines_m2:
  "refines 
     (R12 \<inter> 
      UNIV \<times> (m2_inv4_inon_secret \<inter> m2_inv3_msg2 \<inter> m2_inv1_nonces))
     med21 m1 m2"
by (rule Refinement_using_invariants) (auto)


end
