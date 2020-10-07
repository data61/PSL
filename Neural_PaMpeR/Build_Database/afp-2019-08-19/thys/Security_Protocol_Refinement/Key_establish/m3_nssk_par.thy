(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Key_establish/m3_nssk_par.thy (Isabelle/HOL 2016-1)
  ID:      $Id: m3_nssk_par.thy 132890 2016-12-24 10:25:57Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>

  Key distribution protocols
  Third refinement: parallel version of Needham-Schroeder Shared Key protocol
  (NSSK, Boyd/Mathuria, Protocol 3.19)

  Copyright (c) 2009-2016 Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Needham-Schroeder Shared Key, "parallel" variant (L3)\<close>

theory m3_nssk_par imports m2_nssk "../Refinement/Message"
begin

text \<open>
We model an abstract version of the Needham-Schroeder Shared Key protocol:
\[
\begin{array}{lll}
  \mathrm{M1.} & A \rightarrow S: & A, B, Na \\ 
  \mathrm{M2.} & S \rightarrow A: & \{Na, B, Kab, \{Kab, A\}_{Kbs} \}_{Kas} \\
  \mathrm{M3.} & A \rightarrow B: & \{Kab, A\}_{Kbs} \\
  \mathrm{M4.} & B \rightarrow A: & \{Nb\}_{Kab} \\ 
  \mathrm{M5.} & A \rightarrow B: & \{Nb - 1 \}_{Kab} \\
\end{array}
\]
We model a "parallel" version of the NSSK protocol:
\[
\begin{array}{lll}
  \mathrm{M1.} & A \rightarrow S: & A, B, Na \\ 
  \mathrm{M2.} & S \rightarrow A: & \{Na, B, Kab\}_{Kas} \\
  \mathrm{M3.} & S \rightarrow B: & \{Kab, A\}_{Kbs} \\
  \mathrm{M4.} & B \rightarrow A: & \{Nb\}_{Kab} \\ 
  \mathrm{M5.} & A \rightarrow B: & \{Nb - 1 \}_{Kab} \\
\end{array}
\]
\<close>

text \<open>Proof tool configuration. Avoid annoying automatic unfolding of
\<open>dom\<close>.\<close>

declare domIff [simp, iff del]


(******************************************************************************)
subsection \<open>Setup\<close>
(******************************************************************************)

text \<open>Now we can define the initial key knowledge.\<close>

overloading ltkeySetup' \<equiv> ltkeySetup begin
definition ltkeySetup_def: "ltkeySetup' \<equiv> {(sharK C, A) | C A. A = C \<or> A = Sv}"
end

lemma corrKey_shrK_bad [simp]: "corrKey = shrK`bad"
by (auto simp add: keySetup_def ltkeySetup_def corrKey_def)


(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>The secure channels are star-shaped to/from the server.  Therefore,
we have only one agent in the relation.\<close>

record m3_state = "m1_state" +
  IK :: "msg set"                                \<comment> \<open>intruder knowledge\<close>


text \<open>Observable state: agent's local state.\<close>

type_synonym
  m3_obs = m2_obs

definition
  m3_obs :: "m3_state \<Rightarrow> m3_obs" where
  "m3_obs s \<equiv> \<lparr> runs = runs s, leak = leak s \<rparr>"

type_synonym
  m3_pred = "m3_state set"

type_synonym
  m3_trans = "(m3_state \<times> m3_state) set"


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

text \<open>Protocol events.\<close>

definition     \<comment> \<open>by @{term "A"}, refines @{term "m2_step1"}\<close>
  m3_step1 :: "[rid_t, agent, agent, nonce] \<Rightarrow> m3_trans"
where
  "m3_step1 Ra A B Na \<equiv> {(s, s1).

    \<comment> \<open>guards:\<close>
    Ra \<notin> dom (runs s) \<and>                      \<comment> \<open>\<open>Ra\<close> is fresh\<close>
    Na = Ra$na \<and>                             \<comment> \<open>generate nonce \<open>Na\<close>\<close>

    \<comment> \<open>actions:\<close>
    s1 = s\<lparr>
      runs := (runs s)(Ra \<mapsto> (Init, [A, B], [])),
      IK := insert \<lbrace>Agent A, Agent B, Nonce Na\<rbrace> (IK s)    \<comment> \<open>send msg 1\<close>
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "B"}, refines @{term "m2_step2"}\<close>
  m3_step2 :: "[rid_t, agent, agent] \<Rightarrow> m3_trans"
where
  "m3_step2 Rb A B \<equiv> {(s, s1).

    \<comment> \<open>guards:\<close>
    Rb \<notin> dom (runs s) \<and>                       \<comment> \<open>\<open>Rb\<close> is fresh\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>create responder thread\<close>
    s1 = s\<lparr>
      runs := (runs s)(Rb \<mapsto> (Resp, [A, B], []))
    \<rparr>
  }"

definition     \<comment> \<open>by @{text "Server"}, refines @{term m2_step3}\<close>
  m3_step3 :: "[rid_t, agent, agent, nonce, key] \<Rightarrow> m3_trans"
where
  "m3_step3 Rs A B Na Kab \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    Rs \<notin> dom (runs s) \<and>                           \<comment> \<open>fresh server run\<close>
    Kab = sesK (Rs$sk) \<and>                          \<comment> \<open>fresh session key\<close>

    \<lbrace>Agent A, Agent B, Nonce Na\<rbrace> \<in> IK s \<and>       \<comment> \<open>recv msg 1\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>record session key and send messages 2 and 3\<close>
    \<comment> \<open>note that last field in server record is for responder nonce\<close>
    s1 = s\<lparr>
      runs := (runs s)(Rs \<mapsto> (Serv, [A, B], [aNon Na])),
      IK := {Crypt (shrK A) \<lbrace>Nonce Na, Agent B, Key Kab\<rbrace>,
             Crypt (shrK B) \<lbrace>Key Kab, Agent A\<rbrace>} \<union> IK s
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "A"}, refines @{term m2_step4}\<close>
  m3_step4 :: "[rid_t, agent, agent, nonce, key] \<Rightarrow> m3_trans"
where
  "m3_step4 Ra A B Na Kab \<equiv> {(s, s1).

    \<comment> \<open>guards:\<close>
    runs s Ra = Some (Init, [A, B], []) \<and>
    Na = Ra$na \<and>

    Crypt (shrK A) \<lbrace>Nonce Na, Agent B, Key Kab\<rbrace> \<in> IK s \<and>  \<comment> \<open>recv msg 2\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>record session key\<close>
    s1 = s\<lparr>
      runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aKey Kab]))
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "B"}, refines @{term m2_step5}\<close>
  m3_step5 :: "[rid_t, agent, agent, nonce, key] \<Rightarrow> m3_trans"
where
  "m3_step5 Rb A B Nb Kab \<equiv> {(s, s1).

    \<comment> \<open>guards:\<close>
    runs s Rb = Some (Resp, [A, B], []) \<and>
    Nb = Rb$nb \<and>

    Crypt (shrK B) \<lbrace>Key Kab, Agent A\<rbrace> \<in> IK s \<and>              \<comment> \<open>recv msg 3\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>record session key\<close>
    s1 = s\<lparr>
      runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [aKey Kab])),
      IK := insert (Crypt Kab (Nonce Nb)) (IK s)
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "A"}, refines @{term m2_step6}\<close>
  m3_step6 :: "[rid_t, agent, agent, nonce, nonce, key] \<Rightarrow> m3_trans"
where
  "m3_step6 Ra A B Na Nb Kab \<equiv> {(s, s').
    runs s Ra = Some (Init, [A, B], [aKey Kab]) \<and>      \<comment> \<open>key recv'd before\<close>
    Na = Ra$na \<and>

    Crypt Kab (Nonce Nb) \<in> IK s \<and>                      \<comment> \<open>receive \<open>M4\<close>\<close>

    \<comment> \<open>actions:\<close>
    s' = s\<lparr>
      runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNon Nb])),
      IK := insert (Crypt Kab \<lbrace>Nonce Nb, Nonce Nb\<rbrace>) (IK s)
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "B"}, refines @{term m2_step6}\<close>
  m3_step7 :: "[rid_t, agent, agent, nonce, key] \<Rightarrow> m3_trans"
where
  "m3_step7 Rb A B Nb Kab \<equiv> {(s, s').
    runs s Rb = Some (Resp, [A, B], [aKey Kab]) \<and>       \<comment> \<open>key recv'd before\<close>
    Nb = Rb$nb \<and>

    Crypt Kab \<lbrace>Nonce Nb, Nonce Nb\<rbrace> \<in> IK s \<and>               \<comment> \<open>receive \<open>M5\<close>\<close>

    \<comment> \<open>actions: (redundant) update local state marks successful termination\<close>
    s' = s\<lparr>
      runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [aKey Kab, END]))
    \<rparr>
  }"

text \<open>Session key compromise.\<close>

definition     \<comment> \<open>refines @{term m2_leak}\<close>
  m3_leak :: "[rid_t, rid_t, rid_t, agent, agent] \<Rightarrow> m3_trans"
where
  "m3_leak Rs Ra Rb A B \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    runs s Rs = Some (Serv, [A, B], [aNon (Ra$na)]) \<and>
    runs s Ra = Some (Init, [A, B], [aKey (sesK (Rs$sk)), aNon (Rb$nb)]) \<and>
    runs s Rb = Some (Resp, [A, B], [aKey (sesK (Rs$sk)), END]) \<and>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>record session key as leaked and add it to intruder knowledge\<close>
    s1 = s\<lparr> leak := insert (sesK (Rs$sk), Ra$na, Rb$nb) (leak s),
            IK := insert (Key (sesK (Rs$sk))) (IK s) \<rparr>
  }"

text \<open>Intruder fake event.\<close>

definition     \<comment> \<open>refines @{term "m2_fake"}\<close>
  m3_DY_fake :: "m3_trans"
where
  "m3_DY_fake \<equiv> {(s, s1).

     \<comment> \<open>actions:\<close>
     s1 = s(|
       IK := synth (analz (IK s))
     |)
  }"


(******************************************************************************)
subsection \<open>Transition system\<close>
(******************************************************************************)

definition
  m3_init :: "m3_state set"
where
  "m3_init \<equiv> { \<lparr>
     runs = Map.empty,
     leak = shrK`bad \<times> {undefined} \<times> {undefined},
     IK = Key`shrK`bad
  \<rparr> }"

definition
  m3_trans :: "(m3_state \<times> m3_state) set" where
  "m3_trans \<equiv> (\<Union>Ra Rb Rs A B Na Nb Kab.
     m3_step1 Ra A B Na \<union>
     m3_step2 Rb A B \<union>
     m3_step3 Rs A B Na Kab \<union>
     m3_step4 Ra A B Na Kab \<union>
     m3_step5 Rb A B Nb Kab \<union>
     m3_step6 Ra A B Na Nb Kab \<union>
     m3_step7 Rb A B Nb Kab \<union>
     m3_leak Rs Ra Rb A B \<union>
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
  m3_step1_def m3_step2_def m3_step3_def m3_step4_def m3_step5_def
  m3_step6_def m3_step7_def m3_leak_def m3_DY_fake_def


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

text \<open>Specialized injection that we can apply more aggressively.\<close>

lemmas analz_Inj_IK = analz.Inj [where H="IK s" for s]
lemmas parts_Inj_IK = parts.Inj [where H="IK s" for s]

declare parts_Inj_IK [dest!]

declare analz_into_parts [dest]


subsubsection \<open>inv1: Secrecy of pre-distributed shared keys\<close>
(******************************************************************************)

text \<open>inv1: Secrecy of long-term keys\<close>

definition
  m3_inv1_lkeysec :: "m3_state set"
where
  "m3_inv1_lkeysec \<equiv> {s. \<forall>C.
     (Key (shrK C) \<in> parts (IK s) \<longrightarrow> C \<in> bad) \<and>
     (C \<in> bad \<longrightarrow> Key (shrK C) \<in> IK s)
  }"

lemmas m3_inv1_lkeysecI = m3_inv1_lkeysec_def [THEN setc_def_to_intro, rule_format]
lemmas m3_inv1_lkeysecE [elim] = m3_inv1_lkeysec_def [THEN setc_def_to_elim, rule_format]
lemmas m3_inv1_lkeysecD = m3_inv1_lkeysec_def [THEN setc_def_to_dest, rule_format]


text \<open>Invariance proof.\<close>

lemma PO_m3_inv1_lkeysec_init [iff]:
  "init m3 \<subseteq> m3_inv1_lkeysec"
by (auto simp add: m3_defs m3_inv1_lkeysec_def)

lemma PO_m3_inv1_lkeysec_trans [iff]:
  "{m3_inv1_lkeysec} trans m3 {> m3_inv1_lkeysec}"
by (fastforce simp add: PO_hoare_defs m3_defs intro!: m3_inv1_lkeysecI)

lemma PO_m3_inv1_lkeysec [iff]: "reach m3 \<subseteq> m3_inv1_lkeysec"
by (rule inv_rule_incr) (fast+)


text \<open>Useful simplifier lemmas\<close>

lemma m3_inv1_lkeysec_for_parts [simp]:
  "\<lbrakk> s \<in> m3_inv1_lkeysec \<rbrakk> \<Longrightarrow> Key (shrK C) \<in> parts (IK s) \<longleftrightarrow> C \<in> bad"
by auto

lemma m3_inv1_lkeysec_for_analz [simp]:
  "\<lbrakk> s \<in> m3_inv1_lkeysec \<rbrakk> \<Longrightarrow> Key (shrK C) \<in> analz (IK s) \<longleftrightarrow> C \<in> bad"
by auto


subsubsection \<open>inv7a: Session keys not used to encrypt other session keys\<close>
(******************************************************************************)

text \<open>Session keys are not used to encrypt other keys. Proof requires
generalization to sets of session keys.

NOTE: This invariant will be derived from the corresponding L2 invariant
using the simulation relation.
\<close>

definition
  m3_inv7a_sesK_compr :: "m3_pred"
where
  "m3_inv7a_sesK_compr \<equiv> {s. \<forall>K KK.
     KK \<subseteq> range sesK \<longrightarrow>
     (Key K \<in> analz (Key`KK \<union> (IK s))) = (K \<in> KK \<or> Key K \<in> analz (IK s))
  }"

lemmas m3_inv7a_sesK_comprI = m3_inv7a_sesK_compr_def [THEN setc_def_to_intro, rule_format]
lemmas m3_inv7a_sesK_comprE = m3_inv7a_sesK_compr_def [THEN setc_def_to_elim, rule_format]
lemmas m3_inv7a_sesK_comprD = m3_inv7a_sesK_compr_def [THEN setc_def_to_dest, rule_format]

text \<open>Additional lemma\<close>
lemmas insert_commute_Key = insert_commute [where x="Key K" for K]

lemmas m3_inv7a_sesK_compr_simps =
  m3_inv7a_sesK_comprD
  m3_inv7a_sesK_comprD [where KK="{Kab}" for Kab, simplified]
  m3_inv7a_sesK_comprD [where KK="insert Kab KK" for Kab KK, simplified]
  insert_commute_Key


(******************************************************************************)
subsection \<open>Refinement\<close>
(******************************************************************************)

subsubsection \<open>Message abstraction and simulation relation\<close>
(******************************************************************************)

text \<open>Abstraction function on sets of messages.\<close>

inductive_set
  abs_msg :: "msg set \<Rightarrow> chmsg set"
  for H :: "msg set"
where
  am_M1:
    "\<lbrace>Agent A, Agent B, Nonce Na\<rbrace> \<in> H
  \<Longrightarrow> Insec A B (Msg [aNon Na]) \<in> abs_msg H"
| am_M2:
    "Crypt (shrK C) \<lbrace>Nonce N, Agent B, Key K\<rbrace> \<in> H
  \<Longrightarrow> Secure Sv C (Msg [aNon N, aAgt B, aKey K]) \<in> abs_msg H"
| am_M3:
    "Crypt (shrK C) \<lbrace>Key K, Agent A\<rbrace> \<in> H
  \<Longrightarrow> Secure Sv C (Msg [aKey K, aAgt A]) \<in> abs_msg H"
| am_M4:
    "Crypt K (Nonce N) \<in> H
  \<Longrightarrow> dAuth K (Msg [aNon N]) \<in> abs_msg H"
| am_M5:
    "Crypt K \<lbrace>Nonce N, Nonce N'\<rbrace> \<in> H
  \<Longrightarrow> dAuth K (Msg [aNon N, aNon N']) \<in> abs_msg H"


text \<open>R23: The simulation relation. This is a data refinement of
the insecure and secure channels of refinement 2.\<close>

definition
  R23_msgs :: "(m2_state \<times> m3_state) set" where
  "R23_msgs \<equiv> {(s, t). abs_msg (parts (IK t)) \<subseteq> chan s}"

definition
  R23_keys :: "(m2_state \<times> m3_state) set" where      \<comment> \<open>equivalence!\<close>
  "R23_keys \<equiv> {(s, t). \<forall>KK K. KK \<subseteq> range sesK \<longrightarrow>
     Key K \<in> analz (Key`KK \<union> IK t) \<longleftrightarrow> aKey K \<in> extr (aKey`KK \<union> ik0) (chan s)
  }"

definition
  R23_non :: "(m2_state \<times> m3_state) set" where      \<comment> \<open>only an implication!\<close>
  "R23_non \<equiv> {(s, t). \<forall>KK N. KK \<subseteq> range sesK \<longrightarrow>
     Nonce N \<in> analz (Key`KK \<union> IK t) \<longrightarrow> aNon N \<in> extr (aKey`KK \<union> ik0) (chan s)
  }"

definition
  R23_pres :: "(m2_state \<times> m3_state) set" where
  "R23_pres \<equiv> {(s, t). runs s = runs t \<and> leak s = leak t}"

definition
  R23 :: "(m2_state \<times> m3_state) set" where
  "R23 \<equiv> R23_msgs \<inter> R23_keys \<inter> R23_non \<inter> R23_pres"

lemmas R23_defs =
  R23_def R23_msgs_def R23_keys_def R23_non_def R23_pres_def


text \<open>The mediator function is the identity here.\<close>

definition
  med32 :: "m3_obs \<Rightarrow> m2_obs" where
  "med32 \<equiv> id"


lemmas R23_msgsI = R23_msgs_def [THEN rel_def_to_intro, simplified, rule_format]
lemmas R23_msgsE [elim] = R23_msgs_def [THEN rel_def_to_elim, simplified, rule_format]

lemmas R23_keysI = R23_keys_def [THEN rel_def_to_intro, simplified, rule_format]
lemmas R23_keysE [elim] = R23_keys_def [THEN rel_def_to_elim, simplified, rule_format]
lemmas R23_keysD = R23_keys_def [THEN rel_def_to_dest, simplified, rule_format]

lemmas R23_nonI = R23_non_def [THEN rel_def_to_intro, simplified, rule_format]
lemmas R23_nonE [elim] = R23_non_def [THEN rel_def_to_elim, simplified, rule_format]
lemmas R23_nonD = R23_non_def [THEN rel_def_to_dest, simplified, rule_format, rotated 2]

lemmas R23_presI = R23_pres_def [THEN rel_def_to_intro, simplified, rule_format]
lemmas R23_presE [elim] = R23_pres_def [THEN rel_def_to_elim, simplified, rule_format]

lemmas R23_intros = R23_msgsI R23_keysI R23_nonI R23_presI


text \<open>Further lemmas: general lemma for simplifier and different instantiations.\<close>

lemmas R23_keys_simps =
  R23_keysD
  R23_keysD [where KK="{}", simplified]
  R23_keysD [where KK="{K'}" for K', simplified]
  R23_keysD [where KK="insert K' KK" for K' KK, simplified, OF _ conjI]

lemmas R23_non_dests =
  R23_nonD
  R23_nonD [where KK="{}", simplified]
  R23_nonD [where KK="{K}" for K, simplified]
  R23_nonD [where KK="insert K KK" for K KK, simplified, OF _ _ conjI]


subsubsection \<open>General lemmas\<close>
(******************************************************************************)

text \<open>General facts about @{term "abs_msg"}\<close>

declare abs_msg.intros [intro!]
declare abs_msg.cases [elim!]

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


text \<open>Facts about @{term "abs_msg"} concerning abstraction of fakeable
messages. This is crucial for proving the refinement of the intruder event.\<close>

lemma abs_msg_DY_subset_fakeable:
  "\<lbrakk> (s, t) \<in> R23_msgs; (s, t) \<in> R23_keys; (s, t) \<in> R23_non; t \<in> m3_inv1_lkeysec \<rbrakk>
  \<Longrightarrow> abs_msg (synth (analz (IK t))) \<subseteq> fake ik0 (dom (runs s)) (chan s)"
apply (auto)
\<comment> \<open>9 subgoals, deal with replays first\<close>
prefer 2 apply (blast)
prefer 3 apply (blast)
prefer 4 apply (blast)
prefer 5 apply (blast)
\<comment> \<open>remaining 5 subgoals are real fakes\<close>
apply (intro fake_StatCh fake_DynCh, auto simp add: R23_keys_simps dest: R23_non_dests)+
done


subsubsection \<open>Refinement proof\<close>
(******************************************************************************)

text \<open>Pair decomposition. These were set to \texttt{elim!}, which is too
agressive here.\<close>

declare MPair_analz [rule del, elim]
declare MPair_parts [rule del, elim]


text \<open>Protocol events.\<close>

lemma PO_m3_step1_refines_m2_step1:
  "{R23}
     (m2_step1 Ra A B Na), (m3_step1 Ra A B Na)
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m2_defs m3_defs intro!: R23_intros)
   (auto)

lemma PO_m3_step2_refines_m2_step2:
  "{R23}
     (m2_step2 Rb A B), (m3_step2 Rb A B)
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m2_defs m3_defs intro!: R23_intros)
   (auto)

lemma PO_m3_step3_refines_m2_step3:
  "{R23 \<inter> (m2_inv3a_sesK_compr) \<times> (m3_inv7a_sesK_compr \<inter> m3_inv1_lkeysec)}
     (m2_step3 Rs A B Na Kab), (m3_step3 Rs A B Na Kab)
   {> R23}"
proof -
  { fix s t
    assume H:
      "(s, t) \<in> R23_msgs" "(s, t) \<in> R23_keys" "(s, t) \<in> R23_non" "(s, t) \<in> R23_pres"
      "s \<in> m2_inv3a_sesK_compr" "t \<in> m3_inv7a_sesK_compr" "t \<in> m3_inv1_lkeysec"
      "Kab = sesK (Rs$sk)" "Rs \<notin> dom (runs t)"
      "\<lbrace> Agent A, Agent B, Nonce Na \<rbrace> \<in> parts (IK t)"
    let ?s'=
      "s\<lparr> runs := runs s(Rs \<mapsto> (Serv, [A, B], [aNon Na])),
          chan := insert (Secure Sv A (Msg [aNon Na, aAgt B, aKey Kab]))
                 (insert (Secure Sv B (Msg [aKey Kab, aAgt A])) (chan s)) \<rparr>"
    let ?t'=
      "t\<lparr> runs := runs t(Rs \<mapsto> (Serv, [A, B], [aNon Na])),
          IK := insert (Crypt (shrK A) \<lbrace> Nonce Na, Agent B, Key Kab \<rbrace>)
                (insert (Crypt (shrK B) \<lbrace> Key Kab, Agent A \<rbrace>) (IK t)) \<rparr>"
    have "(?s', ?t') \<in> R23_msgs" using H
    by (-) (rule R23_intros, auto)
  moreover
    have "(?s', ?t') \<in> R23_keys" using H
    by (-) (rule R23_intros,
            auto simp add: m2_inv3a_sesK_compr_simps m3_inv7a_sesK_compr_simps,
            auto simp add: R23_keys_simps)
  moreover
    have "(?s', ?t') \<in> R23_non" using H
    by (-) (rule R23_intros,
            auto simp add: m2_inv3a_sesK_compr_simps m3_inv7a_sesK_compr_simps
                 dest: R23_non_dests)
  moreover
    have "(?s', ?t') \<in> R23_pres" using H
    by (-) (rule R23_intros, auto)
  moreover
    note calculation
  }
  thus ?thesis
  by (auto simp add: PO_rhoare_defs R23_def m2_defs m3_defs)
qed

(*  with equality in R23_keys [OLD, before adding session key compromise]:

goal (1 subgoal):
 1. \<And>s t. \<lbrakk>t \<in> m3_inv3_keyuse; t \<in> m3_inv1_lkeysec; t \<in> m3_inv5_badkeys;
           Kab \<notin> dom (runs t); Kab \<notin> range shrK;
           \<lbrace>Agent A, Agent B, Nonce Na\<rbrace> \<in> parts (IK t);
           Kab \<notin> keysFor (analz (IK t)); Key (shrK A) \<notin> analz (IK t);
           (s, t) \<in> R23_msgs; (s, t) \<in> R23_keys; (s, t) \<in> R23_pres; Kab \<noteq> shrK A;
           Key (shrK B) \<in> analz (IK t); Kab \<noteq> shrK B; A \<notin> bad; B \<in> bad\<rbrakk>
          \<Longrightarrow> Key Kab \<in> analz (IK t)

This does NOT hold, since Kab is revealed in abstract model when A \<notin> bad; B \<in> bad,
but not in concrete one, since here it is protected by A's encryption.
*)


lemma PO_m3_step4_refines_m2_step4:
  "{R23}
     (m2_step4 Ra A B Na Kab), (m3_step4 Ra A B Na Kab)
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m2_defs m3_defs intro!: R23_intros)
   (auto)

lemma PO_m3_step5_refines_m2_step5:
  "{R23}
     (m2_step5 Rb A B Nb Kab), (m3_step5 Rb A B Nb Kab)
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m2_defs m3_defs intro!: R23_intros)
   (auto)

lemma PO_m3_step6_refines_m2_step6:
  "{R23}
     (m2_step6 Ra A B Na Nb Kab), (m3_step6 Ra A B Na Nb Kab)
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m2_defs m3_defs intro!: R23_intros)
   (auto)

lemma PO_m3_step7_refines_m2_step7:
  "{R23}
     (m2_step7 Rb A B Nb Kab), (m3_step7 Rb A B Nb Kab)
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m2_defs m3_defs intro!: R23_intros)
   (auto)


text \<open>Intruder events.\<close>

lemma PO_m3_leak_refines_m2_leak:
  "{R23}
     (m2_leak Rs Ra Rb A B), (m3_leak Rs Ra Rb A B)
   {>R23}"
by (auto simp add: PO_rhoare_defs R23_def m2_defs m3_defs intro!: R23_intros)
   (auto simp add: R23_keys_simps dest: R23_non_dests)

lemma PO_m3_DY_fake_refines_m2_fake:
  "{R23 \<inter> UNIV \<times> m3_inv1_lkeysec}
     m2_fake, m3_DY_fake
   {> R23}"
apply (auto simp add: PO_rhoare_defs R23_def m2_defs m3_defs intro!: R23_intros
            del: abs_msg.cases)
apply (auto intro: abs_msg_DY_subset_fakeable [THEN subsetD]
            del: abs_msg.cases)
apply (auto simp add: R23_keys_simps dest: R23_non_dests)
done


text \<open>All together now...\<close>

lemmas PO_m3_trans_refines_m2_trans =
  PO_m3_step1_refines_m2_step1 PO_m3_step2_refines_m2_step2
  PO_m3_step3_refines_m2_step3 PO_m3_step4_refines_m2_step4
  PO_m3_step5_refines_m2_step5 PO_m3_step6_refines_m2_step6
  PO_m3_step7_refines_m2_step7 PO_m3_leak_refines_m2_leak
  PO_m3_DY_fake_refines_m2_fake


lemma PO_m3_refines_init_m2 [iff]:
  "init m3 \<subseteq> R23``(init m2)"
by (auto simp add: R23_def m2_defs m3_defs intro!: R23_intros)

lemma PO_m3_refines_trans_m2 [iff]:
  "{R23 \<inter> (m2_inv3a_sesK_compr) \<times> (m3_inv7a_sesK_compr \<inter> m3_inv1_lkeysec)}
     (trans m2), (trans m3)
   {> R23}"
apply (auto simp add: m3_def m3_trans_def m2_def m2_trans_def)
apply (blast intro!: PO_m3_trans_refines_m2_trans)+
done

lemma PO_m3_observation_consistent [iff]:
  "obs_consistent R23 med32 m2 m3"
by (auto simp add: obs_consistent_def R23_def med32_def m2_defs m3_defs)


text \<open>Refinement result.\<close>

lemma m3_refines_m2 [iff]:
  "refines (R23 \<inter> m2_inv3a_sesK_compr \<times> m3_inv1_lkeysec)
     med32 m2 m3"
proof -
  have "R23 \<inter> m2_inv3a_sesK_compr \<times> UNIV \<subseteq> UNIV \<times> m3_inv7a_sesK_compr"
    by (auto simp add: R23_def R23_keys_simps intro!: m3_inv7a_sesK_comprI)
  thus ?thesis
    by (-) (rule Refinement_using_invariants, auto)
qed


lemma m3_implements_m2 [iff]:
  "implements med32 m2 m3"
by (rule refinement_soundness) (auto)


subsection \<open>Inherited invariants\<close>
(******************************************************************************)

subsubsection \<open>inv4 (derived): Key secrecy for initiator\<close>
(*invh*************************************************************************)

definition
  m3_inv4_ikk_init :: "m3_state set"
where
  "m3_inv4_ikk_init \<equiv> {s. \<forall>Ra K A B al.
     runs s Ra = Some (Init, [A, B], aKey K # al) \<longrightarrow> A \<in> good \<longrightarrow> B \<in> good \<longrightarrow>
     Key K \<in> analz (IK s) \<longrightarrow>
       (\<exists>Nb'. (K, Ra $ na, Nb') \<in> leak s)
  }"

lemmas m3_inv4_ikk_initI = m3_inv4_ikk_init_def [THEN setc_def_to_intro, rule_format]
lemmas m3_inv4_ikk_initE [elim] = m3_inv4_ikk_init_def [THEN setc_def_to_elim, rule_format]
lemmas m3_inv4_ikk_initD = m3_inv4_ikk_init_def [THEN setc_def_to_dest, rule_format, rotated 1]

lemma PO_m3_inv4_ikk_init: "reach m3 \<subseteq> m3_inv4_ikk_init"
proof (rule INV_from_Refinement_using_invariants [OF m3_refines_m2])
  show "Range (R23 \<inter> m2_inv3a_sesK_compr \<times> m3_inv1_lkeysec
                   \<inter> m2_inv6_ikk_init \<times> UNIV)
      \<subseteq> m3_inv4_ikk_init"
    by (auto simp add: R23_def R23_pres_def R23_keys_simps intro!: m3_inv4_ikk_initI)
qed auto


subsubsection \<open>inv5 (derived): Key secrecy for responder\<close>
(*invh*************************************************************************)

definition
  m3_inv5_ikk_resp :: "m3_state set"
where
  "m3_inv5_ikk_resp \<equiv> {s. \<forall>Rb K A B al.
     runs s Rb = Some (Resp, [A, B], aKey K # al) \<longrightarrow> A \<in> good \<longrightarrow> B \<in> good \<longrightarrow>
     Key K \<in> analz (IK s) \<longrightarrow>
       K \<in> Domain (leak s)
  }"

lemmas m3_inv5_ikk_respI = m3_inv5_ikk_resp_def [THEN setc_def_to_intro, rule_format]
lemmas m3_inv5_ikk_respE [elim] = m3_inv5_ikk_resp_def [THEN setc_def_to_elim, rule_format]
lemmas m3_inv5_ikk_respD = m3_inv5_ikk_resp_def [THEN setc_def_to_dest, rule_format, rotated 1]

lemma PO_m3_inv4_ikk_resp: "reach m3 \<subseteq> m3_inv5_ikk_resp"
proof (rule INV_from_Refinement_using_invariants [OF m3_refines_m2])
  show "Range (R23 \<inter> m2_inv3a_sesK_compr \<times> m3_inv1_lkeysec
                   \<inter> m2_inv7_ikk_resp \<times> UNIV)
      \<subseteq> m3_inv5_ikk_resp"
    by (auto simp add: R23_def R23_pres_def R23_keys_simps intro!: m3_inv5_ikk_respI)
       (elim m2_inv7_ikk_respE, auto)
qed auto


end

