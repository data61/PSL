(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Key_establish/m3_kerberos5.thy (Isabelle/HOL 2016-1)
  ID:      $Id: m3_kerberos5.thy 132890 2016-12-24 10:25:57Z csprenge $
  Authors: Ivano Somaini, ETH Zurich <somainii@student.ethz.ch>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>

  Key distribution protocols
  Third refinement: core Kerberos V

  Copyright (c) 2009-2016 Ivano Somaini, Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Core Kerberos 5 (L3)\<close>

theory m3_kerberos5 imports m2_kerberos "../Refinement/Message"
begin

text \<open>
We model the core Kerberos 5 protocol:
\[
\begin{array}{lll}
  \mathrm{M1.} & A \rightarrow S: & A, B, Na \\ 
  \mathrm{M2.} & S \rightarrow A: & \{Kab, B, Ts, Na\}_{Kas}, \{Kab, A, Ts\}_{Kbs} \\
  \mathrm{M3.} & A \rightarrow B: & \{A, Ta\}_{Kab}, \{Kab, A, Ts\}_{Kbs} \\
  \mathrm{M4.} & B \rightarrow A: & \{Ta\}_{Kab} \\
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


text \<open>Observable state:
@{term "runs"}, @{term "leak"}, @{term "clk"}, and @{term "cache"}.\<close>

type_synonym
  m3_obs = "m2_obs"

definition
  m3_obs :: "m3_state \<Rightarrow> m3_obs" where
  "m3_obs s \<equiv> \<lparr> runs = runs s, leak = leak s, clk = clk s, cache = cache s \<rparr>"

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
    Ra \<notin> dom (runs s) \<and>                  \<comment> \<open>\<open>Ra\<close> is fresh\<close>
    Na = Ra$na \<and>                         \<comment> \<open>generated nonce\<close>

    \<comment> \<open>actions:\<close>
    s1 = s\<lparr>
      runs := (runs s)(Ra \<mapsto> (Init, [A, B], [])),
      IK := insert \<lbrace>Agent A, Agent B, Nonce Na\<rbrace> (IK s)   \<comment> \<open>send M1\<close>
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "B"}, refines @{term "m2_step2"}\<close>
  m3_step2 :: "[rid_t, agent, agent] \<Rightarrow> m3_trans"
where
  "m3_step2 \<equiv> m1_step2"

definition     \<comment> \<open>by @{text "Server"}, refines @{term m2_step3}\<close>
  m3_step3 :: "[rid_t, agent, agent, key, nonce, time] \<Rightarrow> m3_trans"
where
  "m3_step3 Rs A B Kab Na Ts \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    Rs \<notin> dom (runs s) \<and>                          \<comment> \<open>fresh server run\<close>
    Kab = sesK (Rs$sk) \<and>                          \<comment> \<open>fresh session key\<close>

    \<lbrace>Agent A, Agent B, Nonce Na\<rbrace> \<in> IK s \<and>    \<comment> \<open>recv \<open>M1\<close>\<close>
    Ts = clk s \<and>                                 \<comment> \<open>fresh timestamp\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>record session key and send \<open>M2\<close>\<close>
    s1 = s\<lparr>
      runs := (runs s)(Rs \<mapsto> (Serv, [A, B], [aNon Na, aNum Ts])),
      IK := insert \<lbrace>Crypt (shrK A) \<lbrace>Key Kab, Agent B, Number Ts, Nonce Na\<rbrace>,
                      Crypt (shrK B) \<lbrace>Key Kab, Agent A, Number Ts\<rbrace>\<rbrace>
               (IK s)
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "A"}, refines @{term m2_step4}\<close>
  m3_step4 :: "[rid_t, agent, agent, nonce, key, time, time, msg] \<Rightarrow> m3_trans"
where
  "m3_step4 Ra A B Na Kab Ts Ta X \<equiv> {(s, s1).

     \<comment> \<open>guards:\<close>
     runs s Ra = Some (Init, [A, B], []) \<and>           \<comment> \<open>key not yet recv'd\<close>
     Na = Ra$na \<and>                                    \<comment> \<open>generated nonce\<close>

     \<lbrace>Crypt (shrK A)                               \<comment> \<open>recv \<open>M2\<close>\<close>
          \<lbrace>Key Kab, Agent B, Number Ts, Nonce Na\<rbrace>, X\<rbrace> \<in> IK s \<and>

     \<comment> \<open>read current time\<close>
     Ta = clk s \<and>

     \<comment> \<open>check freshness of session key\<close>
     clk s < Ts + Ls \<and>

     \<comment> \<open>actions:\<close>
     \<comment> \<open>record session key and send \<open>M3\<close>\<close>
     s1 = s\<lparr>
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta])),
       IK := insert \<lbrace>Crypt Kab \<lbrace>Agent A, Number Ta\<rbrace>, X\<rbrace> (IK s)  \<comment> \<open>\<open>M3\<close>\<close>
     \<rparr>
  }"

definition     \<comment> \<open>by @{term "B"}, refines @{term m2_step5}\<close>
  m3_step5 :: "[rid_t, agent, agent, key, time, time] \<Rightarrow> m3_trans"
where
  "m3_step5 Rb A B Kab Ts Ta \<equiv> {(s, s1).
     \<comment> \<open>guards:\<close>
     runs s Rb = Some (Resp, [A, B], []) \<and>             \<comment> \<open>key not yet recv'd\<close>

     \<lbrace>Crypt Kab \<lbrace>Agent A, Number Ta\<rbrace>,            \<comment> \<open>recv \<open>M3\<close>\<close>
        Crypt (shrK B) \<lbrace>Key Kab, Agent A, Number Ts\<rbrace>\<rbrace> \<in> IK s \<and>

     \<comment> \<open>ensure freshness of session key\<close>
     clk s < Ts + Ls \<and>

     \<comment> \<open>check authenticator's validity and replay; 'replays' with fresh authenticator ok!\<close>
     clk s < Ta + La \<and>
     (B, Kab, Ta) \<notin> cache s \<and>

     \<comment> \<open>actions:\<close>
     \<comment> \<open>record session key\<close>
     s1 = s\<lparr>
       runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [aKey Kab, aNum Ts, aNum Ta])),
       cache := insert (B, Kab, Ta) (cache s),
       IK := insert (Crypt Kab (Number Ta)) (IK s)              \<comment> \<open>send \<open>M4\<close>\<close>
     \<rparr>
  }"

definition     \<comment> \<open>by @{term "A"}, refines @{term m2_step6}\<close>
  m3_step6 :: "[rid_t, agent, agent, nonce, key, time, time] \<Rightarrow> m3_trans"
where
  "m3_step6 Ra A B Na Kab Ts Ta \<equiv> {(s, s').
     \<comment> \<open>guards:\<close>
     runs s Ra = Some (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta]) \<and>  \<comment> \<open>knows key\<close>
     Na = Ra$na \<and>                                    \<comment> \<open>generated nonce\<close>
     clk s < Ts + Ls \<and>                               \<comment> \<open>check session key's recentness\<close>

     Crypt Kab (Number Ta) \<in> IK s \<and>                  \<comment> \<open>recv \<open>M4\<close>\<close>

     \<comment> \<open>actions:\<close>
     s' = s\<lparr>
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta, END]))
     \<rparr>
  }"

text \<open>Clock tick event\<close>

definition   \<comment> \<open>refines @{term "m2_tick"}\<close>
  m3_tick :: "time \<Rightarrow> m3_trans"
where
  "m3_tick \<equiv> m1_tick"


text \<open>Purge event: purge cache of expired timestamps\<close>

definition     \<comment> \<open>refines @{term "m2_purge"}\<close>
  m3_purge :: "agent \<Rightarrow> m3_trans"
where
  "m3_purge \<equiv> m1_purge"


text \<open>Session key compromise.\<close>

definition     \<comment> \<open>refines @{term m2_leak}\<close>
  m3_leak :: "[rid_t, agent, agent, nonce, time] \<Rightarrow> m3_trans"
where
  "m3_leak Rs A B Na Ts \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    runs s Rs = Some (Serv, [A, B], [aNon Na, aNum Ts]) \<and>
    (clk s \<ge> Ts + Ls) \<and>             \<comment> \<open>only compromise 'old' session keys\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>record session key as leaked and add it to intruder knowledge\<close>
    s1 = s\<lparr> leak := insert (sesK (Rs$sk), A, B, Na, Ts) (leak s),
            IK := insert (Key (sesK (Rs$sk))) (IK s) \<rparr>
  }"

text \<open>Intruder fake event. The following "Dolev-Yao" event generates all
intruder-derivable messages.\<close>

definition     \<comment> \<open>refines @{term "m2_fake"}\<close>
  m3_DY_fake :: "m3_trans"
where
  "m3_DY_fake \<equiv> {(s, s1).

     \<comment> \<open>actions:\<close>
     s1 = s(| IK := synth (analz (IK s)) |)       \<comment> \<open>take DY closure\<close>
  }"


(******************************************************************************)
subsection \<open>Transition system\<close>
(******************************************************************************)

definition
  m3_init :: "m3_pred"
where
  "m3_init \<equiv> { \<lparr>
     runs = Map.empty,
     leak = shrK`bad \<times> {undefined},
     clk = 0,
     cache = {},
     IK = Key`shrK`bad
  \<rparr> }"

definition
  m3_trans :: "m3_trans" where
  "m3_trans \<equiv> (\<Union>A B Ra Rb Rs Na Kab Ts Ta T X.
     m3_step1 Ra A B Na \<union>
     m3_step2 Rb A B \<union>
     m3_step3 Rs A B Kab Na Ts \<union>
     m3_step4 Ra A B Na Kab Ts Ta X \<union>
     m3_step5 Rb A B Kab Ts Ta \<union>
     m3_step6 Ra A B Na Kab Ts Ta \<union>
     m3_tick T \<union>
     m3_purge A \<union>
     m3_leak Rs A B Na Ts \<union>
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

lemmas m3_loc_defs =
  m3_def m3_init_def m3_trans_def m3_obs_def
  m3_step1_def m3_step2_def m3_step3_def m3_step4_def m3_step5_def
  m3_step6_def m3_tick_def m3_purge_def m3_leak_def m3_DY_fake_def

lemmas m3_defs = m3_loc_defs m2_defs


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

text \<open>Specialized injection that we can apply more aggressively.\<close>

lemmas analz_Inj_IK = analz.Inj [where H="IK s" for s]
lemmas parts_Inj_IK = parts.Inj [where H="IK s" for s]

declare parts_Inj_IK [dest!]

declare analz_into_parts [dest]


subsubsection \<open>inv1: Secrecy of pre-distributed shared keys\<close>
(*inv*************************************************************************)

definition
  m3_inv1_lkeysec :: "m3_pred"
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
by (auto simp add: m3_defs intro!: m3_inv1_lkeysecI)

lemma PO_m3_inv1_lkeysec_trans [iff]:
  "{m3_inv1_lkeysec} trans m3 {> m3_inv1_lkeysec}"
by (fastforce simp add: PO_hoare_defs m3_defs intro!: m3_inv1_lkeysecI)

lemma PO_m3_inv1_lkeysec [iff]: "reach m3 \<subseteq> m3_inv1_lkeysec"
by (rule inv_rule_basic) (fast+)


text \<open>Useful simplifier lemmas\<close>

lemma m3_inv1_lkeysec_for_parts [simp]:
  "\<lbrakk> s \<in> m3_inv1_lkeysec \<rbrakk> \<Longrightarrow> Key (shrK C) \<in> parts (IK s) \<longleftrightarrow> C \<in> bad"
by auto

lemma m3_inv1_lkeysec_for_analz [simp]:
  "\<lbrakk> s \<in> m3_inv1_lkeysec \<rbrakk> \<Longrightarrow> Key (shrK C) \<in> analz (IK s) \<longleftrightarrow> C \<in> bad"
by auto


subsubsection \<open>inv2: Session keys not used to encrypt other session keys\<close>
(*invh*************************************************************************)

text \<open>Session keys are not used to encrypt other keys. Proof requires
generalization to sets of session keys.

NOTE: This invariant will be inherted from the corresponding L2 invariant
using the simulation relation.
\<close>

definition
  m3_inv2_sesK_compr :: "m3_pred"
where
  "m3_inv2_sesK_compr \<equiv> {s. \<forall>K KK.
     KK \<subseteq> range sesK \<longrightarrow>
     (Key K \<in> analz (Key`KK \<union> (IK s))) = (K \<in> KK \<or> Key K \<in> analz (IK s))
  }"

lemmas m3_inv2_sesK_comprI = m3_inv2_sesK_compr_def [THEN setc_def_to_intro, rule_format]
lemmas m3_inv2_sesK_comprE = m3_inv2_sesK_compr_def [THEN setc_def_to_elim, rule_format]
lemmas m3_inv2_sesK_comprD = m3_inv2_sesK_compr_def [THEN setc_def_to_dest, rule_format]

text \<open>Additional lemma\<close>
lemmas insert_commute_Key = insert_commute [where x="Key K" for K]

lemmas m3_inv2_sesK_compr_simps =
  m3_inv2_sesK_comprD
  m3_inv2_sesK_comprD [where KK="insert Kab KK" for Kab KK, simplified]
  m3_inv2_sesK_comprD [where KK="{Kab}" for Kab, simplified]
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
    "\<lbrace>Agent A, Agent B, Nonce N\<rbrace> \<in> H
  \<Longrightarrow> Insec A B (Msg [aNon N]) \<in> abs_msg H"
| am_M2a:
    "Crypt (shrK C) \<lbrace>Key K, Agent B, Number T, Nonce N\<rbrace> \<in> H
  \<Longrightarrow> Secure Sv C (Msg [aKey K, aAgt B, aNum T, aNon N]) \<in> abs_msg H"
| am_M2b:
    "Crypt (shrK C) \<lbrace>Key K,  Agent A, Number T\<rbrace> \<in> H
  \<Longrightarrow> Secure Sv C (Msg [aKey K, aAgt A, aNum T]) \<in> abs_msg H"
| am_M3:
    "Crypt K \<lbrace>Agent A, Number T\<rbrace> \<in> H
  \<Longrightarrow> dAuth K (Msg [aAgt A, aNum T]) \<in> abs_msg H"
| am_M4:
    "Crypt K (Number T) \<in> H
  \<Longrightarrow> dAuth K (Msg [aNum T]) \<in> abs_msg H"


text \<open>R23: The simulation relation. This is a data refinement of
the insecure and secure channels of refinement 2.\<close>

definition
  R23_msgs :: "(m2_state \<times> m3_state) set" where
  "R23_msgs \<equiv> {(s, t). abs_msg (parts (IK t)) \<subseteq> chan s }"

definition
  R23_keys :: "(m2_state \<times> m3_state) set" where
  "R23_keys \<equiv> {(s, t). \<forall>KK K. KK \<subseteq> range sesK \<longrightarrow>
     Key K \<in> analz (Key`KK \<union> (IK t)) \<longleftrightarrow> aKey K \<in> extr (aKey`KK \<union> ik0) (chan s)
  }"

definition
  R23_non :: "(m2_state \<times> m3_state) set" where
  "R23_non \<equiv> {(s, t). \<forall>KK N. KK \<subseteq> range sesK \<longrightarrow>
     Nonce N \<in> analz (Key`KK \<union> (IK t)) \<longleftrightarrow> aNon N \<in> extr (aKey`KK \<union> ik0) (chan s)
  }"

definition
  R23_pres :: "(m2_state \<times> m3_state) set" where
  "R23_pres \<equiv> {(s, t). runs s = runs t \<and> leak s = leak t \<and> clk s = clk t \<and> cache s = cache t}"

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
lemmas R23_msgsE' [elim] = R23_msgs_def [THEN rel_def_to_dest, simplified, rule_format, THEN subsetD]

lemmas R23_keysI = R23_keys_def [THEN rel_def_to_intro, simplified, rule_format]
lemmas R23_keysE [elim] = R23_keys_def [THEN rel_def_to_elim, simplified, rule_format]

lemmas R23_nonI = R23_non_def [THEN rel_def_to_intro, simplified, rule_format]
lemmas R23_nonE [elim] = R23_non_def [THEN rel_def_to_elim, simplified, rule_format]

lemmas R23_presI = R23_pres_def [THEN rel_def_to_intro, simplified, rule_format]
lemmas R23_presE [elim] = R23_pres_def [THEN rel_def_to_elim, simplified, rule_format]

lemmas R23_intros = R23_msgsI R23_keysI R23_nonI R23_presI


text \<open>Simplifier lemmas for various instantiations (keys and nonces).\<close>

lemmas R23_keys_simp = R23_keys_def [THEN rel_def_to_dest, simplified, rule_format]
lemmas R23_keys_simps =
  R23_keys_simp
  R23_keys_simp [where KK="{}", simplified]
  R23_keys_simp [where KK="{K'}" for K', simplified]
  R23_keys_simp [where KK="insert K' KK" for K' KK, simplified, OF _ conjI]

lemmas R23_non_simp = R23_non_def [THEN rel_def_to_dest, simplified, rule_format]
lemmas R23_non_simps =
  R23_non_simp
  R23_non_simp [where KK="{}", simplified]
  R23_non_simp [where KK="{K}" for K, simplified]
  R23_non_simp [where KK="insert K KK" for K KK, simplified, OF _ conjI]

lemmas R23_simps = R23_keys_simps R23_non_simps


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
apply (intro fake_StatCh fake_DynCh, auto simp add: R23_simps)+
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
by (auto simp add: PO_rhoare_defs R23_def m3_defs intro!: R23_intros) (auto)

lemma PO_m3_step2_refines_m2_step2:
  "{R23}
     (m2_step2 Rb A B), (m3_step2 Rb A B)
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m3_defs intro!: R23_intros)

lemma PO_m3_step3_refines_m2_step3:
  "{R23 \<inter> (m2_inv3a_sesK_compr) \<times> (m3_inv2_sesK_compr \<inter> m3_inv1_lkeysec)}
     (m2_step3 Rs A B Kab Na Ts), (m3_step3 Rs A B Kab Na Ts)
   {> R23}"
proof -
  { fix s t
    assume H:
      "(s, t) \<in> R23_msgs" "(s, t) \<in> R23_keys" "(s, t) \<in> R23_non"
      "(s, t) \<in> R23_pres"
      "s \<in> m2_inv3a_sesK_compr"
      "t \<in> m3_inv2_sesK_compr" "t \<in> m3_inv1_lkeysec"
      "Kab = sesK (Rs$sk)" "Rs \<notin> dom (runs t)"
      "\<lbrace> Agent A, Agent B, Nonce Na \<rbrace> \<in> parts (IK t)"
    let ?s'=
      "s\<lparr> runs := runs s(Rs \<mapsto> (Serv, [A, B], [aNon Na, aNum (clk t)])),
          chan := insert (Secure Sv A (Msg [aKey Kab, aAgt B, aNum (clk t), aNon Na]))
                 (insert (Secure Sv B (Msg [aKey Kab, aAgt A, aNum (clk t)])) (chan s)) \<rparr>"
    let ?t'=
      "t\<lparr> runs := runs t(Rs \<mapsto> (Serv, [A, B], [aNon Na, aNum (clk t)])),
          IK := insert
                  \<lbrace> Crypt (shrK A) \<lbrace> Key Kab, Agent B, Number (clk t), Nonce Na \<rbrace>,
                    Crypt (shrK B) \<lbrace> Key Kab, Agent A, Number (clk t) \<rbrace> \<rbrace>
                  (IK t) \<rparr>"
  \<comment> \<open>here we go\<close>
    have "(?s', ?t') \<in> R23_msgs" using H
    by (-) (rule R23_intros, auto)
  moreover
    have "(?s', ?t') \<in> R23_keys" using H
    by (-) (rule R23_intros,
            auto simp add: m2_inv3a_sesK_compr_simps m3_inv2_sesK_compr_simps,
            auto simp add: R23_keys_simps)
  moreover
    have "(?s', ?t') \<in> R23_non" using H
    by (-)
       (rule R23_intros,
        auto simp add: m2_inv3a_sesK_compr_simps m3_inv2_sesK_compr_simps R23_non_simps)
  moreover
    have "(?s', ?t') \<in> R23_pres" using H
    by (-) (rule R23_intros, auto)
  moreover
    note calculation
  }
  thus ?thesis
  by (auto simp add: PO_rhoare_defs R23_def m3_defs)
qed

lemma PO_m3_step4_refines_m2_step4:
  "{R23 \<inter> UNIV \<times> m3_inv1_lkeysec}
     (m2_step4 Ra A B Na Kab Ts Ta), (m3_step4 Ra A B Na Kab Ts Ta X)
   {> R23}"
proof -
  { fix s t
    assume H:
      "(s, t) \<in> R23_msgs" "(s, t) \<in> R23_keys" "(s, t) \<in> R23_non"
      "(s, t) \<in> R23_pres"  "t \<in> m3_inv1_lkeysec"
      "runs t Ra = Some (Init, [A, B], [])" "Na = Ra$na"
      "\<lbrace> Crypt (shrK A) \<lbrace>Key Kab, Agent B, Number Ts, Nonce Na\<rbrace>, X\<rbrace>  \<in> analz (IK t)"
    let ?s' = "s\<lparr> runs := runs s(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts, aNum (clk t)])),
                 chan := insert (dAuth Kab (Msg [aAgt A, aNum (clk t)])) (chan s) \<rparr>"
    and ?t' = "t\<lparr> runs := runs t(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts, aNum (clk t)])),
                 IK := insert \<lbrace>Crypt Kab \<lbrace>Agent A, Number (clk t)\<rbrace>, X\<rbrace> (IK t) \<rparr>"
    from H have
      "Secure Sv A (Msg [aKey Kab, aAgt B, aNum Ts, aNon Na]) \<in> chan s"
    by (auto dest!: analz_into_parts elim!: MPair_parts)
  moreover
    from H have "X \<in> parts (IK t)" by (auto)
    with H have "(?s', ?t') \<in> R23_msgs" by (auto intro!: R23_intros) (auto)
  moreover
    from H have "X \<in> analz (IK t)" by (auto)
    with H have "(?s', ?t') \<in> R23_keys"
    by (auto intro!: R23_intros) (auto dest!: analz_cut intro: analz_monotonic)
  moreover
    from H have "X \<in> analz (IK t)" by (auto)
    with H have "(?s', ?t') \<in> R23_non"
    by (auto intro!: R23_intros) (auto dest!: analz_cut intro: analz_monotonic)
  moreover
    have "(?s', ?t') \<in> R23_pres" using H
    by (auto intro!: R23_intros)
  moreover
    note calculation
  }
  thus ?thesis
  by (auto simp add: PO_rhoare_defs R23_def m3_defs dest!: analz_Inj_IK)
qed

lemma PO_m3_step5_refines_m2_step5:
  "{R23}
     (m2_step5 Rb A B Kab Ts Ta), (m3_step5 Rb A B Kab Ts Ta)
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m3_defs intro!: R23_intros)
   (auto)

lemma PO_m3_step6_refines_m2_step6:
  "{R23}
     (m2_step6 Ra A B Na Kab Ts Ta), (m3_step6 Ra A B Na Kab Ts Ta)
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m3_defs intro!: R23_intros)

lemma PO_m3_tick_refines_m2_tick:
  "{R23}
    (m2_tick T), (m3_tick T)
   {>R23}"
by (auto simp add: PO_rhoare_defs R23_def m3_defs intro!: R23_intros)

lemma PO_m3_purge_refines_m2_purge:
  "{R23}
     (m2_purge A), (m3_purge A)
   {>R23}"
by (auto simp add: PO_rhoare_defs R23_def m3_defs intro!: R23_intros)


text \<open>Intruder events.\<close>

lemma PO_m3_leak_refines_m2_leak:
  "{R23}
     (m2_leak Rs A B Na Ts), (m3_leak Rs A B Na Ts)
   {>R23}"
by (auto simp add: PO_rhoare_defs R23_def m3_defs R23_simps intro!: R23_intros)

lemma PO_m3_DY_fake_refines_m2_fake:
  "{R23 \<inter> m2_inv3a_sesK_compr \<times> (m3_inv2_sesK_compr \<inter> m3_inv1_lkeysec)}
     m2_fake, m3_DY_fake
   {> R23}"
apply (auto simp add: PO_rhoare_defs R23_def m3_defs intro!: R23_intros
            del: abs_msg.cases)
apply (auto intro: abs_msg_DY_subset_fakeable [THEN subsetD]
            del: abs_msg.cases)
apply (auto simp add: R23_simps)
done


text \<open>All together now...\<close>

lemmas PO_m3_trans_refines_m2_trans =
  PO_m3_step1_refines_m2_step1 PO_m3_step2_refines_m2_step2
  PO_m3_step3_refines_m2_step3 PO_m3_step4_refines_m2_step4
  PO_m3_step5_refines_m2_step5 PO_m3_step6_refines_m2_step6
  PO_m3_tick_refines_m2_tick PO_m3_purge_refines_m2_purge
  PO_m3_leak_refines_m2_leak PO_m3_DY_fake_refines_m2_fake


lemma PO_m3_refines_init_m2 [iff]:
  "init m3 \<subseteq> R23``(init m2)"
by (auto simp add: R23_def m3_defs intro!: R23_intros)

lemma PO_m3_refines_trans_m2 [iff]:
  "{R23 \<inter> (m2_inv3a_sesK_compr) \<times> (m3_inv2_sesK_compr \<inter> m3_inv1_lkeysec)}
     (trans m2), (trans m3)
   {> R23}"
by (auto simp add: m3_def m3_trans_def m2_def m2_trans_def)
   (blast intro!: PO_m3_trans_refines_m2_trans)+

lemma PO_m3_observation_consistent [iff]:
  "obs_consistent R23 med32 m2 m3"
by (auto simp add: obs_consistent_def R23_def med32_def m3_defs)


text \<open>Refinement result.\<close>

lemma m3_refines_m2 [iff]:
  "refines
     (R23 \<inter> (m2_inv3a_sesK_compr) \<times> (m3_inv1_lkeysec))
     med32 m2 m3"
proof -
  have "R23 \<inter> m2_inv3a_sesK_compr \<times> UNIV \<subseteq> UNIV \<times> m3_inv2_sesK_compr"
    by (auto simp add: R23_def R23_keys_simps intro!: m3_inv2_sesK_comprI)
  thus ?thesis
    by (-) (rule Refinement_using_invariants, auto)
qed

lemma m3_implements_m2 [iff]:
  "implements med32 m2 m3"
by (rule refinement_soundness) (auto)


subsection \<open>Inherited invariants\<close>
(******************************************************************************)

subsubsection \<open>inv3 (derived): Key secrecy for initiator\<close>
(*invh*************************************************************************)

definition
  m3_inv3_ikk_init :: "m3_state set"
where
  "m3_inv3_ikk_init \<equiv> {s. \<forall>A B Ra K Ts nl.
     runs s Ra = Some (Init, [A, B], aKey K # aNum Ts # nl) \<longrightarrow> A \<in> good \<longrightarrow> B \<in> good \<longrightarrow>
     Key K \<in> analz (IK s) \<longrightarrow>
       (K, A, B, Ra$na, Ts) \<in> leak s
  }"

lemmas m3_inv3_ikk_initI = m3_inv3_ikk_init_def [THEN setc_def_to_intro, rule_format]
lemmas m3_inv3_ikk_initE [elim] = m3_inv3_ikk_init_def [THEN setc_def_to_elim, rule_format]
lemmas m3_inv3_ikk_initD = m3_inv3_ikk_init_def [THEN setc_def_to_dest, rule_format, rotated 1]

lemma PO_m3_inv3_ikk_init: "reach m3 \<subseteq> m3_inv3_ikk_init"
proof (rule INV_from_Refinement_using_invariants [OF m3_refines_m2])
  show "Range (R23 \<inter> m2_inv3a_sesK_compr \<times> m3_inv1_lkeysec \<inter> m2_inv6_ikk_init \<times> UNIV)
      \<subseteq> m3_inv3_ikk_init"
    by (fastforce simp add: R23_def R23_keys_simps intro!: m3_inv3_ikk_initI)
qed auto


subsubsection \<open>inv4 (derived): Key secrecy for responder\<close>
(*invh*************************************************************************)

definition
  m3_inv4_ikk_resp :: "m3_state set"
where
  "m3_inv4_ikk_resp \<equiv> {s. \<forall>A B Rb K Ts nl.
     runs s Rb = Some (Resp, [A, B], aKey K # aNum Ts # nl) \<longrightarrow> A \<in> good \<longrightarrow> B \<in> good \<longrightarrow>
     Key K \<in> analz (IK s) \<longrightarrow>
       (\<exists>Na. (K, A, B, Na, Ts) \<in> leak s)
  }"

lemmas m3_inv4_ikk_respI = m3_inv4_ikk_resp_def [THEN setc_def_to_intro, rule_format]
lemmas m3_inv4_ikk_respE [elim] = m3_inv4_ikk_resp_def [THEN setc_def_to_elim, rule_format]
lemmas m3_inv4_ikk_respD = m3_inv4_ikk_resp_def [THEN setc_def_to_dest, rule_format, rotated 1]

lemma PO_m3_inv4_ikk_resp: "reach m3 \<subseteq> m3_inv4_ikk_resp"
proof (rule INV_from_Refinement_using_invariants [OF m3_refines_m2])
  show "Range (R23 \<inter> m2_inv3a_sesK_compr \<times> m3_inv1_lkeysec \<inter> m2_inv7_ikk_resp \<times> UNIV)
      \<subseteq> m3_inv4_ikk_resp"
    by (auto simp add: R23_def R23_keys_simps intro!: m3_inv4_ikk_respI)
       (elim m2_inv7_ikk_respE, auto)
qed auto


end
