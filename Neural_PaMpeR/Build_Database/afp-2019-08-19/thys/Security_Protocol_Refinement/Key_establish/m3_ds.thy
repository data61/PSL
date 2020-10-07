(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Key_establish/m3_ds.thy (Isabelle/HOL 2016-1)
  ID:      $Id: m3_ds.thy 132890 2016-12-24 10:25:57Z csprenge $
  Authors: Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Ivano Somaini, ETH Zurich <somainii@student.ethz.ch>

  Key distribution protocols
  Level 3: Denning-Sacco protocol

  Copyright (c) 2009-2016 Christoph Sprenger, Ivano Somaini
  Licence: LGPL

*******************************************************************************)

section \<open>Denning-Sacco protocol (L3)\<close>

theory m3_ds imports m2_ds "../Refinement/Message"
begin

text \<open>
We model the Denning-Sacco protocol:
\[
\begin{array}{lll}
  \mathrm{M1.} & A \rightarrow S: & A, B \\ 
  \mathrm{M2.} & S \rightarrow A: & \{Kab, B, Ts, Na, \{Kab, A, Ts\}_{Kbs} \}_{Kas} \\
  \mathrm{M3.} & A \rightarrow B: & \{Kab, A, Ts\}_{Kbs}
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
  "m3_obs s \<equiv> \<lparr> runs = runs s, leak = leak s, clk = clk s \<rparr>"

type_synonym
  m3_pred = "m3_state set"

type_synonym
  m3_trans = "(m3_state \<times> m3_state) set"


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

text \<open>Protocol events.\<close>

definition     \<comment> \<open>by @{term "A"}, refines @{term "m2_step1"}\<close>
  m3_step1 :: "[rid_t, agent, agent] \<Rightarrow> m3_trans"
where
  "m3_step1 Ra A B \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    Ra \<notin> dom (runs s) \<and>                                 \<comment> \<open>\<open>Ra\<close> is fresh\<close>

    \<comment> \<open>actions:\<close>
    s1 = s\<lparr>
      runs := (runs s)(Ra \<mapsto> (Init, [A, B], [])),
      IK := insert \<lbrace>Agent A, Agent B\<rbrace> (IK s)        \<comment> \<open>send \<open>M1\<close>\<close>
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "B"}, refines @{term "m2_step2"}\<close>
  m3_step2 :: "[rid_t, agent, agent] \<Rightarrow> m3_trans"
where
  "m3_step2 \<equiv> m1_step2"

definition     \<comment> \<open>by @{text "Server"}, refines @{term m2_step3}\<close>
  m3_step3 :: "[rid_t, agent, agent, key, time] \<Rightarrow> m3_trans"
where
  "m3_step3 Rs A B Kab Ts \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    Rs \<notin> dom (runs s) \<and>                           \<comment> \<open>fresh server run\<close>
    Kab = sesK (Rs$sk) \<and>                          \<comment> \<open>fresh session key\<close>

    \<lbrace>Agent A, Agent B\<rbrace> \<in> IK s \<and>                   \<comment> \<open>recv \<open>M1\<close>\<close>
    Ts = clk s \<and>                                  \<comment> \<open>fresh timestamp\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>record session key and send \<open>M2\<close>\<close>
    s1 = s\<lparr>
      runs := (runs s)(Rs \<mapsto> (Serv, [A, B], [aNum Ts])),
      IK := insert (Crypt (shrK A)                        \<comment> \<open>send \<open>M2\<close>\<close>
                     \<lbrace>Key Kab, Agent B, Number Ts,
                        Crypt (shrK B) \<lbrace>Key Kab, Agent A, Number Ts\<rbrace>\<rbrace>)
                   (IK s)
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "A"}, refines @{term m2_step4}\<close>
  m3_step4 :: "[rid_t, agent, agent, key, time, msg] \<Rightarrow> m3_trans"
where
  "m3_step4 Ra A B Kab Ts X \<equiv> {(s, s1).

     \<comment> \<open>guards:\<close>
     runs s Ra = Some (Init, [A, B], []) \<and>           \<comment> \<open>key not yet recv'd\<close>

     Crypt (shrK A)                                  \<comment> \<open>recv \<open>M2\<close>\<close>
       \<lbrace>Key Kab, Agent B, Number Ts, X\<rbrace> \<in> IK s \<and>

     \<comment> \<open>check freshness of session key\<close>
     clk s < Ts + Ls \<and>

     \<comment> \<open>actions:\<close>
     \<comment> \<open>record session key and send \<open>M3\<close>\<close>
     s1 = s\<lparr>
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts])),
       IK := insert X (IK s)                         \<comment> \<open>send \<open>M3\<close>\<close>
     \<rparr>
  }"

definition     \<comment> \<open>by @{term "B"}, refines @{term m2_step5}\<close>
  m3_step5 :: "[rid_t, agent, agent, key, time] \<Rightarrow> m3_trans"
where
  "m3_step5 Rb A B Kab Ts \<equiv> {(s, s1).
     \<comment> \<open>guards:\<close>
     runs s Rb = Some (Resp, [A, B], []) \<and>             \<comment> \<open>key not yet recv'd\<close>

     Crypt (shrK B) \<lbrace>Key Kab, Agent A, Number Ts\<rbrace> \<in> IK s \<and>    \<comment> \<open>recv \<open>M3\<close>\<close>

     \<comment> \<open>ensure freshness of session key; replays with fresh authenticator ok!\<close>
     clk s < Ts + Ls \<and>

     \<comment> \<open>actions:\<close>
     \<comment> \<open>record session key\<close>
     s1 = s\<lparr>
       runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [aKey Kab, aNum Ts]))
     \<rparr>
  }"


text \<open>Clock tick event\<close>

definition   \<comment> \<open>refines @{term "m2_tick"}\<close>
  m3_tick :: "time \<Rightarrow> m3_trans"
where
  "m3_tick \<equiv> m1_tick"


text \<open>Session key compromise.\<close>

definition     \<comment> \<open>refines @{term m2_leak}\<close>
  m3_leak :: "rid_t \<Rightarrow> m3_trans"
where
  "m3_leak Rs \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    Rs \<in> dom (runs s) \<and>
    fst (the (runs s Rs)) = Serv \<and>         \<comment> \<open>compromise server run \<open>Rs\<close>\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>record session key as leaked and add it to intruder knowledge\<close>
    s1 = s\<lparr> leak := insert (sesK (Rs$sk)) (leak s),
            IK := insert (Key (sesK (Rs$sk))) (IK s) \<rparr>
  }"


text \<open>Intruder fake event. The following "Dolev-Yao" event generates all
intruder-derivable messages.\<close>

definition     \<comment> \<open>refines @{term "m2_fake"}\<close>
  m3_DY_fake :: "m3_trans"
where
  "m3_DY_fake \<equiv> {(s, s1).

     \<comment> \<open>actions:\<close>
     s1 = s\<lparr> IK := synth (analz (IK s)) \<rparr>       \<comment> \<open>take DY closure\<close>
  }"


(******************************************************************************)
subsection \<open>Transition system\<close>
(******************************************************************************)

definition
  m3_init :: "m3_pred"
where
  "m3_init \<equiv> { \<lparr>
     runs = Map.empty,
     leak = shrK`bad,
     clk = 0,
     IK = Key`shrK`bad
  \<rparr> }"

definition
  m3_trans :: "m3_trans" where
  "m3_trans \<equiv> (\<Union>A B Ra Rb Rs Kab Ts T X.
     m3_step1 Ra A B \<union>
     m3_step2 Rb A B \<union>
     m3_step3 Rs A B Kab Ts \<union>
     m3_step4 Ra A B Kab Ts X \<union>
     m3_step5 Rb A B Kab Ts \<union>
     m3_tick T \<union>
     m3_leak Rs \<union>
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
  m3_tick_def m3_leak_def m3_DY_fake_def

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
(******************************************************************************)

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
by (auto simp add: PO_hoare_defs m3_defs intro!: m3_inv1_lkeysecI)
   (auto dest!: Body)

lemma PO_m3_inv1_lkeysec [iff]: "reach m3 \<subseteq> m3_inv1_lkeysec"
by (rule inv_rule_incr) (fast+)


text \<open>Useful simplifier lemmas\<close>

lemma m3_inv1_lkeysec_for_parts [simp]:
  "\<lbrakk> s \<in> m3_inv1_lkeysec \<rbrakk> \<Longrightarrow> Key (shrK C) \<in> parts (IK s) \<longleftrightarrow> C \<in> bad"
by auto

lemma m3_inv1_lkeysec_for_analz [simp]:
  "\<lbrakk> s \<in> m3_inv1_lkeysec \<rbrakk> \<Longrightarrow> Key (shrK C) \<in> analz (IK s) \<longleftrightarrow> C \<in> bad"
by auto


subsubsection \<open>inv2: Ticket shape for honestly encrypted M2\<close>
(******************************************************************************)

definition
  m3_inv2_ticket :: "m3_pred"
where
  "m3_inv2_ticket \<equiv> {s. \<forall>A B T K X.
     A \<notin> bad \<longrightarrow>
     Crypt (shrK A) \<lbrace>Key K, Agent B, Number T, X\<rbrace> \<in> parts (IK s) \<longrightarrow>
       X = Crypt (shrK B) \<lbrace>Key K, Agent A, Number T\<rbrace> \<and> K \<in> range sesK
  }"

lemmas m3_inv2_ticketI = m3_inv2_ticket_def [THEN setc_def_to_intro, rule_format]
lemmas m3_inv2_ticketE [elim] = m3_inv2_ticket_def [THEN setc_def_to_elim, rule_format]
lemmas m3_inv2_ticketD = m3_inv2_ticket_def [THEN setc_def_to_dest, rule_format, rotated -1]


text \<open>Invariance proof.\<close>

lemma PO_m3_inv2_ticket_init [iff]:
  "init m3 \<subseteq> m3_inv2_ticket"
by (auto simp add: m3_defs intro!: m3_inv2_ticketI)

lemma PO_m3_inv2_ticket_trans [iff]:
  "{m3_inv2_ticket \<inter> m3_inv1_lkeysec} trans m3 {> m3_inv2_ticket}"
apply (auto simp add: PO_hoare_defs m3_defs intro!: m3_inv2_ticketI)
apply (auto dest: m3_inv2_ticketD)
\<comment> \<open>2 subgoals, from step4\<close>
apply (drule parts_cut, drule Body, auto dest: m3_inv2_ticketD)+
done

lemma PO_m3_inv2_ticket [iff]: "reach m3 \<subseteq> m3_inv2_ticket"
by (rule inv_rule_incr) (auto del: subsetI)


subsubsection \<open>inv3: Session keys not used to encrypt other session keys\<close>
(******************************************************************************)

text \<open>Session keys are not used to encrypt other keys. Proof requires
generalization to sets of session keys.\<close>

definition
  m3_inv3_sesK_compr :: "m3_pred"
where
  "m3_inv3_sesK_compr \<equiv> {s. \<forall>K KK.
     KK \<subseteq> range sesK \<longrightarrow>
     (Key K \<in> analz (Key`KK \<union> (IK s))) = (K \<in> KK \<or> Key K \<in> analz (IK s))
  }"

lemmas m3_inv3_sesK_comprI = m3_inv3_sesK_compr_def [THEN setc_def_to_intro, rule_format]
lemmas m3_inv3_sesK_comprE = m3_inv3_sesK_compr_def [THEN setc_def_to_elim, rule_format]
lemmas m3_inv3_sesK_comprD = m3_inv3_sesK_compr_def [THEN setc_def_to_dest, rule_format]

text \<open>Additional lemma\<close>
lemmas insert_commute_Key = insert_commute [where x="Key K" for K]

lemmas m3_inv3_sesK_compr_simps =
  m3_inv3_sesK_comprD
  m3_inv3_sesK_comprD [where KK="{Kab}" for Kab, simplified]
  m3_inv3_sesK_comprD [where KK="insert Kab KK" for Kab KK, simplified]
  insert_commute_Key    \<comment> \<open>to get the keys to the front\<close>


text \<open>Invariance proof.\<close>

lemma PO_m3_inv3_sesK_compr_step4:
  "{m3_inv3_sesK_compr \<inter> m3_inv2_ticket \<inter> m3_inv1_lkeysec}
      m3_step4 Ra A B Kab Ts X
   {> m3_inv3_sesK_compr}"
proof -
  { fix K KK s
    assume H:
      "s \<in> m3_inv1_lkeysec" "s \<in> m3_inv3_sesK_compr" "s \<in> m3_inv2_ticket"
      "runs s Ra = Some (Init, [A, B], [])"
      "KK \<subseteq> range sesK"
      "Crypt (shrK A) \<lbrace>Key Kab, Agent B, Number Ts, X\<rbrace> \<in> analz (IK s)"
    have
      "(Key K \<in> analz (insert X (Key ` KK \<union> IK s))) =
          (K \<in> KK \<or> Key K \<in> analz (insert X (IK s)))"
    proof (cases "A \<in> bad")
      case True show ?thesis
      proof -
        note H
      moreover
        with \<open>A \<in> bad\<close> have "X \<in> analz (IK s)"
        by (auto dest!: Decrypt)
      moreover
        hence "X \<in> analz (Key ` KK \<union> IK s)"
        by (auto intro: analz_mono [THEN [2] rev_subsetD])
      ultimately
        show ?thesis
        by (auto simp add: m3_inv3_sesK_compr_simps analz_insert_eq)
      qed
    next
      case False thus ?thesis using H
      by (fastforce simp add: m3_inv3_sesK_compr_simps dest!: m3_inv2_ticketD [OF analz_into_parts])
    qed
  }
  thus ?thesis
  by (auto simp add: PO_hoare_defs m3_defs intro!: m3_inv3_sesK_comprI dest!: analz_Inj_IK)
qed


text \<open>All together now.\<close>

lemmas PO_m3_inv3_sesK_compr_trans_lemmas =
  PO_m3_inv3_sesK_compr_step4

lemma PO_m3_inv3_sesK_compr_init [iff]:
  "init m3 \<subseteq> m3_inv3_sesK_compr"
by (auto simp add: m3_defs intro!: m3_inv3_sesK_comprI)

lemma PO_m3_inv3_sesK_compr_trans [iff]:
  "{m3_inv3_sesK_compr \<inter> m3_inv2_ticket \<inter> m3_inv1_lkeysec}
     trans m3
   {> m3_inv3_sesK_compr}"
by (auto simp add: m3_def m3_trans_def intro!: PO_m3_inv3_sesK_compr_trans_lemmas)
   (auto simp add: PO_hoare_defs m3_defs m3_inv3_sesK_compr_simps intro!: m3_inv3_sesK_comprI)

lemma PO_m3_inv3_sesK_compr [iff]: "reach m3 \<subseteq> m3_inv3_sesK_compr"
by (rule_tac J="m3_inv2_ticket \<inter> m3_inv1_lkeysec" in inv_rule_incr) (auto)


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
    "\<lbrace>Agent A, Agent B\<rbrace> \<in> H
  \<Longrightarrow> Insec A B (Msg []) \<in> abs_msg H"
| am_M2a:
    "Crypt (shrK C) \<lbrace>Key K, Agent B, Number T, X\<rbrace> \<in> H
  \<Longrightarrow> Secure Sv C (Msg [aAgt B, aKey K, aNum T]) \<in> abs_msg H"
| am_M2b:
    "Crypt (shrK C) \<lbrace>Key K, Agent A, Number T\<rbrace> \<in> H
  \<Longrightarrow> Secure Sv C (Msg [aKey K, aAgt A, aNum T]) \<in> abs_msg H"


text \<open>R23: The simulation relation. This is a data refinement of
the insecure and secure channels of refinement 2.\<close>

definition
  R23_msgs :: "(m2_state \<times> m3_state) set" where
  "R23_msgs \<equiv> {(s, t). abs_msg (parts (IK t)) \<subseteq> chan s }"

definition
  R23_keys :: "(m2_state \<times> m3_state) set" where
  "R23_keys \<equiv> {(s, t). \<forall>KK K. KK \<subseteq> range sesK \<longrightarrow>
     Key K \<in> analz (Key`KK \<union> (IK t)) \<longrightarrow> aKey K \<in> extr (aKey`KK \<union> ik0) (chan s)
  }"

definition
  R23_pres :: "(m2_state \<times> m3_state) set" where
  "R23_pres \<equiv> {(s, t). runs s = runs t \<and> clk s = clk t \<and> leak s = leak t}"

definition
  R23 :: "(m2_state \<times> m3_state) set" where
  "R23 \<equiv> R23_msgs \<inter> R23_keys \<inter> R23_pres"

lemmas R23_defs =
  R23_def R23_msgs_def R23_keys_def R23_pres_def


text \<open>The mediator function is the identity here.\<close>

definition
  med32 :: "m3_obs \<Rightarrow> m2_obs" where
  "med32 \<equiv> id"


lemmas R23_msgsI = R23_msgs_def [THEN rel_def_to_intro, simplified, rule_format]
lemmas R23_msgsE [elim] = R23_msgs_def [THEN rel_def_to_elim, simplified, rule_format]

lemmas R23_keysI = R23_keys_def [THEN rel_def_to_intro, simplified, rule_format]
lemmas R23_keysE [elim] = R23_keys_def [THEN rel_def_to_elim, simplified, rule_format]

lemmas R23_presI = R23_pres_def [THEN rel_def_to_intro, simplified, rule_format]
lemmas R23_presE [elim] = R23_pres_def [THEN rel_def_to_elim, simplified, rule_format]

lemmas R23_intros = R23_msgsI R23_keysI R23_presI


text \<open>Lemmas for various instantiations (for keys).\<close>

lemmas R23_keys_dest = R23_keys_def [THEN rel_def_to_dest, simplified, rule_format, rotated 2]
lemmas R23_keys_dests =
  R23_keys_dest
  R23_keys_dest [where KK="{}", simplified]
  R23_keys_dest [where KK="{K'}" for K', simplified]
  R23_keys_dest [where KK="insert K' KK" for K' KK, simplified, OF _ _ conjI]


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
\<comment> \<open>4 subgoals, deal with replays first\<close>
apply (blast)
defer 1 apply (blast)
\<comment> \<open>remaining 2 subgoals are real fakes\<close>
apply (rule fake_StatCh, auto dest: R23_keys_dests)+
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
     (m2_step1 Ra A B), (m3_step1 Ra A B)
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m3_defs intro!: R23_intros)
   (auto)

lemma PO_m3_step2_refines_m2_step2:
  "{R23}
     (m2_step2 Rb A B), (m3_step2 Rb A B)
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m3_defs intro!: R23_intros)
   (auto)

lemma PO_m3_step3_refines_m2_step3:
  "{R23 \<inter> (m2_inv3a_sesK_compr) \<times> (m3_inv3_sesK_compr \<inter> m3_inv1_lkeysec)}
     (m2_step3 Rs A B Kab Ts), (m3_step3 Rs A B Kab Ts)
   {> R23}"
proof -
  { fix s t
    assume H:
      "(s, t) \<in> R23_msgs" "(s, t) \<in> R23_keys" "(s, t) \<in> R23_pres"
      "s \<in> m2_inv3a_sesK_compr" "t \<in> m3_inv3_sesK_compr" "t \<in> m3_inv1_lkeysec"
      "Kab = sesK (Rs$sk)" "Rs \<notin> dom (runs t)"
      "\<lbrace>Agent A, Agent B\<rbrace> \<in> parts (IK t)"
    let ?s'=
      "s\<lparr> runs := runs s(Rs \<mapsto> (Serv, [A, B], [aNum (clk t)])),
          chan := insert (Secure Sv A (Msg [aAgt B, aKey Kab, aNum (clk t)]))
                 (insert (Secure Sv B (Msg [aKey Kab, aAgt A, aNum (clk t)])) (chan s)) \<rparr>"
    let ?t'=
      "t\<lparr> runs := runs t(Rs \<mapsto> (Serv, [A, B], [aNum (clk t)])),
          IK := insert
                  (Crypt (shrK A)
                     \<lbrace> Key Kab, Agent B, Number (clk t),
                       Crypt (shrK B) \<lbrace> Key Kab, Agent A, Number (clk t) \<rbrace>\<rbrace>)
                  (IK t) \<rparr>"
    have "(?s', ?t') \<in> R23_msgs" using H
    by (-) (rule R23_intros, auto)
  moreover
    have "(?s', ?t') \<in> R23_keys" using H
    by (-) (rule R23_intros,
            auto simp add: m2_inv3a_sesK_compr_simps m3_inv3_sesK_compr_simps dest: R23_keys_dests)
  moreover
    have "(?s', ?t') \<in> R23_pres" using H
    by (-) (rule R23_intros, auto)
  moreover
    note calculation
  }
  thus ?thesis by (auto simp add: PO_rhoare_defs R23_def m3_defs)
qed

lemma PO_m3_step4_refines_m2_step4:
  "{R23 \<inter>
    UNIV \<times> (m3_inv3_sesK_compr \<inter> m3_inv2_ticket \<inter> m3_inv1_lkeysec)}
     (m2_step4 Ra A B Kab Ts), (m3_step4 Ra A B Kab Ts X)
   {> R23}"
proof -
  { fix s t
    assume H:
      "(s, t) \<in> R23_msgs" "(s, t) \<in> R23_keys" "(s, t) \<in> R23_pres"
      "t \<in> m3_inv3_sesK_compr" "t \<in> m3_inv2_ticket"  "t \<in> m3_inv1_lkeysec"
      "runs t Ra = Some (Init, [A, B], [])"
      "Crypt (shrK A) \<lbrace>Key Kab, Agent B, Number Ts, X\<rbrace> \<in> analz (IK t)"
    let ?s' = "s\<lparr> runs := runs s(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts])) \<rparr>"
    and ?t' = "t\<lparr> runs := runs t(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts])),
                 IK := insert X  (IK t) \<rparr>"
    from H have
      "Secure Sv A (Msg [aAgt B, aKey Kab, aNum Ts]) \<in> chan s"
      by (auto)
  moreover
    have "X \<in> parts (IK t)" using H
      by (auto dest!: Body MPair_parts)
    hence "(?s', ?t') \<in> R23_msgs" using H
      by (auto intro!: R23_intros) (auto)
  moreover
    have "(?s', ?t') \<in> R23_keys"
    proof (cases)
      assume "A \<in> bad" show ?thesis
      proof -
        note H
      moreover
        hence "X \<in> analz (IK t)" using \<open>A \<in> bad\<close>
          by (-) (drule Decrypt, auto)
      ultimately
        show ?thesis
          by (-) (rule R23_intros, auto dest!: analz_cut intro: analz_monotonic)
      qed
    next
      assume "A \<notin> bad" show ?thesis
      proof -
        note H
      moreover
        with \<open>A \<notin> bad\<close> have
          "X = Crypt (shrK B) \<lbrace>Key Kab, Agent A, Number Ts \<rbrace> \<and> Kab \<in> range sesK"
          by (auto dest!: m3_inv2_ticketD)
      moreover
        { assume H1: "Key (shrK B) \<in> analz (IK t)"
          have "aKey Kab \<in> extr ik0 (chan s)"
          proof -
            note calculation
          moreover
            hence "Secure Sv B (Msg [aKey Kab, aAgt A, aNum Ts]) \<in> chan s"
              by (-) (drule analz_into_parts, drule Body, elim MPair_parts, auto)
          ultimately
            show ?thesis using H1 by auto
          qed
        }
      ultimately show ?thesis
        by (-) (rule R23_intros, auto simp add: m3_inv3_sesK_compr_simps)
      qed
    qed
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
     (m2_step5 Rb A B Kab Ts), (m3_step5 Rb A B Kab Ts)
   {> R23}"
by (auto simp add: PO_rhoare_defs R23_def m3_defs intro!: R23_intros)
   (auto)

lemma PO_m3_tick_refines_m2_tick:
  "{R23}
    (m2_tick T), (m3_tick T)
   {>R23}"
by (auto simp add: PO_rhoare_defs R23_def m3_defs intro!: R23_intros)
   (auto)


text \<open>Intruder events.\<close>

lemma PO_m3_leak_refines_m2_leak:
  "{R23}
    (m2_leak Rs), (m3_leak Rs)
   {>R23}"
by (auto simp add: PO_rhoare_defs R23_def m3_defs intro!: R23_intros)
   (auto dest: R23_keys_dests)

lemma PO_m3_DY_fake_refines_m2_fake:
  "{R23 \<inter> UNIV \<times> (m3_inv1_lkeysec)}
     m2_fake, m3_DY_fake
   {> R23}"
apply (auto simp add: PO_rhoare_defs R23_def m3_defs intro!: R23_intros del: abs_msg.cases)
apply (auto intro: abs_msg_DY_subset_fakeable [THEN subsetD] del: abs_msg.cases
            dest: R23_keys_dests)
done


text \<open>All together now...\<close>

lemmas PO_m3_trans_refines_m2_trans =
  PO_m3_step1_refines_m2_step1 PO_m3_step2_refines_m2_step2
  PO_m3_step3_refines_m2_step3 PO_m3_step4_refines_m2_step4
  PO_m3_step5_refines_m2_step5 PO_m3_tick_refines_m2_tick
  PO_m3_leak_refines_m2_leak PO_m3_DY_fake_refines_m2_fake


lemma PO_m3_refines_init_m2 [iff]:
  "init m3 \<subseteq> R23``(init m2)"
by (auto simp add: R23_def m3_defs ik0_def intro!: R23_intros)

lemma PO_m3_refines_trans_m2 [iff]:
  "{R23 \<inter>
    (m2_inv3a_sesK_compr) \<times> (m3_inv3_sesK_compr \<inter> m3_inv2_ticket \<inter> m3_inv1_lkeysec)}
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
     (R23 \<inter> (m2_inv3a_sesK_compr) \<times> (m3_inv3_sesK_compr \<inter> m3_inv2_ticket \<inter> m3_inv1_lkeysec))
     med32 m2 m3"
by (rule Refinement_using_invariants) (auto)

lemma m3_implements_m2 [iff]:
  "implements med32 m2 m3"
by (rule refinement_soundness) (auto)


end

