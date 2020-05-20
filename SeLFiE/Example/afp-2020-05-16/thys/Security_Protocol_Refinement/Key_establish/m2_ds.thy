(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Key_establish/m2_ds.thy (Isabelle/HOL 2016-1)
  ID:      $Id: m2_ds.thy 132890 2016-12-24 10:25:57Z csprenge $
  Author:  Ivano Somaini, ETH Zurich <somainii@student.ethz.ch>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>

  Key distribution protocols
  Level 2: channel protocol, parallel version of Denning-Sacco

  Copyright (c) 2009-2016 Ivano Somaini and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Abstract Denning-Sacco protocol (L2)\<close>

theory m2_ds imports m1_ds "../Refinement/Channels"
begin

text \<open>
We model an abstract version of the Denning-Sacco protocol:
\[
\begin{array}{lll}
  \mathrm{M1.} & A \rightarrow S: & A, B \\ 
  \mathrm{M2.} & S \rightarrow A: & \{B, Kab, T,\{Kab, A, T\}_{Kbs} \}_{Kas} \\
  \mathrm{M3.} & A \rightarrow B: & \{Kab, A, T\}_{Kbs} \\
\end{array}
\]

This refinement introduces channels with security properties.  We model 
a parallel version of the DS protocol:
\[
\begin{array}{lll}
  \mathrm{M1.} & A \rightarrow S: & A, B \\ 
  \mathrm{M2a.} & S \rightarrow A: & \{B, Kab, T\}_{Kas} \\
  \mathrm{M2b.} & S \rightarrow B: & \{Kab, A, T\}_{Kbs} \\
\end{array}
\]
Message 1 is sent over an insecure channel, the other two message over
secure channels.
\<close>

declare domIff [simp, iff del]


(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>State and observations\<close>

record m2_state = "m1_state" +
  chan :: "chmsg set"              \<comment> \<open>channel messages\<close>

type_synonym 
  m2_obs = "m1_state" 

definition 
  m2_obs :: "m2_state \<Rightarrow> m2_obs" where
  "m2_obs s \<equiv> \<lparr> 
     runs = runs s,
     leak = leak s,
     clk = clk s
  \<rparr>"

type_synonym
  m2_pred = "m2_state set"

type_synonym
  m2_trans = "(m2_state \<times> m2_state) set"


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

text \<open>Protocol events.\<close>

definition     \<comment> \<open>by @{term "A"}, refines @{term "m1a_step1"}\<close>
  m2_step1 :: "[rid_t, agent, agent] \<Rightarrow> m2_trans"
where
  "m2_step1 Ra A B \<equiv> {(s, s1).

     \<comment> \<open>guards:\<close>
     Ra \<notin> dom (runs s) \<and>                                \<comment> \<open>\<open>Ra\<close> is fresh\<close>

     \<comment> \<open>actions:\<close>
     \<comment> \<open>create initiator thread and send message 1\<close>
     s1 = s\<lparr>
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [])),
       chan := insert (Insec A B (Msg [])) (chan s)     \<comment> \<open>send M1\<close>
     \<rparr>
  }"

definition     \<comment> \<open>by @{term "B"}, refines @{term "m1e_step2"}\<close>
  m2_step2 :: "[rid_t, agent, agent] \<Rightarrow> m2_trans"
where
  "m2_step2 \<equiv> m1_step2"

definition     \<comment> \<open>by @{text "Server"}, refines @{term m1e_step3}\<close>
  m2_step3 :: "[rid_t, agent, agent, key, time] \<Rightarrow> m2_trans"
where
  "m2_step3 Rs A B Kab Ts \<equiv> {(s, s1). 

     \<comment> \<open>guards:\<close>
     Rs \<notin> dom (runs s) \<and>                           \<comment> \<open>fresh server run\<close>
     Kab = sesK (Rs$sk) \<and>                          \<comment> \<open>fresh session key\<close>
     Ts = clk s \<and>                                  \<comment> \<open>fresh timestamp\<close> 

     Insec A B (Msg []) \<in> chan s \<and>                 \<comment> \<open>recv M1\<close>
   
     \<comment> \<open>actions:\<close>
     \<comment> \<open>record key and send messages 2 and 3\<close>
     s1 = s\<lparr>
       runs := (runs s)(Rs \<mapsto> (Serv, [A, B], [aNum Ts])), 
       chan := {Secure Sv A (Msg [aAgt B, aKey Kab, aNum Ts]),    \<comment> \<open>send \<open>M2a/b\<close>\<close>
                Secure Sv B (Msg [aKey Kab, aAgt A, aNum Ts])} \<union> chan s
     \<rparr>
  }"

definition     \<comment> \<open>by @{term "A"}, refines @{term m1e_step4}\<close>
  m2_step4 :: "[rid_t, agent, agent, key, time] \<Rightarrow> m2_trans"
where
  "m2_step4 Ra A B Kab Ts \<equiv> {(s, s1).

     \<comment> \<open>guards:\<close>
     runs s Ra = Some (Init, [A, B], []) \<and> 
     Secure Sv A (Msg [aAgt B, aKey Kab, aNum Ts]) \<in> chan s \<and>  \<comment> \<open>recv \<open>M2a\<close>\<close>

     clk s < Ts + Ls \<and>                              \<comment> \<open>ensure key freshness\<close>

     \<comment> \<open>actions:\<close>
     \<comment> \<open>record session key\<close>
     s1 = s\<lparr>
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts]))
     \<rparr>
  }"

definition     \<comment> \<open>by @{term "B"}, refines @{term m1e_step5}\<close>
  m2_step5 :: "[rid_t, agent, agent, key, time] \<Rightarrow> m2_trans"
where
  "m2_step5 Rb A B Kab Ts \<equiv> {(s, s1). 

     \<comment> \<open>guards:\<close>
     runs s Rb = Some (Resp, [A, B], []) \<and>
     Secure Sv B (Msg [aKey Kab, aAgt A, aNum Ts]) \<in> chan s \<and>  \<comment> \<open>recv \<open>M2b\<close>\<close>

     \<comment> \<open>ensure freshness of session key\<close>
     clk s < Ts + Ls \<and>

     \<comment> \<open>actions:\<close>
     \<comment> \<open>record session key\<close>
     s1 = s\<lparr>
       runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [aKey Kab, aNum Ts]))
     \<rparr>
  }"

text \<open>Clock tick event\<close>

definition     \<comment> \<open>refines @{term m1_tick}\<close>
  m2_tick :: "time \<Rightarrow> m2_trans" 
where
  "m2_tick \<equiv> m1_tick"


text \<open>Session key compromise.\<close>

definition     \<comment> \<open>refines @{term m1_leak}\<close> 
  m2_leak :: "rid_t \<Rightarrow> m2_trans"
where
  "m2_leak Rs \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    Rs \<in> dom (runs s) \<and>
    fst (the (runs s Rs)) = Serv \<and>         \<comment> \<open>compromise server run \<open>Rs\<close>\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>record session key as leaked;\<close>
    \<comment> \<open>intruder sends himself an insecure channel message containing the key\<close>
    s1 = s\<lparr> leak := insert (sesK (Rs$sk)) (leak s), 
            chan := insert (Insec undefined undefined (Msg [aKey (sesK (Rs$sk))])) (chan s) \<rparr> 
  }"


text \<open>Intruder fake event (new).\<close>

definition     \<comment> \<open>refines @{term Id}\<close> 
  m2_fake :: "m2_trans"
where
  "m2_fake \<equiv> {(s, s1). 

     \<comment> \<open>actions:\<close>
     s1 = s\<lparr>
       \<comment> \<open>close under fakeable messages\<close>
       chan := fake ik0 (dom (runs s)) (chan s) 
     \<rparr>
  }"


(******************************************************************************)
subsection \<open>Transition system\<close>
(******************************************************************************)

definition 
  m2_init :: "m2_pred"
where
  "m2_init \<equiv> { \<lparr>
     runs = Map.empty,
     leak = corrKey,
     clk = 0,
     chan = {}              \<comment> \<open>\<open>Channels.ik0\<close> contains \<open>aKey`corrKey\<close>\<close>
  \<rparr> }"

definition 
  m2_trans :: "m2_trans" where
  "m2_trans \<equiv> (\<Union>A B Ra Rb Rs Kab Ts T.
     m2_step1 Ra A B \<union>
     m2_step2 Rb A B \<union>
     m2_step3 Rs A B Kab Ts \<union>
     m2_step4 Ra A B Kab Ts \<union>
     m2_step5 Rb A B Kab Ts \<union>
     m2_tick T \<union>
     m2_leak Rs \<union>
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

lemmas m2_loc_defs = 
  m2_def m2_init_def m2_trans_def m2_obs_def
  m2_step1_def m2_step2_def m2_step3_def m2_step4_def m2_step5_def 
  m2_tick_def m2_leak_def m2_fake_def 

lemmas m2_defs = m2_loc_defs m1_defs


(******************************************************************************)
subsection \<open>Invariants and simulation relation\<close>
(******************************************************************************)

(*
subsubsection {* inv1: Key definedness [UNUSED] *}
(******************************************************************************)

text {* All session keys in channel messages stem from existing runs. *}

definition 
  m2_inv1_keys :: "m2_state set"
where 
  "m2_inv1_keys \<equiv> {s. \<forall>R.
     aKey (sesK (R$sk)) \<in> atoms (chan s) (* \<or> sesK (R$sk) \<in> leak s *) \<longrightarrow> 
       R \<in> dom (runs s)
  }"

lemmas m2_inv1_keysI = 
  m2_inv1_keys_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv1_keysE [elim] = 
  m2_inv1_keys_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv1_keysD = 
  m2_inv1_keys_def [THEN setc_def_to_dest, rule_format]


text {* Invariance proof. *}

lemma PO_m2_inv1_keys_init [iff]:
  "init m2 \<subseteq> m2_inv1_keys"
by (auto simp add: m2_defs intro!: m2_inv1_keysI)

lemma PO_m2_inv1_keys_trans [iff]:
  "{m2_inv1_keys} trans m2 {> m2_inv1_keys}"
by (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv1_keysI)
   (auto simp add: ik0_def dest: m2_inv1_keysD dom_lemmas)

lemma PO_m2_inv1_keys [iff]: "reach m2 \<subseteq> m2_inv1_keys"
by (rule inv_rule_basic) (auto)


subsubsection {* inv2: Definedness of used keys [UNUSED] *}
(******************************************************************************)

definition 
  m2_inv2_keys_for :: "m2_state set"
where 
  "m2_inv2_keys_for \<equiv> {s. \<forall>R.
     sesK (R$sk) \<in> keys_for (chan s) \<longrightarrow> R \<in> dom (runs s)
  }"

lemmas m2_inv2_keys_forI = 
  m2_inv2_keys_for_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv2_keys_forE [elim] = 
  m2_inv2_keys_for_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv2_keys_forD = 
  m2_inv2_keys_for_def [THEN setc_def_to_dest, rule_format, rotated 1]


text {* Invariance proof. *}

lemma PO_m2_inv2_keys_for_init [iff]:
  "init m2 \<subseteq> m2_inv2_keys_for"
by (auto simp add: m2_defs intro!: m2_inv2_keys_forI)

lemma PO_m2_inv2_keys_for_trans [iff]:
  "{m2_inv2_keys_for \<inter> m2_inv1_keys} trans m2 {> m2_inv2_keys_for}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv2_keys_forI) 
-- {* 1 subgoal, from fake *}
apply (auto simp add: keys_for_def ik0_def, erule fake.cases, fastforce+)
done

lemma PO_m2_inv2_keys_for [iff]: "reach m2 \<subseteq> m2_inv2_keys_for"
by (rule inv_rule_incr) (auto del: subsetI)


text {* Useful application of invariant. *}

lemma m2_inv2_keys_for__extr_insert_key:                   (* OBSOLETE?! *)
  "\<lbrakk> R \<notin> dom (runs s); s \<in> m2_inv2_keys_for \<rbrakk>
 \<Longrightarrow> extr (insert (aKey (sesK (R$sk))) T) (chan s) 
     = insert (aKey (sesK (R$sk))) (extr T (chan s))"
by (subgoal_tac "sesK (R$sk) \<notin> keys_for (chan s)") 
   (auto)
*)

subsubsection \<open>inv3a: Session key compromise\<close>
(******************************************************************************)

text \<open>A L2 version of a session key comprise invariant. Roughly, it states
that adding a set of keys @{term KK} to the parameter \<open>T\<close> of @{term extr} 
does not help the intruder to extract keys other than those in @{term KK} or
extractable without adding @{term KK}.
\<close>

definition 
  m2_inv3a_sesK_compr :: "m2_state set"
where 
  "m2_inv3a_sesK_compr \<equiv> {s. \<forall>K KK.
     aKey K \<in> extr (aKey`KK \<union> ik0) (chan s) \<longleftrightarrow> (K \<in> KK \<or> aKey K \<in> extr ik0 (chan s)) 
  }"

lemmas m2_inv3a_sesK_comprI = 
  m2_inv3a_sesK_compr_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv3a_sesK_comprE [elim] = 
  m2_inv3a_sesK_compr_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv3a_sesK_comprD = 
  m2_inv3a_sesK_compr_def [THEN setc_def_to_dest, rule_format]

text \<open>Additional lemma\<close>
lemmas insert_commute_aKey = insert_commute [where x="aKey K" for K] 

lemmas m2_inv3a_sesK_compr_simps = 
  m2_inv3a_sesK_comprD
  m2_inv3a_sesK_comprD [where KK="insert Kab KK" for Kab KK, simplified]
  m2_inv3a_sesK_comprD [where KK="{Kab}" for Kab, simplified]
  insert_commute_aKey   \<comment> \<open>to get the keys to the front\<close>

lemma PO_m2_inv3a_sesK_compr_init [iff]:
  "init m2 \<subseteq> m2_inv3a_sesK_compr"
by (auto simp add: m2_defs intro!: m2_inv3a_sesK_comprI)

lemma PO_m2_inv3a_sesK_compr_trans [iff]:
  "{m2_inv3a_sesK_compr} trans m2 {> m2_inv3a_sesK_compr}"
by (auto simp add: PO_hoare_defs m2_defs m2_inv3a_sesK_compr_simps intro!: m2_inv3a_sesK_comprI)

lemma PO_m2_inv3a_sesK_compr [iff]: "reach m2 \<subseteq> m2_inv3a_sesK_compr"
by (rule inv_rule_basic) (auto) 


subsubsection \<open>inv3: Extracted session keys\<close>
(******************************************************************************)

text \<open>inv3: Extracted non-leaked session keys were generated by the server 
for at least one bad agent. This invariant is needed in the proof of the 
strengthening of the authorization guards in steps 4 and 5 
(e.g., @{term "(Kab, A) \<in> azC (runs s)"} for the initiator's step4).\<close>

definition 
  m2_inv3_extrKey :: "m2_state set"
where
  "m2_inv3_extrKey \<equiv> {s. \<forall>K.
     aKey K \<in> extr ik0 (chan s) \<longrightarrow>  K \<notin> leak s \<longrightarrow> \<comment> \<open>was: \<open>K \<notin> corrKey \<longrightarrow>\<close>\<close>
       (\<exists>R A' B' Ts'. K = sesK (R$sk) \<and>
          runs s R = Some (Serv, [A', B'], [aNum Ts']) \<and> 
                    (A' \<in> bad \<or> B' \<in> bad))
  }"

lemmas m2_inv3_extrKeyI = 
  m2_inv3_extrKey_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv3_extrKeyE [elim] = 
  m2_inv3_extrKey_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv3_extrKeyD = 
  m2_inv3_extrKey_def [THEN setc_def_to_dest, rule_format, rotated 1]

lemma PO_m2_inv3_extrKey_init [iff]:
  "init m2 \<subseteq> m2_inv3_extrKey"
by (auto simp add: m2_defs ik0_def intro!: m2_inv3_extrKeyI)

lemma PO_m2_inv3_extrKey_trans [iff]:
  "{m2_inv3_extrKey \<inter> m2_inv3a_sesK_compr} 
      trans m2 
   {> m2_inv3_extrKey}"
proof (simp add: m2_def m2_trans_def, safe)
  fix Rs A B Kab Ts
  show
    "{m2_inv3_extrKey \<inter> m2_inv3a_sesK_compr} m2_step3 Rs A B Kab Ts {> m2_inv3_extrKey}"
  apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv3_extrKeyI)
  apply (auto simp add: m2_inv3a_sesK_compr_simps 
              dest!: m2_inv3_extrKeyD dest: dom_lemmas)
  done
next
  fix Ra A B Kab Ts
  show 
    "{m2_inv3_extrKey \<inter> m2_inv3a_sesK_compr} m2_step4 Ra A B Kab Ts {> m2_inv3_extrKey}"
  apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv3_extrKeyI)
  apply (auto simp add: dest!: m2_inv3_extrKeyD dest: dom_lemmas) 
  apply (auto intro!: exI)
  done
next 
  fix Rb A B Kab Ts
  show 
    "{m2_inv3_extrKey \<inter> m2_inv3a_sesK_compr} m2_step5 Rb A B Kab Ts {> m2_inv3_extrKey}"
  apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv3_extrKeyI)
  apply (auto dest!: m2_inv3_extrKeyD dest: dom_lemmas) 
  apply (auto intro!: exI)
  done
next 
  fix Rs
  show
    "{m2_inv3_extrKey \<inter> m2_inv3a_sesK_compr} m2_leak Rs {> m2_inv3_extrKey}"
  apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv3_extrKeyI)
  apply (auto simp add: m2_inv3a_sesK_compr_simps)
  done
qed (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv3_extrKeyI,
     auto dest!: m2_inv3_extrKeyD dest: dom_lemmas)


lemma PO_m2_inv3_extrKey [iff]: "reach m2 \<subseteq> m2_inv3_extrKey"
by (rule_tac J="m2_inv3a_sesK_compr" in inv_rule_incr) (auto) 



subsubsection \<open>inv4: Messages M2a/M2b for good agents and server state\<close>
(******************************************************************************)

text \<open>inv4: Secure messages to honest agents and server state; one variant 
for each of M2a and M2b. These invariants establish guard strengthening for
server authentication by the initiator and the responder.\<close>

definition 
  m2_inv4_M2a :: "m2_state set"
where
  "m2_inv4_M2a \<equiv> {s. \<forall>A B Kab Ts.
     Secure Sv A (Msg [aAgt B, aKey Kab, aNum Ts]) \<in> chan s \<longrightarrow> A \<in> good \<longrightarrow>
       (\<exists>Rs. Kab = sesK (Rs$sk) \<and>
          runs s Rs = Some (Serv, [A, B], [aNum Ts]))
  }"

definition 
  m2_inv4_M2b :: "m2_state set"
where
  "m2_inv4_M2b \<equiv> {s. \<forall>A B Kab Ts.
     Secure Sv B (Msg [aKey Kab, aAgt A, aNum Ts]) \<in> chan s \<longrightarrow> B \<in> good \<longrightarrow>
        (\<exists>Rs. Kab = sesK (Rs$sk) \<and>
           runs s Rs = Some (Serv, [A, B], [aNum Ts]))
  }"

lemmas m2_inv4_M2aI = 
  m2_inv4_M2a_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv4_M2aE [elim] = 
  m2_inv4_M2a_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv4_M2aD = 
  m2_inv4_M2a_def [THEN setc_def_to_dest, rule_format, rotated 1]

lemmas m2_inv4_M2bI = m2_inv4_M2b_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv4_M2bE [elim] = 
  m2_inv4_M2b_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv4_M2bD = 
  m2_inv4_M2b_def [THEN setc_def_to_dest, rule_format, rotated 1]


text \<open>Invariance proofs.\<close>

lemma PO_m2_inv4_M2a_init [iff]:
  "init m2 \<subseteq> m2_inv4_M2a"
by (auto simp add: m2_defs intro!: m2_inv4_M2aI)

lemma PO_m2_inv4_M2a_trans [iff]:
  "{m2_inv4_M2a} trans m2 {> m2_inv4_M2a}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv4_M2aI)
apply (auto dest!: m2_inv4_M2aD dest: dom_lemmas)
\<comment> \<open>3 subgoals\<close>
apply (force dest!: spec)+
done

lemma PO_m2_inv4_M2a [iff]: "reach m2 \<subseteq> m2_inv4_M2a"
by (rule inv_rule_basic) (auto)


lemma PO_m2_inv4_M2b_init [iff]:
  "init m2 \<subseteq> m2_inv4_M2b"
by (auto simp add: m2_defs intro!: m2_inv4_M2bI)

lemma PO_m2_inv4_M2b_trans [iff]:
  "{m2_inv4_M2b} trans m2 {> m2_inv4_M2b}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv4_M2bI) 
apply (auto dest!: m2_inv4_M2bD dest: dom_lemmas)
\<comment> \<open>3 subgoals\<close>
apply (force dest!: spec)+
done

lemma PO_m2_inv4_M2b [iff]: "reach m2 \<subseteq> m2_inv4_M2b"
by (rule inv_rule_incr) (auto del: subsetI)


text \<open>Consequence needed in proof of inv8/step5 and inv9/step4: The 
session key uniquely identifies other fields in M2a and M2b, provided it 
is secret.\<close>

lemma m2_inv4_M2a_M2b_match:
  "\<lbrakk> Secure Sv A' (Msg [aAgt B', aKey Kab, aNum Ts']) \<in> chan s; 
     Secure Sv B (Msg [aKey Kab, aAgt A, aNum Ts]) \<in> chan s; 
     aKey Kab \<notin> extr ik0 (chan s); s \<in> m2_inv4_M2a; s \<in> m2_inv4_M2b \<rbrakk>
  \<Longrightarrow> A = A' \<and> B = B' \<and> Ts = Ts'"
apply (subgoal_tac "A' \<notin> bad \<and> B \<notin> bad", auto)
apply (auto dest!: m2_inv4_M2aD m2_inv4_M2bD)
done


text \<open>More consequences of invariants. Needed in ref/step4 and ref/step5 
respectively to show the strengthening of the authorization guards.\<close>

lemma m2_inv34_M2a_authorized:
  assumes "Secure Sv A (Msg [aAgt B, aKey K, aNum T]) \<in> chan s" 
          "s \<in> m2_inv3_extrKey" "s \<in> m2_inv4_M2a" "K \<notin> leak s"  
  shows   "(K, A) \<in> azC (runs s)"
proof (cases "A \<in> bad")
  case True 
  from assms(1) \<open>A \<in> bad\<close> have "aKey K \<in> extr ik0 (chan s)" by auto
  with \<open>s \<in> m2_inv3_extrKey\<close> \<open>K \<notin> leak s\<close> show ?thesis by auto 
next
  case False 
  with assms show ?thesis by (auto dest: m2_inv4_M2aD) 
qed

lemma m2_inv34_M2b_authorized:
  assumes "Secure Sv B (Msg [aKey K, aAgt A, aNum T]) \<in> chan s" 
          "s \<in> m2_inv3_extrKey" "s \<in> m2_inv4_M2b" "K \<notin> leak s"  
  shows  "(K, B) \<in> azC (runs s)"
proof (cases "B \<in> bad")
  case True 
  from assms(1) \<open>B \<in> bad\<close> have "aKey K \<in> extr ik0 (chan s)" by auto
  with \<open>s \<in> m2_inv3_extrKey\<close> \<open>K \<notin> leak s\<close> show ?thesis by auto 
next
  case False 
  with assms show ?thesis by (auto dest: m2_inv4_M2bD) 
qed


subsubsection \<open>inv5: Key secrecy for server\<close>
(******************************************************************************)

text \<open>inv5: Key secrecy from server perspective. This invariant links the 
abstract notion of key secrecy to the intruder key knowledge.\<close>

definition 
  m2_inv5_ikk_sv :: "m2_state set"
where
  "m2_inv5_ikk_sv \<equiv> {s. \<forall>R A B al.
     runs s R = Some (Serv, [A, B], al) \<longrightarrow> A \<in> good \<longrightarrow> B \<in> good \<longrightarrow>
     aKey (sesK (R$sk)) \<in> extr ik0 (chan s) \<longrightarrow>
       sesK (R$sk) \<in> leak s
  }"

lemmas m2_inv5_ikk_svI = 
  m2_inv5_ikk_sv_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv5_ikk_svE [elim] = 
  m2_inv5_ikk_sv_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv5_ikk_svD = 
  m2_inv5_ikk_sv_def [THEN setc_def_to_dest, rule_format, rotated 1]


text \<open>Invariance proof.\<close>

lemma PO_m2_inv5_ikk_sv_init [iff]:
  "init m2 \<subseteq> m2_inv5_ikk_sv"
by (auto simp add: m2_defs intro!: m2_inv5_ikk_svI)

lemma PO_m2_inv5_ikk_sv_trans [iff]:
  "{m2_inv5_ikk_sv \<inter> m2_inv3a_sesK_compr \<inter> m2_inv3_extrKey} 
     trans m2 
   {> m2_inv5_ikk_sv}"
by (simp add: PO_hoare_defs m2_defs, safe intro!: m2_inv5_ikk_svI)
   (auto simp add: m2_inv3a_sesK_compr_simps dest: dom_lemmas)

lemma PO_m2_inv5_ikk_sv [iff]: "reach m2 \<subseteq> m2_inv5_ikk_sv"
by (rule_tac J="m2_inv3_extrKey \<inter> m2_inv3a_sesK_compr" in inv_rule_incr) (auto)


subsubsection \<open>inv6/7: Key secrecy for initiator and responder\<close>
(******************************************************************************)

text \<open>These invariants are derivable.\<close>

definition 
  m2_inv6_ikk_init :: "m2_state set"
where
  "m2_inv6_ikk_init \<equiv> {s. \<forall>A B Ra K Ts nl.
     runs s Ra = Some (Init, [A, B], aKey K # aNum Ts # nl) \<longrightarrow> 
     A \<in> good \<longrightarrow> B \<in> good \<longrightarrow> aKey K \<in> extr ik0 (chan s) \<longrightarrow> 
       K \<in> leak s
  }"

lemmas m2_inv6_ikk_initI = m2_inv6_ikk_init_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv6_ikk_initE [elim] = m2_inv6_ikk_init_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv6_ikk_initD = m2_inv6_ikk_init_def [THEN setc_def_to_dest, rule_format, rotated 1]


definition 
  m2_inv7_ikk_resp :: "m2_state set"
where
  "m2_inv7_ikk_resp \<equiv> {s. \<forall>A B Rb K Ts nl.
     runs s Rb = Some (Resp, [A, B], aKey K # aNum Ts # nl) \<longrightarrow> 
     A \<in> good \<longrightarrow> B \<in> good \<longrightarrow> aKey K \<in> extr ik0 (chan s) \<longrightarrow>
       K \<in> leak s
  }"

lemmas m2_inv7_ikk_respI = m2_inv7_ikk_resp_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv7_ikk_respE [elim] = m2_inv7_ikk_resp_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv7_ikk_respD = m2_inv7_ikk_resp_def [THEN setc_def_to_dest, rule_format, rotated 1]


(******************************************************************************)
subsection \<open>Refinement\<close>
(******************************************************************************)

text \<open>The simulation relation. This is a pure superposition refinement.\<close>

definition
  R12 :: "(m1_state \<times> m2_state) set" where
  "R12 \<equiv> {(s, t). runs s = runs t \<and> leak s = leak t \<and> clk s = clk t}"

text \<open>The mediator function is the identity.\<close>

definition 
  med21 :: "m2_obs \<Rightarrow> m1_obs" where
  "med21 = id"


text \<open>Refinement proof.\<close>

lemma PO_m2_step1_refines_m1_step1:
  "{R12} 
     (m1_step1 Ra A B), (m2_step1 Ra A B) 
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)

lemma PO_m2_step2_refines_m1_step2:
  "{R12} 
     (m1_step2 Rb A B), (m2_step2 Rb A B)
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)

lemma PO_m2_step3_refines_m1_step3:
  "{R12} 
     (m1_step3 Rs A B Kab Ts), (m2_step3 Rs A B Kab Ts)
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)

lemma PO_m2_step4_refines_m1_step4:
  "{R12 \<inter> UNIV \<times> (m2_inv4_M2a \<inter> m2_inv3_extrKey)} 
     (m1_step4 Ra A B Kab Ts), (m2_step4 Ra A B Kab Ts)  
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, simp_all)
   (auto dest: m2_inv34_M2a_authorized)

lemma PO_m2_step5_refines_m1_step5:
  "{R12 \<inter> UNIV \<times> (m2_inv4_M2b \<inter> m2_inv3_extrKey)}          \<comment> \<open>REMOVED!: \<open>m2_inv5_ikk_sv\<close>\<close>
     (m1_step5 Rb A B Kab Ts), (m2_step5 Rb A B Kab Ts) 
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, simp_all)
   (auto dest: m2_inv34_M2b_authorized)

lemma PO_m2_tick_refines_m1_tick:
  "{R12}
    (m1_tick T), (m2_tick T)
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, simp_all)

lemma PO_m2_leak_refines_m1_leak:
  "{R12} 
     (m1_leak Rs), (m2_leak Rs)
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)

lemma PO_m2_fake_refines_skip:
  "{R12} 
     Id, m2_fake
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)


text \<open>All together now...\<close>

lemmas PO_m2_trans_refines_m1_trans = 
  PO_m2_step1_refines_m1_step1 PO_m2_step2_refines_m1_step2
  PO_m2_step3_refines_m1_step3 PO_m2_step4_refines_m1_step4
  PO_m2_step5_refines_m1_step5 PO_m2_tick_refines_m1_tick 
  PO_m2_leak_refines_m1_leak PO_m2_fake_refines_skip 

lemma PO_m2_refines_init_m1 [iff]:
  "init m2 \<subseteq> R12``(init m1)"
by (auto simp add: R12_def m1_defs m2_loc_defs)

lemma PO_m2_refines_trans_m1 [iff]:
  "{R12 \<inter> 
    UNIV \<times> (m2_inv4_M2b \<inter> m2_inv4_M2a \<inter> m2_inv3_extrKey)} 
     (trans m1), (trans m2) 
   {> R12}"
by (auto simp add: m2_def m2_trans_def m1_def m1_trans_def)
   (blast intro!: PO_m2_trans_refines_m1_trans)+


lemma PO_obs_consistent_R12 [iff]: 
  "obs_consistent R12 med21 m1 m2"
by (auto simp add: obs_consistent_def R12_def med21_def m2_defs)


text \<open>Refinement result.\<close>

lemma m2_refines_m1 [iff]:
  "refines 
     (R12 \<inter> 
      (UNIV \<times> (m2_inv4_M2b \<inter> m2_inv4_M2a \<inter> m2_inv3_extrKey \<inter> m2_inv3a_sesK_compr)))
     med21 m1 m2"
by (rule Refinement_using_invariants) (auto)

lemma m2_implements_m1 [iff]:
  "implements med21 m1 m2"
by (rule refinement_soundness) (auto)


(******************************************************************************)
subsection \<open>Inherited and derived invariants\<close>
(******************************************************************************)
(*
text {* Show preservation of invariants @{term "m1_inv2i_serv"} and
@{term "m1_inv2r_serv"} from @{text "m1"}. *}

lemma PO_m2_sat_m1_inv2i_serv [iff]: "reach m2 \<subseteq> m1_inv2i_serv"
by (rule_tac Pa=m1_inv2i_serv and Qa=m1_inv2i_serv and Q=m1_inv2i_serv 
       in m2_implements_m1 [THEN [5] internal_invariant_translation])
   (auto simp add: m2_loc_defs med21_def intro!: m1_inv2i_servI)

lemma PO_m2_sat_m1_inv2r_serv [iff]: "reach m2 \<subseteq> m1_inv2r_serv"
by (rule_tac Pa=m1_inv2r_serv and Qa=m1_inv2r_serv and Q=m1_inv2r_serv
       in m2_implements_m1 [THEN [5] internal_invariant_translation])
   (fastforce simp add: m2_loc_defs med21_def intro!: m1_inv2r_servI)+


text {* Now we derive the L2 key secrecy invariants for the initiator 
and the responder (for definition, see above). *}

lemma PO_m2_inv6_init_ikk [iff]: "reach m2 \<subseteq> m2_inv6_ikk_init"
apply (rule_tac B=" m1_inv2i_serv \<inter> m2_inv5_ikk_sv" in subset_trans, auto)
apply (rule m2_inv6_ikk_initI, auto)
apply (blast dest!: m1_inv2i_servD) 
done

lemma PO_m2_inv6_resp_ikk [iff]: "reach m2 \<subseteq> m2_inv7_ikk_resp"
apply (rule_tac B=" m1_inv2r_serv \<inter> m2_inv5_ikk_sv" in subset_trans, auto)
apply (rule m2_inv7_ikk_respI, auto)
apply (blast dest!: m1_inv2r_servD) 
done
*)

end

