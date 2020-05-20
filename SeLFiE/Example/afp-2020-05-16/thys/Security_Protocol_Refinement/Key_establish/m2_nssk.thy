(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Key_establish/m2_nssk.thy (Isabelle/HOL 2016-1)
  ID:      $Id: m2_nssk.thy 133854 2017-03-20 17:53:50Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Key distribution protocols
  Second refinement: channel-protocol, parallel version of Needham-Schroeder
  Shared Key protocol (NSSK, Boyd/Mathuria, Protocol 3.19)

  Copyright (c) 2009-2016 Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Abstract Needham-Schroeder Shared Key (L2)\<close>

theory m2_nssk imports m1_nssk "../Refinement/Channels"
begin

text \<open>
We model an abstract version of the Needham-Schroeder Shared Key protocol:
\[
\begin{array}{lll}
  \mathrm{M1.} & A \rightarrow S: & A, B, Na \\ 
  \mathrm{M2.} & S \rightarrow A: & \{Na, B, Kab, \{Kab, A\}_{Kbs} \}_{Kas} \\
  \mathrm{M3.} & A \rightarrow B: & \{A, Kab\}_{Kbs} \\
  \mathrm{M4.} & B \rightarrow A: & \{Nb\}_{Kab} \\  
  \mathrm{M5.} & A \rightarrow B: & \{Nb - 1 \}_{Kab} \\
\end{array}
\]
The last two message are supposed to authenticate $A$ to $B$, but this fails
as shown by Dening and Sacco.  Therefore and since we are mainly interested
in secrecy at this point, we drop the last two message from this development.

This refinement introduces channels with security properties.  We model 
a parallel/"channel-pure" version of the first three messages of the NSSK 
protocol:
\[
\begin{array}{lll}
  \mathrm{M1.} & A \rightarrow S: & A, B, Na \\ 
  \mathrm{M2.} & S \rightarrow A: & \{Na, B, Kab\}_{Kas} \\
  \mathrm{M3.} & S \rightarrow B: & \{Kab, A\}_{Kbs} \\
\end{array}
\]
Message 1 is sent over an insecure channel, the other two message over
secure channels to/from the server.
\<close>

declare domIff [simp, iff del]


(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

record m2_state = "m1_state" +
  chan :: "chmsg set"              \<comment> \<open>channel messages\<close>

type_synonym
  m2_obs = "m1_state"

definition 
  m2_obs :: "m2_state \<Rightarrow> m2_obs" where
  "m2_obs s \<equiv> \<lparr> runs = runs s, leak = leak s \<rparr>"

type_synonym
  m2_pred = "m2_state set"

type_synonym
  m2_trans = "(m2_state \<times> m2_state) set"


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

text \<open>Protocol events.\<close>

definition     \<comment> \<open>by @{term "A"}, refines @{term "m1a_step1"}\<close>
  m2_step1 :: "[rid_t, agent, agent, nonce] \<Rightarrow> m2_trans"
where
  "m2_step1 Ra A B Na \<equiv> {(s, s1).

    \<comment> \<open>guards:\<close>
    Ra \<notin> dom (runs s) \<and>                      \<comment> \<open>fresh run identifier\<close>
    Na = Ra$na \<and>                             \<comment> \<open>generate nonce \<open>Na\<close>\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>create initiator thread and send message 1\<close>
    s1 = s\<lparr>
      runs := (runs s)(Ra \<mapsto> (Init, [A, B], [])),
      chan := insert (Insec A B (Msg [aNon Na])) (chan s)   \<comment> \<open>msg 1\<close>
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "B"}, refines @{term "m1a_step2"}\<close>
  m2_step2 :: "[rid_t, agent, agent] \<Rightarrow> m2_trans"
where
  "m2_step2 \<equiv> m1_step2"

definition     \<comment> \<open>by @{text "Server"}, refines @{term m1a_step3}\<close>
  m2_step3 :: "[rid_t, agent, agent, nonce, key] \<Rightarrow> m2_trans"
where
  "m2_step3 Rs A B Na Kab \<equiv> {(s, s1). 
    \<comment> \<open>guards:\<close>
    Rs \<notin> dom (runs s) \<and>                           \<comment> \<open>new server run\<close>
    Kab = sesK (Rs$sk) \<and>                          \<comment> \<open>fresh session key\<close>

    Insec A B (Msg [aNon Na]) \<in> chan s \<and>          \<comment> \<open>recv msg 1\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>record key and send messages 2 and 3\<close>
    \<comment> \<open>note that last field in server record is for responder nonce\<close>
    s1 = s\<lparr>
      runs := (runs s)(Rs \<mapsto> (Serv, [A, B], [aNon Na])), 
      chan := {Secure Sv A (Msg [aNon Na, aAgt B, aKey Kab]), 
               Secure Sv B (Msg [aKey Kab, aAgt A])} \<union> chan s
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "A"}, refines @{term m1a_step4}\<close>
  m2_step4 :: "[rid_t, agent, agent, nonce, key] \<Rightarrow> m2_trans"
where
  "m2_step4 Ra A B Na Kab \<equiv> {(s, s1).

    \<comment> \<open>guards:\<close>
    runs s Ra = Some (Init, [A, B], []) \<and> 
    Na = Ra$na \<and>

    Secure Sv A (Msg [aNon Na, aAgt B, aKey Kab]) \<in> chan s \<and>  \<comment> \<open>recv msg 2\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>record session key\<close>
    s1 = s\<lparr>
      runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aKey Kab]))
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "B"}, refines @{term m1_step5}\<close>
  m2_step5 :: "[rid_t, agent, agent, nonce, key] \<Rightarrow> m2_trans"
where
  "m2_step5 Rb A B Nb Kab \<equiv> {(s, s1). 

    \<comment> \<open>guards:\<close>
    runs s Rb = Some (Resp, [A, B], []) \<and>
    Nb = Rb$nb \<and>

    Secure Sv B (Msg [aKey Kab, aAgt A]) \<in> chan s \<and>     \<comment> \<open>recv msg 3\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>record session key\<close>
    s1 = s\<lparr>
      runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [aKey Kab])), 
      chan := insert (dAuth Kab (Msg [aNon Nb])) (chan s)
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "A"}, refines @{term m1_step6}\<close>
  m2_step6 :: "[rid_t, agent, agent, nonce, nonce, key] \<Rightarrow> m2_trans"
where
  "m2_step6 Ra A B Na Nb Kab \<equiv> {(s, s'). 
    runs s Ra = Some (Init, [A, B], [aKey Kab]) \<and>    \<comment> \<open>key recv'd before\<close>
    Na = Ra$na \<and>

    dAuth Kab (Msg [aNon Nb]) \<in> chan s \<and>             \<comment> \<open>receive \<open>M4\<close>\<close>

    \<comment> \<open>actions:\<close>
    s' = s\<lparr>
      runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNon Nb])),
      chan := insert (dAuth Kab (Msg [aNon Nb, aNon Nb])) (chan s)
    \<rparr>
  }"

definition     \<comment> \<open>by @{term "B"}, refines @{term m1_step6}\<close>
  m2_step7 :: "[rid_t, agent, agent, nonce, key] \<Rightarrow> m2_trans"
where
  "m2_step7 Rb A B Nb Kab \<equiv> {(s, s').
    runs s Rb = Some (Resp, [A, B], [aKey Kab]) \<and>     \<comment> \<open>key recv'd before\<close>
    Nb = Rb$nb \<and>

    dAuth Kab (Msg [aNon Nb, aNon Nb]) \<in> chan s \<and>     \<comment> \<open>receive \<open>M5\<close>\<close>

    \<comment> \<open>actions: (redundant) update local state marks successful termination\<close>
    s' = s\<lparr>
      runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [aKey Kab, END]))
    \<rparr>
  }"


text \<open>Intruder fake event.\<close>

definition     \<comment> \<open>refines @{term m1_leak}\<close>
  m2_leak :: "[rid_t, rid_t, rid_t, agent, agent] \<Rightarrow> m2_trans" 
where
  "m2_leak Rs Ra Rb A B \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    runs s Rs = Some (Serv, [A, B], [aNon (Ra$na)]) \<and>
    runs s Ra = Some (Init, [A, B], [aKey (sesK (Rs$sk)), aNon (Rb$nb)]) \<and>  
    runs s Rb = Some (Resp, [A, B], [aKey (sesK (Rs$sk)), END]) \<and>  

    \<comment> \<open>actions:\<close>
    s1 = s\<lparr> leak := insert (sesK (Rs$sk), Ra$na, Rb$nb) (leak s), 
            chan := insert (Insec undefined undefined (Msg [aKey (sesK (Rs$sk))])) (chan s) \<rparr>
  }"

definition     \<comment> \<open>refines @{term Id}\<close> 
  m2_fake :: "m2_trans"
where
  "m2_fake \<equiv> {(s, s1). 

    \<comment> \<open>actions:\<close>
    s1 = s\<lparr>
      chan := fake ik0  (dom (runs s)) (chan s)
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
     leak = corrKey \<times> {undefined} \<times> {undefined}, 
     chan = {} \<rparr> 
  }"

definition 
  m2_trans :: "m2_trans" where
  "m2_trans \<equiv> (\<Union>A B Ra Rb Rs Na Nb Kab.
     m2_step1 Ra A B Na \<union>
     m2_step2 Rb A B \<union>
     m2_step3 Rs A B Na Kab \<union>
     m2_step4 Ra A B Na Kab \<union>
     m2_step5 Rb A B Nb Kab \<union>
     m2_step6 Ra A B Na Nb Kab \<union>
     m2_step7 Rb A B Nb Kab \<union>
     m2_leak Rs Ra Rb A B \<union>
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
  m2_step6_def m2_step7_def m2_leak_def m2_fake_def 

lemmas m2_defs = m2_loc_defs m1_defs


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

subsubsection \<open>inv1: Key definedness\<close>
(*inv**************************************************************************)

text \<open>All session keys in channel messages stem from existing runs.\<close>

definition 
  m2_inv1_keys :: "m2_pred"
where 
  "m2_inv1_keys \<equiv> {s. \<forall>R.
     aKey (sesK (R$sk)) \<in> atoms (chan s) \<or> sesK (R$sk) \<in> Domain (leak s) \<longrightarrow> 
       R \<in> dom (runs s)
  }"

lemmas m2_inv1_keysI = m2_inv1_keys_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv1_keysE [elim] = m2_inv1_keys_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv1_keysD = m2_inv1_keys_def [THEN setc_def_to_dest, rule_format, rotated 1]


text \<open>Invariance proof.\<close>

lemma PO_m2_inv1_keys_init [iff]:
  "init m2 \<subseteq> m2_inv1_keys"
by (auto simp add: m2_defs intro!: m2_inv1_keysI)

lemma PO_m2_inv1_keys_trans [iff]:
  "{m2_inv1_keys} trans m2 {> m2_inv1_keys}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv1_keysI)
apply (auto dest!: m2_inv1_keysD dest: dom_lemmas)
done

lemma PO_m2_inv1_keys [iff]: "reach m2 \<subseteq> m2_inv1_keys"
by (rule inv_rule_basic) (auto)


subsubsection \<open>inv2: Definedness of used keys\<close>
(*inv**************************************************************************)

definition 
  m2_inv2_keys_for :: "m2_pred"
where 
  "m2_inv2_keys_for \<equiv> {s. \<forall>R.
     sesK (R$sk) \<in> keys_for (chan s) \<longrightarrow> R \<in> dom (runs s)
  }"

lemmas m2_inv2_keys_forI = m2_inv2_keys_for_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv2_keys_forE [elim] = m2_inv2_keys_for_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv2_keys_forD = m2_inv2_keys_for_def [THEN setc_def_to_dest, rule_format, rotated 1]

text \<open>Invariance proof.\<close>

lemma PO_m2_inv2_keys_for_init [iff]:
  "init m2 \<subseteq> m2_inv2_keys_for"
by (auto simp add: m2_defs intro!: m2_inv2_keys_forI)

lemma PO_m2_inv2_keys_for_trans [iff]:
  "{m2_inv2_keys_for \<inter> m2_inv1_keys} trans m2 {> m2_inv2_keys_for}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv2_keys_forI)
apply (auto dest!: m2_inv2_keys_forD dest: m2_inv1_keysD dest: dom_lemmas)
\<comment> \<open>2 subgoals, from step 4 and fake\<close>
apply (rename_tac R xa xb xc xe)
apply (subgoal_tac "aKey (sesK (R$sk)) \<in> atoms (chan xa)", 
       auto dest!: m2_inv1_keysD dest: dom_lemmas)
apply (auto simp add: keys_for_def, erule fake.cases, fastforce+) 
done

lemma PO_m2_inv2_keys_for [iff]: "reach m2 \<subseteq> m2_inv2_keys_for"
by (rule inv_rule_incr) (auto del: subsetI)


text \<open>Useful application of invariant.\<close>

lemma m2_inv2_keys_for__extr_insert_key:
  "\<lbrakk> R \<notin> dom (runs s); s \<in> m2_inv2_keys_for \<rbrakk>
 \<Longrightarrow> extr (insert (aKey (sesK (R$sk))) T) (chan s) = insert (aKey (sesK (R$sk))) (extr T (chan s))"
by (subgoal_tac "sesK (R$sk) \<notin> keys_for (chan s)") (auto)


subsubsection \<open>inv2b: leaked keys include corrupted ones\<close>
(*inv**************************************************************************)

definition 
  m2_inv2b_corrKey_leaked :: "m2_pred"
where 
  "m2_inv2b_corrKey_leaked \<equiv> {s. \<forall>K.
     K \<in> corrKey \<longrightarrow> K \<in> Domain (leak s)
  }"

lemmas m2_inv2b_corrKey_leakedI = m2_inv2b_corrKey_leaked_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv2b_corrKey_leakedE [elim] = m2_inv2b_corrKey_leaked_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv2b_corrKey_leakedD = m2_inv2b_corrKey_leaked_def [THEN setc_def_to_dest, rule_format, rotated 1]

text \<open>Invariance proof.\<close>

lemma PO_m2_inv2b_corrKey_leaked_init [iff]:
  "init m2 \<subseteq> m2_inv2b_corrKey_leaked"
by (auto simp add: m2_defs intro!: m2_inv2b_corrKey_leakedI)

lemma PO_m2_inv2b_corrKey_leaked_trans [iff]:
  "{m2_inv2b_corrKey_leaked \<inter> m2_inv1_keys} trans m2 {> m2_inv2b_corrKey_leaked}"
by (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv2b_corrKey_leakedI)

lemma PO_m2_inv2b_corrKey_leaked [iff]: "reach m2 \<subseteq> m2_inv2b_corrKey_leaked"
by (rule inv_rule_incr) (auto del: subsetI)


subsubsection \<open>inv3a: Session key compromise\<close>
(*inv**************************************************************************)

text \<open>A L2 version of a session key comprise invariant. Roughly, it states
that adding a set of keys @{term KK} to the parameter \<open>T\<close> of @{term extr} 
does not help the intruder to extract keys other than those in @{term KK} or
extractable without adding @{term KK}. 
\<close>

definition 
  m2_inv3a_sesK_compr :: "m2_state set"
where 
  "m2_inv3a_sesK_compr \<equiv> {s. \<forall>K KK.
     \<^cancel>\<open>KK \<subseteq> range sesK \<longrightarrow>\<close>
     aKey K \<in> extr (aKey`KK \<union> ik0) (chan s) \<longleftrightarrow> (K \<in> KK \<or> aKey K \<in> extr ik0 (chan s)) 
  }"

lemmas m2_inv3a_sesK_comprI = m2_inv3a_sesK_compr_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv3a_sesK_comprE [elim] = m2_inv3a_sesK_compr_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv3a_sesK_comprD = m2_inv3a_sesK_compr_def [THEN setc_def_to_dest, rule_format]

text \<open>Additional lemma to get the keys in front\<close>
lemmas insert_commute_aKey = insert_commute [where x="aKey K" for K] 

lemmas m2_inv3a_sesK_compr_simps = 
  m2_inv3a_sesK_comprD
  m2_inv3a_sesK_comprD [where KK="{Kab}" for Kab, simplified]
  m2_inv3a_sesK_comprD [where KK="insert Kab KK" for Kab KK, simplified]
  insert_commute_aKey 

lemma PO_m2_inv3a_sesK_compr_init [iff]:
  "init m2 \<subseteq> m2_inv3a_sesK_compr"
by (auto simp add: m2_defs intro!: m2_inv3a_sesK_comprI)

lemma PO_m2_inv3a_sesK_compr_trans [iff]:
  "{m2_inv3a_sesK_compr} trans m2 {> m2_inv3a_sesK_compr}"
by (auto simp add: PO_hoare_defs m2_defs m2_inv3a_sesK_compr_simps intro!: m2_inv3a_sesK_comprI)

lemma PO_m2_inv3a_sesK_compr [iff]: "reach m2 \<subseteq> m2_inv3a_sesK_compr"
by (rule inv_rule_basic) (auto) 


subsubsection \<open>inv3b: Session key compromise for nonces\<close>
(*inv**************************************************************************)

text \<open>A variant of the above for nonces. Roughly, it states that adding 
a set of keys @{term KK} to the parameter \<open>T\<close> of @{term extr} 
does not help the intruder to extract more nonces than those extractable 
without adding @{term KK}.

NOTE: This lemma is only needed at the next refinement level.
\<close>

definition 
  m2_inv3b_sesK_compr_non :: "m2_state set"
where 
  "m2_inv3b_sesK_compr_non \<equiv> {s. \<forall>N KK.
     \<^cancel>\<open>KK \<subseteq> range sesK \<longrightarrow>\<close>
     aNon N \<in> extr (aKey`KK \<union> ik0) (chan s) \<longleftrightarrow> aNon N \<in> extr ik0 (chan s)
  }"

lemmas m2_inv3b_sesK_compr_nonI = m2_inv3b_sesK_compr_non_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv3b_sesK_compr_nonE [elim] = m2_inv3b_sesK_compr_non_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv3b_sesK_compr_nonD = m2_inv3b_sesK_compr_non_def [THEN setc_def_to_dest, rule_format]

lemmas m2_inv3b_sesK_compr_non_simps = 
  m2_inv3b_sesK_compr_nonD
  m2_inv3b_sesK_compr_nonD [where KK="{Kab}" for Kab, simplified] 
  m2_inv3b_sesK_compr_nonD [where KK="insert Kab KK" for Kab KK, simplified] 
  insert_commute_aKey    \<comment> \<open>to get the keys to the front\<close>

lemma PO_m2_inv3b_sesK_compr_non_init [iff]:
  "init m2 \<subseteq> m2_inv3b_sesK_compr_non"
by (auto simp add: m2_defs intro!: m2_inv3b_sesK_compr_nonI)

(* with dSecure instead of dAuth in step5:

lemma PO_m2_inv3b_sesK_compr_non_trans [iff]:
  "{m2_inv3b_sesK_compr_non \<inter> m2_inv3a_sesK_compr} 
     m2_step5 Rb A B Nb Kab 
   {> m2_inv3b_sesK_compr_non}"
apply (auto simp add: PO_hoare_defs m2_defs m2_inv3b_sesK_compr_non_simps 
                      m2_inv3a_sesK_compr_simps
         intro!: m2_inv3b_sesK_compr_nonI)
(* 1 subgoal, unsolvable! *)
oops
*)

lemma PO_m2_inv3b_sesK_compr_non_trans [iff]:
  "{m2_inv3b_sesK_compr_non} trans m2 {> m2_inv3b_sesK_compr_non}"
by (auto simp add: PO_hoare_defs m2_defs m2_inv3b_sesK_compr_non_simps 
         intro!: m2_inv3b_sesK_compr_nonI)

lemma PO_m2_inv3b_sesK_compr_non [iff]: "reach m2 \<subseteq> m2_inv3b_sesK_compr_non"
by (rule inv_rule_basic) (auto) 


subsubsection \<open>inv3: Lost session keys\<close>
(*inv**************************************************************************)

text \<open>inv3: Lost session keys were generated by the server for at least one
bad agent. This invariant is needed in the proof of the strengthening of the 
authorization guards in steps 4 and 5 (e.g., @{term "(Kab, A) \<in> azC (runs s)"} 
for the initiator's step4).\<close>

definition 
  m2_inv3_extrKey :: "m2_state set"
where
  "m2_inv3_extrKey \<equiv> {s. \<forall>K.
     aKey K \<in> extr ik0 (chan s) \<longrightarrow> K \<notin> corrKey \<longrightarrow> 
       (\<exists>R A' B' Na'. K = sesK (R$sk) \<and>
          runs s R = Some (Serv, [A', B'], [aNon Na']) \<and> 
          (A' \<in> bad \<or> B' \<in> bad \<or> (\<exists>Nb'. (K, Na', Nb') \<in> leak s))) 
  }"

lemmas m2_inv3_extrKeyI = m2_inv3_extrKey_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv3_extrKeyE [elim] = m2_inv3_extrKey_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv3_extrKeyD = m2_inv3_extrKey_def [THEN setc_def_to_dest, rule_format, rotated 1]

lemma PO_m2_inv3_extrKey_init [iff]:
  "init m2 \<subseteq> m2_inv3_extrKey"
by (auto simp add: m2_defs intro!: m2_inv3_extrKeyI)

lemma PO_m2_inv3_extrKey_trans [iff]:
  "{m2_inv3_extrKey \<inter> m2_inv3a_sesK_compr} trans m2 {> m2_inv3_extrKey}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv3_extrKeyI)
apply (auto simp add: m2_inv3a_sesK_compr_simps dest: dom_lemmas)
\<comment> \<open>11 subgoals, sledgehammer\<close>
apply (metis m2_inv3_extrKeyD map_definedness_contra)
apply (metis m2_inv3_extrKeyD map_definedness_contra)
apply (metis m2_inv3_extrKeyD)
apply (metis m2_inv3_extrKeyD)
apply (metis m2_inv3_extrKeyD)
apply (metis m2_inv3_extrKeyD map_definedness_contra)
apply (metis m2_inv3_extrKeyD not_Cons_self2 prod.inject option.inject)
apply (metis m2_inv3_extrKeyD not_Cons_self2 prod.inject option.inject)
apply (metis m2_inv3_extrKeyD atom.distinct(7) list.inject option.inject prod.inject)
apply (metis m2_inv3_extrKeyD atom.distinct(7) list.inject option.inject prod.inject)
apply (metis m2_inv3_extrKeyD)
done
(*
apply (aut dest!: m2_inv3_extrKeyD dest: dom_lemmas)        -- {*SLOW*}
-- {* 18 subgoals; go agressive*}
apply (aut intro!: exI dest: dom_lemmas)
done
*)

lemma PO_m2_inv3_extrKey [iff]: "reach m2 \<subseteq> m2_inv3_extrKey"
by (rule_tac J="m2_inv3a_sesK_compr" in inv_rule_incr) (auto) 


subsubsection \<open>inv4: Secure channel and message 2\<close>
(*inv**************************************************************************)

text \<open>inv4: Secure messages to honest agents and server state; one variant 
for each of M2 and M3. Note that the one for M2 is stronger than the 
one for M3.\<close>

definition 
  m2_inv4_M2 :: "m2_pred"
where
  "m2_inv4_M2 \<equiv> {s. \<forall>A B Na Kab.
     Secure Sv A (Msg [aNon Na, aAgt B, aKey Kab]) \<in> chan s \<longrightarrow> A \<in> good \<longrightarrow>
       (\<exists>Rs. Kab = sesK (Rs$sk) \<and> runs s Rs = Some (Serv, [A, B], [aNon Na]))
  }"

lemmas m2_inv4_M2I = m2_inv4_M2_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv4_M2E [elim] = m2_inv4_M2_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv4_M2D = m2_inv4_M2_def [THEN setc_def_to_dest, rule_format, rotated 1]

text \<open>Invariance proof.\<close>

lemma PO_m2_inv4_M2_init [iff]:
  "init m2 \<subseteq> m2_inv4_M2"
by (auto simp add: m2_defs intro!: m2_inv4_M2I)

lemma PO_m2_inv4_M2_trans [iff]:
  "{m2_inv4_M2} trans m2 {> m2_inv4_M2}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv4_M2I)
apply (auto dest!: m2_inv4_M2D dest: dom_lemmas)
\<comment> \<open>5 subgoals\<close>
apply (force dest!: spec)
apply (force dest!: spec)
apply (force dest!: spec)
apply (rule exI, auto)+
done

lemma PO_m2_inv4_M2 [iff]: "reach m2 \<subseteq> m2_inv4_M2"
by (rule inv_rule_basic) (auto)


subsubsection \<open>inv4b: Secure channel and message 3\<close>
(*inv**************************************************************************)

definition 
  m2_inv4_M3 :: "m2_pred"
where
  "m2_inv4_M3 \<equiv> {s. \<forall>A B Kab.
     Secure Sv B (Msg [aKey Kab, aAgt A]) \<in> chan s \<longrightarrow> B \<in> good \<longrightarrow>
       (\<exists>Rs Na. Kab = sesK (Rs$sk) \<and> runs s Rs = Some (Serv, [A, B], [aNon Na]))
  }"

lemmas m2_inv4_M3I = m2_inv4_M3_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv4_M3E [elim] = m2_inv4_M3_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv4_M3D = m2_inv4_M3_def [THEN setc_def_to_dest, rule_format, rotated 1]

text \<open>Invariance proof.\<close>

lemma PO_m2_inv4_M3_init [iff]:
  "init m2 \<subseteq> m2_inv4_M3"
by (auto simp add: m2_defs intro!: m2_inv4_M3I)

lemma PO_m2_inv4_M3_trans [iff]:
  "{m2_inv4_M3} trans m2 {> m2_inv4_M3}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv4_M3I) 
apply (auto dest!: m2_inv4_M3D dest: dom_lemmas)
\<comment> \<open>5 subgoals\<close>
apply (force)+
done

lemma PO_m2_inv4_M3 [iff]: "reach m2 \<subseteq> m2_inv4_M3"
by (rule inv_rule_incr) (auto del: subsetI)


text \<open>Consequence needed in proof of inv8/step5\<close>

lemma m2_inv4_M2_M3_unique_names:
assumes 
  "Secure Sv A' (Msg [aNon Na, aAgt B', aKey Kab]) \<in> chan s" 
  "Secure Sv B  (Msg [aKey Kab, aAgt A]) \<in> chan s" "aKey Kab \<notin> extr ik0 (chan s)" 
  "s \<in> m2_inv4_M2" "s \<in> m2_inv4_M3"
shows 
  "A = A' \<and> B = B'"
proof (cases "A' \<in> bad \<or> B \<in> bad")
  case True thus ?thesis using assms(1-3) by auto
next
  case False thus ?thesis using assms(1,2,4,5) by (auto dest!: m2_inv4_M2D m2_inv4_M3D)
qed


text \<open>More consequences of invariants. Needed in ref/step4 and ref/step5 
respectively to show the strengthening of the authorization guards.\<close>

lemma m2_inv34_M2_authorized:
  assumes "Secure Sv A (Msg [aNon N, aAgt B, aKey K]) \<in> chan s" 
          "s \<in> m2_inv4_M2" "s \<in> m2_inv3_extrKey" "s \<in> m2_inv2b_corrKey_leaked" 
          "K \<notin> Domain (leak s)" 
  shows   "(K, A) \<in> azC (runs s)"
proof (cases)
  assume "A \<in> bad" 
  hence "aKey K \<in> extr ik0 (chan s)" using assms(1) by auto
  thus ?thesis using assms(3-) by auto 
next
  assume "A \<notin> bad" 
  thus ?thesis using assms(1-2) by (auto dest: m2_inv4_M2D) 
qed

lemma m2_inv34_M3_authorized:
  assumes "Secure Sv B (Msg [aKey K, aAgt A]) \<in> chan s" 
          "s \<in> m2_inv4_M3" "s \<in> m2_inv3_extrKey" "s \<in> m2_inv2b_corrKey_leaked" 
          "K \<notin> Domain (leak s)" 
  shows  "(K, B) \<in> azC (runs s)"
proof (cases)
  assume "B \<in> bad" 
  hence "aKey K \<in> extr ik0 (chan s)" using assms(1) by auto
  thus ?thesis using assms(3-) by auto 
next
  assume "B \<notin> bad"
  thus ?thesis using assms(1-2) by (auto dest: m2_inv4_M3D) 
qed


subsubsection \<open>inv5 (derived): Key secrecy for server\<close>
(*invd*************************************************************************)

text \<open>inv5: Key secrecy from server perspective. This invariant links the 
abstract notion of key secrecy to the intruder key knowledge.\<close>

definition 
  m2_inv5_ikk_sv :: "m2_pred"
where
  "m2_inv5_ikk_sv \<equiv> {s. \<forall>Rs A B Na al.
     runs s Rs = Some (Serv, [A, B], aNon Na # al) \<longrightarrow> A \<in> good \<longrightarrow> B \<in> good \<longrightarrow>
     aKey (sesK (Rs$sk)) \<in> extr ik0 (chan s) \<longrightarrow>
       (\<exists>Nb'. (sesK (Rs$sk), Na, Nb') \<in> leak s)
  }"

lemmas m2_inv5_ikk_svI = m2_inv5_ikk_sv_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv5_ikk_svE [elim] = m2_inv5_ikk_sv_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv5_ikk_svD = m2_inv5_ikk_sv_def [THEN setc_def_to_dest, rule_format, rotated 1]


text \<open>Invariance proof. This invariant follows from \<open>m2_inv3_extrKey\<close>.\<close>

lemma m2_inv5_ikk_sv_derived: 
  "s \<in> m2_inv3_extrKey \<Longrightarrow> s \<in> m2_inv5_ikk_sv"
by (auto simp add: m2_inv3_extrKey_def m2_inv5_ikk_sv_def) (force)

lemma PO_m2_inv5_ikk_sv [iff]: "reach m2 \<subseteq> m2_inv5_ikk_sv"
proof -
  have "reach m2 \<subseteq> m2_inv3_extrKey" by blast
  also have "... \<subseteq> m2_inv5_ikk_sv" by (blast intro: m2_inv5_ikk_sv_derived)
  finally show ?thesis .
qed

(*
lemma PO_m2_inv5_ikk_sv_init [iff]:
  "init m2 \<subseteq> m2_inv5_ikk_sv"
by (auto simp add: m2_defs intro!: m2_inv5_ikk_svI)

lemma PO_m2_inv5_ikk_sv_trans [iff]:
  "{m2_inv5_ikk_sv \<inter> m2_inv3a_sesK_compr \<inter> m2_inv3_extrKey} 
     trans m2 
   {> m2_inv5_ikk_sv}"
apply (simp add: PO_hoare_defs m2_defs, safe intro!: m2_inv5_ikk_svI)
apply (auto simp add: m2_inv3a_sesK_compr_simps dest: dom_lemmas)
done

lemma PO_m2_inv5_ikk_sv [iff]: "reach m2 \<subseteq> m2_inv5_ikk_sv"
by (rule_tac J="m2_inv3a_sesK_compr \<inter> m2_inv3_extrKey" in inv_rule_incr) (auto)
*)


subsubsection \<open>inv6 (derived): Key secrecy for initiator\<close>
(*invd**************************************************************************)

text \<open>This invariant is derivable (see below).\<close>

definition 
  m2_inv6_ikk_init :: "m2_pred"
where
  "m2_inv6_ikk_init \<equiv> {s. \<forall>Ra K A B al.
     runs s Ra = Some (Init, [A, B], aKey K # al) \<longrightarrow> A \<in> good \<longrightarrow> B \<in> good \<longrightarrow>
     aKey K \<in> extr ik0 (chan s) \<longrightarrow>
       (\<exists>Nb'. (K, Ra $ na, Nb') \<in> leak s)     
  }"

lemmas m2_inv6_ikk_initI = m2_inv6_ikk_init_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv6_ikk_initE [elim] = m2_inv6_ikk_init_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv6_ikk_initD = m2_inv6_ikk_init_def [THEN setc_def_to_dest, rule_format, rotated 1]


subsubsection \<open>inv7 (derived): Key secrecy for responder\<close>
(*invd**************************************************************************)

text \<open>This invariant is derivable (see below).\<close>

definition 
  m2_inv7_ikk_resp :: "m2_pred"
where
  "m2_inv7_ikk_resp \<equiv> {s. \<forall>Rb K A B al.
     runs s Rb = Some (Resp, [A, B], aKey K # al) \<longrightarrow> A \<in> good \<longrightarrow> B \<in> good \<longrightarrow>
     aKey K \<in> extr ik0 (chan s) \<longrightarrow>
       K \<in> Domain (leak s) 
  }"

lemmas m2_inv7_ikk_respI = m2_inv7_ikk_resp_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv7_ikk_respE [elim] = m2_inv7_ikk_resp_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv7_ikk_respD = m2_inv7_ikk_resp_def [THEN setc_def_to_dest, rule_format, rotated 1]


subsubsection \<open>inv8: Relating M2 and M4 to the responder state\<close>
(*inv**************************************************************************)

text \<open>This invariant relates messages M2 and M4 to the responder's state. 
It is required in the refinement of step 6 to prove that the initiator 
agrees with the responder on (A, B, Nb, Kab).\<close>

definition
  m2_inv8_M4 :: "m2_pred"
where
  "m2_inv8_M4 \<equiv> {s. \<forall>Kab A B Na Nb.
     Secure Sv A (Msg [aNon Na, aAgt B, aKey Kab]) \<in> chan s \<longrightarrow>
     dAuth Kab (Msg [aNon Nb]) \<in> chan s \<longrightarrow>  
     aKey Kab \<notin> extr ik0 (chan s) \<longrightarrow>
       (\<exists>Rb. Nb = Rb$nb \<and> (\<exists>al. runs s Rb = Some (Resp, [A, B], aKey Kab # al)))
  }"

(* original open subgoal in refinement proof for step6:

1. \<And>s t. \<lbrakk>runs s = runs t; runs t Ra = Some (Init, [A, B], [aKey Kab]);
           dAuth Kab (Msg [aNon Nb]) \<in> chan t; A \<notin> bad; B \<notin> bad\<rbrakk>
          \<Longrightarrow> \<exists>Rb nl. Nb = Rb $ nb \<and> runs t Rb = Some (Resp, [A, B], aKey Kab # nl)
*)

lemmas m2_inv8_M4I = m2_inv8_M4_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv8_M4E [elim] = m2_inv8_M4_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv8_M4D = m2_inv8_M4_def [THEN setc_def_to_dest, rule_format, rotated 1]


text \<open>Invariance proof.\<close>

lemma PO_m2_inv8_M4_step1:
  "{m2_inv8_M4} m2_step1 Ra A B Na {> m2_inv8_M4}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8_M4I)
apply (auto dest!: m2_inv8_M4D dest: dom_lemmas)
done

lemma PO_m2_inv8_M4_step2:
  "{m2_inv8_M4} m2_step2 Rb A B {> m2_inv8_M4}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8_M4I)
apply (auto dest!: m2_inv8_M4D dest: dom_lemmas)
done

lemma PO_m2_inv8_M4_step3:
  "{m2_inv8_M4 \<inter> m2_inv2_keys_for} m2_step3 Rs A B Na Kab {> m2_inv8_M4}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8_M4I)
apply (auto simp add: m2_inv2_keys_for__extr_insert_key dest!: m2_inv8_M4D dest: dom_lemmas)
done

lemma PO_m2_inv8_M4_step4:
  "{m2_inv8_M4} m2_step4 Ra A B Na Kab {> m2_inv8_M4}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8_M4I)
\<comment> \<open>1 subgoal\<close>
apply (drule m2_inv8_M4D, auto) 
apply (rule exI, auto)
done

lemma PO_m2_inv8_M4_step5:
  "{m2_inv8_M4 \<inter> m2_inv4_M3 \<inter> m2_inv4_M2} 
      m2_step5 Rb A B Nb Kab 
   {> m2_inv8_M4}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8_M4I)
apply (auto dest: m2_inv4_M2_M3_unique_names)
apply (auto dest!: m2_inv8_M4D)
done

lemma PO_m2_inv8_M4_step6:
  "{m2_inv8_M4} m2_step6 Ra A B Na Nb Kab {> m2_inv8_M4}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8_M4I)
apply (auto dest!: m2_inv8_M4D)
\<comment> \<open>1 subgoal\<close>
apply (rule exI, auto)
done

lemma PO_m2_inv8_M4_step7:
  "{m2_inv8_M4} m2_step7 Rb A B Nb Kab {> m2_inv8_M4}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8_M4I)
apply (auto dest!: m2_inv8_M4D)
done

lemma PO_m2_inv8_M4_leak:
  "{m2_inv8_M4 \<inter> m2_inv3a_sesK_compr} m2_leak Rs Ra Rb A B {> m2_inv8_M4}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8_M4I)
apply (auto simp add: m2_inv3a_sesK_compr_simps dest!: m2_inv8_M4D)
done

lemma PO_m2_inv8_M4_fake:
  "{m2_inv8_M4} m2_fake {> m2_inv8_M4}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8_M4I)
\<comment> \<open>1 subgoal\<close>
apply (erule fake.cases, auto dest!: m2_inv8_M4D)
done

text \<open>All together now..\<close>

lemmas PO_m2_inv8_M4_lemmas = 
  PO_m2_inv8_M4_step1 PO_m2_inv8_M4_step2 PO_m2_inv8_M4_step3
  PO_m2_inv8_M4_step4 PO_m2_inv8_M4_step5 PO_m2_inv8_M4_step6
  PO_m2_inv8_M4_step7 PO_m2_inv8_M4_leak PO_m2_inv8_M4_fake

lemma PO_m2_inv8_M4_init [iff]:
  "init m2 \<subseteq> m2_inv8_M4"
by (auto simp add: m2_defs intro!: m2_inv8_M4I)

lemma PO_m2_inv8_M4_trans [iff]:
  "{m2_inv8_M4 \<inter> m2_inv4_M3 \<inter> m2_inv4_M2 \<inter> m2_inv3a_sesK_compr \<inter> m2_inv2_keys_for} 
      trans m2 
   {> m2_inv8_M4}"
by (auto simp add: m2_def m2_trans_def intro!: PO_m2_inv8_M4_lemmas)

lemma PO_m2_inv8_M4 [iff]: "reach m2 \<subseteq> m2_inv8_M4"
by (rule_tac J="m2_inv4_M3 \<inter> m2_inv4_M2 \<inter>  m2_inv3a_sesK_compr \<inter> m2_inv2_keys_for" in inv_rule_incr) 
   (auto)


subsubsection \<open>inv8a: Relating the initiator state to M2\<close>
(*inv**************************************************************************)

definition
  m2_inv8a_init_M2 :: "m2_pred"
where
  "m2_inv8a_init_M2 \<equiv> {s. \<forall>Ra A B Kab al.
     runs s Ra = Some (Init, [A, B], aKey Kab # al) \<longrightarrow>
       Secure Sv A (Msg [aNon (Ra$na), aAgt B, aKey Kab]) \<in> chan s
  }"

lemmas m2_inv8a_init_M2I = m2_inv8a_init_M2_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv8a_init_M2E [elim] = m2_inv8a_init_M2_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv8a_init_M2D = m2_inv8a_init_M2_def [THEN setc_def_to_dest, rule_format, rotated 1]


text \<open>Invariance proof.\<close>

lemma PO_m2_inv8a_init_M2_init [iff]:
  "init m2 \<subseteq> m2_inv8a_init_M2"
by (auto simp add: m2_defs intro!: m2_inv8a_init_M2I)

lemma PO_m2_inv8a_init_M2_trans [iff]:
  "{m2_inv8a_init_M2}  
      trans m2 
   {> m2_inv8a_init_M2}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8a_init_M2I) 
apply (blast)
done 

lemma PO_m2_inv8a_init_M2 [iff]: "reach m2 \<subseteq> m2_inv8a_init_M2"
by (rule inv_rule_incr) (auto del: subsetI)


subsubsection \<open>inv9a: Relating the responder state to M3\<close>
(*inv**************************************************************************)

definition
  m2_inv9a_resp_M3 :: "m2_pred"
where
  "m2_inv9a_resp_M3 \<equiv> {s. \<forall>Rb A B Kab al.
     runs s Rb = Some (Resp, [A, B], aKey Kab # al) \<longrightarrow>
       Secure Sv B (Msg [aKey Kab, aAgt A]) \<in> chan s
  }"

lemmas m2_inv9a_resp_M3I = m2_inv9a_resp_M3_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv9a_resp_M3E [elim] = m2_inv9a_resp_M3_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv9a_resp_M3D = m2_inv9a_resp_M3_def [THEN setc_def_to_dest, rule_format, rotated 1]


text \<open>Invariance proof.\<close>

lemma PO_m2_inv9a_resp_M3_init [iff]:
  "init m2 \<subseteq> m2_inv9a_resp_M3"
by (auto simp add: m2_defs intro!: m2_inv9a_resp_M3I)

lemma PO_m2_inv9a_resp_M3_trans [iff]:
  "{m2_inv9a_resp_M3}  
      trans m2 
   {> m2_inv9a_resp_M3}"
by (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9a_resp_M3I dest: m2_inv9a_resp_M3D) 
   (blast)

lemma PO_m2_inv9a_resp_M3 [iff]: "reach m2 \<subseteq> m2_inv9a_resp_M3"
by (rule inv_rule_incr) (auto del: subsetI)


subsubsection \<open>inv9: Relating M3 and M5 to the initiator state\<close>
(*inv**************************************************************************)

text \<open>This invariant relates message M5 to the initiator's state. It is 
required in step 7 of the refinement to prove that the initiator agrees with 
the responder on (A, B, Nb, Kab).\<close>

definition
  m2_inv9_M5 :: "m2_pred"
where
  "m2_inv9_M5 \<equiv> {s. \<forall>Kab A B Nb.
     Secure Sv B (Msg [aKey Kab, aAgt A]) \<in> chan s \<longrightarrow>
     dAuth Kab (Msg [aNon Nb, aNon Nb]) \<in> chan s \<longrightarrow> 
     aKey Kab \<notin> extr ik0 (chan s) \<longrightarrow>
       (\<exists>Ra. runs s Ra = Some (Init, [A, B], [aKey Kab, aNon Nb]))
  }"

(* 
 original subgoal in refinement of step 7:

 1. \<And>s t. \<lbrakk>runs s = runs t; runs t Rb = Some (Resp, [A, B], [aKey Kab]);
           dAuth Kab (Msg [Rb$nb, Rb$nb]) \<in> chan t; A \<notin> bad; B \<notin> bad\<rbrakk>
          \<Longrightarrow> \<exists>Ra. runs t Ra = Some (Init, [A, B], [aKey Kab, aNon Nb])
*)

lemmas m2_inv9_M5I = m2_inv9_M5_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv9_M5E [elim] = m2_inv9_M5_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv9_M5D = m2_inv9_M5_def [THEN setc_def_to_dest, rule_format, rotated 1]


text \<open>Invariance proof.\<close>

lemma PO_m2_inv9_M5_step1:
  "{m2_inv9_M5} m2_step1 Ra A B Na {> m2_inv9_M5}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M5I)
apply (auto dest!: m2_inv9_M5D dest: dom_lemmas)
done

lemma PO_m2_inv9_M5_step2:
  "{m2_inv9_M5} m2_step2 Rb A B {> m2_inv9_M5}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M5I)
apply (auto dest!: m2_inv9_M5D dest: dom_lemmas)
done

lemma PO_m2_inv9_M5_step3:
  "{m2_inv9_M5 \<inter> m2_inv2_keys_for} m2_step3 Rs A B Na Kab {> m2_inv9_M5}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M5I)
apply (auto simp add: m2_inv2_keys_for__extr_insert_key dest!: m2_inv9_M5D dest: dom_lemmas)
done

lemma PO_m2_inv9_M5_step4:
  "{m2_inv9_M5} m2_step4 Ra A B Na Kab {> m2_inv9_M5}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M5I)
apply (auto dest!: m2_inv9_M5D dest: dom_lemmas)
\<comment> \<open>1 subgoal\<close>
apply (rule exI, auto)
done

lemma PO_m2_inv9_M5_step5:
  "{m2_inv9_M5} m2_step5 Rb A B Nb Kab {> m2_inv9_M5}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M5I)
\<comment> \<open>1 subgoal\<close>
apply (drule m2_inv9_M5D, fast, fast, fast, clarsimp)
apply (rule exI, auto)
done

lemma PO_m2_inv9_M5_step6:
  "{m2_inv9_M5 \<inter> m2_inv8a_init_M2 \<inter> m2_inv9a_resp_M3 \<inter> m2_inv4_M2 \<inter> m2_inv4_M3}
     m2_step6 Ra A B Na Nb Kab 
   {> m2_inv9_M5}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M5I)
\<comment> \<open>2 subgoals\<close>
defer 1
  apply (drule m2_inv9_M5D, fast, fast, fast, clarsimp)
  apply (rename_tac Raa, rule_tac x=Raa in exI, auto)

  apply (auto dest!: m2_inv8a_init_M2D m2_inv9a_resp_M3D m2_inv4_M2_M3_unique_names)
done

lemma PO_m2_inv9_M5_step7:
  "{m2_inv9_M5} m2_step7 Rb A B Nb Kab {> m2_inv9_M5}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M5I)
\<comment> \<open>1 subgoal\<close>
apply (drule m2_inv9_M5D, fast, fast, fast, clarsimp)
apply (rule exI, auto)
done

lemma PO_m2_inv9_M5_leak:
  "{m2_inv9_M5 \<inter> m2_inv3a_sesK_compr} m2_leak Rs Ra Rb A B {> m2_inv9_M5}"
by (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M5I)
   (auto simp add: m2_inv3a_sesK_compr_simps dest!: m2_inv9_M5D)

lemma PO_m2_inv9_M5_fake:
  "{m2_inv9_M5} m2_fake {> m2_inv9_M5}"
by (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M5I)
   (auto dest!: m2_inv9_M5D)


text \<open>All together now.\<close>

lemmas PO_m2_inv9_M5_lemmas = 
  PO_m2_inv9_M5_step1 PO_m2_inv9_M5_step2 PO_m2_inv9_M5_step3
  PO_m2_inv9_M5_step4 PO_m2_inv9_M5_step5 PO_m2_inv9_M5_step6
  PO_m2_inv9_M5_step7 PO_m2_inv9_M5_leak PO_m2_inv9_M5_fake

lemma PO_m2_inv9_M5_init [iff]:
  "init m2 \<subseteq> m2_inv9_M5"
by (auto simp add: m2_defs intro!: m2_inv9_M5I)

lemma PO_m2_inv9_M5_trans [iff]:
  "{m2_inv9_M5 \<inter> m2_inv8a_init_M2 \<inter> m2_inv9a_resp_M3 \<inter> 
    m2_inv4_M2 \<inter> m2_inv4_M3 \<inter> m2_inv3a_sesK_compr \<inter> m2_inv2_keys_for} 
      trans m2 
   {> m2_inv9_M5}"
by (auto simp add: m2_def m2_trans_def intro!: PO_m2_inv9_M5_lemmas)

lemma PO_m2_inv9_M5 [iff]: "reach m2 \<subseteq> m2_inv9_M5"
by (rule_tac J="m2_inv8a_init_M2 \<inter> m2_inv9a_resp_M3 \<inter> 
                m2_inv4_M2 \<inter> m2_inv4_M3 \<inter> m2_inv3a_sesK_compr \<inter> m2_inv2_keys_for" 
    in inv_rule_incr) 
   (auto simp add: Int_assoc del: subsetI)


(******************************************************************************)
subsection \<open>Refinement\<close>
(******************************************************************************)

text \<open>The simulation relation. This is a pure superposition refinement.\<close>

definition
  R12 :: "(m1_state \<times> m2_state) set" where
  "R12 \<equiv> {(s, t). runs s = runs t \<and> leak s = leak t}"

text \<open>The mediator function projects on the local states.\<close>

definition 
  med21 :: "m2_obs \<Rightarrow> m1_obs" where
  "med21 o2 = \<lparr> runs = runs o2, leak = leak o2 \<rparr>"


text \<open>Refinement proof.\<close>

lemma PO_m2_step1_refines_m1_step1:
  "{R12} 
     (m1_step1 Ra A B Na), (m2_step1 Ra A B Na) 
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)

lemma PO_m2_step2_refines_m1_step2:
  "{R12} 
     (m1_step2 Rb A B), (m2_step2 Rb A B)
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)

lemma PO_m2_step3_refines_m1_step3:
  "{R12} 
     (m1_step3 Rs A B Na Kab), (m2_step3 Rs A B Na Kab)
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)

lemma PO_m2_step4_refines_m1_step4:
  "{R12 \<inter> UNIV \<times> (m2_inv4_M2 \<inter> m2_inv3_extrKey \<inter> m2_inv2b_corrKey_leaked)} 
     (m1_step4 Ra A B Na Kab), (m2_step4 Ra A B Na Kab)  
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, simp_all)     
   (auto dest: m2_inv34_M2_authorized)

lemma PO_m2_step5_refines_m1_step5:
  "{R12 \<inter> UNIV \<times> (m2_inv4_M3 \<inter> m2_inv3_extrKey \<inter> m2_inv2b_corrKey_leaked)} 
     (m1_step5 Rb A B Nb Kab), (m2_step5 Rb A B Nb Kab) 
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, simp_all)
   (auto dest: m2_inv34_M3_authorized)

lemma PO_m2_step6_refines_m1_step6:
  "{R12 \<inter> UNIV \<times> (m2_inv8a_init_M2 \<inter> m2_inv8_M4 \<inter> m2_inv6_ikk_init)} 
     (m1_step6 Ra A B Na Nb Kab), (m2_step6 Ra A B Na Nb Kab) 
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)
   (auto intro!: m2_inv8_M4D [OF m2_inv8a_init_M2D] dest: m2_inv6_ikk_initD) 

lemma PO_m2_step7_refines_m1_step7:
  "{R12 \<inter> UNIV \<times> (m2_inv9_M5 \<inter> m2_inv9a_resp_M3 \<inter> m2_inv7_ikk_resp)} 
     (m1_step7 Rb A B Nb Kab), (m2_step7 Rb A B Nb Kab) 
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)
   (auto intro!: m2_inv9_M5D [OF m2_inv9a_resp_M3D] dest: m2_inv7_ikk_respD) 

lemma PO_m2_leak_refines_leak:
  "{R12} 
     m1_leak Rs Ra Rb A B, m2_leak Rs Ra Rb A B
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)

lemma PO_m2_fake_refines_skip:
  "{R12} 
     Id, m2_fake
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)


text \<open>Consequences of simulation relation and invariants.\<close>

lemma m2_inv6_ikk_init_derived:
assumes "(s, t) \<in> R12" "s \<in> m1_inv2i_serv" "t \<in> m2_inv5_ikk_sv" 
shows "t \<in> m2_inv6_ikk_init"
proof -
  have "t \<in> m1_inv2i_serv" using assms(1,2) by (simp add: R12_def m1_inv2i_serv_def)
  thus ?thesis using assms(3) 
    by (auto simp add: m2_inv6_ikk_init_def dest: m1_inv2i_servD m2_inv5_ikk_svD)
qed

lemma m2_inv7_ikk_resp_derived:
assumes "(s, t) \<in> R12" "s \<in> m1_inv2r_serv" "t \<in> m2_inv5_ikk_sv" 
shows "t \<in> m2_inv7_ikk_resp"
proof -
  have "t \<in> m1_inv2r_serv" using assms(1,2) by (simp add: R12_def m1_inv2r_serv_def)
  thus ?thesis using assms(3) 
    by (auto simp add: m2_inv7_ikk_resp_def dest!: m1_inv2r_servD m2_inv5_ikk_svD)
qed


text \<open>All together now...\<close>

lemmas PO_m2_trans_refines_m1_trans = 
  PO_m2_step1_refines_m1_step1 PO_m2_step2_refines_m1_step2
  PO_m2_step3_refines_m1_step3 PO_m2_step4_refines_m1_step4
  PO_m2_step5_refines_m1_step5 PO_m2_step6_refines_m1_step6 
  PO_m2_step7_refines_m1_step7 PO_m2_leak_refines_leak 
  PO_m2_fake_refines_skip 

lemma PO_m2_refines_init_m1 [iff]:
  "init m2 \<subseteq> R12``(init m1)"
by (auto simp add: R12_def m2_defs)

lemma PO_m2_refines_trans_m1 [iff]:
  "{R12 \<inter> 
    (reach m1 \<times> 
     (m2_inv9_M5 \<inter> m2_inv8a_init_M2 \<inter> m2_inv9a_resp_M3 \<inter> m2_inv8_M4 \<inter> 
      m2_inv4_M3 \<inter> m2_inv4_M2 \<inter> m2_inv3a_sesK_compr \<inter> m2_inv3_extrKey \<inter> m2_inv2b_corrKey_leaked))} 
     (trans m1), (trans m2) 
   {> R12}"
proof -
  \<comment> \<open>derive the key secrecy invariants from simulation relation and the other invariants\<close>
  let ?pre' = "R12 \<inter> (UNIV \<times> (m2_inv9_M5 \<inter> m2_inv8a_init_M2 \<inter> m2_inv9a_resp_M3 \<inter> 
               m2_inv8_M4 \<inter> m2_inv7_ikk_resp \<inter> m2_inv6_ikk_init \<inter> m2_inv5_ikk_sv \<inter> 
               m2_inv4_M3 \<inter> m2_inv4_M2 \<inter> m2_inv3a_sesK_compr \<inter> m2_inv3_extrKey \<inter> 
               m2_inv2b_corrKey_leaked))"
  show ?thesis (is "{?pre} ?t1, ?t2 {>?post}")
  proof (rule relhoare_conseq_left)
    show "?pre \<subseteq> ?pre'"
      by (auto intro: m2_inv6_ikk_init_derived m2_inv7_ikk_resp_derived m2_inv5_ikk_sv_derived)
  next 
    show "{?pre'} ?t1, ?t2 {> ?post}"
      by (auto simp add: m2_def m2_trans_def m1_def m1_trans_def)
         (blast intro!: PO_m2_trans_refines_m1_trans)+
  qed
qed    

lemma PO_obs_consistent_R12 [iff]: 
  "obs_consistent R12 med21 m1 m2"
by (auto simp add: obs_consistent_def R12_def med21_def m2_defs)


text \<open>Refinement result.\<close>

lemma m2_refines_m1 [iff]:
  "refines 
     (R12 \<inter> 
      (reach m1 \<times> 
       (m2_inv9_M5 \<inter> m2_inv8a_init_M2 \<inter> m2_inv9a_resp_M3 \<inter> m2_inv8_M4 \<inter> 
        m2_inv4_M3 \<inter> m2_inv4_M2 \<inter> m2_inv3a_sesK_compr \<inter> m2_inv3_extrKey \<inter> 
        m2_inv2b_corrKey_leaked \<inter> m2_inv2_keys_for \<inter> m2_inv1_keys)))
     med21 m1 m2"
by (rule Refinement_using_invariants) (auto)

lemma m2_implements_m1 [iff]:
  "implements med21 m1 m2"
by (rule refinement_soundness) (auto)


(******************************************************************************)
subsection \<open>Inherited and derived invariants\<close>
(******************************************************************************)

text \<open>Show preservation of invariants @{term "m1_inv2i_serv"} and
@{term "m1_inv2r_serv"} from \<open>m1\<close>.\<close>

(*invh*************************************************************************)

lemma PO_m2_sat_m1_inv2i_serv [iff]: "reach m2 \<subseteq> m1_inv2i_serv"
apply (rule_tac Pa=m1_inv2i_serv and Qa=m1_inv2i_serv and Q=m1_inv2i_serv 
       in m2_implements_m1 [THEN [5] internal_invariant_translation])
apply (auto simp add: m2_loc_defs med21_def intro!: m1_inv2i_servI)
done

(*invh*************************************************************************)

lemma PO_m2_sat_m1_inv2r_serv [iff]: "reach m2 \<subseteq> m1_inv2r_serv"
by (rule_tac Pa=m1_inv2r_serv and Qa=m1_inv2r_serv and Q=m1_inv2r_serv
    in m2_implements_m1 [THEN [5] internal_invariant_translation])
   (fastforce simp add: m2_defs med21_def intro!: m1_inv2r_servI)+

text \<open>Now we derive the additional invariants for the initiator and the responder 
(see above for the definitions).\<close>

lemma PO_m2_inv6_init_ikk [iff]: "reach m2 \<subseteq> m2_inv6_ikk_init"
proof -
  have "reach m2 \<subseteq> m1_inv2i_serv \<inter> m2_inv5_ikk_sv" by simp
  also have "... \<subseteq> m2_inv6_ikk_init" by (blast intro!: m2_inv6_ikk_initI dest: m2_inv5_ikk_svD)
  finally show ?thesis .
qed

lemma PO_m2_inv6_resp_ikk [iff]: "reach m2 \<subseteq> m2_inv7_ikk_resp"
proof -
  have "reach m2 \<subseteq> m1_inv2r_serv \<inter> m2_inv5_ikk_sv" by simp
  also have "... \<subseteq> m2_inv7_ikk_resp" by (blast intro!: m2_inv7_ikk_respI dest: m2_inv5_ikk_svD)
  finally show ?thesis .
qed


end

