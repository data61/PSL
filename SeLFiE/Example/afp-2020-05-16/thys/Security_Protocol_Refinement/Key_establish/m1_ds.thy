(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:   Key_establish/m1_ds.thy (Isabelle/HOL 2016-1)
  ID:       $Id: m1_ds.thy 133856 2017-03-20 18:05:54Z csprenge $
  Author:   Ivano Somaini, ETH Zurich <somainii@student.ethz.ch>
            Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>

  Key distribution protocols
  abstract version of Denning-Sacco with non-injective server authentication 
  using timestamps

  Copyright (c) 2009-2016 Ivano Somaini, Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Abstract Denning-Sacco protocol (L1)\<close>

theory m1_ds imports m1_keydist_inrn "../Refinement/a0n_agree"
begin

text \<open>We augment the basic abstract key distribution model such that 
the server sends a timestamp along with the session key. We check the 
timestamp's validity to ensure recentness of the session key. 

We establish one refinement for this model, namely that this model refines
the basic authenticated key transport model \<open>m1_keydist_inrn\<close>, 
which guarantees non-injective agreement with the server on the session key
and the server-generated timestamp.
\<close>


(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>We extend the basic key distribution by adding timestamps. 
We add a clock variable modeling the current time.  The frames, runs, and 
observations remain the same as in the previous model, but we will use 
the @{typ "nat list"}'s to store timestamps. 
\<close>

type_synonym
  time = "nat"                     \<comment> \<open>for clock and timestamps\<close>

consts
  Ls :: "time"                     \<comment> \<open>life time for session keys\<close>


text \<open>State and observations\<close>

record
  m1_state = "m1x_state" +
    clk :: "time" 

type_synonym
  m1_obs = "m1_state"

type_synonym
  'x m1_pred = "'x m1_state_scheme set"

type_synonym
  'x m1_trans = "('x m1_state_scheme \<times> 'x m1_state_scheme) set"


text \<open>Instantiate parameters regarding list of freshness identifiers stored
at server.\<close>

overloading is_len' \<equiv> "is_len" rs_len' \<equiv> "rs_len" begin
definition is_len_def [simp]: "is_len' \<equiv> 1::nat"
definition rs_len_def [simp]: "rs_len' \<equiv> 1::nat"
end


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

definition         \<comment> \<open>by @{term "A"}, refines @{term "m1x_step1"}\<close>
  m1_step1 :: "[rid_t, agent, agent] \<Rightarrow> 'x m1_trans"
where
  "m1_step1 \<equiv> m1a_step1"

definition       \<comment> \<open>by @{term "B"}, refines @{term "m1x_step2"}\<close>
  m1_step2 :: "[rid_t, agent, agent] \<Rightarrow> 'x m1_trans"
where
  "m1_step2 \<equiv> m1a_step2"

definition       \<comment> \<open>by @{term "Server"}, refines @{term m1x_step3}\<close>
  m1_step3 :: "[rid_t, agent, agent, key, time] \<Rightarrow> 'x m1_trans"
where
  "m1_step3 Rs A B Kab Ts \<equiv> {(s, s').
     \<comment> \<open>new guards:\<close>
     Ts = clk s \<and>                      \<comment> \<open>fresh timestamp\<close>

     \<comment> \<open>rest as before:\<close>
     (s, s') \<in> m1a_step3 Rs A B Kab [aNum Ts]
  }"

definition         \<comment> \<open>by @{text "A"}, refines @{term m1x_step5}\<close>
  m1_step4 :: "[rid_t, agent, agent, key, time] \<Rightarrow> 'x m1_trans"
where
  "m1_step4 Ra A B Kab Ts \<equiv> {(s, s').
     \<comment> \<open>new guards:\<close>
     clk s < Ts + Ls \<and>                \<comment> \<open>ensure session key recentness\<close>

     \<comment> \<open>rest as before\<close>
     (s, s') \<in> m1a_step4 Ra A B Kab [aNum Ts] 
  }"

definition         \<comment> \<open>by @{term "B"}, refines @{term m1x_step4}\<close>
  m1_step5 :: "[rid_t, agent, agent, key, time] \<Rightarrow> 'x m1_trans"
where
  "m1_step5 Rb A B Kab Ts \<equiv> {(s, s'). 
     \<comment> \<open>new guards:\<close>
     \<comment> \<open>ensure freshness of session key\<close>
     clk s < Ts + Ls \<and>

     \<comment> \<open>rest as before\<close>
     (s, s') \<in> m1a_step5 Rb A B Kab [aNum Ts] 
  }"

definition     \<comment> \<open>refines @{term skip}\<close>
  m1_tick :: "time \<Rightarrow> 'x m1_trans"
where
  "m1_tick T \<equiv> {(s, s').
     s' = s\<lparr> clk := clk s + T \<rparr> 
  }"

definition         \<comment> \<open>by attacker, refines @{term m1x_leak}\<close>
  m1_leak :: "[rid_t] \<Rightarrow> 'x m1_trans"
where
  "m1_leak \<equiv> m1a_leak"



(******************************************************************************)
subsection \<open>Specification\<close>
(******************************************************************************)

definition
  m1_init :: "unit m1_pred"
where
  "m1_init \<equiv> { \<lparr> runs = Map.empty, leak = corrKey, clk = 0 \<rparr> }" 

definition 
  m1_trans :: "'x m1_trans" where
  "m1_trans \<equiv> (\<Union>A B Ra Rb Rs Kab Ts T.
        m1_step1 Ra A B \<union>
        m1_step2 Rb A B \<union>
        m1_step3 Rs A B Kab Ts \<union>
        m1_step4 Ra A B Kab Ts \<union>
        m1_step5 Rb A B Kab Ts \<union>
        m1_tick T \<union>
        m1_leak Rs \<union>
        Id
  )"

definition 
  m1 :: "(m1_state, m1_obs) spec" where
  "m1 \<equiv> \<lparr>
      init = m1_init,
      trans = m1_trans,
      obs = id
  \<rparr>" 

lemmas m1_loc_defs = 
  m1_def m1_init_def m1_trans_def
  m1_step1_def m1_step2_def m1_step3_def m1_step4_def m1_step5_def 
  m1_leak_def m1_tick_def

lemmas m1_defs = m1_loc_defs m1a_defs

lemma m1_obs_id [simp]: "obs m1 = id"
by (simp add: m1_def)


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

subsubsection \<open>inv0: Finite domain\<close>
(******************************************************************************)

text \<open>There are only finitely many runs. This is needed to establish
the responder/initiator agreement.\<close>

definition 
  m1_inv0_fin :: "'x m1_pred"
where
  "m1_inv0_fin \<equiv> {s. finite (dom (runs s))}"

lemmas m1_inv0_finI = m1_inv0_fin_def [THEN setc_def_to_intro, rule_format]
lemmas m1_inv0_finE [elim] = m1_inv0_fin_def [THEN setc_def_to_elim, rule_format]
lemmas m1_inv0_finD = m1_inv0_fin_def [THEN setc_def_to_dest, rule_format]

text \<open>Invariance proofs.\<close>

lemma PO_m1_inv0_fin_init [iff]:
  "init m1 \<subseteq> m1_inv0_fin"
by (auto simp add: m1_defs intro!: m1_inv0_finI)

lemma PO_m1_inv0_fin_trans [iff]:
  "{m1_inv0_fin} trans m1 {> m1_inv0_fin}"
by (auto simp add: PO_hoare_defs m1_defs intro!: m1_inv0_finI)

lemma PO_m1_inv0_fin [iff]: "reach m1 \<subseteq> m1_inv0_fin"
by (rule inv_rule_incr, auto del: subsetI)


(******************************************************************************)
subsection \<open>Refinement of \<open>m1a\<close>\<close>
(******************************************************************************)

subsubsection \<open>Simulation relation\<close>
(******************************************************************************)

text \<open>R1a1: The simulation relation and mediator function are identities.\<close>

definition
  med1a1 :: "m1_obs \<Rightarrow> m1a_obs" where
  "med1a1 t \<equiv> \<lparr> runs = runs t, leak = leak t \<rparr>"
   
definition
  R1a1 :: "(m1a_state \<times> m1_state) set" where
  "R1a1 \<equiv> {(s, t). s = med1a1 t}"

lemmas R1a1_defs = R1a1_def med1a1_def 


subsubsection \<open>Refinement proof\<close>
(******************************************************************************)

lemma PO_m1_step1_refines_m1a_step1:
  "{R1a1} 
     (m1a_step1 Ra A B), (m1_step1 Ra A B) 
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs)

lemma PO_m1_step2_refines_m1a_step2:
  "{R1a1} 
     (m1a_step2 Rb A B), (m1_step2 Rb A B) 
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs)

lemma PO_m1_step3_refines_m1a_step3:
  "{R1a1} 
     (m1a_step3 Rs A B Kab [aNum Ts]), (m1_step3 Rs A B Kab Ts)
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs)

lemma PO_m1_step4_refines_m1a_step4:
  "{R1a1} 
     (m1a_step4 Ra A B Kab [aNum Ts]), (m1_step4 Ra A B Kab Ts) 
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs)

lemma PO_m1_step5_refines_m1a_step5:
  "{R1a1} 
     (m1a_step5 Rb A B Kab [aNum Ts]), (m1_step5 Rb A B Kab Ts) 
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs)

lemma PO_m1_leak_refines_m1a_leak:
  "{R1a1} 
     (m1a_leak Rs), (m1_leak Rs) 
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs)

lemma PO_m1_tick_refines_m1a_skip:
  "{R1a1} 
     Id, (m1_tick T) 
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs)


text \<open>All together now...\<close>

lemmas PO_m1_trans_refines_m1a_trans = 
  PO_m1_step1_refines_m1a_step1 PO_m1_step2_refines_m1a_step2
  PO_m1_step3_refines_m1a_step3 PO_m1_step4_refines_m1a_step4
  PO_m1_step5_refines_m1a_step5 PO_m1_leak_refines_m1a_leak 
  PO_m1_tick_refines_m1a_skip 

lemma PO_m1_refines_init_m1a [iff]:
  "init m1 \<subseteq>  R1a1``(init m1a)"
by (auto simp add: R1a1_defs m1_defs intro!: s0g_secrecyI)

lemma PO_m1_refines_trans_m1a [iff]:
  "{R1a1} 
     (trans m1a), (trans m1) 
   {> R1a1}"
apply (auto simp add: m1_def m1_trans_def m1a_def m1a_trans_def
         intro!: PO_m1_trans_refines_m1a_trans)
apply (force intro!: PO_m1_trans_refines_m1a_trans)+
done

text \<open>Observation consistency.\<close>

lemma obs_consistent_med1a1 [iff]: 
  "obs_consistent R1a1 med1a1 m1a m1"
by (auto simp add: obs_consistent_def R1a1_def m1a_def m1_def)


text \<open>Refinement result.\<close>

lemma PO_m1_refines_m1a [iff]: 
  "refines R1a1 med1a1 m1a m1"
by (rule Refinement_basic) (auto del: subsetI)

lemma  m1_implements_m1: "implements med1a1 m1a m1"
by (rule refinement_soundness) (fast)


end
