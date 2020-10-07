(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:   Key_establish/m1_kerberos.thy (Isabelle/HOL 2016)
  ID:       $Id: m1_kerberos.thy 133856 2017-03-20 18:05:54Z csprenge $
  Author:   Ivano Somaini, ETH Zurich <somainii@student.ethz.ch>
            Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>

  Key distribution protocols
  Abstract version of Kerberos protocol with server-authentication and
  mutual initiator and responder authentication.

  Copyright (c) 2009-2016 Ivano Somaini, Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Abstract Kerberos core protocol (L1)\<close>

theory m1_kerberos imports m1_keydist_iirn
begin

text \<open>We augment the basic abstract key distribution model such that 
the server sends a timestamp along with the session key. We use a cache to 
guard against replay attacks and timestamp validity checks to ensure recentness
of the session key. 

We establish three refinements for this model, namely that this model refines
\begin{enumerate}
\item the authenticated key distribution model \<open>m1_keydist_iirn\<close>, 

\item the injective agreement model \<open>a0i\<close>, instantiated such that 
the responder agrees with the initiator on the session key, its timestamp
and the initiator's authenticator timestamp.

\item the injective agreement model \<open>a0i\<close>, instantiated such that 
the initiator agrees with the responder on the session key, its timestamp
and the initiator's authenticator timestamp.
\end{enumerate}
\<close>

(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>We extend the basic key distribution by adding timestamps. 
We add a clock variable modeling the current time and an authenticator
replay cache recording triples @{term "(A, Kab, Ta)"} of agents, session keys,
and authenticator timestamps. The inclusion of the session key avoids false
replay rejections for different keys with identical authenticator timestamps.

The frames, runs, and observations remain the same as in the previous model, 
but we will use the @{typ "nat list"}'s to store timestamps. 
\<close>

type_synonym
  time = "nat"                     \<comment> \<open>for clock and timestamps\<close>

consts
  Ls :: "time"                     \<comment> \<open>life time for session keys\<close>
  La :: "time"                     \<comment> \<open>life time for authenticators\<close>


text \<open>State and observations\<close>

record
  m1_state = "m1r_state" +
    leak :: "(key \<times> agent \<times> agent \<times> nonce \<times> time) set"   \<comment> \<open>key leaked plus context\<close>
    clk :: "time" 
    cache :: "(agent \<times> key \<times> time) set" 

type_synonym m1_obs = "m1_state"

type_synonym 'x m1_pred = "'x m1_state_scheme set"
type_synonym 'x m1_trans = "('x m1_state_scheme \<times> 'x m1_state_scheme) set"

consts
  END :: "atom"                    \<comment> \<open>run end marker (for initiator)\<close>


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

definition         \<comment> \<open>by @{term "A"}, refines @{term "m1x_step1"}\<close>
  m1_step1 :: "[rid_t, agent, agent, nonce] \<Rightarrow> 'x m1_trans"
where
  "m1_step1 \<equiv> m1a_step1"

definition       \<comment> \<open>by @{term "B"}, refines @{term "m1x_step2"}\<close>
  m1_step2 :: "[rid_t, agent, agent] \<Rightarrow> 'x m1_trans"
where
  "m1_step2 \<equiv> m1a_step2"

definition       \<comment> \<open>by @{term "Server"}, refines @{term m1x_step3}\<close>
  m1_step3 :: "[rid_t, agent, agent, key, nonce, time] \<Rightarrow> 'x m1_trans"
where
  "m1_step3 Rs A B Kab Na Ts \<equiv> {(s, s').
     \<comment> \<open>new guards:\<close>
     Ts = clk s \<and>                      \<comment> \<open>fresh timestamp\<close>

     \<comment> \<open>rest as before:\<close>
     (s, s') \<in> m1a_step3 Rs A B Kab Na [aNum Ts]
  }"

definition         \<comment> \<open>by @{text "A"}, refines @{term m1x_step5}\<close>
  m1_step4 :: "[rid_t, agent, agent, nonce, key, time, time] \<Rightarrow> 'x m1_trans"
where
  "m1_step4 Ra A B Na Kab Ts Ta \<equiv> {(s, s').
     \<comment> \<open>previous guards:\<close>
     runs s Ra = Some (Init, [A, B], []) \<and>
     (Kab \<notin> Domain (leak s) \<longrightarrow> (Kab, A) \<in> azC (runs s)) \<and>   \<comment> \<open>authorization guard\<close>
     Na = Ra$na \<and>                                     \<comment> \<open>fix parameter\<close>

     \<comment> \<open>guard for agreement with server on \<open>(Kab, B, Na, isl)\<close>,\<close>
     \<comment> \<open>where \<open>isl = take is_len nla\<close>; injectiveness by including \<open>Na\<close>\<close>
     (A \<notin> bad \<longrightarrow> (\<exists>Rs. Kab = sesK (Rs$sk) \<and>
        runs s Rs = Some (Serv, [A, B], [aNon Na, aNum Ts]))) \<and>

     \<comment> \<open>new guards:\<close>
     Ta = clk s \<and>                     \<comment> \<open>fresh timestamp\<close>
     clk s < Ts + Ls \<and>                \<comment> \<open>ensure session key recentness\<close>

     \<comment> \<open>actions:\<close>
     s' = s\<lparr> runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta])) \<rparr>
  }"

definition         \<comment> \<open>by @{term "B"}, refines @{term m1x_step4}\<close>
  m1_step5 :: "[rid_t, agent, agent, key, time, time] \<Rightarrow> 'x m1_trans"
where
  "m1_step5 Rb A B Kab Ts Ta \<equiv> {(s, s'). 
     \<comment> \<open>previous guards:\<close>
     runs s Rb = Some (Resp, [A, B], []) \<and> 
     (Kab \<notin> Domain (leak s) \<longrightarrow> (Kab, B) \<in> azC (runs s)) \<and>  \<comment> \<open>authorization guard\<close>

     \<comment> \<open>guard for showing agreement with server on \<open>(Kab, A, rsl)\<close>,\<close>
     \<comment> \<open>where \<open>rsl = take rs_len nlb\<close>; this agreement is non-injective\<close>
     (B \<notin> bad \<longrightarrow> (\<exists>Rs Na. Kab = sesK (Rs$sk) \<and>
        runs s Rs = Some (Serv, [A, B], [aNon Na, aNum Ts]))) \<and>

     \<comment> \<open>new guards:\<close>
     \<comment> \<open>guard for showing agreement with initiator \<open>A\<close> on \<open>(Kab, Ts, Ta)\<close>\<close>
     (A \<notin> bad \<longrightarrow> B \<notin> bad \<longrightarrow> 
       (\<exists>Ra nl. runs s Ra = Some (Init, [A, B], aKey Kab # aNum Ts # aNum Ta # nl))) \<and>

     \<comment> \<open>ensure recentness of session key\<close>
     clk s < Ts + Ls \<and>

     \<comment> \<open>check validity of authenticator and prevent its replay\<close>
     \<comment> \<open>'replays' with fresh authenticator ok!\<close>
     clk s < Ta + La \<and> 
     (B, Kab, Ta) \<notin> cache s \<and> 

     \<comment> \<open>actions:\<close>
     s' = s\<lparr>
       runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [aKey Kab, aNum Ts, aNum Ta])),
       cache := insert (B, Kab, Ta) (cache s) 
     \<rparr>
  }"

definition         \<comment> \<open>by @{term "A"}, refines @{term skip}\<close>
  m1_step6 :: "[rid_t, agent, agent, nonce, key, time, time] \<Rightarrow> 'x m1_trans"
where
  "m1_step6 Ra A B Na Kab Ts Ta \<equiv> {(s, s').
     runs s Ra = Some (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta]) \<and>  \<comment> \<open>key recv'd before\<close>
     Na = Ra$na \<and>                                                     \<comment> \<open>fix parameter\<close>

     \<comment> \<open>check key's freshness [NEW]\<close>
     \<comment> \<open>\<open>clk s < Ts + Ls \<and>\<close>\<close>

     \<comment> \<open>guard for showing agreement with \<open>B\<close> on \<open>Kab\<close>, \<open>Ts\<close>, and \<open>Ta\<close>\<close>
     (A \<notin> bad \<longrightarrow> B \<notin> bad \<longrightarrow> 
       (\<exists>Rb. runs s Rb = Some (Resp, [A, B], [aKey Kab, aNum Ts, aNum Ta]))) \<and> 

     \<comment> \<open>actions: (redundant) update local state marks successful termination\<close>
     s' = s\<lparr>
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta, END])) 
     \<rparr>
  }"

definition         \<comment> \<open>by attacker, refines @{term m1a_leak}\<close>
  m1_leak :: "[rid_t, agent, agent, nonce, time] \<Rightarrow> 'x m1_trans"
where
  "m1_leak Rs A B Na Ts \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    runs s Rs = Some (Serv, [A, B], [aNon Na, aNum Ts]) \<and> 
    (clk s \<ge> Ts + Ls) \<and>             \<comment> \<open>only compromise 'old' session keys\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>record session key as leaked;\<close>
    s1 = s\<lparr> leak := insert (sesK (Rs$sk), A, B, Na, Ts) (leak s) \<rparr> 
  }"


text \<open>Clock tick event\<close>

definition     \<comment> \<open>refines @{term skip}\<close>
  m1_tick :: "time \<Rightarrow> 'x m1_trans"
where
  "m1_tick T \<equiv> {(s, s').
     s' = s\<lparr> clk := clk s + T \<rparr> 
  }"


text \<open>Purge event: purge cache of expired timestamps\<close>

definition     \<comment> \<open>refines @{term skip}\<close>
  m1_purge :: "agent \<Rightarrow> 'x m1_trans"
where
  "m1_purge A \<equiv> {(s, s').
     s' = s\<lparr> 
       cache := cache s - {(A, K, T) | A K T. 
         (A, K, T) \<in> cache s \<and> T + La \<le> clk s
       } 
     \<rparr> 
  }"


(******************************************************************************)
subsection \<open>Specification\<close>
(******************************************************************************)

definition
  m1_init :: "m1_state set"
where
  "m1_init \<equiv> { \<lparr> runs = Map.empty, leak = corrKey \<times> {undefined}, clk = 0, cache = {} \<rparr> }" 

definition 
  m1_trans :: "'x m1_trans" where
  "m1_trans \<equiv> (\<Union>A B Ra Rb Rs Na Kab Ts Ta T.
        m1_step1 Ra A B Na \<union>
        m1_step2 Rb A B \<union>
        m1_step3 Rs A B Kab Na Ts \<union>
        m1_step4 Ra A B Na Kab Ts Ta \<union>
        m1_step5 Rb A B Kab Ts Ta \<union>
        m1_step6 Ra A B Na Kab Ts Ta \<union> 
        m1_leak Rs A B Na Ts \<union>
        m1_tick T \<union>
        m1_purge A \<union> 
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
  m1_step6_def m1_leak_def m1_purge_def m1_tick_def

lemmas m1_defs = m1_loc_defs m1a_defs

lemma m1_obs_id [simp]: "obs m1 = id"
by (simp add: m1_def)


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

subsubsection \<open>inv0: Finite domain\<close>
(*inv**************************************************************************)

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


subsubsection \<open>inv1: Caching invariant for responder\<close>
(*inv**************************************************************************)

definition 
  m1_inv1r_cache :: "'x m1_pred"
where
  "m1_inv1r_cache \<equiv> {s. \<forall>Rb A B Kab Ts Ta nl.
     runs s Rb = Some (Resp, [A, B], aKey Kab # aNum Ts # aNum Ta # nl) \<longrightarrow> 
     clk s < Ta + La \<longrightarrow>
       (B, Kab, Ta) \<in> cache s
  }"

lemmas m1_inv1r_cacheI = m1_inv1r_cache_def [THEN setc_def_to_intro, rule_format]
lemmas m1_inv1r_cacheE [elim] = m1_inv1r_cache_def [THEN setc_def_to_elim, rule_format]
lemmas m1_inv1r_cacheD = m1_inv1r_cache_def [THEN setc_def_to_dest, rule_format, rotated 1]


text \<open>Invariance proof\<close>

lemma PO_m1_inv1r_cache_init [iff]:
  "init m1 \<subseteq> m1_inv1r_cache"
by (auto simp add: m1_defs intro!: m1_inv1r_cacheI)

lemma PO_m1_inv1r_cache_trans [iff]:
  "{m1_inv1r_cache} trans m1 {> m1_inv1r_cache}"
apply (auto simp add: PO_hoare_defs m1_defs intro!: m1_inv1r_cacheI
            dest: m1_inv1r_cacheD)
apply (auto dest: m1_inv1r_cacheD)
done

lemma PO_m1_inv1r_cache [iff]: "reach m1 \<subseteq> m1_inv1r_cache"
by (rule inv_rule_basic) (auto del: subsetI)


(******************************************************************************)
subsection \<open>Refinement of \<open>m1a\<close>\<close>
(******************************************************************************)

subsubsection \<open>Simulation relation\<close>
(******************************************************************************)

text \<open>The abstraction removes all but the first freshness
identifiers (corresponding to \<open>Kab\<close> and \<open>Ts\<close>) from the 
initiator and responder frames and leaves the server's freshness ids untouched.
\<close>

overloading is_len' \<equiv> "is_len" rs_len' \<equiv> "rs_len" begin
definition is_len_def [simp]: "is_len' \<equiv> 1::nat"
definition rs_len_def [simp]: "rs_len' \<equiv> 1::nat"
end

fun 
  rm1a1 :: "role_t \<Rightarrow> atom list \<Rightarrow> atom list"
where
  "rm1a1 Init = take (Suc is_len)"       \<comment> \<open>take \<open>Kab\<close>, \<open>Ts\<close>; drop \<open>Ta\<close>\<close>
| "rm1a1 Resp = take (Suc rs_len)"       \<comment> \<open>take \<open>Kab\<close>, \<open>Ts\<close>; drop \<open>Ta\<close>\<close>
| "rm1a1 Serv = id"                      \<comment> \<open>take \<open>Na\<close>, \<open>Ts\<close>\<close>

abbreviation 
  runs1a1 :: "runs_t \<Rightarrow> runs_t" where
  "runs1a1 \<equiv> map_runs rm1a1" 

lemma knC_runs1a1 [simp]:
  "knC (runs1a1 runz) = knC runz"
apply (auto simp add: map_runs_def elim!: knC.cases)
apply (rename_tac b, case_tac b, auto)
apply (rename_tac b, case_tac b, auto)
apply (rule knC_init, auto simp add: map_runs_def)
apply (rule knC_resp, auto simp add: map_runs_def)
apply (rule_tac knC_serv, auto simp add: map_runs_def)
done

text \<open>med1a1: The mediator function maps a concrete observation (i.e., run) 
to an abstract one.\<close>

text \<open>R1a1: The simulation relation is defined in terms of the mediator
function.\<close>

definition
  med1a1 :: "m1_obs \<Rightarrow> m1a_obs" where
  "med1a1 s \<equiv> \<lparr> runs = runs1a1 (runs s), m1x_state.leak = Domain (leak s) \<rparr>"
   
definition
  R1a1 :: "(m1a_state \<times> m1_state) set" where
  "R1a1 \<equiv> {(s, t). s = med1a1 t}"

lemmas R1a1_defs = R1a1_def med1a1_def 


subsubsection \<open>Refinement proof\<close>
(******************************************************************************)

lemma PO_m1_step1_refines_m1a_step1:
  "{R1a1} 
     (m1a_step1 Ra A B Na), (m1_step1 Ra A B Na) 
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs)

lemma PO_m1_step2_refines_m1a_step2:
  "{R1a1} 
     (m1a_step2 Rb A B), (m1_step2 Rb A B) 
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs)

lemma PO_m1_step3_refines_m1a_step3:
  "{R1a1} 
     (m1a_step3 Rs A B Kab Na [aNum Ts]), (m1_step3 Rs A B Kab Na Ts)
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs)

lemma PO_m1_step4_refines_m1a_step4:
  "{R1a1} 
     (m1a_step4 Ra A B Na Kab [aNum Ts]), (m1_step4 Ra A B Na Kab Ts Ta) 
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs map_runs_def)

lemma PO_m1_step5_refines_m1a_step5:
  "{R1a1} 
     (m1a_step5 Rb A B Kab [aNum Ts]), (m1_step5 Rb A B Kab Ts Ta) 
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs map_runs_def)

lemma PO_m1_step6_refines_m1a_skip:
  "{R1a1} 
     Id, (m1_step6 Ra A B Na Kab Ts Ta)
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs map_runs_def)

lemma PO_m1_leak_refines_m1a_leak:
  "{R1a1} 
     (m1a_leak Rs), (m1_leak Rs A B Na Ts)
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs map_runs_def dest: dom_lemmas)

lemma PO_m1_tick_refines_m1a_skip:
  "{R1a1} 
     Id, (m1_tick T) 
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs map_runs_def)

lemma PO_m1_purge_refines_m1a_skip:
  "{R1a1} 
     Id, (m1_purge A) 
   {> R1a1}"
by (auto simp add: PO_rhoare_defs R1a1_defs m1_defs map_runs_def)

text \<open>All together now...\<close>

lemmas PO_m1_trans_refines_m1a_trans = 
  PO_m1_step1_refines_m1a_step1 PO_m1_step2_refines_m1a_step2
  PO_m1_step3_refines_m1a_step3 PO_m1_step4_refines_m1a_step4
  PO_m1_step5_refines_m1a_step5 PO_m1_step6_refines_m1a_skip 
  PO_m1_leak_refines_m1a_leak PO_m1_tick_refines_m1a_skip 
  PO_m1_purge_refines_m1a_skip

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

lemma  m1_implements_m1a [iff]: "implements med1a1 m1a m1"
by (rule refinement_soundness) (fast)


subsubsection \<open>inv (inherited): Secrecy\<close>
(*invh*************************************************************************)

text \<open>Secrecy, as external and internal invariant\<close>

definition 
  m1_secrecy :: "'x m1_pred" where
  "m1_secrecy \<equiv> {s. knC (runs s) \<subseteq> azC (runs s) \<union> Domain (leak s) \<times> UNIV}"

lemmas m1_secrecyI = m1_secrecy_def [THEN setc_def_to_intro, rule_format]
lemmas m1_secrecyE [elim] = m1_secrecy_def [THEN setc_def_to_elim, rule_format]

lemma PO_m1_obs_secrecy [iff]: "oreach m1 \<subseteq> m1_secrecy"
apply (rule_tac Q=m1x_secrecy in external_invariant_translation)
apply (auto del: subsetI)
apply (fastforce simp add: med1a1_def intro!: m1_secrecyI)
done

lemma PO_m1_secrecy [iff]: "reach m1 \<subseteq> m1_secrecy"
by (rule external_to_internal_invariant) (auto del: subsetI)


subsubsection \<open>inv (inherited): Responder auth server.\<close>
(*invh*************************************************************************)

definition 
  m1_inv2r_serv :: "'x m1r_pred"
where
  "m1_inv2r_serv \<equiv> {s. \<forall>A B Rb Kab Ts nlb.
     B \<notin> bad \<longrightarrow> 
     runs s Rb = Some (Resp, [A, B], aKey Kab # aNum Ts # nlb) \<longrightarrow>
       (\<exists>Rs Na. Kab = sesK (Rs$sk) \<and> 
          runs s Rs = Some (Serv, [A, B], [aNon Na, aNum Ts]))
  }"

lemmas m1_inv2r_servI = m1_inv2r_serv_def [THEN setc_def_to_intro, rule_format]
lemmas m1_inv2r_servE [elim] = m1_inv2r_serv_def [THEN setc_def_to_elim, rule_format]
lemmas m1_inv2r_servD = m1_inv2r_serv_def [THEN setc_def_to_dest, rule_format, rotated -1]


text \<open>Proof of invariance.\<close>

lemma PO_m1_inv2r_serv [iff]: "reach m1 \<subseteq> m1_inv2r_serv"
apply (rule_tac Sa=m1a and Pa=m1a_inv2r_serv 
       and Qa=m1a_inv2r_serv and Q=m1_inv2r_serv 
       in internal_invariant_translation)
apply (auto del: subsetI)
\<comment> \<open>1 subgoal\<close>
apply (auto simp add: vimage_def intro!: m1_inv2r_servI)
apply (simp add: m1a_inv2r_serv_def med1a1_def)
apply (rename_tac x A B Rb Kab Ts nlb)
apply (drule_tac x=A in spec)
apply (drule_tac x=B in spec, clarsimp)
apply (drule_tac x=Rb in spec)
apply (drule_tac x=Kab in spec)
apply (drule_tac x="[aNum Ts]" in spec)
apply (auto simp add: map_runs_def) 
done


subsubsection \<open>inv (inherited): Initiator auth server.\<close>
(*invh*************************************************************************)

text \<open>Simplified version of invariant \<open>m1a_inv2i_serv\<close>.\<close>

definition 
  m1_inv2i_serv :: "'x m1r_pred"
where
  "m1_inv2i_serv \<equiv> {s. \<forall>A B Ra Kab Ts nla.
     A \<notin> bad \<longrightarrow> 
     runs s Ra = Some (Init, [A, B], aKey Kab # aNum Ts # nla) \<longrightarrow>
       (\<exists>Rs. Kab = sesK (Rs$sk) \<and>
         runs s Rs = Some (Serv, [A, B],  [aNon (Ra$na), aNum Ts]))
  }"

lemmas m1_inv2i_servI = m1_inv2i_serv_def [THEN setc_def_to_intro, rule_format]
lemmas m1_inv2i_servE [elim] = m1_inv2i_serv_def [THEN setc_def_to_elim, rule_format]
lemmas m1_inv2i_servD = m1_inv2i_serv_def [THEN setc_def_to_dest, rule_format, rotated -1]


text \<open>Proof of invariance.\<close>

lemma PO_m1_inv2i_serv [iff]: "reach m1 \<subseteq> m1_inv2i_serv"
apply (rule_tac Pa=m1a_inv2i_serv and Qa=m1a_inv2i_serv and Q=m1_inv2i_serv
       in internal_invariant_translation)
apply (auto del: subsetI)
\<comment> \<open>1 subgoal\<close>
apply (auto simp add: m1a_inv2i_serv_def med1a1_def vimage_def intro!: m1_inv2i_servI)
apply (rename_tac x A B Ra Kab Ts nla)
apply (drule_tac x=A in spec, clarsimp)
apply (drule_tac x=B in spec) 
apply (drule_tac x=Ra in spec) 
apply (drule_tac x=Kab in spec) 
apply (drule_tac x="[aNum Ts]" in spec)
apply (auto simp add: map_runs_def)
done

declare PO_m1_inv2i_serv [THEN subsetD, intro]


subsubsection \<open>inv (inherited): Initiator key freshness\<close>
(*invh*************************************************************************)

definition 
  m1_inv1_ifresh :: "'x m1_pred"
where
  "m1_inv1_ifresh \<equiv> {s. \<forall>A A' B B' Ra Ra' Kab nl nl'.
     runs s Ra  = Some (Init, [A,  B],  aKey Kab # nl) \<longrightarrow>
     runs s Ra' = Some (Init, [A', B'], aKey Kab # nl') \<longrightarrow>
     A \<notin> bad \<longrightarrow> B \<notin> bad \<longrightarrow> Kab \<notin> Domain (leak s) \<longrightarrow>
       Ra = Ra'
  }"

lemmas m1_inv1_ifreshI = m1_inv1_ifresh_def [THEN setc_def_to_intro, rule_format]
lemmas m1_inv1_ifreshE [elim] = m1_inv1_ifresh_def [THEN setc_def_to_elim, rule_format]
lemmas m1_inv1_ifreshD = m1_inv1_ifresh_def [THEN setc_def_to_dest, rule_format, rotated 1]

lemma PO_m1_ifresh [iff]: "reach m1 \<subseteq> m1_inv1_ifresh"
apply (rule_tac Pa=m1a_inv1_ifresh and Qa=m1a_inv1_ifresh and Q=m1_inv1_ifresh
       in internal_invariant_translation)
apply (auto del: subsetI)
apply (auto simp add: med1a1_def map_runs_def vimage_def m1_inv1_ifresh_def)
done


(******************************************************************************)
subsection \<open>Refinement of \<open>a0i\<close> for responder/initiator\<close>
(******************************************************************************)

text \<open>The responder injectively agrees with the initiator on @{term "Kab"},
@{term "Ts"}, and @{term "Ta"}.\<close>


subsubsection \<open>Simulation relation\<close>
(******************************************************************************)

text \<open>We define two auxiliary functions to reconstruct the signals of the
initial model from completed initiator and responder runs.\<close>

type_synonym
  risig = "key \<times> time \<times> time"

abbreviation
  ri_running :: "[runs_t, agent, agent, key, time, time] \<Rightarrow> rid_t set" 
where
  "ri_running runz A B Kab Ts Ta \<equiv> {Ra. \<exists>nl. 
     runz Ra = Some (Init, [A, B], aKey Kab # aNum Ts # aNum Ta # nl)
  }"

abbreviation
  ri_commit :: "[runs_t, agent, agent, key, time, time] \<Rightarrow> rid_t set" 
where
  "ri_commit runz A B Kab Ts Ta \<equiv> {Rb. \<exists>nl. 
     runz Rb = Some (Resp, [A, B], aKey Kab # aNum Ts # aNum Ta # nl)
  }"

fun
  ri_runs2sigs :: "runs_t \<Rightarrow> risig signal \<Rightarrow> nat"
where
  "ri_runs2sigs runz (Running [B, A] (Kab, Ts, Ta)) = 
     card (ri_running runz A B Kab Ts Ta)"

| "ri_runs2sigs runz (Commit [B, A] (Kab, Ts, Ta)) = 
     card (ri_commit runz A B Kab Ts Ta)"

| "ri_runs2sigs runz _ = 0"


text \<open>Simulation relation and mediator function. We map completed initiator 
and responder runs to commit and running signals, respectively.\<close>

definition 
  med_a0iim1_ri :: "m1_obs \<Rightarrow> risig a0i_obs" where
  "med_a0iim1_ri o1 \<equiv> \<lparr> signals = ri_runs2sigs (runs o1), corrupted = {} \<rparr>"

definition
  R_a0iim1_ri :: "(risig a0i_state \<times> m1_state) set" where
  "R_a0iim1_ri \<equiv> {(s, t). signals s = ri_runs2sigs (runs t) \<and> corrupted s = {} }"

lemmas R_a0iim1_ri_defs = R_a0iim1_ri_def med_a0iim1_ri_def 


subsubsection \<open>Lemmas about the auxiliary functions\<close>
(******************************************************************************)

text \<open>Other lemmas\<close>

lemma ri_runs2sigs_empty [simp]: 
  "runz = Map.empty \<Longrightarrow> ri_runs2sigs runz = (\<lambda>s. 0)"
by (rule ext, erule rev_mp) 
   (rule ri_runs2sigs.induct, auto) 

lemma finite_ri_running [simp, intro]:
  "finite (dom runz) \<Longrightarrow> finite (ri_running runz A B Kab Ts Ta)"
by (auto intro: finite_subset dest: dom_lemmas)

lemma finite_ri_commit [simp, intro]:
  "finite (dom runz) \<Longrightarrow> finite (ri_commit runz A B Kab Ts Ta)"
by (auto intro: finite_subset dest: dom_lemmas)


text \<open>Update lemmas\<close>

lemma ri_runs2sigs_upd_init_none [simp]:
  "\<lbrakk> Na \<notin> dom runz \<rbrakk>
  \<Longrightarrow> ri_runs2sigs (runz(Na \<mapsto> (Init, [A, B], []))) = ri_runs2sigs runz"
by (rule ext, erule rev_mp, rule ri_runs2sigs.induct) 
   (auto dest: dom_lemmas)

lemma ri_runs2sigs_upd_resp_none [simp]:
  "\<lbrakk> Rb \<notin> dom runz \<rbrakk>
  \<Longrightarrow> ri_runs2sigs (runz(Rb \<mapsto> (Resp, [A, B], []))) = ri_runs2sigs runz"
by (rule ext, erule rev_mp, rule ri_runs2sigs.induct)
   (auto dest: dom_lemmas)

lemma ri_runs2sigs_upd_serv [simp]:
  "\<lbrakk> Rs \<notin> dom runz \<rbrakk>
  \<Longrightarrow> ri_runs2sigs (runz(Rs \<mapsto> (Serv, [A, B], [aNon Na, aNum Ts]))) 
      = ri_runs2sigs runz"
by (rule ext, erule rev_mp, rule ri_runs2sigs.induct)
   (auto dest: dom_lemmas)

lemma ri_runs2sigs_upd_init_some [simp]:
  "\<lbrakk> runz Ra = Some (Init, [A, B], []); finite (dom runz) \<rbrakk>
  \<Longrightarrow> ri_runs2sigs (runz(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta]))) =
     (ri_runs2sigs runz)(
       Running [B, A] (Kab, Ts, Ta) := 
         Suc (card (ri_running runz A B Kab Ts Ta)))"
apply (rule ext, (erule rev_mp)+)
apply (rule ri_runs2sigs.induct, auto) 
\<comment> \<open>1 subgoal\<close>
apply (rename_tac runz)
apply (rule_tac s="card (insert Ra (ri_running runz A B Kab Ts Ta))"
       in trans, fast, auto)
done

lemma ri_runs2sigs_upd_resp_some [simp]:
  "\<lbrakk> runz Rb = Some (Resp, [A, B], []); finite (dom runz) \<rbrakk>
  \<Longrightarrow> ri_runs2sigs (runz(Rb \<mapsto> (Resp, [A, B], [aKey Kab, aNum Ts, aNum Ta]))) =
     (ri_runs2sigs runz)(
        Commit [B, A] (Kab, Ts, Ta) := 
          Suc (card (ri_commit runz A B Kab Ts Ta)))"
apply (rule ext, (erule rev_mp)+)
apply (rule ri_runs2sigs.induct, auto)
\<comment> \<open>1 subgoal\<close>
apply (rename_tac runz)
apply (rule_tac s="card (insert Rb (ri_commit runz A B Kab Ts Ta))"
       in trans, fast, auto)
done

lemma ri_runs2sigs_upd_init_some2 [simp]:
  "\<lbrakk> runz Ra = Some (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta]) \<rbrakk>
  \<Longrightarrow> ri_runs2sigs (runz(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta, END]))) =
     ri_runs2sigs runz"
by (rule ext, erule rev_mp, rule ri_runs2sigs.induct)
   (auto dest: dom_lemmas)


subsubsection \<open>Refinement proof\<close>
(******************************************************************************)

lemma PO_m1_step1_refines_a0_ri_skip:
  "{R_a0iim1_ri} 
     Id, (m1_step1 Ra A B Na) 
   {> R_a0iim1_ri}"
by (auto simp add: PO_rhoare_defs R_a0iim1_ri_defs m1_defs)

lemma PO_m1_step2_refines_a0_ri_skip:
  "{R_a0iim1_ri} 
     Id, (m1_step2 Rb A B) 
   {> R_a0iim1_ri}"
by (auto simp add: PO_rhoare_defs R_a0iim1_ri_defs m1_defs)

lemma PO_m1_step3_refines_a0_ri_skip:
  "{R_a0iim1_ri} 
     Id, (m1_step3 Rs A B Kab Na Ts) 
   {> R_a0iim1_ri}"
by (auto simp add: PO_rhoare_defs R_a0iim1_ri_defs m1_defs)

lemma PO_m1_step4_refines_a0_ri_running:
  "{R_a0iim1_ri \<inter> UNIV \<times> m1_inv0_fin} 
     (a0i_running [B, A] (Kab, Ts, Ta)), (m1_step4 Ra A B Na Kab Ts Ta) 
   {> R_a0iim1_ri}"
by (auto simp add: PO_rhoare_defs R_a0iim1_ri_defs a0i_defs m1_defs)

lemma PO_m1_step5_refines_a0_ri_commit:
  "{R_a0iim1_ri \<inter> UNIV \<times> (m1_inv1r_cache \<inter> m1_inv0_fin)} 
     (a0i_commit [B, A] (Kab, Ts, Ta)), (m1_step5 Rb A B Kab Ts Ta) 
   {> R_a0iim1_ri}"
apply (auto simp add: PO_rhoare_defs R_a0iim1_ri_defs a0i_defs m1_defs)
\<comment> \<open>2 subgoals\<close>
apply (rename_tac s t aa ab ac ba Rs Na Ra nl,
       subgoal_tac 
         "card (ri_commit (runs t) A B (sesK (Rs$sk)) Ts Ta) = 0 \<and>
          card (ri_running (runs t) A B (sesK (Rs$sk)) Ts Ta) > 0", auto)
apply (rename_tac s t Rs Na Ra nl,
       subgoal_tac 
         "card (ri_commit (runs t) A B (sesK (Rs$sk)) Ts Ta) = 0 \<and>
          card (ri_running (runs t) A B (sesK (Rs$sk)) Ts Ta) > 0", auto)
done

lemma PO_m1_step6_refines_a0_ri_skip:
  "{R_a0iim1_ri} 
     Id, (m1_step6 Ra A B Na Kab Ts Ta) 
   {> R_a0iim1_ri}"
by (auto simp add: PO_rhoare_defs R_a0iim1_ri_defs m1_defs)

lemma PO_m1_leak_refines_a0_ri_skip:
  "{R_a0iim1_ri} 
     Id, (m1_leak Rs A B Na Ts) 
   {> R_a0iim1_ri}"
by (auto simp add: PO_rhoare_defs R_a0iim1_ri_defs a0i_defs m1_defs)

lemma PO_m1_tick_refines_a0_ri_skip:
  "{R_a0iim1_ri}
     Id, (m1_tick T)
   {> R_a0iim1_ri}"
by (auto simp add: PO_rhoare_defs R_a0iim1_ri_defs m1_defs)

lemma PO_m1_purge_refines_a0_ri_skip:
  "{R_a0iim1_ri}
     Id, (m1_purge A)
   {> R_a0iim1_ri}"
by (auto simp add: PO_rhoare_defs R_a0iim1_ri_defs m1_defs)

text \<open>All together now...\<close>

lemmas PO_m1_trans_refines_a0_ri_trans = 
  PO_m1_step1_refines_a0_ri_skip  PO_m1_step2_refines_a0_ri_skip
  PO_m1_step3_refines_a0_ri_skip  PO_m1_step4_refines_a0_ri_running
  PO_m1_step5_refines_a0_ri_commit PO_m1_step6_refines_a0_ri_skip 
  PO_m1_leak_refines_a0_ri_skip PO_m1_tick_refines_a0_ri_skip 
  PO_m1_purge_refines_a0_ri_skip

lemma PO_m1_refines_init_a0_ri [iff]:
  "init m1 \<subseteq>  R_a0iim1_ri``(init a0i)"
by (auto simp add: R_a0iim1_ri_defs a0i_defs m1_defs
         intro!: exI [where x="\<lparr>signals = \<lambda>s. 0, corrupted = {} \<rparr>"])

lemma PO_m1_refines_trans_a0_ri [iff]:
  "{R_a0iim1_ri \<inter> a0i_inv1_iagree \<times> (m1_inv1r_cache \<inter> m1_inv0_fin)} 
     (trans a0i), (trans m1) 
   {> R_a0iim1_ri}"
by (force simp add: m1_def m1_trans_def a0i_def a0i_trans_def
          intro!: PO_m1_trans_refines_a0_ri_trans)


lemma obs_consistent_med_a0iim1_ri [iff]: 
  "obs_consistent 
     (R_a0iim1_ri \<inter> a0i_inv1_iagree \<times> (m1_inv1r_cache \<inter> m1_inv0_fin))
     med_a0iim1_ri a0i m1"
by (auto simp add: obs_consistent_def R_a0iim1_ri_def med_a0iim1_ri_def 
                   a0i_def m1_def)


text \<open>Refinement result.\<close>

lemma PO_m1_refines_a0ii_ri [iff]: 
  "refines 
     (R_a0iim1_ri \<inter> a0i_inv1_iagree \<times> (m1_inv1r_cache \<inter> m1_inv0_fin))
     med_a0iim1_ri a0i m1"
by (rule Refinement_using_invariants) (auto)

lemma  m1_implements_a0ii_ri: "implements med_a0iim1_ri a0i m1"
by (rule refinement_soundness) (fast)


subsubsection \<open>inv3 (inherited): Responder and initiator\<close>
(*invh*************************************************************************)

text \<open>This is a translation of the agreement property to Level 1. It
follows from the refinement and is needed to prove inv4 below.\<close>

definition 
  m1_inv3r_init :: "'x m1_pred"
where
  "m1_inv3r_init \<equiv> {s. \<forall>A B Rb Kab Ts Ta nlb.
     B \<notin> bad \<longrightarrow> A \<notin> bad \<longrightarrow> Kab \<notin> Domain (leak s) \<longrightarrow>
     runs s Rb = Some (Resp, [A, B], aKey Kab # aNum Ts # aNum Ta # nlb) \<longrightarrow>
       (\<exists>Ra nla. 
        runs s Ra = Some (Init, [A, B], aKey Kab # aNum Ts # aNum Ta # nla))
  }"

lemmas m1_inv3r_initI = m1_inv3r_init_def [THEN setc_def_to_intro, rule_format]
lemmas m1_inv3r_initE [elim] = m1_inv3r_init_def [THEN setc_def_to_elim, rule_format]
lemmas m1_inv3r_initD = m1_inv3r_init_def [THEN setc_def_to_dest, rule_format, rotated -1]


text \<open>Invariance proof.\<close>

lemma PO_m1_inv3r_init [iff]: "reach m1 \<subseteq> m1_inv3r_init"
apply (rule INV_from_Refinement_basic [OF PO_m1_refines_a0ii_ri])
apply (auto simp add: R_a0iim1_ri_def a0i_inv1_iagree_def
            intro!:  m1_inv3r_initI)
\<comment> \<open>1 subgoal\<close>
apply (rename_tac s A B Rb Kab Ts Ta nlb a)
apply (drule_tac x="[B, A]" in spec, clarsimp)
apply (drule_tac x="Kab" in spec)
apply (drule_tac x="Ts" in spec)
apply (drule_tac x="Ta" in spec)
apply (subgoal_tac "card (ri_commit (runs s) A B Kab Ts Ta) > 0", auto) 
done


subsubsection \<open>inv4: Key freshness for responder\<close>
(*inv*************************************************************************)

definition 
  m1_inv4_rfresh :: "'x m1_pred"
where
  "m1_inv4_rfresh \<equiv> {s. \<forall>Rb1 Rb2 A1 A2 B1 B2 Kab Ts1 Ts2 Ta1 Ta2.
     runs s Rb1 = Some (Resp, [A1, B1], [aKey Kab, aNum Ts1, aNum Ta1]) \<longrightarrow> 
     runs s Rb2 = Some (Resp, [A2, B2], [aKey Kab, aNum Ts2, aNum Ta2]) \<longrightarrow> 
     B1 \<notin> bad \<longrightarrow> A1 \<notin> bad \<longrightarrow> Kab \<notin> Domain (leak s) \<longrightarrow>
       Rb1 = Rb2
  }"

lemmas m1_inv4_rfreshI = m1_inv4_rfresh_def [THEN setc_def_to_intro, rule_format]
lemmas m1_inv4_rfreshE [elim] = m1_inv4_rfresh_def [THEN setc_def_to_elim, rule_format]
lemmas m1_inv4_rfreshD = m1_inv4_rfresh_def [THEN setc_def_to_dest, rule_format, rotated 1]


text \<open>Proof of key freshness for responder. All cases except step5 are straightforward.\<close>

lemma PO_m1_inv4_rfresh_step5:
  "{m1_inv4_rfresh \<inter> m1_inv3r_init \<inter> m1_inv2r_serv \<inter> m1_inv1r_cache \<inter>
    m1_secrecy \<inter> m1_inv1_ifresh} 
     (m1_step5 Rb A B Kab Ts Ta)
   {> m1_inv4_rfresh}"
apply (auto simp add: PO_hoare_defs m1_defs intro!: m1_inv4_rfreshI)
apply (auto dest: m1_inv4_rfreshD)
apply (auto dest: m1_inv2r_servD) 

\<comment> \<open>5 subgoals\<close>
  apply (drule m1_inv2r_servD, auto) 
  apply (elim azC.cases, auto)

  apply (drule m1_inv2r_servD, auto)
  apply (elim azC.cases, auto)

  apply (drule m1_inv2r_servD, auto)
  apply (elim azC.cases, auto)

  apply (rename_tac Rb2 A2 B2 Ts2 Ta2 s Rs Na Ra nl)
  apply (case_tac "B2 \<in> bad")
    apply (thin_tac "(sesK (Rs$sk), B) \<in> azC (runs s)")
    apply (subgoal_tac "(sesK (Rs$sk), B2) \<in> azC (runs s)")
    apply (erule azC.cases, auto)
    apply (erule m1_secrecyE, auto) 

    apply (case_tac "A2 \<in> bad", auto dest: m1_inv2r_servD)
    apply (frule m1_inv3r_initD, auto)
    apply (rename_tac Raa nla, subgoal_tac "Raa = Ra", auto)    \<comment> \<open>uses cache invariant\<close>

  apply (frule m1_inv3r_initD, auto)
  apply (rename_tac Raa nla, subgoal_tac "Raa = Ra", auto)      \<comment> \<open>uses cache invariant\<close>
done

lemmas PO_m1_inv4_rfresh_step5_lemmas = 
  PO_m1_inv4_rfresh_step5

lemma PO_m1_inv4_rfresh_init [iff]:
  "init m1 \<subseteq> m1_inv4_rfresh"
by (auto simp add: m1_defs intro!: m1_inv4_rfreshI)

lemma PO_m1_inv4_rfresh_trans [iff]:
  "{m1_inv4_rfresh \<inter> m1_inv3r_init \<inter> m1_inv2r_serv \<inter> m1_inv1r_cache \<inter>
    m1_secrecy \<inter> m1_inv1_ifresh} 
      trans m1 
   {> m1_inv4_rfresh}"
by (auto simp add: m1_def m1_trans_def intro!: PO_m1_inv4_rfresh_step5_lemmas)
   (auto simp add: PO_hoare_defs m1_defs intro!: m1_inv4_rfreshI dest: m1_inv4_rfreshD)


lemma PO_m1_inv4_rfresh [iff]: "reach m1 \<subseteq> m1_inv4_rfresh"
apply (rule_tac 
         J="m1_inv3r_init \<inter> m1_inv2r_serv \<inter> m1_inv1r_cache \<inter> m1_secrecy \<inter> m1_inv1_ifresh" 
       in inv_rule_incr) 
apply (auto simp add: Int_assoc del: subsetI)
done

lemma PO_m1_obs_inv4_rfresh [iff]: "oreach m1 \<subseteq> m1_inv4_rfresh"
by (rule external_from_internal_invariant)
   (auto del: subsetI)


(******************************************************************************)
subsection \<open>Refinement of \<open>a0i\<close> for initiator/responder\<close>
(******************************************************************************)

text \<open>The initiator injectively agrees with the responder on \<open>Kab\<close>,
\<open>Ts\<close>, and \<open>Ta\<close>.\<close>


subsubsection \<open>Simulation relation\<close>
(******************************************************************************)

text \<open>We define two auxiliary functions to reconstruct the signals of the
initial model from completed initiator and responder runs.\<close>

type_synonym
  irsig = "key \<times> time \<times> time"

abbreviation
  ir_running :: "[runs_t, agent, agent, key, time, time] \<Rightarrow> rid_t set" 
where
  "ir_running runz A B Kab Ts Ta \<equiv> {Rb. \<exists>nl. 
     runz Rb = Some (Resp, [A, B], aKey Kab # aNum Ts # aNum Ta # nl)
  }"

abbreviation
  ir_commit :: "[runs_t, agent, agent, key, time, time] \<Rightarrow> rid_t set" 
where
  "ir_commit runz A B Kab Ts Ta \<equiv> {Ra. \<exists>nl. 
     runz Ra = Some (Init, [A, B], aKey Kab # aNum Ts # aNum Ta # END # nl)
  }"

fun
  ir_runs2sigs :: "runs_t \<Rightarrow> risig signal \<Rightarrow> nat"
where
 "ir_runs2sigs runz (Running [A, B] (Kab, Ts, Ta)) = 
     card (ir_running runz A B Kab Ts Ta)"

| "ir_runs2sigs runz (Commit [A, B] (Kab, Ts, Ta)) = 
     card (ir_commit runz A B Kab Ts Ta)"

| "ir_runs2sigs runz _ = 0"


text \<open>Simulation relation and mediator function. We map completed initiator 
and responder runs to commit and running signals, respectively.\<close>

definition 
  med_a0iim1_ir :: "m1_obs \<Rightarrow> irsig a0i_obs" where
  "med_a0iim1_ir o1 \<equiv> \<lparr> signals = ir_runs2sigs (runs o1), corrupted = {} \<rparr>"

definition
  R_a0iim1_ir :: "(irsig a0i_state \<times> m1_state) set" where
  "R_a0iim1_ir \<equiv> {(s, t). signals s = ir_runs2sigs (runs t) \<and> corrupted s = {} }"

lemmas R_a0iim1_ir_defs = R_a0iim1_ir_def med_a0iim1_ir_def


subsubsection \<open>Lemmas about the auxiliary functions\<close>
(******************************************************************************)

lemma ir_runs2sigs_empty [simp]: 
  "runz = Map.empty \<Longrightarrow> ir_runs2sigs runz = (\<lambda>s. 0)"
by (rule ext, erule rev_mp) 
   (rule ir_runs2sigs.induct, auto)

(* already proven higher up:
lemma ir_running_finite [simp, intro]:
  "finite (dom runz) \<Longrightarrow> finite (ir_running runz A B Kab Ts Ta)"
by (auto intro: finite_subset dest: dom_lemmas) 
*)

lemma ir_commit_finite [simp, intro]:
  "finite (dom runz) \<Longrightarrow> finite (ir_commit runz A B Kab Ts Ta)"
by (auto intro: finite_subset dest: dom_lemmas)


text \<open>Update lemmas\<close>

lemma ir_runs2sigs_upd_init_none [simp]:
  "\<lbrakk> Ra \<notin> dom runz \<rbrakk>
  \<Longrightarrow> ir_runs2sigs (runz(Ra \<mapsto> (Init, [A, B], []))) = ir_runs2sigs runz"
by (rule ext, erule rev_mp) 
   (rule ir_runs2sigs.induct, auto dest: dom_lemmas)

lemma ir_runs2sigs_upd_resp_none [simp]:
  "\<lbrakk> Rb \<notin> dom runz \<rbrakk>
  \<Longrightarrow> ir_runs2sigs (runz(Rb \<mapsto> (Resp, [A, B], []))) = ir_runs2sigs runz"
by (rule ext, erule rev_mp) 
   (rule ir_runs2sigs.induct, auto dest: dom_lemmas)

lemma ir_runs2sigs_upd_serv [simp]:
  "\<lbrakk> Rs \<notin> dom (runs y) \<rbrakk>
  \<Longrightarrow> ir_runs2sigs (runs y(Rs \<mapsto> (Serv, [A, B], [aNon Na, aNum Ts]))) 
      = ir_runs2sigs (runs y)"
by (rule ext, erule rev_mp) 
   (rule ir_runs2sigs.induct, auto dest: dom_lemmas)

lemma ir_runs2sigs_upd_init_some [simp]:
  "\<lbrakk> runz Ra = Some (Init, [A, B], []) \<rbrakk>
  \<Longrightarrow> ir_runs2sigs (runz(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta]))) =
     ir_runs2sigs runz"
by (rule ext, erule rev_mp) 
   (rule ir_runs2sigs.induct, auto dest: dom_lemmas)

lemma ir_runs2sigs_upd_resp_some_raw:
  assumes
    "runz Rb = Some (Resp, [A, B], [])" 
    "finite (dom runz)"
  shows
    "ir_runs2sigs (runz(Rb \<mapsto> (Resp, [A, B], [aKey Kab, aNum Ts, aNum Ta]))) s =
     ((ir_runs2sigs runz)(
       Running [A, B] (Kab, Ts, Ta) := 
         Suc (card (ir_running runz A B Kab Ts Ta)))) s"
  using assms
proof (induct rule: ir_runs2sigs.induct) 
  case (1 runz A B Kab Ts Ta) note H = this
    hence "Rb \<notin> ir_running runz A B Kab Ts Ta" by auto
    moreover
    with H have
      "card (insert Rb (ir_running runz A B Kab Ts Ta)) 
       = Suc (card (ir_running runz A B Kab Ts Ta))" by auto
  ultimately show ?case by (auto elim: subst)
qed (auto)

lemma ir_runs2sigs_upd_resp_some [simp]:
  "\<lbrakk> runz Rb = Some (Resp, [A, B], []); finite (dom runz) \<rbrakk>
  \<Longrightarrow> ir_runs2sigs (runz(Rb \<mapsto> (Resp, [A, B], [aKey Kab, aNum Ts, aNum Ta]))) =
     (ir_runs2sigs runz)(
       Running [A, B] (Kab, Ts, Ta) := 
         Suc (card (ir_running runz A B Kab Ts Ta)))"
by (intro ext ir_runs2sigs_upd_resp_some_raw)

lemma ir_runs2sigs_upd_init_some2_raw:
  assumes 
    "runz Ra = Some (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta])" 
    "finite (dom runz)" 
  shows
    "ir_runs2sigs (runz(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta, END]))) s =
     ((ir_runs2sigs runz)(
        Commit [A, B] (Kab, Ts, Ta) := 
          Suc (card (ir_commit runz A B Kab Ts Ta)))) s"
  using assms
proof (induct runz s rule: ir_runs2sigs.induct)
  case (2 runz A B Kab Ts Ta) note H = this 
    from H have "Ra \<notin> ir_commit runz A B Kab Ts Ta" by auto
    moreover
    with H have 
      "card (insert Ra (ir_commit runz A B Kab Ts Ta)) 
       = Suc (card (ir_commit runz A B Kab Ts Ta))" 
    by (auto)
    ultimately show ?case by (auto elim: subst)
qed (auto)

lemma ir_runs2sigs_upd_init_some2 [simp]:
  "\<lbrakk> runz Na = Some (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta]); finite (dom runz) \<rbrakk>
  \<Longrightarrow> ir_runs2sigs (runz(Na \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta, END]))) =
     (ir_runs2sigs runz)(
        Commit [A, B] (Kab, Ts, Ta) := 
          Suc (card (ir_commit runz A B Kab Ts Ta)))"
by (intro ir_runs2sigs_upd_init_some2_raw ext)


subsubsection \<open>Refinement proof\<close>
(******************************************************************************)

lemma PO_m1_step1_refines_ir_a0ii_skip:
  "{R_a0iim1_ir} 
     Id, (m1_step1 Ra A B Na) 
   {> R_a0iim1_ir}"
by (simp add: PO_rhoare_defs R_a0iim1_ir_defs m1_defs, safe, auto)

lemma PO_m1_step2_refines_ir_a0ii_skip:
  "{R_a0iim1_ir} 
     Id, (m1_step2 Rb A B) 
   {> R_a0iim1_ir}"
by (simp add: PO_rhoare_defs R_a0iim1_ir_defs m1_defs, safe, auto)

lemma PO_m1_step3_refines_ir_a0ii_skip:
  "{R_a0iim1_ir} 
     Id, (m1_step3 Rs A B Kab Na Ts) 
   {> R_a0iim1_ir}"
by (simp add: PO_rhoare_defs R_a0iim1_ir_defs a0i_defs m1_defs, safe, auto)

lemma PO_m1_step4_refines_ir_a0ii_skip:
  "{R_a0iim1_ir} 
     Id, (m1_step4 Ra A B Na Kab Ts Ta) 
   {> R_a0iim1_ir}"
by (simp add: PO_rhoare_defs R_a0iim1_ir_defs m1_defs, safe, auto)

lemma PO_m1_step5_refines_ir_a0ii_running:
  "{R_a0iim1_ir \<inter> UNIV \<times> m1_inv0_fin} 
     (a0i_running [A, B] (Kab, Ts, Ta)), (m1_step5 Rb A B Kab Ts Ta) 
   {> R_a0iim1_ir}"
by (simp add: PO_rhoare_defs R_a0iim1_ir_defs a0i_defs m1_defs, safe, auto)

lemma PO_m1_step6_refines_ir_a0ii_commit:
  "{R_a0iim1_ir \<inter> UNIV \<times> m1_inv0_fin} 
     (a0n_commit [A, B] (Kab, Ts, Ta)), (m1_step6 Ra A B Na Kab Ts Ta) 
   {> R_a0iim1_ir}"
by (simp add: PO_rhoare_defs R_a0iim1_ir_defs a0n_defs m1_defs, safe, auto)

lemma PO_m1_leak_refines_ir_a0ii_skip:
  "{R_a0iim1_ir}
     Id, (m1_leak Rs A B Na Ts)
   {> R_a0iim1_ir}"
by (simp add: PO_rhoare_defs R_a0iim1_ir_defs a0n_defs m1_defs, safe, auto)

lemma PO_m1_tick_refines_ir_a0ii_skip:
  "{R_a0iim1_ir}
     Id, (m1_tick T)
   {> R_a0iim1_ir}"
by (simp add: PO_rhoare_defs R_a0iim1_ir_defs m1_defs, safe, auto)

lemma PO_m1_purge_refines_ir_a0ii_skip:
  "{R_a0iim1_ir}
     Id, (m1_purge A)
   {> R_a0iim1_ir}"
by (simp add: PO_rhoare_defs R_a0iim1_ir_defs m1_defs, safe, auto)

text \<open>All together now...\<close>

lemmas PO_m1_trans_refines_ir_a0ii_trans = 
  PO_m1_step1_refines_ir_a0ii_skip  PO_m1_step2_refines_ir_a0ii_skip
  PO_m1_step3_refines_ir_a0ii_skip  PO_m1_step4_refines_ir_a0ii_skip
  PO_m1_step5_refines_ir_a0ii_running PO_m1_step6_refines_ir_a0ii_commit
  PO_m1_leak_refines_ir_a0ii_skip PO_m1_tick_refines_ir_a0ii_skip 
  PO_m1_purge_refines_ir_a0ii_skip

lemma PO_m1_refines_init_ir_a0ii [iff]:
  "init m1 \<subseteq>  R_a0iim1_ir``(init a0n)"
by (auto simp add: R_a0iim1_ir_defs a0n_defs m1_defs
         intro!: exI [where x="\<lparr>signals = \<lambda>s. 0, corrupted = {}\<rparr>"])

lemma PO_m1_refines_trans_ir_a0ii [iff]:
  "{R_a0iim1_ir \<inter> UNIV \<times> m1_inv0_fin} 
     (trans a0n), (trans m1) 
   {> R_a0iim1_ir}"
by (auto simp add: m1_def m1_trans_def a0n_def a0n_trans_def
         intro!: PO_m1_trans_refines_ir_a0ii_trans)


text \<open>Observation consistency.\<close>

lemma obs_consistent_med_a0iim1_ir [iff]: 
  "obs_consistent 
     (R_a0iim1_ir \<inter> UNIV \<times> m1_inv0_fin) 
     med_a0iim1_ir a0n m1"
by (auto simp add: obs_consistent_def R_a0iim1_ir_def med_a0iim1_ir_def 
                   a0n_def m1_def)


text \<open>Refinement result.\<close>

lemma PO_m1_refines_a0ii_ir [iff]: 
  "refines (R_a0iim1_ir \<inter> UNIV \<times> m1_inv0_fin) 
     med_a0iim1_ir a0n m1"
by (rule Refinement_using_invariants) (auto) 

lemma  m1_implements_a0ii_ir: "implements med_a0iim1_ir a0n m1"
by (rule refinement_soundness) (fast)


end
