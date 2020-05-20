(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:   Key_establish/m1_keydist_iirn.thy (Isabelle/HOL 2016-1)
  ID:       $Id: m1_keydist_iirn.thy 133854 2017-03-20 17:53:50Z csprenge $
  Author:   Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>

  Key distribution protocols
  Level 1, 1st refinement: Abstract server-based key transport protocol with 
  initiator and responder roles. Provides injective server authentication to 
  the initiator and non-injective server authenticaiton to the responder.

  Copyright (c) 2009-2016 Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Abstract (i/n)-authenticated key transport (L1)\<close>

theory m1_keydist_iirn imports m1_keydist "../Refinement/a0i_agree"
begin

text \<open>We add authentication for the initiator and responder to the basic
server-based key transport protocol: 
\begin{enumerate}
\item the initiator injectively agrees with the server on the key and some
additional data
\item the responder non-injectively agrees with the server on the key and 
some additional data.
\end{enumerate}
The "additional data" is a parameter of this model.\<close>

declare option.split [split]
(* declare option.split_asm [split] *)

consts
  na :: "nat"

(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>The state type remains the same, but in this model we will record
nonces and timestamps in the run frame.\<close>

type_synonym m1a_state = "m1x_state"
type_synonym m1a_obs = "m1x_obs"

type_synonym 'x m1a_pred = "'x m1x_pred"
type_synonym 'x m1a_trans = "'x m1x_trans"


text \<open>We need some parameters regarding the list of freshness values
stored by the server. These   should be defined in further refinements.\<close>

consts 
  is_len :: "nat"   \<comment> \<open>num of agreeing list elements for initiator-server\<close>  
  rs_len :: "nat"   \<comment> \<open>num of agreeing list elements for responder-server\<close>


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

definition         \<comment> \<open>by @{term "A"}, refines @{term "m1x_step1"}\<close>
  m1a_step1 :: "[rid_t, agent, agent, nonce] \<Rightarrow> 'x m1r_trans"
where
  "m1a_step1 Ra A B Na \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    Ra \<notin> dom (runs s) \<and>                \<comment> \<open>\<open>Ra\<close> is fresh\<close>
    Na = Ra$na \<and>                       \<comment> \<open>NEW: generate a nonce\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>create initiator thread\<close>
    s1 = s\<lparr> runs := (runs s)(Ra \<mapsto> (Init, [A, B], [])) \<rparr>
  }"

definition       \<comment> \<open>by @{term "B"}, refines @{term "m1x_step2"}\<close>
  m1a_step2 :: "[rid_t, agent, agent] \<Rightarrow> 'x m1r_trans"
where
  "m1a_step2 \<equiv> m1x_step2"

definition       \<comment> \<open>by @{term "Server"}, refines @{term m1x_step3}\<close>
  m1a_step3 :: "[rid_t, agent, agent, key, nonce, atom list] \<Rightarrow> 'x m1r_trans"
where
  "m1a_step3 Rs A B Kab Na al \<equiv> {(s, s1).
     \<comment> \<open>guards:\<close>
     Rs \<notin> dom (runs s) \<and>                 \<comment> \<open>fresh run id\<close>
     Kab = sesK (Rs$sk) \<and>                \<comment> \<open>generate session key\<close>

     \<comment> \<open>actions:\<close>
     s1 = s\<lparr> runs := (runs s)(Rs \<mapsto> (Serv, [A, B], aNon Na # al)) \<rparr>
  }"

definition         \<comment> \<open>by @{text "A"}, refines @{term m1x_step4}\<close>
  m1a_step4 :: "[rid_t, agent, agent, nonce, key, atom list] \<Rightarrow> 'x m1a_trans"
where
  "m1a_step4 Ra A B Na Kab nla \<equiv> {(s, s').
     \<comment> \<open>guards:\<close>
     runs s Ra = Some (Init, [A, B], []) \<and>
     (Kab \<notin> leak s \<longrightarrow> (Kab, A) \<in> azC (runs s)) \<and>  \<comment> \<open>authorization guard\<close>
     Na = Ra$na \<and>                                   \<comment> \<open>fix parameter\<close>

     \<comment> \<open>new guard for agreement with server on \<open>(Kab, B, Na, isl)\<close>,\<close>
     \<comment> \<open>where \<open>isl = take is_len nla\<close>; injectiveness by including \<open>Na\<close>\<close>
     (A \<notin> bad \<longrightarrow> (\<exists>Rs. Kab = sesK (Rs$sk) \<and>
        runs s Rs = Some (Serv, [A, B], aNon Na # take is_len nla))) \<and>

     \<comment> \<open>actions:\<close>
     s' = s\<lparr> runs := (runs s)(Ra \<mapsto> (Init, [A, B], aKey Kab # nla)) \<rparr>
  }" 

definition         \<comment> \<open>by @{term "B"}, refines @{term m1x_step5}\<close>
  m1a_step5 :: "[rid_t, agent, agent, key, atom list] \<Rightarrow> 'x m1a_trans"
where
  "m1a_step5 Rb A B Kab nlb \<equiv> {(s, s1). 
     \<comment> \<open>guards:\<close>
     runs s Rb = Some (Resp, [A, B], []) \<and> 
     (Kab \<notin> leak s \<longrightarrow> (Kab, B) \<in> azC (runs s)) \<and>         \<comment> \<open>authorization guard\<close>

     \<comment> \<open>guard for showing agreement with server on \<open>(Kab, A, rsl)\<close>,\<close>
     \<comment> \<open>where \<open>rsl = take rs_len nlb\<close>; this agreement is non-injective\<close>

     (B \<notin> bad \<longrightarrow> (\<exists>Rs Na. Kab = sesK (Rs$sk) \<and>
        runs s Rs = Some (Serv, [A, B], aNon Na # take rs_len nlb))) \<and>

     \<comment> \<open>actions:\<close>
     s1 = s\<lparr> runs := (runs s)(Rb \<mapsto> (Resp, [A, B], aKey Kab # nlb)) \<rparr>
  }"

definition     \<comment> \<open>by attacker, refines @{term m1x_leak}\<close>
  m1a_leak :: "rid_t \<Rightarrow> 'x m1x_trans"
where
  "m1a_leak = m1x_leak" 


(******************************************************************************)
subsection \<open>Specification\<close>
(******************************************************************************)

definition
  m1a_init :: "m1a_state set"
where
  "m1a_init \<equiv> m1x_init" 

definition 
  m1a_trans :: "'x m1a_trans" where
  "m1a_trans \<equiv> (\<Union>A B Ra Rb Rs Na Kab nls nla nlb.
     m1a_step1 Ra A B Na \<union>
     m1a_step2 Rb A B \<union>
     m1a_step3 Rs A B Kab Na nls \<union>
     m1a_step4 Ra A B Na Kab nla \<union>
     m1a_step5 Rb A B Kab nlb \<union>
     m1a_leak Rs \<union>
     Id
  )"

definition 
  m1a :: "(m1a_state, m1a_obs) spec" where
  "m1a \<equiv> \<lparr>
     init = m1a_init,
     trans = m1a_trans,
     obs = id
  \<rparr>" 

lemma init_m1a: "init m1a = m1a_init"
by (simp add: m1a_def)

lemma trans_m1a: "trans m1a = m1a_trans"
by (simp add: m1a_def)

lemma obs_m1a [simp]: "obs m1a = id"
by (simp add: m1a_def)

lemmas m1a_loc_defs = 
  m1a_def m1a_init_def m1a_trans_def
  m1a_step1_def m1a_step2_def m1a_step3_def m1a_step4_def m1a_step5_def 
  m1a_leak_def 

lemmas m1a_defs = m1a_loc_defs m1x_defs


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

subsubsection \<open>inv0: Finite domain\<close>
(*inv**************************************************************************)

text \<open>There are only finitely many runs. This is needed to establish
the responder/initiator agreement.\<close>

definition 
  m1a_inv0_fin :: "'x m1r_pred"
where
  "m1a_inv0_fin \<equiv> {s. finite (dom (runs s))}"

lemmas m1a_inv0_finI = m1a_inv0_fin_def [THEN setc_def_to_intro, rule_format]
lemmas m1a_inv0_finE [elim] = m1a_inv0_fin_def [THEN setc_def_to_elim, rule_format]
lemmas m1a_inv0_finD = m1a_inv0_fin_def [THEN setc_def_to_dest, rule_format]

text \<open>Invariance proof.\<close>

lemma PO_m1a_inv0_fin_init [iff]:
  "init m1a \<subseteq> m1a_inv0_fin"
by (auto simp add: m1a_defs intro!: m1a_inv0_finI)

lemma PO_m1a_inv0_fin_trans [iff]:
  "{m1a_inv0_fin} trans m1a {> m1a_inv0_fin}"
by (auto simp add: PO_hoare_defs m1a_defs intro!: m1a_inv0_finI)

lemma PO_m1a_inv0_fin [iff]: "reach m1a \<subseteq> m1a_inv0_fin"
by (rule inv_rule_incr, auto del: subsetI)


(******************************************************************************)
subsection \<open>Refinement of \<open>m1x\<close>\<close>
(******************************************************************************)

subsubsection \<open>Simulation relation\<close>
(******************************************************************************)

text \<open>Define run abstraction.\<close>

fun 
  rm1x1a :: "role_t \<Rightarrow> atom list \<Rightarrow> atom list"
where
  "rm1x1a Init = take 1"         \<comment> \<open>take \<open>Kab\<close> from \<open>Kab # nla\<close>\<close>
| "rm1x1a Resp = take 1"         \<comment> \<open>take \<open>Kab\<close> from \<open>Kab # nlb\<close>\<close>
| "rm1x1a Serv = take 0"         \<comment> \<open>drop all from \<open>[Na]\<close>\<close>

abbreviation 
  runs1x1a :: "runs_t \<Rightarrow> runs_t" where 
  "runs1x1a \<equiv> map_runs rm1x1a"

text \<open>med1x1: The mediator function maps a concrete observation to an 
abstract one.\<close>

definition
  med1x1a :: "m1a_obs \<Rightarrow> m1x_obs" where
  "med1x1a t \<equiv> \<lparr> runs = runs1x1a (runs t), leak = leak t \<rparr>"

text \<open>R1x1a: The simulation relation is defined in terms of the mediator
function.\<close>

definition
  R1x1a :: "(m1x_state \<times> m1a_state) set" where
  "R1x1a \<equiv> {(s, t). s = med1x1a t}"

lemmas R1x1a_defs = 
  R1x1a_def med1x1a_def 


subsubsection \<open>Refinement proof\<close>
(******************************************************************************)

lemma PO_m1a_step1_refines_m1x_step1:
  "{R1x1a} 
     (m1x_step1 Ra A B), (m1a_step1 Ra A B Na) 
   {> R1x1a}"
by (auto simp add: PO_rhoare_defs R1x1a_defs m1a_defs)

lemma PO_m1a_step2_refines_m1x_step2:
  "{R1x1a} 
     (m1x_step2 Rb A B), (m1a_step2 Rb A B) 
   {> R1x1a}"
by (auto simp add: PO_rhoare_defs R1x1a_defs m1a_defs)

lemma PO_m1a_step3_refines_m1x_step3:
  "{R1x1a} 
     (m1x_step3 Rs A B Kab), (m1a_step3 Rs A B Kab Na nls)
   {> R1x1a}"
by (auto simp add: PO_rhoare_defs R1x1a_defs m1a_defs)

lemma PO_m1a_step4_refines_m1x_step4:
  "{R1x1a} 
     (m1x_step4 Ra A B Kab), (m1a_step4 Ra A B Na Kab nla) 
   {> R1x1a}"
by (auto simp add: PO_rhoare_defs R1x1a_defs m1a_defs map_runs_def)

lemma PO_m1a_step5_refines_m1x_step5:
  "{R1x1a} 
     (m1x_step5 A B Rb Kab), (m1a_step5 A B Rb Kab nlb) 
   {> R1x1a}"
by (auto simp add: PO_rhoare_defs R1x1a_defs m1a_defs map_runs_def)

lemma PO_m1a_leak_refines_m1x_leak:
  "{R1x1a} 
     (m1x_leak Rs), (m1a_leak Rs) 
   {> R1x1a}"
by (auto simp add: PO_rhoare_defs R1x1a_defs m1a_defs map_runs_def)


text \<open>All together now...\<close>

lemmas PO_m1a_trans_refines_m1x_trans = 
  PO_m1a_step1_refines_m1x_step1 PO_m1a_step2_refines_m1x_step2
  PO_m1a_step3_refines_m1x_step3 PO_m1a_step4_refines_m1x_step4
  PO_m1a_step5_refines_m1x_step5 PO_m1a_leak_refines_m1x_leak


lemma PO_m1a_refines_init_m1x [iff]:
  "init m1a \<subseteq>  R1x1a``(init m1x)"
by (auto simp add: R1x1a_defs m1a_defs)

lemma PO_m1a_refines_trans_m1x [iff]:
  "{R1x1a} 
     (trans m1x), (trans m1a) 
   {> R1x1a}"
apply (auto simp add: m1a_def m1a_trans_def m1x_def m1x_trans_def
            intro!: PO_m1a_trans_refines_m1x_trans)
apply (force intro!: PO_m1a_trans_refines_m1x_trans)+
done

text \<open>Observation consistency.\<close>

lemma obs_consistent_med1x1a [iff]: 
  "obs_consistent R1x1a med1x1a m1x m1a"
by (auto simp add: obs_consistent_def R1x1a_def m1a_defs)


text \<open>Refinement result.\<close>

lemma PO_m1a_refines_m1x [iff]: 
  "refines R1x1a med1x1a m1x m1a"
by (rule Refinement_basic) (auto del: subsetI)

lemma  m1a_implements_m1x [iff]: "implements med1x1a m1x m1a"
by (rule refinement_soundness) (fast)

text \<open>By transitivity:\<close>

lemma m1a_implements_s0g [iff]: "implements (med01x o med1x1a) s0g m1a"
by (rule implements_trans, auto)


subsubsection \<open>inv (inherited): Secrecy\<close>
(*invh*************************************************************************)

text \<open>Secrecy preserved from \<open>m1x\<close>.\<close>

lemma knC_runs1x1a [simp]: "knC (runs1x1a runz) = knC runz"
apply (auto simp add: map_runs_def elim!: knC.cases, auto)
\<comment> \<open>5 subgoals\<close>
apply (rename_tac b, case_tac b, auto)
apply (rename_tac b, case_tac b, auto)
apply (rule knC_init, auto simp add: map_runs_def)
apply (rule knC_resp, auto simp add: map_runs_def)
apply (rule knC_serv, auto simp add: map_runs_def)
done

lemma PO_m1a_obs_secrecy [iff]: "oreach m1a \<subseteq> m1x_secrecy"
apply (rule_tac Q=m1x_secrecy in external_invariant_translation)
apply (auto del: subsetI)
apply (auto simp add: med1x1a_def m1x_secrecy_def)
done

lemma PO_m1a_secrecy [iff]: "reach m1a \<subseteq> m1x_secrecy"
by (rule external_to_internal_invariant) (auto del: subsetI)


(******************************************************************************)
subsection \<open>Refinement of \<open>a0i\<close> for initiator/server\<close>
(******************************************************************************)

text \<open>For the initiator, we get an injective agreement with the server on 
the session key, the responder name, the initiator's nonce and the list of 
freshness values @{term "isl"}.\<close>


subsubsection \<open>Simulation relation\<close>
(******************************************************************************)

text \<open>We define two auxiliary functions to reconstruct the signals of the
initial model from completed initiator and server runs.\<close>

type_synonym 
  issig = "key \<times> agent \<times> nonce \<times> atom list"

fun
  is_runs2sigs :: "runs_t \<Rightarrow> issig signal \<Rightarrow> nat"
where
  "is_runs2sigs runz (Running [A, Sv] (Kab, B, Na, nl)) = 
     (if \<exists>Rs. Kab = sesK (Rs$sk) \<and> 
         runz Rs = Some (Serv, [A, B], aNon Na # nl) 
      then 1 else 0)"

| "is_runs2sigs runz (Commit [A, Sv] (Kab, B, Na, nl)) = 
     (if \<exists>Ra nla. Na = Ra$na \<and> 
         runz Ra = Some (Init, [A, B], aKey Kab # nla) \<and> 
         take is_len nla = nl
      then 1 else 0)"

| "is_runs2sigs runz _ = 0"


text \<open>Simulation relation and mediator function. We map completed initiator 
and responder runs to commit and running signals, respectively.\<close>

definition 
  med_a0m1a_is :: "m1a_obs \<Rightarrow> issig a0i_obs" where
  "med_a0m1a_is o1 \<equiv> \<lparr> signals = is_runs2sigs (runs o1), corrupted = {} \<rparr>"

definition
  R_a0m1a_is :: "(issig a0i_state \<times> m1a_state) set" where
  "R_a0m1a_is \<equiv> {(s, t). signals s = is_runs2sigs (runs t) \<and> corrupted s = {} }"

lemmas R_a0m1a_is_defs = R_a0m1a_is_def med_a0m1a_is_def 


subsubsection \<open>Lemmas about the auxiliary functions\<close>
(******************************************************************************)

lemma is_runs2sigs_empty [simp]: 
  "runz = Map.empty \<Longrightarrow> is_runs2sigs runz = (\<lambda>s. 0)"
by (rule ext, erule rev_mp) 
   (rule is_runs2sigs.induct, auto)


text \<open>Update lemmas\<close>

lemma is_runs2sigs_upd_init_none [simp]:
  "\<lbrakk> Ra \<notin> dom runz \<rbrakk>
  \<Longrightarrow> is_runs2sigs (runz(Ra \<mapsto> (Init, [A, B], []))) = is_runs2sigs runz"
by (rule ext, erule rev_mp) 
   (rule is_runs2sigs.induct, auto dest: dom_lemmas)

lemma is_runs2sigs_upd_resp_none [simp]:
  "\<lbrakk> Rb \<notin> dom runz \<rbrakk>
  \<Longrightarrow> is_runs2sigs (runz(Rb \<mapsto> (Resp, [A, B], []))) = is_runs2sigs runz"
by (rule ext, erule rev_mp) 
   (rule is_runs2sigs.induct, auto dest: dom_lemmas)

lemma is_runs2sigs_upd_serv [simp]:
  "\<lbrakk> Rs \<notin> dom runz \<rbrakk>
  \<Longrightarrow> is_runs2sigs (runz(Rs \<mapsto> (Serv, [A, B], aNon Na # ils))) = 
     (is_runs2sigs runz)(Running [A, Sv] (sesK (Rs$sk), B, Na, ils) := 1)"
apply (rule ext, (erule rev_mp)+) 
apply (rule is_runs2sigs.induct)
apply (safe, simp_all)+
apply (fastforce simp add: domIff)+
done

lemma is_runs2sigs_upd_init_some [simp]:
  "\<lbrakk> runz Ra = Some (Init, [A, B], []); ils = take is_len nla \<rbrakk>
  \<Longrightarrow> is_runs2sigs (runz(Ra \<mapsto> (Init, [A, B], aKey Kab # nla))) =
     (is_runs2sigs runz)(Commit [A, Sv] (Kab, B, Ra$na, ils) := 1)"
apply (rule ext, (erule rev_mp)+)
apply (rule is_runs2sigs.induct)
apply (safe, simp_all)+ 
apply (fastforce)+
done

lemma is_runs2sigs_upd_resp_some [simp]:
  "\<lbrakk> runz Rb = Some (Resp, [A, B], []) \<rbrakk>
  \<Longrightarrow> is_runs2sigs (runz(Rb \<mapsto> (Resp, [A, B], aKey Kab # nlb))) =
     is_runs2sigs runz" 
apply (rule ext, erule rev_mp)
apply (rule is_runs2sigs.induct, auto)  
done


subsubsection \<open>Refinement proof\<close>
(******************************************************************************)

lemma PO_m1a_step1_refines_a0_is_skip:
  "{R_a0m1a_is} 
     Id, (m1a_step1 Ra A B Na) 
   {> R_a0m1a_is}"
by (auto simp add: PO_rhoare_defs R_a0m1a_is_defs m1a_defs)

lemma PO_m1a_step2_refines_a0_is_skip:
  "{R_a0m1a_is} 
     Id, (m1a_step2 Rb A B) 
   {> R_a0m1a_is}"
by (auto simp add: PO_rhoare_defs R_a0m1a_is_defs m1a_defs)

lemma PO_m1a_step3_refines_a0_is_running:
  "{R_a0m1a_is} 
     (a0i_running [A, Sv] (Kab, B, Na, nls)), 
     (m1a_step3 Rs A B Kab Na nls) 
   {> R_a0m1a_is}"
by (auto simp add: PO_rhoare_defs R_a0m1a_is_defs a0i_defs m1a_defs 
         dest: dom_lemmas)

lemma PO_m1a_step4_refines_a0_is_commit:
  "{R_a0m1a_is \<inter> UNIV \<times> m1a_inv0_fin} 
     (a0i_commit [A, Sv] (Kab, B, Na, take is_len nla)), 
     (m1a_step4 Ra A B Na Kab nla) 
   {> R_a0m1a_is}"
by (auto simp add: PO_rhoare_defs R_a0m1a_is_defs a0i_defs m1a_defs)

lemma PO_m1a_step5_refines_a0_is_skip:
  "{R_a0m1a_is} 
     Id, (m1a_step5 A B Rb Kab nlb) 
   {> R_a0m1a_is}"
by (auto simp add: PO_rhoare_defs R_a0m1a_is_defs m1a_defs)

lemma PO_m1a_leak_refines_a0_is_skip:
  "{R_a0m1a_is} 
     Id, (m1a_leak Rs) 
   {> R_a0m1a_is}"
by (auto simp add: PO_rhoare_defs R_a0m1a_is_defs m1a_defs)

text \<open>All together now...\<close>

lemmas PO_m1a_trans_refines_a0_is_trans = 
  PO_m1a_step1_refines_a0_is_skip PO_m1a_step2_refines_a0_is_skip
  PO_m1a_step3_refines_a0_is_running PO_m1a_step4_refines_a0_is_commit
  PO_m1a_step5_refines_a0_is_skip PO_m1a_leak_refines_a0_is_skip
  

lemma PO_m1a_refines_init_a0_is [iff]:
  "init m1a \<subseteq>  R_a0m1a_is``(init a0i)"
by (auto simp add: R_a0m1a_is_defs a0i_defs m1a_defs)

lemma PO_m1a_refines_trans_a0_is [iff]:
  "{R_a0m1a_is \<inter> a0i_inv1_iagree \<times> m1a_inv0_fin} 
     (trans a0i), (trans m1a) 
   {> R_a0m1a_is}"
by (force simp add: m1a_def m1a_trans_def a0i_def a0i_trans_def
          intro!: PO_m1a_trans_refines_a0_is_trans)

lemma obs_consistent_med_a0m1a_is [iff]: 
  "obs_consistent R_a0m1a_is med_a0m1a_is a0i m1a"
by (auto simp add: obs_consistent_def R_a0m1a_is_def med_a0m1a_is_def 
                   a0i_def m1a_def)

text \<open>Refinement result.\<close>

lemma PO_m1a_refines_a0_is [iff]: 
  "refines (R_a0m1a_is \<inter> a0i_inv1_iagree \<times> m1a_inv0_fin) med_a0m1a_is a0i m1a"
by (rule Refinement_using_invariants) 
   (auto del: subsetI)

lemma  m1a_implements_a0_is: "implements med_a0m1a_is a0i m1a"
by (rule refinement_soundness) (fast)


subsubsection \<open>inv2i (inherited): Initiator and server\<close>
(*invh*************************************************************************)

text \<open>This is a translation of the agreement property to Level 1. It
follows from the refinement and is needed to prove inv1.\<close>

definition 
  m1a_inv2i_serv :: "'x m1x_state_scheme set"
where
  "m1a_inv2i_serv \<equiv> {s. \<forall>A B Ra Kab nla.
     A \<notin> bad \<longrightarrow>
     runs s Ra = Some (Init, [A, B], aKey Kab # nla) \<longrightarrow>
       (\<exists>Rs. Kab = sesK (Rs$sk) \<and> 
         runs s Rs = Some (Serv, [A, B], aNon (Ra$na) # take is_len nla))
  }"

lemmas m1a_inv2i_servI = 
  m1a_inv2i_serv_def [THEN setc_def_to_intro, rule_format]
lemmas m1a_inv2i_servE =     (* DO NOT declare elim: leads to slow proofs! *)
  m1a_inv2i_serv_def [THEN setc_def_to_elim, rule_format]
lemmas m1a_inv2i_servD =     (* DO NOT declare dest: leads to slow proofs! *)
  m1a_inv2i_serv_def [THEN setc_def_to_dest, rule_format, rotated -1]


text \<open>Invariance proof, see below after init/serv authentication proof.\<close>

lemma PO_m1a_inv2i_serv [iff]:
  "reach m1a \<subseteq> m1a_inv2i_serv"
apply (rule INV_from_Refinement_basic [OF PO_m1a_refines_a0_is])
apply (auto simp add: R_a0m1a_is_def a0i_inv1_iagree_def 
            intro!: m1a_inv2i_servI)
apply (drule_tac x="[A, Sv]" in spec, force)
done


subsubsection \<open>inv1: Key freshness for initiator\<close>
(*inv**************************************************************************)

text \<open>The initiator obtains key freshness from the injective agreement
with the server AND the fact that there is only one server run with a 
given key.\<close>

definition 
  m1a_inv1_ifresh :: "'x m1a_pred"
where
  "m1a_inv1_ifresh \<equiv> {s. \<forall>A A' B B' Ra Ra' Kab nl nl'.
     runs s Ra  = Some (Init, [A,  B],  aKey Kab # nl) \<longrightarrow>
     runs s Ra' = Some (Init, [A', B'], aKey Kab # nl') \<longrightarrow>
     A \<notin> bad \<longrightarrow> B \<notin> bad \<longrightarrow> Kab \<notin> leak s \<longrightarrow>
       Ra = Ra'
  }"

lemmas m1a_inv1_ifreshI = m1a_inv1_ifresh_def [THEN setc_def_to_intro, rule_format]
lemmas m1a_inv1_ifreshE [elim] = m1a_inv1_ifresh_def [THEN setc_def_to_elim, rule_format]
lemmas m1a_inv1_ifreshD = m1a_inv1_ifresh_def [THEN setc_def_to_dest, rule_format, rotated 1]


text \<open>Invariance proof\<close>

lemma PO_m1a_inv1_ifresh_init [iff]:
  "init m1a \<subseteq> m1a_inv1_ifresh"
by (auto simp add: m1a_defs intro!: m1a_inv1_ifreshI)


lemma PO_m1a_inv1_ifresh_step4:
  "{m1a_inv1_ifresh \<inter> m1a_inv2i_serv \<inter> m1x_secrecy} 
      m1a_step4 Ra A B Na Kab nla
   {> m1a_inv1_ifresh}"
proof (auto simp add: PO_hoare_defs m1a_defs intro!: m1a_inv1_ifreshI,  (* UGLY *)
       auto dest: m1a_inv1_ifreshD, auto dest: m1a_inv2i_servD)
  fix Rs Ra' A' B' nl' s 
  assume H: 
    "(sesK (Rs $ sk), A) \<in> azC (runs s)" "sesK (Rs $ sk) \<notin> leak s" 
    "A \<notin> bad" "B \<notin> bad" "Ra' \<noteq> Ra"
    "runs s Ra = Some (Init, [A, B], [])" 
    "runs s Rs = Some (Serv, [A, B], aNon (Ra $ na) # take is_len nla)" 
    "runs s Ra' = Some (Init, [A', B'], aKey (sesK (Rs $ sk)) # nl')"
    "s \<in> m1x_secrecy" "s \<in> m1a_inv2i_serv" 
  thus False
  proof (cases "A' \<in> bad")
    case True 
    from H have "(sesK (Rs$sk), A') \<in> azC (runs s)" by (elim m1x_secrecyE, auto) 
    with H True show ?thesis by (elim azC.cases) (auto dest: m1a_inv2i_servD) 
  next 
    case False thus ?thesis using H by (auto dest: m1a_inv2i_servD)
  qed
next
  fix A' B' Ra' nl s
  assume 
    "(Kab, A) \<in> azC (runs s)" "Kab \<notin> leak s" 
    "A' \<notin> bad"  "B' \<notin> bad" "A \<in> bad" "Ra' \<noteq> Ra"
    "runs s Ra' = Some (Init, [A', B'], aKey Kab # nl)"
    "runs s Ra = Some (Init, [A, B], [])"
    "s \<in> m1a_inv2i_serv" 
  thus False 
  by (elim azC.cases, auto dest: m1a_inv2i_servD)
qed 

lemma PO_m1a_inv1_ifresh_trans [iff]:
  "{m1a_inv1_ifresh \<inter> m1a_inv2i_serv \<inter> m1x_secrecy} trans m1a {> m1a_inv1_ifresh}"
proof (simp add: m1a_def m1a_trans_def, safe)
  fix Ra A B Kab Ts nla
  show
    "{m1a_inv1_ifresh \<inter> m1a_inv2i_serv \<inter> m1x_secrecy} 
        m1a_step4 Ra A B Kab Ts nla
     {> m1a_inv1_ifresh}"
  by (rule PO_m1a_inv1_ifresh_step4)
qed (auto simp add: PO_hoare_defs m1a_defs intro!: m1a_inv1_ifreshI)

lemma PO_m1a_inv1_ifresh [iff]: "reach m1a \<subseteq> m1a_inv1_ifresh"
by (rule_tac J=" m1a_inv2i_serv \<inter> m1x_secrecy" in inv_rule_incr) 
   (auto simp add: Int_assoc del: subsetI)


(******************************************************************************)
subsection \<open>Refinement of \<open>a0n\<close> for responder/server\<close>
(******************************************************************************)

text \<open>For the responder, we get a non-injective agreement with the server on 
the session key, the initiator's name, and additional data.\<close>


subsubsection \<open>Simulation relation\<close>
(******************************************************************************)

text \<open>We define two auxiliary functions to reconstruct the signals of the
initial model from completed responder and server runs.\<close>

type_synonym
  rssig = "key \<times> agent \<times> atom list"

abbreviation
  rs_commit :: "[runs_t, agent, agent, key, atom list] \<Rightarrow> rid_t set" 
where
  "rs_commit runz A B Kab rsl \<equiv> {Rb. \<exists>nlb. 
     runz Rb = Some (Resp, [A, B], aKey Kab # nlb) \<and> take rs_len nlb = rsl 
  }"

fun
  rs_runs2sigs :: "runs_t \<Rightarrow> rssig signal \<Rightarrow> nat"
where
  "rs_runs2sigs runz (Running [B, Sv] (Kab, A, rsl)) = 
     (if (\<exists>Rs Na. Kab = sesK (Rs$sk) \<and> 
           runz Rs = Some (Serv, [A, B], aNon Na # rsl)) 
      then 1 else 0)"

| "rs_runs2sigs runz (Commit [B, Sv] (Kab, A, rsl)) = 
     card (rs_commit runz A B Kab rsl)"

| "rs_runs2sigs runz _ = 0"


text \<open>Simulation relation and mediator function. We map completed initiator 
and responder runs to commit and running signals, respectively.\<close>

definition 
  med_a0m1a_rs :: "m1a_obs \<Rightarrow> rssig a0n_obs" where
  "med_a0m1a_rs o1 \<equiv> \<lparr> signals = rs_runs2sigs (runs o1), corrupted = {} \<rparr>"

definition
  R_a0m1a_rs :: "(rssig a0n_state \<times> m1a_state) set" where
  "R_a0m1a_rs \<equiv> {(s, t). signals s = rs_runs2sigs (runs t) \<and> corrupted s = {} }"

lemmas R_a0m1a_rs_defs = R_a0m1a_rs_def med_a0m1a_rs_def 


subsubsection \<open>Lemmas about the auxiliary functions\<close>
(******************************************************************************)

text \<open>Other lemmas\<close>

lemma rs_runs2sigs_empty [simp]: 
  "runz = Map.empty \<Longrightarrow> rs_runs2sigs runz = (\<lambda>s. 0)"
by (rule ext, erule rev_mp) 
   (rule rs_runs2sigs.induct, auto)

lemma rs_commit_finite [simp, intro]:
  "finite (dom runz) \<Longrightarrow> finite (rs_commit runz A B Kab nls)"
by (auto intro: finite_subset dest: dom_lemmas)


text \<open>Update lemmas\<close>

lemma rs_runs2sigs_upd_init_none [simp]:
  "\<lbrakk> Ra \<notin> dom runz \<rbrakk>
  \<Longrightarrow> rs_runs2sigs (runz(Ra \<mapsto> (Init, [A, B], []))) = rs_runs2sigs runz"
by (rule ext, erule rev_mp) 
   (rule rs_runs2sigs.induct, auto dest: dom_lemmas)

lemma rs_runs2sigs_upd_resp_none [simp]:
  "\<lbrakk> Rb \<notin> dom runz \<rbrakk>
  \<Longrightarrow> rs_runs2sigs (runz(Rb \<mapsto> (Resp, [A, B], []))) = rs_runs2sigs runz"
by (rule ext, erule rev_mp) 
   (rule rs_runs2sigs.induct, auto dest: dom_lemmas)

lemma rs_runs2sigs_upd_serv [simp]:
  "\<lbrakk> Rs \<notin> dom runz \<rbrakk>
  \<Longrightarrow> rs_runs2sigs (runz(Rs \<mapsto> (Serv, [A, B], aNon Na # nls))) = 
     (rs_runs2sigs runz)(Running [B, Sv] (sesK (Rs$sk), A, nls) := 1)"
by (rule ext, erule rev_mp) 
   (rule rs_runs2sigs.induct, auto dest: dom_lemmas)

lemma rs_runs2sigs_upd_init_some [simp]:
  "\<lbrakk> runz Ra = Some (Init, [A, B], []) \<rbrakk>
  \<Longrightarrow> rs_runs2sigs (runz(Ra \<mapsto> (Init, [A, B], aKey Kab # nl))) =
     rs_runs2sigs runz" 
by (rule ext, erule rev_mp)
   (rule rs_runs2sigs.induct, auto dest: dom_lemmas)  

lemma rs_runs2sigs_upd_resp_some [simp]:
  "\<lbrakk> runz Rb = Some (Resp, [A, B], []); finite (dom runz);
     rsl = take rs_len nlb \<rbrakk>
 \<Longrightarrow> rs_runs2sigs (runz(Rb \<mapsto> (Resp, [A, B], aKey Kab # nlb))) =
   (rs_runs2sigs runz)(
      Commit [B, Sv] (Kab, A, rsl) := Suc (card (rs_commit runz A B Kab rsl)))"
apply (rule ext, (erule rev_mp)+) 
apply (rule rs_runs2sigs.induct, auto dest: dom_lemmas)
\<comment> \<open>1 subgoal\<close>
apply (rule_tac s="card (insert Rb (rs_commit runz A B Kab (take rs_len nlb)))" 
       in trans, fast, auto)
done


subsubsection \<open>Refinement proof\<close>
(******************************************************************************)

lemma PO_m1a_step1_refines_a0_rs_skip:
  "{R_a0m1a_rs} 
     Id, (m1a_step1 Ra A B Na) 
   {> R_a0m1a_rs}"
by (auto simp add: PO_rhoare_defs R_a0m1a_rs_defs m1a_defs)

lemma PO_m1a_step2_refines_a0_rs_skip:
  "{R_a0m1a_rs} 
     Id, (m1a_step2 Rb A B) 
   {> R_a0m1a_rs}"
by (auto simp add: PO_rhoare_defs R_a0m1a_rs_defs m1a_defs)

lemma PO_m1a_step3_refines_a0_rs_running:
  "{R_a0m1a_rs} 
     (a0n_running [B, Sv] (Kab, A, nls)), 
     (m1a_step3 Rs A B Kab Na nls) 
   {> R_a0m1a_rs}"
by (auto simp add: PO_rhoare_defs R_a0m1a_rs_defs a0i_defs m1a_defs
         dest: dom_lemmas)

lemma PO_m1a_step4_refines_a0_rs_skip:
  "{R_a0m1a_rs} 
     Id, (m1a_step4 Ra A B Na Kab nla) 
   {> R_a0m1a_rs}"
by (auto simp add: PO_rhoare_defs R_a0m1a_rs_defs a0i_defs m1a_defs)

lemma PO_m1a_step5_refines_a0_rs_commit:
  "{R_a0m1a_rs \<inter> UNIV \<times> m1a_inv0_fin} 
     (a0n_commit [B, Sv] (Kab, A, take rs_len nlb)), 
     (m1a_step5 Rb A B Kab nlb) 
   {> R_a0m1a_rs}"
by (auto simp add: PO_rhoare_defs R_a0m1a_rs_defs a0i_defs m1a_defs)

lemma PO_m1a_leak_refines_a0_rs_skip:
  "{R_a0m1a_rs} 
     Id, (m1a_leak Rs) 
   {> R_a0m1a_rs}"
by (auto simp add: PO_rhoare_defs R_a0m1a_rs_defs a0i_defs m1a_defs)


text \<open>All together now...\<close>

lemmas PO_m1a_trans_refines_a0_rs_trans = 
  PO_m1a_step1_refines_a0_rs_skip PO_m1a_step2_refines_a0_rs_skip
  PO_m1a_step3_refines_a0_rs_running PO_m1a_step4_refines_a0_rs_skip
  PO_m1a_step5_refines_a0_rs_commit PO_m1a_leak_refines_a0_rs_skip


lemma PO_m1a_refines_init_ra0n [iff]:
  "init m1a \<subseteq>  R_a0m1a_rs``(init a0n)"
by (auto simp add: R_a0m1a_rs_defs a0n_defs m1a_defs)

lemma PO_m1a_refines_trans_ra0n [iff]:
  "{R_a0m1a_rs \<inter> a0n_inv1_niagree \<times> m1a_inv0_fin} 
     (trans a0n), (trans m1a) 
   {> R_a0m1a_rs}"
by (force simp add: m1a_def m1a_trans_def a0n_def a0n_trans_def
          intro!: PO_m1a_trans_refines_a0_rs_trans)

lemma obs_consistent_med_a0m1a_rs [iff]: 
  "obs_consistent 
     (R_a0m1a_rs \<inter> a0n_inv1_niagree \<times> m1a_inv0_fin) 
     med_a0m1a_rs a0n m1a"
by (auto simp add: obs_consistent_def R_a0m1a_rs_def med_a0m1a_rs_def 
                   a0n_def m1a_def)


text \<open>Refinement result.\<close>

lemma PO_m1a_refines_a0_rs [iff]: 
  "refines (R_a0m1a_rs \<inter> a0n_inv1_niagree \<times> m1a_inv0_fin) med_a0m1a_rs a0n m1a"
by (rule Refinement_using_invariants) (auto)

lemma m1a_implements_ra0n: "implements med_a0m1a_rs a0n m1a"
by (rule refinement_soundness) (fast)


subsubsection \<open>inv2r (inherited): Responder and server\<close>
(*invh*************************************************************************)

text \<open>This is a translation of the agreement property to Level 1. It
follows from the refinement and not needed here but later.\<close>

definition 
  m1a_inv2r_serv :: "'x m1x_state_scheme set"
where
  "m1a_inv2r_serv \<equiv> {s. \<forall>A B Rb Kab nlb.
     B \<notin> bad \<longrightarrow> 
     runs s Rb = Some (Resp, [A, B], aKey Kab # nlb) \<longrightarrow>
       (\<exists>Rs Na. Kab = sesK (Rs$sk) \<and>
        runs s Rs = Some (Serv, [A, B], aNon Na # take rs_len nlb))
  }"

lemmas m1a_inv2r_servI = 
  m1a_inv2r_serv_def [THEN setc_def_to_intro, rule_format]
lemmas m1a_inv2r_servE [elim] = 
  m1a_inv2r_serv_def [THEN setc_def_to_elim, rule_format]
lemmas m1a_inv2r_servD = 
  m1a_inv2r_serv_def [THEN setc_def_to_dest, rule_format, rotated -1]


text \<open>Invariance proof\<close>

lemma PO_m1a_inv2r_serv [iff]:
  "reach m1a \<subseteq> m1a_inv2r_serv"
apply (rule INV_from_Refinement_basic [OF PO_m1a_refines_a0_rs])
apply (auto simp add: R_a0m1a_rs_def a0n_inv1_niagree_def intro!: m1a_inv2r_servI)
apply (rename_tac x A B Rb Kab nlb a, drule_tac x="[B, Sv]" in spec, clarsimp)
apply (rename_tac x A B Rb Kab nlb a, drule_tac x="Kab" in spec, force)
done


end
