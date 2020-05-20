(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Key_establish/m1b_keydist.thy (Isabelle/HOL 2016-1)
  ID:      $Id: m1_keydist.thy 134925 2017-05-24 17:53:14Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Key distribution protocols
  First refinement: abstract server-based key transport protocol with 
  initiator and responder roles.

  Copyright (c) 2009-2016 Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

chapter \<open>Key Establishment Protocols\<close>

text \<open>In this chapter, we develop several key establishment protocols:
\begin{itemize} 
\item Needham-Schroeder Shared Key (NSSK) 
\item core Kerberos IV and V, and
\item Denning-Sacco. 
\end{itemize}
\<close>


section \<open>Basic abstract key distribution (L1)\<close>

theory m1_keydist imports "../Refinement/Runs" "../Refinement/s0g_secrecy"
begin

text \<open>The first refinement introduces the protocol roles, local memory of the
agents and the communication structure of the protocol.  For actual 
communication, the "receiver" directly reads the memory of the "sender". 

It captures the core of essentials of server-based key distribution protocols:
The server generates a key that the clients read from his memory. At this
stage we are only interested in secrecy preservation, not in authentication.
\<close>

declare option.split_asm [split]
declare domIff [simp, iff del] 

consts
  sk :: "nat"             \<comment> \<open>identifier used for session keys\<close>


(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>Runs record the protocol participants (initiator, responder) and the 
keys learned during the execution. In later refinements, we will also add
nonces and timestamps to the run record.

The variables \<open>kn\<close> and \<open>az\<close> from \<open>s0g_secrecy_leak\<close> 
are replaced by runs using a data refinement. Variable \<open>lk\<close> is 
concretized into variable \<open>leak\<close>. 

We define the state in two separate record definitions. The first one has 
just a runs field and the second extends this with a leak field.  Later 
refinements may define different state for leaks (e.g. to record more context).
\<close>

record m1r_state = 
  runs :: runs_t

record m1x_state = m1r_state +  
  leak :: "key set"             \<comment> \<open>keys leaked to attacker\<close>

type_synonym m1x_obs = "m1x_state"

text \<open>Predicate types for invariants and transition relation types. Use the
r-version for invariants and transitions if there is no reference to the leak
variable. This improves reusability in later refinements.
\<close>
type_synonym 'x m1r_pred = "'x m1r_state_scheme set"
type_synonym 'x m1x_pred = "'x m1x_state_scheme set"

type_synonym 'x m1r_trans = "('x m1r_state_scheme \<times> 'x m1r_state_scheme) set"
type_synonym 'x m1x_trans = "('x m1x_state_scheme \<times> 'x m1x_state_scheme) set"


subsubsection \<open>Key knowledge and authorization (reconstruction)\<close>
(******************************************************************************)

text \<open>Key knowledge and authorization relations, reconstructed from the runs 
and an unspecified initial key setup. These auxiliary definitions are used in 
some event guards and in the simulation relation (see below).\<close>

text \<open>Knowledge relation (reconstructed)\<close>

inductive_set
  knC :: "runs_t \<Rightarrow> (key \<times> agent) set" for runz :: "runs_t" 
where
  knC_init:
    "runz Ra = Some (Init, [A, B], aKey K # al) \<Longrightarrow> (K, A) \<in> knC runz"
| knC_resp:
    "runz Rb = Some (Resp, [A, B], aKey K # al) \<Longrightarrow> (K, B) \<in> knC runz"
| knC_serv:
    "\<lbrakk> Rs \<in> dom runz; fst (the (runz Rs)) = Serv \<rbrakk> \<Longrightarrow> (sesK (Rs$sk), Sv) \<in> knC runz"
| knC_0:
    "(K, A) \<in> keySetup \<Longrightarrow> (K, A) \<in> knC runz"


text \<open>Authorization relation (reconstructed)\<close>

inductive_set
  azC :: "runs_t \<Rightarrow> (key \<times> agent) set" for runz :: "runs_t"
where
  azC_good:
    "\<lbrakk> runz Rs = Some (Serv, [A, B], al); C \<in> {A, B, Sv} \<rbrakk> 
   \<Longrightarrow> (sesK (Rs$sk), C) \<in> azC runz"
| azC_bad:
    "\<lbrakk> runz Rs = Some (Serv, [A, B], al); A \<in> bad \<or> B \<in> bad \<rbrakk> 
   \<Longrightarrow> (sesK (Rs$sk), C) \<in> azC runz"
| azC_0:
    "\<lbrakk> (K, C) \<in> keySetup \<rbrakk> \<Longrightarrow> (K, C) \<in> azC runz"


declare knC.intros [intro]
declare azC.intros [intro]


text \<open>Misc lemmas: empty state, projections, ...\<close>

lemma knC_empty [simp]: "knC Map.empty = keySetup"
by (auto elim: knC.cases)

lemma azC_empty [simp]: "azC Map.empty = keySetup"
by (auto elim: azC.cases)


text \<open>\<open>azC\<close> and run abstraction\<close>

lemma azC_map_runs [simp]: "azC (map_runs h runz) = azC runz"
by (auto simp add: map_runs_def elim!: azC.cases)


text \<open>Update lemmas for @{term "knC"}\<close>

lemma knC_upd_Init_Resp_None:
  "\<lbrakk> R \<notin> dom runz; rol \<in> {Init, Resp} \<rbrakk>
  \<Longrightarrow> knC (runz(R \<mapsto> (rol, [A, B], []))) = knC runz"
by (fastforce simp add: domIff elim!: knC.cases)

lemma knC_upd_Init_Some:
  "\<lbrakk> runz Ra = Some (Init, [A, B], []) \<rbrakk> 
  \<Longrightarrow> knC (runz(Ra \<mapsto> (Init, [A, B], [aKey Kab]))) = insert (Kab, A) (knC runz)"
apply (auto elim!: knC.cases) 
\<comment> \<open>3 subgoals\<close>
apply (rename_tac Raa Aa Ba K al, rule_tac A=Aa and B=Ba and al=al in knC_init, auto)
apply (rename_tac Rb Aa Ba K al, rule_tac A=Aa and B=Ba and al=al in knC_resp, auto)
apply (rule_tac knC_serv, auto)
done

lemma knC_upd_Resp_Some:
  "\<lbrakk> runz Ra = Some (Resp, [A, B], []) \<rbrakk> 
  \<Longrightarrow> knC (runz(Ra \<mapsto> (Resp, [A, B], [aKey Kab]))) = insert (Kab, B) (knC runz)"
apply (auto elim!: knC.cases)
\<comment> \<open>3 subgoals\<close>
apply (rename_tac Raa Aa Ba K al, rule_tac A=Aa and B=Ba and al=al in knC_init, auto)
apply (rename_tac Raa Aa Ba K al, rule_tac A=Aa and B=Ba and al=al in knC_resp, auto)
apply (rule_tac knC_serv, auto)
done

lemma knC_upd_Server:
  "\<lbrakk> Rs \<notin> dom runz \<rbrakk>
  \<Longrightarrow> knC (runz(Rs \<mapsto> (Serv, [A, B], []))) = insert (sesK (Rs$sk), Sv) (knC runz)"
apply (auto elim!: knC.cases)
\<comment> \<open>2 subgoals\<close>
apply (rename_tac Raa Aa Ba K al, rule_tac A=Aa and B=Ba in knC_init, auto dest: dom_lemmas)
apply (rename_tac Raa Aa Ba K al, rule_tac A=Aa and B=Ba in knC_resp, auto dest: dom_lemmas)
done

lemmas knC_upd_lemmas [simp] = 
  knC_upd_Init_Resp_None knC_upd_Init_Some knC_upd_Resp_Some
  knC_upd_Server 


text \<open>Update lemmas for @{term "azC"}\<close>

lemma azC_upd_Init_None:
  "\<lbrakk> Ra \<notin> dom runz \<rbrakk>
  \<Longrightarrow> azC (runz(Ra \<mapsto> (Init, [A, B], []))) = azC runz"
by (auto simp add: azC.simps elim!: azC.cases dest: dom_lemmas)

lemma azC_upd_Resp_None:
  "\<lbrakk> Rb \<notin> dom runz \<rbrakk>
  \<Longrightarrow> azC (runz(Rb \<mapsto> (Resp, [A, B], []))) = azC runz"
by (auto simp add: azC.simps elim!: azC.cases dest: dom_lemmas)

lemma azC_upd_Init_Some:
  "\<lbrakk> runz Ra = Some (Init, [A, B], []) \<rbrakk>
  \<Longrightarrow> azC (runz(Ra \<mapsto> (Init, [A, B], al))) = azC runz"
apply (auto elim!: azC.cases)
\<comment> \<open>5 subgoals\<close>
apply (rule_tac azC_good, auto)
apply (rule_tac azC_good, auto)
apply (rule_tac azC_good, auto)
apply (rule_tac azC_bad, auto)+
done

lemma azC_upd_Resp_Some:
  "\<lbrakk> runz Rb = Some (Resp, [A, B], []) \<rbrakk>
  \<Longrightarrow> azC (runz(Rb \<mapsto> (Resp, [A, B], al))) = azC runz"
apply (auto elim!: azC.cases)
\<comment> \<open>5 subgoals\<close>
apply (rule_tac azC_good, auto)
apply (rule_tac azC_good, auto)
apply (rule_tac azC_good, auto)
apply (rule_tac azC_bad, auto)+
done

lemma azC_upd_Serv_bad:
  "\<lbrakk> Rs \<notin> dom runz; A \<in> bad \<or> B \<in> bad \<rbrakk>
  \<Longrightarrow> azC (runz(Rs \<mapsto> (Serv, [A, B], al))) = azC runz \<union> {sesK (Rs$sk)} \<times> UNIV"
apply (auto elim!: azC.cases)
\<comment> \<open>10 subgoals\<close>
apply (
  rename_tac Rsa Aa Ba ala, rule_tac A=Aa and B=Ba and al=ala in azC_good, auto dest: dom_lemmas,
  rename_tac Rsa Aa Ba ala, rule_tac A=Aa and B=Ba and al=ala in azC_good, auto dest: dom_lemmas,
  rename_tac Rsa Aa Ba ala, rule_tac A=Aa and B=Ba and al=ala in azC_good, auto dest: dom_lemmas,
  rename_tac Rsa Aa Ba ala C, rule_tac A=Aa and B=Ba and al=ala in azC_bad, auto dest: dom_lemmas,
  rename_tac Rsa Aa Ba ala C, rule_tac A=Aa and B=Ba and al=ala in azC_bad, auto dest: dom_lemmas
)+
done

lemma azC_upd_Serv_good:
  "\<lbrakk> Rs \<notin> dom runz; K = sesK (Rs$sk); A \<notin> bad; B \<notin> bad \<rbrakk>
  \<Longrightarrow> azC (runz(Rs \<mapsto> (Serv, [A, B], al))) 
      = azC runz \<union> {(K, A), (K, B), (K, Sv)}"
apply (auto elim!: azC.cases)
\<comment> \<open>5 subgoals\<close>
apply (
  rename_tac Rsa Aa Ba ala, rule_tac A=Aa and B=Ba and al=ala in azC_good, auto dest: dom_lemmas,
  rename_tac Rsa Aa Ba ala, rule_tac A=Aa and B=Ba and al=ala in azC_good, auto dest: dom_lemmas,
  rename_tac Rsa Aa Ba ala, rule_tac A=Aa and B=Ba and al=ala in azC_good, auto dest: dom_lemmas,
  rename_tac Rsa Aa Ba ala C, rule_tac A=Aa and B=Ba and al=ala in azC_bad, auto dest: dom_lemmas,
  rename_tac Rsa Aa Ba ala C, rule_tac A=Aa and B=Ba and al=ala in azC_bad, auto dest: dom_lemmas
)+
done

lemma azC_upd_Serv:
  "\<lbrakk> Rs \<notin> dom runz; K = sesK (Rs$sk) \<rbrakk>
  \<Longrightarrow> azC (runz(Rs \<mapsto> (Serv, [A, B], al))) =
     azC runz \<union> {K} \<times> (if A \<notin> bad \<and> B \<notin> bad then {A, B, Sv} else UNIV)" 
by (simp add: azC_upd_Serv_bad azC_upd_Serv_good) 

lemmas azC_upd_lemmas [simp] =
  azC_upd_Init_None azC_upd_Resp_None
  azC_upd_Init_Some azC_upd_Resp_Some azC_upd_Serv


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

definition     \<comment> \<open>by @{term "A"}, refines skip\<close>
  m1x_step1 :: "[rid_t, agent, agent] \<Rightarrow> 'x m1r_trans"
where
  "m1x_step1 Ra A B \<equiv> {(s, s1).

    \<comment> \<open>guards:\<close>
    Ra \<notin> dom (runs s) \<and>                \<comment> \<open>\<open>Ra\<close> is fresh\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>create initiator thread\<close>
    s1 = s\<lparr> runs := (runs s)(Ra \<mapsto> (Init, [A, B], [])) \<rparr>
  }"

definition     \<comment> \<open>by @{term "B"}, refines skip\<close>
  m1x_step2 :: "[rid_t, agent, agent] \<Rightarrow> 'x m1r_trans"
where
  "m1x_step2 Rb A B \<equiv> {(s, s1).

    \<comment> \<open>guards:\<close>
    Rb \<notin> dom (runs s) \<and>               \<comment> \<open>\<open>Rb\<close> is fresh\<close>

    \<comment> \<open>actions:\<close>
    \<comment> \<open>create responder thread\<close>
    s1 = s\<lparr> runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [])) \<rparr>
  }"

definition     \<comment> \<open>by @{term "Server"}, refines @{term s0g_gen}\<close>
  m1x_step3 :: "[rid_t, agent, agent, key] \<Rightarrow> 'x m1r_trans"
where
  "m1x_step3 Rs A B Kab \<equiv> {(s, s1).

    \<comment> \<open>guards:\<close>
    Rs \<notin> dom (runs s) \<and>                        \<comment> \<open>\<open>Rs\<close> is fresh\<close>
    Kab = sesK (Rs$sk) \<and>                       \<comment> \<open>generate session key\<close>

    \<comment> \<open>actions:\<close>
    s1 = s\<lparr> runs := (runs s)(Rs \<mapsto> (Serv, [A, B], [])) \<rparr>
  }"

definition     \<comment> \<open>by @{term "A"}, refines @{term s0g_learn}\<close>
  m1x_step4 :: "[rid_t, agent, agent, key] \<Rightarrow> 'x m1x_trans"
where
  "m1x_step4 Ra A B Kab \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    runs s Ra = Some (Init, [A, B], []) \<and>
    (Kab \<notin> leak s \<longrightarrow> (Kab, A) \<in> azC (runs s)) \<and>   \<comment> \<open>authorization guard\<close>

    \<comment> \<open>actions:\<close>
    s1 = s\<lparr> runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aKey Kab])) \<rparr>
  }"

definition     \<comment> \<open>by @{text "B"}, refines @{term s0g_learn}\<close>
  m1x_step5 :: "[rid_t, agent, agent, key] \<Rightarrow> 'x m1x_trans"
where
  "m1x_step5 Rb A B Kab \<equiv> {(s, s1).
    \<comment> \<open>guards:\<close>
    runs s Rb = Some (Resp, [A, B], []) \<and> 
    (Kab \<notin> leak s \<longrightarrow> (Kab, B) \<in> azC (runs s)) \<and>    \<comment> \<open>authorization guard\<close>

    \<comment> \<open>actions:\<close>
    s1 = s\<lparr> runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [aKey Kab])) \<rparr>
  }"

definition     \<comment> \<open>by attacker, refines @{term s0g_leak}\<close>
  m1x_leak :: "rid_t \<Rightarrow> 'x m1x_trans"
where
  "m1x_leak Rs \<equiv> {(s, s1).           
    \<comment> \<open>guards:\<close>
    Rs \<in> dom (runs s) \<and>
    fst (the (runs s Rs)) = Serv \<and>         \<comment> \<open>compromise server run \<open>Rs\<close>\<close>

    \<comment> \<open>actions:\<close>
    s1 = s\<lparr> leak := insert (sesK (Rs$sk)) (leak s) \<rparr>
  }"


(******************************************************************************)
subsection \<open>Specification\<close>
(******************************************************************************)

definition 
  m1x_init :: "m1x_state set"
where
  "m1x_init \<equiv> { \<lparr>
     runs = Map.empty,
     leak = corrKey         \<comment> \<open>statically corrupted keys initially leaked\<close>
  \<rparr> }"

definition 
  m1x_trans :: "'x m1x_trans" where
  "m1x_trans \<equiv> (\<Union>A B Ra Rb Rs Kab.
     m1x_step1 Ra A B \<union>
     m1x_step2 Rb A B \<union>
     m1x_step3 Rs A B Kab \<union>
     m1x_step4 Ra A B Kab \<union>
     m1x_step5 Rb A B Kab \<union>
     m1x_leak Rs \<union>
     Id
  )"

definition 
  m1x :: "(m1x_state, m1x_obs) spec" where
  "m1x \<equiv> \<lparr>
    init = m1x_init,
    trans = m1x_trans,
    obs = id
  \<rparr>"

lemmas m1x_defs = 
  m1x_def m1x_init_def m1x_trans_def
  m1x_step1_def m1x_step2_def m1x_step3_def m1x_step4_def m1x_step5_def 
  m1x_leak_def 

lemma m1x_obs_id [simp]: "obs m1x = id"
by (simp add: m1x_def)


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

subsubsection \<open>inv1: Key definedness\<close>
(*inv**************************************************************************)

text \<open>Only run identifiers or static keys can be (concretely) known or 
authorized keys. (This reading corresponds to the contraposition of the 
property expressed below.)\<close>

definition 
  m1x_inv1_key :: "m1x_state set" 
where
  "m1x_inv1_key \<equiv> {s. \<forall>Rs A.
     Rs \<notin> dom (runs s) \<longrightarrow> 
       (sesK (Rs$sk), A) \<notin> knC (runs s) \<and> 
       (sesK (Rs$sk), A) \<notin> azC (runs s) \<and>
       sesK (Rs$sk) \<notin> leak s
  }"

lemmas m1x_inv1_keyI = m1x_inv1_key_def [THEN setc_def_to_intro, rule_format]
lemmas m1x_inv1_keyE [elim] = 
  m1x_inv1_key_def [THEN setc_def_to_elim, rule_format]
lemmas m1x_inv1_keyD [dest] = 
  m1x_inv1_key_def [THEN setc_def_to_dest, rule_format, rotated 1]


text \<open>Invariance proof.\<close>

lemma PO_m1x_inv1_key_init [iff]:
  "init m1x \<subseteq> m1x_inv1_key"
by (auto simp add: m1x_defs m1x_inv1_key_def) 

lemma PO_m1x_inv1_key_trans [iff]:
  "{m1x_inv1_key} trans m1x {> m1x_inv1_key}"
by (auto simp add: PO_hoare_defs m1x_defs intro!: m1x_inv1_keyI)

lemma PO_m1x_inv1_key [iff]: "reach m1x \<subseteq> m1x_inv1_key"
by (rule inv_rule_basic) (auto)


(******************************************************************************)
subsection \<open>Refinement of s0g\<close>
(******************************************************************************)

text \<open>med10: The mediator function maps a concrete observation to an 
abstract one.\<close>

definition 
  med01x :: "m1x_obs \<Rightarrow> key s0g_obs"
where
  "med01x t \<equiv> \<lparr> kn = knC (runs t), az = azC (runs t), lk = leak t \<rparr>"


text \<open>R01: The simulation relation expreses key knowledge and authorization
in terms of the client and server run information.\<close>

definition
  R01x :: "(key s0g_state \<times> m1x_state) set" where
  "R01x \<equiv> {(s, t). s = med01x t}"

lemmas R01x_defs = R01x_def med01x_def


text \<open>Refinement proof.\<close>

lemma PO_m1x_step1_refines_skip:
  "{R01x} 
     Id, (m1x_step1 Ra A B) 
   {> R01x}"
by (auto simp add: PO_rhoare_defs R01x_defs s0g_defs m1x_defs)

lemma PO_m1x_step2_refines_skip:
  "{R01x} 
     Id, (m1x_step2 Rb A B) 
   {> R01x}"
by (auto simp add: PO_rhoare_defs R01x_defs s0g_defs m1x_defs)

lemma PO_m1x_step3_refines_s0g_gen:
  "{R01x \<inter> UNIV \<times> m1x_inv1_key} 
     (s0g_gen Kab Sv {Sv, A, B}), (m1x_step3 Rs A B Kab) 
   {> R01x}"
by (auto simp add: PO_rhoare_defs R01x_defs s0g_defs m1x_defs)

lemma PO_m1x_step4_refines_s0g_learn:
  "{R01x} 
     (s0g_learn Kab A), (m1x_step4 Ra A B Kab) 
   {> R01x}"
by (auto simp add: PO_rhoare_defs R01x_defs s0g_defs m1x_defs)

lemma PO_m1x_step5_refines_s0g_learn:
  "{R01x} 
     (s0g_learn Kab B), (m1x_step5 Rb A B Kab) 
   {> R01x}"
by (auto simp add: PO_rhoare_defs R01x_defs s0g_defs m1x_defs) 

lemma PO_m1x_leak_refines_s0g_leak:
  "{R01x} 
     (s0g_leak (sesK (Rs$sk))), (m1x_leak Rs) 
   {> R01x}"
by (fastforce simp add: PO_rhoare_defs R01x_defs s0g_defs m1x_defs)


text \<open>All together now...\<close>

lemmas PO_m1x_trans_refines_s0g_trans = 
  PO_m1x_step1_refines_skip PO_m1x_step2_refines_skip
  PO_m1x_step3_refines_s0g_gen PO_m1x_step4_refines_s0g_learn 
  PO_m1x_step5_refines_s0g_learn PO_m1x_leak_refines_s0g_leak

lemma PO_m1x_refines_init_s0g [iff]:
  "init m1x \<subseteq> R01x``(init s0g)"
by (auto simp add: R01x_defs s0g_defs m1x_defs intro!: s0g_secrecyI s0g_domI)

lemma PO_m1x_refines_trans_s0g [iff]:
  "{R01x \<inter> UNIV \<times> m1x_inv1_key} 
     (trans s0g), (trans m1x) 
   {> R01x}"
by (auto simp add: m1x_def m1x_trans_def s0g_def s0g_trans_def
         intro!: PO_m1x_trans_refines_s0g_trans)


text \<open>Observation consistency.\<close>

lemma obs_consistent_med01x [iff]: 
  "obs_consistent R01x med01x s0g m1x"
by (auto simp add: obs_consistent_def R01x_defs s0g_def m1x_def)


text \<open>Refinement result.\<close>

lemma PO_m1x_refines_s0g [iff]: 
  "refines 
     (R01x \<inter> UNIV \<times> m1x_inv1_key)
     med01x s0g m1x"
by (rule Refinement_using_invariants) (auto del: subsetI)

lemma  m1x_implements_s0g [iff]: "implements med01x s0g m1x"
by (rule refinement_soundness) (fast)


subsection \<open>Derived invariants\<close>
(******************************************************************************)

subsubsection \<open>inv2: Secrecy\<close>
(*invh*************************************************************************)

text \<open>Secrecy, expressed in terms of runs.\<close>

definition 
  m1x_secrecy :: "'x m1x_pred"
where
  "m1x_secrecy \<equiv> {s. knC (runs s) \<subseteq> azC (runs s) \<union> leak s \<times> UNIV}"

lemmas m1x_secrecyI = m1x_secrecy_def [THEN setc_def_to_intro, rule_format]
lemmas m1x_secrecyE [elim] = m1x_secrecy_def [THEN setc_def_to_elim, rule_format]


text \<open>Invariance proof.\<close>

lemma PO_m1x_obs_secrecy [iff]: "oreach m1x \<subseteq> m1x_secrecy"
apply (rule external_invariant_translation [OF PO_s0g_obs_secrecy _ m1x_implements_s0g])
apply (auto simp add: med01x_def m1x_secrecy_def s0g_secrecy_def)
done

lemma PO_m1x_secrecy [iff]: "reach m1x \<subseteq> m1x_secrecy"
by (rule external_to_internal_invariant [OF PO_m1x_obs_secrecy], auto)


end

