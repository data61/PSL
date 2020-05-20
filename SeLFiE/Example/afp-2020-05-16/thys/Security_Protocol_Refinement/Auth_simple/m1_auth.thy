(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Auth_simple/m1_auth.thy (Isabelle/HOL 2016-1)
  ID:      $Id: m1_auth.thy 134925 2017-05-24 17:53:14Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  One-Way authentication protocols
  Refinement 1: Direct memory access protocol 

  Copyright (c) 2009-2016 Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

chapter \<open>Unidirectional Authentication Protocols\<close>

text \<open>In this chapter, we derive some simple unilateral authentication 
protocols. We have a single abstract model at Level 1. We then refine this model 
into two channel protocols (Level 2), one using authentic channels and one using 
confidential channels. We then refine these in turn into cryptographic protocols 
(Level 3) respectively using signatures and public-key encryption.
\<close>


section \<open>Refinement 1: Abstract Protocol\<close>

theory m1_auth imports "../Refinement/Runs" "../Refinement/a0i_agree"
begin

(* declare option.split_asm [split] *)
declare domIff [simp, iff del]

(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>We introduce protocol runs.\<close>

record m1_state = 
  runs :: runs_t

type_synonym 
  m1_obs = m1_state

definition 
  m1_init :: "m1_state set" where
  "m1_init \<equiv> { \<lparr> 
     runs = Map.empty 
  \<rparr> }"

(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

definition   \<comment> \<open>refines @{term skip}\<close>
  m1_step1 :: "[rid_t, agent, agent, nonce] \<Rightarrow> (m1_state \<times> m1_state) set" 
where  
  "m1_step1 Ra A B Na \<equiv> {(s, s1).  

     \<comment> \<open>guards\<close>
     Ra \<notin> dom (runs s) \<and>              \<comment> \<open>new initiator run\<close>
     Na = Ra$0 \<and>                      \<comment> \<open>generated nonce\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       runs := (runs s)(
         Ra \<mapsto> (Init, [A, B], [])
       )  
     \<rparr>
  }"

definition   \<comment> \<open>refines @{term a0i_running}\<close>
  m1_step2 :: "[rid_t, agent, agent, nonce, nonce] \<Rightarrow> (m1_state \<times> m1_state) set" 
where
  "m1_step2 Rb A B Na Nb \<equiv> {(s, s1).  \<comment> \<open>\<open>Ni\<close> is completely arbitrary\<close>

     \<comment> \<open>guards\<close>
     Rb \<notin> dom (runs s) \<and>              \<comment> \<open>new responder run\<close>
     Nb = Rb$0 \<and>                      \<comment> \<open>generated nonce\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr>
       runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [aNon Na]))
     \<rparr>
  }"

definition   \<comment> \<open>refines @{term a0i_commit}\<close>
  m1_step3 :: 
    "[rid_t, agent, agent, nonce, nonce] \<Rightarrow> (m1_state \<times> m1_state) set" 
where
  "m1_step3 Ra A B Na Nb \<equiv> {(s, s1).

     \<comment> \<open>guards\<close>
     runs s Ra = Some (Init, [A, B], []) \<and>
     Na = Ra$0 \<and>

     \<comment> \<open>authentication guard:\<close>
     (A \<notin> bad \<and> B \<notin> bad \<longrightarrow> (\<exists>Rb. 
        Nb = Rb$0 \<and> runs s Rb = Some (Resp, [A, B], [aNon Na]))) \<and>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr>
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aNon Nb]))
     \<rparr>
  }"

text \<open>Transition system.\<close>

definition 
  m1_trans :: "(m1_state \<times> m1_state) set" where
  "m1_trans \<equiv> (\<Union> A B Ra Rb Na Nb.
     m1_step1 Ra A B Na    \<union>
     m1_step2 Rb A B Na Nb \<union>
     m1_step3 Ra A B Na Nb \<union>
     Id
  )"

definition
  m1 :: "(m1_state, m1_obs) spec" where
  "m1 \<equiv> \<lparr>
    init = m1_init,
    trans = m1_trans, 
    obs = id
  \<rparr>"

lemmas m1_defs = 
  m1_def m1_init_def m1_trans_def
  m1_step1_def m1_step2_def m1_step3_def 


(******************************************************************************)
subsection \<open>Simulation relation\<close>
(******************************************************************************)

text \<open>We define two auxiliary functions to reconstruct the signals of the
initial model from completed initiator and responder runs of the current one.\<close>

type_synonym 
  irsig = "nonce \<times> nonce"

fun
  runs2sigs :: "runs_t \<Rightarrow> irsig signal \<Rightarrow> nat"
where
  "runs2sigs runz (Commit [A, B] (Ra$0, Nb)) = 
    (if runz Ra = Some (Init, [A, B], [aNon Nb]) then 1 else 0)"

| "runs2sigs runz (Running [A, B] (Na, Rb$0)) = 
    (if runz Rb = Some (Resp, [A, B], [aNon Na]) then 1 else 0)"

| "runs2sigs runz _ = 0"


text \<open>Simulation relation and mediator function. We map completed initiator 
and responder runs to commit and running signals, respectively.\<close>

definition 
  med10 :: "m1_obs \<Rightarrow> irsig a0i_obs" where
  "med10 o1 \<equiv> \<lparr> signals = runs2sigs (runs o1), corrupted = {} \<rparr>"

definition
  R01 :: "(irsig a0i_state \<times> m1_state) set" where
  "R01 \<equiv> {(s, t). signals s = runs2sigs (runs t) \<and> corrupted s = {} }"

lemmas R01_defs = R01_def med10_def 


subsubsection \<open>Lemmas about the auxiliary functions\<close>
(******************************************************************************)

text \<open>Basic lemmas\<close>

lemma runs2sigs_empty [simp]: 
  "runz = Map.empty \<Longrightarrow> runs2sigs runz = (\<lambda>x. 0)"
by (rule ext, erule rev_mp) 
   (rule runs2sigs.induct, auto)


text \<open>Update lemmas\<close>

lemma runs2sigs_upd_init_none [simp]:
  "\<lbrakk> Ra \<notin> dom runz \<rbrakk>
  \<Longrightarrow> runs2sigs (runz(Ra \<mapsto> (Init, [A, B], []))) = runs2sigs runz"
by (rule ext, erule rev_mp)
   (rule runs2sigs.induct, auto dest: dom_lemmas)

lemma runs2sigs_upd_init_some [simp]:
  "\<lbrakk> runz Ra = Some (Init, [A, B], []) \<rbrakk>
  \<Longrightarrow> runs2sigs (runz(Ra \<mapsto> (Init, [A, B], [aNon Nb]))) = 
     (runs2sigs runz)(Commit [A, B] (Ra$0, Nb) := 1)"
by (rule ext, erule rev_mp) 
   (rule runs2sigs.induct, auto)

lemma runs2sigs_upd_resp [simp]:
  "\<lbrakk> Rb \<notin> dom runz \<rbrakk>
  \<Longrightarrow> runs2sigs (runz(Rb \<mapsto> (Resp, [A, B], [aNon Na]))) = 
     (runs2sigs runz)(Running [A, B] (Na, Rb$0) := 1)"
by (rule ext, (erule rev_mp)+) 
   (rule runs2sigs.induct, auto dest: dom_lemmas)


(******************************************************************************)
subsection \<open>Refinement\<close>
(******************************************************************************)

lemma PO_m1_step1_refines_skip:
  "{R01} 
     Id, (m1_step1 Ra A B Na) 
   {> R01}"
by (auto simp add: PO_rhoare_def R01_defs a0i_defs m1_defs)

lemma PO_m1_step2_refines_a0i_running:
  "{R01} 
     (a0i_running [A, B] (Na, Nb)), (m1_step2 Rb A B Na Nb) 
   {> R01}"
by (auto simp add: PO_rhoare_defs R01_defs a0i_defs m1_defs dest: dom_lemmas) 

lemma PO_m1_step3_refines_a0i_commit:
  "{R01} 
     (a0i_commit [A, B] (Na, Nb)), (m1_step3 Ra A B Na Nb) 
   {> R01}"
by (auto simp add: PO_rhoare_defs R01_defs a0i_defs m1_defs)

lemmas PO_m1_trans_refines_a0i_trans = 
  PO_m1_step1_refines_skip PO_m1_step2_refines_a0i_running
  PO_m1_step3_refines_a0i_commit


text \<open>All together now...\<close>

lemma PO_m1_refines_init_a0i [iff]:
  "init m1 \<subseteq> R01``(init a0i)"
by (auto simp add: R01_defs a0i_defs m1_defs)

lemma PO_m1_refines_trans_a0i [iff]:
  "{R01} 
     (trans a0i), (trans m1) 
   {> R01}"
by (auto simp add: m1_def m1_trans_def a0i_def a0i_trans_def
         intro!: PO_m1_trans_refines_a0i_trans)

lemma PO_obs_consistent [iff]:
  "obs_consistent R01 med10 a0i m1"
by (auto simp add: obs_consistent_def R01_defs a0i_def m1_def)

lemma PO_m1_refines_a0i:
  "refines R01 med10 a0i m1"
by (rule Refinement_basic) (auto)


end
