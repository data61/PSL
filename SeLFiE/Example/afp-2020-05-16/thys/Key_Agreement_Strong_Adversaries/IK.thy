(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  IK.thy (Isabelle/HOL 2016-1)
  ID:      $Id: IK.thy 132882 2016-12-23 09:03:55Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  State with intruder knowledge and corresponding Dolev-Yao derivation event.
  - This is used a building block for Secrecy model. 
  - The attacker event is also used by level-3 models.

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Environment: Dolev-Yao Intruder\<close>

theory IK
imports Message_derivation 
begin

text \<open>Basic state contains intruder knowledge. The secrecy model and concrete Level 1 
states will be record extensions of this state.\<close>

record ik_state =
  ik :: "msg set"


text \<open>Dolev-Yao intruder event adds a derived message.\<close>

definition
  ik_dy :: "msg \<Rightarrow> ('a ik_state_scheme * 'a ik_state_scheme) set"
where
  "ik_dy m \<equiv> {(s, s').
    \<comment> \<open>guard\<close>
    m \<in> synth (analz (ik s)) \<and>

    \<comment> \<open>action\<close>
    s' = s \<lparr>ik := ik s \<union> {m}\<rparr>
  }"

definition
  ik_trans :: "('a ik_state_scheme * 'a ik_state_scheme) set"
where
  "ik_trans \<equiv> (\<Union> m.  ik_dy m)"

lemmas ik_trans_defs = ik_trans_def ik_dy_def


lemma ik_trans_ik_increasing: "(s, s') \<in> ik_trans \<Longrightarrow> ik s \<subseteq> ik s'"
by (auto simp add: ik_trans_defs)

lemma ik_trans_synth_analz_ik_increasing: 
  "(s, s') \<in> ik_trans \<Longrightarrow> synth (analz (ik s)) \<subseteq> synth (analz (ik s'))"
by (simp only: synth_analz_mono ik_trans_ik_increasing)


end
