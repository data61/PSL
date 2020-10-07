(*  Title:       variants/b_fwdrreps/OAodv.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
*)

section "The `open' AODV model"

theory B_OAodv
imports B_Aodv AWN.OAWN_SOS_Labels AWN.OAWN_Convert
begin

text \<open>Definitions for stating and proving global network properties over individual processes.\<close>

definition \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V' :: "((ip \<Rightarrow> state) \<times> ((state, msg, pseqp, pseqp label) seqp)) set"
where "\<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V' \<equiv> {(\<lambda>i. aodv_init i, \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PAodv)}"

abbreviation opaodv
  :: "ip \<Rightarrow> ((ip \<Rightarrow> state) \<times> (state, msg, pseqp, pseqp label) seqp, msg seq_action) automaton"
where
  "opaodv i \<equiv> \<lparr> init = \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V', trans = oseqp_sos \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i \<rparr>"

lemma initiali_aodv [intro!, simp]: "initiali i (init (opaodv i)) (init (paodv i))"
  unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_def \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V'_def by rule simp_all

lemma oaodv_control_within [simp]: "control_within \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (init (opaodv i))"
  unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V'_def by (rule control_withinI) (auto simp del: \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_simps)

lemma \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V'_labels [simp]: "(\<sigma>, p) \<in> \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V' \<Longrightarrow>  labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p = {PAodv-:0}"
  unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V'_def by simp

lemma oaodv_init_kD_empty [simp]:
  "(\<sigma>, p) \<in> \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V' \<Longrightarrow> kD (rt (\<sigma> i)) = {}"
  unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V'_def kD_def by simp

lemma oaodv_init_vD_empty [simp]:
  "(\<sigma>, p) \<in> \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V' \<Longrightarrow> vD (rt (\<sigma> i)) = {}"
  unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V'_def vD_def by simp

lemma oaodv_trans: "trans (opaodv i) = oseqp_sos \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i"
  by simp

declare
  oseq_invariant_ctermsI [OF aodv_wf oaodv_control_within aodv_simple_labels oaodv_trans, cterms_intros]
  oseq_step_invariant_ctermsI [OF aodv_wf oaodv_control_within aodv_simple_labels oaodv_trans, cterms_intros]

end

