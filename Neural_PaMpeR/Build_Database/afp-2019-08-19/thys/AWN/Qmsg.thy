(*  Title:       Qmsg.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Model the standard queuing model"

theory Qmsg
imports AWN_SOS_Labels AWN_Invariants
begin

text \<open>Define the queue process\<close>

fun \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G :: "('m list, 'm, unit, unit label) seqp_env"
where
  "\<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G () = labelled () (receive(\<lambda>msg msgs. msgs @ [msg]). call(())
           \<oplus> \<langle>msgs. msgs \<noteq> []\<rangle>
               (send(\<lambda>msgs. hd msgs).
                 (\<lbrakk>msgs. tl msgs\<rbrakk> call(())
                  \<oplus> receive(\<lambda>msg msgs. tl msgs @ [msg]). call(()))
              \<oplus> receive(\<lambda>msg msgs. msgs @ [msg]). call(())))"

definition \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G :: "(('m::msg) list \<times> ('m list, 'm, unit, unit label) seqp) set"
where "\<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G \<equiv> {([], \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G ())}"

abbreviation qmsg
  :: "(('m::msg) list \<times> ('m list, 'm, unit, unit label) seqp, 'm seq_action) automaton"
where
  "qmsg \<equiv> \<lparr> init = \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G, trans = seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G \<rparr>"

declare \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G.simps [simp del, code del]
lemmas \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_simps [simp, code] = \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G.simps [simplified]

lemma \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_not_empty [simp, intro]: "\<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G \<noteq> {}"
  unfolding \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_def by simp

lemma \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_exists [simp]: "\<exists>qmsg q. (qmsg, q) \<in> \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G"
  unfolding \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_def by simp

lemma qmsg_wf [simp]: "wellformed \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G"
  by (rule wf_no_direct_calls) auto

lemmas qmsg_labels_not_empty [simp] = labels_not_empty [OF qmsg_wf]

lemma qmsg_control_within [simp]: "control_within \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G (init qmsg)"
  unfolding \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_def by (rule control_withinI) (auto simp del: \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_simps)

lemma qmsg_simple_labels [simp]: "simple_labels \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G"
  unfolding simple_labels_def by auto

lemma qmsg_trans: "trans qmsg = seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G"
  by simp

lemma \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_labels [simp]: "(\<xi>, q) \<in> \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G \<Longrightarrow>  labels \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G q = {()-:0}"
  unfolding \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_def by simp

lemma qmsg_proc_cases [dest]:
  fixes p pn
  shows "p \<in> ctermsl (\<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G pn) \<Longrightarrow> p \<in> ctermsl (\<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G ())"
  by simp

declare
  \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_simps [cterms_env]
  qmsg_proc_cases [ctermsl_cases]
  seq_invariant_ctermsI [OF qmsg_wf qmsg_control_within qmsg_simple_labels qmsg_trans, cterms_intros]
  seq_step_invariant_ctermsI [OF qmsg_wf qmsg_control_within qmsg_simple_labels qmsg_trans, cterms_intros]

end
