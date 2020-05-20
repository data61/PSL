(*  Title:       AWN_SOS_Labels.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Configure the inv-cterms tactic for sequential processes"

theory AWN_SOS_Labels
imports AWN_SOS Inv_Cterms
begin

lemma elimder_guard:
  assumes "p = {l}\<langle>fg\<rangle> qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
  obtains p' where "p = {l}\<langle>fg\<rangle> p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemma elimder_assign:
  assumes "p = {l}\<lbrakk>fa\<rbrakk> qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
  obtains p' where "p = {l}\<lbrakk>fa\<rbrakk> p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemma elimder_ucast:
  assumes "p = {l}unicast(fip, fmsg).q1 \<triangleright> q2"
      and "l' \<in> labels \<Gamma> q"
      and "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
  obtains p' pp' where "p = {l}unicast(fip, fmsg).p' \<triangleright> pp'"
                   and "case a of unicast _ _ \<Rightarrow> l' \<in> labels \<Gamma> q1
                                        | _ \<Rightarrow> l' \<in> labels \<Gamma> q2"
  using assms by simp (erule seqpTEs, auto)

lemma elimder_bcast:
  assumes "p = {l}broadcast(fmsg).qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
  obtains p' where "p = {l}broadcast(fmsg). p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemma elimder_gcast:
  assumes "p = {l}groupcast(fips, fmsg).qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
  obtains p' where "p = {l}groupcast(fips, fmsg). p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemma elimder_send:
  assumes "p = {l}send(fmsg).qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
  obtains p' where "p = {l}send(fmsg). p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemma elimder_deliver:
  assumes "p = {l}deliver(fdata).qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
  obtains p' where "p = {l}deliver(fdata).p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemma elimder_receive:
  assumes "p = {l}receive(fmsg).qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
  obtains p' where "p = {l}receive(fmsg).p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemmas elimders = 
   elimder_guard
   elimder_assign
   elimder_ucast
   elimder_bcast
   elimder_gcast
   elimder_send
   elimder_deliver
   elimder_receive

declare
  seqpTEs [cterms_seqte]
  elimders [cterms_elimders]

end
