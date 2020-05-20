(*  Title:       OAWN_SOS_Labels.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Configure the inv-cterms tactic for open sequential processes"

theory OAWN_SOS_Labels
imports OAWN_SOS Inv_Cterms
begin

lemma oelimder_guard:
  assumes "p = {l}\<langle>fg\<rangle> qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
  obtains p' where "p = {l}\<langle>fg\<rangle> p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemma oelimder_assign:
  assumes "p = {l}\<lbrakk>fa\<rbrakk> qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
  obtains p' where "p = {l}\<lbrakk>fa\<rbrakk> p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemma oelimder_ucast:
  assumes "p = {l}unicast(fip, fmsg).q1 \<triangleright> q2"
      and "l' \<in> labels \<Gamma> q"
      and "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
  obtains p' pp' where "p = {l}unicast(fip, fmsg).p' \<triangleright> pp'"
                   and "case a of unicast _ _ \<Rightarrow> l' \<in> labels \<Gamma> q1
                                        | _ \<Rightarrow> l' \<in> labels \<Gamma> q2"
  using assms by simp (erule oseqpTEs, auto)

lemma oelimder_bcast:
  assumes "p = {l}broadcast(fmsg).qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
  obtains p' where "p = {l}broadcast(fmsg). p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemma oelimder_gcast:
  assumes "p = {l}groupcast(fips, fmsg).qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
  obtains p' where "p = {l}groupcast(fips, fmsg). p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemma oelimder_send:
  assumes "p = {l}send(fmsg).qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
  obtains p' where "p = {l}send(fmsg). p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemma oelimder_deliver:
  assumes "p = {l}deliver(fdata).qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
  obtains p' where "p = {l}deliver(fdata).p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemma oelimder_receive:
  assumes "p = {l}receive(fmsg).qq"
      and "l' \<in> labels \<Gamma> q"
      and "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
  obtains p' where "p = {l}receive(fmsg).p'"
               and "l' \<in> labels \<Gamma> qq"
  using assms by auto

lemmas oelimders =
   oelimder_guard
   oelimder_assign
   oelimder_ucast
   oelimder_bcast
   oelimder_gcast
   oelimder_send
   oelimder_deliver
   oelimder_receive

declare
  oseqpTEs [cterms_seqte]
  oelimders [cterms_elimders]

end
