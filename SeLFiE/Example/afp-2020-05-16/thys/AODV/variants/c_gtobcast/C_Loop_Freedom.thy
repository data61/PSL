(*  Title:       aodvmech/aodv/Loop_Freedom.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
    Author:      Peter Höfner, NICTA
*)

section "Routing graphs and loop freedom"

theory C_Loop_Freedom
imports C_Aodv_Predicates C_Fresher
begin

text \<open>Define the central theorem that relates an invariant over network states to the absence
      of loops in the associate routing graph.\<close>

definition
  rt_graph :: "(ip \<Rightarrow> state) \<Rightarrow> ip \<Rightarrow> ip rel"
where
  "rt_graph \<sigma> = (\<lambda>dip.
     {(ip, ip') | ip ip' dsn dsk hops.
        ip \<noteq> dip \<and> rt (\<sigma> ip) dip = Some (dsn, dsk, val, hops, ip')})"

text \<open>Given the state of a network @{term \<sigma>}, a routing graph for a given destination
      ip address @{term dip} abstracts the details of routing tables into nodes
      (ip addresses) and vertices (valid routes between ip addresses).\<close>

lemma rt_graphE [elim]:
    fixes n dip ip ip'
  assumes "(ip, ip') \<in> rt_graph \<sigma> dip"
    shows "ip \<noteq> dip \<and> (\<exists>r. rt (\<sigma> ip) = r
                            \<and> (\<exists>dsn dsk hops. r dip = Some (dsn, dsk, val, hops, ip')))"
  using assms unfolding rt_graph_def by auto

lemma rt_graph_vD [dest]:
  "\<And>ip ip' \<sigma> dip. (ip, ip') \<in> rt_graph \<sigma> dip \<Longrightarrow> dip \<in> vD(rt (\<sigma> ip))"
  unfolding rt_graph_def vD_def by auto

lemma rt_graph_vD_trans [dest]:
  "\<And>ip ip' \<sigma> dip. (ip, ip') \<in> (rt_graph \<sigma> dip)\<^sup>+ \<Longrightarrow> dip \<in> vD(rt (\<sigma> ip))"
  by (erule converse_tranclE) auto

lemma rt_graph_not_dip [dest]:
  "\<And>ip ip' \<sigma> dip. (ip, ip') \<in> rt_graph \<sigma> dip \<Longrightarrow> ip \<noteq> dip"
  unfolding rt_graph_def by auto

lemma rt_graph_not_dip_trans [dest]:
  "\<And>ip ip' \<sigma> dip. (ip, ip') \<in> (rt_graph \<sigma> dip)\<^sup>+ \<Longrightarrow> ip \<noteq> dip"
  by (erule converse_tranclE) auto

text "NB: the property below cannot be lifted to the transitive closure"

lemma rt_graph_nhip_is_nhop [dest]:
  "\<And>ip ip' \<sigma> dip. (ip, ip') \<in> rt_graph \<sigma> dip \<Longrightarrow> ip' = the (nhop (rt (\<sigma> ip)) dip)"
  unfolding rt_graph_def by auto

theorem inv_to_loop_freedom:
  assumes "\<forall>i dip. let nhip = the (nhop (rt (\<sigma> i)) dip)
                   in dip \<in> vD (rt (\<sigma> i)) \<inter> vD (rt (\<sigma> nhip)) \<and> nhip \<noteq> dip
                      \<longrightarrow> (rt (\<sigma> i)) \<sqsubset>\<^bsub>dip\<^esub> (rt (\<sigma> nhip))"
    shows "\<forall>dip. irrefl ((rt_graph \<sigma> dip)\<^sup>+)"
  using assms proof (intro allI)
    fix \<sigma> :: "ip \<Rightarrow> state" and dip
    assume inv: "\<forall>ip dip.
                  let nhip = the (nhop (rt (\<sigma> ip)) dip)
                  in dip \<in> vD(rt (\<sigma> ip)) \<inter> vD(rt (\<sigma> nhip)) \<and>
                     nhip \<noteq> dip \<longrightarrow> rt (\<sigma> ip) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> nhip)"
    { fix ip ip'
      assume "(ip, ip') \<in> (rt_graph \<sigma> dip)\<^sup>+"
         and "dip \<in> vD(rt (\<sigma> ip'))"
         and "ip' \<noteq> dip"
       hence "rt (\<sigma> ip) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> ip')"
         proof induction
           fix nhip
           assume "(ip, nhip) \<in> rt_graph \<sigma> dip"
              and "dip \<in> vD(rt (\<sigma> nhip))"
              and "nhip \<noteq> dip"
           from \<open>(ip, nhip) \<in> rt_graph \<sigma> dip\<close> have "dip \<in> vD(rt (\<sigma> ip))"
                                               and "nhip = the (nhop (rt (\<sigma> ip)) dip)"
             by auto
           from \<open>dip \<in> vD(rt (\<sigma> ip))\<close> and \<open>dip \<in> vD(rt (\<sigma> nhip))\<close>
             have "dip \<in> vD(rt (\<sigma> ip)) \<inter> vD(rt (\<sigma> nhip))" ..
           with \<open>nhip = the (nhop (rt (\<sigma> ip)) dip)\<close>
                and \<open>nhip \<noteq> dip\<close>
                and inv
             show "rt (\<sigma> ip) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> nhip)"
             by (clarsimp simp: Let_def)
         next
           fix nhip nhip'
           assume "(ip, nhip) \<in> (rt_graph \<sigma> dip)\<^sup>+"
              and "(nhip, nhip') \<in> rt_graph \<sigma> dip"
              and IH: "\<lbrakk> dip \<in> vD(rt (\<sigma> nhip)); nhip \<noteq> dip \<rbrakk> \<Longrightarrow> rt (\<sigma> ip) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> nhip)"
              and "dip \<in> vD(rt (\<sigma> nhip'))"
              and "nhip' \<noteq> dip"
           from \<open>(nhip, nhip') \<in> rt_graph \<sigma> dip\<close> have 1: "dip \<in> vD(rt (\<sigma> nhip))"
                                                  and 2: "nhip \<noteq> dip"
                                                  and "nhip' = the (nhop (rt (\<sigma> nhip)) dip)"
             by auto
           from 1 2 have "rt (\<sigma> ip) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> nhip)" by (rule IH)
           also have "rt (\<sigma> nhip) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> nhip')"
             proof -
               from \<open>dip \<in> vD(rt (\<sigma> nhip))\<close> and \<open>dip \<in> vD(rt (\<sigma> nhip'))\<close>
                 have "dip \<in> vD(rt (\<sigma> nhip)) \<inter> vD(rt (\<sigma> nhip'))" ..
               with \<open>nhip' \<noteq> dip\<close>
                    and \<open>nhip' = the (nhop (rt (\<sigma> nhip)) dip)\<close>
                    and inv
                 show "rt (\<sigma> nhip) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> nhip')"
                   by (clarsimp simp: Let_def)
             qed
           finally show "rt (\<sigma> ip) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> nhip')" .
         qed } note fresher = this

    show "irrefl ((rt_graph \<sigma> dip)\<^sup>+)"
    unfolding irrefl_def proof (intro allI notI)
      fix ip
      assume "(ip, ip) \<in> (rt_graph \<sigma> dip)\<^sup>+"
      moreover then have "dip \<in> vD(rt (\<sigma> ip))"
                     and "ip \<noteq> dip"
        by auto
      ultimately have "rt (\<sigma> ip) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> ip)" by (rule fresher)
      thus False by simp
    qed
  qed

end
