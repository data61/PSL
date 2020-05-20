(*  Title:       Closed.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Lemmas for closed networks"

theory Closed
imports Pnet
begin

lemma complete_net_preserves_subnets:
  assumes "(SubnetS s t, a, st') \<in> cnet_sos (pnet_sos (trans (pnet np p1)) (trans (pnet np p2)))"
    shows "\<exists>s' t'. st' = SubnetS s' t'"
  using assms by cases (auto dest: partial_net_preserves_subnets)

lemma complete_net_reachable_is_subnet:
  assumes "st \<in> reachable (closed (pnet np (p1 \<parallel> p2))) I"
    shows "\<exists>s t. st = SubnetS s t"
  using assms by induction (auto dest!: complete_net_preserves_subnets)

lemma closed_reachable_par_subnet_induct [consumes, case_names init step]:
  assumes "SubnetS s t \<in> reachable (closed (pnet np (p1 \<parallel> p2))) I"
      and init: "\<And>s t. SubnetS s t \<in> init (closed (pnet np (p1 \<parallel> p2))) \<Longrightarrow> P s t"
      and step: "\<And>s t s' t' a. \<lbrakk>
                    SubnetS s t \<in> reachable (closed (pnet np (p1 \<parallel> p2))) I;
                    P s t; (SubnetS s t, a, SubnetS s' t') \<in> trans (closed (pnet np (p1 \<parallel> p2))); I a \<rbrakk>
                    \<Longrightarrow> P s' t'"
    shows "P s t"
  using assms(1) proof (induction "SubnetS s t" arbitrary: s t)
    fix s t
    assume "SubnetS s t \<in> init (closed (pnet np (p1 \<parallel> p2)))"
    with init show "P s t" .
  next
    fix st a s' t'
    assume "st \<in> reachable (closed (pnet np (p1 \<parallel> p2))) I"
       and tr: "(st, a, SubnetS s' t') \<in> trans (closed (pnet np (p1 \<parallel> p2)))"
       and "I a"
       and IH: "\<And>s t. st = SubnetS s t \<Longrightarrow> P s t"
    from this(1) obtain s t where "st = SubnetS s t"
                              and "SubnetS s t \<in> reachable (closed (pnet np (p1 \<parallel> p2))) I"
      by (metis complete_net_reachable_is_subnet)
    note this(2)
    moreover from IH and \<open>st = SubnetS s t\<close> have "P s t" .
    moreover from tr and \<open>st = SubnetS s t\<close>
      have "(SubnetS s t, a, SubnetS s' t') \<in> trans (closed (pnet np (p1 \<parallel> p2)))" by simp
    ultimately show "P s' t'"
      using \<open>I a\<close> by (rule assms(3))
  qed

lemma reachable_closed_reachable_pnet [elim]:
  assumes "s \<in> reachable (closed (pnet np n)) TT"
    shows "s \<in> reachable (pnet np n) TT"
  using assms proof (induction rule: reachable.induct)
    fix s s' a
    assume sr: "s \<in> reachable (pnet np n) TT"
       and "(s, a, s') \<in> trans (closed (pnet np n))"
    from this(2) have "(s, a, s') \<in> cnet_sos (trans (pnet np n))" by simp
    thus "s' \<in> reachable (pnet np n) TT"
      by cases (insert sr, auto elim!: reachable_step)
  qed (auto elim: reachable_init)

lemma closed_node_net_state [elim]:
  assumes "st \<in> reachable (closed (pnet np \<langle>ii; R\<^sub>i\<rangle>)) TT"
  obtains \<xi> p q R where "st = NodeS ii ((\<xi>, p), q) R"
  using assms by (metis net_node_reachable_is_node reachable_closed_reachable_pnet surj_pair)

lemma closed_subnet_net_state [elim]:
  assumes "st \<in> reachable (closed (pnet np (p1 \<parallel> p2))) TT"
  obtains s t where "st = SubnetS s t"
  using assms by (metis reachable_closed_reachable_pnet net_par_reachable_is_subnet)

lemma closed_imp_pnet_trans [elim, dest]:
  assumes "(s, a, s') \<in> trans (closed (pnet np n))"
    shows "\<exists>a'. (s, a', s') \<in> trans (pnet np n)"
  using assms by (auto elim!: cnet_sos.cases)

lemma reachable_not_in_net_tree_ips [elim]:
  assumes "s \<in> reachable (closed (pnet np n)) TT"
      and "i\<notin>net_tree_ips n"
    shows "netmap s i = None"
  using assms proof induction
    fix s
    assume "s \<in> init (closed (pnet np n))"
       and "i \<notin> net_tree_ips n"
    thus "netmap s i = None"                                     
    proof (induction n arbitrary: s)
      fix ii R s
      assume "s \<in> init (closed (pnet np \<langle>ii; R\<rangle>))"
         and "i \<notin> net_tree_ips \<langle>ii; R\<rangle>"
      from this(2) have "i \<noteq> ii" by simp
      moreover from \<open>s \<in> init (closed (pnet np \<langle>ii; R\<rangle>))\<close> obtain p where "s = NodeS ii p R"
        by simp (metis pnet.simps(1) pnet_node_init')
      ultimately show "netmap s i = None" by simp
    next
      fix p1 p2 s
      assume IH1: "\<And>s. s \<in> init (closed (pnet np p1)) \<Longrightarrow> i \<notin> net_tree_ips p1
                        \<Longrightarrow> netmap s i = None"
         and IH2: "\<And>s. s \<in> init (closed (pnet np p2)) \<Longrightarrow> i \<notin> net_tree_ips p2
                        \<Longrightarrow> netmap s i = None"
         and "s \<in> init (closed (pnet np (p1 \<parallel> p2)))"
         and "i \<notin> net_tree_ips (p1 \<parallel> p2)"
      from this(3) obtain s1 s2 where "s = SubnetS s1 s2"
                                  and "s1 \<in> init (closed (pnet np p1))"
                                  and "s2 \<in> init (closed (pnet np p2))" by simp metis
      moreover from \<open>i \<notin> net_tree_ips (p1 \<parallel> p2)\<close> have "i \<notin> net_tree_ips p1"
                                                  and "i \<notin> net_tree_ips p2" by auto
      ultimately have "netmap s1 i = None"
                  and "netmap s2 i = None"
        using IH1 IH2 by auto
      with \<open>s = SubnetS s1 s2\<close> show "netmap s i = None" by simp
    qed
  next
    fix s a s'
    assume sr: "s \<in> reachable (closed (pnet np n)) TT"
       and tr: "(s, a, s') \<in> trans (closed (pnet np n))"
       and IH: "i \<notin> net_tree_ips n \<Longrightarrow> netmap s i = None"
       and "i \<notin> net_tree_ips n"
    from this(3-4) have "i\<notin>net_ips s" by auto
    with tr have "i\<notin>net_ips s'"
      by simp (erule cnet_sos.cases, (metis net_ips_is_dom_netmap pnet_maintains_dom)+)
    thus "netmap s' i = None" by simp
  qed

lemma closed_pnet_aodv_init [elim]:
  assumes "s \<in> init (closed (pnet np n))"
      and "i\<in>net_tree_ips n"
    shows "the (netmap s i) \<in> init (np i)"
  using assms proof (induction n arbitrary: s)
    fix ii R s
    assume "s \<in> init (closed (pnet np \<langle>ii; R\<rangle>))"
       and "i\<in>net_tree_ips \<langle>ii; R\<rangle>"
    hence "s \<in> init (pnet np \<langle>i; R\<rangle>)" by simp
    then obtain p where "s = NodeS i p R"
                    and "p \<in> init (np i)" ..
    with \<open>s = NodeS i p R\<close> have "netmap s = [i \<mapsto> p]" by simp
    with \<open>p \<in> init (np i)\<close> show "the (netmap s i) \<in> init (np i)" by simp
  next
    fix p1 p2 s
    assume IH1: "\<And>s. s \<in> init (closed (pnet np p1)) \<Longrightarrow>
                      i\<in>net_tree_ips p1 \<Longrightarrow> the (netmap s i) \<in> init (np i)"
       and IH2: "\<And>s. s \<in> init (closed (pnet np p2)) \<Longrightarrow>
                     i\<in>net_tree_ips p2 \<Longrightarrow> the (netmap s i) \<in> init (np i)"
       and "s \<in> init (closed (pnet np (p1 \<parallel> p2)))"
       and "i\<in>net_tree_ips (p1 \<parallel> p2)"
    from this(3) obtain s1 s2 where "s = SubnetS s1 s2"
                                and "s1 \<in> init (closed (pnet np p1))"
                                and "s2 \<in> init (closed (pnet np p2))"
      by auto
    from this(2) have "net_tree_ips p1 = net_ips s1"
      by (clarsimp dest!: pnet_init_net_ips_net_tree_ips)
    from \<open>s2 \<in> init (closed (pnet np p2))\<close> have "net_tree_ips p2 = net_ips s2"
      by (clarsimp dest!: pnet_init_net_ips_net_tree_ips)
    show "the (netmap s i) \<in> init (np i)"
    proof (cases "i\<in>net_tree_ips p2")
      assume "i\<in>net_tree_ips p2"
      with \<open>s2 \<in> init (closed (pnet np p2))\<close> have "the (netmap s2 i) \<in> init (np i)"
        by (rule IH2)
      moreover from \<open>i\<in>net_tree_ips p2\<close> and \<open>net_tree_ips p2 = net_ips s2\<close>
        have "i\<in>net_ips s2" by simp
      ultimately show ?thesis
        using \<open>s = SubnetS s1 s2\<close> by (auto simp add: net_ips_is_dom_netmap)
    next
      assume "i\<notin>net_tree_ips p2"
      with \<open>i\<in>net_tree_ips (p1 \<parallel> p2)\<close> have "i\<in>net_tree_ips p1" by simp
      with \<open>s1 \<in> init (closed (pnet np p1))\<close> have "the (netmap s1 i) \<in> init (np i)"
        by (rule IH1)
      moreover from \<open>i\<in>net_tree_ips p1\<close> and \<open>net_tree_ips p1 = net_ips s1\<close>
        have "i\<in>net_ips s1" by simp
      moreover from \<open>i\<notin>net_tree_ips p2\<close> and \<open>net_tree_ips p2 = net_ips s2\<close>
        have "i\<notin>net_ips s2" by simp
      ultimately show ?thesis
        using \<open>s = SubnetS s1 s2\<close>
        by (simp add: map_add_dom_app_simps net_ips_is_dom_netmap)
    qed
  qed

end

