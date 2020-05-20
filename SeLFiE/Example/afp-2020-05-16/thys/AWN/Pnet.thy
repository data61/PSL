(*  Title:       Pnet.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Lemmas for partial networks"

theory Pnet
imports AWN_SOS Invariants
begin

text \<open>
  These lemmas mostly concern the preservation of node structure by @{term pnet_sos} transitions.
\<close>

lemma pnet_maintains_dom:
  assumes "(s, a, s') \<in> trans (pnet np p)"
    shows "net_ips s = net_ips s'"
  using assms proof (induction p arbitrary: s a s')
    fix i R \<sigma> s a s'
    assume "(s, a, s') \<in> trans (pnet np \<langle>i; R\<rangle>)"
    hence "(s, a, s') \<in> node_sos (trans (np i))" ..
    thus "net_ips s = net_ips s'"
      by (rule node_sos.cases) simp_all
  next
    fix p1 p2 s a s'
    assume "\<And>s a s'. (s, a, s') \<in> trans (pnet np p1) \<Longrightarrow> net_ips s = net_ips s'"
       and "\<And>s a s'. (s, a, s') \<in> trans (pnet np p2) \<Longrightarrow> net_ips s = net_ips s'"
       and "(s, a, s') \<in> trans (pnet np (p1 \<parallel> p2))"
    thus "net_ips s = net_ips s'"
      by simp (erule pnet_sos.cases, simp_all)
  qed

lemma pnet_net_ips_net_tree_ips [elim]:
  assumes "s \<in> reachable (pnet np p) I"
    shows "net_ips s = net_tree_ips p"
  using assms proof induction
    fix s
    assume "s \<in> init (pnet np p)"
    thus "net_ips s = net_tree_ips p"
    proof (induction p arbitrary: s)
      fix i R s
      assume "s \<in> init (pnet np \<langle>i; R\<rangle>)"
      then obtain ns where "s = NodeS i ns R" ..
      thus "net_ips s = net_tree_ips \<langle>i; R\<rangle>"
        by simp
    next
      fix p1 p2 s
      assume IH1: "\<And>s. s \<in> init (pnet np p1) \<Longrightarrow> net_ips s = net_tree_ips p1"
         and IH2: "\<And>s. s \<in> init (pnet np p2) \<Longrightarrow> net_ips s = net_tree_ips p2"
         and "s \<in> init (pnet np (p1 \<parallel> p2))"
      from this(3) obtain s1 s2 where "s1 \<in> init (pnet np p1)"
                                  and "s2 \<in> init (pnet np p2)"
                                  and "s = SubnetS s1 s2" by auto
      from this(1-2) have "net_ips s1 = net_tree_ips p1"
                      and "net_ips s2 = net_tree_ips p2"
        using IH1 IH2 by auto
      with \<open>s = SubnetS s1 s2\<close> show "net_ips s = net_tree_ips (p1 \<parallel> p2)" by auto
    qed
  next
    fix s a s'
    assume "(s, a, s') \<in> trans (pnet np p)"
       and "net_ips s = net_tree_ips p"
    from this(1) have "net_ips s = net_ips s'"
      by (rule pnet_maintains_dom)
    with \<open>net_ips s = net_tree_ips p\<close> show "net_ips s' = net_tree_ips p"
      by simp
  qed

lemma pnet_init_net_ips_net_tree_ips:
  assumes "s \<in> init (pnet np p)"
    shows "net_ips s = net_tree_ips p"
  using assms(1) by (rule reachable_init [THEN pnet_net_ips_net_tree_ips])

lemma pnet_init_in_net_ips_in_net_tree_ips [elim]:
  assumes "s \<in> init (pnet np p)"
      and "i \<in> net_ips s"
    shows "i \<in> net_tree_ips p"
  using assms by (clarsimp dest!: pnet_init_net_ips_net_tree_ips)

lemma pnet_init_in_net_tree_ips_in_net_ips [elim]:
  assumes "s \<in> init (pnet np p)"
      and "i \<in> net_tree_ips p"
    shows "i \<in> net_ips s"
  using assms by (clarsimp dest!: pnet_init_net_ips_net_tree_ips)

lemma pnet_init_not_in_net_tree_ips_not_in_net_ips [elim]:
  assumes "s \<in> init (pnet np p)"
      and "i \<notin> net_tree_ips p"
    shows "i \<notin> net_ips s"
  proof
    assume "i \<in> net_ips s"
    with assms(1) have "i \<in> net_tree_ips p" ..
    with assms(2) show False ..
  qed

lemma net_node_reachable_is_node:
  assumes "st \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) I"
    shows "\<exists>ns R. st = NodeS ii ns R"
  using assms proof induct
    fix s
    assume "s \<in> init (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
    thus "\<exists>ns R. s = NodeS ii ns R"
      by (rule pnet_node_init') simp
  next
    fix s a s'
    assume "s \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) I"
       and "\<exists>ns R. s = NodeS ii ns R"
       and "(s, a, s') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
       and "I a"
    thus "\<exists>ns R. s' = NodeS ii ns R"
      by (auto simp add: trans_node_comp dest!: node_sos_dest)
  qed

lemma partial_net_preserves_subnets:
  assumes "(SubnetS s t, a, st') \<in> pnet_sos (trans (pnet np p1)) (trans (pnet np p2))"
    shows "\<exists>s' t'. st' = SubnetS s' t'"
  using assms by cases simp_all

lemma net_par_reachable_is_subnet:
  assumes "st \<in> reachable (pnet np (p1 \<parallel> p2)) I"
    shows "\<exists>s t. st = SubnetS s t"
  using assms by induct (auto dest!: partial_net_preserves_subnets)

lemma reachable_par_subnet_induct [consumes, case_names init step]:
  assumes "SubnetS s t \<in> reachable (pnet np (p1 \<parallel> p2)) I"
      and init: "\<And>s t. SubnetS s t \<in> init (pnet np (p1 \<parallel> p2)) \<Longrightarrow> P s t"
      and step: "\<And>s t s' t' a. \<lbrakk>
                    SubnetS s t \<in> reachable (pnet np (p1 \<parallel> p2)) I;
                    P s t; (SubnetS s t, a, SubnetS s' t') \<in> (trans (pnet np (p1 \<parallel> p2))); I a \<rbrakk>
                    \<Longrightarrow> P s' t'"
    shows "P s t"
  using assms(1) proof (induction "SubnetS s t" arbitrary: s t)
    fix s t
    assume "SubnetS s t \<in> init (pnet np (p1 \<parallel> p2))"
    with init show "P s t" .
  next
    fix st a s' t'
    assume "st \<in> reachable (pnet np (p1 \<parallel> p2)) I"
       and tr: "(st, a, SubnetS s' t') \<in> trans (pnet np (p1 \<parallel> p2))"
       and "I a"
       and IH: "\<And>s t. st = SubnetS s t \<Longrightarrow> P s t"
    from this(1) obtain s t where "st = SubnetS s t"
                              and str: "SubnetS s t \<in> reachable (pnet np (p1 \<parallel> p2)) I"
      by (metis net_par_reachable_is_subnet)
    note this(2)
    moreover from IH and \<open>st = SubnetS s t\<close> have "P s t" .
    moreover from \<open>st = SubnetS s t\<close> and tr
      have "(SubnetS s t, a, SubnetS s' t') \<in> trans (pnet np (p1 \<parallel> p2))" by simp
    ultimately show "P s' t'"
      using \<open>I a\<close> by (rule step)
  qed

lemma subnet_reachable:
  assumes "SubnetS s1 s2 \<in> reachable (pnet np (p1 \<parallel> p2)) TT"
    shows "s1 \<in> reachable (pnet np p1) TT"
          "s2 \<in> reachable (pnet np p2) TT"
  proof -
    from assms have "s1 \<in> reachable (pnet np p1) TT
                  \<and> s2 \<in> reachable (pnet np p2) TT"
    proof (induction rule: reachable_par_subnet_induct)
      fix s1 s2
      assume "SubnetS s1 s2 \<in> init (pnet np (p1 \<parallel> p2))"
      thus "s1 \<in> reachable (pnet np p1) TT
          \<and> s2 \<in> reachable (pnet np p2) TT"
        by (auto dest: reachable_init)
    next
      case (step s1 s2 s1' s2' a)
      hence "SubnetS s1 s2 \<in> reachable (pnet np (p1 \<parallel> p2)) TT"
        and sr1: "s1 \<in> reachable (pnet np p1) TT"
        and sr2: "s2 \<in> reachable (pnet np p2) TT"
        and "(SubnetS s1 s2, a, SubnetS s1' s2') \<in> trans (pnet np (p1 \<parallel> p2))" by auto
      from this(4)
        have "(SubnetS s1 s2, a, SubnetS s1' s2') \<in> pnet_sos (trans (pnet np p1)) (trans (pnet np p2))"
          by simp
      thus "s1' \<in> reachable (pnet np p1) TT
         \<and> s2' \<in> reachable (pnet np p2) TT"
        by cases (insert sr1 sr2, auto elim: reachable_step)
    qed
    thus "s1 \<in> reachable (pnet np p1) TT"
         "s2 \<in> reachable (pnet np p2) TT" by auto
  qed

lemma delivered_to_node [elim]:
  assumes "s \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
      and "(s, i:deliver(d), s') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
    shows "i = ii"
  proof -
    from assms(1) obtain P R where "s = NodeS ii P R"
      by (metis net_node_reachable_is_node)
    with assms(2) show "i = ii"
       by (clarsimp simp add: trans_node_comp elim!: node_deliverTE')
  qed

lemma delivered_to_net_ips:
  assumes "s \<in> reachable (pnet np p) TT"
      and "(s, i:deliver(d), s') \<in> trans (pnet np p)"
    shows "i \<in> net_ips s"
  using assms proof (induction p arbitrary: s s')
    fix ii R\<^sub>i s s'
    assume sr: "s \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
       and "(s, i:deliver(d), s') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
    from this(2) have tr: "(s, i:deliver(d), s') \<in> node_sos (trans (np ii))" by simp
    from sr obtain P R where [simp]: "s = NodeS ii P R"
      by (metis net_node_reachable_is_node)
    moreover from tr obtain P' R' where [simp]: "s' = NodeS ii P' R'"
      by simp (metis node_sos_dest)
    ultimately have "i = ii" using tr by auto
    thus "i \<in> net_ips s" by simp
  next
    fix p1 p2 s s'
    assume IH1: "\<And>s s'. \<lbrakk> s \<in> reachable (pnet np p1) TT;
                          (s, i:deliver(d), s') \<in> trans (pnet np p1) \<rbrakk> \<Longrightarrow> i \<in> net_ips s"
       and IH2: "\<And>s s'. \<lbrakk> s \<in> reachable (pnet np p2) TT;
                          (s, i:deliver(d), s') \<in> trans (pnet np p2) \<rbrakk> \<Longrightarrow> i \<in> net_ips s"
       and sr: "s \<in> reachable (pnet np (p1 \<parallel> p2)) TT"
       and tr: "(s, i:deliver(d), s') \<in> trans (pnet np (p1 \<parallel> p2))"
    from tr have "(s, i:deliver(d), s') \<in> pnet_sos (trans (pnet np p1)) (trans (pnet np p2))"
      by simp
    thus "i \<in> net_ips s"
    proof (rule partial_deliverTE)
      fix s1 s1' s2
      assume "s = SubnetS s1 s2"
         and "s' = SubnetS s1' s2"
         and tr: "(s1, i:deliver(d), s1') \<in> trans (pnet np p1)"
      from sr have "s1 \<in> reachable (pnet np p1) TT"
        by (auto simp only: \<open>s = SubnetS s1 s2\<close> elim: subnet_reachable)
      hence "i \<in> net_ips s1" using tr by (rule IH1)
      thus "i \<in> net_ips s" by (simp add: \<open>s = SubnetS s1 s2\<close>)
    next
      fix s2 s2' s1
      assume "s = SubnetS s1 s2"
         and "s' = SubnetS s1 s2'"
         and tr: "(s2, i:deliver(d), s2') \<in> trans (pnet np p2)"
      from sr have "s2 \<in> reachable (pnet np p2) TT"
        by (auto simp only: \<open>s = SubnetS s1 s2\<close> elim: subnet_reachable)
      hence "i \<in> net_ips s2" using tr by (rule IH2)
      thus "i \<in> net_ips s" by (simp add: \<open>s = SubnetS s1 s2\<close>)
    qed
  qed

lemma wf_net_tree_net_ips_disjoint [elim]:
  assumes "wf_net_tree (p1 \<parallel> p2)"
      and "s1 \<in> reachable (pnet np p1) S"
      and "s2 \<in> reachable (pnet np p2) S"
    shows "net_ips s1 \<inter> net_ips s2 = {}"
  proof -
    from \<open>wf_net_tree (p1 \<parallel> p2)\<close> have "net_tree_ips p1 \<inter> net_tree_ips p2 = {}" by auto
    moreover from assms(2) have "net_ips s1 = net_tree_ips p1" ..
    moreover from assms(3) have "net_ips s2 = net_tree_ips p2" ..
    ultimately show ?thesis by simp
  qed

lemma init_mapstate_Some_aodv_init [elim]:
  assumes "s \<in> init (pnet np p)"
      and "netmap s i = Some v"
    shows "v \<in> init (np i)"
  using assms proof (induction p arbitrary: s)
    fix ii R s
    assume "s \<in> init (pnet np \<langle>ii; R\<rangle>)"
       and "netmap s i = Some v"
    from this(1) obtain ns where s: "s = NodeS ii ns R"
      and ns: "ns \<in> init (np ii)" ..
    from s and \<open>netmap s i = Some v\<close> have "i = ii"
      by simp (metis domI domIff)
    with s ns show "v \<in> init (np i)"
      using \<open>netmap s i = Some v\<close> by simp
  next
    fix p1 p2 s
    assume IH1: "\<And>s. s \<in> init (pnet np p1) \<Longrightarrow> netmap s i = Some v \<Longrightarrow> v \<in> init (np i)"
       and IH2: "\<And>s. s \<in> init (pnet np p2) \<Longrightarrow> netmap s i = Some v \<Longrightarrow> v \<in> init (np i)"
       and "s \<in> init (pnet np (p1 \<parallel> p2))"
       and "netmap s i = Some v"
    from this(3) obtain s1 s2 where "s = SubnetS s1 s2"
                                and "s1 \<in> init (pnet np p1)"
                                and "s2 \<in> init (pnet np p2)" by auto
    from this(1) and \<open>netmap s i = Some v\<close>
      have "netmap s1 i = Some v \<or> netmap s2 i = Some v" by auto
    thus "v \<in> init (np i)"
    proof
      assume "netmap s1 i = Some v"
      with \<open>s1 \<in> init (pnet np p1)\<close> show ?thesis by (rule IH1)
    next
      assume "netmap s2 i = Some v"
      with \<open>s2 \<in> init (pnet np p2)\<close> show ?thesis by (rule IH2)
    qed
  qed

lemma reachable_connect_netmap [elim]:
  assumes "s \<in> reachable (pnet np n) TT"
      and "(s, connect(i, i'), s') \<in> trans (pnet np n)"
    shows "netmap s' = netmap s"
  using assms proof (induction n arbitrary: s s')
    fix ii R\<^sub>i s s'
    assume sr: "s \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
       and "(s, connect(i, i'), s') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
    from this(2) have tr: "(s, connect(i, i'), s') \<in> node_sos (trans (np ii))" ..
    from sr obtain p R where "s = NodeS ii p R"
      by (metis net_node_reachable_is_node)
    with tr show "netmap s' = netmap s"
      by (auto elim!: node_sos.cases)
  next
    fix p1 p2 s s'
    assume IH1: "\<And>s s'. \<lbrakk> s \<in> reachable (pnet np p1) TT;
                          (s, connect(i, i'), s') \<in> trans (pnet np p1) \<rbrakk> \<Longrightarrow> netmap s' = netmap s"
       and IH2: "\<And>s s'. \<lbrakk> s \<in> reachable (pnet np p2) TT;
                          (s, connect(i, i'), s') \<in> trans (pnet np p2) \<rbrakk> \<Longrightarrow> netmap s' = netmap s"
       and sr: "s \<in> reachable (pnet np (p1 \<parallel> p2)) TT"
       and tr: "(s, connect(i, i'), s') \<in> trans (pnet np (p1 \<parallel> p2))"
    from tr have "(s, connect(i, i'), s') \<in> pnet_sos (trans (pnet np p1)) (trans (pnet np p2))"
      by simp
    thus "netmap s' = netmap s"
    proof cases
      fix s1 s1' s2 s2'
      assume "s = SubnetS s1 s2"
         and "s' = SubnetS s1' s2'"
         and tr1: "(s1, connect(i, i'), s1') \<in> trans (pnet np p1)"
         and tr2: "(s2, connect(i, i'), s2') \<in> trans (pnet np p2)"
    from this(1) and sr
      have "SubnetS s1 s2 \<in> reachable (pnet np (p1 \<parallel> p2)) TT" by simp
    hence sr1: "s1 \<in> reachable (pnet np p1) TT"
      and sr2: "s2 \<in> reachable (pnet np p2) TT"
      by (auto intro: subnet_reachable)
    from sr1 tr1 have "netmap s1' = netmap s1" by (rule IH1)
    moreover from sr2 tr2 have "netmap s2' = netmap s2" by (rule IH2)
    ultimately show "netmap s' = netmap s"
      using \<open>s = SubnetS s1 s2\<close> and \<open>s' = SubnetS s1' s2'\<close> by simp
    qed simp_all
  qed

lemma reachable_disconnect_netmap [elim]:
  assumes "s \<in> reachable (pnet np n) TT"
      and "(s, disconnect(i, i'), s') \<in> trans (pnet np n)"
    shows "netmap s' = netmap s"
  using assms proof (induction n arbitrary: s s')
    fix ii R\<^sub>i s s'
    assume sr: "s \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
       and "(s, disconnect(i, i'), s') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
    from this(2) have tr: "(s, disconnect(i, i'), s') \<in> node_sos (trans (np ii))" ..
    from sr obtain p R where "s = NodeS ii p R"
      by (metis net_node_reachable_is_node)
    with tr show "netmap s' = netmap s"
      by (auto elim!: node_sos.cases)
  next
    fix p1 p2 s s'
    assume IH1: "\<And>s s'. \<lbrakk> s \<in> reachable (pnet np p1) TT;
                          (s, disconnect(i, i'), s') \<in> trans (pnet np p1) \<rbrakk> \<Longrightarrow> netmap s' = netmap s"
       and IH2: "\<And>s s'. \<lbrakk> s \<in> reachable (pnet np p2) TT;
                          (s, disconnect(i, i'), s') \<in> trans (pnet np p2) \<rbrakk> \<Longrightarrow> netmap s' = netmap s"
       and sr: "s \<in> reachable (pnet np (p1 \<parallel> p2)) TT"
       and tr: "(s, disconnect(i, i'), s') \<in> trans (pnet np (p1 \<parallel> p2))"
    from tr have "(s, disconnect(i, i'), s') \<in> pnet_sos (trans (pnet np p1)) (trans (pnet np p2))"
      by simp
    thus "netmap s' = netmap s"
    proof cases
      fix s1 s1' s2 s2'
      assume "s = SubnetS s1 s2"
         and "s' = SubnetS s1' s2'"
         and tr1: "(s1, disconnect(i, i'), s1') \<in> trans (pnet np p1)"
         and tr2: "(s2, disconnect(i, i'), s2') \<in> trans (pnet np p2)"
    from this(1) and sr
      have "SubnetS s1 s2 \<in> reachable (pnet np (p1 \<parallel> p2)) TT" by simp
    hence sr1: "s1 \<in> reachable (pnet np p1) TT"
      and sr2: "s2 \<in> reachable (pnet np p2) TT"
      by (auto intro: subnet_reachable)
    from sr1 tr1 have "netmap s1' = netmap s1" by (rule IH1)
    moreover from sr2 tr2 have "netmap s2' = netmap s2" by (rule IH2)
    ultimately show "netmap s' = netmap s"
      using \<open>s = SubnetS s1 s2\<close> and \<open>s' = SubnetS s1' s2'\<close> by simp
    qed simp_all
  qed

fun net_ip_action :: "(ip \<Rightarrow> ('s, 'm seq_action) automaton)
                       \<Rightarrow> 'm node_action \<Rightarrow> ip \<Rightarrow> net_tree \<Rightarrow> 's net_state \<Rightarrow> 's net_state \<Rightarrow> bool"
where
    "net_ip_action np a i (p1 \<parallel> p2) (SubnetS s1 s2) (SubnetS s1' s2') =
         ((i \<in> net_ips s1 \<longrightarrow> ((s1, a, s1') \<in> trans (pnet np p1)
                                \<and> s2' = s2 \<and> net_ip_action np a i p1 s1 s1'))
          \<and> (i \<in> net_ips s2 \<longrightarrow> ((s2, a, s2') \<in> trans (pnet np p2))
                                   \<and> s1' = s1 \<and> net_ip_action np a i p2 s2 s2'))"
  | "net_ip_action np a i p s s' = True"

lemma pnet_tau_single_node [elim]:
  assumes "wf_net_tree p"
      and "s \<in> reachable (pnet np p) TT"
      and "(s, \<tau>, s') \<in> trans (pnet np p)"
  shows "\<exists>i\<in>net_ips s. ((\<forall>j. j\<noteq>i \<longrightarrow> netmap s' j = netmap s j)
                         \<and> net_ip_action np \<tau> i p s s')"
  using assms proof (induction p arbitrary: s s')
    fix ii R\<^sub>i s s'
    assume "s \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
       and "(s, \<tau>, s') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
    from this obtain p R p' R' where "s = NodeS ii p R" and "s' = NodeS ii p' R'"
      by (metis (hide_lams, no_types) TT_True net_node_reachable_is_node
                                      reachable_step)
    hence "net_ips s = {ii}"
      and "net_ips s' = {ii}" by simp_all
    hence "\<exists>i\<in>dom (netmap s). \<forall>j. j \<noteq> i \<longrightarrow> netmap s' j = netmap s j"
      by (simp add: net_ips_is_dom_netmap)
    thus "\<exists>i\<in>net_ips s. (\<forall>j. j \<noteq> i \<longrightarrow> netmap s' j = netmap s j)
                         \<and> net_ip_action np \<tau> i (\<langle>ii; R\<^sub>i\<rangle>) s s'"
      by (simp add: net_ips_is_dom_netmap)
  next
    fix p1 p2 s s'
    assume IH1: "\<And>s s'. \<lbrakk> wf_net_tree p1;
                          s \<in> reachable (pnet np p1) TT;
                          (s, \<tau>, s') \<in> trans (pnet np p1) \<rbrakk>
                         \<Longrightarrow> \<exists>i\<in>net_ips s. (\<forall>j. j \<noteq> i \<longrightarrow> netmap s' j = netmap s j)
                                            \<and> net_ip_action np \<tau> i p1 s s'"
       and IH2: "\<And>s s'. \<lbrakk> wf_net_tree p2;
                          s \<in> reachable (pnet np p2) TT;
                          (s, \<tau>, s') \<in> trans (pnet np p2) \<rbrakk>
                         \<Longrightarrow> \<exists>i\<in>net_ips s. (\<forall>j. j \<noteq> i \<longrightarrow> netmap s' j = netmap s j)
                                            \<and> net_ip_action np \<tau> i p2 s s'"
       and sr: "s \<in> reachable (pnet np (p1 \<parallel> p2)) TT"
       and "wf_net_tree (p1 \<parallel> p2)"
       and tr: "(s, \<tau>, s') \<in> trans (pnet np (p1 \<parallel> p2))"
    from \<open>wf_net_tree (p1 \<parallel> p2)\<close> have "net_tree_ips p1 \<inter> net_tree_ips p2 = {}"
                                  and "wf_net_tree p1" 
                                  and "wf_net_tree p2" by auto
    from tr have "(s, \<tau>, s') \<in> pnet_sos (trans (pnet np p1)) (trans (pnet np p2))" by simp
    thus "\<exists>i\<in>net_ips s. (\<forall>j. j \<noteq> i \<longrightarrow> netmap s' j = netmap s j)
                        \<and> net_ip_action np \<tau> i (p1 \<parallel> p2) s s'"
    proof cases
      fix s1 s1' s2
      assume subs:  "s = SubnetS s1 s2"
         and subs': "s' = SubnetS s1' s2"
         and tr1: "(s1, \<tau>, s1') \<in> trans (pnet np p1)"
      from sr have sr1: "s1 \<in> reachable (pnet np p1) TT"
               and "s2 \<in> reachable (pnet np p2) TT"
        by (simp_all only: subs) (erule subnet_reachable)+
      with \<open>net_tree_ips p1 \<inter> net_tree_ips p2 = {}\<close> have "dom(netmap s1) \<inter> dom(netmap s2) = {}"
        by (metis net_ips_is_dom_netmap pnet_net_ips_net_tree_ips)
      from \<open>wf_net_tree p1\<close> sr1 tr1 obtain i where "i\<in>dom(netmap s1)"
                                               and *: "\<forall>j. j \<noteq> i \<longrightarrow> netmap s1' j = netmap s1 j"
                                               and "net_ip_action np \<tau> i p1 s1 s1'"
          by (auto simp add: net_ips_is_dom_netmap dest!: IH1)
      from this(1) and \<open>dom(netmap s1) \<inter> dom(netmap s2) = {}\<close> have "i\<notin>dom(netmap s2)"
        by auto
      with subs subs' tr1 \<open>net_ip_action np \<tau> i p1 s1 s1'\<close> have "net_ip_action np \<tau> i (p1 \<parallel> p2) s s'"
        by (simp add: net_ips_is_dom_netmap)
      moreover have "\<forall>j. j \<noteq> i \<longrightarrow> (netmap s1' ++ netmap s2) j = (netmap s1 ++ netmap s2) j"
      proof (intro allI impI)
        fix j
        assume "j \<noteq> i"
        with * have "netmap s1' j = netmap s1 j" by simp
        thus "(netmap s1' ++ netmap s2) j = (netmap s1 ++ netmap s2) j"
          by (metis (hide_lams, mono_tags) map_add_dom_app_simps(1) map_add_dom_app_simps(3))
      qed
      ultimately show ?thesis using \<open>i\<in>dom(netmap s1)\<close> subs subs'
        by (auto simp add: net_ips_is_dom_netmap)
    next
      fix s2 s2' s1
      assume subs: "s = SubnetS s1 s2"
         and subs': "s' = SubnetS s1 s2'"
         and tr2: "(s2, \<tau>, s2') \<in> trans (pnet np p2)"
      from sr have "s1 \<in> reachable (pnet np p1) TT"
               and sr2: "s2 \<in> reachable (pnet np p2) TT"
        by (simp_all only: subs) (erule subnet_reachable)+
      with \<open>net_tree_ips p1 \<inter> net_tree_ips p2 = {}\<close> have "dom(netmap s1) \<inter> dom(netmap s2) = {}"
        by (metis net_ips_is_dom_netmap pnet_net_ips_net_tree_ips)
      from \<open>wf_net_tree p2\<close> sr2 tr2 obtain i where "i\<in>dom(netmap s2)"
                                               and *: "\<forall>j. j \<noteq> i \<longrightarrow> netmap s2' j = netmap s2 j"
                                               and "net_ip_action np \<tau> i p2 s2 s2'"
          by (auto simp add: net_ips_is_dom_netmap dest!: IH2)
      from this(1) and \<open>dom(netmap s1) \<inter> dom(netmap s2) = {}\<close> have "i\<notin>dom(netmap s1)"
        by auto
      with subs subs' tr2 \<open>net_ip_action np \<tau> i p2 s2 s2'\<close> have "net_ip_action np \<tau> i (p1 \<parallel> p2) s s'"
        by (simp add: net_ips_is_dom_netmap)
      moreover have "\<forall>j. j \<noteq> i \<longrightarrow> (netmap s1 ++ netmap s2') j = (netmap s1 ++ netmap s2) j"
      proof (intro allI impI)
        fix j
        assume "j \<noteq> i"
        with * have "netmap s2' j = netmap s2 j" by simp
        thus "(netmap s1 ++ netmap s2') j = (netmap s1 ++ netmap s2) j"
          by (metis (hide_lams, mono_tags) domD map_add_Some_iff map_add_dom_app_simps(3))
      qed
      ultimately show ?thesis using \<open>i\<in>dom(netmap s2)\<close> subs subs'
        by (clarsimp simp add: net_ips_is_dom_netmap)
           (metis domI dom_map_add map_add_find_right)
    qed simp_all
  qed

lemma pnet_deliver_single_node [elim]:
  assumes "wf_net_tree p"
      and "s \<in> reachable (pnet np p) TT"
      and "(s, i:deliver(d), s') \<in> trans (pnet np p)"
  shows "(\<forall>j. j\<noteq>i \<longrightarrow> netmap s' j = netmap s j) \<and> net_ip_action np (i:deliver(d)) i p s s'"
    (is "?P p s s'")
  using assms proof (induction p arbitrary: s s')
    fix ii R\<^sub>i s s'
    assume sr: "s \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
       and tr: "(s, i:deliver(d), s') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
    from this obtain p R p' R' where "s = NodeS ii p R" and "s' = NodeS ii p' R'"
      by (metis (hide_lams, no_types) TT_True net_node_reachable_is_node
                                      reachable_step)
    hence "net_ips s = {ii}"
      and "net_ips s' = {ii}" by simp_all
    hence "\<forall>j. j \<noteq> ii \<longrightarrow> netmap s' j = netmap s j"
      by simp
    moreover from sr tr have "i = ii" by (rule delivered_to_node)
    ultimately show "(\<forall>j. j \<noteq> i \<longrightarrow> netmap s' j = netmap s j)
                     \<and> net_ip_action np (i:deliver(d)) i (\<langle>ii; R\<^sub>i\<rangle>) s s'"
      by simp
  next
    fix p1 p2 s s'
    assume IH1: "\<And>s s'. \<lbrakk> wf_net_tree p1;
                          s \<in> reachable (pnet np p1) TT;
                          (s, i:deliver(d), s') \<in> trans (pnet np p1) \<rbrakk>
                         \<Longrightarrow> (\<forall>j. j \<noteq> i \<longrightarrow> netmap s' j = netmap s j)
                             \<and> net_ip_action np (i:deliver(d)) i p1 s s'"
       and IH2: "\<And>s s'. \<lbrakk> wf_net_tree p2;
                          s \<in> reachable (pnet np p2) TT;
                          (s, i:deliver(d), s') \<in> trans (pnet np p2) \<rbrakk>
                         \<Longrightarrow> (\<forall>j. j \<noteq> i \<longrightarrow> netmap s' j = netmap s j)
                             \<and> net_ip_action np (i:deliver(d)) i p2 s s'"
       and sr: "s \<in> reachable (pnet np (p1 \<parallel> p2)) TT"
       and "wf_net_tree (p1 \<parallel> p2)"
       and tr: "(s, i:deliver(d), s') \<in> trans (pnet np (p1 \<parallel> p2))"
    from \<open>wf_net_tree (p1 \<parallel> p2)\<close> have "net_tree_ips p1 \<inter> net_tree_ips p2 = {}"
                                  and "wf_net_tree p1" 
                                  and "wf_net_tree p2" by auto
    from tr have "(s, i:deliver(d), s') \<in> pnet_sos (trans (pnet np p1)) (trans (pnet np p2))" by simp
    thus "(\<forall>j. j \<noteq> i \<longrightarrow> netmap s' j = netmap s j)
          \<and> net_ip_action np (i:deliver(d)) i (p1 \<parallel> p2) s s'"
    proof cases
      fix s1 s1' s2
      assume subs:  "s = SubnetS s1 s2"
         and subs': "s' = SubnetS s1' s2"
         and tr1: "(s1, i:deliver(d), s1') \<in> trans (pnet np p1)"
      from sr have sr1: "s1 \<in> reachable (pnet np p1) TT"
               and "s2 \<in> reachable (pnet np p2) TT"
        by (simp_all only: subs) (erule subnet_reachable)+
      with \<open>net_tree_ips p1 \<inter> net_tree_ips p2 = {}\<close> have "dom(netmap s1) \<inter> dom(netmap s2) = {}"
        by (metis net_ips_is_dom_netmap pnet_net_ips_net_tree_ips)
      moreover from sr1 tr1 have "i \<in> net_ips s1" by (rule delivered_to_net_ips)
      ultimately have "i\<notin>dom(netmap s2)" by (auto simp add: net_ips_is_dom_netmap)

      from \<open>wf_net_tree p1\<close> sr1 tr1 have *: "\<forall>j. j \<noteq> i \<longrightarrow> netmap s1' j = netmap s1 j"
                                     and "net_ip_action np (i:deliver(d)) i p1 s1 s1'"
          by (auto dest!: IH1)
      from subs subs' tr1 this(2) \<open>i\<notin>dom(netmap s2)\<close>
        have "net_ip_action np (i:deliver(d)) i (p1 \<parallel> p2) s s'"
          by (simp add: net_ips_is_dom_netmap)
      moreover have "\<forall>j. j \<noteq> i \<longrightarrow> (netmap s1' ++ netmap s2) j = (netmap s1 ++ netmap s2) j"
      proof (intro allI impI)
        fix j
        assume "j \<noteq> i"
        with * have "netmap s1' j = netmap s1 j" by simp
        thus "(netmap s1' ++ netmap s2) j = (netmap s1 ++ netmap s2) j"
          by (metis (hide_lams, mono_tags) map_add_dom_app_simps(1) map_add_dom_app_simps(3))
      qed
      ultimately show ?thesis using \<open>i\<in>net_ips s1\<close> subs subs' by auto
    next
      fix s2 s2' s1
      assume subs: "s = SubnetS s1 s2"
         and subs': "s' = SubnetS s1 s2'"
         and tr2: "(s2, i:deliver(d), s2') \<in> trans (pnet np p2)"
      from sr have "s1 \<in> reachable (pnet np p1) TT"
               and sr2: "s2 \<in> reachable (pnet np p2) TT"
        by (simp_all only: subs) (erule subnet_reachable)+
      with \<open>net_tree_ips p1 \<inter> net_tree_ips p2 = {}\<close> have "dom(netmap s1) \<inter> dom(netmap s2) = {}"
        by (metis net_ips_is_dom_netmap pnet_net_ips_net_tree_ips)
      moreover from sr2 tr2 have "i \<in> net_ips s2" by (rule delivered_to_net_ips)
      ultimately have "i\<notin>dom(netmap s1)" by (auto simp add: net_ips_is_dom_netmap)

      from \<open>wf_net_tree p2\<close> sr2 tr2 have *: "\<forall>j. j \<noteq> i \<longrightarrow> netmap s2' j = netmap s2 j"
                                     and "net_ip_action np (i:deliver(d)) i p2 s2 s2'"
          by (auto dest!: IH2)
      from subs subs' tr2 this(2) \<open>i\<notin>dom(netmap s1)\<close>
        have "net_ip_action np (i:deliver(d)) i (p1 \<parallel> p2) s s'"
          by (simp add: net_ips_is_dom_netmap)
      moreover have "\<forall>j. j \<noteq> i \<longrightarrow> (netmap s1 ++ netmap s2') j = (netmap s1 ++ netmap s2) j"
      proof (intro allI impI)
        fix j
        assume "j \<noteq> i"
        with * have "netmap s2' j = netmap s2 j" by simp
        thus "(netmap s1 ++ netmap s2') j = (netmap s1 ++ netmap s2) j"
          by (metis (hide_lams, mono_tags) domD map_add_Some_iff map_add_dom_app_simps(3))
      qed
      ultimately show ?thesis using \<open>i\<in>net_ips s2\<close> subs subs' by auto
    qed simp_all
  qed

end
