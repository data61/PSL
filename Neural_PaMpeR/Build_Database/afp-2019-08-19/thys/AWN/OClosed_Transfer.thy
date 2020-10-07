(*  Title:       OClosed_Transfer.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Transfer open results onto closed models"

theory OClosed_Transfer
imports Closed OClosed_Lifting
begin

locale openproc =
  fixes np  :: "ip \<Rightarrow> ('s, ('m::msg) seq_action) automaton"
    and onp :: "ip \<Rightarrow> ((ip \<Rightarrow> 'g) \<times> 'l, 'm seq_action) automaton"
    and sr  :: "'s \<Rightarrow> ('g \<times> 'l)"
  assumes  init: "{ (\<sigma>, \<zeta>) |\<sigma> \<zeta> s. s \<in> init (np i)
                             \<and> (\<sigma> i, \<zeta>) = sr s
                             \<and> (\<forall>j. j\<noteq>i \<longrightarrow> \<sigma> j \<in> (fst o sr) ` init (np j)) } \<subseteq> init (onp i)"
      and init_notempty: "\<forall>j. init (np j) \<noteq> {}"
      and trans: "\<And>s a s' \<sigma> \<sigma>'. \<lbrakk> \<sigma> i = fst (sr s);
                                  \<sigma>' i = fst (sr s');
                                  (s, a, s') \<in> trans (np i) \<rbrakk>
                   \<Longrightarrow> ((\<sigma>, snd (sr s)), a, (\<sigma>', snd (sr s'))) \<in> trans (onp i)"
begin

lemma init_pnet_p_NodeS:
  assumes "NodeS i s R \<in> init (pnet np p)"
    shows "p = \<langle>i; R\<rangle>"
  using assms by (cases p) (auto simp add: node_comps)

lemma init_pnet_p_SubnetS:
  assumes "SubnetS s1 s2 \<in> init (pnet np p)"
  obtains p1 p2 where "p = (p1 \<parallel> p2)"
                  and "s1 \<in> init (pnet np p1)"
                  and "s2 \<in> init (pnet np p2)"
  using assms by (cases p) (auto simp add: node_comps)

lemma init_pnet_fst_sr_netgmap:
  assumes "s \<in> init (pnet np p)"
      and "i \<in> net_ips s"
      and "wf_net_tree p"
    shows "the (fst (netgmap sr s) i) \<in> (fst \<circ> sr) ` init (np i)"
  using assms proof (induction s arbitrary: p)
    fix ii s R\<^sub>i p
    assume "NodeS ii s R\<^sub>i \<in> init (pnet np p)"
       and "i \<in> net_ips (NodeS ii s R\<^sub>i)"
       and "wf_net_tree p"
    note this(1)
    moreover then have "p = \<langle>ii; R\<^sub>i\<rangle>"
      by (rule init_pnet_p_NodeS)
    ultimately have "s \<in> init (np ii)"
      by (clarsimp simp: node_comps)
    with \<open>i \<in> net_ips (NodeS ii s R\<^sub>i)\<close>
      show "the (fst (netgmap sr (NodeS ii s R\<^sub>i)) i) \<in> (fst \<circ> sr) ` init (np i)"
        by clarsimp
  next
    fix s1 s2 p
    assume IH1: "\<And>p. s1 \<in> init (pnet np p)
                  \<Longrightarrow> i \<in> net_ips s1
                  \<Longrightarrow> wf_net_tree p
                  \<Longrightarrow> the (fst (netgmap sr s1) i) \<in> (fst \<circ> sr) ` init (np i)"
       and IH2: "\<And>p. s2 \<in> init (pnet np p)
                  \<Longrightarrow> i \<in> net_ips s2
                  \<Longrightarrow> wf_net_tree p
                  \<Longrightarrow> the (fst (netgmap sr s2) i) \<in> (fst \<circ> sr) ` init (np i)"
       and "SubnetS s1 s2 \<in> init (pnet np p)"
       and "i \<in> net_ips (SubnetS s1 s2)"
       and "wf_net_tree p"
    from this(3) obtain p1 p2 where "p = (p1 \<parallel> p2)"
                                and "s1 \<in> init (pnet np p1)"
                                and "s2 \<in> init (pnet np p2)"
      by (rule init_pnet_p_SubnetS)
    from this(1) and \<open>wf_net_tree p\<close> have "wf_net_tree p1"
                                      and "wf_net_tree p2"
                                      and "net_tree_ips p1 \<inter> net_tree_ips p2 = {}"
      by auto
    from \<open>i \<in> net_ips (SubnetS s1 s2)\<close> have "i \<in> net_ips s1 \<or> i \<in> net_ips s2"
      by simp
    thus "the (fst (netgmap sr (SubnetS s1 s2)) i) \<in> (fst \<circ> sr) ` init (np i)"
    proof
      assume "i \<in> net_ips s1"
      hence "i \<notin> net_ips s2"
      proof -
        from \<open>s1 \<in> init (pnet np p1)\<close> and \<open>i \<in> net_ips s1\<close> have "i\<in>net_tree_ips p1" ..
        with \<open>net_tree_ips p1 \<inter> net_tree_ips p2 = {}\<close> have "i\<notin>net_tree_ips p2" by auto
        with \<open>s2 \<in> init (pnet np p2)\<close> show ?thesis ..
      qed
      moreover from \<open>s1 \<in> init (pnet np p1)\<close>  \<open>i \<in> net_ips s1\<close> and \<open>wf_net_tree p1\<close>
        have "the (fst (netgmap sr s1) i) \<in> (fst \<circ> sr) ` init (np i)"
          by (rule IH1)
      ultimately show ?thesis by simp
    next
      assume "i \<in> net_ips s2"
      moreover with \<open>s2 \<in> init (pnet np p2)\<close> have "the (fst (netgmap sr s2) i) \<in> (fst \<circ> sr) ` init (np i)"
        using \<open>wf_net_tree p2\<close> by (rule IH2)
      moreover from \<open>s2 \<in> init (pnet np p2)\<close> and \<open>i \<in> net_ips s2\<close> have "i\<in>net_tree_ips p2" ..
      ultimately show ?thesis by simp
    qed
  qed

lemma init_lifted:
  assumes "wf_net_tree p"                                                          
  shows "{ (\<sigma>, snd (netgmap sr s)) |\<sigma> s. s \<in> init (pnet np p)
                               \<and> (\<forall>i. if i\<in>net_tree_ips p then \<sigma> i = the (fst (netgmap sr s) i)
                                      else \<sigma> i \<in> (fst o sr) ` init (np i)) } \<subseteq> init (opnet onp p)"
  using assms proof (induction p)
    fix i R
    assume "wf_net_tree \<langle>i; R\<rangle>"
    show "{(\<sigma>, snd (netgmap sr s)) |\<sigma> s. s \<in> init (pnet np \<langle>i; R\<rangle>)
            \<and> (\<forall>j. if j \<in> net_tree_ips \<langle>i; R\<rangle> then \<sigma> j = the (fst (netgmap sr s) j)
                   else \<sigma> j \<in> (fst \<circ> sr) ` init (np j))} \<subseteq> init (opnet onp \<langle>i; R\<rangle>)"
      by (clarsimp simp add: node_comps onode_comps)
         (rule subsetD [OF init], auto)
  next
    fix p1 p2
    assume IH1: "wf_net_tree p1
                \<Longrightarrow> {(\<sigma>, snd (netgmap sr s)) |\<sigma> s. s \<in> init (pnet np p1)
                      \<and> (\<forall>i. if i \<in> net_tree_ips p1 then \<sigma> i = the (fst (netgmap sr s) i)
                             else \<sigma> i \<in> (fst \<circ> sr) ` init (np i))} \<subseteq> init (opnet onp p1)"
                (is "_ \<Longrightarrow> ?S1 \<subseteq> _")
       and IH2: "wf_net_tree p2
                 \<Longrightarrow> {(\<sigma>, snd (netgmap sr s)) |\<sigma> s. s \<in> init (pnet np p2)
                       \<and> (\<forall>i. if i \<in> net_tree_ips p2 then \<sigma> i = the (fst (netgmap sr s) i)
                              else \<sigma> i \<in> (fst \<circ> sr) ` init (np i))} \<subseteq> init (opnet onp p2)"
                (is "_ \<Longrightarrow> ?S2 \<subseteq> _")
        and "wf_net_tree (p1 \<parallel> p2)"
    from this(3) have "wf_net_tree p1"
                  and "wf_net_tree p2"
                  and "net_tree_ips p1 \<inter> net_tree_ips p2 = {}" by auto
    show "{(\<sigma>, snd (netgmap sr s)) |\<sigma> s. s \<in> init (pnet np (p1 \<parallel> p2))
            \<and> (\<forall>i. if i \<in> net_tree_ips (p1 \<parallel> p2) then \<sigma> i = the (fst (netgmap sr s) i)
                   else \<sigma> i \<in> (fst \<circ> sr) ` init (np i))} \<subseteq> init (opnet onp (p1 \<parallel> p2))"
    proof (rule, clarsimp simp only: split_paired_all pnet.simps automaton.simps)
      fix \<sigma> s1 s2
      assume \<sigma>_desc: "\<forall>i. if i \<in> net_tree_ips (p1 \<parallel> p2)
                          then \<sigma> i = the (fst (netgmap sr (SubnetS s1 s2)) i)
                          else \<sigma> i \<in> (fst \<circ> sr) ` init (np i)"
         and "s1 \<in> init (pnet np p1)"
         and "s2 \<in> init (pnet np p2)"
      from this(2-3) have "net_ips s1 = net_tree_ips p1"
                      and "net_ips s2 = net_tree_ips p2" by auto
      have "(\<sigma>, snd (netgmap sr s1)) \<in> ?S1"
      proof -
        { fix i
          assume "i \<in> net_tree_ips p1"
          with \<open>net_tree_ips p1 \<inter> net_tree_ips p2 = {}\<close> have "i \<notin> net_tree_ips p2" by auto
          with \<open>s2 \<in> init (pnet np p2)\<close> have "i \<notin> net_ips s2" ..
          hence "the ((fst (netgmap sr s1) ++ fst (netgmap sr s2)) i) = the (fst (netgmap sr s1) i)"
            by simp
        }
        moreover
        { fix i
          assume "i \<notin> net_tree_ips p1"
          have "\<sigma> i \<in> (fst \<circ> sr) ` init (np i)"
          proof (cases "i \<in> net_tree_ips p2")
            assume "i \<notin> net_tree_ips p2"
            with \<open>i \<notin> net_tree_ips p1\<close> and \<sigma>_desc show ?thesis
              by (auto dest: spec [of _ i])
          next
            assume "i \<in> net_tree_ips p2"
            with \<open>s2 \<in> init (pnet np p2)\<close> have "i \<in> net_ips s2" ..
            with \<open>s2 \<in> init (pnet np p2)\<close> have "the (fst (netgmap sr s2) i) \<in> (fst \<circ> sr) ` init (np i)"
              using \<open>wf_net_tree p2\<close> by (rule init_pnet_fst_sr_netgmap)
            with \<open>i\<in>net_tree_ips p2\<close> and \<open>i\<in>net_ips s2\<close> show ?thesis
              using \<sigma>_desc by simp
          qed
        }
        ultimately show ?thesis
          using \<open>s1 \<in> init (pnet np p1)\<close> and \<sigma>_desc by auto
      qed
      hence "(\<sigma>, snd (netgmap sr s1)) \<in> init (opnet onp p1)"
        by (rule subsetD [OF IH1 [OF \<open>wf_net_tree p1\<close>]])

      have "(\<sigma>, snd (netgmap sr s2)) \<in> ?S2"
      proof -
        { fix i
          assume "i \<in> net_tree_ips p2"
          with \<open>s2 \<in> init (pnet np p2)\<close> have "i \<in> net_ips s2" ..
          hence "the ((fst (netgmap sr s1) ++ fst (netgmap sr s2)) i) = the (fst (netgmap sr s2) i)"
            by simp
        }
        moreover
        { fix i
          assume "i \<notin> net_tree_ips p2"
          have "\<sigma> i \<in> (fst \<circ> sr) ` init (np i)"
          proof (cases "i \<in> net_tree_ips p1")
            assume "i \<notin> net_tree_ips p1"
            with \<open>i \<notin> net_tree_ips p2\<close> and \<sigma>_desc show ?thesis
              by (auto dest: spec [of _ i])
          next
            assume "i \<in> net_tree_ips p1"
            with \<open>s1 \<in> init (pnet np p1)\<close> have "i \<in> net_ips s1" ..
            with \<open>s1 \<in> init (pnet np p1)\<close> have "the (fst (netgmap sr s1) i) \<in> (fst \<circ> sr) ` init (np i)"
              using \<open>wf_net_tree p1\<close> by (rule init_pnet_fst_sr_netgmap)
            moreover from \<open>s2 \<in> init (pnet np p2)\<close> and \<open>i \<notin> net_tree_ips p2\<close> have "i\<notin>net_ips s2" ..
            ultimately show ?thesis
              using \<open>i\<in>net_tree_ips p1\<close> \<open>i\<in>net_ips s1\<close> and \<open>i\<notin>net_tree_ips p2\<close> \<sigma>_desc by simp
          qed
        }
        ultimately show ?thesis
          using \<open>s2 \<in> init (pnet np p2)\<close> and \<sigma>_desc by auto
      qed
      hence "(\<sigma>, snd (netgmap sr s2)) \<in> init (opnet onp p2)"
        by (rule subsetD [OF IH2 [OF \<open>wf_net_tree p2\<close>]])

      with \<open>(\<sigma>, snd (netgmap sr s1)) \<in> init (opnet onp p1)\<close>
        show "(\<sigma>, snd (netgmap sr (SubnetS s1 s2))) \<in> init (opnet onp (p1 \<parallel> p2))"
        using \<open>net_tree_ips p1 \<inter> net_tree_ips p2 = {}\<close>
              \<open>net_ips s1 = net_tree_ips p1\<close>
              \<open>net_ips s2 = net_tree_ips p2\<close> by simp
    qed
  qed

lemma init_pnet_opnet [elim]:
  assumes "wf_net_tree p"
      and "s \<in> init (pnet np p)"
    shows "netgmap sr s \<in> netmask (net_tree_ips p) ` init (opnet onp p)"
  proof -
    from \<open>wf_net_tree p\<close>
      have "{ (\<sigma>, snd (netgmap sr s)) |\<sigma> s. s \<in> init (pnet np p)
                              \<and> (\<forall>i. if i\<in>net_tree_ips p then \<sigma> i = the (fst (netgmap sr s) i)
                                     else \<sigma> i \<in> (fst o sr) ` init (np i)) } \<subseteq> init (opnet onp p)"
        (is "?S \<subseteq> _")
      by (rule init_lifted)
    hence "netmask (net_tree_ips p) ` ?S \<subseteq> netmask (net_tree_ips p) ` init (opnet onp p)"
      by (rule image_mono)
    moreover have "netgmap sr s \<in> netmask (net_tree_ips p) ` ?S"
    proof -
      { fix i
        from init_notempty have "\<exists>s. s \<in> (fst \<circ> sr) ` init (np i)" by auto
        hence "(SOME x. x \<in> (fst \<circ> sr) ` init (np i)) \<in> (fst \<circ> sr) ` init (np i)" ..
      }
      with \<open>s \<in> init (pnet np p)\<close> and init_notempty
        have "(\<lambda>i. if i \<in> net_tree_ips p
                   then the (fst (netgmap sr s) i)
                   else SOME x. x \<in> (fst \<circ> sr) ` init (np i), snd (netgmap sr s)) \<in> ?S"
          (is "?s \<in> ?S") by auto
      moreover have "netgmap sr s = netmask (net_tree_ips p) ?s"
      proof (intro prod_eqI ext)
        fix i
        show "fst (netgmap sr s) i = fst (netmask (net_tree_ips p) ?s) i"
        proof (cases "i \<in> net_tree_ips p")
          assume "i \<in> net_tree_ips p"
          with \<open>s\<in>init (pnet np p)\<close> have "i\<in>net_ips s" ..
          hence "Some (the (fst (netgmap sr s) i)) = fst (netgmap sr s) i"
            by (rule some_the_fst_netgmap)
          with \<open>i\<in>net_tree_ips p\<close> show ?thesis
            by simp
        next
          assume "i \<notin> net_tree_ips p"
          moreover with \<open>s\<in>init (pnet np p)\<close> have "i\<notin>net_ips s" ..
          ultimately show ?thesis
            by simp
        qed
      qed simp
      ultimately show ?thesis
        by (rule rev_image_eqI)
    qed
    ultimately show ?thesis
      by (rule rev_subsetD [rotated])
  qed

lemma transfer_connect:
  assumes "(s, connect(i, i'), s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), connect(i, i'), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    from assms have "((\<sigma>, snd (netgmap sr s)), connect(i, i'), (\<sigma>, snd (netgmap sr s'))) \<in> trans (opnet onp n)
                     \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>, snd (netgmap sr s'))"
      proof (induction n arbitrary: s s' \<zeta>)
        fix ii R\<^sub>i ns ns' \<zeta>
        assume "(ns, connect(i, i'), ns') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
           and "netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)"
        from this(1) have "(ns, connect(i, i'), ns') \<in> node_sos (trans (np ii))"
          by (simp add: node_comps)
        moreover then obtain ni s s' R R' where "ns  = NodeS ni s R"
                                            and "ns' = NodeS ni s' R'" ..
        ultimately have "(NodeS ni s R, connect(i, i'), NodeS ni s' R') \<in> node_sos (trans (np ii))"
          by simp
        moreover then have "s' = s" by auto
        ultimately have "((\<sigma>, NodeS ni (snd (sr s)) R), connect(i, i'), (\<sigma>, NodeS ni (snd (sr s)) R'))
                                                                      \<in> onode_sos (trans (onp ii))"
          by - (rule node_connectTE', auto intro!: onode_sos.intros [simplified])
        with \<open>ns = NodeS ni s R\<close> \<open>ns' = NodeS ni s' R'\<close> \<open>s' = s\<close>
             and \<open>netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)\<close>
          show "((\<sigma>, snd (netgmap sr ns)), connect(i, i'), (\<sigma>, snd (netgmap sr ns'))) \<in> trans (opnet onp \<langle>ii; R\<^sub>i\<rangle>)
                \<and> netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, snd (netgmap sr ns'))"
            by (simp add: onode_comps)
      next
        fix n1 n2 s s' \<zeta>
        assume IH1: "\<And>s s' \<zeta>. (s, connect(i, i'), s') \<in> trans (pnet np n1)
                      \<Longrightarrow> s \<in> reachable (pnet np n1) TT
                      \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n1) (\<sigma>, \<zeta>)
                      \<Longrightarrow> wf_net_tree n1
                      \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), connect(i, i'), (\<sigma>, snd (netgmap sr s'))) \<in> trans (opnet onp n1)
                          \<and> netgmap sr s' = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s'))"
           and IH2: "\<And>s s' \<zeta>. (s, connect(i, i'), s') \<in> trans (pnet np n2)
                      \<Longrightarrow> s \<in> reachable (pnet np n2) TT
                      \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n2) (\<sigma>, \<zeta>)
                      \<Longrightarrow> wf_net_tree n2
                      \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), connect(i, i'), (\<sigma>, snd (netgmap sr s'))) \<in> trans (opnet onp n2)
                          \<and> netgmap sr s' = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s'))"
           and tr: "(s, connect(i, i'), s') \<in> trans (pnet np (n1 \<parallel> n2))"
           and sr: "s \<in> reachable (pnet np (n1 \<parallel> n2)) TT"
           and nm: "netgmap sr s = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
           and "wf_net_tree (n1 \<parallel> n2)"
        from this(3) have "(s, connect(i, i'), s') \<in> pnet_sos (trans (pnet np n1))
                                                               (trans (pnet np n2))"
          by simp
        then obtain s1 s1' s2 s2' where "s = SubnetS s1 s2"
                                    and "s' = SubnetS s1' s2'"
                                    and "(s1, connect(i, i'), s1') \<in> trans (pnet np n1)"
                                    and "(s2, connect(i, i'), s2') \<in> trans (pnet np n2)"
          by (rule partial_connectTE) auto
        from this(1) and nm have "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
          by simp

        from \<open>wf_net_tree (n1 \<parallel> n2)\<close> have "wf_net_tree n1" and "wf_net_tree n2"
                                      and "net_tree_ips n1 \<inter> net_tree_ips n2 = {}" by auto

        from sr \<open>s = SubnetS s1 s2\<close> have "s1 \<in> reachable (pnet np n1) TT" by (metis subnet_reachable(1))
        hence "net_ips s1 = net_tree_ips n1" by (rule pnet_net_ips_net_tree_ips)

        from sr \<open>s = SubnetS s1 s2\<close> have "s2 \<in> reachable (pnet np n2) TT" by (metis subnet_reachable(2))
        hence "net_ips s2 = net_tree_ips n2" by (rule pnet_net_ips_net_tree_ips)

        from nm \<open>s = SubnetS s1 s2\<close>
          have "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)" by simp
        hence "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
          using \<open>net_tree_ips n1 \<inter> net_tree_ips n2 = {}\<close> \<open>net_ips s1 = net_tree_ips n1\<close>
                and \<open>net_ips s2 = net_tree_ips n2\<close> by (rule netgmap_subnet_split1)
        with \<open>(s1, connect(i, i'), s1') \<in> trans (pnet np n1)\<close>
         and \<open>s1 \<in> reachable (pnet np n1) TT\<close>
         have "((\<sigma>, snd (netgmap sr s1)), connect(i, i'), (\<sigma>, snd (netgmap sr s1'))) \<in> trans (opnet onp n1)"
          and "netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1'))"
           using \<open>wf_net_tree n1\<close> unfolding atomize_conj by (rule IH1)

        from \<open>netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)\<close>
             \<open>net_ips s1 = net_tree_ips n1\<close> and \<open>net_ips s2 = net_tree_ips n2\<close>
          have "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
            by (rule netgmap_subnet_split2)
        with \<open>(s2, connect(i, i'), s2') \<in> trans (pnet np n2)\<close>
         and \<open>s2 \<in> reachable (pnet np n2) TT\<close>
         have "((\<sigma>, snd (netgmap sr s2)), connect(i, i'), (\<sigma>, snd (netgmap sr s2'))) \<in> trans (opnet onp n2)"
          and "netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2'))"
           using \<open>wf_net_tree n2\<close> unfolding atomize_conj by (rule IH2)

        have "((\<sigma>, snd (netgmap sr s)), connect(i, i'), (\<sigma>, snd (netgmap sr s')))
                                         \<in> trans (opnet onp (n1 \<parallel> n2))"
        proof -
          from \<open>((\<sigma>, snd (netgmap sr s1)), connect(i, i'), (\<sigma>, snd (netgmap sr s1'))) \<in> trans (opnet onp n1)\<close>
           and \<open>((\<sigma>, snd (netgmap sr s2)), connect(i, i'), (\<sigma>, snd (netgmap sr s2'))) \<in> trans (opnet onp n2)\<close>
            have "((\<sigma>, SubnetS (snd (netgmap sr s1)) (snd (netgmap sr s2))), connect(i, i'),
                   (\<sigma>, SubnetS (snd (netgmap sr s1')) (snd (netgmap sr s2'))))
                                           \<in> opnet_sos (trans (opnet onp n1)) (trans (opnet onp n2))"
              by (rule opnet_connect)
          with \<open>s = SubnetS s1 s2\<close> \<open>s' = SubnetS s1' s2'\<close> show ?thesis by simp
        qed

        moreover from \<open>netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1'))\<close>
                      \<open>netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2'))\<close>
                      \<open>s' = SubnetS s1' s2'\<close>
          have "netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, snd (netgmap sr s'))" ..

        ultimately show "((\<sigma>, snd (netgmap sr s)), connect(i, i'), (\<sigma>, snd (netgmap sr s')))
                                                                \<in> trans (opnet onp (n1 \<parallel> n2))
                         \<and> netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, snd (netgmap sr s'))" ..
      qed
    moreover from \<open>netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)\<close> have "\<zeta> = snd (netgmap sr s)" by simp
    ultimately show " \<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), connect(i, i'), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                              \<and> (\<forall>j. j \<notin> net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                              \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')" by auto
  qed

lemma transfer_disconnect:
  assumes "(s, disconnect(i, i'), s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), disconnect(i, i'), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    from assms have "((\<sigma>, snd (netgmap sr s)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s'))) \<in> trans (opnet onp n)
                     \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>, snd (netgmap sr s'))"
      proof (induction n arbitrary: s s' \<zeta>)
        fix ii R\<^sub>i ns ns' \<zeta>
        assume "(ns, disconnect(i, i'), ns') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
           and "netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)"
        from this(1) have "(ns, disconnect(i, i'), ns') \<in> node_sos (trans (np ii))"
          by (simp add: node_comps)
        moreover then obtain ni s s' R R' where "ns  = NodeS ni s R"
                                            and "ns' = NodeS ni s' R'" ..
        ultimately have "(NodeS ni s R, disconnect(i, i'), NodeS ni s' R') \<in> node_sos (trans (np ii))"
          by simp
        moreover then have "s' = s" by auto
        ultimately have "((\<sigma>, NodeS ni (snd (sr s)) R), disconnect(i, i'), (\<sigma>, NodeS ni (snd (sr s)) R'))
                                                                      \<in> onode_sos (trans (onp ii))"
          by - (rule node_disconnectTE', auto intro!: onode_sos.intros [simplified])
        with \<open>ns = NodeS ni s R\<close> \<open>ns' = NodeS ni s' R'\<close> \<open>s' = s\<close>
             and \<open>netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)\<close>
          show "((\<sigma>, snd (netgmap sr ns)), disconnect(i, i'), (\<sigma>, snd (netgmap sr ns'))) \<in> trans (opnet onp \<langle>ii; R\<^sub>i\<rangle>)
                \<and> netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, snd (netgmap sr ns'))"
            by (simp add: onode_comps)
      next
        fix n1 n2 s s' \<zeta>
        assume IH1: "\<And>s s' \<zeta>. (s, disconnect(i, i'), s') \<in> trans (pnet np n1)
                      \<Longrightarrow> s \<in> reachable (pnet np n1) TT
                      \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n1) (\<sigma>, \<zeta>)
                      \<Longrightarrow> wf_net_tree n1
                      \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s'))) \<in> trans (opnet onp n1)
                          \<and> netgmap sr s' = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s'))"
           and IH2: "\<And>s s' \<zeta>. (s, disconnect(i, i'), s') \<in> trans (pnet np n2)
                      \<Longrightarrow> s \<in> reachable (pnet np n2) TT
                      \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n2) (\<sigma>, \<zeta>)
                      \<Longrightarrow> wf_net_tree n2
                      \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s'))) \<in> trans (opnet onp n2)
                          \<and> netgmap sr s' = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s'))"
           and tr: "(s, disconnect(i, i'), s') \<in> trans (pnet np (n1 \<parallel> n2))"
           and sr: "s \<in> reachable (pnet np (n1 \<parallel> n2)) TT"
           and nm: "netgmap sr s = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
           and "wf_net_tree (n1 \<parallel> n2)"
        from this(3) have "(s, disconnect(i, i'), s') \<in> pnet_sos (trans (pnet np n1))
                                                               (trans (pnet np n2))"
          by simp
        then obtain s1 s1' s2 s2' where "s = SubnetS s1 s2"
                                    and "s' = SubnetS s1' s2'"
                                    and "(s1, disconnect(i, i'), s1') \<in> trans (pnet np n1)"
                                    and "(s2, disconnect(i, i'), s2') \<in> trans (pnet np n2)"
          by (rule partial_disconnectTE) auto
        from this(1) and nm have "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
          by simp

        from \<open>wf_net_tree (n1 \<parallel> n2)\<close> have "wf_net_tree n1" and "wf_net_tree n2"
                                      and "net_tree_ips n1 \<inter> net_tree_ips n2 = {}" by auto

        from sr \<open>s = SubnetS s1 s2\<close> have "s1 \<in> reachable (pnet np n1) TT" by (metis subnet_reachable(1))
        hence "net_ips s1 = net_tree_ips n1" by (rule pnet_net_ips_net_tree_ips)

        from sr \<open>s = SubnetS s1 s2\<close> have "s2 \<in> reachable (pnet np n2) TT" by (metis subnet_reachable(2))
        hence "net_ips s2 = net_tree_ips n2" by (rule pnet_net_ips_net_tree_ips)

        from nm \<open>s = SubnetS s1 s2\<close>
          have "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)" by simp
        hence "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
          using \<open>net_tree_ips n1 \<inter> net_tree_ips n2 = {}\<close> \<open>net_ips s1 = net_tree_ips n1\<close>
                and \<open>net_ips s2 = net_tree_ips n2\<close> by (rule netgmap_subnet_split1)
        with \<open>(s1, disconnect(i, i'), s1') \<in> trans (pnet np n1)\<close>
         and \<open>s1 \<in> reachable (pnet np n1) TT\<close>
         have "((\<sigma>, snd (netgmap sr s1)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s1'))) \<in> trans (opnet onp n1)"
          and "netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1'))"
           using \<open>wf_net_tree n1\<close> unfolding atomize_conj by (rule IH1)

        from \<open>netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)\<close>
             \<open>net_ips s1 = net_tree_ips n1\<close> and \<open>net_ips s2 = net_tree_ips n2\<close>
          have "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
            by (rule netgmap_subnet_split2)
        with \<open>(s2, disconnect(i, i'), s2') \<in> trans (pnet np n2)\<close>
         and \<open>s2 \<in> reachable (pnet np n2) TT\<close>
         have "((\<sigma>, snd (netgmap sr s2)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s2'))) \<in> trans (opnet onp n2)"
          and "netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2'))"
           using \<open>wf_net_tree n2\<close> unfolding atomize_conj by (rule IH2)

        have "((\<sigma>, snd (netgmap sr s)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s')))
                                         \<in> trans (opnet onp (n1 \<parallel> n2))"
        proof -
          from \<open>((\<sigma>, snd (netgmap sr s1)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s1'))) \<in> trans (opnet onp n1)\<close>
           and \<open>((\<sigma>, snd (netgmap sr s2)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s2'))) \<in> trans (opnet onp n2)\<close>
            have "((\<sigma>, SubnetS (snd (netgmap sr s1)) (snd (netgmap sr s2))), disconnect(i, i'),
                   (\<sigma>, SubnetS (snd (netgmap sr s1')) (snd (netgmap sr s2'))))
                                           \<in> opnet_sos (trans (opnet onp n1)) (trans (opnet onp n2))"
              by (rule opnet_disconnect)
          with \<open>s = SubnetS s1 s2\<close> \<open>s' = SubnetS s1' s2'\<close> show ?thesis by simp
        qed

        moreover from \<open>netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1'))\<close>
                      \<open>netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2'))\<close>
                      \<open>s' = SubnetS s1' s2'\<close>
          have "netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, snd (netgmap sr s'))" ..

        ultimately show "((\<sigma>, snd (netgmap sr s)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s')))
                                                                \<in> trans (opnet onp (n1 \<parallel> n2))
                         \<and> netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, snd (netgmap sr s'))" ..
      qed
    moreover from \<open>netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)\<close> have "\<zeta> = snd (netgmap sr s)" by simp
    ultimately show "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), disconnect(i, i'), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                              \<and> (\<forall>j. j \<notin> net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                              \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')" by auto
  qed

lemma transfer_tau:
  assumes "(s, \<tau>, s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), \<tau>, (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    from assms(4,2,1) obtain i where "i\<in>net_ips s"
                                 and "\<forall>j. j\<noteq>i \<longrightarrow> netmap s' j = netmap s j"
                                 and "net_ip_action np \<tau> i n s s'"
      by (metis pnet_tau_single_node)
    from this(2) have "\<forall>j. j\<noteq>i \<longrightarrow> fst (netgmap sr s') j = fst (netgmap sr s) j"
      by (clarsimp intro!: netmap_is_fst_netgmap')
    from \<open>(s, \<tau>, s') \<in> trans (pnet np n)\<close> have "net_ips s' = net_ips s"
      by (rule pnet_maintains_dom [THEN sym])
    define \<sigma>' where "\<sigma>' j = (if j = i then the (fst (netgmap sr s') i) else \<sigma> j)" for j
    from \<open>\<forall>j. j\<noteq>i \<longrightarrow> fst (netgmap sr s') j = fst (netgmap sr s) j\<close>
         and \<open>netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)\<close>
      have "\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j"
        unfolding \<sigma>'_def by clarsimp

    from assms(2) have "net_ips s = net_tree_ips n"
      by (rule pnet_net_ips_net_tree_ips)

    from \<open>netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)\<close>
      have "\<zeta> = snd (netgmap sr s)" by simp

    from \<open>\<forall>j. j\<noteq>i \<longrightarrow> fst (netgmap sr s') j = fst (netgmap sr s) j\<close> \<open>i \<in> net_ips s\<close>
         \<open>net_ips s = net_tree_ips n\<close> \<open>net_ips s' = net_ips s\<close>
         \<open>netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)\<close>
      have "fst (netgmap sr s') = fst (netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s')))"
        unfolding \<sigma>'_def [abs_def] by - (rule ext, clarsimp)

    hence "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
      by (rule prod_eqI, simp)

    with assms(1, 3)
      have "((\<sigma>, snd (netgmap sr s)), \<tau>, (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
        using assms(2,4) \<open>i\<in>net_ips s\<close> and \<open>net_ip_action np \<tau> i n s s'\<close>
    proof (induction n arbitrary: s s' \<zeta>)
      fix ii R\<^sub>i ns ns' \<zeta>
      assume "(ns, \<tau>, ns') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
         and nsr: "ns \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
         and "netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)"
         and "netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))"
         and "i\<in>net_ips ns"
      from this(1) have "(ns, \<tau>, ns') \<in> node_sos (trans (np ii))"
        by (simp add: node_comps)
      moreover with nsr obtain s s' R R' where "ns  = NodeS ii s R"
                                           and "ns' = NodeS ii s' R'"
         by (metis net_node_reachable_is_node node_tauTE')
      moreover from \<open>i \<in> net_ips ns\<close> and \<open>ns  = NodeS ii s R\<close> have "ii = i" by simp
      ultimately have ntr: "(NodeS i s R, \<tau>, NodeS i s' R') \<in> node_sos (trans (np i))"
        by simp
      hence "R' = R" by (metis net_state.inject(1) node_tauTE')

      from ntr obtain a where "(s, a, s') \<in> trans (np i)"
                          and "(\<exists>d. a = \<not>unicast d \<and> d\<notin>R) \<or> (a = \<tau>)"
        by (rule node_tauTE') auto

      from \<open>netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)\<close> \<open>ns  = NodeS ii s R\<close> and \<open>ii = i\<close>
        have "\<sigma> i = fst (sr s)" by simp (metis map_upd_Some_unfold)

      moreover from \<open>netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))\<close>
                    \<open>ns' = NodeS ii s' R'\<close> and \<open>ii = i\<close>
        have "\<sigma>' i = fst (sr s')"
          unfolding \<sigma>'_def [abs_def] by clarsimp (hypsubst_thin,
                                        metis (full_types, lifting) fun_upd_same option.sel)
      ultimately have "((\<sigma>, snd (sr s)), a, (\<sigma>', snd (sr s'))) \<in> trans (onp i)"
        using \<open>(s, a, s') \<in> trans (np i)\<close> by (rule trans)

      from \<open>(\<exists>d. a = \<not>unicast d \<and> d\<notin>R) \<or> (a = \<tau>)\<close> \<open>\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j\<close> \<open>R'=R\<close>
           and \<open>((\<sigma>, snd (sr s)), a, (\<sigma>', snd (sr s'))) \<in> trans (onp i)\<close>
        have "((\<sigma>, NodeS i (snd (sr s)) R), \<tau>, (\<sigma>', NodeS i (snd (sr s')) R')) \<in> onode_sos (trans (onp i))"
          by (metis onode_sos.onode_notucast onode_sos.onode_tau)

      with \<open>ns  = NodeS ii s R\<close> \<open>ns' = NodeS ii s' R'\<close> \<open>ii = i\<close>
        show "((\<sigma>, snd (netgmap sr ns)), \<tau>, (\<sigma>', snd (netgmap sr ns'))) \<in> trans (opnet onp \<langle>ii; R\<^sub>i\<rangle>)"
          by (simp add: onode_comps)
    next
      fix n1 n2 s s' \<zeta>
      assume IH1: "\<And>s s' \<zeta>. (s, \<tau>, s') \<in> trans (pnet np n1)
                    \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n1) (\<sigma>, \<zeta>)
                    \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s'))
                    \<Longrightarrow> s \<in> reachable (pnet np n1) TT
                    \<Longrightarrow> wf_net_tree n1
                    \<Longrightarrow> i\<in>net_ips s
                    \<Longrightarrow> net_ip_action np \<tau> i n1 s s'
                    \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), \<tau>, (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n1)"
         and IH2: "\<And>s s' \<zeta>. (s, \<tau>, s') \<in> trans (pnet np n2)
                    \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n2) (\<sigma>, \<zeta>)
                    \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s'))
                    \<Longrightarrow> s \<in> reachable (pnet np n2) TT
                    \<Longrightarrow> wf_net_tree n2
                    \<Longrightarrow> i\<in>net_ips s
                    \<Longrightarrow> net_ip_action np \<tau> i n2 s s'
                    \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), \<tau>, (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n2)"
         and tr: "(s, \<tau>, s') \<in> trans (pnet np (n1 \<parallel> n2))"
         and sr: "s \<in> reachable (pnet np (n1 \<parallel> n2)) TT"
         and nm: "netgmap sr s = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
         and nm': "netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>', snd (netgmap sr s'))"
         and "wf_net_tree (n1 \<parallel> n2)"
         and "i\<in>net_ips s"
         and "net_ip_action np \<tau> i (n1 \<parallel> n2) s s'"
      from tr have "(s, \<tau>, s') \<in> pnet_sos (trans (pnet np n1)) (trans (pnet np n2))" by simp
      then obtain s1 s1' s2 s2' where "s = SubnetS s1 s2"
                                  and "s' = SubnetS s1' s2'"
        by (rule partial_tauTE) auto
      from this(1) and nm have "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
        by simp
      from \<open>s' = SubnetS s1' s2'\<close> and nm'
        have "netgmap sr (SubnetS s1' s2') = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>', snd (netgmap sr s'))"
          by simp

      from \<open>wf_net_tree (n1 \<parallel> n2)\<close> have "wf_net_tree n1"
                                    and "wf_net_tree n2"
                                    and "net_tree_ips n1 \<inter> net_tree_ips n2 = {}" by auto

      from sr [simplified \<open>s = SubnetS s1 s2\<close>] have "s1 \<in> reachable (pnet np n1) TT"
        by (rule subnet_reachable(1))
      hence "net_ips s1 = net_tree_ips n1" by (rule pnet_net_ips_net_tree_ips)

      from sr [simplified \<open>s = SubnetS s1 s2\<close>] have "s2 \<in> reachable (pnet np n2) TT"
        by (rule subnet_reachable(2))
      hence "net_ips s2 = net_tree_ips n2" by (rule pnet_net_ips_net_tree_ips)

      from nm [simplified \<open>s = SubnetS s1 s2\<close>]
           \<open>net_tree_ips n1 \<inter> net_tree_ips n2 = {}\<close>
           \<open>net_ips s1 = net_tree_ips n1\<close>
           \<open>net_ips s2 = net_tree_ips n2\<close> 
        have "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
          by (rule netgmap_subnet_split1)

      from nm [simplified \<open>s = SubnetS s1 s2\<close>]
           \<open>net_ips s1 = net_tree_ips n1\<close>
           \<open>net_ips s2 = net_tree_ips n2\<close> 
        have "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
          by (rule netgmap_subnet_split2)

      from \<open>i\<in>net_ips s\<close> and \<open>s = SubnetS s1 s2\<close> have "i\<in>net_ips s1 \<or> i\<in>net_ips s2" by auto
        thus "((\<sigma>, snd (netgmap sr s)), \<tau>, (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp (n1 \<parallel> n2))"
      proof
        assume "i\<in>net_ips s1"
        with \<open>s = SubnetS s1 s2\<close> \<open>s' = SubnetS s1' s2'\<close> \<open>net_ip_action np \<tau> i (n1 \<parallel> n2) s s'\<close>
          have "(s1, \<tau>, s1') \<in> trans (pnet np n1)"
           and "net_ip_action np \<tau> i n1 s1 s1'"
           and "s2' = s2" by simp_all

        from \<open>net_ips s1 = net_tree_ips n1\<close> and \<open>(s1, \<tau>, s1') \<in> trans (pnet np n1)\<close>
          have "net_ips s1' = net_tree_ips n1" by (metis pnet_maintains_dom)

        from nm' [simplified \<open>s' = SubnetS s1' s2'\<close> \<open>s2' = s2\<close>]
                        \<open>net_tree_ips n1 \<inter> net_tree_ips n2 = {}\<close>
                        \<open>net_ips s1' = net_tree_ips n1\<close>
                        \<open>net_ips s2 = net_tree_ips n2\<close>
          have "netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))"
            by (rule netgmap_subnet_split1)

        from \<open>(s1, \<tau>, s1') \<in> trans (pnet np n1)\<close>
             \<open>netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))\<close>
             \<open>netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))\<close>
             \<open>s1 \<in> reachable (pnet np n1) TT\<close>
             \<open>wf_net_tree n1\<close>
             \<open>i\<in>net_ips s1\<close>
             \<open>net_ip_action np \<tau> i n1 s1 s1'\<close>
          have "((\<sigma>, snd (netgmap sr s1)), \<tau>, (\<sigma>', snd (netgmap sr s1'))) \<in> trans (opnet onp n1)"
             by (rule IH1)

        with \<open>s = SubnetS s1 s2\<close> \<open>s' = SubnetS s1' s2'\<close> \<open>s2' = s2\<close> show ?thesis
          by (simp del: step_node_tau) (erule opnet_tau1)
      next
        assume "i\<in>net_ips s2"
        with \<open>s = SubnetS s1 s2\<close> \<open>s' = SubnetS s1' s2'\<close> \<open>net_ip_action np \<tau> i (n1 \<parallel> n2) s s'\<close>
          have "(s2, \<tau>, s2') \<in> trans (pnet np n2)"
           and "net_ip_action np \<tau> i n2 s2 s2'"
           and "s1' = s1" by simp_all

        from \<open>net_ips s2 = net_tree_ips n2\<close> and \<open>(s2, \<tau>, s2') \<in> trans (pnet np n2)\<close>
          have "net_ips s2' = net_tree_ips n2" by (metis pnet_maintains_dom)

        from nm' [simplified \<open>s' = SubnetS s1' s2'\<close> \<open>s1' = s1\<close>]
                        \<open>net_ips s1 = net_tree_ips n1\<close>
                        \<open>net_ips s2' = net_tree_ips n2\<close>
          have "netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))"
            by (rule netgmap_subnet_split2)

        from \<open>(s2, \<tau>, s2') \<in> trans (pnet np n2)\<close>
             \<open>netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))\<close>
             \<open>netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))\<close>
             \<open>s2 \<in> reachable (pnet np n2) TT\<close>
             \<open>wf_net_tree n2\<close>
             \<open>i\<in>net_ips s2\<close>
             \<open>net_ip_action np \<tau> i n2 s2 s2'\<close>
          have "((\<sigma>, snd (netgmap sr s2)), \<tau>, (\<sigma>', snd (netgmap sr s2'))) \<in> trans (opnet onp n2)"
             by (rule IH2)

        with \<open>s = SubnetS s1 s2\<close> \<open>s' = SubnetS s1' s2'\<close> \<open>s1' = s1\<close> show ?thesis
          by (simp del: step_node_tau) (erule opnet_tau2)
      qed
    qed
    with \<open>\<zeta> = snd (netgmap sr s)\<close> have "((\<sigma>, \<zeta>), \<tau>, (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
      by simp
    moreover from \<open>\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j\<close> \<open>i \<in> net_ips s\<close> \<open>\<zeta> = snd (netgmap sr s)\<close>
      have "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j" by (metis net_ips_netgmap)
    ultimately have "((\<sigma>, \<zeta>), \<tau>, (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)
                     \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                     \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
      using \<open>netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))\<close> by simp
    thus "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), \<tau>, (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                  \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                  \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')" by auto
  qed

lemma transfer_deliver:
  assumes "(s, i:deliver(d), s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), i:deliver(d), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    from assms(4,2,1) obtain "i\<in>net_ips s"
                         and "\<forall>j. j\<noteq>i \<longrightarrow> netmap s' j = netmap s j"
                         and "net_ip_action np (i:deliver(d)) i n s s'"
      by (metis delivered_to_net_ips pnet_deliver_single_node)
    from this(2) have "\<forall>j. j\<noteq>i \<longrightarrow> fst (netgmap sr s') j = fst (netgmap sr s) j"
      by (clarsimp intro!: netmap_is_fst_netgmap')
    from \<open>(s, i:deliver(d), s') \<in> trans (pnet np n)\<close> have "net_ips s' = net_ips s"
      by (rule pnet_maintains_dom [THEN sym])
    define \<sigma>' where "\<sigma>' j = (if j = i then the (fst (netgmap sr s') i) else \<sigma> j)" for j
    from \<open>\<forall>j. j\<noteq>i \<longrightarrow> fst (netgmap sr s') j = fst (netgmap sr s) j\<close>
         and \<open>netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)\<close>
      have "\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j"
        unfolding \<sigma>'_def by clarsimp

    from assms(2) have "net_ips s = net_tree_ips n"
      by (rule pnet_net_ips_net_tree_ips)

    from \<open>netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)\<close>
      have "\<zeta> = snd (netgmap sr s)" by simp

    from \<open>\<forall>j. j\<noteq>i \<longrightarrow> fst (netgmap sr s') j = fst (netgmap sr s) j\<close> \<open>i \<in> net_ips s\<close>
         \<open>net_ips s = net_tree_ips n\<close> \<open>net_ips s' = net_ips s\<close>
         \<open>netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)\<close>
      have "fst (netgmap sr s') = fst (netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s')))"
        unfolding \<sigma>'_def [abs_def] by - (rule ext, clarsimp)

    hence "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
      by (rule prod_eqI, simp)

    with assms(1, 3)
      have "((\<sigma>, snd (netgmap sr s)), i:deliver(d), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
        using assms(2,4) \<open>i\<in>net_ips s\<close> and \<open>net_ip_action np (i:deliver(d)) i n s s'\<close>
    proof (induction n arbitrary: s s' \<zeta>)
      fix ii R\<^sub>i ns ns' \<zeta>
      assume "(ns, i:deliver(d), ns') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
         and nsr: "ns \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
         and "netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)"
         and "netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))"
         and "i\<in>net_ips ns"
      from this(1) have "(ns, i:deliver(d), ns') \<in> node_sos (trans (np ii))"
        by (simp add: node_comps)
      moreover with nsr obtain s s' R R' where "ns  = NodeS ii s R"
                                           and "ns' = NodeS ii s' R'"
         by (metis net_node_reachable_is_node node_sos_dest)
      moreover from \<open>i \<in> net_ips ns\<close> and \<open>ns  = NodeS ii s R\<close> have "ii = i" by simp
      ultimately have ntr: "(NodeS i s R, i:deliver(d), NodeS i s' R') \<in> node_sos (trans (np i))"
        by simp
      hence "R' = R" by (metis net_state.inject(1) node_deliverTE')

      from ntr have "(s, deliver d, s') \<in> trans (np i)"
        by (rule node_deliverTE') simp

      from \<open>netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)\<close> \<open>ns  = NodeS ii s R\<close> and \<open>ii = i\<close>
        have "\<sigma> i = fst (sr s)" by simp (metis map_upd_Some_unfold)

      moreover from \<open>netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))\<close>
                    \<open>ns' = NodeS ii s' R'\<close> and \<open>ii = i\<close>
        have "\<sigma>' i = fst (sr s')"
          unfolding \<sigma>'_def [abs_def] by clarsimp (hypsubst_thin,
                                        metis (lifting, full_types) fun_upd_same option.sel)
      ultimately have "((\<sigma>, snd (sr s)), deliver d, (\<sigma>', snd (sr s'))) \<in> trans (onp i)"
        using \<open>(s, deliver d, s') \<in> trans (np i)\<close> by (rule trans)

      with \<open>\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j\<close> \<open>R'=R\<close>
        have "((\<sigma>, NodeS i (snd (sr s)) R), i:deliver(d), (\<sigma>', NodeS i (snd (sr s')) R'))
                                                                      \<in> onode_sos (trans (onp i))"
          by (metis onode_sos.onode_deliver)

      with \<open>ns  = NodeS ii s R\<close> \<open>ns' = NodeS ii s' R'\<close> \<open>ii = i\<close>
        show "((\<sigma>, snd (netgmap sr ns)), i:deliver(d), (\<sigma>', snd (netgmap sr ns'))) \<in> trans (opnet onp \<langle>ii; R\<^sub>i\<rangle>)"
          by (simp add: onode_comps)
    next
      fix n1 n2 s s' \<zeta>
      assume IH1: "\<And>s s' \<zeta>. (s, i:deliver(d), s') \<in> trans (pnet np n1)
                    \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n1) (\<sigma>, \<zeta>)
                    \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s'))
                    \<Longrightarrow> s \<in> reachable (pnet np n1) TT
                    \<Longrightarrow> wf_net_tree n1
                    \<Longrightarrow> i\<in>net_ips s
                    \<Longrightarrow> net_ip_action np (i:deliver(d)) i n1 s s'
                    \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), i:deliver(d), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n1)"
         and IH2: "\<And>s s' \<zeta>. (s, i:deliver(d), s') \<in> trans (pnet np n2)
                    \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n2) (\<sigma>, \<zeta>)
                    \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s'))
                    \<Longrightarrow> s \<in> reachable (pnet np n2) TT
                    \<Longrightarrow> wf_net_tree n2
                    \<Longrightarrow> i\<in>net_ips s
                    \<Longrightarrow> net_ip_action np (i:deliver(d)) i n2 s s'
                    \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), i:deliver(d), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n2)"
         and tr: "(s, i:deliver(d), s') \<in> trans (pnet np (n1 \<parallel> n2))"
         and sr: "s \<in> reachable (pnet np (n1 \<parallel> n2)) TT"
         and nm: "netgmap sr s = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
         and nm': "netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>', snd (netgmap sr s'))"
         and "wf_net_tree (n1 \<parallel> n2)"
         and "i\<in>net_ips s"
         and "net_ip_action np (i:deliver(d)) i (n1 \<parallel> n2) s s'"
      from tr have "(s, i:deliver(d), s') \<in> pnet_sos (trans (pnet np n1)) (trans (pnet np n2))" by simp
      then obtain s1 s1' s2 s2' where "s = SubnetS s1 s2"
                                  and "s' = SubnetS s1' s2'"
        by (rule partial_deliverTE) auto
      from this(1) and nm have "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
        by simp
      from \<open>s' = SubnetS s1' s2'\<close> and nm'
        have "netgmap sr (SubnetS s1' s2') = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>', snd (netgmap sr s'))"
          by simp

      from \<open>wf_net_tree (n1 \<parallel> n2)\<close> have "wf_net_tree n1"
                                    and "wf_net_tree n2"
                                    and "net_tree_ips n1 \<inter> net_tree_ips n2 = {}" by auto

      from sr [simplified \<open>s = SubnetS s1 s2\<close>] have "s1 \<in> reachable (pnet np n1) TT"
        by (rule subnet_reachable(1))
      hence "net_ips s1 = net_tree_ips n1" by (rule pnet_net_ips_net_tree_ips)

      from sr [simplified \<open>s = SubnetS s1 s2\<close>] have "s2 \<in> reachable (pnet np n2) TT"
        by (rule subnet_reachable(2))
      hence "net_ips s2 = net_tree_ips n2" by (rule pnet_net_ips_net_tree_ips)

      from nm [simplified \<open>s = SubnetS s1 s2\<close>]
           \<open>net_tree_ips n1 \<inter> net_tree_ips n2 = {}\<close>
           \<open>net_ips s1 = net_tree_ips n1\<close>
           \<open>net_ips s2 = net_tree_ips n2\<close> 
        have "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
          by (rule netgmap_subnet_split1)

      from nm [simplified \<open>s = SubnetS s1 s2\<close>]
           \<open>net_ips s1 = net_tree_ips n1\<close>
           \<open>net_ips s2 = net_tree_ips n2\<close> 
        have "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
          by (rule netgmap_subnet_split2)

      from \<open>i\<in>net_ips s\<close> and \<open>s = SubnetS s1 s2\<close> have "i\<in>net_ips s1 \<or> i\<in>net_ips s2" by auto
        thus "((\<sigma>, snd (netgmap sr s)), i:deliver(d), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp (n1 \<parallel> n2))"
      proof
        assume "i\<in>net_ips s1"
        with \<open>s = SubnetS s1 s2\<close> \<open>s' = SubnetS s1' s2'\<close> \<open>net_ip_action np (i:deliver(d)) i (n1 \<parallel> n2) s s'\<close>
          have "(s1, i:deliver(d), s1') \<in> trans (pnet np n1)"
           and "net_ip_action np (i:deliver(d)) i n1 s1 s1'"
           and "s2' = s2" by simp_all

        from \<open>net_ips s1 = net_tree_ips n1\<close> and \<open>(s1, i:deliver(d), s1') \<in> trans (pnet np n1)\<close>
          have "net_ips s1' = net_tree_ips n1" by (metis pnet_maintains_dom)

        from nm' [simplified \<open>s' = SubnetS s1' s2'\<close> \<open>s2' = s2\<close>]
                        \<open>net_tree_ips n1 \<inter> net_tree_ips n2 = {}\<close>
                        \<open>net_ips s1' = net_tree_ips n1\<close>
                        \<open>net_ips s2 = net_tree_ips n2\<close>
          have "netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))"
            by (rule netgmap_subnet_split1)

        from \<open>(s1, i:deliver(d), s1') \<in> trans (pnet np n1)\<close>
             \<open>netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))\<close>
             \<open>netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))\<close>
             \<open>s1 \<in> reachable (pnet np n1) TT\<close>
             \<open>wf_net_tree n1\<close>
             \<open>i\<in>net_ips s1\<close>
             \<open>net_ip_action np (i:deliver(d)) i n1 s1 s1'\<close>
          have "((\<sigma>, snd (netgmap sr s1)), i:deliver(d), (\<sigma>', snd (netgmap sr s1'))) \<in> trans (opnet onp n1)"
             by (rule IH1)

        with \<open>s = SubnetS s1 s2\<close> \<open>s' = SubnetS s1' s2'\<close> \<open>s2' = s2\<close> show ?thesis
          by simp (erule opnet_deliver1)
      next
        assume "i\<in>net_ips s2"
        with \<open>s = SubnetS s1 s2\<close> \<open>s' = SubnetS s1' s2'\<close> \<open>net_ip_action np (i:deliver(d)) i (n1 \<parallel> n2) s s'\<close>
          have "(s2, i:deliver(d), s2') \<in> trans (pnet np n2)"
           and "net_ip_action np (i:deliver(d)) i n2 s2 s2'"
           and "s1' = s1" by simp_all

        from \<open>net_ips s2 = net_tree_ips n2\<close> and \<open>(s2, i:deliver(d), s2') \<in> trans (pnet np n2)\<close>
          have "net_ips s2' = net_tree_ips n2" by (metis pnet_maintains_dom)

        from nm' [simplified \<open>s' = SubnetS s1' s2'\<close> \<open>s1' = s1\<close>]
                        \<open>net_ips s1 = net_tree_ips n1\<close>
                        \<open>net_ips s2' = net_tree_ips n2\<close>
          have "netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))"
            by (rule netgmap_subnet_split2)

        from \<open>(s2, i:deliver(d), s2') \<in> trans (pnet np n2)\<close>
             \<open>netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))\<close>
             \<open>netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))\<close>
             \<open>s2 \<in> reachable (pnet np n2) TT\<close>
             \<open>wf_net_tree n2\<close>
             \<open>i\<in>net_ips s2\<close>
             \<open>net_ip_action np (i:deliver(d)) i n2 s2 s2'\<close>
          have "((\<sigma>, snd (netgmap sr s2)), i:deliver(d), (\<sigma>', snd (netgmap sr s2'))) \<in> trans (opnet onp n2)"
             by (rule IH2)

        with \<open>s = SubnetS s1 s2\<close> \<open>s' = SubnetS s1' s2'\<close> \<open>s1' = s1\<close> show ?thesis
          by simp (erule opnet_deliver2)
      qed
    qed
    with \<open>\<zeta> = snd (netgmap sr s)\<close> have "((\<sigma>, \<zeta>), i:deliver(d), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
      by simp
    moreover from \<open>\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j\<close> \<open>i \<in> net_ips s\<close> \<open>\<zeta> = snd (netgmap sr s)\<close>
      have "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j" by (metis net_ips_netgmap)
    ultimately have "((\<sigma>, \<zeta>), i:deliver(d), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)
                     \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                     \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
      using \<open>netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))\<close> by simp
    thus "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), i:deliver(d), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                  \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                  \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')" by auto
  qed

lemma transfer_arrive':
  assumes "(s, H\<not>K:arrive(m), s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s  = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
      and "wf_net_tree n"
  shows "((\<sigma>, \<zeta>), H\<not>K:arrive(m), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
  proof -

    from assms(2) have "net_ips s = net_tree_ips n" ..
    with assms(1) have "net_ips s' = net_tree_ips n"
      by (metis pnet_maintains_dom)

    from \<open>netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)\<close>
      have "\<zeta> = snd (netgmap sr s)" by simp

    from \<open>netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')\<close>
      have "\<zeta>' = snd (netgmap sr s')"
       and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
         by simp_all

    from assms(1-3) \<open>netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))\<close> assms(5)
      have "((\<sigma>, snd (netgmap sr s)), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
      proof (induction n arbitrary: s s' \<zeta> H K)
        fix ii R\<^sub>i ns ns' \<zeta> H K
        assume "(ns, H\<not>K:arrive(m), ns') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
           and nsr: "ns \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
           and "netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)"
           and "netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))"
        from this(1) have "(ns, H\<not>K:arrive(m), ns') \<in> node_sos (trans (np ii))"
          by (simp add: node_comps)
        moreover with nsr obtain s s' R where "ns  = NodeS ii s R"
                                          and "ns' = NodeS ii s' R"
          by (metis net_node_reachable_is_node node_arriveTE')
        ultimately have "(NodeS ii s R, H\<not>K:arrive(m), NodeS ii s' R) \<in> node_sos (trans (np ii))"
          by simp
        from this(1) have "((\<sigma>, NodeS ii (snd (sr s)) R), H\<not>K:arrive(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
        proof (rule node_arriveTE)
          assume "(s, receive m, s') \<in> trans (np ii)"
             and "H = {ii}"
             and "K = {}"
          from \<open>netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)\<close> and \<open>ns  = NodeS ii s R\<close>
            have "\<sigma> ii = fst (sr s)"
              by simp (metis map_upd_Some_unfold)
          moreover from \<open>netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))\<close>
                        and \<open>ns' = NodeS ii s' R\<close>
            have "\<sigma>' ii = fst (sr s')" by simp (metis map_upd_Some_unfold)
          ultimately have "((\<sigma>, snd (sr s)), receive m, (\<sigma>', snd (sr s'))) \<in> trans (onp ii)"
            using \<open>(s, receive m, s') \<in> trans (np ii)\<close> by (rule trans)
          hence "((\<sigma>, NodeS ii (snd (sr s)) R), {ii}\<not>{}:arrive(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
            by (rule onode_receive)
          with \<open>H={ii}\<close> and \<open>K={}\<close>
            show "((\<sigma>, NodeS ii (snd (sr s)) R), H\<not>K:arrive(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
              by simp
        next
          assume "H = {}"
             and "s = s'"
             and "K = {ii}"
          from \<open>s = s'\<close> \<open>netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))\<close>
                        \<open>netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)\<close>
                        \<open>ns = NodeS ii s R\<close> and \<open>ns' = NodeS ii s' R\<close>
            have "\<sigma>' ii = \<sigma> ii" by simp (metis option.sel)
          hence "((\<sigma>, NodeS ii (snd (sr s)) R), {}\<not>{ii}:arrive(m), (\<sigma>', NodeS ii (snd (sr s)) R))
                                                                      \<in> onode_sos (trans (onp ii))"
            by (rule onode_arrive)
          with \<open>H={}\<close> \<open>K={ii}\<close> and \<open>s = s'\<close>
            show "((\<sigma>, NodeS ii (snd (sr s)) R), H\<not>K:arrive(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
              by simp
        qed
      with \<open>ns = NodeS ii s R\<close> \<open>ns' = NodeS ii s' R\<close>
        show "((\<sigma>, snd (netgmap sr ns)), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr ns')))
                                                             \<in> trans (opnet onp \<langle>ii; R\<^sub>i\<rangle>)"
          by (simp add: onode_comps)
    next
      fix n1 n2 s s' \<zeta> H K
      assume IH1: "\<And>s s' \<zeta> H K. (s, H\<not>K:arrive(m), s') \<in> trans (pnet np n1)
                         \<Longrightarrow> s \<in> reachable (pnet np n1) TT
                         \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n1) (\<sigma>, \<zeta>)
                         \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s'))
                         \<Longrightarrow> wf_net_tree n1
                         \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), H\<not>K:arrive(m), \<sigma>', snd (netgmap sr s'))
                                                                        \<in> trans (opnet onp n1)"
        and IH2: "\<And>s s' \<zeta> H K. (s, H\<not>K:arrive(m), s') \<in> trans (pnet np n2)
                         \<Longrightarrow> s \<in> reachable (pnet np n2) TT
                         \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n2) (\<sigma>, \<zeta>)
                         \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s'))
                         \<Longrightarrow> wf_net_tree n2
                         \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), H\<not>K:arrive(m), \<sigma>', snd (netgmap sr s'))
                                                                        \<in> trans (opnet onp n2)"
        and "(s, H\<not>K:arrive(m), s') \<in> trans (pnet np (n1 \<parallel> n2))"
        and sr: "s \<in> reachable (pnet np (n1 \<parallel> n2)) TT"
        and nm: "netgmap sr s = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
        and nm': "netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>', snd (netgmap sr s'))"
        and "wf_net_tree (n1 \<parallel> n2)"
      from this(3) have "(s, H\<not>K:arrive(m), s') \<in> pnet_sos (trans (pnet np n1))
                                                              (trans (pnet np n2))"
        by simp
      thus "((\<sigma>, snd (netgmap sr s)), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr s')))
                                                                   \<in> trans (opnet onp (n1 \<parallel> n2))"
      proof (rule partial_arriveTE)
        fix s1 s1' s2 s2' H1 H2 K1 K2
        assume "s = SubnetS s1 s2"
           and "s' = SubnetS s1' s2'"
           and tr1: "(s1, H1\<not>K1:arrive(m), s1') \<in> trans (pnet np n1)"
           and tr2: "(s2, H2\<not>K2:arrive(m), s2') \<in> trans (pnet np n2)"
           and "H = H1 \<union> H2"
           and "K = K1 \<union> K2"

        from \<open>wf_net_tree (n1 \<parallel> n2)\<close> have "wf_net_tree n1"
                                      and "wf_net_tree n2"
                                      and "net_tree_ips n1 \<inter> net_tree_ips n2 = {}" by auto

        from sr [simplified \<open>s = SubnetS s1 s2\<close>] have "s1 \<in> reachable (pnet np n1) TT"
          by (rule subnet_reachable(1))
        hence "net_ips s1 = net_tree_ips n1" by (rule pnet_net_ips_net_tree_ips)
        with tr1 have "net_ips s1' = net_tree_ips n1" by (metis pnet_maintains_dom)

        from sr [simplified \<open>s = SubnetS s1 s2\<close>] have "s2 \<in> reachable (pnet np n2) TT"
          by (rule subnet_reachable(2))
        hence "net_ips s2 = net_tree_ips n2" by (rule pnet_net_ips_net_tree_ips)
        with tr2 have "net_ips s2' = net_tree_ips n2" by (metis pnet_maintains_dom)

        from \<open>(s1, H1\<not>K1:arrive(m), s1') \<in> trans (pnet np n1)\<close>
             \<open>s1 \<in> reachable (pnet np n1) TT\<close>
          have "((\<sigma>, snd (netgmap sr s1)), H1\<not>K1:arrive(m), (\<sigma>', snd (netgmap sr s1')))
                                                                            \<in> trans (opnet onp n1)"
          proof (rule IH1 [OF _ _ _ _ \<open>wf_net_tree n1\<close>])
            from nm [simplified \<open>s = SubnetS s1 s2\<close>]
                 \<open>net_tree_ips n1 \<inter> net_tree_ips n2 = {}\<close>
                 \<open>net_ips s1 = net_tree_ips n1\<close>
                 \<open>net_ips s2 = net_tree_ips n2\<close> 
              show "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
                by (rule netgmap_subnet_split1)
          next
            from nm' [simplified \<open>s' = SubnetS s1' s2'\<close>]
                 \<open>net_tree_ips n1 \<inter> net_tree_ips n2 = {}\<close>
                 \<open>net_ips s1' = net_tree_ips n1\<close>
                 \<open>net_ips s2' = net_tree_ips n2\<close> 
              show "netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))"
                by (rule netgmap_subnet_split1)
          qed

        moreover from \<open>(s2, H2\<not>K2:arrive(m), s2') \<in> trans (pnet np n2)\<close>
                      \<open>s2 \<in> reachable (pnet np n2) TT\<close>
          have "((\<sigma>, snd (netgmap sr s2)), H2\<not>K2:arrive(m), (\<sigma>', snd (netgmap sr s2')))
                                                                            \<in> trans (opnet onp n2)"
          proof (rule IH2 [OF _ _ _ _ \<open>wf_net_tree n2\<close>])
            from nm [simplified \<open>s = SubnetS s1 s2\<close>]
                 \<open>net_ips s1 = net_tree_ips n1\<close>
                 \<open>net_ips s2 = net_tree_ips n2\<close> 
              show "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
                by (rule netgmap_subnet_split2)
          next
            from nm' [simplified \<open>s' = SubnetS s1' s2'\<close>]
                 \<open>net_ips s1' = net_tree_ips n1\<close>
                 \<open>net_ips s2' = net_tree_ips n2\<close> 
              show "netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))"
                by (rule netgmap_subnet_split2)
          qed
        ultimately show "((\<sigma>, snd (netgmap sr s)), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr s')))
                                                                     \<in> trans (opnet onp (n1 \<parallel> n2))"
          using \<open>s = SubnetS s1 s2\<close> \<open>s' = SubnetS s1' s2'\<close> \<open>H = H1 \<union> H2\<close> \<open>K = K1 \<union> K2\<close>
            by simp (rule opnet_sos.opnet_arrive)
      qed
    qed
    with \<open>\<zeta> = snd (netgmap sr s)\<close> and \<open>\<zeta>' = snd (netgmap sr s')\<close>
      show "((\<sigma>, \<zeta>), H\<not>K:arrive(m), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
        by simp
  qed

lemma transfer_arrive:
  assumes "(s, H\<not>K:arrive(m), s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s  = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), H\<not>K:arrive(m), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    define \<sigma>' where "\<sigma>' i = (if i\<in>net_tree_ips n then the (fst (netgmap sr s') i) else \<sigma> i)" for i

    from assms(2) have "net_ips s = net_tree_ips n"
      by (rule pnet_net_ips_net_tree_ips)
    with assms(1) have "net_ips s' = net_tree_ips n"
      by (metis pnet_maintains_dom)

    have "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
    proof (rule prod_eqI)
      from \<open>net_ips s' = net_tree_ips n\<close>
        show "fst (netgmap sr s') = fst (netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s')))"
          unfolding \<sigma>'_def [abs_def] by - (rule ext, clarsimp)
    qed simp

    moreover with assms(1-3)
    have "((\<sigma>, \<zeta>), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
      using \<open>wf_net_tree n\<close> by (rule transfer_arrive')

    moreover have "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
    proof -
      have "\<forall>j. j\<notin>net_tree_ips n \<longrightarrow> \<sigma>' j = \<sigma> j" unfolding \<sigma>'_def by simp
      with assms(3) and \<open>net_ips s = net_tree_ips n\<close>
        show ?thesis
          by clarsimp (metis (mono_tags) net_ips_netgmap snd_conv)
    qed

    ultimately show "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), H\<not>K:arrive(m), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                          \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                          \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')" by auto
  qed

lemma transfer_cast:
  assumes "(s, mR:*cast(m), s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), mR:*cast(m), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    define \<sigma>' where "\<sigma>' i = (if i\<in>net_tree_ips n then the (fst (netgmap sr s') i) else \<sigma> i)" for i

    from assms(2) have "net_ips s = net_tree_ips n" ..
    with assms(1) have "net_ips s' = net_tree_ips n"
      by (metis pnet_maintains_dom)
    have "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
    proof (rule prod_eqI)
      from \<open>net_ips s' = net_tree_ips n\<close>
        show "fst (netgmap sr s') = fst (netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s')))"
      unfolding \<sigma>'_def [abs_def] by - (rule ext, clarsimp simp add: some_the_fst_netgmap)
    qed simp

    from \<open>net_ips s' = net_tree_ips n\<close> and \<open>net_ips s = net_tree_ips n\<close> 
      have "\<forall>j. j\<notin>net_ips (snd (netgmap sr s)) \<longrightarrow> \<sigma>' j = \<sigma> j"
        unfolding \<sigma>'_def by simp

    from \<open>netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)\<close>
      have "\<zeta> = snd (netgmap sr s)" by simp

    from assms(1-3) \<open>netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))\<close> assms(4)
      have "((\<sigma>, snd (netgmap sr s)), mR:*cast(m), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
      proof (induction n arbitrary: s s' \<zeta> mR)
        fix ii R\<^sub>i ns ns' \<zeta> mR
        assume "(ns, mR:*cast(m), ns') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
           and nsr: "ns \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
           and "netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)"
           and "netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))"
        from this(1) have "(ns, mR:*cast(m), ns') \<in> node_sos (trans (np ii))"
          by (simp add: node_comps)
        moreover with nsr obtain s s' R where "ns  = NodeS ii s R"
                                          and "ns' = NodeS ii s' R"
          by (metis net_node_reachable_is_node node_castTE')
        ultimately have "(NodeS ii s R, mR:*cast(m), NodeS ii s' R) \<in> node_sos (trans (np ii))"
          by simp

        from \<open>netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)\<close> and \<open>ns  = NodeS ii s R\<close>
          have "\<sigma> ii = fst (sr s)"
            by simp (metis map_upd_Some_unfold)
        from \<open>netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))\<close>
             and \<open>ns' = NodeS ii s' R\<close>
          have "\<sigma>' ii = fst (sr s')" by simp (metis map_upd_Some_unfold)

        from \<open>(NodeS ii s R, mR:*cast(m), NodeS ii s' R) \<in> node_sos (trans (np ii))\<close>
          have "((\<sigma>, NodeS ii (snd (sr s)) R), mR:*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
        proof (rule node_castTE)
          assume "(s, broadcast m, s') \<in> trans (np ii)"
             and "R = mR"
          from \<open>\<sigma> ii = fst (sr s)\<close> \<open>\<sigma>' ii = fst (sr s')\<close> and this(1)
            have "((\<sigma>, snd (sr s)), broadcast m, (\<sigma>', snd (sr s'))) \<in> trans (onp ii)"
              by (rule trans)
          hence "((\<sigma>, NodeS ii (snd (sr s)) R), R:*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
            by (rule onode_bcast)
          with \<open>R=mR\<close> show "((\<sigma>, NodeS ii (snd (sr s)) R), mR:*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
              by simp
        next
          fix D
          assume "(s, groupcast D m, s') \<in> trans (np ii)"
             and "mR = R \<inter> D"
          from \<open>\<sigma> ii = fst (sr s)\<close> \<open>\<sigma>' ii = fst (sr s')\<close> and this(1)
            have "((\<sigma>, snd (sr s)), groupcast D m, (\<sigma>', snd (sr s'))) \<in> trans (onp ii)"
              by (rule trans)
          hence "((\<sigma>, NodeS ii (snd (sr s)) R), (R \<inter> D):*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
            by (rule onode_gcast)
          with \<open>mR = R \<inter> D\<close> show "((\<sigma>, NodeS ii (snd (sr s)) R), mR:*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
              by simp
        next
          fix d
          assume "(s, unicast d m, s') \<in> trans (np ii)"
             and "d \<in> R"
             and "mR = {d}"
          from \<open>\<sigma> ii = fst (sr s)\<close> \<open>\<sigma>' ii = fst (sr s')\<close> and this(1)
            have "((\<sigma>, snd (sr s)), unicast d m, (\<sigma>', snd (sr s'))) \<in> trans (onp ii)"
              by (rule trans)
          hence "((\<sigma>, NodeS ii (snd (sr s)) R), {d}:*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
            using \<open>d\<in>R\<close> by (rule onode_ucast)
          with \<open>mR={d}\<close> show "((\<sigma>, NodeS ii (snd (sr s)) R), mR:*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
            by simp
        qed
      with \<open>ns = NodeS ii s R\<close> \<open>ns' = NodeS ii s' R\<close>
        show "((\<sigma>, snd (netgmap sr ns)), mR:*cast(m), (\<sigma>', snd (netgmap sr ns')))
                                                             \<in> trans (opnet onp \<langle>ii; R\<^sub>i\<rangle>)"
          by (simp add: onode_comps)
    next
      fix n1 n2 s s' \<zeta> mR
      assume IH1: "\<And>s s' \<zeta> mR. (s, mR:*cast(m), s') \<in> trans (pnet np n1)
                         \<Longrightarrow> s \<in> reachable (pnet np n1) TT
                         \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n1) (\<sigma>, \<zeta>)
                         \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s'))
                         \<Longrightarrow> wf_net_tree n1
                         \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), mR:*cast(m), \<sigma>', snd (netgmap sr s'))
                                                                        \<in> trans (opnet onp n1)"
        and IH2: "\<And>s s' \<zeta> mR. (s, mR:*cast(m), s') \<in> trans (pnet np n2)
                         \<Longrightarrow> s \<in> reachable (pnet np n2) TT
                         \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n2) (\<sigma>, \<zeta>)
                         \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s'))
                         \<Longrightarrow> wf_net_tree n2
                         \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), mR:*cast(m), \<sigma>', snd (netgmap sr s'))
                                                                        \<in> trans (opnet onp n2)"
        and "(s, mR:*cast(m), s') \<in> trans (pnet np (n1 \<parallel> n2))"
        and sr: "s \<in> reachable (pnet np (n1 \<parallel> n2)) TT"
        and nm: "netgmap sr s = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
        and nm': "netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>', snd (netgmap sr s'))"
        and "wf_net_tree (n1 \<parallel> n2)"
      from this(3) have "(s, mR:*cast(m), s') \<in> pnet_sos (trans (pnet np n1)) (trans (pnet np n2))"
        by simp
      then obtain s1 s1' s2 s2' H K
        where "s  = SubnetS s1  s2"
          and "s' = SubnetS s1' s2'"
          and "H \<subseteq> mR"
          and "K \<inter> mR = {}"
          and trtr: "((s1, mR:*cast(m), s1') \<in> trans (pnet np n1)
                                  \<and> (s2, H\<not>K:arrive(m), s2') \<in> trans (pnet np n2))
                    \<or> ((s1, H\<not>K:arrive(m), s1') \<in> trans (pnet np n1)
                                  \<and> (s2, mR:*cast(m), s2') \<in> trans (pnet np n2))"
          by (rule partial_castTE) metis+

      from \<open>wf_net_tree (n1 \<parallel> n2)\<close> have "wf_net_tree n1"
                                    and "wf_net_tree n2"
                                    and "net_tree_ips n1 \<inter> net_tree_ips n2 = {}" by auto

      from sr [simplified \<open>s = SubnetS s1 s2\<close>] have "s1 \<in> reachable (pnet np n1) TT"
        by (rule subnet_reachable(1))
      hence "net_ips s1 = net_tree_ips n1" by (rule pnet_net_ips_net_tree_ips)
      with trtr have "net_ips s1' = net_tree_ips n1" by (metis pnet_maintains_dom)

      from sr [simplified \<open>s = SubnetS s1 s2\<close>] have "s2 \<in> reachable (pnet np n2) TT"
        by (rule subnet_reachable(2))
      hence "net_ips s2 = net_tree_ips n2" by (rule pnet_net_ips_net_tree_ips)
      with trtr have "net_ips s2' = net_tree_ips n2" by (metis pnet_maintains_dom)

      from nm [simplified \<open>s = SubnetS s1 s2\<close>]
           \<open>net_tree_ips n1 \<inter> net_tree_ips n2 = {}\<close>
           \<open>net_ips s1 = net_tree_ips n1\<close>
           \<open>net_ips s2 = net_tree_ips n2\<close> 
        have "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
          by (rule netgmap_subnet_split1)

      from nm' [simplified \<open>s' = SubnetS s1' s2'\<close>]
           \<open>net_tree_ips n1 \<inter> net_tree_ips n2 = {}\<close>
           \<open>net_ips s1' = net_tree_ips n1\<close>
           \<open>net_ips s2' = net_tree_ips n2\<close> 
        have "netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))"
          by (rule netgmap_subnet_split1)

      from nm [simplified \<open>s = SubnetS s1 s2\<close>]
           \<open>net_ips s1 = net_tree_ips n1\<close>
           \<open>net_ips s2 = net_tree_ips n2\<close> 
        have "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
          by (rule netgmap_subnet_split2)

      from nm' [simplified \<open>s' = SubnetS s1' s2'\<close>]
           \<open>net_ips s1' = net_tree_ips n1\<close>
           \<open>net_ips s2' = net_tree_ips n2\<close> 
        have "netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))"
          by (rule netgmap_subnet_split2)

      from trtr show "((\<sigma>, snd (netgmap sr s)), mR:*cast(m), (\<sigma>', snd (netgmap sr s')))
                                                              \<in> trans (opnet onp (n1 \<parallel> n2))"
      proof (elim disjE conjE)
        assume "(s1, mR:*cast(m), s1') \<in> trans (pnet np n1)"
           and "(s2, H\<not>K:arrive(m), s2') \<in> trans (pnet np n2)"
        from \<open>(s1, mR:*cast(m), s1') \<in> trans (pnet np n1)\<close>
             \<open>s1 \<in> reachable (pnet np n1) TT\<close>
             \<open>netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))\<close>
             \<open>netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))\<close>
             \<open>wf_net_tree n1\<close>
          have "((\<sigma>, snd (netgmap sr s1)), mR:*cast(m), (\<sigma>', snd (netgmap sr s1'))) \<in> trans (opnet onp n1)"
            by (rule IH1)

        moreover from \<open>(s2, H\<not>K:arrive(m), s2') \<in> trans (pnet np n2)\<close>
             \<open>s2 \<in> reachable (pnet np n2) TT\<close>
             \<open>netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))\<close>
             \<open>netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))\<close>
             \<open>wf_net_tree n2\<close>
          have "((\<sigma>, snd (netgmap sr s2)), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr s2'))) \<in> trans (opnet onp n2)"
            by (rule transfer_arrive')

        ultimately have "((\<sigma>, SubnetS (snd (netgmap sr s1)) (snd (netgmap sr s2))), mR:*cast(m),
                          (\<sigma>', SubnetS (snd (netgmap sr s1')) (snd (netgmap sr s2'))))
                             \<in> opnet_sos (trans (opnet onp n1)) (trans (opnet onp n2))"
          using \<open>H \<subseteq> mR\<close> and \<open>K \<inter> mR = {}\<close> by (rule opnet_sos.intros(1))
        with \<open>s = SubnetS s1 s2\<close> \<open>s' = SubnetS s1' s2'\<close> show ?thesis by simp
      next
        assume "(s1, H\<not>K:arrive(m), s1') \<in> trans (pnet np n1)"
           and "(s2, mR:*cast(m), s2') \<in> trans (pnet np n2)"
        from \<open>(s1, H\<not>K:arrive(m), s1') \<in> trans (pnet np n1)\<close>
             \<open>s1 \<in> reachable (pnet np n1) TT\<close>
             \<open>netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))\<close>
             \<open>netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))\<close>
             \<open>wf_net_tree n1\<close>
          have "((\<sigma>, snd (netgmap sr s1)), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr s1'))) \<in> trans (opnet onp n1)"
            by (rule transfer_arrive')

        moreover from \<open>(s2, mR:*cast(m), s2') \<in> trans (pnet np n2)\<close>
             \<open>s2 \<in> reachable (pnet np n2) TT\<close>
             \<open>netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))\<close>
             \<open>netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))\<close>
             \<open>wf_net_tree n2\<close>
          have "((\<sigma>, snd (netgmap sr s2)), mR:*cast(m), (\<sigma>', snd (netgmap sr s2'))) \<in> trans (opnet onp n2)"
            by (rule IH2)

        ultimately have "((\<sigma>, SubnetS (snd (netgmap sr s1)) (snd (netgmap sr s2))), mR:*cast(m),
                          (\<sigma>', SubnetS (snd (netgmap sr s1')) (snd (netgmap sr s2'))))
                             \<in> opnet_sos (trans (opnet onp n1)) (trans (opnet onp n2))"
          using \<open>H \<subseteq> mR\<close> and \<open>K \<inter> mR = {}\<close> by (rule opnet_sos.intros(2))
        with \<open>s = SubnetS s1 s2\<close> \<open>s' = SubnetS s1' s2'\<close> show ?thesis by simp
      qed
    qed
    with \<open>\<zeta> = snd (netgmap sr s)\<close> have "((\<sigma>, \<zeta>), mR:*cast(m), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
      by simp
    moreover from \<open>\<forall>j. j\<notin>net_ips (snd (netgmap sr s)) \<longrightarrow> \<sigma>' j = \<sigma> j\<close> \<open>\<zeta> = snd (netgmap sr s)\<close>
      have "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j" by simp
    moreover note \<open>netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))\<close>
    ultimately show "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), mR:*cast(m), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                           \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                           \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
      by auto
  qed

lemma transfer_pnet_action:
  assumes "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
      and "(s, a, s') \<in> trans (pnet np n)"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    show "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                  \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                  \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
    proof (cases a)
      case node_cast
      with assms(4) show ?thesis
        by (auto elim!: transfer_cast [OF _ assms(1-3)])
    next
      case node_deliver
      with assms(4) show ?thesis
        by (auto elim!: transfer_deliver [OF _ assms(1-3)])
    next
      case node_arrive
      with assms(4) show ?thesis
        by (auto elim!: transfer_arrive [OF _ assms(1-3)])
    next
      case node_connect
      with assms(4) show ?thesis
        by (auto elim!: transfer_connect [OF _ assms(1-3)])
    next
      case node_disconnect
      with assms(4) show ?thesis
        by (auto elim!: transfer_disconnect [OF _ assms(1-3)])
    next
      case node_newpkt
      with assms(4) have False by (metis pnet_never_newpkt)
      thus ?thesis ..
    next
      case node_tau
      with assms(4) show ?thesis
        by (auto elim!: transfer_tau [OF _ assms(1-3), simplified])
    qed
  qed

lemma transfer_action_pnet_closed:
  assumes "(s, a, s') \<in> trans (closed (pnet np n))"
  obtains a' where "(s, a', s') \<in> trans (pnet np n)"
               and "\<And>\<sigma> \<zeta> \<sigma>' \<zeta>'. \<lbrakk> ((\<sigma>, \<zeta>), a', (\<sigma>', \<zeta>')) \<in> trans (opnet onp n);
                                  (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j) \<rbrakk>
                            \<Longrightarrow> ((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp n))"
  proof (atomize_elim)
    from assms have "(s, a, s') \<in> cnet_sos (trans (pnet np n))" by simp
    thus "\<exists>a'. (s, a', s') \<in> trans (pnet np n)
                \<and> (\<forall>\<sigma> \<zeta> \<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), a', (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                               \<longrightarrow> (\<forall>j. j \<notin> net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                               \<longrightarrow> ((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp n)))"
    proof cases
      case (cnet_cast R m) thus ?thesis
      by (auto intro!: exI [where x="R:*cast(m)"] dest!: ocnet_cast)
    qed (auto intro!: ocnet_sos.intros [simplified])
  qed

lemma transfer_action:
  assumes "s \<in> reachable (closed (pnet np n)) TT"
      and "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
      and "(s, a, s') \<in> trans (closed (pnet np n))"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp n))"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    from assms(1) have "s \<in> reachable (pnet np n) TT" ..
    from assms(4)
      show "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp n))
                    \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
        by (cases a)
           ((elim transfer_action_pnet_closed
                  transfer_pnet_action [OF \<open>s \<in> reachable (pnet np n) TT\<close> assms(2-3)])?,
            (auto intro!: exI)[1])+
  qed

lemma pnet_reachable_transfer':
  assumes "wf_net_tree n"
      and "s \<in> reachable (closed (pnet np n)) TT"
    shows "netgmap sr s \<in> netmask (net_tree_ips n) ` oreachable (oclosed (opnet onp n)) (\<lambda>_ _ _. True) U"
          (is " _ \<in> ?f ` ?oreachable n")
  using assms(2) proof induction
    fix s
    assume "s \<in> init (closed (pnet np n))"
    hence "s \<in> init (pnet np n)" by simp
    with \<open>wf_net_tree n\<close> have "netgmap sr s \<in> netmask (net_tree_ips n) ` init (opnet onp n)"
      by (rule init_pnet_opnet)
    hence "netgmap sr s \<in> netmask (net_tree_ips n) ` init (oclosed (opnet onp n))"
      by simp
    moreover have "netmask (net_tree_ips n) ` init (oclosed (opnet onp n))
                                        \<subseteq> netmask (net_tree_ips n) ` ?oreachable n"
      by (intro image_mono subsetI) (rule oreachable_init)
    ultimately show "netgmap sr s \<in> netmask (net_tree_ips n) ` ?oreachable n"
      by (rule rev_subsetD)
  next
    fix s a s'
    assume "s \<in> reachable (closed (pnet np n)) TT"
       and "netgmap sr s \<in> netmask (net_tree_ips n) ` ?oreachable n"
       and "(s, a, s') \<in> trans (closed (pnet np n))"
    from this(2) obtain \<sigma> \<zeta> where "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
                              and "(\<sigma>, \<zeta>) \<in> ?oreachable n"
      by clarsimp
    from \<open>s \<in> reachable (closed (pnet np n)) TT\<close> this(1) \<open>wf_net_tree n\<close>
         and \<open>(s, a, s') \<in> trans (closed (pnet np n))\<close>
      obtain \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp n))"
                     and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
        by (rule transfer_action)
    from \<open>(\<sigma>, \<zeta>) \<in> ?oreachable n\<close> and this(1) have "(\<sigma>', \<zeta>') \<in> ?oreachable n"
      by (rule oreachable_local) simp
    with \<open>netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')\<close>
      show "netgmap sr s' \<in> netmask (net_tree_ips n) ` ?oreachable n" by (rule image_eqI)
  qed

definition
  someinit :: "nat \<Rightarrow> 'g"
where
  "someinit i \<equiv> SOME x. x \<in> (fst o sr) ` init (np i)"

definition
  initmissing :: "((nat \<Rightarrow> 'g option) \<times> 'a) \<Rightarrow> (nat \<Rightarrow> 'g) \<times> 'a"
where
  "initmissing \<sigma> = (\<lambda>i. case (fst \<sigma>) i of None \<Rightarrow> someinit i | Some s \<Rightarrow> s, snd \<sigma>)"

lemma initmissing_def':
  "initmissing = apfst (default someinit)"
  by (auto simp add: initmissing_def default_def)

lemma netmask_initmissing_netgmap:
  "netmask (net_ips s) (initmissing (netgmap sr s)) = netgmap sr s"
  proof (intro prod_eqI ext)
    fix i
    show "fst (netmask (net_ips s) (initmissing (netgmap sr s))) i = fst (netgmap sr s) i"
      unfolding initmissing_def by (clarsimp split: option.split)
  qed (simp add: initmissing_def)

lemma snd_initmissing [simp]:
  "snd (initmissing x)= snd x"
  unfolding initmissing_def by simp

lemma initmnissing_snd_netgmap [simp]:
  assumes "initmissing (netgmap sr s) = (\<sigma>, \<zeta>)"
    shows "snd (netgmap sr s) = \<zeta>"
  using assms unfolding initmissing_def by simp


lemma in_net_ips_fst_init_missing [simp]:
  assumes "i \<in> net_ips s"
    shows "fst (initmissing (netgmap sr s)) i = the (fst (netgmap sr s) i)"
  using assms unfolding initmissing_def by (clarsimp split: option.split)

lemma not_in_net_ips_fst_init_missing [simp]:
  assumes "i \<notin> net_ips s"
    shows "fst (initmissing (netgmap sr s)) i = someinit i"
  using assms unfolding initmissing_def by (clarsimp split: option.split)

lemma initmissing_oreachable_netmask [elim]:
  assumes "initmissing (netgmap sr s) \<in> oreachable (oclosed (opnet onp n)) (\<lambda>_ _ _. True) U"
          (is "_ \<in> ?oreachable n")
      and "net_ips s = net_tree_ips n"
    shows "netgmap sr s \<in> netmask (net_tree_ips n) ` ?oreachable n"
  proof -
    obtain \<sigma> \<zeta> where "initmissing (netgmap sr s) = (\<sigma>, \<zeta>)" by (metis surj_pair)
    with assms(1) have "(\<sigma>, \<zeta>) \<in> ?oreachable n" by simp

    have "netgmap sr s = netmask (net_ips s) (\<sigma>, \<zeta>)"
    proof (intro prod_eqI ext)
      fix i
      show "fst (netgmap sr s) i = fst (netmask (net_ips s) (\<sigma>, \<zeta>)) i"
      proof (cases "i\<in>net_ips s")
        assume "i\<in>net_ips s"
        hence "fst (initmissing (netgmap sr s)) i = the (fst (netgmap sr s) i)"
          by (rule in_net_ips_fst_init_missing)
        moreover from \<open>i\<in>net_ips s\<close> have "Some (the (fst (netgmap sr s) i)) = fst (netgmap sr s) i"
          by (rule some_the_fst_netgmap)
        ultimately show ?thesis
          using \<open>initmissing (netgmap sr s) = (\<sigma>, \<zeta>)\<close> by simp
      qed simp
    next
      from \<open>initmissing (netgmap sr s) = (\<sigma>, \<zeta>)\<close>
        show "snd (netgmap sr s) = snd (netmask (net_ips s) (\<sigma>, \<zeta>))"
          by simp
    qed
    with assms(2) have "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)" by simp
    moreover from \<open>(\<sigma>, \<zeta>) \<in> ?oreachable n\<close>
      have "netmask (net_ips s) (\<sigma>, \<zeta>) \<in> netmask (net_ips s) ` ?oreachable n"
        by (rule imageI)
    ultimately show ?thesis
      by (simp only: assms(2))
  qed

lemma pnet_reachable_transfer:
  assumes "wf_net_tree n"
      and "s \<in> reachable (closed (pnet np n)) TT"
    shows "initmissing (netgmap sr s) \<in> oreachable (oclosed (opnet onp n)) (\<lambda>_ _ _. True) U"
          (is " _ \<in> ?oreachable n")
  using assms(2) proof induction
    fix s
    assume "s \<in> init (closed (pnet np n))"
    hence "s \<in> init (pnet np n)" by simp

    from \<open>wf_net_tree n\<close> have "initmissing (netgmap sr s) \<in> init (opnet onp n)"
    proof (rule init_lifted [THEN subsetD], intro CollectI exI conjI allI)
      show "initmissing (netgmap sr s) = (fst (initmissing (netgmap sr s)), snd (netgmap sr s))"
        by (metis snd_initmissing surjective_pairing)
    next
      from \<open>s \<in> init (pnet np n)\<close> show "s \<in> init (pnet np n)" ..
    next
      fix i
      show "if i \<in> net_tree_ips n
            then (fst (initmissing (netgmap sr s))) i = the (fst (netgmap sr s) i)
            else (fst (initmissing (netgmap sr s))) i \<in> (fst \<circ> sr) ` init (np i)"
      proof (cases "i \<in> net_tree_ips n", simp_all only: if_True if_False)
        assume "i \<in> net_tree_ips n"
        with \<open>s \<in> init (pnet np n)\<close> have "i \<in> net_ips s" ..
        thus "fst (initmissing (netgmap sr s)) i = the (fst (netgmap sr s) i)" by simp
      next
        assume "i \<notin> net_tree_ips n"
        with \<open>s \<in> init (pnet np n)\<close> have "i \<notin> net_ips s" ..
        hence "fst (initmissing (netgmap sr s)) i = someinit i" by simp
        moreover have "someinit i \<in> (fst \<circ> sr) ` init (np i)"
        unfolding someinit_def proof (rule someI_ex)
          from init_notempty show "\<exists>x. x \<in> (fst o sr) ` init (np i)" by auto
        qed
        ultimately show "fst (initmissing (netgmap sr s)) i \<in> (fst \<circ> sr) ` init (np i)"
          by simp
      qed
    qed
    hence "initmissing (netgmap sr s) \<in> init (oclosed (opnet onp n))" by simp
    thus "initmissing (netgmap sr s) \<in> ?oreachable n" ..
  next
    fix s a s'
    assume "s \<in> reachable (closed (pnet np n)) TT"
       and "(s, a, s') \<in> trans (closed (pnet np n))"
       and "initmissing (netgmap sr s) \<in> ?oreachable n"
    from this(1) have "s \<in> reachable (pnet np n) TT" ..
    hence "net_ips s = net_tree_ips n" by (rule pnet_net_ips_net_tree_ips)
    with \<open>initmissing (netgmap sr s) \<in> ?oreachable n\<close>
      have "netgmap sr s \<in> netmask (net_tree_ips n) ` ?oreachable n"
        by (rule initmissing_oreachable_netmask)

    obtain \<sigma> \<zeta> where "(\<sigma>, \<zeta>) = initmissing (netgmap sr s)" by (metis surj_pair)
    with \<open>initmissing (netgmap sr s) \<in> ?oreachable n\<close>
      have "(\<sigma>, \<zeta>) \<in> ?oreachable n" by simp
    from \<open>(\<sigma>, \<zeta>) = initmissing (netgmap sr s)\<close> and \<open>net_ips s = net_tree_ips n\<close> [symmetric]
      have "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
        by (clarsimp simp add: netmask_initmissing_netgmap)

    with \<open>s \<in> reachable (closed (pnet np n)) TT\<close>
      obtain \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp n))"
                     and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
        using \<open>wf_net_tree n\<close> and \<open>(s, a, s') \<in> trans (closed (pnet np n))\<close>
        by (rule transfer_action)

    from \<open>(\<sigma>, \<zeta>) \<in> ?oreachable n\<close> have "net_ips \<zeta> = net_tree_ips n"
      by (rule opnet_net_ips_net_tree_ips [OF oclosed_oreachable_oreachable])
    with \<open>((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp n))\<close>
      have "\<forall>j. j\<notin>net_tree_ips n \<longrightarrow> \<sigma>' j = \<sigma> j"
        by (clarsimp elim!: ocomplete_no_change)
    have "initmissing (netgmap sr s') = (\<sigma>', \<zeta>')"
    proof (intro prod_eqI ext)
      fix i
      from \<open>netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')\<close>
           \<open>\<forall>j. j\<notin>net_tree_ips n \<longrightarrow> \<sigma>' j = \<sigma> j\<close>
           \<open>(\<sigma>, \<zeta>) = initmissing (netgmap sr s)\<close>
           \<open>net_ips s = net_tree_ips n\<close>
      show "fst (initmissing (netgmap sr s')) i = fst (\<sigma>', \<zeta>') i"
        unfolding initmissing_def by simp
    next
      from \<open>netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')\<close>
        show "snd (initmissing (netgmap sr s')) = snd (\<sigma>', \<zeta>')" by simp
    qed
    moreover from \<open>(\<sigma>, \<zeta>) \<in> ?oreachable n\<close> \<open>((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp n))\<close>
      have "(\<sigma>', \<zeta>') \<in> ?oreachable n"
        by (rule oreachable_local) (rule TrueI)

    ultimately show "initmissing (netgmap sr s') \<in> ?oreachable n"
      by simp
  qed

definition
  netglobal :: "((nat \<Rightarrow> 'g) \<Rightarrow> bool) \<Rightarrow> 's net_state \<Rightarrow> bool"
where
  "netglobal P \<equiv> (\<lambda>s. P (fst (initmissing (netgmap sr s))))"

lemma netglobalsimp [simp]:
  "netglobal P s = P (fst (initmissing (netgmap sr s)))"
  unfolding netglobal_def by simp

lemma netglobalE [elim]:
  assumes "netglobal P s"
      and "\<And>\<sigma>. \<lbrakk> P \<sigma>; fst (initmissing (netgmap sr s)) = \<sigma> \<rbrakk> \<Longrightarrow> Q \<sigma>"
    shows "netglobal Q s"
  using assms by simp

lemma netglobal_weakenE [elim]:
  assumes "p \<TTurnstile> netglobal P"
      and "\<And>\<sigma>. P \<sigma> \<Longrightarrow> Q \<sigma>"
    shows "p \<TTurnstile> netglobal Q"
  using assms(1) proof (rule invariant_weakenE)
    fix s
    assume "netglobal P s"
    thus "netglobal Q s"
      by (rule netglobalE) (erule assms(2))
  qed

lemma close_opnet:
  assumes "wf_net_tree n"
      and "oclosed (opnet onp n) \<Turnstile> (\<lambda>_ _ _. True, U \<rightarrow>) global P"
    shows "closed (pnet np n) \<TTurnstile> netglobal P"
  unfolding invariant_def proof
    fix s
    assume "s \<in> reachable (closed (pnet np n)) TT"
    with assms(1)
      have "initmissing (netgmap sr s) \<in> oreachable (oclosed (opnet onp n)) (\<lambda>_ _ _. True) U"
        by (rule pnet_reachable_transfer)
    with assms(2) have "global P (initmissing (netgmap sr s))" ..
    thus "netglobal P s" by simp
  qed

end

locale openproc_parq =
  op?: openproc np onp sr for np :: "ip \<Rightarrow> ('s, ('m::msg) seq_action) automaton" and onp sr
  + fixes qp :: "('t, 'm seq_action) automaton"
    assumes init_qp_notempty: "init qp \<noteq> {}"

sublocale openproc_parq \<subseteq> openproc "\<lambda>i. np i \<langle>\<langle> qp"
                                   "\<lambda>i. onp i \<langle>\<langle>\<^bsub>i\<^esub> qp"
                                   "\<lambda>(p, q). (fst (sr p), (snd (sr p), q))"
  proof unfold_locales
    fix i
    show "{ (\<sigma>, \<zeta>) |\<sigma> \<zeta> s. s \<in> init (np i \<langle>\<langle> qp)
                         \<and> (\<sigma> i, \<zeta>) = ((\<lambda>(p, q). (fst (sr p), (snd (sr p), q))) s)
                         \<and> (\<forall>j. j\<noteq>i \<longrightarrow> \<sigma> j \<in> (fst o (\<lambda>(p, q). (fst (sr p), (snd (sr p), q))))
                                                  ` init (np j \<langle>\<langle> qp)) } \<subseteq> init (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
       (is "?S \<subseteq> _")
    proof
      fix s
      assume "s \<in> ?S"
      then obtain \<sigma> p lq
        where "s = (\<sigma>, (snd (sr p), lq))"
          and "lq \<in> init qp"
          and "p \<in> init (np i)"
          and "\<sigma> i = fst (sr p)"
          and "\<forall>j. j \<noteq> i \<longrightarrow> \<sigma> j \<in> (fst \<circ> (\<lambda>(p, q). (fst (sr p), snd (sr p), q)))
                                                                        ` (init (np j) \<times> init qp)"
        by auto
      from this(5) have "\<forall>j. j \<noteq> i \<longrightarrow> \<sigma> j \<in> (fst \<circ> sr) ` init (np j)"
        by auto
      with \<open>p \<in> init (np i)\<close> and \<open>\<sigma> i = fst (sr p)\<close> have "(\<sigma>, snd (sr p)) \<in> init (onp i)"
        by - (rule init [THEN subsetD], auto)
      with \<open>lq\<in> init qp\<close> have "((\<sigma>, snd (sr p)), lq) \<in> init (onp i) \<times> init qp"
        by simp
      hence "(\<sigma>, (snd (sr p), lq)) \<in> extg ` (init (onp i) \<times> init qp)"
        by (rule rev_image_eqI) simp
      with \<open>s = (\<sigma>, (snd (sr p), lq))\<close> show "s \<in> init (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
        by simp
    qed
  next
    fix i s a s' \<sigma> \<sigma>'
    assume "\<sigma> i = fst ((\<lambda>(p, q). (fst (sr p), (snd (sr p), q))) s)"
       and "\<sigma>' i = fst ((\<lambda>(p, q). (fst (sr p), (snd (sr p), q))) s')"
       and "(s, a, s') \<in> trans (np i \<langle>\<langle> qp)"
    then obtain p q p' q' where "s  = (p, q)"
                            and "s' = (p', q')"
                            and "\<sigma> i  = fst (sr p)"
                            and "\<sigma>' i = fst (sr p')"
      by (clarsimp split: prod.split_asm)
    from this(1-2) and \<open>(s, a, s') \<in> trans (np i \<langle>\<langle> qp)\<close>
      have "((p, q), a, (p', q')) \<in> parp_sos (trans (np i)) (trans qp)" by simp
    hence "((\<sigma>, (snd (sr p), q)), a, (\<sigma>', (snd (sr p'), q'))) \<in> trans (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
    proof cases
      assume "q' = q"
         and "(p, a, p') \<in> trans (np i)"
         and "\<And>m. a \<noteq> receive m"
      from \<open>\<sigma> i = fst (sr p)\<close> and \<open>\<sigma>' i = fst (sr p')\<close> this(2)
        have "((\<sigma>, snd (sr p)), a, (\<sigma>', snd (sr p'))) \<in> trans (onp i)" by (rule trans)
      with \<open>q' = q\<close> and \<open>\<And>m. a \<noteq> receive m\<close>
        show "((\<sigma>, snd (sr p), q), a, (\<sigma>', (snd (sr p'), q'))) \<in> trans (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
          by (auto elim!: oparleft)
    next
      assume "p' = p"
         and "(q, a, q') \<in> trans qp"
         and "\<And>m. a \<noteq> send m"
      with \<open>\<sigma> i = fst (sr p)\<close> and \<open>\<sigma>' i = fst (sr p')\<close>
        show "((\<sigma>, snd (sr p), q), a, (\<sigma>', (snd (sr p'), q'))) \<in> trans (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
          by (auto elim!: oparright)
    next
      fix m
      assume "a = \<tau>"
         and "(p, receive m, p') \<in> trans (np i)"
         and "(q, send m, q') \<in> trans qp"
      from \<open>\<sigma> i = fst (sr p)\<close> and \<open>\<sigma>' i = fst (sr p')\<close> this(2)
        have "((\<sigma>, snd (sr p)), receive m, (\<sigma>', snd (sr p'))) \<in> trans (onp i)"
          by (rule trans)
      with \<open>(q, send m, q') \<in> trans qp\<close> and \<open>a = \<tau>\<close>
        show "((\<sigma>, snd (sr p), q), a, (\<sigma>', (snd (sr p'), q'))) \<in> trans (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
          by (simp del: step_seq_tau) (rule oparboth)
    qed
    with \<open>s = (p, q)\<close> \<open>s' = (p', q')\<close>
      show "((\<sigma>, snd ((\<lambda>(p, q). (fst (sr p), (snd (sr p), q))) s)), a,
                 (\<sigma>', snd ((\<lambda>(p, q). (fst (sr p), (snd (sr p), q))) s'))) \<in> trans (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
        by simp
  next
    show "\<forall>j. init (np j \<langle>\<langle> qp) \<noteq> {}"
      by (clarsimp simp add: init_notempty init_qp_notempty)
  qed

end
