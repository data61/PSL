(*  Title:       ONode_Lifting.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Lifting rules for (open) nodes"

theory ONode_Lifting
imports AWN OAWN_SOS OInvariants
begin

lemma node_net_state':
  assumes "s \<in> oreachable (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o) S U"
    shows "\<exists>\<sigma> \<zeta> R. s = (\<sigma>, NodeS i \<zeta> R)"
  using assms proof induction
    fix s
    assume "s \<in> init (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o)"
    then obtain \<sigma> \<zeta> where "s = (\<sigma>, NodeS i \<zeta> R\<^sub>i)"
      by (auto simp: onode_comps)
    thus "\<exists>\<sigma> \<zeta> R. s = (\<sigma>, NodeS i \<zeta> R)" by auto
  next
    fix s a \<sigma>'
    assume rt: "s \<in> oreachable (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o) S U"
       and ih: "\<exists>\<sigma> \<zeta> R. s = (\<sigma>, NodeS i \<zeta> R)"
       and "U (fst s) \<sigma>'"
    then obtain \<sigma> \<zeta> R
      where "(\<sigma>, NodeS i \<zeta> R)  \<in> oreachable (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o) S U"
        and "U \<sigma> \<sigma>'" and "snd s = NodeS i \<zeta> R" by auto
    from this(1-2)
      have "(\<sigma>', NodeS i \<zeta> R) \<in> oreachable (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o) S U"
        by - (erule(1) oreachable_other')
    with \<open>snd s = NodeS i \<zeta> R\<close> show "\<exists>\<sigma> \<zeta> R. (\<sigma>', snd s) = (\<sigma>, NodeS i \<zeta> R)" by simp
  next
    fix s a s'
    assume rt: "s \<in> oreachable (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o) S U"
       and ih: "\<exists>\<sigma> \<zeta> R. s = (\<sigma>, NodeS i \<zeta> R)"
       and tr: "(s, a, s') \<in> trans (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o)"
       and "S (fst s) (fst s') a"
     from ih obtain \<sigma> \<zeta> R where "s = (\<sigma>, NodeS i \<zeta> R)" by auto
     with tr have "((\<sigma>, NodeS i \<zeta> R), a, s') \<in> onode_sos (trans T)"
       by (simp add: onode_comps)
     then obtain \<sigma>' \<zeta>' R' where "s' = (\<sigma>', NodeS i \<zeta>' R')"
       using onode_sos_dest_is_net_state' by metis
     with tr \<open>s = (\<sigma>, NodeS i \<zeta> R)\<close> show "\<exists>\<sigma> \<zeta> R. s' = (\<sigma>, NodeS i \<zeta> R)"
       by simp
  qed

lemma node_net_state:
  assumes "(\<sigma>, s) \<in> oreachable (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o) S U"
    shows "\<exists>\<zeta> R. s = NodeS i \<zeta> R"
  using assms
  by (metis Pair_inject node_net_state')

lemma node_net_state_trans [elim]:
  assumes sor: "(\<sigma>, s) \<in> oreachable (\<langle>i : \<zeta>\<^sub>i : R\<^sub>i\<rangle>\<^sub>o) S U"
      and str: "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans (\<langle>i : \<zeta>\<^sub>i : R\<^sub>i\<rangle>\<^sub>o)"
  obtains \<zeta> R \<zeta>' R'
    where "s = NodeS i \<zeta> R"
      and "s' = NodeS i \<zeta>' R'"
  proof -
    assume *: "\<And>\<zeta> R \<zeta>' R'. s = NodeS i \<zeta> R \<Longrightarrow> s' = NodeS i \<zeta>' R' \<Longrightarrow> thesis"
    from sor obtain \<zeta> R where "s = NodeS i \<zeta> R"
      by (metis node_net_state)
    moreover with str obtain \<zeta>' R' where "s' = NodeS i \<zeta>' R'"
      by (simp only: onode_comps)
         (metis onode_sos_dest_is_net_state'')
    ultimately show thesis by (rule *)
  qed

lemma nodemap_induct' [consumes, case_names init other local]:
  assumes "(\<sigma>, NodeS ii \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U"
      and init: "\<And>\<sigma> \<zeta>. (\<sigma>, NodeS ii \<zeta> R\<^sub>i) \<in> init (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) \<Longrightarrow> P (\<sigma>, NodeS ii \<zeta> R\<^sub>i)"
      and other: "\<And>\<sigma> \<zeta> R \<sigma>' a.
                  \<lbrakk> (\<sigma>, NodeS ii \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U;
                    U \<sigma> \<sigma>'; P (\<sigma>, NodeS ii \<zeta> R) \<rbrakk> \<Longrightarrow> P (\<sigma>', NodeS ii \<zeta> R)"
      and local: "\<And>\<sigma> \<zeta> R \<sigma>' \<zeta>' R' a.
                  \<lbrakk> (\<sigma>, NodeS ii \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U;
                    ((\<sigma>, NodeS ii \<zeta> R), a, (\<sigma>', NodeS ii \<zeta>' R')) \<in> trans (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o);
                    S \<sigma> \<sigma>' a; P (\<sigma>, NodeS ii \<zeta> R) \<rbrakk> \<Longrightarrow> P (\<sigma>', NodeS ii \<zeta>' R')"
    shows "P (\<sigma>, NodeS ii \<zeta> R)"
  using assms(1) proof induction
    fix s
    assume "s \<in> init (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)"
    hence "s \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U"
      by (rule oreachable_init)
    with \<open>s \<in> init (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)\<close> obtain \<sigma> \<zeta> where "s = (\<sigma>, NodeS ii \<zeta> R\<^sub>i)"
      by (simp add: onode_comps) metis
    with \<open>s \<in> init (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)\<close> and init show "P s" by simp
  next
    fix s a \<sigma>'
    assume sr: "s \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U"
       and "U (fst s) \<sigma>'"
       and "P s"
    from sr obtain \<sigma> \<zeta> R where "s = (\<sigma>, NodeS ii \<zeta> R)"
      using node_net_state' by metis
    with sr \<open>U (fst s) \<sigma>'\<close> \<open>P s\<close> show "P (\<sigma>', snd s)"
    by simp (metis other)
  next
    fix s a s'
    assume sr: "s \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U"
       and tr: "(s, a, s') \<in> trans (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)"
       and "S (fst s) (fst s') a"
       and "P s"
    from this(1-3) have "s' \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U"
      by - (erule(2) oreachable_local)
    then obtain \<sigma>' \<zeta>' R' where [simp]: "s' = (\<sigma>', NodeS ii \<zeta>' R')"
      using node_net_state' by metis
    from sr and \<open>P s\<close> obtain \<sigma> \<zeta> R
      where [simp]: "s = (\<sigma>, NodeS ii \<zeta> R)"
        and A1: "(\<sigma>, NodeS ii \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U"
        and A4: "P (\<sigma>, NodeS ii \<zeta> R)"
      using node_net_state' by metis
    with tr and \<open>S (fst s) (fst s') a\<close>
      have A2: "((\<sigma>, NodeS ii \<zeta> R), a, (\<sigma>', NodeS ii \<zeta>' R')) \<in> trans (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)"
       and A3: "S \<sigma> \<sigma>' a" by simp_all
    from A1 A2 A3 A4 have "P (\<sigma>', NodeS ii \<zeta>' R')" by (rule local)
    thus "P s'" by simp
  qed

lemma nodemap_induct [consumes, case_names init step]:
  assumes "(\<sigma>, NodeS ii \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U"
      and init: "\<And>\<sigma> \<zeta>. (\<sigma>, NodeS ii \<zeta> R\<^sub>i) \<in> init (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) \<Longrightarrow> P \<sigma> \<zeta> R\<^sub>i"
      and other: "\<And>\<sigma> \<zeta> R \<sigma>' a.
                  \<lbrakk> (\<sigma>, NodeS ii \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U;
                    U \<sigma> \<sigma>'; P \<sigma> \<zeta> R \<rbrakk> \<Longrightarrow> P \<sigma>' \<zeta> R"
      and local: "\<And>\<sigma> \<zeta> R \<sigma>' \<zeta>' R' a.
                  \<lbrakk> (\<sigma>, NodeS ii \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U;
                    ((\<sigma>, NodeS ii \<zeta> R), a, (\<sigma>', NodeS ii \<zeta>' R')) \<in> trans (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o);
                    S \<sigma> \<sigma>' a; P \<sigma> \<zeta> R \<rbrakk> \<Longrightarrow> P \<sigma>' \<zeta>' R'"
    shows "P \<sigma> \<zeta> R"
  using assms(1) proof (induction "(\<sigma>, NodeS ii \<zeta> R)" arbitrary: \<sigma> \<zeta> R)
    fix \<sigma> \<zeta> R
    assume a1: "(\<sigma>, NodeS ii \<zeta> R) \<in> init (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)"
    hence "R = R\<^sub>i" by (simp add: init_onode_comp)
    with a1 have "(\<sigma>, NodeS ii \<zeta> R\<^sub>i) \<in> init (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)" by simp
    with init and \<open>R = R\<^sub>i\<close> show "P \<sigma> \<zeta> R" by simp
  next
    fix st a \<sigma>' \<zeta>' R'
    assume "st \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U"
       and tr: "(st, a, (\<sigma>', NodeS ii \<zeta>' R')) \<in> trans (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)"
       and "S (fst st) (fst (\<sigma>', NodeS ii \<zeta>' R')) a"
       and IH: "\<And>\<sigma> \<zeta> R. st = (\<sigma>, NodeS ii \<zeta> R) \<Longrightarrow> P \<sigma> \<zeta> R"
    from this(1) obtain \<sigma> \<zeta> R where "st = (\<sigma>, NodeS ii \<zeta> R)"
                                and "(\<sigma>, NodeS ii \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U"
      by (metis node_net_state')
    note this(2)
    moreover from tr and \<open>st = (\<sigma>, NodeS ii \<zeta> R)\<close>
      have "((\<sigma>, NodeS ii \<zeta> R), a, (\<sigma>', NodeS ii \<zeta>' R')) \<in> trans (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)" by simp
    moreover from \<open>S (fst st) (fst (\<sigma>', NodeS ii \<zeta>' R')) a\<close> and \<open>st = (\<sigma>, NodeS ii \<zeta> R)\<close>
      have "S \<sigma> \<sigma>' a" by simp
    moreover from IH and \<open>st = (\<sigma>, NodeS ii \<zeta> R)\<close> have "P \<sigma> \<zeta> R" .
    ultimately show "P \<sigma>' \<zeta>' R'" by (rule local)
  next
    fix st \<sigma>' \<zeta> R
    assume "st \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U"
       and "U (fst st) \<sigma>'"
       and "snd st = NodeS ii \<zeta> R"
       and IH: "\<And>\<sigma> \<zeta> R. st = (\<sigma>, NodeS ii \<zeta> R) \<Longrightarrow> P \<sigma> \<zeta> R"
    from this(1,3) obtain \<sigma> where "st = (\<sigma>, NodeS ii \<zeta> R)"
                              and "(\<sigma>, NodeS ii \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U"
      by (metis surjective_pairing)
    note this(2)
    moreover from \<open>U (fst st) \<sigma>'\<close> and \<open>st = (\<sigma>, NodeS ii \<zeta> R)\<close> have "U \<sigma> \<sigma>'" by simp
    moreover from IH and \<open>st = (\<sigma>, NodeS ii \<zeta> R)\<close> have "P \<sigma> \<zeta> R" .
    ultimately show "P \<sigma>' \<zeta> R" by (rule other)
  qed

lemma node_addressD [dest, simp]:
  assumes "(\<sigma>, NodeS i \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) S U"
    shows "i = ii"
  using assms by (clarsimp dest!: node_net_state')

lemma node_proc_reachable [dest]:
  assumes "(\<sigma>, NodeS i \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)
                                         (otherwith S {ii} (oarrivemsg I)) (other U {ii})"
      and sgivesu: "\<And>\<xi> \<xi>'. S \<xi> \<xi>' \<Longrightarrow> U \<xi> \<xi>'"
    shows "(\<sigma>, \<zeta>) \<in> oreachable T (otherwith S {ii} (orecvmsg I)) (other U {ii})"
  proof -
    from assms(1) have "(\<sigma>, NodeS ii \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)
                                             (otherwith S {ii} (oarrivemsg I)) (other U {ii})"
      by - (frule node_addressD, simp)
    thus ?thesis
    proof (induction rule: nodemap_induct)
      fix \<sigma> \<zeta>
      assume "(\<sigma>, NodeS ii \<zeta> R\<^sub>i) \<in> init (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)"
      hence "(\<sigma>, \<zeta>) \<in> init T" by (auto simp: onode_comps)
      thus "(\<sigma>, \<zeta>) \<in> oreachable T (otherwith S {ii} (orecvmsg I)) (other U {ii})"
        by (rule oreachable_init)
    next
      fix \<sigma> \<zeta> R \<sigma>' \<zeta>' R' a
      assume "other U {ii} \<sigma> \<sigma>'"
         and "(\<sigma>, \<zeta>) \<in> oreachable T (otherwith S {ii} (orecvmsg I)) (other U {ii})"
      thus "(\<sigma>', \<zeta>) \<in> oreachable T (otherwith S {ii} (orecvmsg I)) (other U {ii})"
        by - (rule oreachable_other')
    next
      fix \<sigma> \<zeta> R \<sigma>' \<zeta>' R' a
      assume rs: "(\<sigma>, NodeS ii \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)
                                         (otherwith S {ii} (oarrivemsg I)) (other U {ii})"
         and tr: "((\<sigma>, NodeS ii \<zeta> R), a, (\<sigma>', NodeS ii \<zeta>' R')) \<in> trans (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)"
         and ow: "otherwith S {ii} (oarrivemsg I) \<sigma> \<sigma>' a"
         and ih: "(\<sigma>, \<zeta>) \<in> oreachable T (otherwith S {ii} (orecvmsg I)) (other U {ii})"

      from ow have *: "\<sigma>' ii = \<sigma> ii \<Longrightarrow> other U {ii} \<sigma> \<sigma>'"
        by (clarsimp elim!: otherwithE) (rule otherI, simp_all, metis sgivesu)
      from tr have "((\<sigma>, NodeS ii \<zeta> R), a, (\<sigma>', NodeS ii \<zeta>' R')) \<in> onode_sos (trans T)"
        by (simp add: onode_comps)
      thus "(\<sigma>', \<zeta>') \<in> oreachable T (otherwith S {ii} (orecvmsg I)) (other U {ii})"
      proof cases
        case onode_bcast
        with ih and ow show ?thesis
          by (auto elim!: oreachable_local' otherwithE)
      next
        case onode_gcast
        with ih and ow show ?thesis
          by (auto elim!: oreachable_local' otherwithE)
      next
        case onode_ucast
        with ih and ow show ?thesis
          by (auto elim!: oreachable_local' otherwithE)
      next
        case onode_notucast
        with ih and ow show ?thesis
          by (auto elim!: oreachable_local' otherwithE)
      next
        case onode_deliver
        with ih and ow show ?thesis
          by (auto elim!: oreachable_local' otherwithE)
      next
        case onode_tau
        with ih and ow show ?thesis
          by (auto elim!: oreachable_local' otherwithE)
      next
        case onode_receive
        with ih and ow show ?thesis
          by (auto elim!: oreachable_local' otherwithE)
      next
        case (onode_arrive m)
        hence "\<zeta>' = \<zeta>" and "\<sigma>' ii = \<sigma> ii" by auto
        from this(2) have "other U {ii} \<sigma> \<sigma>'" by (rule *)
        with ih and \<open>\<zeta>' = \<zeta>\<close> show ?thesis by auto
      next
        case onode_connect1
        hence "\<zeta>' = \<zeta>" and "\<sigma>' ii = \<sigma> ii" by auto
        from this(2) have "other U {ii} \<sigma> \<sigma>'" by (rule *)
        with ih and \<open>\<zeta>' = \<zeta>\<close> show ?thesis by auto
      next
        case onode_connect2
        hence "\<zeta>' = \<zeta>" and "\<sigma>' ii = \<sigma> ii" by auto
        from this(2) have "other U {ii} \<sigma> \<sigma>'" by (rule *)
        with ih and \<open>\<zeta>' = \<zeta>\<close> show ?thesis by auto
      next
        case onode_connect_other
        hence "\<zeta>' = \<zeta>" and "\<sigma>' ii = \<sigma> ii" by auto
        from this(2) have "other U {ii} \<sigma> \<sigma>'" by (rule *)
        with ih and \<open>\<zeta>' = \<zeta>\<close> show ?thesis by auto
      next
        case onode_disconnect1
        hence "\<zeta>' = \<zeta>" and "\<sigma>' ii = \<sigma> ii" by auto
        from this(2) have "other U {ii} \<sigma> \<sigma>'" by (rule *)
        with ih and \<open>\<zeta>' = \<zeta>\<close> show ?thesis by auto
      next
        case onode_disconnect2
        hence "\<zeta>' = \<zeta>" and "\<sigma>' ii = \<sigma> ii" by auto
        from this(2) have "other U {ii} \<sigma> \<sigma>'" by (rule *)
        with ih and \<open>\<zeta>' = \<zeta>\<close> show ?thesis by auto
      next
        case onode_disconnect_other
        hence "\<zeta>' = \<zeta>" and "\<sigma>' ii = \<sigma> ii" by auto
        from this(2) have "other U {ii} \<sigma> \<sigma>'" by (rule *)
        with ih and \<open>\<zeta>' = \<zeta>\<close> show ?thesis by auto
      qed
    qed
  qed

lemma node_proc_reachable_statelessassm [dest]:
  assumes "(\<sigma>, NodeS i \<zeta> R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)
                                         (otherwith (\<lambda>_ _. True) {ii} (oarrivemsg I))
                                         (other (\<lambda>_ _. True) {ii})"
    shows "(\<sigma>, \<zeta>) \<in> oreachable T
                               (otherwith (\<lambda>_ _. True) {ii} (orecvmsg I)) (other (\<lambda>_ _. True) {ii})"
  using assms
  by (rule node_proc_reachable) simp_all

lemma node_lift:
  assumes "T \<Turnstile> (otherwith S {ii} (orecvmsg I), other U {ii} \<rightarrow>) global P"
      and "\<And>\<xi> \<xi>'. S \<xi> \<xi>' \<Longrightarrow> U \<xi> \<xi>'"
    shows "\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o \<Turnstile> (otherwith S {ii} (oarrivemsg I), other U {ii} \<rightarrow>) global P"
  proof (rule oinvariant_oreachableI)
    fix \<sigma> \<zeta>
    assume "(\<sigma>, \<zeta>) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o) (otherwith S {ii} (oarrivemsg I)) (other U {ii})"
    moreover then obtain i s R where "\<zeta> = NodeS i s R"
      by (metis node_net_state)
    ultimately have "(\<sigma>, NodeS i s R) \<in> oreachable (\<langle>ii : T : R\<^sub>i\<rangle>\<^sub>o)
                                                   (otherwith S {ii} (oarrivemsg I)) (other U {ii})"
      by simp
    hence "(\<sigma>, s) \<in> oreachable T (otherwith S {ii} (orecvmsg I)) (other U {ii})"
      by - (erule node_proc_reachable, erule assms(2))
    with assms(1) show "global P (\<sigma>, \<zeta>)"
      by (metis fst_conv globalsimp oinvariantD)
  qed

lemma node_lift_step [intro]:
  assumes pinv: "T \<Turnstile>\<^sub>A (otherwith S {i} (orecvmsg I), other U {i} \<rightarrow>) globala (\<lambda>(\<sigma>, _, \<sigma>'). Q \<sigma> \<sigma>')"
      and other: "\<And>\<sigma> \<sigma>'. other U {i} \<sigma> \<sigma>' \<Longrightarrow> Q \<sigma> \<sigma>'"
      and sgivesu: "\<And>\<xi> \<xi>'. S \<xi> \<xi>' \<Longrightarrow> U \<xi> \<xi>'"
    shows "\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (otherwith S {i} (oarrivemsg I), other U {i} \<rightarrow>)
                            globala (\<lambda>(\<sigma>, _, \<sigma>'). Q \<sigma> \<sigma>')"
    (is "_ \<Turnstile>\<^sub>A (?S, ?U \<rightarrow>) _")
  proof (rule ostep_invariantI, simp)
    fix \<sigma> s a \<sigma>' s'
    assume rs: "(\<sigma>, s) \<in> oreachable (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o) ?S ?U"
       and tr: "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o)"
       and ow: "?S \<sigma> \<sigma>' a"
    from ow have *: "\<sigma>' i = \<sigma> i \<Longrightarrow> other U {i} \<sigma> \<sigma>'"
      by (clarsimp elim!: otherwithE) (rule otherI, simp_all, metis sgivesu)
    from rs tr obtain \<zeta> R
      where [simp]: "s = NodeS i \<zeta> R"
        and "(\<sigma>, NodeS i \<zeta> R) \<in> oreachable (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o) ?S ?U"
      by (metis node_net_state)
    from this(2) have or: "(\<sigma>, \<zeta>) \<in> oreachable T (otherwith S {i} (orecvmsg I)) ?U"
      by (rule node_proc_reachable [OF _ assms(3)])
    from tr have "((\<sigma>, NodeS i \<zeta> R), a, (\<sigma>', s')) \<in> onode_sos (trans T)"
      by (simp add: onode_comps)
    thus "Q \<sigma> \<sigma>'"
    proof cases
      fix m \<zeta>'
      assume "a = R:*cast(m)"
         and tr': "((\<sigma>, \<zeta>), broadcast m, (\<sigma>', \<zeta>')) \<in> trans T"
      from this(1) and \<open>?S \<sigma> \<sigma>' a\<close> have "otherwith S {i} (orecvmsg I) \<sigma> \<sigma>' (broadcast m)"
        by (auto elim!: otherwithE)
      with or tr' show ?thesis by (rule ostep_invariantD [OF pinv, simplified])
    next
      fix D m \<zeta>'
      assume "a = (R \<inter> D):*cast(m)"
         and tr': "((\<sigma>, \<zeta>), groupcast D m, (\<sigma>', \<zeta>')) \<in> trans T"
      from this(1) and \<open>?S \<sigma> \<sigma>' a\<close> have "otherwith S {i} (orecvmsg I) \<sigma> \<sigma>' (groupcast D m)"
        by (auto elim!: otherwithE)
      with or tr' show ?thesis by (rule ostep_invariantD [OF pinv, simplified])
    next
      fix d m \<zeta>'
      assume "a = {d}:*cast(m)"
         and tr': "((\<sigma>, \<zeta>), unicast d m, (\<sigma>', \<zeta>')) \<in> trans T"
      from this(1) and \<open>?S \<sigma> \<sigma>' a\<close> have "otherwith S {i} (orecvmsg I) \<sigma> \<sigma>' (unicast d m)"
        by (auto elim!: otherwithE)
      with or tr' show ?thesis by (rule ostep_invariantD [OF pinv, simplified])
    next
      fix d \<zeta>'
      assume "a = \<tau>"
         and tr': "((\<sigma>, \<zeta>), \<not>unicast d, (\<sigma>', \<zeta>')) \<in> trans T"
      from this(1) and \<open>?S \<sigma> \<sigma>' a\<close> have "otherwith S {i} (orecvmsg I) \<sigma> \<sigma>' (\<not>unicast d)"
        by (auto elim!: otherwithE)
      with or tr' show ?thesis by (rule ostep_invariantD [OF pinv, simplified])
    next
      fix d \<zeta>'
      assume "a = i:deliver(d)"
         and tr': "((\<sigma>, \<zeta>), deliver d, (\<sigma>', \<zeta>')) \<in> trans T"
      from this(1) and \<open>?S \<sigma> \<sigma>' a\<close> have "otherwith S {i} (orecvmsg I) \<sigma> \<sigma>' (deliver d)"
        by (auto elim!: otherwithE)
      with or tr' show ?thesis by (rule ostep_invariantD [OF pinv, simplified])
    next
      fix \<zeta>'
      assume "a = \<tau>"
         and tr': "((\<sigma>, \<zeta>), \<tau>, (\<sigma>', \<zeta>')) \<in> trans T"
      from this(1) and \<open>?S \<sigma> \<sigma>' a\<close> have "otherwith S {i} (orecvmsg I) \<sigma> \<sigma>' \<tau>"
        by (auto elim!: otherwithE)
      with or tr' show ?thesis by (rule ostep_invariantD [OF pinv, simplified])
    next
      fix m \<zeta>'
      assume "a = {i}\<not>{}:arrive(m)"
         and tr': "((\<sigma>, \<zeta>), receive m, (\<sigma>', \<zeta>')) \<in> trans T"
      from this(1) and \<open>?S \<sigma> \<sigma>' a\<close> have "otherwith S {i} (orecvmsg I) \<sigma> \<sigma>' (receive m)"
        by (auto elim!: otherwithE)
      with or tr' show ?thesis by (rule ostep_invariantD [OF pinv, simplified])
    next
      fix m
      assume "a = {}\<not>{i}:arrive(m)"
         and "\<sigma>' i = \<sigma> i"
      from this(2) have "other U {i} \<sigma> \<sigma>'" by (rule *)
      thus ?thesis by (rule other)
    next
      fix i'
      assume "a = connect(i, i')"
         and "\<sigma>' i = \<sigma> i"
      from this(2) have "other U {i} \<sigma> \<sigma>'" by (rule *)
      thus ?thesis by (rule other)
    next
      fix i'
      assume "a = connect(i', i)"
         and "\<sigma>' i = \<sigma> i"
      from this(2) have "other U {i} \<sigma> \<sigma>'" by (rule *)
      thus ?thesis by (rule other)
    next
      fix i' i''
      assume "a = connect(i', i'')"
         and "\<sigma>' i = \<sigma> i"
      from this(2) have "other U {i} \<sigma> \<sigma>'" by (rule *)
      thus ?thesis by (rule other)
    next
      fix i'
      assume "a = disconnect(i, i')"
         and "\<sigma>' i = \<sigma> i"
      from this(2) have "other U {i} \<sigma> \<sigma>'" by (rule *)
      thus ?thesis by (rule other)
    next
      fix i'
      assume "a = disconnect(i', i)"
         and "\<sigma>' i = \<sigma> i"
      from this(2) have "other U {i} \<sigma> \<sigma>'" by (rule *)
      thus ?thesis by (rule other)
    next
      fix i' i''
      assume "a = disconnect(i', i'')"
         and "\<sigma>' i = \<sigma> i"
      from this(2) have "other U {i} \<sigma> \<sigma>'" by (rule *)
      thus ?thesis by (rule other)
    qed
  qed

lemma node_lift_step_statelessassm [intro]:
  assumes "T \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg I \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                       globala (\<lambda>(\<sigma>, _, \<sigma>'). Q (\<sigma> i) (\<sigma>' i))"
      and "\<And>\<xi>. Q \<xi> \<xi>"
    shows "\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                            globala (\<lambda>(\<sigma>, _, \<sigma>'). Q (\<sigma> i) (\<sigma>' i))"
  proof -
    from assms(1)
      have "T \<Turnstile>\<^sub>A (otherwith (\<lambda>_ _. True) {i} (orecvmsg I), other (\<lambda>_ _. True) {i} \<rightarrow>)
                  globala (\<lambda>(\<sigma>, _, \<sigma>'). Q (\<sigma> i) (\<sigma>' i))"
        by rule auto
    with assms(2) have "\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (otherwith (\<lambda>_ _. True) {i} (oarrivemsg I),
                                          other (\<lambda>_ _. True) {i} \<rightarrow>)
                                         globala (\<lambda>(\<sigma>, _, \<sigma>'). Q (\<sigma> i) (\<sigma>' i))"
      by - (rule node_lift_step, auto)
    thus ?thesis by rule auto
  qed

lemma node_lift_anycast [intro]:
  assumes pinv: "T \<Turnstile>\<^sub>A (otherwith S {i} (orecvmsg I), other U {i} \<rightarrow>)
                       globala (\<lambda>(\<sigma>, a, \<sigma>'). anycast (Q \<sigma> \<sigma>') a)"
      and "\<And>\<xi> \<xi>'. S \<xi> \<xi>' \<Longrightarrow> U \<xi> \<xi>'"
    shows "\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (otherwith S {i} (oarrivemsg I), other U {i} \<rightarrow>)
                            globala (\<lambda>(\<sigma>, a, \<sigma>'). castmsg (Q \<sigma> \<sigma>') a)"
    (is "_ \<Turnstile>\<^sub>A (?S, ?U \<rightarrow>) _")
  proof (rule ostep_invariantI, simp)
    fix \<sigma> s a \<sigma>' s'
    assume rs: "(\<sigma>, s) \<in> oreachable (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o) ?S ?U"
       and tr: "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o)"
       and "?S \<sigma> \<sigma>' a"
    from this(1-2) obtain \<zeta> R
      where [simp]: "s = NodeS i \<zeta> R"
        and "(\<sigma>, NodeS i \<zeta> R) \<in> oreachable (\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o) ?S ?U"
      by (metis node_net_state)
    from this(2) have "(\<sigma>, \<zeta>) \<in> oreachable T (otherwith S {i} (orecvmsg I)) ?U"
      by (rule node_proc_reachable [OF _ assms(2)])
    moreover from tr have "((\<sigma>, NodeS i \<zeta> R), a, (\<sigma>', s')) \<in> onode_sos (trans T)"
      by (simp add: onode_comps)
    ultimately show "castmsg (Q \<sigma> \<sigma>') a" using \<open>?S \<sigma> \<sigma>' a\<close>
      by - (erule onode_sos.cases, auto elim!: otherwithE dest!: ostep_invariantD [OF pinv])
  qed

lemma node_lift_anycast_statelessassm [intro]:
  assumes pinv: "T \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg I \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                       globala (\<lambda>(\<sigma>, a, \<sigma>'). anycast (Q \<sigma> \<sigma>') a)"
    shows "\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                            globala (\<lambda>(\<sigma>, a, \<sigma>'). castmsg (Q \<sigma> \<sigma>') a)"
    (is "_ \<Turnstile>\<^sub>A (?S, _ \<rightarrow>) _")
  proof -
    from assms(1)
      have "T \<Turnstile>\<^sub>A (otherwith (\<lambda>_ _. True) {i} (orecvmsg I), other (\<lambda>_ _. True) {i} \<rightarrow>)
                  globala (\<lambda>(\<sigma>, a, \<sigma>'). anycast (Q \<sigma> \<sigma>') a)"
        by rule auto
    hence "\<langle>i : T : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (otherwith (\<lambda>_ _. True) {i} (oarrivemsg I), other (\<lambda>_ _. True) {i} \<rightarrow>)
                            globala (\<lambda>(\<sigma>, a, \<sigma>'). castmsg (Q \<sigma> \<sigma>') a)"
      by (rule node_lift_anycast) simp_all
    thus ?thesis
      by rule auto
  qed

lemma node_local_deliver:
  "\<langle>i : \<zeta>\<^sub>i : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (S, U \<rightarrow>) globala (\<lambda>(_, a, _). \<forall>j. j\<noteq>i \<longrightarrow> (\<forall>d. a \<noteq> j:deliver(d)))"
  proof (rule ostep_invariantI, simp)
    fix \<sigma> s a \<sigma>' s'
    assume 1: "(\<sigma>, s) \<in> oreachable (\<langle>i : \<zeta>\<^sub>i : R\<^sub>i\<rangle>\<^sub>o) S U"
       and 2: "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans (\<langle>i : \<zeta>\<^sub>i : R\<^sub>i\<rangle>\<^sub>o)"
       and "S \<sigma> \<sigma>' a"
    moreover from 1 2 obtain \<zeta> R \<zeta>' R' where "s = NodeS i \<zeta> R" and "s' = NodeS i \<zeta>' R'" ..
    ultimately show "\<forall>j. j\<noteq>i \<longrightarrow> (\<forall>d. a \<noteq> j:deliver(d))"
      by (cases a) (auto simp add: onode_comps)
  qed

lemma node_tau_deliver_unchanged:
  "\<langle>i : \<zeta>\<^sub>i : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (S, U \<rightarrow>) globala (\<lambda>(\<sigma>, a, \<sigma>'). a = \<tau> \<or> (\<exists>i d. a = i:deliver(d))
                                                     \<longrightarrow> (\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j))"
  proof (rule ostep_invariantI, clarsimp simp only: globalasimp snd_conv fst_conv)
    fix \<sigma> s a \<sigma>' s' j
    assume 1: "(\<sigma>, s) \<in> oreachable (\<langle>i : \<zeta>\<^sub>i : R\<^sub>i\<rangle>\<^sub>o) S U"
       and 2: "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans (\<langle>i : \<zeta>\<^sub>i : R\<^sub>i\<rangle>\<^sub>o)"
       and "S \<sigma> \<sigma>' a"
       and "a = \<tau> \<or> (\<exists>i d. a = i:deliver(d))"
       and "j \<noteq> i"
    moreover from 1 2 obtain \<zeta> R \<zeta>' R' where "s = NodeS i \<zeta> R" and "s' = NodeS i \<zeta>' R'" ..
    ultimately show "\<sigma>' j = \<sigma> j"
      by (cases a) (auto simp del: step_node_tau simp add: onode_comps)
  qed

end
