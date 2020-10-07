(*  Title:       Qmsg_Lifting.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Lifting rules for parallel compositions with QMSG"

theory Qmsg_Lifting
imports Qmsg OAWN_SOS Inv_Cterms OAWN_Invariants
begin

lemma oseq_no_change_on_send:
  fixes \<sigma> s a \<sigma>' s'
  assumes "((\<sigma>, s), a, (\<sigma>', s')) \<in> oseqp_sos \<Gamma> i"
  shows "case a of
           broadcast m     \<Rightarrow> \<sigma>' i = \<sigma> i
         | groupcast ips m \<Rightarrow> \<sigma>' i = \<sigma> i
         | unicast ips m   \<Rightarrow> \<sigma>' i = \<sigma> i
         | \<not>unicast ips    \<Rightarrow> \<sigma>' i = \<sigma> i
         | send m          \<Rightarrow> \<sigma>' i = \<sigma> i
         | deliver m       \<Rightarrow> \<sigma>' i = \<sigma> i
         | _ \<Rightarrow> True"
  using assms by induction simp_all

lemma qmsg_no_change_on_send_or_receive:
    fixes \<sigma> s a \<sigma>' s'
  assumes "((\<sigma>, s), a, (\<sigma>', s')) \<in> oparp_sos i (oseqp_sos \<Gamma> i) (seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G)"
      and "a \<noteq> \<tau>"
    shows "\<sigma>' i = \<sigma> i"
  proof -
    from assms(1) obtain p q p' q'
      where "((\<sigma>, (p, q)), a, (\<sigma>', (p', q'))) \<in> oparp_sos i (oseqp_sos \<Gamma> i) (seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G)"
      by (cases s, cases s', simp)
    thus ?thesis
    proof
      assume "((\<sigma>, p), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
         and "\<And>m. a \<noteq> receive m"
      with \<open>a \<noteq> \<tau>\<close> show "\<sigma>' i = \<sigma> i"
        by - (drule oseq_no_change_on_send, cases a, auto)
    next
      assume "(q, a, q') \<in> seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G"
         and "\<sigma>' i = \<sigma> i"
        thus "\<sigma>' i = \<sigma> i" by simp
    next
      assume "a = \<tau>" with \<open>a \<noteq> \<tau>\<close> show ?thesis by auto
    qed
  qed

lemma qmsg_msgs_not_empty:
  "qmsg \<TTurnstile> onl \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G (\<lambda>(msgs, l). l = ()-:1 \<longrightarrow> msgs \<noteq> [])"
  by inv_cterms

lemma qmsg_send_from_queue:
  "qmsg \<TTurnstile>\<^sub>A (\<lambda>((msgs, q), a, _). sendmsg (\<lambda>m. m\<in>set msgs) a)"
  proof -
    have "qmsg \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G (\<lambda>((msgs, _), a, _). sendmsg (\<lambda>m. m\<in>set msgs) a)"
      by (inv_cterms inv add: onl_invariant_sterms [OF qmsg_wf qmsg_msgs_not_empty])
    thus ?thesis
      by (rule step_invariant_weakenE) (auto dest!: onllD)
  qed

lemma qmsg_queue_contents:
  "qmsg \<TTurnstile>\<^sub>A (\<lambda>((msgs, q), a, (msgs', q')). case a of
                                             receive m \<Rightarrow> set msgs' \<subseteq> set (msgs @ [m])
                                           | _ \<Rightarrow> set msgs' \<subseteq> set msgs)"
  proof -
    have "qmsg \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G (\<lambda>((msgs, q), a, (msgs', q')).
                                     case a of
                                       receive m \<Rightarrow> set msgs' \<subseteq> set (msgs @ [m])
                                     | _ \<Rightarrow> set msgs' \<subseteq> set msgs)"
      by (inv_cterms) (clarsimp simp add: in_set_tl)+
    thus ?thesis
      by (rule step_invariant_weakenE) (auto dest!: onllD)
  qed

lemma qmsg_send_receive_or_tau:
  "qmsg \<TTurnstile>\<^sub>A (\<lambda>(_, a, _). \<exists>m. a = send m \<or> a = receive m \<or> a = \<tau>)"
  proof -
   have "qmsg \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G (\<lambda>(_, a, _). \<exists>m. a = send m \<or> a = receive m \<or> a = \<tau>)"
     by inv_cterms
   thus ?thesis
    by rule (auto dest!: onllD)
  qed

lemma par_qmsg_oreachable:
  assumes "(\<sigma>, \<zeta>) \<in> oreachable (A \<langle>\<langle>\<^bsub>i\<^esub> qmsg) (otherwith S {i} (orecvmsg R)) (other U {i})"
           (is "_ \<in> oreachable _ ?owS _")
      and pinv: "A \<Turnstile>\<^sub>A (otherwith S {i} (orecvmsg R), other U {i} \<rightarrow>)
                       globala (\<lambda>(\<sigma>, _, \<sigma>'). U (\<sigma> i) (\<sigma>' i))"
      and ustutter: "\<And>\<xi>. U \<xi> \<xi>"
      and sgivesu: "\<And>\<xi> \<xi>'. S \<xi> \<xi>' \<Longrightarrow> U \<xi> \<xi>'"
      and upreservesq: "\<And>\<sigma> \<sigma>' m. \<lbrakk> \<forall>j. U (\<sigma> j) (\<sigma>' j); R \<sigma> m \<rbrakk> \<Longrightarrow> R \<sigma>' m"
  shows "(\<sigma>, fst \<zeta>) \<in> oreachable A ?owS (other U {i})
         \<and> snd \<zeta> \<in> reachable qmsg (recvmsg (R \<sigma>))
         \<and> (\<forall>m\<in>set (fst (snd \<zeta>)). R \<sigma> m)"
  using assms(1) proof (induction rule: oreachable_pair_induct)
    fix \<sigma> pq
    assume "(\<sigma>, pq) \<in> init (A \<langle>\<langle>\<^bsub>i\<^esub> qmsg)"
    then obtain p ms q where "pq = (p, (ms, q))"
                         and "(\<sigma>, p) \<in> init A"
                         and "(ms, q) \<in> init qmsg"
      by (clarsimp simp del: \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_simps)
    from this(2) have "(\<sigma>, p) \<in> oreachable A ?owS (other U {i})" ..
    moreover from \<open>(ms, q) \<in> init qmsg\<close> have "(ms, q) \<in> reachable qmsg (recvmsg (R \<sigma>))" ..
    moreover from \<open>(ms, q) \<in> init qmsg\<close> have "ms = []"
        unfolding \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_def by simp
    ultimately show "(\<sigma>, fst pq) \<in> oreachable A ?owS (other U {i})
                     \<and> snd pq \<in> reachable qmsg (recvmsg (R \<sigma>))
                     \<and> (\<forall>m\<in>set (fst (snd pq)). R \<sigma> m)"
      using \<open>pq = (p, (ms, q))\<close> by simp
  next
    note \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_simps [simp del]
    case (other \<sigma> pq \<sigma>')
    hence "(\<sigma>, fst pq) \<in> oreachable A ?owS (other U {i})"
      and "other U {i} \<sigma> \<sigma>'"
      and qr: "snd pq \<in> reachable qmsg (recvmsg (R \<sigma>))"
      and "\<forall>m\<in>set (fst (snd pq)). R \<sigma> m"
      by simp_all
    from \<open>other U {i} \<sigma> \<sigma>'\<close> and ustutter have "\<forall>j. U (\<sigma> j) (\<sigma>' j)"
        by (clarsimp elim!: otherE) metis
    from \<open>other U {i} \<sigma> \<sigma>'\<close>
     and \<open>(\<sigma>, fst pq) \<in> oreachable A ?owS (other U {i})\<close>
      have "(\<sigma>', fst pq) \<in> oreachable A ?owS (other U {i})"
        by - (rule oreachable_other')
    moreover have "\<forall>m\<in>set (fst (snd pq)). R \<sigma>' m"
    proof
      fix m assume "m \<in> set (fst (snd pq))"
      with \<open>\<forall>m\<in>set (fst (snd pq)). R \<sigma> m\<close> have "R \<sigma> m" ..
      with \<open>\<forall>j. U (\<sigma> j) (\<sigma>' j)\<close> show "R \<sigma>' m" by (rule upreservesq)
    qed
    moreover from qr have "snd pq \<in> reachable qmsg (recvmsg (R \<sigma>'))"
    proof
      fix a
      assume "recvmsg (R \<sigma>) a"
      thus "recvmsg (R \<sigma>') a"
      proof (rule recvmsgE [where R=R])
        fix m assume "R \<sigma> m"
        with \<open>\<forall>j. U (\<sigma> j) (\<sigma>' j)\<close> show "R \<sigma>' m" by (rule upreservesq)
      qed
    qed
    ultimately show ?case using qr by simp
  next
    case (local \<sigma> pq \<sigma>' pq' a)
    obtain p ms q p' ms' q' where "pq = (p, (ms, q))"
                              and "pq' = (p', (ms', q'))"
      by (cases pq, cases pq') metis
    with local.hyps local.IH
      have pqtr: "((\<sigma>, (p, (ms, q))), a, (\<sigma>', (p', (ms', q'))))
                    \<in> oparp_sos i (trans A) (seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G)"
        and por: "(\<sigma>, p) \<in> oreachable A ?owS (other U {i})"
        and qr: "(ms, q) \<in> reachable qmsg (recvmsg (R \<sigma>))"
        and "\<forall>m\<in>set ms. R \<sigma> m"
        and "?owS \<sigma> \<sigma>' a"
      by (simp_all del: \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_simps)

    from \<open>?owS \<sigma> \<sigma>' a\<close> have "\<forall>j. j\<noteq>i \<longrightarrow> S (\<sigma> j) (\<sigma>' j)"
      by (clarsimp dest!: otherwith_syncD)
    with sgivesu have "\<forall>j. j\<noteq>i \<longrightarrow> U (\<sigma> j) (\<sigma>' j)" by simp

    from \<open>?owS \<sigma> \<sigma>' a\<close> have "orecvmsg R \<sigma> a" by (rule otherwithE)
    hence "recvmsg (R \<sigma>) a" ..

    from pqtr have "(\<sigma>', p') \<in> oreachable A ?owS (other U {i})
                  \<and> (ms', q') \<in> reachable qmsg (recvmsg (R \<sigma>'))
                  \<and> (\<forall>m\<in>set ms'. R \<sigma>' m)"
    proof
      assume "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A"
         and "\<And>m. a \<noteq> receive m"
         and "(ms', q') = (ms, q)"
      from this(1) have ptr: "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A" by simp
      with pinv por and \<open>?owS \<sigma> \<sigma>' a\<close> have "U (\<sigma> i) (\<sigma>' i)"
        by (auto dest!: ostep_invariantD)
      with \<open>\<forall>j. j\<noteq>i \<longrightarrow> U (\<sigma> j) (\<sigma>' j)\<close> have "\<forall>j. U (\<sigma> j) (\<sigma>' j)" by auto

      hence recvmsg': "\<And>a. recvmsg (R \<sigma>) a \<Longrightarrow> recvmsg (R \<sigma>') a"
        by (auto elim!: recvmsgE [where R=R] upreservesq)

      from por ptr \<open>?owS \<sigma> \<sigma>' a\<close> have "(\<sigma>', p') \<in> oreachable A ?owS (other U {i})"
        by - (rule oreachable_local')

      moreover have "(ms', q') \<in> reachable qmsg (recvmsg (R \<sigma>'))"
      proof -
        from qr and \<open>(ms', q') = (ms, q)\<close>
          have "(ms', q') \<in> reachable qmsg (recvmsg (R \<sigma>))" by simp
        thus ?thesis by (rule reachable_weakenE) (erule recvmsg')
      qed

      moreover have "\<forall>m\<in>set ms'. R \<sigma>' m"
      proof
        fix m
        assume "m\<in>set ms'"
        with \<open>(ms', q') = (ms, q)\<close> have "m\<in>set ms" by simp
        with \<open>\<forall>m\<in>set ms. R \<sigma> m\<close> have "R \<sigma> m" ..
        with \<open>\<forall>j. U (\<sigma> j) (\<sigma>' j)\<close> show "R \<sigma>' m"
          by (rule upreservesq)
      qed

      ultimately show
        "(\<sigma>', p') \<in> oreachable A ?owS (other U {i})
          \<and> (ms', q') \<in> reachable qmsg (recvmsg (R \<sigma>'))
          \<and> (\<forall>m\<in>set ms'. R \<sigma>' m)" by simp_all
    next
      assume qtr: "((ms, q), a, (ms', q')) \<in> seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G"
         and "\<And>m. a \<noteq> send m"
         and "p' = p"
         and "\<sigma>' i = \<sigma> i"

      from this(4) and \<open>\<And>\<xi>. U \<xi> \<xi>\<close> have "U (\<sigma> i) (\<sigma>' i)" by simp
      with \<open>\<forall>j. j\<noteq>i \<longrightarrow> U (\<sigma> j) (\<sigma>' j)\<close> have "\<forall>j. U (\<sigma> j) (\<sigma>' j)" by auto

      hence recvmsg': "\<And>a. recvmsg (R \<sigma>) a \<Longrightarrow> recvmsg (R \<sigma>') a"
        by (auto elim!: recvmsgE [where R=R] upreservesq)

      from qtr have tqtr: "((ms, q), a, (ms', q')) \<in> trans qmsg" by simp

      from \<open>\<forall>j. U (\<sigma> j) (\<sigma>' j)\<close> and  \<open>\<sigma>' i = \<sigma> i\<close> have "other U {i} \<sigma> \<sigma>'" by auto
      with por and \<open>p' = p\<close>
        have "(\<sigma>', p') \<in> oreachable A ?owS (other U {i})"
          by (auto dest: oreachable_other)

      moreover have "(ms', q') \<in> reachable qmsg (recvmsg (R \<sigma>'))"
      proof (rule reachable_weakenE [where P="recvmsg (R \<sigma>)"])
        from qr tqtr \<open>recvmsg (R \<sigma>) a\<close> show "(ms', q') \<in> reachable qmsg (recvmsg (R \<sigma>))" ..
      qed (rule recvmsg')

      moreover have "\<forall>m\<in>set ms'. R \<sigma>' m"
      proof
        fix m
        assume "m \<in> set ms'"
        moreover have "case a of receive m \<Rightarrow> set ms' \<subseteq> set (ms @ [m]) | _ \<Rightarrow> set ms' \<subseteq> set ms"
          proof -
            from qr have "(ms, q) \<in> reachable qmsg TT" ..
            thus ?thesis using tqtr
              by (auto dest!: step_invariantD [OF qmsg_queue_contents])
          qed
        ultimately have "R \<sigma> m" using \<open>\<forall>m\<in>set ms. R \<sigma> m\<close> and \<open>orecvmsg R \<sigma> a\<close> 
          by (cases a) auto
        with \<open>\<forall>j. U (\<sigma> j) (\<sigma>' j)\<close> show "R \<sigma>' m"
          by (rule upreservesq)
      qed

      ultimately show "(\<sigma>', p') \<in> oreachable A ?owS (other U {i})
                     \<and> (ms', q') \<in> reachable qmsg (recvmsg (R \<sigma>'))
                     \<and> (\<forall>m\<in>set ms'. R \<sigma>' m)" by simp
    next
      fix m
      assume "a = \<tau>"
         and "((\<sigma>, p), receive m, (\<sigma>', p')) \<in> trans A"
         and "((ms, q), send m, (ms', q')) \<in> seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G"
      from this(2-3)
        have ptr: "((\<sigma>, p), receive m, (\<sigma>', p')) \<in> trans A"
         and qtr: "((ms, q), send m, (ms', q')) \<in> trans qmsg" by simp_all

      from qr have "(ms, q) \<in> reachable qmsg TT" ..
      with qtr have "m \<in> set ms"
        by (auto dest!: step_invariantD [OF qmsg_send_from_queue])
      with \<open>\<forall>m\<in>set ms. R \<sigma> m\<close> have "R \<sigma> m" ..
      hence "orecvmsg R \<sigma> (receive m)" by simp

      with \<open>\<forall>j. j\<noteq>i \<longrightarrow> S (\<sigma> j) (\<sigma>' j)\<close> have "?owS \<sigma> \<sigma>' (receive m)"
        by (auto intro!: otherwithI)
      with pinv por ptr have "U (\<sigma> i) (\<sigma>' i)"
        by (auto dest!: ostep_invariantD)
      with \<open>\<forall>j. j\<noteq>i \<longrightarrow> U (\<sigma> j) (\<sigma>' j)\<close> have "\<forall>j. U (\<sigma> j) (\<sigma>' j)" by auto
      hence recvmsg': "\<And>a. recvmsg (R \<sigma>) a \<Longrightarrow> recvmsg (R \<sigma>') a"
        by (auto elim!: recvmsgE [where R=R] upreservesq)

      from por ptr have "(\<sigma>', p') \<in> oreachable A ?owS (other U {i})"
        using \<open>?owS \<sigma> \<sigma>' (receive m)\<close> by - (erule(1) oreachable_local, simp)

      moreover have "(ms', q') \<in> reachable qmsg (recvmsg (R \<sigma>'))"
      proof (rule reachable_weakenE [where P="recvmsg (R \<sigma>)"])
        have "recvmsg (R \<sigma>) (send m)" by simp
        with qr qtr show "(ms', q') \<in> reachable qmsg (recvmsg (R \<sigma>))" ..
      qed (rule recvmsg')

      moreover have "\<forall>m\<in>set ms'. R \<sigma>' m"
      proof
        fix m
        assume "m \<in> set ms'"
        moreover have "set ms' \<subseteq> set ms"
          proof -
            from qr have "(ms, q) \<in> reachable qmsg TT" ..
            thus ?thesis using qtr
              by (auto dest!: step_invariantD [OF qmsg_queue_contents])
          qed
        ultimately have "R \<sigma> m" using \<open>\<forall>m\<in>set ms. R \<sigma> m\<close> by auto
        with \<open>\<forall>j. U (\<sigma> j) (\<sigma>' j)\<close> show "R \<sigma>' m"
          by (rule upreservesq)
      qed

      ultimately show "(\<sigma>', p') \<in> oreachable A ?owS (other U {i})
                     \<and> (ms', q') \<in> reachable qmsg (recvmsg (R \<sigma>'))
                     \<and> (\<forall>m\<in>set ms'. R \<sigma>' m)" by simp
    qed
    with \<open>pq = (p, (ms, q))\<close> and \<open>pq' = (p', (ms', q'))\<close> show ?case
      by (simp_all del: \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_simps)
  qed

lemma par_qmsg_oreachable_statelessassm:
  assumes "(\<sigma>, \<zeta>) \<in> oreachable (A \<langle>\<langle>\<^bsub>i\<^esub> qmsg)
                               (\<lambda>\<sigma> _. orecvmsg (\<lambda>_. R) \<sigma>) (other (\<lambda>_ _. True) {i})"
      and ustutter: "\<And>\<xi>. U \<xi> \<xi>"
  shows "(\<sigma>, fst \<zeta>) \<in> oreachable A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_. R) \<sigma>) (other (\<lambda>_ _. True) {i})
         \<and> snd \<zeta> \<in> reachable qmsg (recvmsg R)
         \<and> (\<forall>m\<in>set (fst (snd \<zeta>)). R m)"
  proof -
    from assms(1)
      have "(\<sigma>, \<zeta>) \<in> oreachable (A \<langle>\<langle>\<^bsub>i\<^esub> qmsg)
                                (otherwith (\<lambda>_ _. True) {i} (orecvmsg (\<lambda>_. R)))
                                (other (\<lambda>_ _. True) {i})" by auto
    moreover
      have "A \<Turnstile>\<^sub>A (otherwith (\<lambda>_ _. True) {i} (orecvmsg (\<lambda>_. R)),
                  other (\<lambda>_ _. True) {i} \<rightarrow>) globala (\<lambda>(\<sigma>, _, \<sigma>'). True)"
        by auto
    ultimately
      obtain "(\<sigma>, fst \<zeta>) \<in> oreachable A
                           (otherwith (\<lambda>_ _. True) {i} (orecvmsg (\<lambda>_. R))) (other (\<lambda>_ _. True) {i})"
         and  *: "snd \<zeta> \<in> reachable qmsg (recvmsg R)"
         and **: "(\<forall>m\<in>set (fst (snd \<zeta>)). R m)"
        by (auto dest!: par_qmsg_oreachable)
    from this(1)
      have "(\<sigma>, fst \<zeta>) \<in> oreachable A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_. R) \<sigma>) (other (\<lambda>_ _. True) {i})"
        by rule auto
    thus ?thesis using * ** by simp
  qed

lemma lift_into_qmsg:
  assumes "A \<Turnstile> (otherwith S {i} (orecvmsg R), other U {i} \<rightarrow>) global P"
      and "\<And>\<xi>. U \<xi> \<xi>"
      and "\<And>\<xi> \<xi>'. S \<xi> \<xi>' \<Longrightarrow> U \<xi> \<xi>'"
      and "\<And>\<sigma> \<sigma>' m. \<lbrakk> \<forall>j. U (\<sigma> j) (\<sigma>' j); R \<sigma> m \<rbrakk> \<Longrightarrow> R \<sigma>' m"
      and "A \<Turnstile>\<^sub>A (otherwith S {i} (orecvmsg R), other U {i} \<rightarrow>)
                 globala (\<lambda>(\<sigma>, _, \<sigma>'). U (\<sigma> i) (\<sigma>' i))"
    shows "A \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile> (otherwith S {i} (orecvmsg R), other U {i} \<rightarrow>) global P"
  proof (rule oinvariant_oreachableI)
    fix \<sigma> \<zeta>
    assume "(\<sigma>, \<zeta>) \<in> oreachable (A \<langle>\<langle>\<^bsub>i\<^esub> qmsg) (otherwith S {i} (orecvmsg R)) (other U {i})"
    then obtain s where "(\<sigma>, s) \<in> oreachable A (otherwith S {i} (orecvmsg R)) (other U {i})"
      by (auto dest!: par_qmsg_oreachable [OF _ assms(5,2-4)])
    with assms(1) show "global P (\<sigma>, \<zeta>)"
      by (auto dest: oinvariant_weakenD [OF assms(1)])
  qed

lemma lift_step_into_qmsg:
  assumes inv: "A \<Turnstile>\<^sub>A (otherwith S {i} (orecvmsg R), other U {i} \<rightarrow>) globala P"
      and ustutter: "\<And>\<xi>. U \<xi> \<xi>"
      and sgivesu: "\<And>\<xi> \<xi>'. S \<xi> \<xi>' \<Longrightarrow> U \<xi> \<xi>'"
      and upreservesq: "\<And>\<sigma> \<sigma>' m. \<lbrakk> \<forall>j. U (\<sigma> j) (\<sigma>' j); R \<sigma> m \<rbrakk> \<Longrightarrow> R \<sigma>' m"
      and self_sync: "A \<Turnstile>\<^sub>A (otherwith S {i} (orecvmsg R), other U {i} \<rightarrow>)
                            globala (\<lambda>(\<sigma>, _, \<sigma>'). U (\<sigma> i) (\<sigma>' i))"

      and recv_stutter:  "\<And>\<sigma> \<sigma>' m. \<lbrakk> \<forall>j. U (\<sigma> j) (\<sigma>' j); \<sigma>' i = \<sigma> i \<rbrakk> \<Longrightarrow> P (\<sigma>, receive m, \<sigma>')"
      and receive_right: "\<And>\<sigma> \<sigma>' m.  P (\<sigma>, receive m, \<sigma>') \<Longrightarrow> P (\<sigma>, \<tau>, \<sigma>')"
    shows "A \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (otherwith S {i} (orecvmsg R), other U {i} \<rightarrow>) globala P"
      (is "_ \<Turnstile>\<^sub>A (?owS, ?U \<rightarrow>) _")
  proof (rule ostep_invariantI)
    fix \<sigma> \<zeta> a \<sigma>' \<zeta>'
    assume or: "(\<sigma>, \<zeta>) \<in> oreachable (A \<langle>\<langle>\<^bsub>i\<^esub> qmsg) ?owS ?U"
       and otr: "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (A \<langle>\<langle>\<^bsub>i\<^esub> qmsg)"
       and "?owS \<sigma> \<sigma>' a"
    from this(2) have "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> oparp_sos i (trans A) (seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G)"
        by simp
    then obtain s msgs q s' msgs' q'
      where "\<zeta> = (s, (msgs, q))" "\<zeta>' = (s', (msgs', q'))"
        and "((\<sigma>, (s, (msgs, q))), a, (\<sigma>', (s', (msgs', q'))))
               \<in> oparp_sos i (trans A) (seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G)"
        by (metis prod_cases3)
    from this(1-2) and or
      obtain "(\<sigma>, s) \<in> oreachable A ?owS ?U"
             "(msgs, q) \<in> reachable qmsg (recvmsg (R \<sigma>))"
             "(\<forall>m\<in>set msgs. R \<sigma> m)"
       by (auto dest: par_qmsg_oreachable [OF _ self_sync ustutter sgivesu]
                elim!: upreservesq)
    from otr \<open>\<zeta> = (s, (msgs, q))\<close> \<open>\<zeta>' = (s', (msgs', q'))\<close>
      have "((\<sigma>, (s, (msgs, q))), a, (\<sigma>', (s', (msgs', q'))))
              \<in> oparp_sos i (trans A) (seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G)"
        by simp
    hence "globala P ((\<sigma>, s), a, (\<sigma>', s'))"
    proof
      assume "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans A"
      with \<open>(\<sigma>, s) \<in> oreachable A ?owS ?U\<close>
        show "globala P ((\<sigma>, s), a, (\<sigma>', s'))"
          using \<open>?owS \<sigma> \<sigma>' a\<close> by (rule ostep_invariantD [OF inv])
    next
      assume "((msgs, q), a, (msgs', q')) \<in> seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G"
         and "\<And>m. a \<noteq> send m"
         and "\<sigma>' i = \<sigma> i"
      from this(3) and ustutter have "U (\<sigma> i) (\<sigma>' i)" by simp
      with \<open>?owS \<sigma> \<sigma>' a\<close> and sgivesu have "\<forall>j. U (\<sigma> j) (\<sigma>' j)"
        by (clarsimp dest!: otherwith_syncD) metis
      moreover have "(\<exists>m. a = receive m) \<or> (a = \<tau>)"
      proof -
        from \<open>(msgs, q) \<in> reachable qmsg (recvmsg (R \<sigma>))\<close>
          have "(msgs, q) \<in> reachable qmsg TT" ..
        moreover from \<open>((msgs, q), a, (msgs', q')) \<in> seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G\<close>
          have "((msgs, q), a, (msgs', q')) \<in> trans qmsg" by simp
        ultimately show ?thesis
          using \<open>\<And>m. a \<noteq> send m\<close>
          by (auto dest!: step_invariantD [OF qmsg_send_receive_or_tau])
      qed
      ultimately show "globala P ((\<sigma>, s), a, (\<sigma>', s'))"
        using \<open>\<sigma>' i = \<sigma> i\<close>
        by simp (metis receive_right recv_stutter step_seq_tau)
    next
      fix m
      assume "a = \<tau>"
         and "((\<sigma>, s), receive m, (\<sigma>', s')) \<in> trans A"
         and "((msgs, q), send m, (msgs', q')) \<in> seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G"

      from \<open>(msgs, q) \<in> reachable qmsg (recvmsg (R \<sigma>))\<close>
        have "(msgs, q) \<in> reachable qmsg TT" ..
      moreover from \<open>((msgs, q), send m, (msgs', q')) \<in> seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G\<close>
        have "((msgs, q), send m, (msgs', q')) \<in> trans qmsg" by simp
      ultimately have "m\<in>set msgs"
        by (auto dest!: step_invariantD [OF qmsg_send_from_queue])

      with \<open>\<forall>m\<in>set msgs. R \<sigma> m\<close> have "R \<sigma> m" ..
      with \<open>?owS \<sigma> \<sigma>' a\<close> have "?owS \<sigma> \<sigma>' (receive m)"
          by (auto dest!: otherwith_syncD)

      with \<open>((\<sigma>, s), receive m, (\<sigma>', s')) \<in> trans A\<close>
        have "globala P ((\<sigma>, s), receive m, (\<sigma>', s'))"
          using \<open>(\<sigma>, s) \<in> oreachable A ?owS ?U\<close>
          by - (rule ostep_invariantD [OF inv])
      hence "P (\<sigma>, receive m, \<sigma>')" by simp
      hence "P (\<sigma>, \<tau>, \<sigma>')" by (rule receive_right)
      with \<open>a = \<tau>\<close> show "globala P ((\<sigma>, s), a, (\<sigma>', s'))" by simp
    qed
    with \<open>\<zeta> = (s, (msgs, q))\<close> and \<open>\<zeta>' = (s', (msgs', q'))\<close> show "globala P ((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>'))"
      by simp
  qed

lemma lift_step_into_qmsg_statelessassm:
  assumes "A \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_. R) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>) globala P"
      and "\<And>\<sigma> \<sigma>' m. \<sigma>' i = \<sigma> i \<Longrightarrow> P (\<sigma>, receive m, \<sigma>')"
      and "\<And>\<sigma> \<sigma>' m. P (\<sigma>, receive m, \<sigma>') \<Longrightarrow> P (\<sigma>, \<tau>, \<sigma>')"
    shows "A \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_. R) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>) globala P"
  proof -
    from assms(1) have *: "A \<Turnstile>\<^sub>A (otherwith (\<lambda>_ _. True) {i} (orecvmsg (\<lambda>_. R)),
                                 other (\<lambda>_ _. True) {i} \<rightarrow>) globala P"
      by rule auto
    hence "A \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A
              (otherwith (\<lambda>_ _. True) {i} (orecvmsg (\<lambda>_. R)), other (\<lambda>_ _. True) {i} \<rightarrow>) globala P"
      by (rule lift_step_into_qmsg)
         (auto elim!: assms(2-3) simp del: step_seq_tau)
    thus ?thesis by rule auto
  qed

end
