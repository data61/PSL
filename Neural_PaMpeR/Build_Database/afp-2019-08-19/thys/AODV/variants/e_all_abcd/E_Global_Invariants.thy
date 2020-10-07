(*  Title:       variants/e_all_abcd/Global_Invariants.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
    Author:      Peter Höfner, NICTA
*)

section "Global invariant proofs over sequential processes"

theory E_Global_Invariants
imports E_Seq_Invariants
        E_Aodv_Predicates
        E_Fresher
        E_Quality_Increases
        AWN.OAWN_Convert
        E_OAodv
begin

lemma other_quality_increases [elim]:
  assumes "other quality_increases I \<sigma> \<sigma>'"
    shows "\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)"
  using assms by (rule, clarsimp) (metis quality_increases_refl)

lemma weaken_otherwith [elim]:
    fixes m
  assumes *: "otherwith P I (orecvmsg Q) \<sigma> \<sigma>' a"
      and weakenP: "\<And>\<sigma> m. P \<sigma> m \<Longrightarrow> P' \<sigma> m"
      and weakenQ: "\<And>\<sigma> m. Q \<sigma> m \<Longrightarrow> Q' \<sigma> m"
    shows "otherwith P' I (orecvmsg Q') \<sigma> \<sigma>' a"
  proof
    fix j
    assume "j\<notin>I"
    with * have "P (\<sigma> j) (\<sigma>' j)" by auto
    thus "P' (\<sigma> j) (\<sigma>' j)" by (rule weakenP)
  next
    from * have "orecvmsg Q \<sigma> a" by auto
    thus "orecvmsg Q' \<sigma> a"
      by rule (erule weakenQ)
  qed

lemma oreceived_msg_inv:
  assumes other: "\<And>\<sigma> \<sigma>' m. \<lbrakk> P \<sigma> m; other Q {i} \<sigma> \<sigma>' \<rbrakk> \<Longrightarrow> P \<sigma>' m"
      and local: "\<And>\<sigma> m. P \<sigma> m \<Longrightarrow> P (\<sigma>(i := \<sigma> i\<lparr>msg := m\<rparr>)) m"
    shows "opaodv i \<Turnstile> (otherwith Q {i} (orecvmsg P), other Q {i} \<rightarrow>)
                       onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<sigma>, l). l \<in> {PAodv-:1} \<longrightarrow> P \<sigma> (msg (\<sigma> i)))"
  proof (inv_cterms, intro impI)
    fix \<sigma> \<sigma>' l
    assume "l = PAodv-:1 \<longrightarrow> P \<sigma> (msg (\<sigma> i))"
       and "l = PAodv-:1"
       and "other Q {i} \<sigma> \<sigma>'"
    from this(1-2) have "P \<sigma> (msg (\<sigma> i))" ..
    hence "P \<sigma>' (msg (\<sigma> i))" using \<open>other Q {i} \<sigma> \<sigma>'\<close>
      by (rule other)
    moreover from \<open>other Q {i} \<sigma> \<sigma>'\<close> have "\<sigma>' i = \<sigma> i" ..
    ultimately show "P \<sigma>' (msg (\<sigma>' i))" by simp
  next
    fix \<sigma> \<sigma>' msg
    assume "otherwith Q {i} (orecvmsg P) \<sigma> \<sigma>' (receive msg)"
       and "\<sigma>' i = \<sigma> i\<lparr>msg := msg\<rparr>"
    from this(1) have "P \<sigma> msg"
                 and "\<forall>j. j\<noteq>i \<longrightarrow> Q (\<sigma> j) (\<sigma>' j)" by auto
    from this(1) have "P (\<sigma>(i := \<sigma> i\<lparr>msg := msg\<rparr>)) msg" by (rule local)
    thus "P \<sigma>' msg"
    proof (rule other)
      from \<open>\<sigma>' i = \<sigma> i\<lparr>msg := msg\<rparr>\<close> and \<open>\<forall>j. j\<noteq>i \<longrightarrow> Q (\<sigma> j) (\<sigma>' j)\<close>
        show "other Q {i} (\<sigma>(i := \<sigma> i\<lparr>msg := msg\<rparr>)) \<sigma>'"
          by - (rule otherI, auto)
    qed
  qed

text \<open>(Equivalent to) Proposition 7.27\<close>

lemma local_quality_increases:
  "paodv i \<TTurnstile>\<^sub>A (recvmsg rreq_rrep_sn \<rightarrow>) onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), _, (\<xi>', _)). quality_increases \<xi> \<xi>')"
  proof (rule step_invariantI)
    fix s a s'
    assume sr: "s \<in> reachable (paodv i) (recvmsg rreq_rrep_sn)"
       and tr: "(s, a, s') \<in> trans (paodv i)"
       and rm: "recvmsg rreq_rrep_sn a"
    from sr have srTT: "s \<in> reachable (paodv i) TT" ..

    from route_tables_fresher sr tr rm
      have "onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), _, (\<xi>', _)). \<forall>dip\<in>kD (rt \<xi>). rt \<xi> \<sqsubseteq>\<^bsub>dip\<^esub> rt \<xi>') (s, a, s')"
        by (rule step_invariantD)

    moreover from known_destinations_increase srTT tr TT_True
      have "onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), _, (\<xi>', _)). kD (rt \<xi>) \<subseteq> kD (rt \<xi>')) (s, a, s')"
        by (rule step_invariantD)

    moreover from sqns_increase srTT tr TT_True
      have "onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), _, (\<xi>', _)). \<forall>ip. sqn (rt \<xi>) ip \<le> sqn (rt \<xi>') ip) (s, a, s')"
        by (rule step_invariantD)

     ultimately show "onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), _, (\<xi>', _)). quality_increases \<xi> \<xi>') (s, a, s')"
       unfolding onll_def by auto
  qed

lemmas olocal_quality_increases =
   open_seq_step_invariant [OF local_quality_increases initiali_aodv oaodv_trans aodv_trans,
                            simplified seqll_onll_swap]

lemma oquality_increases:
  "opaodv i \<Turnstile>\<^sub>A (otherwith quality_increases {i} (orecvmsg (\<lambda>_. rreq_rrep_sn)),
                other quality_increases {i} \<rightarrow>)
                onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<sigma>, _), _, (\<sigma>', _)). \<forall>j. quality_increases (\<sigma> j) (\<sigma>' j))"
  (is "_ \<Turnstile>\<^sub>A (?S, _ \<rightarrow>) _")
  proof (rule onll_ostep_invariantI, simp)
    fix \<sigma> p l a \<sigma>' p' l'
    assume or: "(\<sigma>, p) \<in> oreachable (opaodv i) ?S (other quality_increases {i})"
       and ll: "l \<in> labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p"
       and "?S \<sigma> \<sigma>' a"
       and tr: "((\<sigma>, p), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i"
       and ll': "l' \<in> labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p'"
    from this(1-3) have "orecvmsg (\<lambda>_. rreq_rrep_sn) \<sigma> a"
      by (auto dest!: oreachable_weakenE [where QS="act (recvmsg rreq_rrep_sn)"
                                            and QU="other quality_increases {i}"]
                      otherwith_actionD)
    with or have orw: "(\<sigma>, p) \<in> oreachable (opaodv i) (act (recvmsg rreq_rrep_sn))
                                                      (other quality_increases {i})"
      by - (erule oreachable_weakenE, auto)
    with tr ll ll' and \<open>orecvmsg (\<lambda>_. rreq_rrep_sn) \<sigma> a\<close> have "quality_increases (\<sigma> i) (\<sigma>' i)"
      by - (drule onll_ostep_invariantD [OF olocal_quality_increases], auto simp: seqll_def)
    with \<open>?S \<sigma> \<sigma>' a\<close> show "\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)"
      by (auto dest!: otherwith_syncD)
  qed

lemma rreq_rrep_nsqn_fresh_any_step_invariant:
  "opaodv i \<Turnstile>\<^sub>A (act (recvmsg rreq_rrep_sn), other A {i} \<rightarrow>)
                onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<sigma>, _), a, _). anycast (msg_fresh \<sigma>) a)"
  proof (rule ostep_invariantI, simp del: act_simp)
    fix \<sigma> p a \<sigma>' p'
    assume or: "(\<sigma>, p) \<in> oreachable (opaodv i) (act (recvmsg rreq_rrep_sn)) (other A {i})"
       and "((\<sigma>, p), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i"
       and recv: "act (recvmsg rreq_rrep_sn) \<sigma> \<sigma>' a"
    obtain l l' where "l\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p" and "l'\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p'"
      by (metis aodv_ex_label)
    from \<open>((\<sigma>, p), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i\<close>
      have tr: "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans (opaodv i)" by simp

    have "anycast (rreq_rrep_fresh (rt (\<sigma> i))) a"
    proof -
      have "opaodv i \<Turnstile>\<^sub>A (act (recvmsg rreq_rrep_sn), other A {i} \<rightarrow>)
                           onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (seqll i (\<lambda>((\<xi>, _), a, _). anycast (rreq_rrep_fresh (rt \<xi>)) a))"
        by (rule ostep_invariant_weakenE [OF
              open_seq_step_invariant [OF rreq_rrep_fresh_any_step_invariant initiali_aodv,
                                       simplified seqll_onll_swap]]) auto
      hence "onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (seqll i (\<lambda>((\<xi>, _), a, _). anycast (rreq_rrep_fresh (rt \<xi>)) a))
                                                                     ((\<sigma>, p), a, (\<sigma>', p'))"
        using or tr recv by - (erule(4) ostep_invariantE)
      thus ?thesis
        using \<open>l\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p\<close> and \<open>l'\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p'\<close> by auto
    qed

    moreover have "anycast (rerr_invalid (rt (\<sigma> i))) a"
    proof -
      have "opaodv i \<Turnstile>\<^sub>A (act (recvmsg rreq_rrep_sn), other A {i} \<rightarrow>)
                           onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (seqll i (\<lambda>((\<xi>, _), a, _). anycast (rerr_invalid (rt \<xi>)) a))"
        by (rule ostep_invariant_weakenE [OF
              open_seq_step_invariant [OF rerr_invalid_any_step_invariant initiali_aodv,
                                       simplified seqll_onll_swap]]) auto
      hence "onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (seqll i (\<lambda>((\<xi>, _), a, _). anycast (rerr_invalid (rt \<xi>)) a))
                                                                     ((\<sigma>, p), a, (\<sigma>', p'))"
        using or tr recv by - (erule(4) ostep_invariantE)
      thus ?thesis
        using \<open>l\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p\<close> and \<open>l'\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p'\<close> by auto
    qed

    moreover have "anycast rreq_rrep_sn a"
    proof -
      from or tr recv
        have "onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (seqll i (\<lambda>(_, a, _). anycast rreq_rrep_sn a)) ((\<sigma>, p), a, (\<sigma>', p'))"
          by (rule ostep_invariantE [OF
                open_seq_step_invariant [OF rreq_rrep_sn_any_step_invariant initiali_aodv
                                            oaodv_trans aodv_trans,
                                         simplified seqll_onll_swap]])
      thus ?thesis
        using \<open>l\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p\<close> and \<open>l'\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p'\<close> by auto
    qed

    moreover have "anycast (\<lambda>m. not_Pkt m \<longrightarrow> msg_sender m = i) a"
      proof -
        have "opaodv i \<Turnstile>\<^sub>A (act (recvmsg rreq_rrep_sn), other A {i} \<rightarrow>)
               onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (seqll i (\<lambda>((\<xi>, _), a, _). anycast (\<lambda>m. not_Pkt m \<longrightarrow> msg_sender m = i) a))"
          by (rule ostep_invariant_weakenE [OF
                open_seq_step_invariant [OF sender_ip_valid initiali_aodv,
                                         simplified seqll_onll_swap]]) auto
        thus ?thesis using or tr recv \<open>l\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p\<close> and \<open>l'\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p'\<close>
          by - (drule(3) onll_ostep_invariantD, auto)
      qed

    ultimately have "anycast (msg_fresh \<sigma>) a"
      by (simp_all add: anycast_def
                   del: msg_fresh
                   split: seq_action.split_asm msg.split_asm) simp_all
    thus "onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<sigma>, _), a, _). anycast (msg_fresh \<sigma>) a) ((\<sigma>, p), a, (\<sigma>', p'))"
      by auto
  qed

lemma oreceived_rreq_rrep_nsqn_fresh_inv:
  "opaodv i \<Turnstile> (otherwith quality_increases {i} (orecvmsg msg_fresh),
                other quality_increases {i} \<rightarrow>)
               onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<sigma>, l). l \<in> {PAodv-:1} \<longrightarrow> msg_fresh \<sigma> (msg (\<sigma> i)))"
  proof (rule oreceived_msg_inv)
    fix \<sigma> \<sigma>' m
    assume *: "msg_fresh \<sigma> m"
       and "other quality_increases {i} \<sigma> \<sigma>'"
    from this(2) have "\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)" ..
    thus "msg_fresh \<sigma>' m" using * ..
  next
    fix \<sigma> m
    assume "msg_fresh \<sigma> m"
    thus "msg_fresh (\<sigma>(i := \<sigma> i\<lparr>msg := m\<rparr>)) m"
    proof (cases m)
      fix dests sip
      assume "m = Rerr dests sip"
      with \<open>msg_fresh \<sigma> m\<close> show ?thesis by auto
    qed auto
  qed

lemma oquality_increases_nsqn_fresh:
  "opaodv i \<Turnstile>\<^sub>A (otherwith quality_increases {i} (orecvmsg msg_fresh),
                other quality_increases {i} \<rightarrow>)
                onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<sigma>, _), _, (\<sigma>', _)). \<forall>j. quality_increases (\<sigma> j) (\<sigma>' j))"
  by (rule ostep_invariant_weakenE [OF oquality_increases]) auto

lemma oosn_rreq:
  "opaodv i \<Turnstile> (otherwith quality_increases {i} (orecvmsg msg_fresh),
                other quality_increases {i} \<rightarrow>)
       onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (seql i (\<lambda>(\<xi>, l). l \<in> {PAodv-:4, PAodv-:5} \<union> {PRreq-:n |n. True} \<longrightarrow> 1 \<le> osn \<xi>))"
  by (rule oinvariant_weakenE [OF open_seq_invariant [OF osn_rreq initiali_aodv]])
     (auto simp: seql_onl_swap)

lemma rreq_sip:
  "opaodv i \<Turnstile> (otherwith quality_increases {i} (orecvmsg msg_fresh),
                other quality_increases {i} \<rightarrow>)
               onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<sigma>, l).
                   (l \<in> {PAodv-:4, PAodv-:5, PRreq-:0, PRreq-:2} \<and> sip (\<sigma> i) \<noteq> oip (\<sigma> i))
                    \<longrightarrow> oip (\<sigma> i) \<in> kD(rt (\<sigma> (sip (\<sigma> i))))
                        \<and> nsqn (rt (\<sigma> (sip (\<sigma> i)))) (oip (\<sigma> i)) \<ge> osn (\<sigma> i)
                        \<and> (nsqn (rt (\<sigma> (sip (\<sigma> i)))) (oip (\<sigma> i)) = osn (\<sigma> i)
                            \<longrightarrow> (hops (\<sigma> i) \<ge> the (dhops (rt (\<sigma> (sip (\<sigma> i)))) (oip (\<sigma> i)))
                                  \<or> the (flag (rt (\<sigma> (sip (\<sigma> i)))) (oip (\<sigma> i))) = inv)))"
    (is "_ \<Turnstile> (?S, ?U \<rightarrow>) _")
    proof (inv_cterms inv add: oseq_step_invariant_sterms [OF oquality_increases_nsqn_fresh
                                                              aodv_wf oaodv_trans]
                             onl_oinvariant_sterms [OF aodv_wf oreceived_rreq_rrep_nsqn_fresh_inv]
                             onl_oinvariant_sterms [OF aodv_wf oosn_rreq]
                   simp add: seqlsimp
                   simp del: One_nat_def, rule impI)
    fix \<sigma> \<sigma>' p l
    assume "(\<sigma>, p) \<in> oreachable (opaodv i) ?S ?U"
       and "l \<in> labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p"
       and pre:
           "(l = PAodv-:4 \<or> l = PAodv-:5 \<or> l = PRreq-:0 \<or> l = PRreq-:2) \<and> sip (\<sigma> i) \<noteq> oip (\<sigma> i)
             \<longrightarrow> oip (\<sigma> i) \<in> kD (rt (\<sigma> (sip (\<sigma> i))))
                 \<and> osn (\<sigma> i) \<le> nsqn (rt (\<sigma> (sip (\<sigma> i)))) (oip (\<sigma> i))
                 \<and> (nsqn (rt (\<sigma> (sip (\<sigma> i)))) (oip (\<sigma> i)) = osn (\<sigma> i)
                    \<longrightarrow> the (dhops (rt (\<sigma> (sip (\<sigma> i)))) (oip (\<sigma> i))) \<le> hops (\<sigma> i)
                        \<or> the (flag (rt (\<sigma> (sip (\<sigma> i)))) (oip (\<sigma> i))) = inv)"
       and "other quality_increases {i} \<sigma> \<sigma>'"
       and hyp: "(l=PAodv-:4 \<or> l=PAodv-:5 \<or> l=PRreq-:0 \<or> l=PRreq-:2) \<and> sip (\<sigma>' i) \<noteq> oip (\<sigma>' i)"
           (is "?labels \<and> sip (\<sigma>' i) \<noteq> oip (\<sigma>' i)")
    from this(4) have "\<sigma>' i = \<sigma> i" ..
    with hyp have hyp': "?labels \<and> sip (\<sigma> i) \<noteq> oip (\<sigma> i)" by simp
    show "oip (\<sigma>' i) \<in> kD (rt (\<sigma>' (sip (\<sigma>' i))))
          \<and> osn (\<sigma>' i) \<le> nsqn (rt (\<sigma>' (sip (\<sigma>' i)))) (oip (\<sigma>' i))
          \<and> (nsqn (rt (\<sigma>' (sip (\<sigma>' i)))) (oip (\<sigma>' i)) = osn (\<sigma>' i)
             \<longrightarrow> the (dhops (rt (\<sigma>' (sip (\<sigma>' i)))) (oip (\<sigma>' i))) \<le> hops (\<sigma>' i)
                  \<or> the (flag (rt (\<sigma>' (sip (\<sigma>' i)))) (oip (\<sigma>' i))) = inv)"
    proof (cases "sip (\<sigma> i) = i")
      assume "sip (\<sigma> i) \<noteq> i"
      from \<open>other quality_increases {i} \<sigma> \<sigma>'\<close>
        have "quality_increases (\<sigma> (sip (\<sigma> i))) (\<sigma>' (sip (\<sigma>' i)))"
          by (rule otherE)  (clarsimp simp: \<open>sip (\<sigma> i) \<noteq> i\<close>)
      moreover from \<open>(\<sigma>, p) \<in> oreachable (opaodv i) ?S ?U\<close> \<open>l \<in> labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p\<close> and hyp
        have "1 \<le> osn (\<sigma>' i)"
          by (auto dest!: onl_oinvariant_weakenD [OF oosn_rreq]
                   simp add: seqlsimp \<open>\<sigma>' i = \<sigma> i\<close>)
      moreover from \<open>sip (\<sigma> i) \<noteq> i\<close> hyp' and pre
        have "oip (\<sigma>' i) \<in> kD (rt (\<sigma> (sip (\<sigma> i))))
              \<and> osn (\<sigma>' i) \<le> nsqn (rt (\<sigma> (sip (\<sigma> i)))) (oip (\<sigma>' i))
              \<and> (nsqn (rt (\<sigma> (sip (\<sigma> i)))) (oip (\<sigma>' i)) = osn (\<sigma>' i)
                  \<longrightarrow> the (dhops (rt (\<sigma> (sip (\<sigma> i)))) (oip (\<sigma>' i))) \<le> hops (\<sigma>' i)
                       \<or> the (flag (rt (\<sigma> (sip (\<sigma> i)))) (oip (\<sigma>' i))) = inv)"
        by (auto simp: \<open>\<sigma>' i = \<sigma> i\<close>)
      ultimately show ?thesis
        by (rule quality_increases_rreq_rrep_props)
    next
      assume "sip (\<sigma> i) = i" thus ?thesis
        using \<open>\<sigma>' i = \<sigma> i\<close> hyp and pre by auto
    qed
  qed (auto elim!: quality_increases_rreq_rrep_props')

lemma odsn_rrep:
  "opaodv i \<Turnstile> (otherwith quality_increases {i} (orecvmsg msg_fresh),
                other quality_increases {i} \<rightarrow>)
      onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (seql i (\<lambda>(\<xi>, l). l \<in> {PAodv-:6, PAodv-:7} \<union> {PRrep-:n|n. True} \<longrightarrow> 1 \<le> dsn \<xi>))"
  by (rule oinvariant_weakenE [OF open_seq_invariant [OF dsn_rrep initiali_aodv]])
     (auto simp: seql_onl_swap)

lemma rrep_sip:
  "opaodv i \<Turnstile> (otherwith quality_increases {i} (orecvmsg msg_fresh),
                other quality_increases {i} \<rightarrow>)
               onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<sigma>, l).
                   (l \<in> {PAodv-:6, PAodv-:7, PRrep-:0, PRrep-:1} \<and> sip (\<sigma> i) \<noteq> dip (\<sigma> i))
                    \<longrightarrow> dip (\<sigma> i) \<in> kD(rt (\<sigma> (sip (\<sigma> i))))
                        \<and> nsqn (rt (\<sigma> (sip (\<sigma> i)))) (dip (\<sigma> i)) \<ge> dsn (\<sigma> i)
                        \<and> (nsqn (rt (\<sigma> (sip (\<sigma> i)))) (dip (\<sigma> i)) = dsn (\<sigma> i)
                            \<longrightarrow> (hops (\<sigma> i) \<ge> the (dhops (rt (\<sigma> (sip (\<sigma> i)))) (dip (\<sigma> i)))
                                  \<or> the (flag (rt (\<sigma> (sip (\<sigma> i)))) (dip (\<sigma> i))) = inv)))"
    (is "_ \<Turnstile> (?S, ?U \<rightarrow>) _")
  proof (inv_cterms inv add: oseq_step_invariant_sterms [OF oquality_increases_nsqn_fresh aodv_wf
                                                            oaodv_trans]
                             onl_oinvariant_sterms [OF aodv_wf oreceived_rreq_rrep_nsqn_fresh_inv]
                             onl_oinvariant_sterms [OF aodv_wf odsn_rrep]
                   simp del: One_nat_def, rule impI)
    fix \<sigma> \<sigma>' p l
    assume "(\<sigma>, p) \<in> oreachable (opaodv i) ?S ?U"
       and "l \<in> labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p"
       and pre:
           "(l = PAodv-:6 \<or> l = PAodv-:7 \<or> l = PRrep-:0 \<or> l = PRrep-:1) \<and> sip (\<sigma> i) \<noteq> dip (\<sigma> i)
           \<longrightarrow> dip (\<sigma> i) \<in> kD (rt (\<sigma> (sip (\<sigma> i))))
               \<and> dsn (\<sigma> i) \<le> nsqn (rt (\<sigma> (sip (\<sigma> i)))) (dip (\<sigma> i))
               \<and> (nsqn (rt (\<sigma> (sip (\<sigma> i)))) (dip (\<sigma> i)) = dsn (\<sigma> i)
                  \<longrightarrow> the (dhops (rt (\<sigma> (sip (\<sigma> i)))) (dip (\<sigma> i))) \<le> hops (\<sigma> i)
                      \<or> the (flag (rt (\<sigma> (sip (\<sigma> i)))) (dip (\<sigma> i))) = inv)"
       and "other quality_increases {i} \<sigma> \<sigma>'"
       and hyp: "(l=PAodv-:6 \<or> l=PAodv-:7 \<or> l=PRrep-:0 \<or> l=PRrep-:1) \<and> sip (\<sigma>' i) \<noteq> dip (\<sigma>' i)"
           (is "?labels \<and> sip (\<sigma>' i) \<noteq> dip (\<sigma>' i)")
    from this(4) have "\<sigma>' i = \<sigma> i" ..
    with hyp have hyp': "?labels \<and> sip (\<sigma> i) \<noteq> dip (\<sigma> i)" by simp
    show "dip (\<sigma>' i) \<in> kD (rt (\<sigma>' (sip (\<sigma>' i))))
          \<and> dsn (\<sigma>' i) \<le> nsqn (rt (\<sigma>' (sip (\<sigma>' i)))) (dip (\<sigma>' i))
          \<and> (nsqn (rt (\<sigma>' (sip (\<sigma>' i)))) (dip (\<sigma>' i)) = dsn (\<sigma>' i)
             \<longrightarrow> the (dhops (rt (\<sigma>' (sip (\<sigma>' i)))) (dip (\<sigma>' i))) \<le> hops (\<sigma>' i)
                 \<or> the (flag (rt (\<sigma>' (sip (\<sigma>' i)))) (dip (\<sigma>' i))) = inv)"
    proof (cases "sip (\<sigma> i) = i")
      assume "sip (\<sigma> i) \<noteq> i"
      from \<open>other quality_increases {i} \<sigma> \<sigma>'\<close>
        have "quality_increases (\<sigma> (sip (\<sigma> i))) (\<sigma>' (sip (\<sigma>' i)))"
          by (rule otherE)  (clarsimp simp: \<open>sip (\<sigma> i) \<noteq> i\<close>)
      moreover from \<open>(\<sigma>, p) \<in> oreachable (opaodv i) ?S ?U\<close> \<open>l \<in> labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p\<close> and hyp
        have "1 \<le> dsn (\<sigma>' i)"
          by (auto dest!: onl_oinvariant_weakenD [OF odsn_rrep]
                   simp add: seqlsimp \<open>\<sigma>' i = \<sigma> i\<close>)
      moreover from \<open>sip (\<sigma> i) \<noteq> i\<close> hyp' and pre
        have "dip (\<sigma>' i) \<in> kD (rt (\<sigma> (sip (\<sigma> i))))
              \<and> dsn (\<sigma>' i) \<le> nsqn (rt (\<sigma> (sip (\<sigma> i)))) (dip (\<sigma>' i))
              \<and> (nsqn (rt (\<sigma> (sip (\<sigma> i)))) (dip (\<sigma>' i)) = dsn (\<sigma>' i)
                 \<longrightarrow> the (dhops (rt (\<sigma> (sip (\<sigma> i)))) (dip (\<sigma>' i))) \<le> hops (\<sigma>' i)
                     \<or> the (flag (rt (\<sigma> (sip (\<sigma> i)))) (dip (\<sigma>' i))) = inv)"
        by (auto simp: \<open>\<sigma>' i = \<sigma> i\<close>)
      ultimately show ?thesis
        by (rule quality_increases_rreq_rrep_props)
    next
      assume "sip (\<sigma> i) = i" thus ?thesis
        using \<open>\<sigma>' i = \<sigma> i\<close> hyp and pre by auto
    qed
  qed (auto simp add: seqlsimp elim!: quality_increases_rreq_rrep_props')

lemma rerr_sip:
  "opaodv i \<Turnstile> (otherwith quality_increases {i} (orecvmsg msg_fresh),
                other quality_increases {i} \<rightarrow>)
               onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<sigma>, l).
                 l \<in> {PAodv-:8, PAodv-:9, PRerr-:0, PRerr-:1}
                 \<longrightarrow> (\<forall>ripc\<in>dom(dests (\<sigma> i)). ripc\<in>kD(rt (\<sigma> (sip (\<sigma> i)))) \<and>
                        the (dests (\<sigma> i) ripc) - 1 \<le> nsqn (rt (\<sigma> (sip (\<sigma> i)))) ripc))"
  (is "_ \<Turnstile> (?S, ?U \<rightarrow>) _")
  proof -
    { fix dests rip sip rsn and \<sigma> \<sigma>' :: "ip \<Rightarrow> state"
      assume qinc: "\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)"
         and *: "\<forall>rip\<in>dom dests. rip \<in> kD (rt (\<sigma> sip))
                                  \<and> the (dests rip) - 1 \<le> nsqn (rt (\<sigma> sip)) rip"
         and "dests rip = Some rsn"
      from this(3) have "rip\<in>dom dests" by auto
      with * and \<open>dests rip = Some rsn\<close> have "rip\<in>kD(rt (\<sigma> sip))"
                                         and "rsn - 1 \<le> nsqn (rt (\<sigma> sip)) rip"
        by (auto dest!: bspec)
      from qinc have "quality_increases (\<sigma> sip) (\<sigma>' sip)" ..
      have "rip \<in> kD(rt (\<sigma>' sip)) \<and> rsn - 1 \<le> nsqn (rt (\<sigma>' sip)) rip"
      proof
        from \<open>rip\<in>kD(rt (\<sigma> sip))\<close> and \<open>quality_increases (\<sigma> sip) (\<sigma>' sip)\<close>
          show "rip \<in> kD(rt (\<sigma>' sip))" ..
      next
        from \<open>rip\<in>kD(rt (\<sigma> sip))\<close> and \<open>quality_increases (\<sigma> sip) (\<sigma>' sip)\<close>
          have "nsqn (rt (\<sigma> sip)) rip \<le> nsqn (rt (\<sigma>' sip)) rip" ..
        with \<open>rsn - 1 \<le> nsqn (rt (\<sigma> sip)) rip\<close> show "rsn - 1 \<le> nsqn (rt (\<sigma>' sip)) rip"
          by (rule le_trans)
      qed
    } note partial = this

    show ?thesis
      by (inv_cterms inv add: oseq_step_invariant_sterms [OF oquality_increases_nsqn_fresh aodv_wf
                                                             oaodv_trans]
                              onl_oinvariant_sterms [OF aodv_wf oreceived_rreq_rrep_nsqn_fresh_inv]
                              other_quality_increases other_localD
                    simp del: One_nat_def, intro conjI)
         (clarsimp simp del: One_nat_def split: if_split_asm option.split_asm, erule(2) partial)+
  qed

lemma prerr_guard: "paodv i \<TTurnstile>
                  onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l). (l = PRerr-:1
                      \<longrightarrow> (\<forall>ip\<in>dom(dests \<xi>). ip\<in>vD(rt \<xi>)
                                             \<and> the (nhop (rt \<xi>) ip) = sip \<xi>
                                             \<and> sqn (rt \<xi>) ip < the (dests \<xi> ip))))"
  by (inv_cterms) (clarsimp split: option.split_asm if_split_asm)

lemmas odests_vD_inc_sqn =
         open_seq_invariant [OF dests_vD_inc_sqn initiali_aodv oaodv_trans aodv_trans,
                             simplified seql_onl_swap,
                             THEN oinvariant_anyact]

lemmas oprerr_guard =
         open_seq_invariant [OF prerr_guard initiali_aodv oaodv_trans aodv_trans,
                             simplified seql_onl_swap,
                             THEN oinvariant_anyact]

text \<open>Proposition 7.28\<close>

lemma seq_compare_next_hop':
  "opaodv i \<Turnstile> (otherwith quality_increases {i} (orecvmsg msg_fresh),
                other quality_increases {i} \<rightarrow>) onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<sigma>, _).
                   \<forall>dip. let nhip = the (nhop (rt (\<sigma> i)) dip)
                         in dip \<in> kD(rt (\<sigma> i)) \<and> nhip \<noteq> dip \<longrightarrow>
                            dip \<in> kD(rt (\<sigma> nhip)) \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma> nhip)) dip)"
  (is "_ \<Turnstile> (?S, ?U \<rightarrow>) _")
  proof -

  { fix nhop and \<sigma> \<sigma>' :: "ip \<Rightarrow> state"
    assume  pre: "\<forall>dip\<in>kD(rt (\<sigma> i)). nhop dip \<noteq> dip \<longrightarrow>
                    dip\<in>kD(rt (\<sigma> (nhop dip))) \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma> (nhop dip))) dip"
       and qinc: "\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)"
    have "\<forall>dip\<in>kD(rt (\<sigma> i)). nhop dip \<noteq> dip \<longrightarrow>
                  dip\<in>kD(rt (\<sigma>' (nhop dip))) \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma>' (nhop dip))) dip"
    proof (intro ballI impI)
      fix dip
      assume "dip\<in>kD(rt (\<sigma> i))"
         and "nhop dip \<noteq> dip"
      with pre have "dip\<in>kD(rt (\<sigma> (nhop dip)))"
                and "nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma> (nhop dip))) dip"
        by auto
      from qinc have qinc_nhop: "quality_increases (\<sigma> (nhop dip)) (\<sigma>' (nhop dip))" ..
      with \<open>dip\<in>kD(rt (\<sigma> (nhop dip)))\<close> have "dip\<in>kD (rt (\<sigma>' (nhop dip)))" ..

      moreover have "nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma>' (nhop dip))) dip"
      proof -
        from \<open>dip\<in>kD(rt (\<sigma> (nhop dip)))\<close> qinc_nhop
          have "nsqn (rt (\<sigma> (nhop dip))) dip \<le> nsqn (rt (\<sigma>' (nhop dip))) dip" ..
        with \<open>nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma> (nhop dip))) dip\<close> show ?thesis
          by simp
      qed

      ultimately show "dip\<in>kD(rt (\<sigma>' (nhop dip)))
                       \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma>' (nhop dip))) dip" ..
    qed
  } note basic = this

  { fix nhop and \<sigma> \<sigma>' :: "ip \<Rightarrow> state"
    assume pre: "\<forall>dip\<in>kD(rt (\<sigma> i)). nhop dip \<noteq> dip \<longrightarrow> dip\<in>kD(rt (\<sigma> (nhop dip)))
                                             \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma> (nhop dip))) dip"
       and ndest: "\<forall>ripc\<in>dom (dests (\<sigma> i)). ripc \<in> kD (rt (\<sigma> (sip (\<sigma> i))))
                                   \<and> the (dests (\<sigma> i) ripc) - 1 \<le> nsqn (rt (\<sigma> (sip (\<sigma> i)))) ripc"
       and issip: "\<forall>ip\<in>dom (dests (\<sigma> i)). nhop ip = sip (\<sigma> i)"
       and qinc: "\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)"
    have "\<forall>dip\<in>kD(rt (\<sigma> i)). nhop dip \<noteq> dip \<longrightarrow> dip \<in> kD (rt (\<sigma>' (nhop dip)))
                 \<and> nsqn (invalidate (rt (\<sigma> i)) (dests (\<sigma> i))) dip \<le> nsqn (rt (\<sigma>' (nhop dip))) dip"
    proof (intro ballI impI)
      fix dip
      assume "dip\<in>kD(rt (\<sigma> i))"
         and "nhop dip \<noteq> dip"
      with pre and qinc have "dip\<in>kD(rt (\<sigma>' (nhop dip)))"
                         and "nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma>' (nhop dip))) dip"
        by (auto dest!: basic)

      have "nsqn (invalidate (rt (\<sigma> i)) (dests (\<sigma> i))) dip \<le> nsqn (rt (\<sigma>' (nhop dip))) dip"
      proof (cases "dip\<in>dom (dests (\<sigma> i))")
        assume "dip\<in>dom (dests (\<sigma> i))"
        with \<open>dip\<in>kD(rt (\<sigma> i))\<close> obtain dsn where "dests (\<sigma> i) dip = Some dsn"
          by auto
        with \<open>dip\<in>kD(rt (\<sigma> i))\<close> have "nsqn (invalidate (rt (\<sigma> i)) (dests (\<sigma> i))) dip = dsn - 1"
           by (rule nsqn_invalidate_eq)
        moreover have "dsn - 1 \<le> nsqn (rt (\<sigma>' (nhop dip))) dip"
        proof -
          from \<open>dests (\<sigma> i) dip = Some dsn\<close> have "the (dests (\<sigma> i) dip) = dsn" by simp
          with ndest and \<open>dip\<in>dom (dests (\<sigma> i))\<close> have "dip \<in> kD (rt (\<sigma> (sip (\<sigma> i))))"
                                                      "dsn - 1 \<le> nsqn (rt (\<sigma> (sip (\<sigma> i)))) dip"
            by auto
          moreover from issip and \<open>dip\<in>dom (dests (\<sigma> i))\<close> have "nhop dip = sip (\<sigma> i)" ..
          ultimately have "dip \<in> kD (rt (\<sigma> (nhop dip)))"
                      and "dsn - 1 \<le> nsqn (rt (\<sigma> (nhop dip))) dip" by auto
          with qinc show "dsn - 1 \<le> nsqn (rt (\<sigma>' (nhop dip))) dip"
            by simp (metis kD_nsqn_quality_increases_trans)
        qed
        ultimately show ?thesis by simp
      next
        assume "dip \<notin> dom (dests (\<sigma> i))"
        with \<open>dip\<in>kD(rt (\<sigma> i))\<close>
          have "nsqn (invalidate (rt (\<sigma> i)) (dests (\<sigma> i))) dip = nsqn (rt (\<sigma> i)) dip"
            by (rule nsqn_invalidate_other)
        with \<open>nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma>' (nhop dip))) dip\<close> show ?thesis by simp
      qed
      with \<open>dip\<in>kD(rt (\<sigma>' (nhop dip)))\<close>
        show "dip \<in> kD (rt (\<sigma>' (nhop dip)))
              \<and> nsqn (invalidate (rt (\<sigma> i)) (dests (\<sigma> i))) dip \<le> nsqn (rt (\<sigma>' (nhop dip))) dip" ..
    qed
  } note basic_prerr = this

  { fix \<sigma> \<sigma>' :: "ip \<Rightarrow> state"
    assume a1: "\<forall>dip\<in>kD(rt (\<sigma> i)). the (nhop (rt (\<sigma> i)) dip) \<noteq> dip
                \<longrightarrow> dip\<in>kD(rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))
                    \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip)))) dip"
       and a2: "\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)"
    have "\<forall>dip\<in>kD(rt (\<sigma> i)).
          the (nhop (update (rt (\<sigma> i)) (sip (\<sigma> i)) (0, unk, val, Suc 0, sip (\<sigma> i))) dip) \<noteq> dip \<longrightarrow>
          dip\<in>kD(rt (\<sigma>' (the (nhop (update (rt (\<sigma> i)) (sip (\<sigma> i))
                                        (0, unk, val, Suc 0, sip (\<sigma> i)))
                                  dip)))) \<and>
          nsqn (update (rt (\<sigma> i)) (sip (\<sigma> i)) (0, unk, val, Suc 0, sip (\<sigma> i))) dip
          \<le> nsqn (rt (\<sigma>' (the (nhop (update (rt (\<sigma> i)) (sip (\<sigma> i))
                                      (0, unk, val, Suc 0, sip (\<sigma> i)))
                                dip))))
             dip" (is "\<forall>dip\<in>kD(rt (\<sigma> i)). ?P dip")
    proof
      fix dip
      assume "dip\<in>kD(rt (\<sigma> i))"
      with a1 and a2  
        have "the (nhop (rt (\<sigma> i)) dip) \<noteq> dip \<longrightarrow> dip\<in>kD(rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip))))
                        \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip)))) dip"
           by - (drule(1) basic, auto)
      thus "?P dip" by (cases "dip = sip (\<sigma> i)") auto
    qed
  } note nhop_update_sip = this

  { fix \<sigma> \<sigma>' oip sip osn hops
    assume pre: "\<forall>dip\<in>kD (rt (\<sigma> i)). the (nhop (rt (\<sigma> i)) dip) \<noteq> dip
                 \<longrightarrow> dip\<in>kD(rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))
                     \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip)))) dip"
       and qinc: "\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)"
       and *: "sip \<noteq> oip \<longrightarrow> oip\<in>kD(rt (\<sigma> sip))
                             \<and> osn \<le> nsqn (rt (\<sigma> sip)) oip
                             \<and> (nsqn (rt (\<sigma> sip)) oip = osn
                                \<longrightarrow> the (dhops (rt (\<sigma> sip)) oip) \<le> hops
                                    \<or> the (flag (rt (\<sigma> sip)) oip) = inv)"
    from pre and qinc
      have pre': "\<forall>dip\<in>kD (rt (\<sigma> i)). the (nhop (rt (\<sigma> i)) dip) \<noteq> dip
                   \<longrightarrow> dip\<in>kD(rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip))))
                       \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip)))) dip"
        by (rule basic)
    have "(the (nhop (update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)) oip) \<noteq> oip
           \<longrightarrow> oip\<in>kD(rt (\<sigma>' (the (nhop (update (rt (\<sigma> i)) oip
                                                   (osn, kno, val, Suc hops, sip)) oip))))
                \<and> nsqn (update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)) oip
                   \<le> nsqn (rt (\<sigma>' (the (nhop (update (rt (\<sigma> i)) oip
                                                   (osn, kno, val, Suc hops, sip)) oip)))) oip)"
       (is "?nhop_not_oip \<longrightarrow> ?oip_in_kD \<and> ?nsqn_le_nsqn")
     proof (rule, split update_rt_split_asm)
       assume "rt (\<sigma> i) = update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)"
          and "the (nhop (rt (\<sigma> i)) oip) \<noteq> oip"
       with pre' show "?oip_in_kD \<and> ?nsqn_le_nsqn" by auto
     next
       assume rtnot: "rt (\<sigma> i) \<noteq> update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)"
          and notoip: ?nhop_not_oip
       with * qinc have ?oip_in_kD
         by (clarsimp elim!: kD_quality_increases)
       moreover with * pre qinc rtnot notoip have ?nsqn_le_nsqn
        by simp (metis kD_nsqn_quality_increases_trans)
       ultimately show "?oip_in_kD \<and> ?nsqn_le_nsqn" ..
     qed
  } note update1 = this

  { fix \<sigma> \<sigma>' oip sip osn hops
    assume pre: "\<forall>dip\<in>kD (rt (\<sigma> i)). the (nhop (rt (\<sigma> i)) dip) \<noteq> dip
                  \<longrightarrow> dip\<in>kD(rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))
                      \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip)))) dip"
       and qinc: "\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)"
       and *: "sip \<noteq> oip \<longrightarrow> oip\<in>kD(rt (\<sigma> sip))
                           \<and> osn \<le> nsqn (rt (\<sigma> sip)) oip
                           \<and> (nsqn (rt (\<sigma> sip)) oip = osn
                              \<longrightarrow> the (dhops (rt (\<sigma> sip)) oip) \<le> hops
                                  \<or> the (flag (rt (\<sigma> sip)) oip) = inv)"
    from pre and qinc
      have pre': "\<forall>dip\<in>kD (rt (\<sigma> i)). the (nhop (rt (\<sigma> i)) dip) \<noteq> dip
                   \<longrightarrow> dip\<in>kD(rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip))))
                       \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip)))) dip"
        by (rule basic)
    have "\<forall>dip\<in>kD(rt (\<sigma> i)).
           the (nhop (update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)) dip) \<noteq> dip
           \<longrightarrow> dip\<in>kD(rt (\<sigma>' (the (nhop (update (rt (\<sigma> i)) oip
                                                  (osn, kno, val, Suc hops, sip)) dip))))
               \<and> nsqn (update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)) dip
                  \<le> nsqn (rt (\<sigma>' (the (nhop (update (rt (\<sigma> i)) oip
                                                  (osn, kno, val, Suc hops, sip)) dip)))) dip"
       (is "\<forall>dip\<in>kD(rt (\<sigma> i)). _ \<longrightarrow> ?dip_in_kD dip \<and> ?nsqn_le_nsqn dip")
     proof (intro ballI impI, split update_rt_split_asm)
       fix dip
       assume "dip\<in>kD(rt (\<sigma> i))"
          and "the (nhop (rt (\<sigma> i)) dip) \<noteq> dip"
          and "rt (\<sigma> i) = update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)"
        with pre' show "?dip_in_kD dip \<and> ?nsqn_le_nsqn dip" by simp
     next
       fix dip
       assume "dip\<in>kD(rt (\<sigma> i))"
          and notdip: "the (nhop (update (rt (\<sigma> i)) oip
                             (osn, kno, val, Suc hops, sip)) dip) \<noteq> dip"
          and rtnot: "rt (\<sigma> i) \<noteq> update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)"
       show "?dip_in_kD dip \<and> ?nsqn_le_nsqn dip"
       proof (cases "dip = oip")
         assume "dip \<noteq> oip"
         with pre' \<open>dip\<in>kD(rt (\<sigma> i))\<close> notdip
           show ?thesis by clarsimp
       next
         assume "dip = oip"
         with rtnot qinc \<open>dip\<in>kD(rt (\<sigma> i))\<close> notdip *
           have "?dip_in_kD dip"
            by simp (metis kD_quality_increases)
         moreover from \<open>dip = oip\<close> rtnot qinc \<open>dip\<in>kD(rt (\<sigma> i))\<close> notdip *
           have "?nsqn_le_nsqn dip" by simp (metis kD_nsqn_quality_increases_trans)
         ultimately show ?thesis ..
       qed
     qed
  } note update2 = this

  have "opaodv i \<Turnstile> (?S, ?U \<rightarrow>) onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<sigma>, _).
                   \<forall>dip \<in> kD(rt (\<sigma> i)). the (nhop (rt (\<sigma> i)) dip) \<noteq> dip
                      \<longrightarrow> dip \<in> kD(rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))
                          \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip)))) dip)"
    by (inv_cterms inv add: oseq_step_invariant_sterms [OF oquality_increases_nsqn_fresh aodv_wf
                                                           oaodv_trans]
                            onl_oinvariant_sterms [OF aodv_wf odests_vD_inc_sqn]
                            onl_oinvariant_sterms [OF aodv_wf oprerr_guard]
                            onl_oinvariant_sterms [OF aodv_wf rreq_sip]
                            onl_oinvariant_sterms [OF aodv_wf rrep_sip]
                            onl_oinvariant_sterms [OF aodv_wf rerr_sip]
                            other_quality_increases
                            other_localD
                      solve: basic basic_prerr
                      simp add: seqlsimp nsqn_invalidate nhop_update_sip
                      simp del: One_nat_def)
       (rule conjI, erule(2) update1, erule(2) update2)+

    thus ?thesis unfolding Let_def by auto
  qed

text \<open>Proposition 7.30\<close>

lemmas okD_unk_or_atleast_one =
         open_seq_invariant [OF kD_unk_or_atleast_one initiali_aodv,
                             simplified seql_onl_swap]

lemmas ozero_seq_unk_hops_one =
         open_seq_invariant [OF zero_seq_unk_hops_one initiali_aodv,
                             simplified seql_onl_swap]

lemma oreachable_fresh_okD_unk_or_atleast_one:
    fixes dip
  assumes "(\<sigma>, p) \<in> oreachable (opaodv i)
                       (otherwith ((=)) {i} (orecvmsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m
                                                             \<and> msg_zhops m)))
                       (other quality_increases {i})"
      and "dip\<in>kD(rt (\<sigma> i))"
    shows "\<pi>\<^sub>3(the (rt (\<sigma> i) dip)) = unk \<or> 1 \<le> \<pi>\<^sub>2(the (rt (\<sigma> i) dip))"
    (is "?P dip")
  proof -
    have "\<exists>l. l\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p" by (metis aodv_ex_label)
    with assms(1) have "\<forall>dip\<in>kD (rt (\<sigma> i)). ?P dip"
      by - (drule oinvariant_weakenD [OF okD_unk_or_atleast_one [OF oaodv_trans aodv_trans]],
            auto dest!: otherwith_actionD onlD simp: seqlsimp)
    with \<open>dip\<in>kD(rt (\<sigma> i))\<close> show ?thesis by simp
  qed

lemma oreachable_fresh_ozero_seq_unk_hops_one:
    fixes dip
  assumes "(\<sigma>, p) \<in> oreachable (opaodv i)
                     (otherwith ((=)) {i} (orecvmsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m
                                                         \<and> msg_zhops m)))
                     (other quality_increases {i})"
      and "dip\<in>kD(rt (\<sigma> i))"
    shows "sqn (rt (\<sigma> i)) dip = 0 \<longrightarrow>
             sqnf (rt (\<sigma> i)) dip = unk
             \<and> the (dhops (rt (\<sigma> i)) dip) = 1
             \<and> the (nhop (rt (\<sigma> i)) dip) = dip"
    (is "?P dip")
  proof -
    have "\<exists>l. l\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p" by (metis aodv_ex_label)
    with assms(1) have "\<forall>dip\<in>kD (rt (\<sigma> i)). ?P dip"
      by - (drule oinvariant_weakenD [OF ozero_seq_unk_hops_one [OF oaodv_trans aodv_trans]],
            auto dest!: onlD otherwith_actionD simp: seqlsimp)
    with \<open>dip\<in>kD(rt (\<sigma> i))\<close> show ?thesis by simp
  qed

lemma seq_nhop_quality_increases':
  shows "opaodv i \<Turnstile> (otherwith ((=)) {i}
                        (orecvmsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m \<and> msg_zhops m)),
                         other quality_increases {i} \<rightarrow>)
                        onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<sigma>, _). \<forall>dip. let nhip = the (nhop (rt (\<sigma> i)) dip)
                                               in dip \<in> vD (rt (\<sigma> i)) \<inter> vD (rt (\<sigma> nhip))
                                                  \<and> nhip \<noteq> dip
                                                  \<longrightarrow> (rt (\<sigma> i)) \<sqsubset>\<^bsub>dip\<^esub> (rt (\<sigma> nhip)))"
  (is "_ \<Turnstile> (?S i, _ \<rightarrow>) _")
  proof -
    have weaken:
      "\<And>p I Q R P. p \<Turnstile> (otherwith quality_increases I (orecvmsg Q), other quality_increases I \<rightarrow>) P
       \<Longrightarrow> p \<Turnstile> (otherwith ((=)) I (orecvmsg (\<lambda>\<sigma> m. Q \<sigma> m \<and> R \<sigma> m)), other quality_increases I \<rightarrow>) P"
        by auto
    {
      fix i a and \<sigma> \<sigma>' :: "ip \<Rightarrow> state"
      assume a1: "\<forall>dip. dip\<in>vD(rt (\<sigma> i))
                        \<and> dip\<in>vD(rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))
                        \<and> (the (nhop (rt (\<sigma> i)) dip)) \<noteq> dip
                         \<longrightarrow> rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip)))"
         and ow: "?S i \<sigma> \<sigma>' a"
      have "\<forall>dip. dip\<in>vD(rt (\<sigma> i))
                  \<and> dip\<in>vD (rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip))))
                  \<and> (the (nhop (rt (\<sigma> i)) dip)) \<noteq> dip
               \<longrightarrow> rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip)))"
      proof clarify
        fix dip
        assume a2: "dip\<in>vD(rt (\<sigma> i))"
           and a3: "dip\<in>vD (rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip))))"
           and a4: "(the (nhop (rt (\<sigma> i)) dip)) \<noteq> dip"
        from ow have "\<forall>j. j \<noteq> i \<longrightarrow> \<sigma> j = \<sigma>' j" by auto
        show "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip)))"
        proof (cases "(the (nhop (rt (\<sigma> i)) dip)) = i")
          assume "(the (nhop (rt (\<sigma> i)) dip)) = i"
          with \<open>dip \<in> vD(rt (\<sigma> i))\<close> have "dip \<in> vD(rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))" by simp
          with a1 a2 a4 have "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip)))" by simp
          with \<open>(the (nhop (rt (\<sigma> i)) dip)) = i\<close> have "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> i)" by simp
          hence False by simp
          thus ?thesis ..
        next
          assume "(the (nhop (rt (\<sigma> i)) dip)) \<noteq> i"
          with \<open>\<forall>j. j \<noteq> i \<longrightarrow> \<sigma> j = \<sigma>' j\<close>
            have *: "\<sigma> (the (nhop (rt (\<sigma> i)) dip)) = \<sigma>' (the (nhop (rt (\<sigma> i)) dip))" by simp
          with \<open>dip\<in>vD (rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip))))\<close>
            have "dip\<in>vD (rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))" by simp
          with a1 a2 a4 have "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip)))" by simp
          with * show ?thesis by simp
        qed
      qed
    } note basic = this

    { fix \<sigma> \<sigma>' a dip sip i
      assume a1: "\<forall>dip. dip\<in>vD(rt (\<sigma> i))
                      \<and> dip\<in>vD(rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))
                      \<and> the (nhop (rt (\<sigma> i)) dip) \<noteq> dip
                      \<longrightarrow> rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip)))"
         and ow: "?S i \<sigma> \<sigma>' a"
      have "\<forall>dip. dip\<in>vD(update (rt (\<sigma> i)) sip (0, unk, val, Suc 0, sip))
           \<and> dip\<in>vD(rt (\<sigma>' (the (nhop (update (rt (\<sigma> i)) sip (0, unk, val, Suc 0, sip)) dip))))
           \<and> the (nhop (update (rt (\<sigma> i)) sip (0, unk, val, Suc 0, sip)) dip) \<noteq> dip
           \<longrightarrow> update (rt (\<sigma> i)) sip (0, unk, val, Suc 0, sip)
               \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma>' (the (nhop (update (rt (\<sigma> i)) sip (0, unk, val, Suc 0, sip)) dip)))"
      proof clarify
        fix dip
        assume a2: "dip\<in>vD (update (rt (\<sigma> i)) sip (0, unk, val, Suc 0, sip))"
           and a3: "dip\<in>vD(rt (\<sigma>' (the (nhop
                         (update (rt (\<sigma> i)) sip (0, unk, val, Suc 0, sip)) dip))))"
           and a4: "the (nhop (update (rt (\<sigma> i)) sip (0, unk, val, Suc 0, sip)) dip) \<noteq> dip"
        show "update (rt (\<sigma> i)) sip (0, unk, val, Suc 0, sip)
              \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma>' (the (nhop (update (rt (\<sigma> i)) sip (0, unk, val, Suc 0, sip)) dip)))"
        proof (cases "dip = sip")
          assume "dip = sip"
          with \<open>the (nhop (update (rt (\<sigma> i)) sip (0, unk, val, Suc 0, sip)) dip) \<noteq> dip\<close>
          have False by simp
          thus ?thesis ..
        next
          assume [simp]: "dip \<noteq> sip"
          from a2 have "dip\<in>vD(rt (\<sigma> i)) \<or> dip = sip"
            by (rule vD_update_val)
          with \<open>dip \<noteq> sip\<close> have "dip\<in>vD(rt (\<sigma> i))" by simp
          moreover from a3 have "dip\<in>vD(rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip))))" by simp
          moreover from a4 have "the (nhop (rt (\<sigma> i)) dip) \<noteq> dip" by simp
          ultimately have "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip)))"
            using a1 ow by - (drule(1) basic, simp)
          with \<open>dip \<noteq> sip\<close> show ?thesis
            by - (erule rt_strictly_fresher_update_other, simp)
        qed
      qed
    } note update_0_unk = this

    { fix \<sigma> a \<sigma>' nhop
      assume pre: "\<forall>dip. dip\<in>vD(rt (\<sigma> i)) \<and> dip\<in>vD(rt (\<sigma> (nhop dip))) \<and> nhop dip \<noteq> dip
                         \<longrightarrow> rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> (nhop dip))"
         and ow: "?S i \<sigma> \<sigma>' a"
      have "\<forall>dip. dip \<in> vD (invalidate (rt (\<sigma> i)) (dests (\<sigma> i)))
                  \<and> dip \<in> vD (rt (\<sigma>' (nhop dip))) \<and> nhop dip \<noteq> dip
                  \<longrightarrow> rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma>' (nhop dip))"
      proof clarify
        fix dip
        assume "dip\<in>vD(invalidate (rt (\<sigma> i)) (dests (\<sigma> i)))"
           and "dip\<in>vD(rt (\<sigma>' (nhop dip)))"
           and "nhop dip \<noteq> dip"
        from this(1) have "dip\<in>vD (rt (\<sigma> i))"
          by (clarsimp dest!: vD_invalidate_vD_not_dests)
        moreover from ow have "\<forall>j. j \<noteq> i \<longrightarrow> \<sigma> j = \<sigma>' j" by auto
        ultimately have "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> (nhop dip))"
          using pre \<open>dip \<in> vD (rt (\<sigma>' (nhop dip)))\<close> \<open>nhop dip \<noteq> dip\<close>
          by metis
        with \<open>\<forall>j. j \<noteq> i \<longrightarrow> \<sigma> j = \<sigma>' j\<close> show  "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma>' (nhop dip))"
          by (metis rt_strictly_fresher_irefl)
      qed
    } note invalidate = this

    { fix \<sigma> a \<sigma>' dip oip osn sip hops i
      assume pre: "\<forall>dip. dip \<in> vD (rt (\<sigma> i))
                       \<and> dip \<in> vD (rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))
                       \<and> the (nhop (rt (\<sigma> i)) dip) \<noteq> dip
                   \<longrightarrow> rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip)))"
         and ow: "?S i \<sigma> \<sigma>' a"
         and "Suc 0 \<le> osn"
         and a6: "sip \<noteq> oip \<longrightarrow> oip \<in> kD (rt (\<sigma> sip))
                                 \<and> osn \<le> nsqn (rt (\<sigma> sip)) oip
                                 \<and> (nsqn (rt (\<sigma> sip)) oip = osn
                                    \<longrightarrow> the (dhops (rt (\<sigma> sip)) oip) \<le> hops
                                         \<or> the (flag (rt (\<sigma> sip)) oip) = inv)"
         and after: "\<sigma>' i = \<sigma> i\<lparr>rt := update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)\<rparr>"
      have "\<forall>dip. dip \<in> vD (update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip))
                \<and> dip \<in> vD (rt (\<sigma>' (the (nhop (update (rt (\<sigma> i)) oip
                                      (osn, kno, val, Suc hops, sip)) dip))))
                \<and> the (nhop (update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)) dip) \<noteq> dip
             \<longrightarrow> update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)
                 \<sqsubset>\<^bsub>dip\<^esub>
                 rt (\<sigma>' (the (nhop (update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)) dip)))"
      proof clarify
        fix dip
        assume a2: "dip\<in>vD(update (rt (\<sigma> i)) oip (osn, kno, val, Suc (hops), sip))"
           and a3: "dip\<in>vD(rt (\<sigma>' (the (nhop (update (rt (\<sigma> i)) oip
                                                        (osn, kno, val, Suc hops, sip)) dip))))"
           and a4: "the (nhop (update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)) dip) \<noteq> dip"
        from ow have a5: "\<forall>j. j \<noteq> i \<longrightarrow> \<sigma> j = \<sigma>' j" by auto
        show "update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)
              \<sqsubset>\<^bsub>dip\<^esub>
              rt (\<sigma>' (the (nhop (update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip)) dip)))"
          (is "?rt1 \<sqsubset>\<^bsub>dip\<^esub> ?rt2 dip")
        proof (cases "?rt1 = rt (\<sigma> i)")
          assume nochange [simp]:
            "update (rt (\<sigma> i)) oip (osn, kno, val, Suc hops, sip) = rt (\<sigma> i)"

          from after have "\<sigma>' i = \<sigma> i" by simp
          with a5 have "\<forall>j. \<sigma> j = \<sigma>' j" by metis

          from a2 have "dip\<in>vD (rt (\<sigma> i))" by simp
          moreover from a3 have "dip\<in>vD(rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))"
            using nochange and \<open>\<forall>j. \<sigma> j = \<sigma>' j\<close> by clarsimp
          moreover from a4 have "the (nhop (rt (\<sigma> i)) dip) \<noteq> dip" by simp
          ultimately have "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip)))"
            using pre by simp

          hence "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma>' (the (nhop (rt (\<sigma> i)) dip)))"
            using \<open>\<forall>j. \<sigma> j = \<sigma>' j\<close> by simp
          thus "?thesis" by simp
        next
          assume change: "?rt1 \<noteq> rt (\<sigma> i)"
          from after a2 have "dip\<in>kD(rt (\<sigma>' i))" by auto
          show ?thesis
          proof (cases "dip = oip")
            assume "dip \<noteq> oip"

            with a2 have "dip\<in>vD (rt (\<sigma> i))" by auto
            moreover with a3 a5 after and \<open>dip \<noteq> oip\<close>
              have "dip\<in>vD(rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))"
                by simp metis
            moreover from a4 and \<open>dip \<noteq> oip\<close> have "the (nhop (rt (\<sigma> i)) dip) \<noteq> dip" by simp
            ultimately have "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip)))"
              using pre by simp

            with after and a5 and \<open>dip \<noteq> oip\<close> show ?thesis
              by simp (metis rt_strictly_fresher_update_other
                             rt_strictly_fresher_irefl)
          next
            assume "dip = oip"

            with a4 and change have "sip \<noteq> oip" by simp
            with a6 have "oip\<in>kD(rt (\<sigma> sip))"
                     and "osn \<le> nsqn (rt (\<sigma> sip)) oip" by auto

            from a3 change \<open>dip = oip\<close> have "oip\<in>vD(rt (\<sigma>' sip))" by simp
            hence "the (flag (rt (\<sigma>' sip)) oip) = val" by simp

            from \<open>oip\<in>kD(rt (\<sigma> sip))\<close>
            have "osn < nsqn (rt (\<sigma>' sip)) oip \<or> (osn = nsqn (rt (\<sigma>' sip)) oip
                                                   \<and> the (dhops (rt (\<sigma>' sip)) oip) \<le> hops)"
            proof
              assume "oip\<in>vD(rt (\<sigma> sip))"
              hence "the (flag (rt (\<sigma> sip)) oip) = val" by simp
              with a6 \<open>sip \<noteq> oip\<close> have "nsqn (rt (\<sigma> sip)) oip = osn \<longrightarrow>
                                          the (dhops (rt (\<sigma> sip)) oip) \<le> hops"
                by simp
              show ?thesis
              proof (cases "sip = i")
                assume "sip \<noteq> i"
                with a5 have "\<sigma> sip = \<sigma>' sip" by simp
                with \<open>osn \<le> nsqn (rt (\<sigma> sip)) oip\<close>
                 and \<open>nsqn (rt (\<sigma> sip)) oip = osn \<longrightarrow> the (dhops (rt (\<sigma> sip)) oip) \<le> hops\<close>
                show ?thesis by auto
              next
                \<comment> \<open>alternative to using @{text sip_not_ip}\<close>
                assume [simp]: "sip = i"
                have "?rt1 = rt (\<sigma> i)"
                proof (rule update_cases_kD, simp_all)
                  from \<open>Suc 0 \<le> osn\<close> show "0 < osn" by simp
                next
                  from \<open>oip\<in>kD(rt (\<sigma> sip))\<close> and \<open>sip = i\<close> show "oip\<in>kD(rt (\<sigma> i))"
                    by simp
                next
                  assume "sqn (rt (\<sigma> i)) oip < osn"
                  also from \<open>osn \<le> nsqn (rt (\<sigma> sip)) oip\<close>
                    have "... \<le> nsqn (rt (\<sigma> i)) oip" by simp
                  also have "... \<le> sqn (rt (\<sigma> i)) oip"
                    by (rule nsqn_sqn)
                  finally have "sqn (rt (\<sigma> i)) oip < sqn (rt (\<sigma> i)) oip" .
                  hence False by simp
                  thus "(\<lambda>a. if a = oip
                             then Some (osn, kno, val, Suc hops, i)
                             else rt (\<sigma> i) a) = rt (\<sigma> i)" ..
                next
                  assume "sqn (rt (\<sigma> i)) oip = osn"
                     and "Suc hops < the (dhops (rt (\<sigma> i)) oip)"
                  from this(1) and \<open>oip \<in> vD (rt (\<sigma> sip))\<close> have "nsqn (rt (\<sigma> i)) oip = osn"
                    by simp
                  with \<open>nsqn (rt (\<sigma> sip)) oip = osn \<longrightarrow> the (dhops (rt (\<sigma> sip)) oip) \<le> hops\<close>
                    have "the (dhops (rt (\<sigma> i)) oip) \<le> hops" by simp
                  with \<open>Suc hops < the (dhops (rt (\<sigma> i)) oip)\<close> have False by simp
                  thus "(\<lambda>a. if a = oip
                             then Some (osn, kno, val, Suc hops, i)
                             else rt (\<sigma> i) a) = rt (\<sigma> i)" ..
                next
                  assume "the (flag (rt (\<sigma> i)) oip) = inv"
                  with \<open>the (flag (rt (\<sigma> sip)) oip) = val\<close> have False by simp
                  thus "(\<lambda>a. if a = oip
                             then Some (osn, kno, val, Suc hops, i)
                             else rt (\<sigma> i) a) = rt (\<sigma> i)" ..
                next
                  from \<open>oip\<in>kD(rt (\<sigma> sip))\<close>
                    show "(\<lambda>a. if a = oip then Some (the (rt (\<sigma> i) oip)) else rt (\<sigma> i) a) = rt (\<sigma> i)"
                      by (auto dest!: kD_Some)
                qed
                with change have False ..
                thus ?thesis ..
              qed
            next
              assume "oip\<in>iD(rt (\<sigma> sip))"
              with \<open>the (flag (rt (\<sigma>' sip)) oip) = val\<close> and a5 have "sip = i"
                by (metis f.distinct(1) iD_flag_is_inv)
              from \<open>oip\<in>iD(rt (\<sigma> sip))\<close> have "the (flag (rt (\<sigma> sip)) oip) = inv" by auto
              with \<open>sip = i\<close> \<open>Suc 0 \<le> osn\<close> change after \<open>oip\<in>kD(rt (\<sigma> sip))\<close>
                have "nsqn (rt (\<sigma> sip)) oip < nsqn (rt (\<sigma>' sip)) oip"
                  unfolding update_def
                  by (clarsimp split: option.split_asm if_split_asm)
                     (auto simp: sqn_def)
              with \<open>osn \<le> nsqn (rt (\<sigma> sip)) oip\<close> have "osn < nsqn (rt (\<sigma>' sip)) oip"
                by simp
              thus ?thesis ..
            qed
            thus ?thesis
            proof
              assume osnlt: "osn < nsqn (rt (\<sigma>' sip)) oip"
              from \<open>dip\<in>kD(rt (\<sigma>' i))\<close> and \<open>dip = oip\<close> have "dip \<in> kD (?rt1)" by simp
              moreover from a3 have "dip \<in> kD(?rt2 dip)" by simp
              moreover have "nsqn ?rt1 dip < nsqn (?rt2 dip) dip"
                proof -
                  have "nsqn ?rt1 oip = osn"
                    by (simp add: \<open>dip = oip\<close> nsqn_update_changed_kno_val [OF change [THEN not_sym]])
                  also have "... < nsqn (rt (\<sigma>' sip)) oip" using osnlt .
                  also have  "... = nsqn (?rt2 oip) oip" by (simp add: change)
                  finally show ?thesis
                    using \<open>dip = oip\<close> by simp
                qed
              ultimately show ?thesis
                by (rule rt_strictly_fresher_ltI)
            next
              assume osneq: "osn = nsqn (rt (\<sigma>' sip)) oip \<and> the (dhops (rt (\<sigma>' sip)) oip) \<le> hops"

              have "oip\<in>kD(?rt1)" by simp
              moreover from a3 \<open>dip = oip\<close> have "oip\<in>kD(?rt2 oip)" by simp

              moreover have "nsqn ?rt1 oip = nsqn (?rt2 oip) oip"
              proof -
                from osneq have "osn = nsqn (rt (\<sigma>' sip)) oip" ..
                also have "osn = nsqn ?rt1 oip"
                  by (simp add: \<open>dip = oip\<close> nsqn_update_changed_kno_val [OF change [THEN not_sym]])
                also have  "nsqn (rt (\<sigma>' sip)) oip = nsqn (?rt2 oip) oip"
                  by (simp add: change)
                finally show ?thesis .
              qed

              moreover have "\<pi>\<^sub>5(the (?rt2 oip oip)) < \<pi>\<^sub>5(the (?rt1 oip))"
              proof -
                from osneq have "the (dhops (rt (\<sigma>' sip)) oip) \<le> hops" ..
                moreover from \<open>oip \<in> vD (rt (\<sigma>' sip))\<close> have "oip\<in>kD(rt (\<sigma>' sip))" by auto
                ultimately have "\<pi>\<^sub>5(the (rt (\<sigma>' sip) oip)) \<le> hops"
                  by (auto simp add: proj5_eq_dhops)
                also from change after have "hops < \<pi>\<^sub>5(the (rt (\<sigma>' i) oip))"
                  by (simp add: proj5_eq_dhops) (metis dhops_update_changed lessI)
                finally have "\<pi>\<^sub>5(the (rt (\<sigma>' sip) oip)) < \<pi>\<^sub>5(the (rt (\<sigma>' i) oip))" .
                with change after show ?thesis by simp
              qed

              ultimately have "?rt1 \<sqsubset>\<^bsub>oip\<^esub> ?rt2 oip"
                by (rule rt_strictly_fresher_eqI)
              with \<open>dip = oip\<close> show ?thesis by simp
                qed
          qed
       qed
     qed
    } note rreq_rrep_update = this

    have "opaodv i \<Turnstile> (otherwith ((=)) {i} (orecvmsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m
                                                            \<and> msg_zhops m)),
                       other quality_increases {i} \<rightarrow>)
            onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V
           (\<lambda>(\<sigma>, _). \<forall>dip. dip \<in> vD (rt (\<sigma> i)) \<inter> vD (rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))
                           \<and> the (nhop (rt (\<sigma> i)) dip) \<noteq> dip
                           \<longrightarrow> rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))"
      proof (inv_cterms inv add: onl_oinvariant_sterms [OF aodv_wf rreq_sip [THEN weaken]]
                                 onl_oinvariant_sterms [OF aodv_wf rrep_sip [THEN weaken]]
                                 onl_oinvariant_sterms [OF aodv_wf rerr_sip [THEN weaken]]
                                 onl_oinvariant_sterms [OF aodv_wf oosn_rreq [THEN weaken]]
                                 onl_oinvariant_sterms [OF aodv_wf odsn_rrep [THEN weaken]]
                        solve: basic update_0_unk invalidate rreq_rrep_update
                        simp add: seqlsimp)
        fix \<sigma> \<sigma>' p l
        assume or: "(\<sigma>, p) \<in> oreachable (opaodv i) (?S i)  (other quality_increases {i})"
           and "other quality_increases {i} \<sigma> \<sigma>'"
           and ll: "l \<in> labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p"
           and pre: "\<forall>dip. dip\<in>vD (rt (\<sigma> i))
                           \<and> dip\<in>vD(rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip))))
                           \<and> the (nhop (rt (\<sigma> i)) dip) \<noteq> dip
                        \<longrightarrow> rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> (the (nhop (rt (\<sigma> i)) dip)))"
        from this(1-2)
          have or': "(\<sigma>', p) \<in> oreachable (opaodv i) (?S i)  (other quality_increases {i})"
            by - (rule oreachable_other')

        from or and ll have next_hop: "\<forall>dip. let nhip = the (nhop (rt (\<sigma> i)) dip)
                                             in dip \<in> kD(rt (\<sigma> i)) \<and> nhip \<noteq> dip
                                             \<longrightarrow> dip \<in> kD(rt (\<sigma> nhip))
                                                 \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma> nhip)) dip"
          by (auto dest!: onl_oinvariant_weakenD [OF seq_compare_next_hop'])

        from or and ll have unk_hops_one: "\<forall>dip\<in>kD (rt (\<sigma> i)). sqn (rt (\<sigma> i)) dip = 0
                                                \<longrightarrow> sqnf (rt (\<sigma> i)) dip = unk
                                                    \<and> the (dhops (rt (\<sigma> i)) dip) = 1
                                                    \<and> the (nhop (rt (\<sigma> i)) dip) = dip"
          by (auto dest!: onl_oinvariant_weakenD [OF ozero_seq_unk_hops_one
                                                     [OF oaodv_trans aodv_trans]]
                          otherwith_actionD
                          simp: seqlsimp)

        from \<open>other quality_increases {i} \<sigma> \<sigma>'\<close> have "\<sigma>' i = \<sigma> i" by auto
        hence "quality_increases (\<sigma> i) (\<sigma>' i)" by auto
        with \<open>other quality_increases {i} \<sigma> \<sigma>'\<close> have "\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)"
          by - (erule otherE, metis singleton_iff)

        show "\<forall>dip. dip \<in> vD (rt (\<sigma>' i))
                  \<and> dip \<in> vD (rt (\<sigma>' (the (nhop (rt (\<sigma>' i)) dip))))
                  \<and> the (nhop (rt (\<sigma>' i)) dip) \<noteq> dip
              \<longrightarrow> rt (\<sigma>' i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma>' (the (nhop (rt (\<sigma>' i)) dip)))"
        proof clarify
          fix dip
          assume "dip\<in>vD(rt (\<sigma>' i))"
             and "dip\<in>vD(rt (\<sigma>' (the (nhop (rt (\<sigma>' i)) dip))))"
             and "the (nhop (rt (\<sigma>' i)) dip) \<noteq> dip"
          from this(1) and \<open>\<sigma>' i = \<sigma> i\<close> have "dip\<in>vD(rt (\<sigma> i))"
                                         and "dip\<in>kD(rt (\<sigma> i))"
            by auto

          from \<open>the (nhop (rt (\<sigma>' i)) dip) \<noteq> dip\<close> and \<open>\<sigma>' i = \<sigma> i\<close>
            have "the (nhop (rt (\<sigma> i)) dip) \<noteq> dip" (is "?nhip \<noteq> _") by simp
          with \<open>dip\<in>kD(rt (\<sigma> i))\<close> and next_hop
            have "dip\<in>kD(rt (\<sigma> (?nhip)))"
             and nsqns: "nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma> ?nhip)) dip"
               by (auto simp: Let_def)

          have "0 < sqn (rt (\<sigma> i)) dip"
            proof (rule neq0_conv [THEN iffD1, OF notI])
              assume "sqn (rt (\<sigma> i)) dip = 0"
              with \<open>dip\<in>kD(rt (\<sigma> i))\<close> and unk_hops_one
                have "?nhip = dip" by simp
              with \<open>?nhip \<noteq> dip\<close> show False ..
            qed
          also have "... = nsqn (rt (\<sigma> i)) dip"
            by (rule vD_nsqn_sqn [OF \<open>dip\<in>vD(rt (\<sigma> i))\<close>, THEN sym])
          also have "... \<le> nsqn (rt (\<sigma> ?nhip)) dip"
            by (rule nsqns)
          also have "... \<le> sqn (rt (\<sigma> ?nhip)) dip"
            by (rule nsqn_sqn)
          finally have "0 < sqn (rt (\<sigma> ?nhip)) dip" .

          have "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma>' ?nhip)"
          proof (cases "dip\<in>vD(rt (\<sigma> ?nhip))")
            assume "dip\<in>vD(rt (\<sigma> ?nhip))"
            with pre \<open>dip\<in>vD(rt (\<sigma> i))\<close> and \<open>?nhip \<noteq> dip\<close>
              have "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> ?nhip)" by auto
            moreover from \<open>\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)\<close>
              have "quality_increases (\<sigma> ?nhip) (\<sigma>' ?nhip)" ..
            ultimately show ?thesis
              using \<open>dip\<in>kD(rt (\<sigma> ?nhip))\<close>
              by (rule strictly_fresher_quality_increases_right)
          next
            assume "dip\<notin>vD(rt (\<sigma> ?nhip))"
            with \<open>dip\<in>kD(rt (\<sigma> ?nhip))\<close> have "dip\<in>iD(rt (\<sigma> ?nhip))" ..
            hence "the (flag (rt (\<sigma> ?nhip)) dip) = inv"
              by auto
            have "nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma> ?nhip)) dip"
              by (rule nsqns)
            also from \<open>dip\<in>iD(rt (\<sigma> ?nhip))\<close>
              have "... = sqn (rt (\<sigma> ?nhip)) dip - 1" ..
            also have "... < sqn (rt (\<sigma>' ?nhip)) dip"
              proof -
                from \<open>\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)\<close>
                  have "quality_increases (\<sigma> ?nhip) (\<sigma>' ?nhip)" ..
                hence "\<forall>ip. sqn (rt (\<sigma> ?nhip)) ip \<le> sqn (rt (\<sigma>' ?nhip)) ip" by auto
                hence "sqn (rt (\<sigma> ?nhip)) dip \<le> sqn (rt (\<sigma>' ?nhip)) dip" ..
                with \<open>0 < sqn (rt (\<sigma> ?nhip)) dip\<close> show ?thesis by auto
              qed
            also have "... = nsqn (rt (\<sigma>' ?nhip)) dip"
              proof (rule vD_nsqn_sqn [THEN sym])
                from \<open>dip\<in>vD(rt (\<sigma>' (the (nhop (rt (\<sigma>' i)) dip))))\<close> and \<open>\<sigma>' i = \<sigma> i\<close>
                  show "dip\<in>vD(rt (\<sigma>' ?nhip))" by simp
              qed
            finally have "nsqn (rt (\<sigma> i)) dip < nsqn (rt (\<sigma>' ?nhip)) dip" .

            moreover from \<open>dip\<in>vD(rt (\<sigma>' (the (nhop (rt (\<sigma>' i)) dip))))\<close> and \<open>\<sigma>' i = \<sigma> i\<close>
              have "dip\<in>kD(rt (\<sigma>' ?nhip))" by auto
            ultimately show "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma>' ?nhip)"
              using \<open>dip\<in>kD(rt (\<sigma> i))\<close> by - (rule rt_strictly_fresher_ltI)
          qed
          with \<open>\<sigma>' i = \<sigma> i\<close> show "rt (\<sigma>' i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma>' (the (nhop (rt (\<sigma>' i)) dip)))"
            by simp
        qed
      qed
    thus ?thesis unfolding Let_def .
  qed

lemma seq_compare_next_hop:
  fixes w
  shows "opaodv i \<Turnstile> (otherwith ((=)) {i} (orecvmsg msg_fresh),
                      other quality_increases {i} \<rightarrow>)
                       global (\<lambda>\<sigma>. \<forall>dip. let nhip = the (nhop (rt (\<sigma> i)) dip)
                                         in dip \<in> kD(rt (\<sigma> i)) \<and> nhip \<noteq> dip \<longrightarrow>
                                            dip \<in> kD(rt (\<sigma> nhip))
                                            \<and> nsqn (rt (\<sigma> i)) dip \<le> nsqn (rt (\<sigma> nhip)) dip)"
  by (rule oinvariant_weakenE [OF seq_compare_next_hop']) (auto dest!: onlD)

lemma seq_nhop_quality_increases:
  shows "opaodv i \<Turnstile> (otherwith ((=)) {i}
                        (orecvmsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m \<and> msg_zhops m)),
                         other quality_increases {i} \<rightarrow>)
                        global (\<lambda>\<sigma>. \<forall>dip. let nhip = the (nhop (rt (\<sigma> i)) dip)
                                          in dip \<in> vD (rt (\<sigma> i)) \<inter> vD (rt (\<sigma> nhip)) \<and> nhip \<noteq> dip
                                             \<longrightarrow> (rt (\<sigma> i)) \<sqsubset>\<^bsub>dip\<^esub> (rt (\<sigma> nhip)))"
  by (rule oinvariant_weakenE [OF seq_nhop_quality_increases']) (auto dest!: onlD)

end
