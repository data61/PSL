(*  Title:       variants/a_norreqid/Quality_Increases.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
    Author:      Peter Höfner, NICTA
*)

section "The quality increases predicate"

theory A_Quality_Increases
imports A_Aodv_Predicates A_Fresher
begin

definition quality_increases :: "state \<Rightarrow> state \<Rightarrow> bool"
where "quality_increases \<xi> \<xi>' \<equiv> (\<forall>dip\<in>kD(rt \<xi>). dip \<in> kD(rt \<xi>') \<and> rt \<xi> \<sqsubseteq>\<^bsub>dip\<^esub> rt \<xi>')
                                               \<and> (\<forall>dip. sqn (rt \<xi>) dip \<le> sqn (rt \<xi>') dip)"

lemma quality_increasesI [intro!]:
  assumes "\<And>dip. dip \<in> kD(rt \<xi>) \<Longrightarrow> dip \<in> kD(rt \<xi>')"
      and "\<And>dip. \<lbrakk> dip \<in> kD(rt \<xi>); dip \<in> kD(rt \<xi>') \<rbrakk> \<Longrightarrow> rt \<xi> \<sqsubseteq>\<^bsub>dip\<^esub> rt \<xi>'"          
      and "\<And>dip. sqn (rt \<xi>) dip \<le> sqn (rt \<xi>') dip"
    shows "quality_increases \<xi> \<xi>'"
  unfolding quality_increases_def using assms by clarsimp

lemma quality_increasesE [elim]:
    fixes dip
  assumes "quality_increases \<xi> \<xi>'"
      and "dip\<in>kD(rt \<xi>)"
      and "\<lbrakk> dip \<in> kD(rt \<xi>'); rt \<xi> \<sqsubseteq>\<^bsub>dip\<^esub> rt \<xi>'; sqn (rt \<xi>) dip \<le> sqn (rt \<xi>') dip \<rbrakk> \<Longrightarrow> R dip \<xi> \<xi>'"
    shows "R dip \<xi> \<xi>'"
  using assms unfolding quality_increases_def by clarsimp

lemma quality_increases_rt_fresherD [dest]:
    fixes ip
  assumes "quality_increases \<xi> \<xi>'"
      and "ip\<in>kD(rt \<xi>)"
    shows "rt \<xi> \<sqsubseteq>\<^bsub>ip\<^esub> rt \<xi>'"
  using assms by auto

lemma quality_increases_sqnE [elim]:
    fixes dip
  assumes "quality_increases \<xi> \<xi>'"
      and "sqn (rt \<xi>) dip \<le> sqn (rt \<xi>') dip \<Longrightarrow> R dip \<xi> \<xi>'"
    shows "R dip \<xi> \<xi>'"
  using assms unfolding quality_increases_def by clarsimp

lemma quality_increases_refl [intro, simp]: "quality_increases \<xi> \<xi>"
  by rule simp_all

lemma strictly_fresher_quality_increases_right [elim]:
    fixes \<sigma> \<sigma>' dip
  assumes "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> nhip)"                       
      and qinc: "quality_increases (\<sigma> nhip) (\<sigma>' nhip)"
      and "dip\<in>kD(rt (\<sigma> nhip))"
    shows "rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma>' nhip)"
  proof -
    from qinc have "rt (\<sigma> nhip) \<sqsubseteq>\<^bsub>dip\<^esub> rt (\<sigma>' nhip)" using \<open>dip\<in>kD(rt (\<sigma> nhip))\<close>
      by auto
    with \<open>rt (\<sigma> i) \<sqsubset>\<^bsub>dip\<^esub> rt (\<sigma> nhip)\<close> show ?thesis ..
  qed

lemma kD_quality_increases [elim]:
  assumes "i\<in>kD(rt \<xi>)"
      and "quality_increases \<xi> \<xi>'"
    shows "i\<in>kD(rt \<xi>')"
  using assms by auto

lemma kD_nsqn_quality_increases [elim]:
  assumes "i\<in>kD(rt \<xi>)"
      and "quality_increases \<xi> \<xi>'"
    shows "i\<in>kD(rt \<xi>') \<and> nsqn (rt \<xi>) i \<le> nsqn (rt \<xi>') i"
  proof -
    from assms have "i\<in>kD(rt \<xi>')" ..
    moreover with assms have "rt \<xi> \<sqsubseteq>\<^bsub>i\<^esub> rt \<xi>'" by auto
    ultimately have "nsqn (rt \<xi>) i \<le> nsqn (rt \<xi>') i"
      using \<open>i\<in>kD(rt \<xi>)\<close> by - (erule(2) rt_fresher_imp_nsqn_le)
    with \<open>i\<in>kD(rt \<xi>')\<close> show ?thesis ..
  qed

lemma nsqn_quality_increases [elim]:
  assumes "i\<in>kD(rt \<xi>)"
      and "quality_increases \<xi> \<xi>'"
    shows "nsqn (rt \<xi>) i \<le> nsqn (rt \<xi>') i"
  using assms by (rule kD_nsqn_quality_increases [THEN conjunct2])

lemma kD_nsqn_quality_increases_trans [elim]:
  assumes "i\<in>kD(rt \<xi>)"
      and "s \<le> nsqn (rt \<xi>) i"
      and "quality_increases \<xi> \<xi>'"
    shows "i\<in>kD(rt \<xi>') \<and> s \<le> nsqn (rt \<xi>') i"
  proof
    from \<open>i\<in>kD(rt \<xi>)\<close> and \<open>quality_increases \<xi> \<xi>'\<close> show "i\<in>kD(rt \<xi>')" ..
  next
    from \<open>i\<in>kD(rt \<xi>)\<close> and \<open>quality_increases \<xi> \<xi>'\<close> have "nsqn (rt \<xi>) i \<le> nsqn (rt \<xi>') i" ..
    with \<open>s \<le> nsqn (rt \<xi>) i\<close> show "s \<le> nsqn (rt \<xi>') i" by (rule le_trans)
  qed

lemma nsqn_quality_increases_nsqn_lt_lt [elim]:
  assumes "i\<in>kD(rt \<xi>)"
      and "quality_increases \<xi> \<xi>'"
     and "s < nsqn (rt \<xi>) i"
    shows "s < nsqn (rt \<xi>') i"
  proof -
    from assms(1-2) have "nsqn (rt \<xi>) i \<le> nsqn (rt \<xi>') i" ..
    with \<open>s < nsqn (rt \<xi>) i\<close> show "s < nsqn (rt \<xi>') i" by simp
  qed

lemma nsqn_quality_increases_dhops [elim]:
  assumes "i\<in>kD(rt \<xi>)"
      and "quality_increases \<xi> \<xi>'"
      and "nsqn (rt \<xi>) i = nsqn (rt \<xi>') i"
    shows "the (dhops (rt \<xi>) i) \<ge> the (dhops (rt \<xi>') i)"
  using assms unfolding quality_increases_def
  by (clarsimp) (drule(1) bspec, clarsimp simp: rt_fresher_def2)

lemma nsqn_quality_increases_nsqn_eq_le [elim]:
  assumes "i\<in>kD(rt \<xi>)"
      and "quality_increases \<xi> \<xi>'"
      and "s = nsqn (rt \<xi>) i"
    shows "s < nsqn (rt \<xi>') i \<or> (s = nsqn (rt \<xi>') i \<and> the (dhops (rt \<xi>) i) \<ge> the (dhops (rt \<xi>') i))"
  using assms by (metis nat_less_le nsqn_quality_increases nsqn_quality_increases_dhops)

lemma quality_increases_rreq_rrep_props [elim]:
    fixes sn ip hops sip
  assumes qinc: "quality_increases (\<sigma> sip) (\<sigma>' sip)"
      and "1 \<le> sn"
      and *: "ip\<in>kD(rt (\<sigma> sip)) \<and> sn \<le> nsqn (rt (\<sigma> sip)) ip
                                \<and> (nsqn (rt (\<sigma> sip)) ip = sn
                                    \<longrightarrow> (the (dhops (rt (\<sigma> sip)) ip) \<le> hops
                                          \<or> the (flag (rt (\<sigma> sip)) ip) = inv))"
    shows "ip\<in>kD(rt (\<sigma>' sip)) \<and> sn \<le> nsqn (rt (\<sigma>' sip)) ip
                              \<and> (nsqn (rt (\<sigma>' sip)) ip = sn
                                  \<longrightarrow> (the (dhops (rt (\<sigma>' sip)) ip) \<le> hops
                                        \<or> the (flag (rt (\<sigma>' sip)) ip) = inv))"
      (is "_ \<and> ?nsqnafter")
  proof -
    from *  obtain "ip\<in>kD(rt (\<sigma> sip))" and "sn \<le> nsqn (rt (\<sigma> sip)) ip" by auto

    from \<open>quality_increases (\<sigma> sip) (\<sigma>' sip)\<close>
       have "sqn (rt (\<sigma> sip)) ip \<le> sqn (rt (\<sigma>' sip)) ip" ..
    from \<open>quality_increases (\<sigma> sip) (\<sigma>' sip)\<close> and \<open>ip\<in>kD (rt (\<sigma> sip))\<close>
      have "ip\<in>kD (rt (\<sigma>' sip))" ..

    from \<open>sn \<le> nsqn (rt (\<sigma> sip)) ip\<close> have ?nsqnafter
    proof
      assume "sn < nsqn (rt (\<sigma> sip)) ip"
      also from \<open>ip\<in>kD(rt (\<sigma> sip))\<close> and \<open>quality_increases (\<sigma> sip) (\<sigma>' sip)\<close>
        have "... \<le> nsqn (rt (\<sigma>' sip)) ip" ..
      finally have "sn < nsqn (rt (\<sigma>' sip)) ip" .
      thus ?thesis by simp
    next
      assume "sn = nsqn (rt (\<sigma> sip)) ip"
      with \<open>ip\<in>kD(rt (\<sigma> sip))\<close> and \<open>quality_increases (\<sigma> sip) (\<sigma>' sip)\<close>
        have "sn < nsqn (rt (\<sigma>' sip)) ip
              \<or> (sn = nsqn (rt (\<sigma>' sip)) ip
                 \<and> the (dhops (rt (\<sigma>' sip)) ip) \<le> the (dhops (rt (\<sigma> sip)) ip))" ..
      hence "sn < nsqn (rt (\<sigma>' sip)) ip
              \<or> (nsqn (rt (\<sigma>' sip)) ip = sn \<and> (the (dhops (rt (\<sigma>' sip)) ip) \<le> hops
                                                 \<or> the (flag (rt (\<sigma>' sip)) ip) = inv))"
      proof
        assume "sn < nsqn (rt (\<sigma>' sip)) ip" thus ?thesis ..
      next
        assume "sn = nsqn (rt (\<sigma>' sip)) ip
                \<and> the (dhops (rt (\<sigma> sip)) ip) \<ge> the (dhops (rt (\<sigma>' sip)) ip)"
        hence "sn = nsqn (rt (\<sigma>' sip)) ip"
          and "the (dhops (rt (\<sigma>' sip)) ip) \<le> the (dhops (rt (\<sigma> sip)) ip)" by auto

        from * and \<open>sn = nsqn (rt (\<sigma> sip)) ip\<close> have "the (dhops (rt (\<sigma> sip)) ip) \<le> hops
                                                       \<or> the (flag (rt (\<sigma> sip)) ip) = inv"
          by simp
        thus ?thesis
        proof
          assume "the (dhops (rt (\<sigma> sip)) ip) \<le> hops"
          with  \<open>the (dhops (rt (\<sigma>' sip)) ip) \<le> the (dhops (rt (\<sigma> sip)) ip)\<close>
           have "the (dhops (rt (\<sigma>' sip)) ip) \<le> hops" by simp
          with \<open>sn = nsqn (rt (\<sigma>' sip)) ip\<close> show ?thesis by simp
        next
          assume "the (flag (rt (\<sigma> sip)) ip) = inv"
          with \<open>ip\<in>kD(rt (\<sigma> sip))\<close> have "nsqn (rt (\<sigma> sip)) ip = sqn (rt (\<sigma> sip)) ip - 1" ..

          with \<open>sn \<ge> 1\<close> and \<open>sn = nsqn (rt (\<sigma> sip)) ip\<close>
            have "sqn (rt (\<sigma> sip)) ip > 1" by simp

          from \<open>ip\<in>kD(rt (\<sigma>' sip))\<close> show ?thesis
          proof (rule vD_or_iD)
            assume "ip\<in>iD(rt (\<sigma>' sip))"
            hence "the (flag (rt (\<sigma>' sip)) ip) = inv" ..
            with \<open>sn = nsqn (rt (\<sigma>' sip)) ip\<close> show ?thesis
              by simp
          next
            (* the tricky case: sn = nsqn (rt (\<sigma>' sip)) ip
                                \<and> ip\<in>iD(rt (\<sigma> sip))
                                \<and> ip\<in>vD(rt (\<sigma>' sip)) *)
            assume "ip\<in>vD(rt (\<sigma>' sip))"
            hence "nsqn (rt (\<sigma>' sip)) ip = sqn (rt (\<sigma>' sip)) ip" ..
            with \<open>sqn (rt (\<sigma> sip)) ip \<le> sqn (rt (\<sigma>' sip)) ip\<close>
              have "nsqn (rt (\<sigma>' sip)) ip \<ge> sqn (rt (\<sigma> sip)) ip" by simp

            with \<open>sqn (rt (\<sigma> sip)) ip > 1\<close>
              have "nsqn (rt (\<sigma>' sip)) ip > sqn (rt (\<sigma> sip)) ip - 1" by simp
            with \<open>nsqn (rt (\<sigma> sip)) ip = sqn (rt (\<sigma> sip)) ip - 1\<close>
              have "nsqn (rt (\<sigma>' sip)) ip > nsqn (rt (\<sigma> sip)) ip" by simp
            with \<open>sn = nsqn (rt (\<sigma> sip)) ip\<close> have "nsqn (rt (\<sigma>' sip)) ip > sn"
              by simp
            thus ?thesis ..
          qed
        qed
      qed
      thus ?thesis by (metis (mono_tags) le_cases not_le)
    qed
    with \<open>ip\<in>kD (rt (\<sigma>' sip))\<close> show "ip\<in>kD (rt (\<sigma>' sip)) \<and> ?nsqnafter" ..
  qed

lemma quality_increases_rreq_rrep_props':
    fixes sn ip hops sip
  assumes "\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)"
      and "1 \<le> sn"
      and *: "ip\<in>kD(rt (\<sigma> sip)) \<and> sn \<le> nsqn (rt (\<sigma> sip)) ip
                                \<and> (nsqn (rt (\<sigma> sip)) ip = sn
                                    \<longrightarrow> (the (dhops (rt (\<sigma> sip)) ip) \<le> hops
                                          \<or> the (flag (rt (\<sigma> sip)) ip) = inv))"
    shows "ip\<in>kD(rt (\<sigma>' sip)) \<and> sn \<le> nsqn (rt (\<sigma>' sip)) ip
                              \<and> (nsqn (rt (\<sigma>' sip)) ip = sn
                                  \<longrightarrow> (the (dhops (rt (\<sigma>' sip)) ip) \<le> hops
                                        \<or> the (flag (rt (\<sigma>' sip)) ip) = inv))"
  proof -
    from assms(1) have "quality_increases (\<sigma> sip) (\<sigma>' sip)" ..
    thus ?thesis using assms(2-3) by (rule quality_increases_rreq_rrep_props)
  qed

lemma rteq_quality_increases:
  assumes "\<forall>j. j \<noteq> i \<longrightarrow> quality_increases (\<sigma> j) (\<sigma>' j)"
      and "rt (\<sigma>' i) = rt (\<sigma> i)"
    shows "\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)"
  using assms by clarsimp (metis order_refl quality_increasesI rt_fresher_refl)

definition msg_fresh :: "(ip \<Rightarrow> state) \<Rightarrow> msg \<Rightarrow> bool"
where "msg_fresh \<sigma> m \<equiv>
         case m of Rreq hopsc  _ _ _ oipc osnc sipc \<Rightarrow> osnc \<ge> 1 \<and> (sipc \<noteq> oipc \<longrightarrow>
                       oipc\<in>kD(rt (\<sigma> sipc)) \<and> nsqn (rt (\<sigma> sipc)) oipc \<ge> osnc
                       \<and> (nsqn (rt (\<sigma> sipc)) oipc = osnc
                             \<longrightarrow> (hopsc \<ge> the (dhops (rt (\<sigma> sipc)) oipc)
                                  \<or> the (flag (rt (\<sigma> sipc)) oipc) = inv)))
                   | Rrep hopsc dipc dsnc _ sipc \<Rightarrow> dsnc \<ge> 1 \<and> (sipc \<noteq> dipc \<longrightarrow>
                       dipc\<in>kD(rt (\<sigma> sipc)) \<and> nsqn (rt (\<sigma> sipc)) dipc \<ge> dsnc
                       \<and> (nsqn (rt (\<sigma> sipc)) dipc = dsnc
                             \<longrightarrow> (hopsc \<ge> the (dhops (rt (\<sigma> sipc)) dipc)
                                   \<or> the (flag (rt (\<sigma> sipc)) dipc) = inv)))
                   | Rerr destsc sipc \<Rightarrow> (\<forall>ripc\<in>dom(destsc). (ripc\<in>kD(rt (\<sigma> sipc))
                                         \<and> the (destsc ripc) - 1 \<le> nsqn (rt (\<sigma> sipc)) ripc))
                   | _ \<Rightarrow> True"

lemma msg_fresh [simp]:
  "\<And>hops dip dsn dsk oip osn sip.
           msg_fresh \<sigma> (Rreq hops dip dsn dsk oip osn sip) =
                            (osn \<ge> 1 \<and> (sip \<noteq> oip \<longrightarrow> oip\<in>kD(rt (\<sigma> sip))
                                     \<and> nsqn (rt (\<sigma> sip)) oip \<ge> osn
                                     \<and> (nsqn (rt (\<sigma> sip)) oip = osn
                                           \<longrightarrow> (hops \<ge> the (dhops (rt (\<sigma> sip)) oip)
                                                \<or> the (flag (rt (\<sigma> sip)) oip) = inv))))"
  "\<And>hops dip dsn oip sip. msg_fresh \<sigma> (Rrep hops dip dsn oip sip) =
                            (dsn \<ge> 1 \<and> (sip \<noteq> dip \<longrightarrow> dip\<in>kD(rt (\<sigma> sip))
                                     \<and> nsqn (rt (\<sigma> sip)) dip \<ge> dsn
                                     \<and> (nsqn (rt (\<sigma> sip)) dip = dsn
                                           \<longrightarrow> (hops \<ge> the (dhops (rt (\<sigma> sip)) dip))
                                                 \<or> the (flag (rt (\<sigma> sip)) dip) = inv)))"
  "\<And>dests sip.            msg_fresh \<sigma> (Rerr dests sip) =
                            (\<forall>ripc\<in>dom(dests). (ripc\<in>kD(rt (\<sigma> sip))
                                     \<and> the (dests ripc) - 1 \<le> nsqn (rt (\<sigma> sip)) ripc))"
  "\<And>d dip.                msg_fresh \<sigma> (Newpkt d dip)   = True"
  "\<And>d dip sip.            msg_fresh \<sigma> (Pkt d dip sip)  = True"
  unfolding msg_fresh_def by simp_all

lemma msg_fresh_inc_sn [simp, elim]:
  "msg_fresh \<sigma> m \<Longrightarrow> rreq_rrep_sn m"
  by (cases m) simp_all

lemma recv_msg_fresh_inc_sn [simp, elim]:
  "orecvmsg (msg_fresh) \<sigma> m \<Longrightarrow> recvmsg rreq_rrep_sn m"
  by (cases m) simp_all

lemma rreq_nsqn_is_fresh [simp]:
  fixes \<sigma> msg hops dip dsn dsk oip osn sip
  assumes "rreq_rrep_fresh (rt (\<sigma> sip)) (Rreq hops dip dsn dsk oip osn sip)"
      and "rreq_rrep_sn (Rreq hops  dip dsn dsk oip osn sip)"
  shows "msg_fresh \<sigma> (Rreq hops  dip dsn dsk oip osn sip)"
        (is "msg_fresh \<sigma> ?msg")
  proof -
    let ?rt = "rt (\<sigma> sip)"
    from assms(2) have "1 \<le> osn" by simp
    thus ?thesis
    unfolding msg_fresh_def
    proof (simp only: msg.case, intro conjI impI)
      assume "sip \<noteq> oip"
      with assms(1) show "oip \<in> kD(?rt)" by simp
    next
      assume "sip \<noteq> oip"
         and "nsqn ?rt oip = osn"
      show "the (dhops ?rt oip) \<le> hops \<or> the (flag ?rt oip) = inv"
      proof (cases "oip\<in>vD(?rt)")
        assume "oip\<in>vD(?rt)"
        hence "nsqn ?rt oip = sqn ?rt oip" ..
        with \<open>nsqn ?rt oip = osn\<close> have "sqn ?rt oip = osn" by simp
        with assms(1) and \<open>sip \<noteq> oip\<close> have "the (dhops ?rt oip) \<le> hops"
          by simp
        thus ?thesis ..
      next
        assume "oip\<notin>vD(?rt)"
        moreover from assms(1) and \<open>sip \<noteq> oip\<close> have "oip\<in>kD(?rt)" by simp
        ultimately have "oip\<in>iD(?rt)" by auto
        hence "the (flag ?rt oip) = inv" ..
        thus ?thesis ..
      qed
    next
      assume "sip \<noteq> oip"
      with assms(1) have "osn \<le> sqn ?rt oip" by auto
      thus "osn \<le> nsqn (rt (\<sigma> sip)) oip"
      proof (rule nat_le_eq_or_lt)
        assume "osn < sqn ?rt oip"
        hence "osn \<le> sqn ?rt oip - 1" by simp
        also have "... \<le> nsqn ?rt oip" by (rule sqn_nsqn)
        finally show "osn \<le> nsqn ?rt oip" .
      next
        assume "osn = sqn ?rt oip"
        with assms(1) and \<open>sip \<noteq> oip\<close> have "oip\<in>kD(?rt)"
                                       and "the (flag ?rt oip) = val"
          by auto
        hence "nsqn ?rt oip = sqn ?rt oip" ..
        with \<open>osn = sqn ?rt oip\<close> have "nsqn ?rt oip = osn" by simp
        thus "osn \<le> nsqn ?rt oip" by simp
      qed
    qed simp
  qed

lemma rrep_nsqn_is_fresh [simp]:
  fixes \<sigma> msg hops dip dsn oip sip
  assumes "rreq_rrep_fresh (rt (\<sigma> sip)) (Rrep hops dip dsn oip sip)"
      and "rreq_rrep_sn (Rrep hops dip dsn oip sip)"
  shows "msg_fresh \<sigma> (Rrep hops dip dsn oip sip)"
        (is "msg_fresh \<sigma> ?msg")
  proof -
    let ?rt = "rt (\<sigma> sip)"
    from assms have "sip \<noteq> dip \<longrightarrow> dip\<in>kD(?rt) \<and> sqn ?rt dip = dsn \<and> the (flag ?rt dip) = val"
      by simp
    hence "sip \<noteq> dip \<longrightarrow> dip\<in>kD(?rt) \<and> nsqn ?rt dip \<ge> dsn"
    by clarsimp
    with assms show "msg_fresh \<sigma> ?msg"
      by clarsimp
  qed

lemma rerr_nsqn_is_fresh [simp]:
  fixes \<sigma> msg dests sip
  assumes "rerr_invalid (rt (\<sigma> sip)) (Rerr dests sip)"
  shows "msg_fresh \<sigma> (Rerr dests sip)"
        (is "msg_fresh \<sigma> ?msg")
  proof -
    let ?rt = "rt (\<sigma> sip)"
    from assms have *: "(\<forall>rip\<in>dom(dests). (rip\<in>iD(rt (\<sigma> sip))
                                     \<and> the (dests rip) = sqn (rt (\<sigma> sip)) rip))"
      by clarsimp
    have "(\<forall>rip\<in>dom(dests). (rip\<in>kD(rt (\<sigma> sip))
                                     \<and> the (dests rip) - 1 \<le> nsqn (rt (\<sigma> sip)) rip))"
    proof
      fix rip
      assume "rip \<in> dom dests"
      with * have "rip\<in>iD(rt (\<sigma> sip))" and "the (dests rip) = sqn (rt (\<sigma> sip)) rip"
        by auto

      from this(2) have "the (dests rip) - 1 = sqn (rt (\<sigma> sip)) rip - 1" by simp
      also have "... \<le> nsqn (rt (\<sigma> sip)) rip" by (rule sqn_nsqn)
      finally have "the (dests rip) - 1 \<le> nsqn (rt (\<sigma> sip)) rip" .

      with \<open>rip\<in>iD(rt (\<sigma> sip))\<close>
        show "rip\<in>kD(rt (\<sigma> sip)) \<and> the (dests rip) - 1 \<le> nsqn (rt (\<sigma> sip)) rip"
          by clarsimp
    qed
    thus "msg_fresh \<sigma> ?msg"
      by simp
  qed

lemma quality_increases_msg_fresh [elim]:
  assumes qinc: "\<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)"
      and "msg_fresh \<sigma> m"
    shows "msg_fresh \<sigma>' m"
  using assms(2)
  proof (cases m)
    fix hops rreqid dip dsn dsk oip osn sip
    assume [simp]: "m = Rreq hops  dip dsn dsk oip osn sip"
       and "msg_fresh \<sigma> m"
    then have "osn \<ge> 1" and "sip = oip \<or> (oip\<in>kD(rt (\<sigma> sip)) \<and> osn \<le> nsqn (rt (\<sigma> sip)) oip
                                           \<and> (nsqn (rt (\<sigma> sip)) oip = osn
                                                 \<longrightarrow> (the (dhops (rt (\<sigma> sip)) oip) \<le> hops
                                                      \<or> the (flag (rt (\<sigma> sip)) oip) = inv)))"
      by auto
    from this(2) show ?thesis
    proof
      assume "sip = oip" with \<open>osn \<ge> 1\<close> show ?thesis by simp
    next
      assume "oip\<in>kD(rt (\<sigma> sip)) \<and> osn \<le> nsqn (rt (\<sigma> sip)) oip
                                  \<and> (nsqn (rt (\<sigma> sip)) oip = osn
                                      \<longrightarrow> (the (dhops (rt (\<sigma> sip)) oip) \<le> hops
                                           \<or> the (flag (rt (\<sigma> sip)) oip) = inv))"
      moreover from qinc have "quality_increases (\<sigma> sip) (\<sigma>' sip)" ..
      ultimately have "oip\<in>kD(rt (\<sigma>' sip)) \<and> osn \<le> nsqn (rt (\<sigma>' sip)) oip
                                           \<and> (nsqn (rt (\<sigma>' sip)) oip = osn
                                              \<longrightarrow> (the (dhops (rt (\<sigma>' sip)) oip) \<le> hops
                                                    \<or> the (flag (rt (\<sigma>' sip)) oip) = inv))"
       using \<open>osn \<ge> 1\<close> by (rule quality_increases_rreq_rrep_props [rotated 2])
      with \<open>osn \<ge> 1\<close> show "msg_fresh \<sigma>' m"
        by (clarsimp)
    qed
  next
    fix hops dip dsn oip sip
    assume [simp]: "m = Rrep hops dip dsn oip sip"
       and "msg_fresh \<sigma> m"
    then have "dsn \<ge> 1" and "sip = dip \<or> (dip\<in>kD(rt (\<sigma> sip)) \<and> dsn \<le> nsqn (rt (\<sigma> sip)) dip
                                           \<and> (nsqn (rt (\<sigma> sip)) dip = dsn
                                                 \<longrightarrow> (the (dhops (rt (\<sigma> sip)) dip) \<le> hops
                                                      \<or> the (flag (rt (\<sigma> sip)) dip) = inv)))"
      by auto
    from this(2) show "?thesis"
    proof
      assume "sip = dip" with \<open>dsn \<ge> 1\<close> show ?thesis by simp
    next
      assume "dip\<in>kD(rt (\<sigma> sip)) \<and> dsn \<le> nsqn (rt (\<sigma> sip)) dip
                                  \<and> (nsqn (rt (\<sigma> sip)) dip = dsn
                                      \<longrightarrow> (the (dhops (rt (\<sigma> sip)) dip) \<le> hops
                                           \<or> the (flag (rt (\<sigma> sip)) dip) = inv))"
      moreover from qinc have "quality_increases (\<sigma> sip) (\<sigma>' sip)" ..
      ultimately have "dip\<in>kD(rt (\<sigma>' sip)) \<and> dsn \<le> nsqn (rt (\<sigma>' sip)) dip
                                           \<and> (nsqn (rt (\<sigma>' sip)) dip = dsn
                                              \<longrightarrow> (the (dhops (rt (\<sigma>' sip)) dip) \<le> hops
                                                    \<or> the (flag (rt (\<sigma>' sip)) dip) = inv))"
        using \<open>dsn \<ge> 1\<close> by (rule quality_increases_rreq_rrep_props [rotated 2])
      with \<open>dsn \<ge> 1\<close> show "msg_fresh \<sigma>' m"
        by clarsimp
    qed
  next
    fix dests sip
    assume [simp]: "m = Rerr dests sip"
       and "msg_fresh \<sigma> m"
    then have *: "\<forall>rip\<in>dom(dests). rip\<in>kD(rt (\<sigma> sip))
                              \<and> the (dests rip) - 1 \<le> nsqn (rt (\<sigma> sip)) rip"
      by simp
    have "\<forall>rip\<in>dom(dests). rip\<in>kD(rt (\<sigma>' sip))
                         \<and> the (dests rip) - 1 \<le> nsqn (rt (\<sigma>' sip)) rip"
      proof
        fix rip
        assume "rip\<in>dom(dests)"
        with * have "rip\<in>kD(rt (\<sigma> sip))" and "the (dests rip) - 1 \<le> nsqn (rt (\<sigma> sip)) rip"
          by - (drule(1) bspec, clarsimp)+
        moreover from qinc have "quality_increases (\<sigma> sip) (\<sigma>' sip)" by simp
        ultimately show "rip\<in>kD(rt (\<sigma>' sip)) \<and> the (dests rip) - 1 \<le> nsqn (rt (\<sigma>' sip)) rip" ..
      qed
    thus ?thesis by simp
  qed simp_all

end
