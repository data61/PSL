(*  Title:       OAWN_Invariants.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Generic open invariants on sequential AWN processes"

theory OAWN_Invariants
imports Invariants OInvariants
        AWN_Cterms AWN_Labels AWN_Invariants
        OAWN_SOS
begin

subsection "Open invariants via labelled control terms"

lemma oseqp_sos_subterms:
  assumes "wellformed \<Gamma>"
      and "\<exists>pn. p \<in> subterms (\<Gamma> pn)"
      and "((\<sigma>, p), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
    shows "\<exists>pn. p' \<in> subterms (\<Gamma> pn)"
  using assms
  proof (induct p)
    fix p1 p2
    assume IH1: "\<exists>pn. p1 \<in> subterms (\<Gamma> pn) \<Longrightarrow>
                      ((\<sigma>, p1), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i \<Longrightarrow>
                      \<exists>pn. p' \<in> subterms (\<Gamma> pn)"
       and IH2: "\<exists>pn. p2 \<in> subterms (\<Gamma> pn) \<Longrightarrow>
                      ((\<sigma>, p2), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i \<Longrightarrow>
                      \<exists>pn. p' \<in> subterms (\<Gamma> pn)"
       and "\<exists>pn. p1 \<oplus> p2 \<in> subterms (\<Gamma> pn)"
       and "((\<sigma>, p1 \<oplus> p2), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
    from \<open>\<exists>pn. p1 \<oplus> p2 \<in> subterms (\<Gamma> pn)\<close> obtain pn
                                            where "p1 \<in> subterms (\<Gamma> pn)"
                                              and "p2 \<in> subterms (\<Gamma> pn)" by auto
    from \<open>((\<sigma>, p1 \<oplus> p2), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i\<close>
      have "((\<sigma>, p1), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i
            \<or> ((\<sigma>, p2), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i" by auto
    thus "\<exists>pn. p' \<in> subterms (\<Gamma> pn)"
    proof
      assume "((\<sigma>, p1), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
      with \<open>p1 \<in> subterms (\<Gamma> pn)\<close> show ?thesis by (auto intro: IH1)
    next
      assume "((\<sigma>, p2), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
      with \<open>p2 \<in> subterms (\<Gamma> pn)\<close> show ?thesis by (auto intro: IH2)
    qed
  qed auto

lemma oreachable_subterms:
  assumes "wellformed \<Gamma>"
      and "control_within \<Gamma> (init A)"
      and "trans A = oseqp_sos \<Gamma> i"
      and "(\<sigma>, p) \<in> oreachable A S U"
    shows "\<exists>pn. p \<in> subterms (\<Gamma> pn)"
  using assms(4)
  proof (induct rule: oreachable_pair_induct)
    fix \<sigma> p
    assume "(\<sigma>, p) \<in> init A"
    with \<open>control_within \<Gamma> (init A)\<close> show "\<exists>pn. p \<in> subterms (\<Gamma> pn)" ..
  next
    fix \<sigma> p a \<sigma>' p'
    assume "(\<sigma>, p) \<in> oreachable A S U"
       and "\<exists>pn. p \<in> subterms (\<Gamma> pn)"
       and 3: "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A"
       and "S \<sigma> \<sigma>' a"
    moreover from 3 and \<open>trans A = oseqp_sos \<Gamma> i\<close>
      have "((\<sigma>, p), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i" by simp
    ultimately show "\<exists>pn. p' \<in> subterms (\<Gamma> pn)"
    using \<open>wellformed \<Gamma>\<close>
      by (auto elim: oseqp_sos_subterms)
  qed

lemma onl_oinvariantI [intro]:
  assumes init: "\<And>\<sigma> p l. \<lbrakk> (\<sigma>, p) \<in> init A; l \<in> labels \<Gamma> p \<rbrakk> \<Longrightarrow> P (\<sigma>, l)"
      and other: "\<And>\<sigma> \<sigma>' p l. \<lbrakk> (\<sigma>, p) \<in> oreachable A S U;
                                \<forall>l\<in>labels \<Gamma> p. P (\<sigma>, l);
                                U \<sigma> \<sigma>' \<rbrakk> \<Longrightarrow> \<forall>l\<in>labels \<Gamma> p. P (\<sigma>', l)"
      and step: "\<And>\<sigma> p a \<sigma>' p' l'.
                   \<lbrakk> (\<sigma>, p) \<in> oreachable A S U;
                     \<forall>l\<in>labels \<Gamma> p. P (\<sigma>, l);
                     ((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A;
                     l' \<in> labels \<Gamma> p';
                     S \<sigma> \<sigma>' a \<rbrakk> \<Longrightarrow> P (\<sigma>', l')"
    shows "A \<Turnstile> (S, U \<rightarrow>) onl \<Gamma> P"
  proof
    fix \<sigma> p
    assume "(\<sigma>, p) \<in> init A"
    hence "\<forall>l\<in>labels \<Gamma> p. P (\<sigma>, l)" using init by simp
    thus "onl \<Gamma> P (\<sigma>, p)" ..
  next
    fix \<sigma> p a \<sigma>' p'
    assume rp: "(\<sigma>, p) \<in> oreachable A S U"
       and "onl \<Gamma> P (\<sigma>, p)"
       and tr: "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A"
       and "S \<sigma> \<sigma>' a"
    from \<open>onl \<Gamma> P (\<sigma>, p)\<close> have "\<forall>l\<in>labels \<Gamma> p. P (\<sigma>, l)" ..
    with rp tr \<open>S \<sigma> \<sigma>' a\<close> have "\<forall>l'\<in>labels \<Gamma> p'. P (\<sigma>', l')" by (auto elim: step)
    thus "onl \<Gamma> P (\<sigma>', p')" ..
  next
    fix \<sigma> \<sigma>' p
    assume "(\<sigma>, p) \<in> oreachable A S U"
       and "onl \<Gamma> P (\<sigma>, p)"
       and "U \<sigma> \<sigma>'"
    from \<open>onl \<Gamma> P (\<sigma>, p)\<close> have "\<forall>l\<in>labels \<Gamma> p. P (\<sigma>, l)" by auto
    with \<open>(\<sigma>, p) \<in> oreachable A S U\<close> have "\<forall>l\<in>labels \<Gamma> p. P (\<sigma>', l)"
        using \<open>U \<sigma> \<sigma>'\<close> by (rule other)
    thus "onl \<Gamma> P (\<sigma>', p)" by auto
  qed

lemma global_oinvariantI [intro]:
  assumes init: "\<And>\<sigma> p. (\<sigma>, p) \<in> init A \<Longrightarrow> P \<sigma>"
      and other: "\<And>\<sigma> \<sigma>' p l. \<lbrakk> (\<sigma>, p) \<in> oreachable A S U; P \<sigma>; U \<sigma> \<sigma>' \<rbrakk> \<Longrightarrow> P \<sigma>'"
      and step: "\<And>\<sigma> p a \<sigma>' p'.
                   \<lbrakk> (\<sigma>, p) \<in> oreachable A S U;
                     P \<sigma>;
                     ((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A;
                     S \<sigma> \<sigma>' a \<rbrakk> \<Longrightarrow> P \<sigma>'"
    shows "A \<Turnstile> (S, U \<rightarrow>) (\<lambda>(\<sigma>, _). P \<sigma>)"
  proof
    fix \<sigma> p
    assume "(\<sigma>, p) \<in> init A"
    thus "(\<lambda>(\<sigma>, _). P \<sigma>) (\<sigma>, p)"
      by simp (erule init)
  next
    fix \<sigma> p a \<sigma>' p'
    assume rp: "(\<sigma>, p) \<in> oreachable A S U"
       and "(\<lambda>(\<sigma>, _). P \<sigma>) (\<sigma>, p)"
       and tr: "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A"
       and "S \<sigma> \<sigma>' a"
    from \<open>(\<lambda>(\<sigma>, _). P \<sigma>) (\<sigma>, p)\<close> have "P \<sigma>" by simp
    with rp have "P \<sigma>'"
      using tr \<open>S \<sigma> \<sigma>' a\<close> by (rule step)
    thus "(\<lambda>(\<sigma>, _). P \<sigma>) (\<sigma>', p')" by simp
  next
    fix \<sigma> \<sigma>' p
    assume "(\<sigma>, p) \<in> oreachable A S U"
       and "(\<lambda>(\<sigma>, _). P \<sigma>) (\<sigma>, p)"
       and "U \<sigma> \<sigma>'"
    hence "P \<sigma>'" by simp (erule other)
    thus "(\<lambda>(\<sigma>, _). P \<sigma>) (\<sigma>', p)" by simp
  qed

lemma onl_oinvariantD [dest]:
  assumes "A \<Turnstile> (S, U \<rightarrow>) onl \<Gamma> P"
      and "(\<sigma>, p) \<in> oreachable A S U"
      and "l \<in> labels \<Gamma> p"
    shows "P (\<sigma>, l)"
  using assms unfolding onl_def by auto

lemma onl_oinvariant_weakenD [dest]:
  assumes "A \<Turnstile> (S', U' \<rightarrow>) onl \<Gamma> P"
      and "(\<sigma>, p) \<in> oreachable A S U"
      and "l \<in> labels \<Gamma> p"
      and weakenS: "\<And>s s' a. S s s' a \<Longrightarrow> S' s s' a"
      and weakenU: "\<And>s s'. U s s' \<Longrightarrow> U' s s'"
    shows "P (\<sigma>, l)"
  proof -
    from \<open>(\<sigma>, p) \<in> oreachable A S U\<close> have "(\<sigma>, p) \<in> oreachable A S' U'"
      by (rule oreachable_weakenE)
         (erule weakenS, erule weakenU)
    with \<open>A \<Turnstile> (S', U' \<rightarrow>) onl \<Gamma> P\<close> show "P (\<sigma>, l)"
      using \<open>l \<in> labels \<Gamma> p\<close> ..
  qed

lemma onl_oinvariant_initD [dest]:
  assumes invP: "A \<Turnstile> (S, U \<rightarrow>) onl \<Gamma> P"
      and init: "(\<sigma>, p) \<in> init A"
      and pnl:  "l \<in> labels \<Gamma> p"
    shows "P (\<sigma>, l)"
  proof -
    from init have "(\<sigma>, p) \<in> oreachable A S U" ..
    with invP show ?thesis using pnl ..
  qed

lemma onl_oinvariant_sterms:
  assumes wf: "wellformed \<Gamma>"
      and il: "A \<Turnstile> (S, U \<rightarrow>) onl \<Gamma> P"
      and rp: "(\<sigma>, p) \<in> oreachable A S U"
      and "p'\<in>sterms \<Gamma> p"
      and "l\<in>labels \<Gamma> p'"
    shows "P (\<sigma>, l)"
  proof -
    from wf \<open>p'\<in>sterms \<Gamma> p\<close> \<open>l\<in>labels \<Gamma> p'\<close> have "l\<in>labels \<Gamma> p"
      by (rule labels_sterms_labels)
    with il rp show "P (\<sigma>, l)" ..
  qed

lemma onl_oinvariant_sterms_weaken:
  assumes wf: "wellformed \<Gamma>"
      and il: "A \<Turnstile> (S', U' \<rightarrow>) onl \<Gamma> P"
      and rp: "(\<sigma>, p) \<in> oreachable A S U"
      and "p'\<in>sterms \<Gamma> p"
      and "l\<in>labels \<Gamma> p'"
      and weakenS: "\<And>\<sigma> \<sigma>' a. S \<sigma> \<sigma>' a \<Longrightarrow> S' \<sigma> \<sigma>' a"
      and weakenU: "\<And>\<sigma> \<sigma>'. U \<sigma> \<sigma>' \<Longrightarrow> U' \<sigma> \<sigma>'"
    shows "P (\<sigma>, l)"
  proof -
    from \<open>(\<sigma>, p) \<in> oreachable A S U\<close> have "(\<sigma>, p) \<in> oreachable A S' U'"
      by (rule oreachable_weakenE)
         (erule weakenS, erule weakenU)
    with assms(1-2) show ?thesis using assms(4-5)
      by (rule onl_oinvariant_sterms)
  qed

lemma otrans_from_sterms:
  assumes "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
      and "wellformed \<Gamma>"
    shows "\<exists>p'\<in>sterms \<Gamma> p. ((\<sigma>, p'), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
  using assms by (induction p rule: sterms_pinduct [OF \<open>wellformed \<Gamma>\<close>]) auto

lemma otrans_from_sterms':
  assumes "((\<sigma>, p'), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
      and "wellformed \<Gamma>"
      and "p' \<in> sterms \<Gamma> p"
    shows "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
  using assms by (induction p rule: sterms_pinduct [OF \<open>wellformed \<Gamma>\<close>]) auto

lemma otrans_to_dterms:
  assumes "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
      and "wellformed \<Gamma>"
   shows "\<forall>r\<in>sterms \<Gamma> q. r \<in> dterms \<Gamma> p"
  using assms by (induction q) auto

theorem cterms_includes_sterms_of_oseq_reachable:
  assumes "wellformed \<Gamma>"
      and "control_within \<Gamma> (init A)"
      and "trans A = oseqp_sos \<Gamma> i"
    shows "\<Union>(sterms \<Gamma> ` snd ` oreachable A S U) \<subseteq> cterms \<Gamma>"
  proof
    fix qs
    assume "qs \<in> \<Union>(sterms \<Gamma> ` snd ` oreachable A S U)"
    then obtain \<xi> and q where  *: "(\<xi>, q) \<in> oreachable A S U"
                          and **: "qs \<in> sterms \<Gamma> q" by auto
    from * have "\<And>x. x \<in> sterms \<Gamma> q \<Longrightarrow> x \<in> cterms \<Gamma>"
    proof (induction rule: oreachable_pair_induct)
      fix \<sigma> p q
      assume "(\<sigma>, p) \<in> init A"
         and "q \<in> sterms \<Gamma> p"
      from \<open>control_within \<Gamma> (init A)\<close> and \<open>(\<sigma>, p) \<in> init A\<close>
        obtain pn where "p \<in> subterms (\<Gamma> pn)" by auto
      with \<open>wellformed \<Gamma>\<close> show "q \<in> cterms \<Gamma>" using \<open>q\<in>sterms \<Gamma> p\<close>
        by (rule subterms_sterms_in_cterms)
    next
      fix p \<sigma> a \<sigma>' q x
      assume "(\<sigma>, p) \<in> oreachable A S U"
         and IH: "\<And>x. x \<in> sterms \<Gamma> p \<Longrightarrow> x \<in> cterms \<Gamma>"
         and "((\<sigma>, p), a, (\<sigma>', q)) \<in> trans A"
         and "x \<in> sterms \<Gamma> q"
      from this(3) and \<open>trans A = oseqp_sos \<Gamma> i\<close>
        have step: "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i" by simp
      from step \<open>wellformed \<Gamma>\<close> obtain ps
        where ps: "ps \<in> sterms \<Gamma> p"
          and step': "((\<sigma>, ps), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
        by (rule otrans_from_sterms [THEN bexE])
      from ps have "ps \<in> cterms \<Gamma>" by (rule IH)
      moreover from step' \<open>wellformed \<Gamma>\<close> \<open>x \<in> sterms \<Gamma> q\<close> have "x \<in> dterms \<Gamma> ps"
        by (rule otrans_to_dterms [rule_format])
      ultimately show "x \<in> cterms \<Gamma>" by (rule ctermsDI)
    qed
    thus "qs \<in> cterms \<Gamma>" using ** .
  qed

corollary oseq_reachable_in_cterms:
  assumes "wellformed \<Gamma>"
      and "control_within \<Gamma> (init A)"
      and "trans A = oseqp_sos \<Gamma> i"
      and "(\<sigma>, p) \<in> oreachable A S U"
      and "p' \<in> sterms \<Gamma> p"
    shows "p' \<in> cterms \<Gamma>"
  using assms(1-3)
  proof (rule cterms_includes_sterms_of_oseq_reachable [THEN subsetD])
    from assms(4-5) show "p' \<in> \<Union>(sterms \<Gamma> ` snd ` oreachable A S U)"
      by (auto elim!: rev_bexI)
  qed

lemma oseq_invariant_ctermI:
  assumes wf: "wellformed \<Gamma>"
      and cw: "control_within \<Gamma> (init A)"
      and sl: "simple_labels \<Gamma>"
      and sp: "trans A = oseqp_sos \<Gamma> i"
      and init: "\<And>\<sigma> p l. \<lbrakk>
                   (\<sigma>, p) \<in> init A;
                   l\<in>labels \<Gamma> p
                 \<rbrakk> \<Longrightarrow> P (\<sigma>, l)"
      and other: "\<And>\<sigma> \<sigma>' p l. \<lbrakk>
                   (\<sigma>, p) \<in> oreachable A S U;
                   l\<in>labels \<Gamma> p;
                   P (\<sigma>, l);
                   U \<sigma> \<sigma>' \<rbrakk> \<Longrightarrow> P (\<sigma>', l)"
      and local: "\<And>p l \<sigma> a q l' \<sigma>' pp. \<lbrakk>
                 p\<in>cterms \<Gamma>;
                 l\<in>labels \<Gamma> p;
                 P (\<sigma>, l);
                 ((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i;
                 ((\<sigma>, p), a, (\<sigma>', q)) \<in> trans A;
                 l'\<in>labels \<Gamma> q;
                 (\<sigma>, pp)\<in>oreachable A S U;
                 p\<in>sterms \<Gamma> pp;
                 (\<sigma>', q)\<in>oreachable A S U;
                 S \<sigma> \<sigma>' a
               \<rbrakk> \<Longrightarrow> P (\<sigma>', l')"
    shows "A \<Turnstile> (S, U \<rightarrow>) onl \<Gamma> P"
  proof
       fix \<sigma> p l
    assume "(\<sigma>, p) \<in> init A"
       and *: "l \<in> labels \<Gamma> p"
      with init show "P (\<sigma>, l)" by auto
  next
       fix \<sigma> p a \<sigma>' q l'
    assume sr: "(\<sigma>, p) \<in> oreachable A S U"
       and pl: "\<forall>l\<in>labels \<Gamma> p. P (\<sigma>, l)"
       and tr: "((\<sigma>, p), a, (\<sigma>', q)) \<in> trans A"
       and A6: "l' \<in> labels \<Gamma> q"
       and "S \<sigma> \<sigma>' a"
      thus "P (\<sigma>', l')"
    proof -
      from sr and tr and \<open>S \<sigma> \<sigma>' a\<close> have A7: "(\<sigma>', q) \<in> oreachable A S U"
        by - (rule oreachable_local')
      from tr and sp have tr': "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i" by simp
      then obtain p' where "p' \<in> sterms \<Gamma> p"
                       and A4: "((\<sigma>, p'), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
        by (blast dest: otrans_from_sterms [OF _ wf])
      from wf cw sp sr this(1) have A1: "p'\<in>cterms \<Gamma>"
        by (rule oseq_reachable_in_cterms)
      from labels_not_empty [OF wf] obtain ll where A2: "ll\<in>labels \<Gamma> p'"
          by blast
      with \<open>p'\<in>sterms \<Gamma> p\<close> have "ll\<in>labels \<Gamma> p"
        by (rule labels_sterms_labels [OF wf])
      with pl have A3: "P (\<sigma>, ll)" by simp
      from sr \<open>p'\<in>sterms \<Gamma> p\<close>
        obtain pp where A7: "(\<sigma>, pp)\<in>oreachable A S U"
                    and A8: "p'\<in>sterms \<Gamma> pp"
        by auto
      from sr tr \<open>S \<sigma> \<sigma>' a\<close> have A9: "(\<sigma>', q)\<in>oreachable A S U"
        by - (rule oreachable_local')
      from sp and \<open>((\<sigma>, p'), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i\<close>
        have A5: "((\<sigma>, p'), a, (\<sigma>', q)) \<in> trans A" by simp
      from A1 A2 A3 A4 A5 A6 A7 A8 A9 \<open>S \<sigma> \<sigma>' a\<close> show ?thesis by (rule local)
    qed
  next
    fix \<sigma> \<sigma>' p l
    assume sr: "(\<sigma>, p) \<in> oreachable A S U"
       and "\<forall>l\<in>labels \<Gamma> p. P (\<sigma>, l)"
       and "U \<sigma> \<sigma>'"
    show "\<forall>l\<in>labels \<Gamma> p. P (\<sigma>', l)"
    proof
      fix l
      assume "l\<in>labels \<Gamma> p"
      with \<open>\<forall>l\<in>labels \<Gamma> p. P (\<sigma>, l)\<close> have "P (\<sigma>, l)" ..
      with sr and \<open>l\<in>labels \<Gamma> p\<close>
        show "P (\<sigma>', l)" using \<open>U \<sigma> \<sigma>'\<close> by (rule other)
    qed
  qed

lemma oseq_invariant_ctermsI:
  assumes wf: "wellformed \<Gamma>"
      and cw: "control_within \<Gamma> (init A)"
      and sl: "simple_labels \<Gamma>"
      and sp: "trans A = oseqp_sos \<Gamma> i"
      and init: "\<And>\<sigma> p l. \<lbrakk>
                   (\<sigma>, p) \<in> init A;
                   l\<in>labels \<Gamma> p
                 \<rbrakk> \<Longrightarrow> P (\<sigma>, l)"
      and other: "\<And>\<sigma> \<sigma>' p l. \<lbrakk>
                   wellformed \<Gamma>;
                   (\<sigma>, p) \<in> oreachable A S U;
                   l\<in>labels \<Gamma> p;
                   P (\<sigma>, l);
                   U \<sigma> \<sigma>' \<rbrakk> \<Longrightarrow> P (\<sigma>', l)"
      and local: "\<And>p l \<sigma> a q l' \<sigma>' pp pn. \<lbrakk>
                 wellformed \<Gamma>;
                 p\<in>ctermsl (\<Gamma> pn);
                 not_call p;
                 l\<in>labels \<Gamma> p;
                 P (\<sigma>, l);
                 ((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i;
                 ((\<sigma>, p), a, (\<sigma>', q)) \<in> trans A;
                 l'\<in>labels \<Gamma> q;
                 (\<sigma>, pp)\<in>oreachable A S U;
                 p\<in>sterms \<Gamma> pp;
                 (\<sigma>', q)\<in>oreachable A S U;
                 S \<sigma> \<sigma>' a
               \<rbrakk> \<Longrightarrow> P (\<sigma>', l')"
    shows "A \<Turnstile> (S, U \<rightarrow>) onl \<Gamma> P"
  proof (rule oseq_invariant_ctermI [OF wf cw sl sp])
    fix \<sigma> p l
    assume "(\<sigma>, p) \<in> init A"
       and "l \<in> labels \<Gamma> p"
    thus "P (\<sigma>, l)" by (rule init)
  next
    fix \<sigma> \<sigma>' p l
    assume "(\<sigma>, p) \<in> oreachable A S U"
       and "l \<in> labels \<Gamma> p"
       and "P (\<sigma>, l)"
       and "U \<sigma> \<sigma>'"
    with wf show "P (\<sigma>', l)" by (rule other)
  next
    fix p l \<sigma> a q l' \<sigma>' pp
    assume "p \<in> cterms \<Gamma>"
       and otherassms: "l \<in> labels \<Gamma> p"
           "P (\<sigma>, l)"
           "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
           "((\<sigma>, p), a, (\<sigma>', q)) \<in> trans A"
           "l' \<in> labels \<Gamma> q"
           "(\<sigma>, pp) \<in> oreachable A S U"
           "p \<in> sterms \<Gamma> pp"
           "(\<sigma>', q) \<in> oreachable A S U"
           "S \<sigma> \<sigma>' a"
    from this(1) obtain pn where "p \<in> ctermsl(\<Gamma> pn)"
                             and "not_call p"
      unfolding cterms_def' [OF wf] by auto
    with wf show "P (\<sigma>', l')"
      using otherassms by (rule local)
  qed

subsection "Open step invariants via labelled control terms"

lemma onll_ostep_invariantI [intro]:
  assumes *: "\<And>\<sigma> p l a \<sigma>' p' l'. \<lbrakk> (\<sigma>, p)\<in>oreachable A S U;
                                   ((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A;
                                   S \<sigma> \<sigma>' a;
                                   l \<in>labels \<Gamma> p;
                                   l'\<in>labels \<Gamma> p' \<rbrakk>
                                 \<Longrightarrow> P ((\<sigma>, l), a, (\<sigma>', l'))"
    shows "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) onll \<Gamma> P"
  proof
    fix \<sigma> p \<sigma>' p' a
    assume "(\<sigma>, p) \<in> oreachable A S U"
       and "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A"
       and "S \<sigma> \<sigma>' a"
    hence "\<forall>l\<in>labels \<Gamma> p. \<forall>l'\<in>labels \<Gamma> p'. P ((\<sigma>, l), a, (\<sigma>', l'))" by (auto elim!: *)
    thus "onll \<Gamma> P ((\<sigma>, p), a, (\<sigma>', p'))" ..
  qed

lemma onll_ostep_invariantE [elim]:
  assumes "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) onll \<Gamma> P"
      and "(\<sigma>, p) \<in> oreachable A S U"
      and "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A"
      and "S \<sigma> \<sigma>' a"
      and lp:  "l \<in>labels \<Gamma> p"
      and lp': "l'\<in>labels \<Gamma> p'"
    shows "P ((\<sigma>, l), a, (\<sigma>', l'))"
  proof -
    from assms(1-4) have "onll \<Gamma> P ((\<sigma>, p), a, (\<sigma>', p'))" ..
    with lp lp' show "P ((\<sigma>, l), a, (\<sigma>', l'))" by auto
  qed

lemma onll_ostep_invariantD [dest]:
  assumes "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) onll \<Gamma> P"
      and "(\<sigma>, p) \<in> oreachable A S U"
      and "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A"
      and "S \<sigma> \<sigma>' a"
    shows "\<forall>l\<in>labels \<Gamma> p. \<forall>l'\<in>labels \<Gamma> p'. P ((\<sigma>, l), a, (\<sigma>', l'))"
  using assms by auto

lemma onll_ostep_invariant_weakenD [dest]:
  assumes "A \<Turnstile>\<^sub>A (S', U' \<rightarrow>) onll \<Gamma> P"
      and "(\<sigma>, p) \<in> oreachable A S U"
      and "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A"
      and "S' \<sigma> \<sigma>' a"
      and weakenS: "\<And>s s' a. S s s' a \<Longrightarrow> S' s s' a"
      and weakenU: "\<And>s s'. U s s' \<Longrightarrow> U' s s'"
    shows "\<forall>l\<in>labels \<Gamma> p. \<forall>l'\<in>labels \<Gamma> p'. P ((\<sigma>, l), a, (\<sigma>', l'))"
  proof -
    from \<open>(\<sigma>, p) \<in> oreachable A S U\<close> have "(\<sigma>, p) \<in> oreachable A S' U'"
      by (rule oreachable_weakenE)
         (erule weakenS, erule weakenU)
    with \<open>A \<Turnstile>\<^sub>A (S', U' \<rightarrow>) onll \<Gamma> P\<close> show ?thesis
      using \<open>((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A\<close> and \<open>S' \<sigma> \<sigma>' a\<close> ..
  qed

lemma onll_ostep_to_invariantI [intro]:
  assumes sinv: "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) onll \<Gamma> Q"
      and wf: "wellformed \<Gamma>"
      and init: "\<And>\<sigma> l p. \<lbrakk> (\<sigma>, p) \<in> init A; l\<in>labels \<Gamma> p \<rbrakk> \<Longrightarrow> P (\<sigma>, l)"
      and other: "\<And>\<sigma> \<sigma>' p l.
                    \<lbrakk> (\<sigma>, p) \<in> oreachable A S U;
                      l\<in>labels \<Gamma> p;
                      P (\<sigma>, l);
                      U \<sigma> \<sigma>' \<rbrakk> \<Longrightarrow> P (\<sigma>', l)"
      and local: "\<And>\<sigma> p l \<sigma>' l' a.
                    \<lbrakk> (\<sigma>, p) \<in> oreachable A S U;
                      l\<in>labels \<Gamma> p;
                      P (\<sigma>, l);
                      Q ((\<sigma>, l), a, (\<sigma>', l'));
                      S \<sigma> \<sigma>' a\<rbrakk> \<Longrightarrow> P (\<sigma>', l')"
    shows "A \<Turnstile> (S, U \<rightarrow>) onl \<Gamma> P"
  proof
    fix \<sigma> p l
    assume "(\<sigma>, p) \<in> init A" and "l\<in>labels \<Gamma> p"
      thus "P (\<sigma>, l)" by (rule init)
  next
    fix \<sigma> p a \<sigma>' p' l'
    assume sr: "(\<sigma>, p) \<in> oreachable A S U"
       and lp: "\<forall>l\<in>labels \<Gamma> p. P (\<sigma>, l)"
       and tr: "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A"
       and "S \<sigma> \<sigma>' a"
       and lp': "l' \<in> labels \<Gamma> p'"
      show "P (\<sigma>', l')"
    proof -
      from lp obtain l where "l\<in>labels \<Gamma> p" and "P (\<sigma>, l)"
        using labels_not_empty [OF wf] by auto
      from sinv sr tr \<open>S \<sigma> \<sigma>' a\<close> this(1) lp' have "Q ((\<sigma>, l), a, (\<sigma>', l'))" ..
      with sr \<open>l\<in>labels \<Gamma> p\<close> \<open>P (\<sigma>, l)\<close> show "P (\<sigma>', l')" using \<open>S \<sigma> \<sigma>' a\<close> by (rule local)
    qed
  next
    fix \<sigma> \<sigma>' p l
    assume "(\<sigma>, p) \<in> oreachable A S U"
       and "\<forall>l\<in>labels \<Gamma> p. P (\<sigma>, l)"
       and "U \<sigma> \<sigma>'"
      show "\<forall>l\<in>labels \<Gamma> p. P (\<sigma>', l)"
    proof
      fix l
      assume "l\<in>labels \<Gamma> p"
      with \<open>\<forall>l\<in>labels \<Gamma> p. P (\<sigma>, l)\<close> have "P (\<sigma>, l)" ..
      with \<open>(\<sigma>, p) \<in> oreachable A S U\<close> and \<open>l\<in>labels \<Gamma> p\<close>
      show "P (\<sigma>', l)" using \<open>U \<sigma> \<sigma>'\<close> by (rule other)
    qed
  qed

lemma onll_ostep_invariant_sterms:
  assumes wf: "wellformed \<Gamma>"
      and si: "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) onll \<Gamma> P"
      and sr: "(\<sigma>, p) \<in> oreachable A S U"
      and sos: "((\<sigma>, p), a, (\<sigma>', q)) \<in> trans A"
      and "S \<sigma> \<sigma>' a"
      and "l'\<in>labels \<Gamma> q"
      and "p'\<in>sterms \<Gamma> p"
      and "l\<in>labels \<Gamma> p'"
    shows "P ((\<sigma>, l), a, (\<sigma>', l'))"
  proof -
    from wf \<open>p'\<in>sterms \<Gamma> p\<close> \<open>l\<in>labels \<Gamma> p'\<close> have "l\<in>labels \<Gamma> p"
      by (rule labels_sterms_labels)
    with si sr sos \<open>S \<sigma> \<sigma>' a\<close> show "P ((\<sigma>, l), a, (\<sigma>', l'))" using \<open>l'\<in>labels \<Gamma> q\<close> ..
  qed

lemma oseq_step_invariant_sterms:
  assumes inv: "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) onll \<Gamma> P"
      and wf: "wellformed \<Gamma>"
      and sp: "trans A = oseqp_sos \<Gamma> i"
      and "l'\<in>labels \<Gamma> q"
      and sr: "(\<sigma>, p) \<in> oreachable A S U"
      and tr: "((\<sigma>, p'), a, (\<sigma>', q)) \<in> trans A"
      and "S \<sigma> \<sigma>' a"
      and "p'\<in>sterms \<Gamma> p"
    shows "\<forall>l\<in>labels \<Gamma> p'. P ((\<sigma>, l), a, (\<sigma>', l'))"
  proof
    from assms(3, 6) have "((\<sigma>, p'), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i" by simp
    hence "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
      using wf \<open>p'\<in>sterms \<Gamma> p\<close>  by (rule otrans_from_sterms')
    with assms(3) have trp: "((\<sigma>, p), a, (\<sigma>', q)) \<in> trans A" by simp
    fix l assume "l \<in> labels \<Gamma> p'"
    with wf inv sr trp \<open>S \<sigma> \<sigma>' a\<close> \<open>l'\<in>labels \<Gamma> q\<close> \<open>p'\<in>sterms \<Gamma> p\<close>
      show "P ((\<sigma>, l), a, (\<sigma>', l'))"
        by - (erule(7) onll_ostep_invariant_sterms)
  qed

lemma oseq_step_invariant_sterms_weaken:
  assumes inv: "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) onll \<Gamma> P"
      and wf: "wellformed \<Gamma>"
      and sp: "trans A = oseqp_sos \<Gamma> i"
      and "l'\<in>labels \<Gamma> q"
      and sr: "(\<sigma>, p) \<in> oreachable A S' U'"
      and tr: "((\<sigma>, p'), a, (\<sigma>', q)) \<in> trans A"
      and "S' \<sigma> \<sigma>' a"
      and "p'\<in>sterms \<Gamma> p"
      and weakenS: "\<And>\<sigma> \<sigma>' a. S' \<sigma> \<sigma>' a \<Longrightarrow> S \<sigma> \<sigma>' a"
      and weakenU: "\<And>\<sigma> \<sigma>'. U' \<sigma> \<sigma>' \<Longrightarrow> U \<sigma> \<sigma>'"
    shows "\<forall>l\<in>labels \<Gamma> p'. P ((\<sigma>, l), a, (\<sigma>', l'))"
  proof -
    from \<open>S' \<sigma> \<sigma>' a\<close> have "S \<sigma> \<sigma>' a" by (rule weakenS)
    from \<open>(\<sigma>, p) \<in> oreachable A S' U'\<close>
      have Ir: "(\<sigma>, p) \<in> oreachable A S U"
        by (rule oreachable_weakenE)
           (erule weakenS, erule weakenU)
    with assms(1-4) show ?thesis
      using tr \<open>S \<sigma> \<sigma>' a\<close> \<open>p'\<in>sterms \<Gamma> p\<close>
      by (rule oseq_step_invariant_sterms)
  qed

lemma onll_ostep_invariant_any_sterms:
  assumes wf: "wellformed \<Gamma>"
      and si: "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) onll \<Gamma> P"
      and sr: "(\<sigma>, p) \<in> oreachable A S U"
      and sos: "((\<sigma>, p), a, (\<sigma>', q)) \<in> trans A"
      and "S \<sigma> \<sigma>' a"
      and "l'\<in>labels \<Gamma> q"
    shows "\<forall>p'\<in>sterms \<Gamma> p. \<forall>l\<in>labels \<Gamma> p'. P ((\<sigma>, l), a, (\<sigma>', l'))"
  by (intro ballI) (rule onll_ostep_invariant_sterms [OF assms])

lemma oseq_step_invariant_ctermI [intro]:
  assumes wf: "wellformed \<Gamma>"
      and cw: "control_within \<Gamma> (init A)"
      and sl: "simple_labels \<Gamma>"
      and sp: "trans A = oseqp_sos \<Gamma> i"
      and local: "\<And>p l \<sigma> a q l' \<sigma>' pp. \<lbrakk>
                   p\<in>cterms \<Gamma>;
                   l\<in>labels \<Gamma> p;
                   ((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i;
                   ((\<sigma>, p), a, (\<sigma>', q)) \<in> trans A;
                   l'\<in>labels \<Gamma> q;
                   (\<sigma>, pp) \<in> oreachable A S U;
                   p\<in>sterms \<Gamma> pp;
                   (\<sigma>', q) \<in> oreachable A S U;
                   S \<sigma> \<sigma>' a
                 \<rbrakk> \<Longrightarrow> P ((\<sigma>, l), a, (\<sigma>', l'))"
    shows "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) onll \<Gamma> P"
  proof
       fix \<sigma> p l a \<sigma>' q l'
    assume sr: "(\<sigma>, p) \<in> oreachable A S U"
       and tr: "((\<sigma>, p), a, (\<sigma>', q)) \<in> trans A"
       and "S \<sigma> \<sigma>' a"
       and pl: "l \<in> labels \<Gamma> p"
       and A5: "l' \<in> labels \<Gamma> q"
    from this(2) and sp have "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i" by simp
    then obtain p' where "p' \<in> sterms \<Gamma> p"
                     and A3: "((\<sigma>, p'), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
      by (blast dest: otrans_from_sterms [OF _ wf])
    from this(2) and sp have A4: "((\<sigma>, p'), a, (\<sigma>', q)) \<in> trans A" by simp
    from wf cw sp sr \<open>p'\<in>sterms \<Gamma> p\<close> have A1: "p'\<in>cterms \<Gamma>"
      by (rule oseq_reachable_in_cterms)
    from sr \<open>p'\<in>sterms \<Gamma> p\<close>
      obtain pp where A6: "(\<sigma>, pp)\<in>oreachable A S U"
                  and A7: "p'\<in>sterms \<Gamma> pp"
      by auto
    from sr tr \<open>S \<sigma> \<sigma>' a\<close> have A8: "(\<sigma>', q)\<in>oreachable A S U"
      by - (erule(2) oreachable_local')
    from wf cw sp sr have "\<exists>pn. p \<in> subterms (\<Gamma> pn)"
      by (rule oreachable_subterms)           
    with sl wf have "\<forall>p'\<in>sterms \<Gamma> p. l \<in> labels \<Gamma> p'"
      using pl by (rule simple_labels_in_sterms)
    with \<open>p' \<in> sterms \<Gamma> p\<close> have "l \<in> labels \<Gamma> p'" by simp
    with A1 show "P ((\<sigma>, l), a, (\<sigma>', l'))" using A3 A4 A5 A6 A7 A8 \<open>S \<sigma> \<sigma>' a\<close>
      by (rule local)
  qed

lemma oseq_step_invariant_ctermsI [intro]:
  assumes wf: "wellformed \<Gamma>"
      and "control_within \<Gamma> (init A)"
      and "simple_labels \<Gamma>"
      and "trans A = oseqp_sos \<Gamma> i"
      and local: "\<And>p l \<sigma> a q l' \<sigma>' pp pn. \<lbrakk>
                   wellformed \<Gamma>;
                   p\<in>ctermsl (\<Gamma> pn);
                   not_call p;
                   l\<in>labels \<Gamma> p;
                   ((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i;
                   ((\<sigma>, p), a, (\<sigma>', q)) \<in> trans A;
                   l'\<in>labels \<Gamma> q;
                   (\<sigma>, pp) \<in> oreachable A S U;
                   p\<in>sterms \<Gamma> pp;
                   (\<sigma>', q) \<in> oreachable A S U;
                   S \<sigma> \<sigma>' a
                 \<rbrakk> \<Longrightarrow> P ((\<sigma>, l), a, (\<sigma>', l'))"
    shows "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) onll \<Gamma> P"
  using assms(1-4) proof (rule oseq_step_invariant_ctermI)
    fix p l \<sigma> a q l' \<sigma>' pp
    assume "p \<in> cterms \<Gamma>"
       and otherassms: "l \<in> labels \<Gamma> p"
           "((\<sigma>, p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
           "((\<sigma>, p), a, (\<sigma>', q)) \<in> trans A"
           "l' \<in> labels \<Gamma> q"
           "(\<sigma>, pp) \<in> oreachable A S U"
           "p \<in> sterms \<Gamma> pp"
           "(\<sigma>', q) \<in> oreachable A S U"
           "S \<sigma> \<sigma>' a"
    from this(1) obtain pn where "p \<in> ctermsl(\<Gamma> pn)"
                             and "not_call p"
      unfolding cterms_def' [OF wf] by auto
    with wf show "P ((\<sigma>, l), a, (\<sigma>', l'))"
      using otherassms by (rule local)
 qed

lemma open_seqp_action [elim]:
  assumes "wellformed \<Gamma>"
      and "((\<sigma> i, p), a, (\<sigma>' i, p')) \<in> seqp_sos \<Gamma>"
    shows "((\<sigma>, p), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
  proof -
    from assms obtain ps where "ps\<in>sterms \<Gamma> p"
                           and "((\<sigma> i, ps), a, (\<sigma>' i, p')) \<in> seqp_sos \<Gamma>"
      by - (drule trans_from_sterms, auto)
    thus ?thesis
    proof (induction p)
      fix p1 p2
      assume "\<lbrakk> ps \<in> sterms \<Gamma> p1; ((\<sigma> i, ps), a, \<sigma>' i, p') \<in> seqp_sos \<Gamma> \<rbrakk>
              \<Longrightarrow> ((\<sigma>, p1), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
         and "\<lbrakk> ps \<in> sterms \<Gamma> p2; ((\<sigma> i, ps), a, \<sigma>' i, p') \<in> seqp_sos \<Gamma> \<rbrakk>
              \<Longrightarrow> ((\<sigma>, p2), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
         and "ps \<in> sterms \<Gamma> (p1 \<oplus> p2)"
         and "((\<sigma> i, ps), a, (\<sigma>' i, p')) \<in> seqp_sos \<Gamma>"
      with assms(1) show "((\<sigma>, p1 \<oplus> p2), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
        by simp (metis oseqp_sos.ochoiceT1 oseqp_sos.ochoiceT2)
    next
      fix l fip fmsg p1 p2
      assume IH1: "\<lbrakk> ps \<in> sterms \<Gamma> p1; ((\<sigma> i, ps), a, \<sigma>' i, p') \<in> seqp_sos \<Gamma> \<rbrakk>
                    \<Longrightarrow> ((\<sigma>, p1), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
         and IH2: "\<lbrakk> ps \<in> sterms \<Gamma> p2; ((\<sigma> i, ps), a, \<sigma>' i, p') \<in> seqp_sos \<Gamma> \<rbrakk>
                    \<Longrightarrow> ((\<sigma>, p2), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
         and "ps \<in> sterms \<Gamma> ({l}unicast(fip, fmsg). p1 \<triangleright> p2)"
         and "((\<sigma> i, ps), a, (\<sigma>' i, p')) \<in> seqp_sos \<Gamma>"
      from this(3-4) have "((\<sigma> i, {l}unicast(fip, fmsg). p1 \<triangleright> p2), a, (\<sigma>' i, p')) \<in> seqp_sos \<Gamma>"
        by simp
      thus "((\<sigma>, {l}unicast(fip, fmsg). p1 \<triangleright> p2), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
      proof (rule seqp_unicastTE)
        assume "a = unicast (fip (\<sigma> i)) (fmsg (\<sigma> i))"
           and "\<sigma>' i = \<sigma> i"
           and "p' = p1"
        thus ?thesis by auto
      next
        assume "a = \<not>unicast (fip (\<sigma> i))"
           and "\<sigma>' i = \<sigma> i"
           and "p' = p2"
        thus ?thesis by auto
      qed
    next
      fix p
      assume "ps \<in> sterms \<Gamma> (call(p))"
         and "((\<sigma> i, ps), a, (\<sigma>' i, p')) \<in> seqp_sos \<Gamma>"
      with assms(1) have "((\<sigma>, ps), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
        by (cases ps) auto
      with assms(1) \<open>ps \<in> sterms \<Gamma> (call(p))\<close> have "((\<sigma>, \<Gamma> p), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
        by - (rule otrans_from_sterms', simp_all)
      thus "((\<sigma>, call(p)), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i" by auto
    qed auto
  qed

end

