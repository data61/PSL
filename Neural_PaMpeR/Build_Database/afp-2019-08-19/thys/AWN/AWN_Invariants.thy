(*  Title:       AWN_Invariants.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Generic invariants on sequential AWN processes"

theory AWN_Invariants
imports Invariants AWN_SOS AWN_Labels
begin

subsection "Invariants via labelled control terms"

text \<open>
  Used to state that the initial control-state of an automaton appears within a process
  specification \<open>\<Gamma>\<close>, meaning that its transitions, and those of its subterms, are
  subsumed by those of \<open>\<Gamma>\<close>.
\<close>

definition
  control_within :: "('s, 'm, 'p, 'l) seqp_env \<Rightarrow> ('z \<times> ('s, 'm, 'p, 'l) seqp) set \<Rightarrow> bool"
where
  "control_within \<Gamma> \<sigma> \<equiv> \<forall>(\<xi>, p)\<in>\<sigma>. \<exists>pn. p \<in> subterms (\<Gamma> pn)"

lemma control_withinI [intro]:
  assumes "\<And>p. p \<in> Range \<sigma> \<Longrightarrow> \<exists>pn. p \<in> subterms (\<Gamma> pn)"
    shows "control_within \<Gamma> \<sigma>"
  using assms unfolding control_within_def by auto

lemma control_withinD [dest]:
  assumes "control_within \<Gamma> \<sigma>"
      and "(\<xi>, p) \<in> \<sigma>"
    shows "\<exists>pn. p \<in> subterms (\<Gamma> pn)"
  using assms unfolding control_within_def by blast

lemma control_within_topI [intro]:
  assumes "\<And>p. p \<in> Range \<sigma> \<Longrightarrow> \<exists>pn. p = \<Gamma> pn"
    shows "control_within \<Gamma> \<sigma>"
  using assms unfolding control_within_def
  by clarsimp (metis Range.RangeI subterms_refl)

lemma seqp_sos_subterms:
  assumes "wellformed \<Gamma>"
      and "\<exists>pn. p \<in> subterms (\<Gamma> pn)"
      and "((\<xi>, p), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>"
    shows "\<exists>pn. p' \<in> subterms (\<Gamma> pn)"
  using assms
  proof (induct p)
    fix p1 p2
    assume IH1: "\<exists>pn. p1 \<in> subterms (\<Gamma> pn) \<Longrightarrow>
                      ((\<xi>, p1), a, (\<xi>', p')) \<in> seqp_sos \<Gamma> \<Longrightarrow>
                      \<exists>pn. p' \<in> subterms (\<Gamma> pn)"
       and IH2: "\<exists>pn. p2 \<in> subterms (\<Gamma> pn) \<Longrightarrow>
                      ((\<xi>, p2), a, (\<xi>', p')) \<in> seqp_sos \<Gamma> \<Longrightarrow>
                      \<exists>pn. p' \<in> subterms (\<Gamma> pn)"
       and "\<exists>pn. p1 \<oplus> p2 \<in> subterms (\<Gamma> pn)"
       and "((\<xi>, p1 \<oplus> p2), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>"
    from \<open>\<exists>pn. p1 \<oplus> p2 \<in> subterms (\<Gamma> pn)\<close> obtain pn
                                            where "p1 \<in> subterms (\<Gamma> pn)"
                                              and "p2 \<in> subterms (\<Gamma> pn)" by auto
    from \<open>((\<xi>, p1 \<oplus> p2), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>\<close>
      have "((\<xi>, p1), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>
            \<or> ((\<xi>, p2), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>" by auto
    thus "\<exists>pn. p' \<in> subterms (\<Gamma> pn)"
    proof
      assume "((\<xi>, p1), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>"
      with \<open>p1 \<in> subterms (\<Gamma> pn)\<close> show ?thesis by (auto intro: IH1)
    next
      assume "((\<xi>, p2), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>"
      with \<open>p2 \<in> subterms (\<Gamma> pn)\<close> show ?thesis by (auto intro: IH2)
    qed
  qed auto

lemma reachable_subterms:
  assumes "wellformed \<Gamma>"
      and "control_within \<Gamma> (init A)"
      and "trans A = seqp_sos \<Gamma>"
      and "(\<xi>, p) \<in> reachable A I"
    shows "\<exists>pn. p \<in> subterms (\<Gamma> pn)"
  using assms(4)
  proof (induct rule: reachable_pair_induct)
    fix \<xi> p
    assume "(\<xi>, p) \<in> init A"
    with \<open>control_within \<Gamma> (init A)\<close> show "\<exists>pn. p \<in> subterms (\<Gamma> pn)" ..
  next
    fix \<xi> p a \<xi>' p'
    assume "(\<xi>, p) \<in> reachable A I"
       and "\<exists>pn. p \<in> subterms (\<Gamma> pn)"
       and *: "((\<xi>, p), a, (\<xi>', p')) \<in> trans A"
       and "I a"
    moreover from * and assms(3) have "((\<xi>, p), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>" by simp
    ultimately show "\<exists>pn. p' \<in> subterms (\<Gamma> pn)"
    using \<open>wellformed \<Gamma>\<close>
      by (auto elim: seqp_sos_subterms)
  qed

definition
  onl :: "('s, 'm, 'p, 'l) seqp_env
           \<Rightarrow> ('z \<times> 'l \<Rightarrow> bool)
           \<Rightarrow> 'z \<times> ('s, 'm, 'p, 'l) seqp
           \<Rightarrow> bool"
where
  "onl \<Gamma> P \<equiv> (\<lambda>(\<xi>, p). \<forall>l\<in>labels \<Gamma> p. P (\<xi>, l))"

lemma onlI [intro]:
  assumes "\<And>l. l\<in>labels \<Gamma> p \<Longrightarrow> P (\<xi>, l)"
    shows "onl \<Gamma> P (\<xi>, p)"
  using assms unfolding onl_def by simp

lemmas onlI' [intro] = onlI [simplified atomize_ball]

lemma onlD [dest]:
  assumes "onl \<Gamma> P (\<xi>, p)"
    shows "\<forall>l\<in>labels \<Gamma> p. P (\<xi>, l)"
  using assms unfolding onl_def by simp

lemma onl_invariantI [intro]:
  assumes init: "\<And>\<xi> p l. \<lbrakk> (\<xi>, p) \<in> init A; l \<in> labels \<Gamma> p \<rbrakk> \<Longrightarrow> P (\<xi>, l)"
      and step: "\<And>\<xi> p a \<xi>' p' l'.
                   \<lbrakk> (\<xi>, p) \<in> reachable A I;
                     \<forall>l\<in>labels \<Gamma> p. P (\<xi>, l);
                     ((\<xi>, p), a, (\<xi>', p')) \<in> trans A;
                     l' \<in> labels \<Gamma> p';
                     I a \<rbrakk> \<Longrightarrow> P (\<xi>', l')"
    shows "A \<TTurnstile> (I \<rightarrow>) onl \<Gamma> P"
  proof (rule invariant_pairI)
    fix \<xi> p
    assume "(\<xi>, p) \<in> init A"
    hence "\<forall>l\<in>labels \<Gamma> p. P (\<xi>, l)" using init by simp
    thus "onl \<Gamma> P (\<xi>, p)" ..
  next
    fix \<xi> p a \<xi>' p'
    assume rp: "(\<xi>, p) \<in> reachable A I"
       and "onl \<Gamma> P (\<xi>, p)"
       and tr: "((\<xi>, p), a, (\<xi>', p')) \<in> trans A"
       and "I a"
    from \<open>onl \<Gamma> P (\<xi>, p)\<close> have "\<forall>l\<in>labels \<Gamma> p. P (\<xi>, l)" ..
    with rp tr \<open>I a\<close> have "\<forall>l'\<in>labels \<Gamma> p'. P (\<xi>', l')" by (auto elim: step)
    thus "onl \<Gamma> P (\<xi>', p')" ..
  qed

lemma onl_invariantD [dest]:
  assumes "A \<TTurnstile> (I \<rightarrow>) onl \<Gamma> P"
      and "(\<xi>, p) \<in> reachable A I"
      and "l \<in> labels \<Gamma> p"
    shows "P (\<xi>, l)"
  using assms unfolding onl_def by auto

lemma onl_invariant_initD [dest]:
  assumes invP: "A \<TTurnstile> (I \<rightarrow>) onl \<Gamma> P"
      and init: "(\<xi>, p) \<in> init A"
      and pnl:  "l \<in> labels \<Gamma> p"
    shows "P (\<xi>, l)"
  proof -
    from init have "(\<xi>, p) \<in> reachable A I" ..
    with invP show ?thesis using pnl ..
  qed

lemma onl_invariant_sterms:
  assumes wf: "wellformed \<Gamma>"
      and il: "A \<TTurnstile> (I \<rightarrow>) onl \<Gamma> P"
      and rp: "(\<xi>, p) \<in> reachable A I"
      and "p'\<in>sterms \<Gamma> p"
      and "l\<in>labels \<Gamma> p'"
    shows "P (\<xi>, l)"
  proof -
    from wf \<open>p'\<in>sterms \<Gamma> p\<close> \<open>l\<in>labels \<Gamma> p'\<close> have "l\<in>labels \<Gamma> p"
      by (rule labels_sterms_labels)
    with il rp show "P (\<xi>, l)" ..
  qed

lemma onl_invariant_sterms_weaken:
  assumes wf: "wellformed \<Gamma>"
      and il: "A \<TTurnstile> (I \<rightarrow>) onl \<Gamma> P"
      and rp: "(\<xi>, p) \<in> reachable A I'"
      and "p'\<in>sterms \<Gamma> p"
      and "l\<in>labels \<Gamma> p'"
      and weaken: "\<And>a. I' a \<Longrightarrow> I a"
    shows "P (\<xi>, l)"
  proof -
    from \<open>(\<xi>, p) \<in> reachable A I'\<close> have "(\<xi>, p) \<in> reachable A I"
      by (rule reachable_weakenE)
         (erule weaken)
    with assms(1-2) show ?thesis using assms(4-5) by (rule onl_invariant_sterms)
  qed

lemma onl_invariant_sterms_TT:
  assumes wf: "wellformed \<Gamma>"
      and il: "A \<TTurnstile> onl \<Gamma> P"
      and rp: "(\<xi>, p) \<in> reachable A I"
      and "p'\<in>sterms \<Gamma> p"
      and "l\<in>labels \<Gamma> p'"
    shows "P (\<xi>, l)"
  using assms by (rule onl_invariant_sterms_weaken) simp

lemma trans_from_sterms:
  assumes "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
      and "wellformed \<Gamma>"
    shows "\<exists>p'\<in>sterms \<Gamma> p. ((\<xi>, p'), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
  using assms by (induction p rule: sterms_pinduct [OF \<open>wellformed \<Gamma>\<close>]) auto

lemma trans_from_sterms':
  assumes "((\<xi>, p'), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
      and "wellformed \<Gamma>"
      and "p' \<in> sterms \<Gamma> p"
    shows "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
  using assms by (induction p rule: sterms_pinduct [OF \<open>wellformed \<Gamma>\<close>]) auto

lemma trans_to_dterms:
  assumes "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
      and "wellformed \<Gamma>"
   shows "\<forall>r\<in>sterms \<Gamma> q. r \<in> dterms \<Gamma> p"
  using assms by (induction q) auto

theorem cterms_includes_sterms_of_seq_reachable:
  assumes "wellformed \<Gamma>"
      and "control_within \<Gamma> (init A)"
      and "trans A = seqp_sos \<Gamma>"
    shows "\<Union>(sterms \<Gamma> ` snd ` reachable A I) \<subseteq> cterms \<Gamma>"
  proof
    fix qs
    assume "qs \<in> \<Union>(sterms \<Gamma> ` snd ` reachable A I)"
    then obtain \<xi> and q where  *: "(\<xi>, q) \<in> reachable A I"
                          and **: "qs \<in> sterms \<Gamma> q" by auto
    from * have "\<And>x. x \<in> sterms \<Gamma> q \<Longrightarrow> x \<in> cterms \<Gamma>"
    proof (induction rule: reachable_pair_induct)
      fix \<xi> p q
      assume "(\<xi>, p) \<in> init A"
         and "q \<in> sterms \<Gamma> p"
      from \<open>control_within \<Gamma> (init A)\<close> and \<open>(\<xi>, p) \<in> init A\<close>
        obtain pn where "p \<in> subterms (\<Gamma> pn)" by auto
      with \<open>wellformed \<Gamma>\<close> show "q \<in> cterms \<Gamma>" using \<open>q\<in>sterms \<Gamma> p\<close>
        by (rule subterms_sterms_in_cterms)
    next
      fix p \<xi> a \<xi>' q x
      assume "(\<xi>, p) \<in> reachable A I"
         and IH: "\<And>x. x \<in> sterms \<Gamma> p \<Longrightarrow> x \<in> cterms \<Gamma>"
         and "((\<xi>, p), a, (\<xi>', q)) \<in> trans A"
         and "x \<in> sterms \<Gamma> q"
      from this(3) and \<open>trans A = seqp_sos \<Gamma>\<close> have "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>" by simp
      from this and \<open>wellformed \<Gamma>\<close> obtain ps
        where ps: "ps \<in> sterms \<Gamma> p"
          and step: "((\<xi>, ps), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
        by (rule trans_from_sterms [THEN bexE])
      from ps have "ps \<in> cterms \<Gamma>" by (rule IH)
      moreover from step \<open>wellformed \<Gamma>\<close> \<open>x \<in> sterms \<Gamma> q\<close> have "x \<in> dterms \<Gamma> ps"
        by (rule trans_to_dterms [rule_format])
      ultimately show "x \<in> cterms \<Gamma>" by (rule ctermsDI)
    qed
    thus "qs \<in> cterms \<Gamma>" using ** .
  qed

corollary seq_reachable_in_cterms:
  assumes "wellformed \<Gamma>"
      and "control_within \<Gamma> (init A)"
      and "trans A = seqp_sos \<Gamma>"
      and "(\<xi>, p) \<in> reachable A I"
      and "p' \<in> sterms \<Gamma> p"
    shows "p' \<in> cterms \<Gamma>"
  using assms(1-3)
  proof (rule cterms_includes_sterms_of_seq_reachable [THEN subsetD])
    from assms(4-5) show "p' \<in> \<Union>(sterms \<Gamma> ` snd ` reachable A I)"
      by (auto elim!: rev_bexI)
  qed

lemma seq_invariant_ctermI:
  assumes wf: "wellformed \<Gamma>"
      and cw: "control_within \<Gamma> (init A)"
      and sl: "simple_labels \<Gamma>"
      and sp: "trans A = seqp_sos \<Gamma>"
      and init: "\<And>\<xi> p l. \<lbrakk>
                   (\<xi>, p) \<in> init A;
                   l\<in>labels \<Gamma> p
                 \<rbrakk> \<Longrightarrow> P (\<xi>, l)"
      and step: "\<And>p l \<xi> a q l' \<xi>' pp. \<lbrakk>
                 p\<in>cterms \<Gamma>;
                 l\<in>labels \<Gamma> p;
                 P (\<xi>, l);
                 ((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>;
                 ((\<xi>, p), a, (\<xi>', q)) \<in> trans A;
                 l'\<in>labels \<Gamma> q;
                 (\<xi>, pp)\<in>reachable A I;
                 p\<in>sterms \<Gamma> pp;
                 (\<xi>', q)\<in>reachable A I;
                 I a
               \<rbrakk> \<Longrightarrow> P (\<xi>', l')"
    shows "A \<TTurnstile> (I \<rightarrow>) onl \<Gamma> P"
  proof
       fix \<xi> p l
    assume "(\<xi>, p) \<in> init A"
       and *: "l \<in> labels \<Gamma> p"
      with init show "P (\<xi>, l)" by auto
  next
       fix \<xi> p a \<xi>' q l'
    assume sr: "(\<xi>, p) \<in> reachable A I"
       and pl: "\<forall>l\<in>labels \<Gamma> p. P (\<xi>, l)"
       and tr: "((\<xi>, p), a, (\<xi>', q)) \<in> trans A"
       and A6: "l' \<in> labels \<Gamma> q"
       and "I a"
     from this(3) and \<open>trans A = seqp_sos \<Gamma>\<close> have tr': "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>" by simp
     show "P (\<xi>', l')"
    proof -
      from sr and tr and \<open>I a\<close> have A7: "(\<xi>', q) \<in> reachable A I" ..
      from tr' obtain p' where "p' \<in> sterms \<Gamma> p"
                           and "((\<xi>, p'), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
        by (blast dest: trans_from_sterms [OF _ wf])
      from wf cw sp sr this(1) have A1: "p'\<in>cterms \<Gamma>"
        by (rule seq_reachable_in_cterms)
      from labels_not_empty [OF wf] obtain ll where A2: "ll\<in>labels \<Gamma> p'"
          by blast
      with \<open>p'\<in>sterms \<Gamma> p\<close> have "ll\<in>labels \<Gamma> p"
        by (rule labels_sterms_labels [OF wf])
      with pl have A3: "P (\<xi>, ll)" by simp
      from \<open>((\<xi>, p'), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>\<close> and sp
        have A5: "((\<xi>, p'), a, (\<xi>', q)) \<in> trans A" by simp
      with sp have A4: "((\<xi>, p'), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>" by simp
      from sr \<open>p'\<in>sterms \<Gamma> p\<close>
        obtain pp where A7: "(\<xi>, pp)\<in>reachable A I"
                    and A8: "p'\<in>sterms \<Gamma> pp"
        by auto
      from sr tr \<open>I a\<close> have A9: "(\<xi>', q) \<in> reachable A I" ..
      from A1 A2 A3 A4 A5 A6 A7 A8 A9 \<open>I a\<close> show ?thesis by (rule step)
    qed
  qed

lemma seq_invariant_ctermsI:
  assumes wf: "wellformed \<Gamma>"
      and "control_within \<Gamma> (init A)"
      and "simple_labels \<Gamma>"
      and "trans A = seqp_sos \<Gamma>"
      and init: "\<And>\<xi> p l. \<lbrakk>
                   (\<xi>, p) \<in> init A;
                   l\<in>labels \<Gamma> p
                 \<rbrakk> \<Longrightarrow> P (\<xi>, l)"
      and step: "\<And>p l \<xi> a q l' \<xi>' pp pn. \<lbrakk>
                 wellformed \<Gamma>;
                 p\<in>ctermsl (\<Gamma> pn);
                 not_call p;
                 l\<in>labels \<Gamma> p;
                 P (\<xi>, l);
                 ((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>;
                 ((\<xi>, p), a, (\<xi>', q)) \<in> trans A;
                 l'\<in>labels \<Gamma> q;
                 (\<xi>, pp)\<in>reachable A I;
                 p\<in>sterms \<Gamma> pp;
                 (\<xi>', q)\<in>reachable A I;
                 I a
               \<rbrakk> \<Longrightarrow> P (\<xi>', l')"
    shows "A \<TTurnstile> (I \<rightarrow>) onl \<Gamma> P"
  using assms(1-4) proof (rule seq_invariant_ctermI)
    fix \<xi> p l
    assume "(\<xi>, p) \<in> init A"
       and "l \<in> labels \<Gamma> p"
    thus "P (\<xi>, l)" by (rule init)
  next
    fix p l \<xi> a q l' \<xi>' pp
    assume "p \<in> cterms \<Gamma>"
       and otherassms: "l \<in> labels \<Gamma> p"
           "P (\<xi>, l)"
           "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
           "((\<xi>, p), a, (\<xi>', q)) \<in> trans A"
           "l' \<in> labels \<Gamma> q"
           "(\<xi>, pp) \<in> reachable A I"
           "p \<in> sterms \<Gamma> pp"
           "(\<xi>', q) \<in> reachable A I"
           "I a"
    from this(1) obtain pn where "p \<in> ctermsl(\<Gamma> pn)"
                             and "not_call p"
      unfolding cterms_def' [OF wf] by auto
    with wf show "P (\<xi>', l')"
      using otherassms by (rule step)
  qed

subsection "Step invariants via labelled control terms"

definition
  onll :: "('s, 'm, 'p, 'l) seqp_env
           \<Rightarrow> (('z \<times> 'l, 'a) transition \<Rightarrow> bool)
           \<Rightarrow> ('z \<times> ('s, 'm, 'p, 'l) seqp, 'a) transition \<Rightarrow> bool"
where
  "onll \<Gamma> P \<equiv> (\<lambda>((\<xi>, p), a, (\<xi>', p')). \<forall>l\<in>labels \<Gamma> p. \<forall>l'\<in>labels \<Gamma> p'. P ((\<xi>, l), a, (\<xi>', l')))"

lemma onllI [intro]:
  assumes "\<And>l l'. \<lbrakk> l\<in>labels \<Gamma> p; l'\<in>labels \<Gamma> p' \<rbrakk> \<Longrightarrow> P ((\<xi>, l), a, (\<xi>', l'))"
    shows "onll \<Gamma> P ((\<xi>, p), a, (\<xi>', p'))"
  using assms unfolding onll_def by simp

lemma onllIl [intro]:
  assumes "\<forall>l\<in>labels \<Gamma> p. \<forall>l'\<in>labels \<Gamma> p'. P ((\<xi>, l), a, (\<xi>', l'))"
    shows "onll \<Gamma> P ((\<xi>, p), a, (\<xi>', p'))"
  using assms by auto

lemma onllD [dest]:
  assumes "onll \<Gamma> P ((\<xi>, p), a, (\<xi>', p'))"
    shows "\<forall>l\<in>labels \<Gamma> p. \<forall>l'\<in>labels \<Gamma> p'. P ((\<xi>, l), a, (\<xi>', l'))"
  using assms unfolding onll_def by simp

lemma onl_weaken [elim!]: "\<And>\<Gamma> P Q s. \<lbrakk> onl \<Gamma> P s; \<And>s. P s \<Longrightarrow> Q s \<rbrakk> \<Longrightarrow> onl \<Gamma> Q s"
  by (clarsimp dest!: onlD intro!: onlI)

lemma onll_weaken [elim!]: "\<And>\<Gamma> P Q s. \<lbrakk> onll \<Gamma> P s; \<And>s. P s \<Longrightarrow> Q s \<rbrakk> \<Longrightarrow> onll \<Gamma> Q s"
  by (clarsimp dest!: onllD intro!: onllI)

lemma onll_weaken' [elim!]: "\<And>\<Gamma> P Q s. \<lbrakk> onll \<Gamma> P ((\<xi>, p), a, (\<xi>', p'));
                                        \<And>l l'. P ((\<xi>, l), a, (\<xi>', l')) \<Longrightarrow> Q ((\<xi>, l), a, (\<xi>', l')) \<rbrakk>
                                      \<Longrightarrow> onll \<Gamma> Q ((\<xi>, p), a, (\<xi>', p'))"
  by (clarsimp dest!: onllD intro!: onllI)

lemma onll_step_invariantI [intro]:
  assumes *: "\<And>\<xi> p l a \<xi>' p' l'. \<lbrakk> (\<xi>, p)\<in>reachable A I;
                                   ((\<xi>, p), a, (\<xi>', p')) \<in> trans A;
                                   I a;
                                   l \<in>labels \<Gamma> p;
                                   l'\<in>labels \<Gamma> p' \<rbrakk>
                                 \<Longrightarrow> P ((\<xi>, l), a, (\<xi>', l'))"
    shows "A \<TTurnstile>\<^sub>A (I \<rightarrow>) onll \<Gamma> P"
  proof
    fix \<xi> p \<xi>' p' a
    assume "(\<xi>, p) \<in> reachable A I"
       and "((\<xi>, p), a, (\<xi>', p')) \<in> trans A"
       and "I a"
    hence "\<forall>l\<in>labels \<Gamma> p. \<forall>l'\<in>labels \<Gamma> p'. P ((\<xi>, l), a, (\<xi>', l'))" by (auto elim!: *)
    thus "onll \<Gamma> P ((\<xi>, p), a, (\<xi>', p'))" ..
  qed

lemma onll_step_invariantE [elim]:
  assumes "A \<TTurnstile>\<^sub>A (I \<rightarrow>) onll \<Gamma> P"
      and "(\<xi>, p) \<in> reachable A I"
      and "((\<xi>, p), a, (\<xi>', p')) \<in> trans A"
      and "I a"
      and lp:  "l \<in>labels \<Gamma> p"
      and lp': "l'\<in>labels \<Gamma> p'"
    shows "P ((\<xi>, l), a, (\<xi>', l'))"
  proof -
    from assms(1-4) have "onll \<Gamma> P ((\<xi>, p), a, (\<xi>', p'))" ..
    with lp lp' show "P ((\<xi>, l), a, (\<xi>', l'))" by auto
  qed

lemma onll_step_invariantD [dest]:
  assumes "A \<TTurnstile>\<^sub>A (I \<rightarrow>) onll \<Gamma> P"
      and "(\<xi>, p) \<in> reachable A I"
      and "((\<xi>, p), a, (\<xi>', p')) \<in> trans A"
      and "I a"
    shows "\<forall>l\<in>labels \<Gamma> p. \<forall>l'\<in>labels \<Gamma> p'. P ((\<xi>, l), a, (\<xi>', l'))"
  using assms by auto

lemma onll_step_to_invariantI [intro]:
  assumes sinv: "A \<TTurnstile>\<^sub>A (I \<rightarrow>) onll \<Gamma> Q"
      and wf: "wellformed \<Gamma>"
      and init: "\<And>\<xi> l p. \<lbrakk> (\<xi>, p) \<in> init A; l\<in>labels \<Gamma> p \<rbrakk> \<Longrightarrow> P (\<xi>, l)"
      and step: "\<And>\<xi> p l \<xi>' l' a.
                   \<lbrakk> (\<xi>, p) \<in> reachable A I;
                     l\<in>labels \<Gamma> p;
                     P (\<xi>, l);
                     Q ((\<xi>, l), a, (\<xi>', l'));
                     I a\<rbrakk> \<Longrightarrow> P (\<xi>', l')"
    shows "A \<TTurnstile> (I \<rightarrow>) onl \<Gamma> P"
  proof
    fix \<xi> p l
    assume "(\<xi>, p) \<in> init A" and "l\<in>labels \<Gamma> p"
      thus "P (\<xi>, l)" by (rule init)
  next
    fix \<xi> p a \<xi>' p' l'
    assume sr: "(\<xi>, p) \<in> reachable A I"
       and lp: "\<forall>l\<in>labels \<Gamma> p. P (\<xi>, l)"
       and tr: "((\<xi>, p), a, (\<xi>', p')) \<in> trans A"
       and "I a"
       and lp': "l' \<in> labels \<Gamma> p'"
      show "P (\<xi>', l')"
    proof -
      from lp obtain l where "l\<in>labels \<Gamma> p" and "P (\<xi>, l)"
        using labels_not_empty [OF wf] by auto
      from sinv sr tr \<open>I a\<close> this(1) lp' have "Q ((\<xi>, l), a, (\<xi>', l'))" ..
      with sr \<open>l\<in>labels \<Gamma> p\<close> \<open>P (\<xi>, l)\<close> show "P (\<xi>', l')" using \<open>I a\<close> by (rule step)
    qed
  qed

lemma onll_step_invariant_sterms:
  assumes wf: "wellformed \<Gamma>"
      and si: "A \<TTurnstile>\<^sub>A (I \<rightarrow>) onll \<Gamma> P"
      and sr: "(\<xi>, p) \<in> reachable A I"
      and sos: "((\<xi>, p), a, (\<xi>', q)) \<in> trans A"
      and "I a"
      and "l'\<in>labels \<Gamma> q"
      and "p'\<in>sterms \<Gamma> p"
      and "l\<in>labels \<Gamma> p'"
    shows "P ((\<xi>, l), a, (\<xi>', l'))"
  proof -
    from wf \<open>p'\<in>sterms \<Gamma> p\<close> \<open>l\<in>labels \<Gamma> p'\<close> have "l\<in>labels \<Gamma> p"
      by (rule labels_sterms_labels)
    with si sr sos \<open>I a\<close> show "P ((\<xi>, l), a, (\<xi>', l'))" using \<open>l'\<in>labels \<Gamma> q\<close> ..
  qed

lemma seq_step_invariant_sterms:
  assumes inv: "A \<TTurnstile>\<^sub>A (I \<rightarrow>) onll \<Gamma> P"
      and wf: "wellformed \<Gamma>"
      and sp: "trans A = seqp_sos \<Gamma>"
      and "l'\<in>labels \<Gamma> q"
      and sr: "(\<xi>, p) \<in> reachable A I"
      and tr: "((\<xi>, p'), a, (\<xi>', q)) \<in> trans A"
      and "I a"
      and "p'\<in>sterms \<Gamma> p"
    shows "\<forall>l\<in>labels \<Gamma> p'. P ((\<xi>, l), a, (\<xi>', l'))"
  proof
    from tr and sp have "((\<xi>, p'), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>" by simp
    hence "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
      using wf \<open>p'\<in>sterms \<Gamma> p\<close> by  (rule trans_from_sterms')
    with sp have trp: "((\<xi>, p), a, (\<xi>', q)) \<in> trans A" by simp
    fix l assume "l \<in> labels \<Gamma> p'"
    with wf inv sr trp \<open>I a\<close> \<open>l'\<in>labels \<Gamma> q\<close> \<open>p'\<in>sterms \<Gamma> p\<close>
      show "P ((\<xi>, l), a, (\<xi>', l'))" by (rule onll_step_invariant_sterms)
  qed

lemma seq_step_invariant_sterms_weaken:
  assumes "A \<TTurnstile>\<^sub>A (I \<rightarrow>) onll \<Gamma> P"
      and "wellformed \<Gamma>"
      and "trans A = seqp_sos \<Gamma>"
      and "l'\<in>labels \<Gamma> q"
      and "(\<xi>, p) \<in> reachable A I'"
      and "((\<xi>, p'), a, (\<xi>', q)) \<in> trans A"
      and "I' a"
      and "p'\<in>sterms \<Gamma> p"
      and weaken: "\<And>a. I' a \<Longrightarrow> I a"
    shows "\<forall>l\<in>labels \<Gamma> p'. P ((\<xi>, l), a, (\<xi>', l'))"
  proof -
    from \<open>I' a\<close> have "I a" by (rule weaken)
    from \<open>(\<xi>, p) \<in> reachable A I'\<close> have Ir: "(\<xi>, p) \<in> reachable A I"
        by (rule reachable_weakenE) (erule weaken)
    with assms(1-4) show ?thesis
      using \<open>((\<xi>, p'), a, (\<xi>', q)) \<in> trans A\<close> \<open>I a\<close> and \<open>p'\<in>sterms \<Gamma> p\<close>
      by (rule seq_step_invariant_sterms)
  qed

lemma seq_step_invariant_sterms_TT:
  assumes "A \<TTurnstile>\<^sub>A onll \<Gamma> P"
      and "wellformed \<Gamma>"
      and "trans A = seqp_sos \<Gamma>"
      and "l'\<in>labels \<Gamma> q"
      and "(\<xi>, p) \<in> reachable A I"
      and "((\<xi>, p'), a, (\<xi>', q)) \<in> trans A"
      and "I a"
      and "p'\<in>sterms \<Gamma> p"
    shows "\<forall>l\<in>labels \<Gamma> p'. P ((\<xi>, l), a, (\<xi>', l'))"
  using assms by (rule seq_step_invariant_sterms_weaken) simp

lemma onll_step_invariant_any_sterms:
  assumes "wellformed \<Gamma>"
      and "A \<TTurnstile>\<^sub>A (I \<rightarrow>) onll \<Gamma> P"
      and "(\<xi>, p) \<in> reachable A I"
      and "((\<xi>, p), a, (\<xi>', q)) \<in> trans A"
      and "I a"
      and "l'\<in>labels \<Gamma> q"
    shows "\<forall>p'\<in>sterms \<Gamma> p. \<forall>l\<in>labels \<Gamma> p'. P ((\<xi>, l), a, (\<xi>', l'))"
  by (intro ballI) (rule onll_step_invariant_sterms [OF assms])

lemma seq_step_invariant_ctermI [intro]:
  assumes wf: "wellformed \<Gamma>"
      and cw: "control_within \<Gamma> (init A)"
      and sl: "simple_labels \<Gamma>"
      and sp: "trans A = seqp_sos \<Gamma>"
      and step: "\<And>p pp l \<xi> a q l' \<xi>'. \<lbrakk>
                 p\<in>cterms \<Gamma>;
                 l\<in>labels \<Gamma> p;
                 ((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>;
                 ((\<xi>, p), a, (\<xi>', q)) \<in> trans A;
                 l'\<in>labels \<Gamma> q;
                 (\<xi>, pp) \<in> reachable A I;
                 p\<in>sterms \<Gamma> pp;
                 (\<xi>', q) \<in> reachable A I;
                 I a
               \<rbrakk> \<Longrightarrow> P ((\<xi>, l), a, (\<xi>', l'))"
    shows "A \<TTurnstile>\<^sub>A (I \<rightarrow>) onll \<Gamma> P"
  proof
       fix \<xi> p l a \<xi>' q l'
    assume sr: "(\<xi>, p) \<in> reachable A I"
       and tr: "((\<xi>, p), a, (\<xi>', q)) \<in> trans A"
       and "I a"
       and pl: "l \<in> labels \<Gamma> p"
       and A5: "l' \<in> labels \<Gamma> q"
    from this(2) and sp have tr': "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>" by simp
    then obtain p' where "p' \<in> sterms \<Gamma> p"
                     and A3: "((\<xi>, p'), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
      by (blast dest: trans_from_sterms [OF _ wf])
    from wf cw sp sr this(1) have A1: "p'\<in>cterms \<Gamma>"
      by (rule seq_reachable_in_cterms)
    from \<open>((\<xi>, p'), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>\<close> and sp
      have A4: "((\<xi>, p'), a, (\<xi>', q)) \<in> trans A" by simp
    from sr \<open>p'\<in>sterms \<Gamma> p\<close> obtain pp where A6: "(\<xi>, pp)\<in>reachable A I"
                                        and A7: "p'\<in>sterms \<Gamma> pp"
      by auto
    from sr tr \<open>I a\<close> have A8: "(\<xi>', q)\<in>reachable A I" ..
    from wf cw sp sr have "\<exists>pn. p \<in> subterms (\<Gamma> pn)"
      by (rule reachable_subterms)
    with sl wf have "\<forall>p'\<in>sterms \<Gamma> p. l \<in> labels \<Gamma> p'"
      using pl by (rule simple_labels_in_sterms)
    with \<open>p' \<in> sterms \<Gamma> p\<close> have "l \<in> labels \<Gamma> p'" by simp
    with A1 show "P ((\<xi>, l), a, (\<xi>', l'))" using A3 A4 A5 A6 A7 A8 \<open>I a\<close>
      by (rule step)
  qed

lemma seq_step_invariant_ctermsI [intro]:
  assumes wf: "wellformed \<Gamma>"
      and cw: "control_within \<Gamma> (init A)"
      and sl: "simple_labels \<Gamma>"
      and sp: "trans A = seqp_sos \<Gamma>"
      and step: "\<And>p l \<xi> a q l' \<xi>' pp pn. \<lbrakk>
                 wellformed \<Gamma>;
                 p\<in>ctermsl (\<Gamma> pn);
                 not_call p;
                 l\<in>labels \<Gamma> p;
                 ((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>;
                 ((\<xi>, p), a, (\<xi>', q)) \<in> trans A;
                 l'\<in>labels \<Gamma> q;
                 (\<xi>, pp) \<in> reachable A I;
                 p\<in>sterms \<Gamma> pp;
                 (\<xi>', q) \<in> reachable A I;
                 I a
               \<rbrakk> \<Longrightarrow> P ((\<xi>, l), a, (\<xi>', l'))"
    shows "A \<TTurnstile>\<^sub>A (I \<rightarrow>) onll \<Gamma> P"
  using assms(1-4) proof (rule seq_step_invariant_ctermI)
    fix p pp l \<xi> a q l' \<xi>'
    assume "p \<in> cterms \<Gamma>"
       and otherassms: "l \<in> labels \<Gamma> p"
           "((\<xi>, p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
           "((\<xi>, p), a, (\<xi>', q)) \<in> trans A"
           "l' \<in> labels \<Gamma> q"
           "(\<xi>, pp) \<in> reachable A I"
           "p \<in> sterms \<Gamma> pp"
           "(\<xi>', q) \<in> reachable A I"
           "I a"
    from this(1) obtain pn where "p \<in> ctermsl(\<Gamma> pn)"
                             and "not_call p"
      unfolding cterms_def' [OF wf] by auto
    with wf show "P ((\<xi>, l), a, (\<xi>', l'))"
      using otherassms by (rule step)
  qed

end

