(*  Title:       OAWN_Convert.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Transfer standard invariants into open invariants"

theory OAWN_Convert
imports AWN_SOS_Labels AWN_Invariants
        OAWN_SOS OAWN_Invariants
begin

definition initiali :: "'i \<Rightarrow> (('i \<Rightarrow> 'g) \<times> 'l) set \<Rightarrow> ('g \<times> 'l) set \<Rightarrow> bool"
where "initiali i OI CI \<equiv> ({(\<sigma> i, p)|\<sigma> p. (\<sigma>, p) \<in> OI} = CI)"

lemma initialiI [intro]:
  assumes OICI: "\<And>\<sigma> p. (\<sigma>, p) \<in> OI \<Longrightarrow> (\<sigma> i, p) \<in> CI"
      and CIOI: "\<And>\<xi> p. (\<xi>, p) \<in> CI \<Longrightarrow> \<exists>\<sigma>. \<xi> = \<sigma> i \<and> (\<sigma>, p) \<in> OI"
    shows "initiali i OI CI"
  unfolding initiali_def
  by (intro set_eqI iffI) (auto elim!: OICI CIOI)

lemma open_from_initialiD [dest]:
  assumes "initiali i OI CI"
      and "(\<sigma>, p) \<in> OI"
    shows "\<exists>\<xi>. \<sigma> i = \<xi> \<and> (\<xi>, p) \<in> CI"
  using assms unfolding initiali_def by auto

lemma closed_from_initialiD [dest]:
  assumes "initiali i OI CI"
      and "(\<xi>, p) \<in> CI"
    shows "\<exists>\<sigma>. \<sigma> i = \<xi> \<and> (\<sigma>, p) \<in> OI"
  using assms unfolding initiali_def by auto

definition
  seql :: "'i \<Rightarrow> (('s \<times> 'l) \<Rightarrow> bool) \<Rightarrow> (('i \<Rightarrow> 's) \<times> 'l) \<Rightarrow> bool"
where
  "seql i P \<equiv> (\<lambda>(\<sigma>, p). P (\<sigma> i, p))"

lemma seqlI [intro]:
  "P (fst s i, snd s) \<Longrightarrow> seql i P s"
  by (clarsimp simp: seql_def)

lemma same_seql [elim]:
  assumes "\<forall>j\<in>{i}. \<sigma>' j = \<sigma> j"
      and "seql i P (\<sigma>', s)"
    shows "seql i P (\<sigma>, s)"
  using assms unfolding seql_def by (clarsimp)

lemma seqlsimp:
  "seql i P (\<sigma>, p) = P (\<sigma> i, p)"
  unfolding seql_def by simp

lemma other_steps_resp_local [intro!, simp]: "other_steps (other A I) I"
  by (clarsimp elim!: otherE)

lemma seql_onl_swap:
  "seql i (onl \<Gamma> P) = onl \<Gamma> (seql i P)"
  unfolding seql_def onl_def by simp

lemma oseqp_sos_resp_local_steps [intro!, simp]:
  fixes \<Gamma> :: "'p \<Rightarrow> ('s, 'm, 'p, 'l) seqp"
  shows "local_steps (oseqp_sos \<Gamma> i) {i}"
  proof
    fix \<sigma> \<sigma>' \<zeta> \<zeta>' :: "nat \<Rightarrow> 's" and s a s'
    assume tr: "((\<sigma>, s), a, \<sigma>', s') \<in> oseqp_sos \<Gamma> i"
       and "\<forall>j\<in>{i}. \<zeta> j = \<sigma> j"
    thus "\<exists>\<zeta>'. (\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j) \<and> ((\<zeta>, s), a, (\<zeta>', s')) \<in> oseqp_sos \<Gamma> i"
    proof induction
      fix \<sigma> \<sigma>' l ms p
      assume "\<sigma>' i = \<sigma> i"
         and "\<forall>j\<in>{i}. \<zeta> j = \<sigma> j"
      hence "((\<zeta>, {l}broadcast(ms).p), broadcast (ms (\<sigma> i)), (\<sigma>', p)) \<in> oseqp_sos \<Gamma> i"
        by (metis obroadcastT singleton_iff)
      with \<open>\<forall>j\<in>{i}. \<zeta> j = \<sigma> j\<close> show "\<exists>\<zeta>'. (\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j) \<and>
            ((\<zeta>, {l}broadcast(ms).p), broadcast (ms (\<sigma> i)), (\<zeta>', p)) \<in> oseqp_sos \<Gamma> i"
        by blast
    next
      fix \<sigma> \<sigma>' :: "nat \<Rightarrow> 's" and fmsg :: "'m \<Rightarrow> 's \<Rightarrow> 's" and msg l p
      assume *:  "\<sigma>' i = fmsg msg (\<sigma> i)"
         and **: "\<forall>j\<in>{i}. \<zeta> j = \<sigma> j"
      hence "\<forall>j\<in>{i}. (\<zeta>(i := fmsg msg (\<zeta> i))) j = \<sigma>' j" by clarsimp
      moreover from * **
        have "((\<zeta>, {l}receive(fmsg).p), receive msg, (\<zeta>(i := fmsg msg (\<zeta> i)), p)) \<in> oseqp_sos \<Gamma> i"
        by (metis fun_upd_same oreceiveT)
      ultimately show "\<exists>\<zeta>'. (\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j) \<and>
                            ((\<zeta>, {l}receive(fmsg).p), receive msg, (\<zeta>', p)) \<in> oseqp_sos \<Gamma> i"
        by blast
    next
      fix \<sigma>' \<sigma> l p and fas :: "'s \<Rightarrow> 's"
      assume *:  "\<sigma>' i = fas (\<sigma> i)"
         and **: "\<forall>j\<in>{i}. \<zeta> j = \<sigma> j"
      hence "\<forall>j\<in>{i}. (\<zeta>(i := fas (\<zeta> i))) j = \<sigma>' j" by clarsimp
      moreover from * ** have "((\<zeta>, {l}\<lbrakk>fas\<rbrakk> p), \<tau>, (\<zeta>(i := fas (\<zeta> i)), p)) \<in> oseqp_sos \<Gamma> i"
        by (metis fun_upd_same oassignT)
      ultimately show "\<exists>\<zeta>'. (\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j) \<and> ((\<zeta>, {l}\<lbrakk>fas\<rbrakk> p), \<tau>, (\<zeta>', p)) \<in> oseqp_sos \<Gamma> i"
        by blast
    next
      fix g :: "'s \<Rightarrow> 's set" and \<sigma> \<sigma>' l p
      assume *:  "\<sigma>' i \<in> g (\<sigma> i)"
         and **: "\<forall>j\<in>{i}. \<zeta> j = \<sigma> j"
      hence "\<forall>j\<in>{i}. (SOME \<zeta>'. \<zeta>' i = \<sigma>' i) j = \<sigma>' j" by simp (metis (lifting, full_types) some_eq_ex)
      moreover with * ** have "((\<zeta>, {l}\<langle>g\<rangle> p), \<tau>, (SOME \<zeta>'. \<zeta>' i = \<sigma>' i, p)) \<in> oseqp_sos \<Gamma> i"
        by simp (metis oguardT step_seq_tau)
      ultimately show "\<exists>\<zeta>'. (\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j) \<and> ((\<zeta>, {l}\<langle>g\<rangle> p), \<tau>, (\<zeta>', p)) \<in> oseqp_sos \<Gamma> i"
        by blast
    next
      fix \<sigma> pn a \<sigma>' p'
      assume "((\<sigma>, \<Gamma> pn), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
         and IH: "\<forall>j\<in>{i}. \<zeta> j = \<sigma> j \<Longrightarrow> \<exists>\<zeta>'. (\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j) \<and> ((\<zeta>, \<Gamma> pn), a, (\<zeta>', p')) \<in> oseqp_sos \<Gamma> i"
         and "\<forall>j\<in>{i}. \<zeta> j = \<sigma> j"
      then obtain \<zeta>' where "\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j"
                       and "((\<zeta>, \<Gamma> pn), a, (\<zeta>', p')) \<in> oseqp_sos \<Gamma> i"
        by blast
      thus "\<exists>\<zeta>'. (\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j) \<and> ((\<zeta>, call(pn)), a, (\<zeta>', p')) \<in> oseqp_sos \<Gamma> i"
        by blast
    next
      fix \<sigma> p a \<sigma>' p' q
      assume "((\<sigma>, p), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
         and "\<forall>j\<in>{i}. \<zeta> j = \<sigma> j \<Longrightarrow> \<exists>\<zeta>'. (\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j) \<and> ((\<zeta>, p), a, (\<zeta>', p')) \<in> oseqp_sos \<Gamma> i"
         and "\<forall>j\<in>{i}. \<zeta> j = \<sigma> j"
      then obtain \<zeta>' where "\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j"
                       and "((\<zeta>, p), a, (\<zeta>', p')) \<in> oseqp_sos \<Gamma> i"
        by blast
      thus "\<exists>\<zeta>'. (\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j) \<and> ((\<zeta>, p \<oplus> q), a, (\<zeta>', p')) \<in> oseqp_sos \<Gamma> i"
        by blast
    next
      fix \<sigma> p a \<sigma>' q q'
      assume "((\<sigma>, q), a, (\<sigma>', q')) \<in> oseqp_sos \<Gamma> i"
         and "\<forall>j\<in>{i}. \<zeta> j = \<sigma> j \<Longrightarrow> \<exists>\<zeta>'. (\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j) \<and> ((\<zeta>, q), a, (\<zeta>', q')) \<in> oseqp_sos \<Gamma> i"
         and "\<forall>j\<in>{i}. \<zeta> j = \<sigma> j"
      then obtain \<zeta>' where "\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j"
                       and "((\<zeta>, q), a, (\<zeta>', q')) \<in> oseqp_sos \<Gamma> i"
        by blast
      thus "\<exists>\<zeta>'. (\<forall>j\<in>{i}. \<zeta>' j = \<sigma>' j) \<and> ((\<zeta>, p \<oplus> q), a, (\<zeta>', q')) \<in> oseqp_sos \<Gamma> i"
        by blast
    qed (simp_all, (metis ogroupcastT ounicastT onotunicastT osendT odeliverT)+)
  qed

lemma oseqp_sos_subreachable [intro!, simp]:
  assumes "trans OA = oseqp_sos \<Gamma> i"
    shows "subreachable OA (other ANY {i}) {i}"
  by rule (clarsimp simp add: assms(1))+

lemma oseq_step_is_seq_step:
    fixes \<sigma> :: "ip \<Rightarrow> 's"
  assumes "((\<sigma>, p), a :: 'm seq_action, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
      and "\<sigma> i = \<xi>"
    shows "\<exists>\<xi>'. \<sigma>' i = \<xi>' \<and> ((\<xi>, p), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>"
  using assms proof induction
    fix \<sigma> \<sigma>' l ms p
    assume "\<sigma>' i = \<sigma> i"
       and "\<sigma> i = \<xi>"
    hence "\<sigma>' i = \<xi>" by simp
    have "((\<xi>, {l}broadcast(ms).p), broadcast (ms \<xi>), (\<xi>, p)) \<in> seqp_sos \<Gamma>"
      by auto
    with \<open>\<sigma> i = \<xi>\<close> and \<open>\<sigma>' i = \<xi>\<close> show "\<exists>\<xi>'. \<sigma>' i = \<xi>'
             \<and> ((\<xi>, {l}broadcast(ms).p), broadcast (ms (\<sigma> i)), (\<xi>', p)) \<in> seqp_sos \<Gamma>"
       by clarsimp
  next
    fix fmsg :: "'m \<Rightarrow> 's \<Rightarrow> 's" and msg :: 'm and \<sigma>' \<sigma> l p
    assume "\<sigma>' i = fmsg msg (\<sigma> i)"
       and "\<sigma> i = \<xi>"
    have "((\<xi>, {l}receive(fmsg).p), receive msg, (fmsg msg \<xi>, p)) \<in> seqp_sos \<Gamma>"
      by auto
    with \<open>\<sigma>' i = fmsg msg (\<sigma> i)\<close> and \<open>\<sigma> i = \<xi>\<close>
      show "\<exists>\<xi>'. \<sigma>' i = \<xi>' \<and> ((\<xi>, {l}receive(fmsg).p), receive msg, (\<xi>', p)) \<in> seqp_sos \<Gamma>"
         by clarsimp
  qed (simp_all, (metis assignT choiceT1 choiceT2 groupcastT guardT
                        callT unicastT notunicastT sendT deliverT step_seq_tau)+)

lemma reachable_oseq_seqp_sos:
  assumes "(\<sigma>, p) \<in> reachable OA I"
      and "initiali i (init OA) (init A)"
      and spo: "trans OA = oseqp_sos \<Gamma> i"
      and sp: "trans A = seqp_sos \<Gamma>"
      shows "\<exists>\<xi>. \<sigma> i = \<xi> \<and> (\<xi>, p) \<in> reachable A I"
  using assms(1) proof (induction rule: reachable_pair_induct)
    fix \<sigma> p
    assume "(\<sigma>, p) \<in> init OA"
    with \<open>initiali i (init OA) (init A)\<close> obtain \<xi> where "\<sigma> i = \<xi>"
                                                    and "(\<xi>, p) \<in> init A"
      by auto
    from \<open>(\<xi>, p) \<in> init A\<close> have "(\<xi>, p) \<in> reachable A I" ..
    with \<open>\<sigma> i = \<xi>\<close> show "\<exists>\<xi>. \<sigma> i = \<xi> \<and> (\<xi>, p) \<in> reachable A I"
      by auto
  next
    fix \<sigma> p \<sigma>' p' a
    assume "(\<sigma>, p) \<in> reachable OA I"
       and IH: "\<exists>\<xi>. \<sigma> i = \<xi> \<and> (\<xi>, p) \<in> reachable A I"
       and otr: "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans OA"
       and "I a"
    from IH obtain \<xi> where "\<sigma> i = \<xi>"
                       and cr: "(\<xi>, p) \<in> reachable A I"
      by clarsimp
    from otr and spo have "((\<sigma>, p), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i" by simp
    with \<open>\<sigma> i = \<xi>\<close> obtain \<xi>' where "\<sigma>' i = \<xi>'"
                               and "((\<xi>, p), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>"
        by (auto dest!: oseq_step_is_seq_step)
    from this(2) and sp have ctr: "((\<xi>, p), a, (\<xi>', p')) \<in> trans A" by simp
    from \<open>(\<xi>, p) \<in> reachable A I\<close> and ctr and \<open>I a\<close>
      have "(\<xi>', p') \<in> reachable A I" ..
    with \<open>\<sigma>' i = \<xi>'\<close> show "\<exists>\<xi>. \<sigma>' i = \<xi> \<and> (\<xi>, p') \<in> reachable A I"
      by blast
  qed

lemma reachable_oseq_seqp_sos':
  assumes "s \<in> reachable OA I"
      and "initiali i (init OA) (init A)"
      and "trans OA = oseqp_sos \<Gamma> i"
      and "trans A = seqp_sos \<Gamma>"
    shows "\<exists>\<xi>. (fst s) i = \<xi> \<and> (\<xi>, snd s) \<in> reachable A I"
  using assms
  by - (cases s, auto dest: reachable_oseq_seqp_sos)

text \<open>
  Any invariant shown in the (simpler) closed semantics can be transferred to an invariant in
  the open semantics.
\<close>

theorem open_seq_invariant [intro]:
  assumes "A \<TTurnstile> (I \<rightarrow>) P"
      and "initiali i (init OA) (init A)"
      and spo: "trans OA = oseqp_sos \<Gamma> i"
      and sp: "trans A = seqp_sos \<Gamma>"
    shows "OA \<Turnstile> (act I, other ANY {i} \<rightarrow>) (seql i P)"
  proof -
    have "OA \<TTurnstile> (I \<rightarrow>) (seql i P)"
      proof (rule invariant_arbitraryI)
        fix s                                      
        assume "s \<in> reachable OA I"
        with \<open>initiali i (init OA) (init A)\<close> obtain \<xi> where "(fst s) i = \<xi>"
                                                        and "(\<xi>, snd s) \<in> reachable A I"
          by (auto dest: reachable_oseq_seqp_sos' [OF _ _ spo sp])
        with \<open>A \<TTurnstile> (I \<rightarrow>) P\<close> have "P (\<xi>, snd s)" by auto
        with \<open>(fst s) i = \<xi>\<close> show "seql i P s" by auto
      qed
    moreover from spo have "subreachable OA (other ANY {i}) {i}" ..
    ultimately show ?thesis
    proof (rule open_closed_invariant)
      fix \<sigma> \<sigma>' s
      assume "\<forall>j\<in>{i}. \<sigma>' j = \<sigma> j"
         and "seql i P (\<sigma>', s)"
      thus "seql i P (\<sigma>, s)" ..
    qed
  qed

definition
  seqll :: "'i \<Rightarrow> ((('s \<times> 'l) \<times> 'a \<times> ('s \<times> 'l)) \<Rightarrow> bool)
               \<Rightarrow> ((('i \<Rightarrow> 's) \<times> 'l) \<times> 'a \<times> (('i \<Rightarrow> 's) \<times> 'l)) \<Rightarrow> bool"
where
  "seqll i P \<equiv> (\<lambda>((\<sigma>, p), a, (\<sigma>', p')). P ((\<sigma> i, p), a, (\<sigma>' i, p')))"

lemma same_seqll [elim]:
  assumes "\<forall>j\<in>{i}. \<sigma>\<^sub>1' j = \<sigma>\<^sub>1 j"
      and "\<forall>j\<in>{i}. \<sigma>\<^sub>2' j = \<sigma>\<^sub>2 j"
      and "seqll i P ((\<sigma>\<^sub>1', s), a, (\<sigma>\<^sub>2', s'))"
    shows "seqll i P ((\<sigma>\<^sub>1,  s), a, (\<sigma>\<^sub>2,  s'))"
  using assms unfolding seqll_def by (clarsimp)

lemma seqllI [intro!]:
  assumes "P ((\<sigma> i, p), a, (\<sigma>' i, p'))"
    shows "seqll i P ((\<sigma>, p), a, (\<sigma>', p'))"
  using assms unfolding seqll_def by simp

lemma seqllD [dest]:
  assumes "seqll i P ((\<sigma>, p), a, (\<sigma>', p'))"
    shows "P ((\<sigma> i, p), a, (\<sigma>' i, p'))"
  using assms unfolding seqll_def by simp

lemma seqllsimp:
  "seqll i P ((\<sigma>, p), a, (\<sigma>', p')) = P ((\<sigma> i, p), a, (\<sigma>' i, p'))"
  unfolding seqll_def by simp

lemma seqll_onll_swap:
  "seqll i (onll \<Gamma> P) = onll \<Gamma> (seqll i P)"
  unfolding seqll_def onll_def by simp

theorem open_seq_step_invariant [intro]:
  assumes "A \<TTurnstile>\<^sub>A (I \<rightarrow>) P"
      and "initiali i (init OA) (init A)"
      and spo: "trans OA = oseqp_sos \<Gamma> i"
      and sp: "trans A = seqp_sos \<Gamma>"
    shows "OA \<Turnstile>\<^sub>A (act I, other ANY {i} \<rightarrow>) (seqll i P)"
  proof -
    have "OA \<TTurnstile>\<^sub>A (I \<rightarrow>) (seqll i P)"
    proof (rule step_invariant_arbitraryI)
      fix \<sigma> p a \<sigma>' p'
      assume or: "(\<sigma>, p) \<in> reachable OA I"
         and otr: "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans OA"
         and "I a"
      from or \<open>initiali i (init OA) (init A)\<close> spo sp obtain \<xi> where "\<sigma> i = \<xi>"
                                                             and cr: "(\<xi>, p) \<in> reachable A I"
        by - (drule(3) reachable_oseq_seqp_sos', auto)
      from otr and spo have "((\<sigma>, p), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i" by simp
      with \<open>\<sigma> i = \<xi>\<close> obtain \<xi>' where "\<sigma>' i = \<xi>'"
                                 and ctr: "((\<xi>, p), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>"
        by (auto dest!: oseq_step_is_seq_step)
      with sp have "((\<xi>, p), a, (\<xi>', p')) \<in> trans A" by simp
      with \<open>A \<TTurnstile>\<^sub>A (I \<rightarrow>) P\<close> cr have "P ((\<xi>, p), a, (\<xi>', p'))" using \<open>I a\<close> ..
      with \<open>\<sigma> i = \<xi>\<close> and \<open>\<sigma>' i = \<xi>'\<close> have "P ((\<sigma> i, p), a, (\<sigma>' i, p'))" by simp
      thus "seqll i P ((\<sigma>, p), a, (\<sigma>', p'))" ..
    qed
    moreover from spo have "local_steps (trans OA) {i}" by simp
    moreover have "other_steps (other ANY {i}) {i}" ..
    ultimately show ?thesis
    proof (rule open_closed_step_invariant)
      fix \<sigma> \<zeta> a \<sigma>' \<zeta>' s s'
      assume "\<forall>j\<in>{i}. \<sigma> j = \<zeta> j"
         and "\<forall>j\<in>{i}. \<sigma>' j = \<zeta>' j"
         and "seqll i P ((\<sigma>, s), a, (\<sigma>', s'))"
        thus "seqll i P ((\<zeta>, s), a, (\<zeta>', s'))" ..
    qed
  qed

end

