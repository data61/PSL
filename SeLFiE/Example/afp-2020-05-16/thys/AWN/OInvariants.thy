(*  Title:       OInvariants.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Open reachability and invariance"

theory OInvariants
imports Invariants
begin

subsection "Open reachability"

text \<open>
  By convention, the states of an open automaton are pairs. The first component is considered
  to be the global state and the second is the local state.

  A state is `open reachable' under @{term S} and @{term U} if it is the initial state, or it
  is the destination of a transition---where the global components satisfy @{term S}---from an
  open reachable state, or it is the destination of an interleaved environment step where the
  global components satisfy @{term U}.
\<close>

inductive_set oreachable
  :: "('g \<times> 'l, 'a) automaton
      \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'a \<Rightarrow> bool)
      \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> bool)
      \<Rightarrow> ('g \<times> 'l) set"
  for A  :: "('g \<times> 'l, 'a) automaton"
  and S  :: "'g \<Rightarrow> 'g \<Rightarrow> 'a \<Rightarrow> bool"
  and U  :: "'g \<Rightarrow> 'g \<Rightarrow> bool"
where
    oreachable_init: "s \<in> init A \<Longrightarrow> s \<in> oreachable A S U"
  | oreachable_local: "\<lbrakk> s \<in> oreachable A S U; (s, a, s') \<in> trans A; S (fst s) (fst s') a \<rbrakk>
                        \<Longrightarrow> s' \<in> oreachable A S U"
  | oreachable_other: "\<lbrakk> s \<in> oreachable A S U; U (fst s) \<sigma>' \<rbrakk>
                        \<Longrightarrow> (\<sigma>', snd s) \<in> oreachable A S U"

lemma oreachable_local' [elim]:
  assumes "(\<sigma>, p) \<in> oreachable A S U"
      and "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A"
      and "S \<sigma> \<sigma>' a"
    shows "(\<sigma>', p') \<in> oreachable A S U"
  using assms by (metis fst_conv oreachable.oreachable_local)

lemma oreachable_other' [elim]:
  assumes "(\<sigma>, p) \<in> oreachable A S U"
      and "U \<sigma> \<sigma>'"
    shows "(\<sigma>', p) \<in> oreachable A S U"
  proof -
    from \<open>U \<sigma> \<sigma>'\<close> have "U (fst (\<sigma>, p)) \<sigma>'" by simp
    with \<open>(\<sigma>, p) \<in> oreachable A S U\<close> have "(\<sigma>', snd (\<sigma>, p)) \<in> oreachable A S U"
      by (rule oreachable_other)
    thus "(\<sigma>', p) \<in> oreachable A S U" by simp
  qed

lemma oreachable_pair_induct [consumes, case_names init other local]:
  assumes "(\<sigma>, p) \<in> oreachable A S U"
      and "\<And>\<sigma> p. (\<sigma>, p) \<in> init A \<Longrightarrow> P \<sigma> p"
      and "(\<And>\<sigma> p \<sigma>'. \<lbrakk> (\<sigma>, p) \<in> oreachable A S U; P \<sigma> p; U \<sigma> \<sigma>' \<rbrakk> \<Longrightarrow> P \<sigma>' p)"
      and "(\<And>\<sigma> p \<sigma>' p' a. \<lbrakk> (\<sigma>, p) \<in> oreachable A S U; P \<sigma> p;
                            ((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A; S \<sigma> \<sigma>' a \<rbrakk> \<Longrightarrow> P \<sigma>' p')"
    shows "P \<sigma> p"
  using assms (1) proof (induction "(\<sigma>, p)" arbitrary: \<sigma> p)
    fix \<sigma> p
    assume "(\<sigma>, p) \<in> init A"
    with assms(2) show "P \<sigma> p" .
  next
    fix s \<sigma>'
    assume "s \<in> oreachable A S U"
       and "U (fst s) \<sigma>'"
       and IH: "\<And>\<sigma> p. s = (\<sigma>, p) \<Longrightarrow> P \<sigma> p"
    from this(1) obtain \<sigma> p where "s = (\<sigma>, p)"
                              and "(\<sigma>, p) \<in> oreachable A S U"
      by (metis surjective_pairing)
    note this(2)
    moreover from IH and \<open>s = (\<sigma>, p)\<close> have "P \<sigma> p" .
    moreover from \<open>U (fst s) \<sigma>'\<close> and \<open>s = (\<sigma>, p)\<close> have "U \<sigma> \<sigma>'" by simp
    ultimately have "P \<sigma>' p" by (rule assms(3))
    with \<open>s = (\<sigma>, p)\<close> show "P \<sigma>' (snd s)" by simp
  next
    fix s a \<sigma>' p'
    assume "s \<in> oreachable A S U"
       and tr: "(s, a, (\<sigma>', p')) \<in> trans A"
       and "S (fst s) (fst (\<sigma>', p')) a"
       and IH: "\<And>\<sigma> p. s = (\<sigma>, p) \<Longrightarrow> P \<sigma> p"
    from this(1) obtain \<sigma> p where "s = (\<sigma>, p)"
                              and "(\<sigma>, p) \<in> oreachable A S U"
      by (metis surjective_pairing)
    note this(2)
    moreover from IH \<open>s = (\<sigma>, p)\<close> have "P \<sigma> p" .
    moreover from tr and \<open>s = (\<sigma>, p)\<close> have "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A" by simp
    moreover from \<open>S (fst s) (fst (\<sigma>', p')) a\<close> and \<open>s = (\<sigma>, p)\<close> have "S \<sigma> \<sigma>' a" by simp
    ultimately show "P \<sigma>' p'" by (rule assms(4))
  qed

lemma oreachable_weakenE [elim]:
  assumes "s \<in> oreachable A PS PU"
      and PSQS: "\<And>s s' a. PS s s' a \<Longrightarrow> QS s s' a"
      and PUQU: "\<And>s s'.   PU s s'   \<Longrightarrow> QU s s'"
    shows "s \<in> oreachable A QS QU"
  using assms(1)
  proof (induction)
    fix s assume "s \<in> init A"
    thus "s \<in> oreachable A QS QU" ..
  next
    fix s a s'
    assume "s \<in> oreachable A QS QU"
       and "(s, a, s') \<in> trans A"
       and "PS (fst s) (fst s') a"
    from \<open>PS (fst s) (fst s') a\<close> have "QS (fst s) (fst s') a" by (rule PSQS)
    with \<open>s \<in> oreachable A QS QU\<close> and \<open>(s, a, s') \<in> trans A\<close> show "s' \<in> oreachable A QS QU" ..
  next
    fix s g'
    assume "s \<in> oreachable A QS QU"
       and "PU (fst s) g'"
    from \<open>PU (fst s) g'\<close> have "QU (fst s) g'" by (rule PUQU)
    with \<open>s \<in> oreachable A QS QU\<close> show "(g', snd s) \<in> oreachable A QS QU" ..
  qed

definition
  act :: "('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool"
where
  "act I \<equiv> (\<lambda>_ _. I)"

lemma act_simp [iff]: "act I s s' a = I a"
  unfolding act_def ..

lemma reachable_in_oreachable [elim]:
    fixes s
  assumes "s \<in> reachable A I"
    shows "s \<in> oreachable A (act I) U"
  unfolding act_def using assms proof induction
    fix s
    assume "s \<in> init A"
    thus "s \<in> oreachable A (\<lambda>_ _. I) U" ..
  next
    fix s a s'
    assume "s \<in> oreachable A (\<lambda>_ _. I) U"
       and "(s, a, s') \<in> trans A"
       and "I a"
    thus "s' \<in> oreachable A (\<lambda>_ _. I) U"
      by (rule oreachable_local)
  qed

subsection "Open Invariance"

definition oinvariant
  :: "('g \<times> 'l, 'a) automaton
      \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> bool)
      \<Rightarrow> (('g \<times> 'l) \<Rightarrow> bool) \<Rightarrow> bool"
  ("_ \<Turnstile> (1'((1_),/ (1_) \<rightarrow>')/ _)" [100, 0, 0, 9] 8)
where
  "(A \<Turnstile> (S, U \<rightarrow>) P) = (\<forall>s\<in>oreachable A S U. P s)"

lemma oinvariantI [intro]:
    fixes T TI S U P
  assumes init: "\<And>s. s \<in> init A \<Longrightarrow> P s"
      and other: "\<And>g g' l.
                  \<lbrakk> (g, l) \<in> oreachable A S U; P (g, l); U g g' \<rbrakk> \<Longrightarrow> P (g', l)"
      and local: "\<And>s a s'.
                  \<lbrakk> s \<in> oreachable A S U; P s; (s, a, s') \<in> trans A; S (fst s) (fst s') a \<rbrakk> \<Longrightarrow> P s'"
    shows "A \<Turnstile> (S, U \<rightarrow>) P"
  unfolding oinvariant_def
  proof
       fix s
    assume "s \<in> oreachable A S U"
      thus "P s"
    proof induction
      fix s assume "s \<in> init A"
      thus "P s" by (rule init)
    next
      fix s a s'
      assume "s \<in> oreachable A S U"
         and "P s"
         and "(s, a, s') \<in> trans A"
         and "S (fst s) (fst s') a"
        thus "P s'" by (rule local)
     next
       fix s g'
       assume "s \<in> oreachable A S U"
          and "P s"
          and "U (fst s) g'"
         thus "P (g', snd s)"
           by - (rule other [where g="fst s"], simp_all)
    qed
  qed

lemma oinvariant_oreachableI:
  assumes "\<And>\<sigma> s. (\<sigma>, s)\<in>oreachable A S U \<Longrightarrow> P (\<sigma>, s)"
  shows "A \<Turnstile> (S, U \<rightarrow>) P"
  using assms unfolding oinvariant_def by auto

lemma oinvariant_pairI [intro]:
  assumes init: "\<And>\<sigma> p. (\<sigma>, p) \<in> init A \<Longrightarrow> P (\<sigma>, p)"
      and local: "\<And>\<sigma> p \<sigma>' p' a.
                   \<lbrakk> (\<sigma>, p) \<in> oreachable A S U; P (\<sigma>, p); ((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A;
                     S \<sigma> \<sigma>' a \<rbrakk> \<Longrightarrow> P (\<sigma>', p')"
      and other: "\<And>\<sigma> \<sigma>' p.
                  \<lbrakk> (\<sigma>, p) \<in> oreachable A S U; P (\<sigma>, p); U \<sigma> \<sigma>' \<rbrakk> \<Longrightarrow> P (\<sigma>', p)"
    shows "A \<Turnstile> (S, U \<rightarrow>) P"
  by (rule oinvariantI)
     (clarsimp | erule init | erule(3) local | erule(2) other)+

lemma oinvariantD [dest]:
  assumes "A \<Turnstile> (S, U \<rightarrow>) P"
      and "s \<in> oreachable A S U"
    shows "P s"
  using assms unfolding oinvariant_def
  by clarsimp

lemma oinvariant_initD [dest, elim]:
  assumes invP: "A \<Turnstile> (S, U \<rightarrow>) P"
      and init: "s \<in> init A"
    shows "P s"
  proof -
    from init have "s \<in> oreachable A S U" ..
    with invP show ?thesis ..
  qed

lemma oinvariant_weakenE [elim!]:
  assumes invP: "A \<Turnstile> (PS, PU \<rightarrow>) P"
      and PQ:   "\<And>s. P s \<Longrightarrow> Q s"
      and QSPS: "\<And>s s' a. QS s s' a \<Longrightarrow> PS s s' a"
      and QUPU: "\<And>s s'.   QU s s'   \<Longrightarrow> PU s s'"
    shows       "A \<Turnstile> (QS, QU \<rightarrow>) Q"
  proof
    fix s
    assume "s \<in> init A"
    with invP have "P s" ..
    thus "Q s" by (rule PQ)
  next
    fix \<sigma> p \<sigma>' p' a
    assume "(\<sigma>, p) \<in> oreachable A QS QU"
       and "((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A"
       and "QS \<sigma> \<sigma>' a"
    from this(3) have "PS \<sigma> \<sigma>' a" by (rule QSPS)
    from \<open>(\<sigma>, p) \<in> oreachable A QS QU\<close> and QSPS QUPU have "(\<sigma>, p) \<in> oreachable A PS PU" ..
    hence "(\<sigma>', p') \<in> oreachable A PS PU" using \<open>((\<sigma>, p), a, (\<sigma>', p')) \<in> trans A\<close> and \<open>PS \<sigma> \<sigma>' a\<close> ..
    with invP have "P (\<sigma>', p')" ..
    thus "Q (\<sigma>', p')" by (rule PQ)
  next
    fix \<sigma> \<sigma>' p
    assume "(\<sigma>, p) \<in> oreachable A QS QU"
       and "Q (\<sigma>, p)"
       and "QU \<sigma> \<sigma>'"
    from \<open>QU \<sigma> \<sigma>'\<close> have "PU \<sigma> \<sigma>'" by (rule QUPU)
    from \<open>(\<sigma>, p) \<in> oreachable A QS QU\<close> and QSPS QUPU have "(\<sigma>, p) \<in> oreachable A PS PU" ..
    hence "(\<sigma>', p) \<in> oreachable A PS PU" using \<open>PU \<sigma> \<sigma>'\<close> ..
    with invP have "P (\<sigma>', p)" ..
    thus "Q (\<sigma>', p)" by (rule PQ)
  qed

lemma oinvariant_weakenD [dest]:
  assumes "A \<Turnstile> (S', U' \<rightarrow>) P"
      and "(\<sigma>, p) \<in> oreachable A S U"
      and weakenS: "\<And>s s' a. S s s' a \<Longrightarrow> S' s s' a"
      and weakenU: "\<And>s s'. U s s' \<Longrightarrow> U' s s'"
    shows "P (\<sigma>, p)"
  proof -
    from \<open>(\<sigma>, p) \<in> oreachable A S U\<close> have "(\<sigma>, p) \<in> oreachable A S' U'"
      by (rule oreachable_weakenE)
         (erule weakenS, erule weakenU)
    with \<open>A \<Turnstile> (S', U' \<rightarrow>) P\<close> show "P (\<sigma>, p)" ..
  qed

lemma close_open_invariant:
  assumes oinv: "A \<Turnstile> (act I, U \<rightarrow>) P"
    shows "A \<TTurnstile> (I \<rightarrow>) P"
  proof
    fix s
    assume "s \<in> init A"
    with oinv show "P s" ..
  next
    fix \<xi> p \<xi>' p' a
    assume sr: "(\<xi>, p) \<in> reachable A I"
       and step: "((\<xi>, p), a, (\<xi>', p')) \<in> trans A"
       and "I a"
    hence "(\<xi>', p') \<in> reachable A I" ..
    hence "(\<xi>', p') \<in> oreachable A (act I) U" ..
    with oinv show "P (\<xi>', p')" ..
  qed

definition local_steps :: "((('i \<Rightarrow> 's1) \<times> 'l1) \<times> 'a \<times> ('i \<Rightarrow> 's2) \<times> 'l2) set \<Rightarrow> 'i set \<Rightarrow> bool"
where "local_steps T J \<equiv>
   (\<forall>\<sigma> \<zeta> s a \<sigma>' s'. ((\<sigma>, s), a, (\<sigma>', s')) \<in> T \<and> (\<forall>j\<in>J. \<zeta> j = \<sigma> j)
   \<longrightarrow> (\<exists>\<zeta>'. (\<forall>j\<in>J. \<zeta>' j = \<sigma>' j) \<and> ((\<zeta>, s), a, (\<zeta>', s')) \<in> T))"

lemma local_stepsI [intro!]:
  assumes "\<And>\<sigma> \<zeta> s a \<sigma>' \<zeta>' s'. \<lbrakk> ((\<sigma>, s), a, (\<sigma>', s')) \<in> T; \<forall>j\<in>J. \<zeta> j = \<sigma> j \<rbrakk>
                               \<Longrightarrow> (\<exists>\<zeta>'. (\<forall>j\<in>J. \<zeta>' j = \<sigma>' j) \<and> ((\<zeta>, s), a, (\<zeta>', s')) \<in> T)"
    shows "local_steps T J"
  unfolding local_steps_def using assms by clarsimp

lemma local_stepsE [elim, dest]:
  assumes "local_steps T J"
      and "((\<sigma>, s), a, (\<sigma>', s')) \<in> T"
      and "\<forall>j\<in>J. \<zeta> j = \<sigma> j"
    shows "\<exists>\<zeta>'. (\<forall>j\<in>J. \<zeta>' j = \<sigma>' j) \<and> ((\<zeta>, s), a, (\<zeta>', s')) \<in> T"
  using assms unfolding local_steps_def by blast

definition other_steps :: "(('i \<Rightarrow> 's) \<Rightarrow> ('i \<Rightarrow> 's) \<Rightarrow> bool) \<Rightarrow> 'i set \<Rightarrow> bool"
where "other_steps U J \<equiv> \<forall>\<sigma> \<sigma>'. U \<sigma> \<sigma>' \<longrightarrow> (\<forall>j\<in>J. \<sigma>' j = \<sigma> j)"

lemma other_stepsI [intro!]:
  assumes "\<And>\<sigma> \<sigma>' j. \<lbrakk> U \<sigma> \<sigma>'; j \<in> J \<rbrakk> \<Longrightarrow> \<sigma>' j = \<sigma> j"
    shows "other_steps U J"
  using assms unfolding other_steps_def by simp

lemma other_stepsE [elim]:
  assumes "other_steps U J"
      and "U \<sigma> \<sigma>'"
    shows "\<forall>j\<in>J. \<sigma>' j = \<sigma> j"
  using assms unfolding other_steps_def by simp

definition subreachable
where "subreachable A U J \<equiv> \<forall>I. \<forall>s \<in> oreachable A (\<lambda>s s'. I) U.
                                  (\<exists>\<sigma>. (\<forall>j\<in>J. \<sigma> j = (fst s) j) \<and> (\<sigma>, snd s) \<in> reachable A I)"

lemma subreachableI [intro]:
  assumes "local_steps (trans A) J"
      and "other_steps U J"
    shows "subreachable A U J"
  unfolding subreachable_def
  proof (rule, rule)
    fix I s
    assume "s \<in> oreachable A (\<lambda>s s'. I) U"
    thus "(\<exists>\<sigma>. (\<forall>j\<in>J. \<sigma> j = (fst s) j) \<and> (\<sigma>, snd s) \<in> reachable A I)"
    proof induction
      fix s
      assume "s \<in> init A"
      hence "(fst s, snd s) \<in> reachable A I"
        by simp (rule reachable_init)
      moreover have "\<forall>j\<in>J. (fst s) j = (fst s) j"
        by simp
      ultimately show "\<exists>\<sigma>. (\<forall>j\<in>J. \<sigma> j = (fst s) j) \<and> (\<sigma>, snd s) \<in> reachable A I"
        by auto
    next
      fix s a s'
      assume "\<exists>\<sigma>. (\<forall>j\<in>J. \<sigma> j = (fst s) j) \<and> (\<sigma>, snd s) \<in> reachable A I"
         and "(s, a, s') \<in> trans A"
         and "I a"
      then obtain \<zeta> where "\<forall>j\<in>J. \<zeta> j = (fst s) j"
                      and "(\<zeta>, snd s) \<in> reachable A I" by auto

      from \<open>(s, a, s') \<in> trans A\<close> have "((fst s, snd s), a, (fst s', snd s')) \<in> trans A"
        by simp
      with \<open>local_steps (trans A) J\<close> obtain \<zeta>' where "\<forall>j\<in>J. \<zeta>' j = (fst s') j"
                                                 and "((\<zeta>, snd s), a, (\<zeta>', snd s')) \<in> trans A"
        using \<open>\<forall>j\<in>J. \<zeta> j = (fst s) j\<close> by - (drule(2) local_stepsE, clarsimp)
      from \<open>(\<zeta>, snd s) \<in> reachable A I\<close>
       and \<open>((\<zeta>, snd s), a, (\<zeta>', snd s')) \<in> trans A\<close>
       and \<open>I a\<close>
       have "(\<zeta>', snd s') \<in> reachable A I" ..

      with \<open>\<forall>j\<in>J. \<zeta>' j = (fst s') j\<close>
        show "\<exists>\<sigma>. (\<forall>j\<in>J. \<sigma> j = (fst s') j) \<and> (\<sigma>, snd s') \<in> reachable A I" by auto
    next
      fix s \<sigma>'
      assume "\<exists>\<sigma>. (\<forall>j\<in>J. \<sigma> j = (fst s) j) \<and> (\<sigma>, snd s) \<in> reachable A I"
         and "U (fst s) \<sigma>'"
      then obtain \<sigma> where "\<forall>j\<in>J. \<sigma> j = (fst s) j"
                      and "(\<sigma>, snd s) \<in> reachable A I" by auto
      from \<open>other_steps U J\<close> and \<open>U (fst s) \<sigma>'\<close> have "\<forall>j\<in>J. \<sigma>' j = (fst s) j"
        by - (erule(1) other_stepsE)
      with \<open>\<forall>j\<in>J. \<sigma> j = (fst s) j\<close> have "\<forall>j\<in>J. \<sigma> j = \<sigma>' j"
        by clarsimp
      with \<open>(\<sigma>, snd s) \<in> reachable A I\<close>
       show "\<exists>\<sigma>. (\<forall>j\<in>J. \<sigma> j = fst (\<sigma>', snd s) j) \<and> (\<sigma>, snd (\<sigma>', snd s)) \<in> reachable A I"
         by auto
    qed
  qed

lemma subreachableE [elim]:
  assumes "subreachable A U J"
      and "s \<in> oreachable A (\<lambda>s s'. I) U"
    shows "\<exists>\<sigma>. (\<forall>j\<in>J. \<sigma> j = (fst s) j) \<and> (\<sigma>, snd s) \<in> reachable A I"
  using assms unfolding subreachable_def by simp

lemma subreachableE_pair [elim]:
  assumes "subreachable A U J"
      and "(\<sigma>, s) \<in> oreachable A (\<lambda>s s'. I) U"
    shows "\<exists>\<zeta>. (\<forall>j\<in>J. \<zeta> j = \<sigma> j) \<and> (\<zeta>, s) \<in> reachable A I"
  using assms unfolding subreachable_def by (metis fst_conv snd_conv)

lemma subreachable_otherE [elim]:
  assumes "subreachable A U J"
      and "(\<sigma>, l) \<in> oreachable A (\<lambda>s s'. I) U"
      and "U \<sigma> \<sigma>'"
    shows "\<exists>\<zeta>'. (\<forall>j\<in>J. \<zeta>' j = \<sigma>' j) \<and> (\<zeta>', l) \<in> reachable A I"
  proof -
    from \<open>(\<sigma>, l) \<in> oreachable A (\<lambda>s s'. I) U\<close> and \<open>U \<sigma> \<sigma>'\<close>
      have "(\<sigma>', l) \<in> oreachable A (\<lambda>s s'. I) U"
      by - (rule oreachable_other')
    with \<open>subreachable A U J\<close> show ?thesis
      by auto
  qed

lemma open_closed_invariant:
    fixes J
  assumes "A \<TTurnstile> (I \<rightarrow>) P"
      and "subreachable A U J"
      and localp: "\<And>\<sigma> \<sigma>' s. \<lbrakk> \<forall>j\<in>J. \<sigma>' j = \<sigma> j; P (\<sigma>', s) \<rbrakk> \<Longrightarrow> P (\<sigma>, s)"
    shows "A \<Turnstile> (act I, U \<rightarrow>) P"
  proof (rule, simp_all only: act_def)
    fix s
    assume "s \<in> init A"
    with \<open>A \<TTurnstile> (I \<rightarrow>) P\<close> show "P s" ..
  next
    fix s a s'
    assume "s \<in> oreachable A (\<lambda>_ _. I) U"
       and "P s"
       and "(s, a, s') \<in> trans A"
       and "I a"
    hence "s' \<in> oreachable A (\<lambda>_ _. I) U"
      by (metis oreachable_local)
    with \<open>subreachable A U J\<close> obtain \<sigma>'
      where "\<forall>j\<in>J. \<sigma>' j = (fst s') j"
        and "(\<sigma>', snd s') \<in> reachable A I"
        by (metis subreachableE)
    from \<open>A \<TTurnstile> (I \<rightarrow>) P\<close> and \<open>(\<sigma>', snd s') \<in> reachable A I\<close> have "P (\<sigma>', snd s')" ..
    with \<open>\<forall>j\<in>J. \<sigma>' j = (fst s') j\<close> show "P s'"
      by (metis localp prod.collapse)
  next
    fix g g' l
    assume or: "(g, l) \<in> oreachable A (\<lambda>s s'. I) U"
       and "U g g'"
       and "P (g, l)"
    from \<open>subreachable A U J\<close> and or and \<open>U g g'\<close>
      obtain gg' where "\<forall>j\<in>J. gg' j = g' j"
                   and "(gg', l) \<in> reachable A I"
        by (auto dest!: subreachable_otherE)
    from \<open>A \<TTurnstile> (I \<rightarrow>) P\<close> and \<open>(gg', l) \<in> reachable A I\<close>
      have "P (gg', l)" ..
    with \<open>\<forall>j\<in>J. gg' j = g' j\<close> show "P (g', l)"
      by (rule localp)
  qed

lemma oinvariant_anyact:
  assumes "A \<Turnstile> (act TT, U \<rightarrow>) P"
    shows "A \<Turnstile> (S, U \<rightarrow>) P"                             
  using assms by rule auto

definition
  ostep_invariant
  :: "('g \<times> 'l, 'a) automaton
      \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> bool)
      \<Rightarrow> (('g \<times> 'l, 'a) transition \<Rightarrow> bool) \<Rightarrow> bool"
  ("_ \<Turnstile>\<^sub>A (1'((1_),/ (1_) \<rightarrow>')/ _)" [100, 0, 0, 9] 8)
where
  "(A \<Turnstile>\<^sub>A (S, U \<rightarrow>) P) =
     (\<forall>s\<in>oreachable A S U. (\<forall>a s'. (s, a, s') \<in> trans A \<and> S (fst s) (fst s') a \<longrightarrow> P (s, a, s')))"

lemma ostep_invariant_def':
  "(A \<Turnstile>\<^sub>A (S, U \<rightarrow>) P) = (\<forall>s\<in>oreachable A S U.
                           (\<forall>a s'. (s, a, s') \<in> trans A \<and> S (fst s) (fst s') a \<longrightarrow> P (s, a, s')))"
  unfolding ostep_invariant_def by auto

lemma ostep_invariantI [intro]:
  assumes *: "\<And>\<sigma> s a \<sigma>' s'. \<lbrakk> (\<sigma>, s)\<in>oreachable A S U; ((\<sigma>, s), a, (\<sigma>', s')) \<in> trans A; S \<sigma> \<sigma>' a \<rbrakk>
                             \<Longrightarrow> P ((\<sigma>, s), a, (\<sigma>', s'))"
    shows "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) P"
  unfolding ostep_invariant_def
  using assms by auto

lemma ostep_invariantD [dest]:
  assumes "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) P"
      and "(\<sigma>, s)\<in>oreachable A S U"
      and "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans A"
      and "S \<sigma> \<sigma>' a"
    shows "P ((\<sigma>, s), a, (\<sigma>', s'))"
  using assms unfolding ostep_invariant_def' by clarsimp

lemma ostep_invariantE [elim]:
  assumes "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) P"
      and "(\<sigma>, s)\<in>oreachable A S U"
      and "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans A"
      and "S \<sigma> \<sigma>' a"
      and "P ((\<sigma>, s), a, (\<sigma>', s')) \<Longrightarrow> Q"
    shows "Q"
  using assms by auto

lemma ostep_invariant_weakenE [elim!]:
  assumes invP: "A \<Turnstile>\<^sub>A (PS, PU \<rightarrow>) P"
      and PQ:   "\<And>t. P t \<Longrightarrow> Q t"
      and QSPS: "\<And>\<sigma> \<sigma>' a. QS \<sigma> \<sigma>' a \<Longrightarrow> PS \<sigma> \<sigma>' a"
      and QUPU: "\<And>\<sigma> \<sigma>'.   QU \<sigma> \<sigma>'   \<Longrightarrow> PU \<sigma> \<sigma>'"
    shows       "A \<Turnstile>\<^sub>A (QS, QU \<rightarrow>) Q"
  proof
    fix \<sigma> s \<sigma>' s' a
    assume "(\<sigma>, s) \<in> oreachable A QS QU"
       and "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans A"
       and "QS \<sigma> \<sigma>' a"
    from \<open>QS \<sigma> \<sigma>' a\<close> have "PS \<sigma> \<sigma>' a" by (rule QSPS)
    from \<open>(\<sigma>, s) \<in> oreachable A QS QU\<close> have "(\<sigma>, s) \<in> oreachable A PS PU" using QSPS QUPU ..
    with invP have "P ((\<sigma>, s), a, (\<sigma>', s'))" using \<open>((\<sigma>, s), a, (\<sigma>', s')) \<in> trans A\<close> \<open>PS \<sigma> \<sigma>' a\<close> ..
    thus "Q ((\<sigma>, s), a, (\<sigma>', s'))" by (rule PQ)
  qed

lemma ostep_invariant_weaken_with_invariantE [elim]:
  assumes pinv: "A \<Turnstile> (S, U \<rightarrow>) P"
      and qinv: "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) Q"
      and wr: "\<And>\<sigma> s a \<sigma>' s'. \<lbrakk> P (\<sigma>, s); P (\<sigma>', s'); Q ((\<sigma>, s), a, (\<sigma>', s')); S \<sigma> \<sigma>' a \<rbrakk>
                              \<Longrightarrow> R ((\<sigma>, s), a, (\<sigma>', s'))"
    shows "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) R"
  proof
    fix \<sigma> s a \<sigma>' s'
    assume sr: "(\<sigma>, s) \<in> oreachable A S U"
       and tr: "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans A"
       and "S \<sigma> \<sigma>' a"
    hence "(\<sigma>', s') \<in> oreachable A S U" ..
    with pinv have "P (\<sigma>', s')" ..
    from pinv and sr have "P (\<sigma>, s)" ..
    from qinv sr tr \<open>S \<sigma> \<sigma>' a\<close> have "Q ((\<sigma>, s), a, (\<sigma>', s'))" ..
    with \<open>P (\<sigma>, s)\<close> and \<open>P (\<sigma>', s')\<close> show "R ((\<sigma>, s), a, (\<sigma>', s'))" using \<open>S \<sigma> \<sigma>' a\<close> by (rule wr)
  qed

lemma ostep_to_invariantI:
  assumes sinv: "A \<Turnstile>\<^sub>A (S, U \<rightarrow>) Q"
      and init: "\<And>\<sigma> s. (\<sigma>, s) \<in> init A \<Longrightarrow> P (\<sigma>, s)"
      and local: "\<And>\<sigma> s \<sigma>' s' a.
                    \<lbrakk> (\<sigma>, s) \<in> oreachable A S U;
                      P (\<sigma>, s);
                      Q ((\<sigma>, s), a, (\<sigma>', s'));
                      S \<sigma> \<sigma>' a \<rbrakk> \<Longrightarrow> P (\<sigma>', s')"
      and other: "\<And>\<sigma> \<sigma>' s. \<lbrakk> (\<sigma>, s) \<in> oreachable A S U; U \<sigma> \<sigma>'; P (\<sigma>, s) \<rbrakk> \<Longrightarrow> P (\<sigma>', s)"
    shows "A \<Turnstile> (S, U \<rightarrow>) P"
  proof
    fix \<sigma> s assume "(\<sigma>, s) \<in> init A" thus "P (\<sigma>, s)" by (rule init)
  next
    fix \<sigma> s \<sigma>' s' a
    assume "(\<sigma>, s) \<in> oreachable A S U"
       and "P (\<sigma>, s)"
       and "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans A"
       and "S \<sigma> \<sigma>' a"
      show "P (\<sigma>', s')"
    proof -
      from sinv and \<open>(\<sigma>, s)\<in>oreachable A S U\<close> and \<open>((\<sigma>, s), a, (\<sigma>', s')) \<in> trans A\<close> and \<open>S \<sigma> \<sigma>' a\<close>
        have "Q ((\<sigma>, s), a, (\<sigma>', s'))" ..
      with \<open>(\<sigma>, s)\<in>oreachable A S U\<close> and \<open>P (\<sigma>, s)\<close> show "P (\<sigma>', s')"
        using \<open>S \<sigma> \<sigma>' a\<close> by (rule local)
    qed
  next
    fix \<sigma> \<sigma>' l
    assume "(\<sigma>, l) \<in> oreachable A S U"
       and "U \<sigma> \<sigma>'"
       and "P (\<sigma>, l)"
      thus "P (\<sigma>', l)" by (rule other)
  qed

lemma open_closed_step_invariant:
  assumes "A \<TTurnstile>\<^sub>A (I \<rightarrow>) P"
      and "local_steps (trans A) J"
      and "other_steps U J"
      and localp: "\<And>\<sigma> \<zeta> a \<sigma>' \<zeta>' s s'.
                   \<lbrakk> \<forall>j\<in>J. \<sigma> j = \<zeta> j; \<forall>j\<in>J. \<sigma>' j = \<zeta>' j; P ((\<sigma>, s), a, (\<sigma>', s')) \<rbrakk>
                   \<Longrightarrow> P ((\<zeta>, s), a, (\<zeta>', s'))"
    shows "A \<Turnstile>\<^sub>A (act I, U \<rightarrow>) P"
  proof
    fix \<sigma> s a \<sigma>' s'
    assume or: "(\<sigma>, s) \<in> oreachable A (act I) U"
       and tr: "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans A"
       and "act I \<sigma> \<sigma>' a"
    from \<open>act I \<sigma> \<sigma>' a\<close> have "I a" ..
    from \<open>local_steps (trans A) J\<close> and \<open>other_steps U J\<close> have "subreachable A U J" ..
    then obtain \<zeta> where "\<forall>j\<in>J. \<zeta> j = \<sigma> j"
                    and "(\<zeta>, s) \<in> reachable A I"
      using or unfolding act_def
        by (auto dest!: subreachableE_pair)

     from \<open>local_steps (trans A) J\<close> and tr and \<open>\<forall>j\<in>J. \<zeta> j = \<sigma> j\<close>
       obtain \<zeta>' where "\<forall>j\<in>J. \<zeta>' j = \<sigma>' j"
                   and "((\<zeta>, s), a, (\<zeta>', s')) \<in> trans A"
       by auto

    from \<open>A \<TTurnstile>\<^sub>A (I \<rightarrow>) P\<close> and \<open>(\<zeta>, s) \<in> reachable A I\<close>
                          and \<open>((\<zeta>, s), a, (\<zeta>', s')) \<in> trans A\<close>
                          and \<open>I a\<close>
      have "P ((\<zeta>, s), a, (\<zeta>', s'))" ..
    with \<open>\<forall>j\<in>J. \<zeta> j = \<sigma> j\<close> and \<open>\<forall>j\<in>J. \<zeta>' j = \<sigma>' j\<close> show "P ((\<sigma>, s), a, (\<sigma>', s'))"
      by (rule localp)
  qed

lemma oinvariant_step_anyact:
  assumes "p \<Turnstile>\<^sub>A (act TT, U \<rightarrow>) P"
    shows "p \<Turnstile>\<^sub>A (S, U \<rightarrow>) P"
  using assms by rule auto

subsection "Standard assumption predicates "

text \<open>otherwith\<close>

definition otherwith :: "('s \<Rightarrow> 's \<Rightarrow> bool)
                          \<Rightarrow> 'i set
                          \<Rightarrow> (('i \<Rightarrow> 's) \<Rightarrow> 'a \<Rightarrow> bool)
                          \<Rightarrow> ('i \<Rightarrow> 's) \<Rightarrow> ('i \<Rightarrow> 's) \<Rightarrow> 'a \<Rightarrow> bool"
where "otherwith Q I P \<sigma> \<sigma>' a \<equiv> (\<forall>i. i\<notin>I \<longrightarrow> Q (\<sigma> i) (\<sigma>' i)) \<and> P \<sigma> a"

lemma otherwithI [intro]:
  assumes other: "\<And>j. j\<notin>I \<Longrightarrow> Q (\<sigma> j) (\<sigma>' j)"
      and sync:  "P \<sigma> a"
    shows "otherwith Q I P \<sigma> \<sigma>' a"
  unfolding otherwith_def using assms by simp

lemma otherwithE [elim]:
  assumes "otherwith Q I P \<sigma> \<sigma>' a"
      and "\<lbrakk> P \<sigma> a; \<forall>j. j\<notin>I \<longrightarrow> Q (\<sigma> j) (\<sigma>' j) \<rbrakk> \<Longrightarrow> R \<sigma> \<sigma>' a"
    shows "R \<sigma> \<sigma>' a"
  using assms unfolding otherwith_def by simp

lemma otherwith_actionD [dest]:
  assumes "otherwith Q I P \<sigma> \<sigma>' a"
    shows "P \<sigma> a"
  using assms by auto

lemma otherwith_syncD [dest]:
  assumes "otherwith Q I P \<sigma> \<sigma>' a"
    shows "\<forall>j. j\<notin>I \<longrightarrow> Q (\<sigma> j) (\<sigma>' j)"
  using assms by auto

lemma otherwithEI [elim]:
  assumes "otherwith P I PO \<sigma> \<sigma>' a"
      and "\<And>\<sigma> a. PO \<sigma> a \<Longrightarrow> QO \<sigma> a"
    shows "otherwith P I QO \<sigma> \<sigma>' a"
  using assms(1) unfolding otherwith_def
  by (clarsimp elim!: assms(2))

lemma all_but:
  assumes "\<And>\<xi>. S \<xi> \<xi>"
      and "\<sigma>' i = \<sigma> i"
      and "\<forall>j. j \<noteq> i \<longrightarrow> S (\<sigma> j) (\<sigma>' j)"
    shows "\<forall>j. S (\<sigma> j) (\<sigma>' j)"
  using assms by metis

lemma all_but_eq [dest]:
  assumes "\<sigma>' i = \<sigma> i"
      and "\<forall>j. j \<noteq> i \<longrightarrow> \<sigma> j = \<sigma>' j"
    shows "\<sigma> = \<sigma>'"
  using assms by - (rule ext, metis)

text \<open>other\<close>

definition other :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 'i set \<Rightarrow> ('i \<Rightarrow> 's) \<Rightarrow> ('i \<Rightarrow> 's) \<Rightarrow> bool"
where "other P I \<sigma> \<sigma>' \<equiv> \<forall>i. if i\<in>I then \<sigma>' i = \<sigma> i else P (\<sigma> i) (\<sigma>' i)"

lemma otherI [intro]:
  assumes local: "\<And>i. i\<in>I \<Longrightarrow> \<sigma>' i = \<sigma> i"
      and other: "\<And>j. j\<notin>I \<Longrightarrow> P (\<sigma> j) (\<sigma>' j)"
    shows "other P I \<sigma> \<sigma>'"
  using assms unfolding other_def by clarsimp

lemma otherE [elim]:
  assumes "other P I \<sigma> \<sigma>'"
      and "\<lbrakk> \<forall>i\<in>I. \<sigma>' i = \<sigma> i; \<forall>j. j\<notin>I \<longrightarrow> P (\<sigma> j) (\<sigma>' j) \<rbrakk> \<Longrightarrow> R \<sigma> \<sigma>'"
    shows "R \<sigma> \<sigma>'"
  using assms unfolding other_def by simp

lemma other_localD [dest]:
  "other P {i} \<sigma> \<sigma>' \<Longrightarrow> \<sigma>' i = \<sigma> i"
  by auto

lemma other_otherD [dest]:
  "other P {i} \<sigma> \<sigma>' \<Longrightarrow> \<forall>j. j\<noteq>i \<longrightarrow> P (\<sigma> j) (\<sigma>' j)"
  by auto

lemma other_bothE [elim]:
  assumes "other P {i} \<sigma> \<sigma>'"
  obtains "\<sigma>' i = \<sigma> i" and "\<forall>j. j\<noteq>i \<longrightarrow> P (\<sigma> j) (\<sigma>' j)"
  using assms by auto

lemma weaken_local [elim]:
  assumes "other P I \<sigma> \<sigma>'"
      and PQ: "\<And>\<xi> \<xi>'. P \<xi> \<xi>' \<Longrightarrow> Q \<xi> \<xi>'"
    shows "other Q I \<sigma> \<sigma>'"
  using assms unfolding other_def by auto

definition global :: "((nat \<Rightarrow> 's) \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 's) \<times> 'local \<Rightarrow> bool"
where "global P \<equiv> (\<lambda>(\<sigma>, _). P \<sigma>)"

lemma globalsimp [simp]: "global P s = P (fst s)"
  unfolding global_def by (simp split: prod.split)

definition globala :: "((nat \<Rightarrow> 's, 'action) transition \<Rightarrow> bool)
                       \<Rightarrow> ((nat \<Rightarrow> 's) \<times> 'local, 'action) transition \<Rightarrow> bool"
where "globala P \<equiv> (\<lambda>((\<sigma>, _), a, (\<sigma>', _)). P (\<sigma>, a, \<sigma>'))"

lemma globalasimp [simp]: "globala P s = P (fst (fst s), fst (snd s), fst (snd (snd s)))"
  unfolding globala_def by (simp split: prod.split)

end

