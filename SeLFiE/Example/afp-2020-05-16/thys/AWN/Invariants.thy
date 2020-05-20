(*  Title:       Invariants.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Reachability and Invariance"

theory Invariants
imports Lib TransitionSystems
begin

subsection Reachability

text \<open>
  A state is `reachable' under @{term I} if either it is the initial state, or it is the
  destination of a transition whose action satisfies @{term I} from a reachable state.
  The `standard' definition of reachability is recovered by setting @{term I} to @{term TT}.
\<close>

inductive_set reachable
  for A :: "('s, 'a) automaton"
  and I :: "'a \<Rightarrow> bool"
where
    reachable_init: "s \<in> init A \<Longrightarrow> s \<in> reachable A I"
  | reachable_step: "\<lbrakk> s \<in> reachable A I; (s, a, s') \<in> trans A; I a \<rbrakk> \<Longrightarrow> s' \<in> reachable A I"

inductive_cases reachable_icases: "s \<in> reachable A I"

lemma reachable_pair_induct [consumes, case_names init step]:
  assumes "(\<xi>, p) \<in> reachable A I"
      and "\<And>\<xi> p. (\<xi>, p) \<in> init A \<Longrightarrow> P \<xi> p"
      and "(\<And>\<xi> p \<xi>' p' a. \<lbrakk> (\<xi>, p) \<in> reachable A I; P \<xi> p;
                            ((\<xi>, p), a, (\<xi>', p')) \<in> trans A; I a \<rbrakk> \<Longrightarrow> P \<xi>' p')"
    shows "P \<xi> p"
  using assms(1) proof (induction "(\<xi>, p)" arbitrary: \<xi> p)
    fix \<xi> p
    assume "(\<xi>, p) \<in> init A"
    with assms(2) show "P \<xi> p" .
  next
    fix s a \<xi>' p'
    assume "s \<in> reachable A I"
       and tr: "(s, a, (\<xi>', p')) \<in> trans A"
       and "I a"
       and IH: "\<And>\<xi> p. s = (\<xi>, p) \<Longrightarrow> P \<xi> p"
    from this(1) obtain \<xi> p where "s = (\<xi>, p)"
                              and "(\<xi>, p) \<in> reachable A I"
      by (metis prod.collapse)
    note this(2)
    moreover from IH and \<open>s = (\<xi>, p)\<close> have "P \<xi> p" .
    moreover from tr and \<open>s = (\<xi>, p)\<close> have "((\<xi>, p), a, (\<xi>', p')) \<in> trans A" by simp
    ultimately show "P \<xi>' p'"
      using \<open>I a\<close> by (rule assms(3))
  qed

lemma reachable_weakenE [elim]:
  assumes "s \<in> reachable A P"
      and PQ: "\<And>a. P a \<Longrightarrow> Q a"
    shows "s \<in> reachable A Q"
  using assms(1)
  proof (induction)
    fix s assume "s \<in> init A"
    thus "s \<in> reachable A Q" ..
  next
    fix s a s'
    assume "s \<in> reachable A P"
       and "s \<in> reachable A Q"
       and "(s, a, s') \<in> trans A"
       and "P a"
    from \<open>P a\<close> have "Q a" by (rule PQ)
    with \<open>s \<in> reachable A Q\<close> and \<open>(s, a, s') \<in> trans A\<close> show "s' \<in> reachable A Q" ..
  qed

lemma reachable_weaken_TT [elim]:
  assumes "s \<in> reachable A I"
    shows "s \<in> reachable A TT"
  using assms by rule simp

lemma init_empty_reachable_empty:
  assumes "init A = {}"
    shows "reachable A I = {}"
  proof (rule ccontr)
    assume "reachable A I \<noteq> {}"
    then obtain s where "s \<in> reachable A I" by auto
    thus False
    proof (induction rule: reachable.induct)
      fix s
      assume "s \<in> init A"
      with \<open>init A = {}\<close> show False by simp
    qed
  qed

subsection Invariance

definition invariant
  :: "('s, 'a) automaton \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool"
  ("_ \<TTurnstile> (1'(_ \<rightarrow>')/ _)" [100, 0, 9] 8)
where
  "(A \<TTurnstile> (I \<rightarrow>) P) = (\<forall>s\<in>reachable A I. P s)"

abbreviation
  any_invariant
  :: "('s, 'a) automaton \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool"
  ("_ \<TTurnstile> _" [100, 9] 8)
where
  "(A \<TTurnstile> P) \<equiv> (A \<TTurnstile> (TT \<rightarrow>) P)"

lemma invariantI [intro]:
  assumes init: "\<And>s. s \<in> init A \<Longrightarrow> P s"
      and step: "\<And>s a s'. \<lbrakk> s \<in> reachable A I; P s; (s, a, s') \<in> trans A; I a \<rbrakk> \<Longrightarrow> P s'"
    shows "A \<TTurnstile> (I \<rightarrow>) P"
  unfolding invariant_def
  proof
       fix s
    assume "s \<in> reachable A I"
      thus "P s"
    proof induction
      fix s assume "s \<in> init A"
      thus "P s" by (rule init)
    next
      fix s a s'
      assume "s \<in> reachable A I"
         and "P s"
         and "(s, a, s') \<in> trans A"
         and "I a"
        thus "P s'" by (rule step)
    qed
  qed

lemma invariant_pairI [intro]:
  assumes init: "\<And>\<xi> p. (\<xi>, p) \<in> init A \<Longrightarrow> P (\<xi>, p)"
      and step: "\<And>\<xi> p \<xi>' p' a.
                   \<lbrakk> (\<xi>, p) \<in> reachable A I; P (\<xi>, p); ((\<xi>, p), a, (\<xi>', p')) \<in> trans A; I a \<rbrakk>
                   \<Longrightarrow> P (\<xi>', p')"
    shows "A \<TTurnstile> (I \<rightarrow>) P"
  using assms by auto

lemma invariant_arbitraryI:
  assumes "\<And>s. s \<in> reachable A I \<Longrightarrow> P s"
    shows "A \<TTurnstile> (I \<rightarrow>) P"
  using assms unfolding invariant_def by simp

lemma invariantD [dest]:
  assumes "A \<TTurnstile> (I \<rightarrow>) P"
      and "s \<in> reachable A I"
    shows "P s"
  using assms unfolding invariant_def by blast

lemma invariant_initE [elim]:
  assumes invP: "A \<TTurnstile> (I \<rightarrow>) P"
      and init: "s \<in> init A"
    shows "P s"
  proof -
    from init have "s \<in> reachable A I" ..
    with invP show ?thesis ..
  qed

lemma invariant_weakenE [elim]:
  fixes T \<sigma> P Q
  assumes invP: "A \<TTurnstile> (PI \<rightarrow>) P"
      and PQ:   "\<And>s. P s \<Longrightarrow> Q s"
      and QIPI: "\<And>a. QI a \<Longrightarrow> PI a"
    shows       "A \<TTurnstile> (QI \<rightarrow>) Q"
  proof
    fix s
    assume "s \<in> init A"
    with invP have "P s" ..
    thus "Q s" by (rule PQ)
  next
    fix s a s'
    assume "s \<in> reachable A QI"
       and "(s, a, s') \<in> trans A"
       and "QI a"
    from \<open>QI a\<close> have "PI a" by (rule QIPI)
    from \<open>s \<in> reachable A QI\<close> and QIPI have "s \<in> reachable A PI" ..
    hence "s' \<in> reachable A PI" using \<open>(s, a, s') \<in> trans A\<close> and \<open>PI a\<close> ..
    with invP have "P s'" ..
    thus "Q s'" by (rule PQ)
  qed

definition
  step_invariant
  :: "('s, 'a) automaton \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> (('s, 'a) transition \<Rightarrow> bool) \<Rightarrow> bool"
  ("_ \<TTurnstile>\<^sub>A (1'(_ \<rightarrow>')/ _)" [100, 0, 0] 8)
where
  "(A \<TTurnstile>\<^sub>A (I \<rightarrow>) P) = (\<forall>a. I a \<longrightarrow> (\<forall>s\<in>reachable A I. (\<forall>s'.(s, a, s') \<in> trans A \<longrightarrow> P (s, a, s'))))"

lemma invariant_restrict_inD [dest]:
  assumes "A \<TTurnstile> (TT \<rightarrow>) P"
    shows "A \<TTurnstile> (QI \<rightarrow>) P"
  using assms by auto

abbreviation
  any_step_invariant
  :: "('s, 'a) automaton \<Rightarrow> (('s, 'a) transition \<Rightarrow> bool) \<Rightarrow> bool"
  ("_ \<TTurnstile>\<^sub>A _" [100, 9] 8)
where
  "(A \<TTurnstile>\<^sub>A P) \<equiv> (A \<TTurnstile>\<^sub>A (TT \<rightarrow>) P)"

lemma step_invariant_true:
  "p \<TTurnstile>\<^sub>A (\<lambda>(s, a, s'). True)"
  unfolding step_invariant_def by simp

lemma step_invariantI [intro]:
  assumes *: "\<And>s a s'. \<lbrakk> s\<in>reachable A I; (s, a, s')\<in>trans A; I a \<rbrakk> \<Longrightarrow> P (s, a, s')"
    shows "A \<TTurnstile>\<^sub>A (I \<rightarrow>) P"
  unfolding step_invariant_def
  using assms by auto

lemma step_invariantD [dest]:
  assumes "A \<TTurnstile>\<^sub>A (I \<rightarrow>) P"
      and "s\<in>reachable A I"
      and "(s, a, s') \<in> trans A"
      and "I a"
    shows "P (s, a, s')"
  using assms unfolding step_invariant_def by blast

lemma step_invariantE [elim]:
    fixes T \<sigma> P I s a s'
  assumes "A \<TTurnstile>\<^sub>A (I \<rightarrow>) P"
      and "s\<in>reachable A I"
      and "(s, a, s') \<in> trans A"
      and "I a"
      and "P (s, a, s') \<Longrightarrow> Q"
    shows "Q"
  using assms by auto

lemma step_invariant_pairI [intro]:
  assumes *: "\<And>\<xi> p \<xi>' p' a.
              \<lbrakk> (\<xi>, p) \<in> reachable A I; ((\<xi>, p), a, (\<xi>', p')) \<in> trans A; I a \<rbrakk>
                                                       \<Longrightarrow> P ((\<xi>, p), a, (\<xi>', p'))"
    shows "A \<TTurnstile>\<^sub>A (I \<rightarrow>) P"
  using assms by auto

lemma step_invariant_arbitraryI:
  assumes "\<And>\<xi> p a \<xi>' p'. \<lbrakk> (\<xi>, p) \<in> reachable A I; ((\<xi>, p), a, (\<xi>', p')) \<in> trans A; I a \<rbrakk>
           \<Longrightarrow> P ((\<xi>, p), a, (\<xi>', p'))"
    shows "A \<TTurnstile>\<^sub>A (I \<rightarrow>) P"
  using assms by auto

lemma step_invariant_weakenE [elim!]:
  fixes T \<sigma> P Q
  assumes invP: "A \<TTurnstile>\<^sub>A (PI \<rightarrow>) P"
      and PQ:   "\<And>t. P t \<Longrightarrow> Q t"
      and QIPI: "\<And>a. QI a \<Longrightarrow> PI a"
    shows       "A \<TTurnstile>\<^sub>A (QI \<rightarrow>) Q"
  proof
    fix s a s'
    assume "s \<in> reachable A QI"
       and "(s, a, s') \<in> trans A"
       and "QI a"
    from \<open>QI a\<close> have "PI a" by (rule QIPI)
    from \<open>s \<in> reachable A QI\<close> have "s \<in> reachable A PI" using QIPI ..
    with invP have "P (s, a, s')" using \<open>(s, a, s') \<in> trans A\<close> \<open>PI a\<close> ..
    thus "Q (s, a, s')" by (rule PQ)
  qed

lemma step_invariant_weaken_with_invariantE [elim]:
  assumes pinv: "A \<TTurnstile> (I \<rightarrow>) P"
      and qinv: "A \<TTurnstile>\<^sub>A (I \<rightarrow>) Q"
      and wr: "\<And>s a s'. \<lbrakk> P s; P s'; Q (s, a, s'); I a \<rbrakk> \<Longrightarrow> R (s, a, s')"
    shows "A \<TTurnstile>\<^sub>A (I \<rightarrow>) R"
  proof
    fix s a s'
    assume sr: "s \<in> reachable A I"
       and tr: "(s, a, s') \<in> trans A"
       and "I a"
    hence "s' \<in> reachable A I" ..
    with pinv have "P s'" ..
    from pinv and sr have "P s" ..
    from qinv sr tr \<open>I a\<close> have "Q (s, a, s')" ..
    with \<open>P s\<close> and \<open>P s'\<close> show "R (s, a, s')" using \<open>I a\<close> by (rule wr)
  qed

lemma step_to_invariantI:
  assumes sinv: "A \<TTurnstile>\<^sub>A (I \<rightarrow>) Q"
      and init: "\<And>s. s \<in> init A \<Longrightarrow> P s"
      and step: "\<And>s s' a.
                   \<lbrakk> s \<in> reachable A I;
                     P s;
                     Q (s, a, s');
                     I a \<rbrakk> \<Longrightarrow> P s'"
    shows "A \<TTurnstile> (I \<rightarrow>) P"
  proof
    fix s assume "s \<in> init A" thus "P s" by (rule init)
  next
    fix s s' a
    assume "s \<in> reachable A I"
       and "P s"
       and "(s, a, s') \<in> trans A"
       and "I a"
      show "P s'"
    proof -
      from sinv and \<open>s\<in>reachable A I\<close> and \<open>(s, a, s')\<in>trans A\<close> and \<open>I a\<close> have "Q (s, a, s')" ..
      with \<open>s\<in>reachable A I\<close> and \<open>P s\<close> show "P s'" using \<open>I a\<close> by (rule step)
    qed
  qed

end

