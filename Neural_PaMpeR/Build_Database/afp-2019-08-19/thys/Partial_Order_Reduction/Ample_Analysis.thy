section \<open>Static Analysis for Partial Order Reduction\<close>

theory Ample_Analysis
imports
  Ample_Abstract
begin

  locale transition_system_ample =
    transition_system_sticky ex en init int sticky +
    transition_system_interpreted_traces ex en int ind
    for ex :: "'action \<Rightarrow> 'state \<Rightarrow> 'state"
    and en :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    and init :: "'state \<Rightarrow> bool"
    and int :: "'state \<Rightarrow> 'interpretation"
    and sticky :: "'action set"
    and ind :: "'action \<Rightarrow> 'action \<Rightarrow> bool"
  begin

    sublocale ample_base "ex" "en" "int" "ind" "scut\<inverse>\<inverse>" by unfold_locales

    lemma restrict_ample_set:
      assumes "s \<in> nodes"
      assumes "A \<inter> {a. en a s} \<noteq> {}" "A \<inter> {a. en a s} \<inter> sticky = {}"
      assumes "Ind (A \<inter> {a. en a s}) (executable - A)"
      assumes "\<And> w. path w s \<Longrightarrow> A \<inter> {a. en a s} \<inter> set w = {} \<Longrightarrow> A \<inter> set w = {}"
      shows "ample_set s (A \<inter> {a. en a s})"
    unfolding ample_set_def
    proof (intro conjI allI impI)
      show "A \<inter> {a. en a s} \<subseteq> {a. en a s}" by simp
    next
      show "A \<inter> {a. en a s} \<noteq> {}" using assms(2) by this
    next
      fix a
      assume 1: "a \<in> A \<inter> {a. en a s}"
      show "scut\<inverse>\<inverse> (ex a s) s"
      proof (rule no_cut_scut)
        show "s \<in> nodes" using assms(1) by this
        show "en a s" using 1 by simp
        show "a \<notin> sticky" using assms(3) 1 by auto
      qed
    next
      have 1: "A \<inter> {a. en a s} \<subseteq> executable" using executable assms(1) by blast
      show "A \<inter> {a. en a s} \<subseteq> invisible" using executable_visible_sticky assms(3) 1 by blast
    next
      fix w
      assume 1: "path w s" "A \<inter> {a. en a s} \<inter> set w = {}"
      have 2: "A \<inter> set w = {}" using assms(5) 1 by this
      have 3: "set w \<subseteq> executable" using assms(1) 1(1) by rule
      show "Ind (A \<inter> {a. en a s}) (set w)" using assms(4) 2 3 by blast
    qed

  end

  locale transition_system_concurrent =
    transition_system_initial ex en init
    for ex :: "'action \<Rightarrow> 'state \<Rightarrow> 'state"
    and en :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    and init :: "'state \<Rightarrow> bool"
    +
    fixes procs :: "'state \<Rightarrow> 'process set"
    fixes pac :: "'process \<Rightarrow> 'action set"
    fixes psen :: "'process \<Rightarrow> 'state \<Rightarrow> 'action set"
    assumes procs_finite: "s \<in> nodes \<Longrightarrow> finite (procs s)"
    assumes psen_en: "s \<in> nodes \<Longrightarrow> pac p \<inter> {a. en a s} \<subseteq> psen p s"
    assumes psen_ex: "s \<in> nodes \<Longrightarrow> a \<in> {a. en a s} - pac p \<Longrightarrow> psen p (ex a s) = psen p s"
  begin

    lemma psen_fin_word:
      assumes "s \<in> nodes" "path w s" "pac p \<inter> set w = {}"
      shows "psen p (target w s) = psen p s"
    using assms(2, 1, 3)
    proof induct
      case (nil s)
      show ?case by simp
    next
      case (cons a s w)
      have 1: "ex a s \<in> nodes" using cons(4, 1) by rule
      have "psen p (target (a # w) s) = psen p (target w (ex a s))" by simp
      also have "\<dots> = psen p (ex a s)" using cons 1 by simp
      also have "\<dots> = psen p s" using psen_ex cons by simp
      finally show ?case by this
    qed

    lemma en_fin_word:
      assumes "\<And> r a b. r \<in> nodes \<Longrightarrow> a \<in> psen p s - {a. en a s} \<Longrightarrow> b \<in> {a. en a r} - pac p \<Longrightarrow>
        en a (ex b r) \<Longrightarrow> en a r"
      assumes "s \<in> nodes" "path w s" "pac p \<inter> set w = {}"
      shows "pac p \<inter> {a. en a (target w s)} \<subseteq> pac p \<inter> {a. en a s}"
    using assms
    proof (induct w rule: rev_induct)
      case Nil
      show ?case by simp
    next
      case (snoc b w)
      show ?case
      proof (safe, rule ccontr)
        fix a
        assume 2: "a \<in> pac p" "en a (target (w @ [b]) s)" "\<not> en a s"
        have 3: "a \<in> psen p s"
        proof -
          have 3: "psen p (target (w @ [b]) s) = psen p s" using psen_fin_word snoc(3, 4, 5) by this
          have 4: "target (w @ [b]) s \<in> nodes" using snoc(3, 4) by rule
          have 5: "a \<in> psen p (target (w @ [b]) s)" using psen_en 4 2(1, 2) by auto
          show ?thesis using 2(1) 3 5 by auto
        qed
        have 4: "en a (target w s)"
        proof (rule snoc(2))
          show "target w s \<in> nodes" using snoc(3, 4) by auto
          show "a \<in> psen p s - {a. en a s}" using 2(3) 3 by simp
          show "b \<in> {a. en a (target w s)} - pac p" using snoc(4, 5) by auto
          show "en a (ex b (target w s))" using 2(2) by simp
        qed
        have 5: "pac p \<inter> {a. en a (target w s)} \<subseteq> pac p \<inter> {a. en a s}"
        proof (rule snoc(1))
          show "\<And> r a b. r \<in> nodes \<Longrightarrow> a \<in> psen p s - {a. en a s} \<Longrightarrow> b \<in> {a. en a r} - pac p \<Longrightarrow>
            en a (ex b r) \<Longrightarrow> en a r" using snoc(2) by this
          show "s \<in> nodes" using snoc(3) by this
          show "path w s" using snoc(4) by auto
          show "pac p \<inter> set w = {}" using snoc(5) by auto
        qed
        have 6: "en a s" using 2(1) 4 5 by auto
        show "False" using 2(3) 6 by simp
      qed
    qed

    lemma pac_en_blocked:
      assumes "\<And> r a b. r \<in> nodes \<Longrightarrow> a \<in> psen p s - {a. en a s} \<Longrightarrow> b \<in> {a. en a r} - pac p \<Longrightarrow>
        en a (ex b r) \<Longrightarrow> en a r"
      assumes "s \<in> nodes" "path w s" "pac p \<inter> {a. en a s} \<inter> set w = {}"
      shows "pac p \<inter> set w = {}"
      using words_fin_blocked en_fin_word assms by metis

    abbreviation "proc a \<equiv> {p. a \<in> pac p}"
    abbreviation "Proc A \<equiv> \<Union> a \<in> A. proc a"

    lemma psen_simple:
      assumes "Proc (psen p s) = {p}"
      assumes "\<And> r a b. r \<in> nodes \<Longrightarrow> a \<in> psen p s - {a. en a s} \<Longrightarrow> en b r \<Longrightarrow>
        proc a \<inter> proc b = {} \<Longrightarrow> en a (ex b r) \<Longrightarrow> en a r"
      shows "\<And> r a b. r \<in> nodes \<Longrightarrow> a \<in> psen p s - {a. en a s} \<Longrightarrow> b \<in> {a. en a r} - pac p \<Longrightarrow>
        en a (ex b r) \<Longrightarrow> en a r"
      using assms by force

  end

end
