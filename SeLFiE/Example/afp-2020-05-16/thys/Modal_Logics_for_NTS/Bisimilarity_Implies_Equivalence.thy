theory Bisimilarity_Implies_Equivalence
imports
  Logical_Equivalence
begin

section \<open>Bisimilarity Implies Logical Equivalence\<close>

context indexed_nominal_ts
begin

  lemma bisimilarity_implies_equivalence_Act:
    assumes "\<And>P Q. P \<sim>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x"
    and "P \<sim>\<cdot> Q"
    and "P \<Turnstile> Act \<alpha> x"
    shows "Q \<Turnstile> Act \<alpha> x"
  proof -
    have "finite (supp Q)"
      by (fact finite_supp)
    with \<open>P \<Turnstile> Act \<alpha> x\<close> obtain \<alpha>' x' P' where eq: "Act \<alpha> x = Act \<alpha>' x'" and trans: "P \<rightarrow> \<langle>\<alpha>',P'\<rangle>" and valid: "P' \<Turnstile> x'" and fresh: "bn \<alpha>' \<sharp>* Q"
      by (metis valid_Act_strong)

    from \<open>P \<sim>\<cdot> Q\<close> and fresh and trans obtain Q' where trans': "Q \<rightarrow> \<langle>\<alpha>',Q'\<rangle>" and bisim': "P' \<sim>\<cdot> Q'"
      by (metis bisimilar_simulation_step)

    from eq obtain p where px: "x' = p \<bullet> x"
      by (metis Act_eq_iff_perm)

    with valid have "-p \<bullet> P' \<Turnstile> x"
      by (metis permute_minus_cancel(1) valid_eqvt)
    moreover from bisim' have "(-p \<bullet> P') \<sim>\<cdot> (-p \<bullet> Q')"
      by (metis bisimilar_eqvt)
    ultimately have "-p \<bullet> Q' \<Turnstile> x"
      using \<open>\<And>P Q. P \<sim>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x\<close> by metis
    with px have "Q' \<Turnstile> x'"
      by (metis permute_minus_cancel(1) valid_eqvt)

    with eq and trans' show "Q \<Turnstile> Act \<alpha> x"
      unfolding valid_Act by metis
  qed

  theorem bisimilarity_implies_equivalence: assumes "P \<sim>\<cdot> Q" shows "P =\<cdot> Q"
  unfolding logically_equivalent_def proof
    fix x :: "('idx, 'pred, 'act) formula"
    from assms show "P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x"
    proof (induction x arbitrary: P Q)
      case (Conj xset) then show ?case
        by simp
    next
      case Not then show ?case
        by simp
    next
      case Pred then show ?case
        by (metis bisimilar_is_bisimulation is_bisimulation_def symp_def valid_Pred)
    next
      case (Act \<alpha> x) then show ?case
        by (metis bisimilar_symp bisimilarity_implies_equivalence_Act sympE)
    qed
  qed

end

end
