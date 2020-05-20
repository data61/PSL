theory Weak_Bisimilarity_Implies_Equivalence
imports
  Weak_Logical_Equivalence
begin

section \<open>Weak Bisimilarity Implies Weak Logical Equivalence\<close>

context indexed_weak_nominal_ts
begin

  lemma weak_bisimilarity_implies_weak_equivalence_Act:
    assumes "\<And>P Q. P \<approx>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x"
    and "P \<approx>\<cdot> Q"
    \<comment> \<open>not needed: and @{prop "weak_formula x"}\<close>
    and "P \<Turnstile> \<langle>\<langle>\<alpha>\<rangle>\<rangle>x"
    shows "Q \<Turnstile> \<langle>\<langle>\<alpha>\<rangle>\<rangle>x"
  proof -
    have "finite (supp Q)"
      by (fact finite_supp)
    with \<open>P \<Turnstile> \<langle>\<langle>\<alpha>\<rangle>\<rangle>x\<close> obtain \<alpha>' x' P' where eq: "Act \<alpha> x = Act \<alpha>' x'" and trans: "P \<Rightarrow>\<langle>\<alpha>'\<rangle> P'" and valid: "P' \<Turnstile> x'" and fresh: "bn \<alpha>' \<sharp>* Q"
      by (metis valid_weak_action_modality_strong)

    from \<open>P \<approx>\<cdot> Q\<close> and fresh and trans obtain Q' where trans': "Q \<Rightarrow>\<langle>\<alpha>'\<rangle> Q'" and bisim': "P' \<approx>\<cdot> Q'"
      by (metis weakly_bisimilar_weak_simulation_step)

    from eq obtain p where px: "x' = p \<bullet> x"
      by (metis Act_eq_iff_perm)

    with valid have "-p \<bullet> P' \<Turnstile> x"
      by (metis permute_minus_cancel(1) valid_eqvt)
    moreover from bisim' have "(-p \<bullet> P') \<approx>\<cdot> (-p \<bullet> Q')"
      by (metis weakly_bisimilar_eqvt)
    ultimately have "-p \<bullet> Q' \<Turnstile> x"
      using \<open>\<And>P Q. P \<approx>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x\<close> by metis
    with px have "Q' \<Turnstile> x'"
      by (metis permute_minus_cancel(1) valid_eqvt)

    with eq and trans' show "Q \<Turnstile> \<langle>\<langle>\<alpha>\<rangle>\<rangle>x"
      unfolding valid_weak_action_modality by metis
  qed

  lemma weak_bisimilarity_implies_weak_equivalence_Pred:
    assumes "\<And>P Q. P \<approx>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x"
    and "P \<approx>\<cdot> Q"
    \<comment> \<open>not needed: and @{prop "weak_formula x"}\<close>
    and "P \<Turnstile> \<langle>\<langle>\<tau>\<rangle>\<rangle>(Conj (binsert (Pred \<phi>) (bsingleton x)))"
    shows "Q \<Turnstile> \<langle>\<langle>\<tau>\<rangle>\<rangle>(Conj (binsert (Pred \<phi>) (bsingleton x)))"
  proof -
    let ?c = "Conj (binsert (Pred \<phi>) (bsingleton x))"

    from \<open>P \<Turnstile> \<langle>\<langle>\<tau>\<rangle>\<rangle>?c\<close> obtain P' where trans: "P \<Rightarrow> P'" and valid: "P' \<Turnstile> ?c"
      using valid_weak_action_modality by auto

    have "bn \<tau>  \<sharp>* Q"
      by (simp add: fresh_star_def)
    with \<open>P \<approx>\<cdot> Q\<close> and trans obtain Q' where trans': "Q \<Rightarrow> Q'" and bisim': "P' \<approx>\<cdot> Q'"
      by (metis weakly_bisimilar_weak_simulation_step weak_transition_tau_iff)

    from valid have *: "P' \<turnstile> \<phi>" and **: "P' \<Turnstile> x"
      by (simp add: binsert.rep_eq)+

    from bisim' and * obtain Q'' where trans'': "Q' \<Rightarrow> Q''" and bisim'': "P' \<approx>\<cdot> Q''" and ***: "Q'' \<turnstile> \<phi>"
      by (metis is_weak_bisimulation_def weakly_bisimilar_is_weak_bisimulation)

    from bisim'' and ** have "Q'' \<Turnstile> x"
      using \<open>\<And>P Q. P \<approx>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x\<close> by metis
    with *** have "Q'' \<Turnstile> ?c"
      by (simp add: binsert.rep_eq)

    moreover from trans' and trans'' have "Q \<Rightarrow>\<langle>\<tau>\<rangle> Q''"
      by (metis tau_transition_trans weak_transition_tau_iff)

    ultimately show "Q \<Turnstile> \<langle>\<langle>\<tau>\<rangle>\<rangle>?c"
      unfolding valid_weak_action_modality by metis
  qed

  theorem weak_bisimilarity_implies_weak_equivalence: assumes "P \<approx>\<cdot> Q" shows "P \<equiv>\<cdot> Q"
  proof -
  {
    fix x :: "('idx, 'pred, 'act) formula"
    assume "weak_formula x"
      then have "\<And>P Q. P \<approx>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x"
    proof (induct rule: weak_formula.induct)
      case (wf_Conj xset) then show ?case
        by simp
    next
      case (wf_Not x) then show ?case
        by simp
    next
      case (wf_Act x \<alpha>) then show ?case
        by (metis weakly_bisimilar_symp weak_bisimilarity_implies_weak_equivalence_Act sympE)
    next
      case (wf_Pred x \<phi>) then show ?case
        by (metis weakly_bisimilar_symp weak_bisimilarity_implies_weak_equivalence_Pred sympE)
      qed
    }
    with assms show ?thesis
      unfolding weakly_logically_equivalent_def by simp
  qed

end

end
