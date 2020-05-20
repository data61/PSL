theory Weak_Transition_System
imports
  Transition_System
begin

section \<open>Nominal Transition Systems and Bisimulations with Unobservable Transitions\<close>

subsection \<open>Nominal transition systems with unobservable transitions\<close>

locale weak_nominal_ts = nominal_ts satisfies transition
  for satisfies :: "'state::fs \<Rightarrow> 'pred::fs \<Rightarrow> bool" (infix "\<turnstile>" 70)
  and transition :: "'state \<Rightarrow> ('act::bn,'state) residual \<Rightarrow> bool" (infix "\<rightarrow>" 70) +
  fixes \<tau> :: 'act
  assumes tau_eqvt [eqvt]: "p \<bullet> \<tau> = \<tau>"
begin

  lemma bn_tau_empty [simp]: "bn \<tau> = {}"
  using bn_eqvt bn_finite tau_eqvt by (metis eqvt_def supp_finite_atom_set supp_fun_eqvt)

  lemma bn_tau_fresh [simp]: "bn \<tau> \<sharp>* P"
  by (simp add: fresh_star_def)

  inductive tau_transition :: "'state \<Rightarrow> 'state \<Rightarrow> bool" (infix "\<Rightarrow>" 70) where
    tau_refl [simp]: "P \<Rightarrow> P"
  | tau_step: "\<lbrakk> P \<rightarrow> \<langle>\<tau>, P'\<rangle>; P' \<Rightarrow> P'' \<rbrakk> \<Longrightarrow> P \<Rightarrow> P''"

  definition observable_transition :: "'state \<Rightarrow> 'act \<Rightarrow> 'state \<Rightarrow> bool" ("_/ \<Rightarrow>{_}/ _" [70, 70, 71] 71) where
    "P \<Rightarrow>{\<alpha>} P' \<equiv> \<exists>Q Q'. P \<Rightarrow> Q \<and> Q \<rightarrow> \<langle>\<alpha>, Q'\<rangle> \<and> Q' \<Rightarrow> P'"

  definition weak_transition :: "'state \<Rightarrow> 'act \<Rightarrow> 'state \<Rightarrow> bool" ("_/ \<Rightarrow>\<langle>_\<rangle>/ _" [70, 70, 71] 71) where
    "P \<Rightarrow>\<langle>\<alpha>\<rangle> P' \<equiv> if \<alpha> = \<tau> then P \<Rightarrow> P' else P \<Rightarrow>{\<alpha>} P'"

  text \<open>The transition relations defined above are equivariant.\<close>

  lemma tau_transition_eqvt (*[eqvt]*):
    assumes "P \<Rightarrow> P'" shows "p \<bullet> P \<Rightarrow> p \<bullet> P'"
  using assms proof (induction)
    case (tau_refl P) show ?case
      by (fact tau_transition.tau_refl)
  next
    case (tau_step P P' P'')
      from \<open>P \<rightarrow> \<langle>\<tau>,P'\<rangle>\<close> have "p \<bullet> P \<rightarrow> \<langle>\<tau>,p \<bullet> P'\<rangle>"
        using tau_eqvt transition_eqvt' by fastforce
      with \<open>p \<bullet> P' \<Rightarrow> p \<bullet> P''\<close> show ?case
        using tau_transition.tau_step by blast
  qed

  lemma observable_transition_eqvt (*[eqvt]*):
    assumes "P \<Rightarrow>{\<alpha>} P'" shows "p \<bullet> P \<Rightarrow>{p \<bullet> \<alpha>} p \<bullet> P'"
  using assms unfolding observable_transition_def by (metis transition_eqvt' tau_transition_eqvt)

  lemma weak_transition_eqvt (*[eqvt]*):
    assumes "P \<Rightarrow>\<langle>\<alpha>\<rangle> P'" shows "p \<bullet> P \<Rightarrow>\<langle>p \<bullet> \<alpha>\<rangle> p \<bullet> P'"
  using assms unfolding weak_transition_def by (metis (full_types) observable_transition_eqvt permute_minus_cancel(2) tau_eqvt tau_transition_eqvt)

  text \<open>Additional lemmas about @{const tau_transition}, @{const observable_transition} and
  @{const weak_transition}.\<close>

  lemma tau_transition_trans:
    assumes "P \<Rightarrow> Q" and "Q \<Rightarrow> R"
    shows "P \<Rightarrow> R"
  using assms by (induction, auto simp add: tau_step)

  lemma observable_transitionI:
    assumes "P \<Rightarrow> Q" and "Q \<rightarrow> \<langle>\<alpha>, Q'\<rangle>" and "Q' \<Rightarrow> P'"
    shows "P \<Rightarrow>{\<alpha>} P'"
  using assms observable_transition_def by blast

  lemma observable_transition_stepI [simp]:
    assumes "P \<rightarrow> \<langle>\<alpha>, P'\<rangle>"
    shows "P \<Rightarrow>{\<alpha>} P'"
  using assms observable_transitionI tau_refl by blast

  lemma observable_tau_transition:
    assumes "P \<Rightarrow>{\<tau>} P'"
    shows "P \<Rightarrow> P'"
  proof -
    from \<open>P \<Rightarrow>{\<tau>} P'\<close> obtain Q Q' where "P \<Rightarrow> Q" and "Q \<rightarrow> \<langle>\<tau>, Q'\<rangle>" and "Q' \<Rightarrow> P'"
      unfolding observable_transition_def by blast
    then show ?thesis
      by (metis tau_step tau_transition_trans)
  qed

  lemma weak_transition_tau_iff [simp]:
    "P \<Rightarrow>\<langle>\<tau>\<rangle> P' \<longleftrightarrow> P \<Rightarrow> P'"
  by (simp add: weak_transition_def)

  lemma weak_transition_not_tau_iff [simp]:
    assumes "\<alpha> \<noteq> \<tau>"
    shows "P \<Rightarrow>\<langle>\<alpha>\<rangle> P' \<longleftrightarrow> P \<Rightarrow>{\<alpha>} P'"
  using assms by (simp add: weak_transition_def)

  lemma weak_transition_stepI [simp]:
    assumes "P \<Rightarrow>{\<alpha>} P'"
    shows "P \<Rightarrow>\<langle>\<alpha>\<rangle> P'"
  using assms by (cases "\<alpha> = \<tau>", simp_all add: observable_tau_transition)

  lemma weak_transition_weakI:
    assumes "P \<Rightarrow> Q" and "Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q'" and "Q' \<Rightarrow> P'"
    shows "P \<Rightarrow>\<langle>\<alpha>\<rangle> P'"
  proof (cases "\<alpha> = \<tau>")
    case True with assms show ?thesis
      by (metis tau_transition_trans weak_transition_tau_iff)
  next
    case False with assms show ?thesis
      using observable_transition_def tau_transition_trans weak_transition_not_tau_iff by blast
  qed

end


subsection \<open>Weak bisimulations\<close>

context weak_nominal_ts
begin

  definition is_weak_bisimulation :: "('state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> bool" where
    "is_weak_bisimulation R \<equiv>
      symp R \<and>
      \<comment> \<open>weak static implication\<close>
      (\<forall>P Q \<phi>. R P Q \<and> P \<turnstile> \<phi> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow> Q' \<and> R P Q' \<and> Q' \<turnstile> \<phi>)) \<and>
      \<comment> \<open>weak simulation\<close>
      (\<forall>P Q. R P Q \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* Q \<longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q' \<and> R P' Q')))"

  definition weakly_bisimilar :: "'state \<Rightarrow> 'state \<Rightarrow> bool"  (infix "\<approx>\<cdot>" 100) where
    "P \<approx>\<cdot> Q \<equiv> \<exists>R. is_weak_bisimulation R \<and> R P Q"

  text \<open>@{const weakly_bisimilar} is an equivariant equivalence relation.\<close>

  lemma is_weak_bisimulation_eqvt (*[eqvt]*):
    assumes "is_weak_bisimulation R" shows "is_weak_bisimulation (p \<bullet> R)"
  using assms unfolding is_weak_bisimulation_def
  proof (clarify)
    assume 1: "symp R"
    assume 2: "\<forall>P Q \<phi>. R P Q \<and> P \<turnstile> \<phi> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow> Q' \<and> R P Q' \<and> Q' \<turnstile> \<phi>)"
    assume 3: "\<forall>P Q. R P Q \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* Q \<longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q' \<and> R P' Q'))"
    have "symp (p \<bullet> R)" (is ?S)
      using 1 by (simp add: symp_eqvt)
    moreover have "\<forall>P Q \<phi>. (p \<bullet> R) P Q \<and> P \<turnstile> \<phi> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow> Q' \<and> (p \<bullet> R) P Q' \<and> Q' \<turnstile> \<phi>)" (is ?T)
      proof (clarify)
        fix P Q \<phi>
        assume pR: "(p \<bullet> R) P Q" and phi: "P \<turnstile> \<phi>"
        from pR have "R (-p \<bullet> P) (-p \<bullet> Q)"
          by (simp add: eqvt_lambda permute_bool_def unpermute_def)
        moreover from phi have "(-p \<bullet> P) \<turnstile> (-p \<bullet> \<phi>)"
          by (metis satisfies_eqvt)
        ultimately obtain Q' where *: "-p \<bullet> Q \<Rightarrow> Q'" and **: "R (-p \<bullet> P) Q'" and ***: "Q' \<turnstile> (-p \<bullet> \<phi>)"
          using 2 by blast
        from * have "Q \<Rightarrow> p \<bullet> Q'"
          by (metis permute_minus_cancel(1) tau_transition_eqvt)
        moreover from ** have "(p \<bullet> R) P (p \<bullet> Q')"
          by (simp add: eqvt_lambda permute_bool_def unpermute_def)
        moreover from *** have "p \<bullet> Q' \<turnstile> \<phi>"
          by (metis permute_minus_cancel(1) satisfies_eqvt)
        ultimately show "\<exists>Q'. Q \<Rightarrow> Q' \<and> (p \<bullet> R) P Q' \<and> Q' \<turnstile> \<phi>"
          by metis
      qed
    moreover have "\<forall>P Q. (p \<bullet> R) P Q \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* Q \<longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q' \<and> (p \<bullet> R) P' Q'))" (is ?U)
      proof (clarify)
        fix P Q \<alpha> P'
        assume *: "(p \<bullet> R) P Q" and **: "bn \<alpha> \<sharp>* Q" and ***: "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
        from * have "R (-p \<bullet> P) (-p \<bullet> Q)"
          by (simp add: eqvt_lambda permute_bool_def unpermute_def)
        moreover have "bn (-p \<bullet> \<alpha>) \<sharp>* (-p \<bullet> Q)"
          using ** by (metis bn_eqvt fresh_star_permute_iff)
        moreover have "-p \<bullet> P \<rightarrow> \<langle>-p \<bullet> \<alpha>, -p \<bullet> P'\<rangle>"
          using *** by (metis transition_eqvt')
        ultimately obtain Q' where T: "-p \<bullet> Q \<Rightarrow>\<langle>-p \<bullet> \<alpha>\<rangle> Q'" and R: "R (-p \<bullet> P') Q'"
          using 3 by metis
        from T have "Q \<Rightarrow>\<langle>\<alpha>\<rangle> (p \<bullet> Q')"
          by (metis permute_minus_cancel(1) weak_transition_eqvt)
        moreover from R have "(p \<bullet> R) P' (p \<bullet> Q')"
          by (metis eqvt_apply eqvt_lambda permute_bool_def unpermute_def)
        ultimately show "\<exists>Q'. Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q' \<and> (p \<bullet> R) P' Q'"
          by metis
      qed
    ultimately show "?S \<and> ?T \<and> ?U" by simp
  qed

  lemma weakly_bisimilar_eqvt (*[eqvt]*):
    assumes "P \<approx>\<cdot> Q" shows "(p \<bullet> P) \<approx>\<cdot> (p \<bullet> Q)"
  proof -
    from assms obtain R where *: "is_weak_bisimulation R \<and> R P Q"
      unfolding weakly_bisimilar_def ..
    then have "is_weak_bisimulation (p \<bullet> R)"
      by (simp add: is_weak_bisimulation_eqvt)
    moreover from "*" have "(p \<bullet> R) (p \<bullet> P) (p \<bullet> Q)"
      by (metis eqvt_apply permute_boolI)
    ultimately show "(p \<bullet> P) \<approx>\<cdot> (p \<bullet> Q)"
      unfolding weakly_bisimilar_def by auto
  qed

  lemma weakly_bisimilar_reflp: "reflp weakly_bisimilar"
  proof (rule reflpI)
    fix x
    have "is_weak_bisimulation (=)"
      unfolding is_weak_bisimulation_def by (simp add: symp_def)
    then show "x \<approx>\<cdot> x"
      unfolding weakly_bisimilar_def by auto
  qed

  lemma weakly_bisimilar_symp: "symp weakly_bisimilar"
  proof (rule sympI)
    fix P Q
    assume "P \<approx>\<cdot> Q"
    then obtain R where *: "is_weak_bisimulation R \<and> R P Q"
      unfolding weakly_bisimilar_def ..
    then have "R Q P"
      unfolding is_weak_bisimulation_def by (simp add: symp_def)
    with "*" show "Q \<approx>\<cdot> P"
      unfolding weakly_bisimilar_def by auto
  qed

  lemma weakly_bisimilar_is_weak_bisimulation: "is_weak_bisimulation weakly_bisimilar"
  unfolding is_weak_bisimulation_def proof
    show "symp (\<approx>\<cdot>)"
      by (fact weakly_bisimilar_symp)
  next
    show "(\<forall>P Q \<phi>. P \<approx>\<cdot> Q \<and> P \<turnstile> \<phi> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow> Q' \<and> P \<approx>\<cdot> Q' \<and> Q' \<turnstile> \<phi>)) \<and>
      (\<forall>P Q. P \<approx>\<cdot> Q \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* Q \<longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q' \<and> P' \<approx>\<cdot> Q')))"
      by (auto simp add: is_weak_bisimulation_def weakly_bisimilar_def) blast+
  qed

  lemma weakly_bisimilar_tau_simulation_step:
    assumes "P \<approx>\<cdot> Q" and "P \<Rightarrow> P'"
    obtains Q' where "Q \<Rightarrow> Q'" and "P' \<approx>\<cdot> Q'"
  using \<open>P \<Rightarrow> P'\<close> \<open>P \<approx>\<cdot> Q\<close> proof (induct arbitrary: Q)
    case (tau_refl P) then show ?case
      by (metis tau_transition.tau_refl)
  next
    case (tau_step P P'' P')
    from \<open>P \<rightarrow> \<langle>\<tau>,P''\<rangle>\<close> and \<open>P \<approx>\<cdot> Q\<close> obtain Q'' where "Q \<Rightarrow> Q''" and "P'' \<approx>\<cdot> Q''"
      by (metis bn_tau_fresh is_weak_bisimulation_def weak_transition_def weakly_bisimilar_is_weak_bisimulation)
    then show ?case
      using tau_step.hyps(3) tau_step.prems(1) by (metis tau_transition_trans)
  qed

  lemma weakly_bisimilar_weak_simulation_step:
    assumes "P \<approx>\<cdot> Q" and "bn \<alpha> \<sharp>* Q" and "P \<Rightarrow>\<langle>\<alpha>\<rangle> P'"
    obtains Q' where "Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q'" and "P' \<approx>\<cdot> Q'"
  proof (cases "\<alpha> = \<tau>")
    case True with \<open>P \<approx>\<cdot> Q\<close> and \<open>P \<Rightarrow>\<langle>\<alpha>\<rangle> P'\<close> and that show ?thesis
      using weak_transition_tau_iff weakly_bisimilar_tau_simulation_step by force
  next
    case False with \<open>P \<Rightarrow>\<langle>\<alpha>\<rangle> P'\<close> have "P \<Rightarrow>{\<alpha>} P'"
      by simp
    then obtain P1 P2 where tauP: "P \<Rightarrow> P1" and trans: "P1 \<rightarrow> \<langle>\<alpha>,P2\<rangle>" and tauP2: "P2 \<Rightarrow> P'"
      using observable_transition_def by blast
    from \<open>P \<approx>\<cdot> Q\<close> and tauP obtain Q1 where tauQ: "Q \<Rightarrow> Q1" and P1Q1: "P1 \<approx>\<cdot> Q1"
      by (metis weakly_bisimilar_tau_simulation_step)

    \<comment> \<open>rename~@{term "\<langle>\<alpha>,P2\<rangle>"} to avoid~@{term Q1}, without touching~@{term Q}\<close>
    obtain p where 1: "(p \<bullet> bn \<alpha>) \<sharp>* Q1" and 2: "supp (\<langle>\<alpha>,P2\<rangle>, Q) \<sharp>* p"
      proof (rule at_set_avoiding2[of "bn \<alpha>" Q1 "(\<langle>\<alpha>,P2\<rangle>, Q)", THEN exE])
        show "finite (bn \<alpha>)" by (fact bn_finite)
      next
        show "finite (supp Q1)" by (fact finite_supp)
      next
        show "finite (supp (\<langle>\<alpha>,P2\<rangle>, Q))" by (simp add: finite_supp supp_Pair)
      next
        show "bn \<alpha> \<sharp>* (\<langle>\<alpha>,P2\<rangle>, Q)" using \<open>bn \<alpha> \<sharp>* Q\<close> by (simp add: fresh_star_Pair)
      qed metis
    from 2 have 3: "supp \<langle>\<alpha>,P2\<rangle> \<sharp>* p" and 4: "supp Q \<sharp>* p"
      by (simp add: fresh_star_Un supp_Pair)+
    from 3 have "\<langle>p \<bullet> \<alpha>, p \<bullet> P2\<rangle> = \<langle>\<alpha>,P2\<rangle>"
      using supp_perm_eq by fastforce
    then obtain Q2 where trans': "Q1 \<Rightarrow>\<langle>p \<bullet> \<alpha>\<rangle> Q2" and P2Q2: "(p \<bullet> P2) \<approx>\<cdot> Q2"
      using P1Q1 trans 1 by (metis (mono_tags, lifting) weakly_bisimilar_is_weak_bisimulation bn_eqvt is_weak_bisimulation_def)

    from tauP2 have "p \<bullet> P2 \<Rightarrow> p \<bullet> P'"
      by (fact tau_transition_eqvt)
    with P2Q2 obtain Q' where tauQ2: "Q2 \<Rightarrow> Q'" and P'Q': "(p \<bullet> P') \<approx>\<cdot> Q'"
      by (metis weakly_bisimilar_tau_simulation_step)

    from tauQ and trans' and tauQ2 have "Q \<Rightarrow>\<langle>p \<bullet> \<alpha>\<rangle> Q'"
      by (rule weak_transition_weakI)
    with 4 have "Q \<Rightarrow>\<langle>\<alpha>\<rangle> (-p \<bullet> Q')"
      by (metis permute_minus_cancel(2) supp_perm_eq weak_transition_eqvt)
    moreover from P'Q' have "P' \<approx>\<cdot> (-p \<bullet> Q')"
      by (metis permute_minus_cancel(2) weakly_bisimilar_eqvt)
    ultimately show ?thesis ..
  qed

  lemma weakly_bisimilar_transp: "transp weakly_bisimilar"
  proof (rule transpI)
    fix P Q R
    assume PQ: "P \<approx>\<cdot> Q" and QR: "Q \<approx>\<cdot> R"
    let ?bisim = "weakly_bisimilar OO weakly_bisimilar"
    have "symp ?bisim"
      proof (rule sympI)
        fix P R
        assume "?bisim P R"
        then obtain Q where "P \<approx>\<cdot> Q" and "Q \<approx>\<cdot> R"
          by blast
        then have "R \<approx>\<cdot> Q" and "Q \<approx>\<cdot> P"
          by (metis weakly_bisimilar_symp sympE)+
        then show "?bisim R P"
          by blast
      qed
    moreover have "\<forall>P Q \<phi>. ?bisim P Q \<and> P \<turnstile> \<phi> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow> Q' \<and> ?bisim P Q' \<and> Q' \<turnstile> \<phi>)"
      proof (clarify)
        fix P Q \<phi> R
        assume phi: "P \<turnstile> \<phi>" and PR: "P \<approx>\<cdot> R" and RQ: "R \<approx>\<cdot> Q"
        from PR and phi obtain R' where "R \<Rightarrow> R'" and "P \<approx>\<cdot> R'" and *: "R' \<turnstile> \<phi>"
          using weakly_bisimilar_is_weak_bisimulation is_weak_bisimulation_def by force
        from RQ and \<open>R \<Rightarrow> R'\<close> obtain Q' where "Q \<Rightarrow> Q'" and "R' \<approx>\<cdot> Q'"
          by (metis weakly_bisimilar_tau_simulation_step)
        from \<open>R' \<approx>\<cdot> Q'\<close> and * obtain Q'' where "Q' \<Rightarrow> Q''" and "R' \<approx>\<cdot> Q''" and **: "Q'' \<turnstile> \<phi>"
          using weakly_bisimilar_is_weak_bisimulation is_weak_bisimulation_def by force
        from \<open>Q \<Rightarrow> Q'\<close> and \<open>Q' \<Rightarrow> Q''\<close> have "Q \<Rightarrow> Q''"
          by (fact tau_transition_trans)
        moreover from \<open>P \<approx>\<cdot> R'\<close> and \<open>R' \<approx>\<cdot> Q''\<close> have "?bisim P Q''"
          by blast
        ultimately show "\<exists>Q'. Q \<Rightarrow> Q' \<and> ?bisim P Q' \<and> Q' \<turnstile> \<phi>"
          using ** by metis
      qed
    moreover have "\<forall>P Q. ?bisim P Q \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* Q \<longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q' \<and> ?bisim P' Q'))"
      proof (clarify)
        fix P Q R \<alpha> P'
        assume PR: "P \<approx>\<cdot> R" and RQ: "R \<approx>\<cdot> Q" and fresh: "bn \<alpha> \<sharp>* Q" and trans: "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
        \<comment> \<open>rename~@{term "\<langle>\<alpha>,P'\<rangle>"} to avoid~@{term R}, without touching~@{term Q}\<close>
        obtain p where 1: "(p \<bullet> bn \<alpha>) \<sharp>* R" and 2: "supp (\<langle>\<alpha>,P'\<rangle>, Q) \<sharp>* p"
          proof (rule at_set_avoiding2[of "bn \<alpha>" R "(\<langle>\<alpha>,P'\<rangle>, Q)", THEN exE])
            show "finite (bn \<alpha>)" by (fact bn_finite)
          next
            show "finite (supp R)" by (fact finite_supp)
          next
            show "finite (supp (\<langle>\<alpha>,P'\<rangle>, Q))" by (simp add: finite_supp supp_Pair)
          next
            show "bn \<alpha> \<sharp>* (\<langle>\<alpha>,P'\<rangle>, Q)" by (simp add: fresh fresh_star_Pair)
          qed metis
        from 2 have 3: "supp \<langle>\<alpha>,P'\<rangle> \<sharp>* p" and 4: "supp Q \<sharp>* p"
          by (simp add: fresh_star_Un supp_Pair)+
        from 3 have "\<langle>p \<bullet> \<alpha>, p \<bullet> P'\<rangle> = \<langle>\<alpha>,P'\<rangle>"
          using supp_perm_eq by fastforce
        with trans obtain pR' where 5: "R \<Rightarrow>\<langle>p \<bullet> \<alpha>\<rangle> pR'" and 6: "(p \<bullet> P') \<approx>\<cdot> pR'"
          using PR 1 by (metis bn_eqvt weakly_bisimilar_is_weak_bisimulation is_weak_bisimulation_def)
        from fresh and 4 have "bn (p \<bullet> \<alpha>) \<sharp>* Q"
          by (metis bn_eqvt fresh_star_permute_iff supp_perm_eq)
        then obtain pQ' where 7: "Q \<Rightarrow>\<langle>p \<bullet> \<alpha>\<rangle> pQ'" and 8: "pR' \<approx>\<cdot> pQ'"
          using RQ 5 by (metis weakly_bisimilar_weak_simulation_step)
        from 7 have "Q \<Rightarrow>\<langle>\<alpha>\<rangle> (-p \<bullet> pQ')"
          using 4 by (metis permute_minus_cancel(2) supp_perm_eq weak_transition_eqvt)
        moreover from 6 and 8 have "?bisim P' (-p \<bullet> pQ')"
          by (metis (no_types, hide_lams) weakly_bisimilar_eqvt permute_minus_cancel(2) relcompp.simps)
        ultimately show "\<exists>Q'. Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q' \<and> ?bisim P' Q'"
          by metis
      qed
    ultimately have "is_weak_bisimulation ?bisim"
      unfolding is_weak_bisimulation_def by metis
    moreover have "?bisim P R"
      using PQ QR by blast
    ultimately show "P \<approx>\<cdot> R"
      unfolding weakly_bisimilar_def by meson
  qed

  lemma weakly_bisimilar_equivp: "equivp weakly_bisimilar"
  by (metis weakly_bisimilar_reflp weakly_bisimilar_symp weakly_bisimilar_transp equivp_reflp_symp_transp)

end

end
