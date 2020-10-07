theory S_Transform
imports
  Bisimilarity_Implies_Equivalence
  Equivalence_Implies_Bisimilarity
  Weak_Bisimilarity_Implies_Equivalence
  Weak_Equivalence_Implies_Bisimilarity
  Weak_Expressive_Completeness
begin

section \<open>\texorpdfstring{$S$}{S}-Transform: State Predicates as Actions\<close>

subsection \<open>Actions and binding names\<close>

datatype ('act,'pred) S_action =
    Act 'act
  | Pred 'pred

instantiation S_action :: (pt,pt) pt
begin

  fun permute_S_action :: "perm \<Rightarrow> ('a,'b) S_action \<Rightarrow> ('a,'b) S_action" where
    "p \<bullet> (Act \<alpha>) = Act (p \<bullet> \<alpha>)"
  | "p \<bullet> (Pred \<phi>) = Pred (p \<bullet> \<phi>)"

  instance
  proof
    fix x :: "('a,'b) S_action"
    show "0 \<bullet> x = x" by (cases x, simp_all)
  next
    fix p q and x :: "('a,'b) S_action"
    show "(p + q) \<bullet> x = p \<bullet> q \<bullet> x" by (cases x, simp_all)
  qed

end

declare permute_S_action.simps [eqvt]

lemma supp_Act [simp]: "supp (Act \<alpha>) = supp \<alpha>"
unfolding supp_def by simp

lemma supp_Pred [simp]: "supp (Pred \<phi>) = supp \<phi>"
unfolding supp_def by simp

instantiation S_action :: (fs,fs) fs
begin

  instance
  proof
    fix x :: "('a,'b) S_action"
    show "finite (supp x)"
      by (cases x) (simp add: finite_supp)+
  qed

end

instantiation S_action :: (bn,fs) bn
begin

  fun bn_S_action :: "('a,'b) S_action \<Rightarrow> atom set" where
    "bn_S_action (Act \<alpha>) = bn \<alpha>"
  | "bn_S_action (Pred _) = {}"

  instance
  proof
    fix p and \<alpha> :: "('a,'b) S_action"
    show "p \<bullet> bn \<alpha> = bn (p \<bullet> \<alpha>)"
      by (cases \<alpha>) (simp add: bn_eqvt, simp)
  next
    fix \<alpha> :: "('a,'b) S_action"
    show "finite (bn \<alpha>)"
      by (cases \<alpha>) (simp add: bn_finite, simp)
  qed

end


subsection \<open>Satisfaction\<close>

context nominal_ts
begin

  text \<open>Here our formalization differs from the informal presentation, where the $S$-transform does
  not have any predicates. In Isabelle/HOL, there are no empty types; we use type @{typ unit}
  instead. However, it is clear from the following definition of the satisfaction relation that the
  single element of this type is not actually used in any meaningful way.\<close>

  definition S_satisfies :: "'state \<Rightarrow> unit \<Rightarrow> bool" (infix "\<turnstile>\<^sub>S" 70) where
    "P \<turnstile>\<^sub>S \<phi> \<longleftrightarrow> False"

  lemma S_satisfies_eqvt: assumes "P \<turnstile>\<^sub>S \<phi>" shows "(p \<bullet> P) \<turnstile>\<^sub>S (p \<bullet> \<phi>)"
  using assms by (simp add: S_satisfies_def)

end


subsection \<open>Transitions\<close>

context nominal_ts
begin

  inductive S_transition :: "'state \<Rightarrow> (('act,'pred) S_action, 'state) residual \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>S" 70) where
    Act: "P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<Longrightarrow> P \<rightarrow>\<^sub>S \<langle>Act \<alpha>,P'\<rangle>"
  | Pred: "P \<turnstile> \<phi> \<Longrightarrow> P \<rightarrow>\<^sub>S \<langle>Pred \<phi>,P\<rangle>"

  lemma S_transition_eqvt: assumes "P \<rightarrow>\<^sub>S \<alpha>\<^sub>SP'" shows "(p \<bullet> P) \<rightarrow>\<^sub>S (p \<bullet> \<alpha>\<^sub>SP')"
  using assms by cases (simp add: S_transition.Act transition_eqvt', simp add: S_transition.Pred satisfies_eqvt)

  text \<open>If there is an $S$-transition, there is an ordinary transition with the same residual---it
  is not necessary to consider alpha-variants.\<close>

  lemma S_transition_cases [case_names Act Pred, consumes 1]: assumes "P \<rightarrow>\<^sub>S \<langle>\<alpha>\<^sub>S,P'\<rangle>"
    and "\<And>\<alpha>. \<alpha>\<^sub>S = Act \<alpha> \<Longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<Longrightarrow> R"
    and "\<And>\<phi>. \<alpha>\<^sub>S = Pred \<phi> \<Longrightarrow> P' = P \<Longrightarrow> P \<turnstile> \<phi> \<Longrightarrow> R"
    shows R
  using assms proof (cases rule: S_transition.cases)
    case (Act \<alpha>' P'')
    let ?Act = "Act :: 'act \<Rightarrow> ('act,'pred) S_action"
    from \<open>\<langle>\<alpha>\<^sub>S,P'\<rangle> = \<langle>Act \<alpha>',P''\<rangle>\<close> obtain \<alpha> where "\<alpha>\<^sub>S = Act \<alpha>"
      by (meson bn_S_action.elims residual_empty_bn_eq_iff)
    with \<open>\<langle>\<alpha>\<^sub>S,P'\<rangle> = \<langle>Act \<alpha>',P''\<rangle>\<close> obtain p where "supp (?Act \<alpha>, P') - bn (?Act \<alpha>) = supp (?Act \<alpha>', P'') - bn (?Act \<alpha>')"
      and "(supp (?Act \<alpha>, P') - bn (?Act \<alpha>)) \<sharp>* p" and "p \<bullet> (?Act \<alpha>, P') = (?Act \<alpha>', P'')" and "p \<bullet> bn (?Act \<alpha>) = bn (?Act \<alpha>')"
      by (auto simp add: residual_eq_iff_perm)
    then have "supp (\<alpha>, P') - bn \<alpha> = supp (\<alpha>', P'') - bn \<alpha>'" and "(supp (\<alpha>, P') - bn \<alpha>) \<sharp>* p"
      and "p \<bullet> (\<alpha>, P') = (\<alpha>', P'')" and "p \<bullet> bn \<alpha> = bn \<alpha>'"
      by (simp_all add: supp_Pair)
    then have "\<langle>\<alpha>,P'\<rangle> = \<langle>\<alpha>',P''\<rangle>"
      by (metis residual_eq_iff_perm)
    with \<open>\<alpha>\<^sub>S = Act \<alpha>\<close> and \<open>P \<rightarrow> \<langle>\<alpha>',P''\<rangle>\<close> show R
      using \<open>\<And>\<alpha>. \<alpha>\<^sub>S = Act \<alpha> \<Longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<Longrightarrow> R\<close> by metis
  next
    case (Pred \<phi>)
    from \<open>\<langle>\<alpha>\<^sub>S,P'\<rangle> = \<langle>Pred \<phi>,P\<rangle>\<close> have "\<alpha>\<^sub>S = Pred \<phi>" and "P' = P"
      by (metis bn_S_action.simps(2) residual_empty_bn_eq_iff)+
    with \<open>P \<turnstile> \<phi>\<close> show R
      using \<open>\<And>\<phi>. \<alpha>\<^sub>S = Pred \<phi> \<Longrightarrow> P' = P \<Longrightarrow> P \<turnstile> \<phi> \<Longrightarrow> R\<close> by metis
  qed

  lemma S_transition_Act_iff: "P \<rightarrow>\<^sub>S \<langle>Act \<alpha>,P'\<rangle> \<longleftrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
    using S_transition.Act S_transition_cases by fastforce

  lemma S_transition_Pred_iff: "P \<rightarrow>\<^sub>S \<langle>Pred \<phi>,P'\<rangle> \<longleftrightarrow> P' = P \<and> P \<turnstile> \<phi>"
    using S_transition.Pred S_transition_cases by fastforce

end


subsection \<open>Strong Bisimilarity in the \texorpdfstring{$S$}{S}-transform\<close>

context nominal_ts
begin

  interpretation S_transform: nominal_ts "(\<turnstile>\<^sub>S)" "(\<rightarrow>\<^sub>S)"
  by unfold_locales (fact S_satisfies_eqvt, fact S_transition_eqvt)

  no_notation S_satisfies (infix "\<turnstile>\<^sub>S" 70) \<comment> \<open>denotes @{const S_transform.S_satisfies} instead\<close>

  notation S_transform.bisimilar (infix "\<sim>\<cdot>\<^sub>S" 100)

  text \<open>Bisimilarity is equivalent to bisimilarity in the $S$-transform.\<close>

  lemma bisimilar_is_S_transform_bisimulation: "S_transform.is_bisimulation bisimilar"
  unfolding S_transform.is_bisimulation_def
  proof
    show "symp bisimilar"
      by (fact bisimilar_symp)
  next
    have "\<forall>P Q. P \<sim>\<cdot> Q \<longrightarrow> (\<forall>\<phi>. P \<turnstile>\<^sub>S \<phi> \<longrightarrow> Q \<turnstile>\<^sub>S \<phi>)" (is ?S)
      by (simp add: S_transform.S_satisfies_def)
    moreover have "\<forall>P Q. P \<sim>\<cdot> Q \<longrightarrow> (\<forall>\<alpha>\<^sub>S P'. bn \<alpha>\<^sub>S \<sharp>* Q \<longrightarrow> P \<rightarrow>\<^sub>S \<langle>\<alpha>\<^sub>S,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<rightarrow>\<^sub>S \<langle>\<alpha>\<^sub>S,Q'\<rangle> \<and> P' \<sim>\<cdot> Q'))" (is ?T)
      proof (clarify)
        fix P Q \<alpha>\<^sub>S P'
        assume bisim: "P \<sim>\<cdot> Q" and fresh\<^sub>S: "bn \<alpha>\<^sub>S \<sharp>* Q" and trans\<^sub>S: "P \<rightarrow>\<^sub>S \<langle>\<alpha>\<^sub>S,P'\<rangle>"
        obtain Q' where "Q \<rightarrow>\<^sub>S \<langle>\<alpha>\<^sub>S,Q'\<rangle>" and "P' \<sim>\<cdot> Q'"
          using trans\<^sub>S proof (cases rule: S_transition_cases)
            case (Act \<alpha>)
            from \<open>\<alpha>\<^sub>S = Act \<alpha>\<close> and fresh\<^sub>S have "bn \<alpha> \<sharp>* Q"
              by simp
            with bisim and \<open>P \<rightarrow> \<langle>\<alpha>,P'\<rangle>\<close> obtain Q' where transQ: "Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>" and bisim': "P' \<sim>\<cdot> Q'"
              by (metis bisimilar_simulation_step)
            from \<open>\<alpha>\<^sub>S = Act \<alpha>\<close> and transQ have "Q \<rightarrow>\<^sub>S \<langle>\<alpha>\<^sub>S,Q'\<rangle>"
              by (simp add: S_transition.Act)
            with bisim' show "thesis"
              using \<open>\<And>Q'. Q \<rightarrow>\<^sub>S \<langle>\<alpha>\<^sub>S,Q'\<rangle> \<Longrightarrow> P' \<sim>\<cdot> Q' \<Longrightarrow> thesis\<close> by blast
          next
            case (Pred \<phi>)
            from bisim and \<open>P \<turnstile> \<phi>\<close> have "Q \<turnstile> \<phi>"
              by (metis is_bisimulation_def bisimilar_is_bisimulation)
            with \<open>\<alpha>\<^sub>S = Pred \<phi>\<close> have "Q \<rightarrow>\<^sub>S \<langle>\<alpha>\<^sub>S,Q\<rangle>"
              by (simp add: S_transition.Pred)
            with bisim and \<open>P' = P\<close> show "thesis"
              using \<open>\<And>Q'. Q \<rightarrow>\<^sub>S \<langle>\<alpha>\<^sub>S,Q'\<rangle> \<Longrightarrow> P' \<sim>\<cdot> Q' \<Longrightarrow> thesis\<close> by blast
          qed
        then show "\<exists>Q'. Q \<rightarrow>\<^sub>S \<langle>\<alpha>\<^sub>S,Q'\<rangle> \<and> P' \<sim>\<cdot> Q'"
          by auto
      qed
    ultimately show "?S \<and> ?T"
      by metis
  qed

  lemma S_transform_bisimilar_is_bisimulation: "is_bisimulation S_transform.bisimilar"
  unfolding is_bisimulation_def
  proof
    show "symp S_transform.bisimilar"
      by (fact S_transform.bisimilar_symp)
  next
    have "\<forall>P Q. P \<sim>\<cdot>\<^sub>S Q \<longrightarrow> (\<forall>\<phi>. P \<turnstile> \<phi> \<longrightarrow> Q \<turnstile> \<phi>)" (is ?S)
    proof (clarify)
      fix P Q \<phi>
      assume bisim: "P \<sim>\<cdot>\<^sub>S Q" and valid: "P \<turnstile> \<phi>"
      from valid have "P \<rightarrow>\<^sub>S \<langle>Pred \<phi>,P\<rangle>"
        by (fact S_transition.Pred)
      moreover have "bn (Pred \<phi>) \<sharp>* Q"
        by (simp add: fresh_star_def)
      ultimately obtain Q' where trans': "Q \<rightarrow>\<^sub>S \<langle>Pred \<phi>,Q'\<rangle>"
        using bisim by (metis S_transform.bisimilar_simulation_step)
      from trans' show "Q \<turnstile> \<phi>"
        using S_transition_Pred_iff by blast
    qed
    moreover have "\<forall>P Q. P \<sim>\<cdot>\<^sub>S Q \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* Q \<longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> P' \<sim>\<cdot>\<^sub>S Q'))" (is ?T)
      proof (clarify)
        fix P Q \<alpha> P'
        assume bisim: "P \<sim>\<cdot>\<^sub>S Q" and fresh: "bn \<alpha> \<sharp>* Q" and trans: "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
        from trans have "P \<rightarrow>\<^sub>S \<langle>Act \<alpha>,P'\<rangle>"
          by (fact S_transition.Act)
        with bisim and fresh obtain Q' where trans': "Q \<rightarrow>\<^sub>S \<langle>Act \<alpha>,Q'\<rangle>" and bisim': "P' \<sim>\<cdot>\<^sub>S Q'"
          by (metis S_transform.bisimilar_simulation_step bn_S_action.simps(1))
        from trans' have "Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>"
          by (metis S_transition_Act_iff)
        with bisim' show "\<exists>Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> P' \<sim>\<cdot>\<^sub>S Q'"
          by metis
      qed
    ultimately show "?S \<and> ?T"
      by metis
  qed

  theorem S_transform_bisimilar_iff: "P \<sim>\<cdot>\<^sub>S Q \<longleftrightarrow> P \<sim>\<cdot> Q"
  proof
    assume "P \<sim>\<cdot>\<^sub>S Q"
    then show "P \<sim>\<cdot> Q"
      by (metis S_transform_bisimilar_is_bisimulation bisimilar_def)
  next
    assume "P \<sim>\<cdot> Q"
    then show "P \<sim>\<cdot>\<^sub>S Q"
      by (metis S_transform.bisimilar_def bisimilar_is_S_transform_bisimulation)
  qed

end


subsection \<open>Weak Bisimilarity in the \texorpdfstring{$S$}{S}-transform\<close>

context weak_nominal_ts
begin

  lemma weakly_bisimilar_tau_transition_weakly_bisimilar:
    assumes "P \<approx>\<cdot> R" and "P \<Rightarrow> Q" and "Q \<Rightarrow> R"
    shows "Q \<approx>\<cdot> R"
  proof -
    let ?bisim = "\<lambda>S T. S \<approx>\<cdot> T \<or> {S,T} = {Q,R}"
    have "is_weak_bisimulation ?bisim"
      unfolding is_weak_bisimulation_def
    proof
      show "symp ?bisim"
        using weakly_bisimilar_symp by (simp add: insert_commute symp_def)
    next
      have "\<forall>S T \<phi>. ?bisim S T \<and> S \<turnstile> \<phi> \<longrightarrow> (\<exists>T'. T \<Rightarrow> T' \<and> ?bisim S T' \<and> T' \<turnstile> \<phi>)" (is ?S)
      proof (clarify)
        fix S T \<phi>
        assume bisim: "?bisim S T" and valid: "S \<turnstile> \<phi>"
        from bisim show "\<exists>T'. T \<Rightarrow> T' \<and> ?bisim S T' \<and> T' \<turnstile> \<phi>"
        proof
          assume "S \<approx>\<cdot> T"
          with valid show ?thesis
            by (metis is_weak_bisimulation_def weakly_bisimilar_is_weak_bisimulation)
        next
          assume "{S, T} = {Q, R}"
          then have "S = Q \<and> T = R \<or> T = Q \<and> S = R"
            by (metis doubleton_eq_iff)
          then show ?thesis
          proof
            assume "S = Q \<and> T = R"
            with \<open>P \<Rightarrow> Q\<close> and \<open>P \<approx>\<cdot> R\<close> and valid show ?thesis
              by (metis is_weak_bisimulation_def tau_transition_trans weakly_bisimilar_is_weak_bisimulation weakly_bisimilar_tau_simulation_step)
          next
            assume "T = Q \<and> S = R"
            with \<open>Q \<Rightarrow> R\<close> and valid show ?thesis
              by (meson reflpE weakly_bisimilar_reflp)
          qed
        qed
      qed
      moreover have "\<forall>S T. ?bisim S T \<longrightarrow> (\<forall>\<alpha> S'. bn \<alpha> \<sharp>* T \<longrightarrow> S \<rightarrow> \<langle>\<alpha>,S'\<rangle> \<longrightarrow> (\<exists>T'. T \<Rightarrow>\<langle>\<alpha>\<rangle> T' \<and> ?bisim S' T'))" (is ?T)
      proof (clarify)
        fix S T \<alpha> S'
        assume bisim: "?bisim S T" and fresh: "bn \<alpha> \<sharp>* T" and trans: "S \<rightarrow> \<langle>\<alpha>,S'\<rangle>"
        from bisim show "\<exists>T'. T \<Rightarrow>\<langle>\<alpha>\<rangle> T' \<and> ?bisim S' T'"
        proof
          assume "S \<approx>\<cdot> T"
          with fresh and trans show ?thesis
            by (metis is_weak_bisimulation_def weakly_bisimilar_is_weak_bisimulation)
        next
          assume "{S, T} = {Q, R}"
          then have "S = Q \<and> T = R \<or> T = Q \<and> S = R"
            by (metis doubleton_eq_iff)
          then show ?thesis
          proof
            assume "S = Q \<and> T = R"
            with \<open>P \<Rightarrow> Q\<close> and \<open>P \<approx>\<cdot> R\<close> and fresh and trans show ?thesis
              using observable_transition_stepI tau_refl weak_transition_stepI weak_transition_weakI weakly_bisimilar_weak_simulation_step by blast
          next
            assume "T = Q \<and> S = R"
            with \<open>Q \<Rightarrow> R\<close> and trans show ?thesis
              by (metis observable_transition_stepI reflpE tau_refl weak_transition_stepI weak_transition_weakI weakly_bisimilar_reflp)
          qed
        qed
      qed
      ultimately show "?S \<and> ?T"
        by metis
    qed
    then show ?thesis
      using weakly_bisimilar_def by blast
  qed

  notation S_satisfies (infix "\<turnstile>\<^sub>S" 70)

  interpretation S_transform: weak_nominal_ts "(\<turnstile>\<^sub>S)" "(\<rightarrow>\<^sub>S)" "Act \<tau>"
  by unfold_locales (fact S_satisfies_eqvt, fact S_transition_eqvt, simp add: tau_eqvt)

  no_notation S_satisfies (infix "\<turnstile>\<^sub>S" 70) \<comment> \<open>denotes @{const S_transform.S_satisfies} instead\<close>

  notation S_transform.tau_transition (infix "\<Rightarrow>\<^sub>S" 70)
  notation S_transform.observable_transition ("_/ \<Rightarrow>{_}\<^sub>S/ _" [70, 70, 71] 71)
  notation S_transform.weak_transition ("_/ \<Rightarrow>\<langle>_\<rangle>\<^sub>S/ _" [70, 70, 71] 71)
  notation S_transform.weakly_bisimilar (infix "\<approx>\<cdot>\<^sub>S" 100)

  lemma S_transform_tau_transition_iff: "P \<Rightarrow>\<^sub>S P' \<longleftrightarrow> P \<Rightarrow> P'"
  proof
    assume "P \<Rightarrow>\<^sub>S P'"
    then show "P \<Rightarrow> P'"
      by induct (simp, metis S_transition_Act_iff tau_step)
  next
    assume "P \<Rightarrow> P'"
    then show "P \<Rightarrow>\<^sub>S P'"
      by induct (simp, metis S_transform.tau_transition.simps S_transition.Act)
  qed

  lemma S_transform_observable_transition_iff: "P \<Rightarrow>{Act \<alpha>}\<^sub>S P' \<longleftrightarrow> P \<Rightarrow>{\<alpha>} P'"
    unfolding S_transform.observable_transition_def observable_transition_def
    by (metis S_transform_tau_transition_iff S_transition_Act_iff)

  lemma S_transform_weak_transition_iff: "P \<Rightarrow>\<langle>Act \<alpha>\<rangle>\<^sub>S P' \<longleftrightarrow> P \<Rightarrow>\<langle>\<alpha>\<rangle> P'"
    by (simp add: S_transform_observable_transition_iff S_transform_tau_transition_iff weak_transition_def)

  text \<open>Weak bisimilarity is equivalent to weak bisimilarity in the $S$-transform.\<close>

  lemma weakly_bisimilar_is_S_transform_weak_bisimulation: "S_transform.is_weak_bisimulation weakly_bisimilar"
  unfolding S_transform.is_weak_bisimulation_def
  proof
    show "symp weakly_bisimilar"
      by (fact weakly_bisimilar_symp)
  next
    have "\<forall>P Q \<phi>. P \<approx>\<cdot> Q \<and> P \<turnstile>\<^sub>S \<phi> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow>\<^sub>S Q' \<and> P \<approx>\<cdot> Q' \<and> Q' \<turnstile>\<^sub>S \<phi>)" (is ?S)
      by (simp add: S_transform.S_satisfies_def)
    moreover have "\<forall>P Q. P \<approx>\<cdot> Q \<longrightarrow> (\<forall>\<alpha>\<^sub>S P'. bn \<alpha>\<^sub>S \<sharp>* Q \<longrightarrow> P \<rightarrow>\<^sub>S \<langle>\<alpha>\<^sub>S,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow>\<langle>\<alpha>\<^sub>S\<rangle>\<^sub>S Q' \<and> P' \<approx>\<cdot> Q'))" (is ?T)
      proof (clarify)
        fix P Q \<alpha>\<^sub>S P'
        assume bisim: "P \<approx>\<cdot> Q" and fresh\<^sub>S: "bn \<alpha>\<^sub>S \<sharp>* Q" and trans\<^sub>S: "P \<rightarrow>\<^sub>S \<langle>\<alpha>\<^sub>S,P'\<rangle>"
        obtain Q' where "Q \<Rightarrow>\<langle>\<alpha>\<^sub>S\<rangle>\<^sub>S Q'" and "P' \<approx>\<cdot> Q'"
          using trans\<^sub>S proof (cases rule: S_transition_cases)
            case (Act \<alpha>)
            from \<open>\<alpha>\<^sub>S = Act \<alpha>\<close> and fresh\<^sub>S have "bn \<alpha> \<sharp>* Q"
              by simp
            with bisim and \<open>P \<rightarrow> \<langle>\<alpha>,P'\<rangle>\<close> obtain Q' where transQ: "Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q'" and bisim': "P' \<approx>\<cdot> Q'"
              by (metis is_weak_bisimulation_def weakly_bisimilar_is_weak_bisimulation)
            from \<open>\<alpha>\<^sub>S = Act \<alpha>\<close> and transQ have "Q \<Rightarrow>\<langle>\<alpha>\<^sub>S\<rangle>\<^sub>S Q'"
              by (metis S_transform_weak_transition_iff)
            with bisim' show "thesis"
              using \<open>\<And>Q'. Q \<Rightarrow>\<langle>\<alpha>\<^sub>S\<rangle>\<^sub>S Q' \<Longrightarrow> P' \<approx>\<cdot> Q' \<Longrightarrow> thesis\<close> by blast
          next
            case (Pred \<phi>)
            from bisim and \<open>P \<turnstile> \<phi>\<close> obtain Q' where "Q \<Rightarrow> Q'" and "P \<approx>\<cdot> Q'" and "Q' \<turnstile> \<phi>"
              by (metis is_weak_bisimulation_def weakly_bisimilar_is_weak_bisimulation)
            from \<open>Q \<Rightarrow> Q'\<close> have "Q \<Rightarrow>\<^sub>S Q'"
              by (metis S_transform_tau_transition_iff)
            moreover from \<open>Q' \<turnstile> \<phi>\<close> have "Q' \<rightarrow>\<^sub>S \<langle>Pred \<phi>,Q'\<rangle>"
              by (simp add: S_transition.Pred)
            ultimately have "Q \<Rightarrow>\<langle>\<alpha>\<^sub>S\<rangle>\<^sub>S Q'"
              using \<open>\<alpha>\<^sub>S = Pred \<phi>\<close> by (metis S_transform.observable_transitionI S_transform.tau_refl S_transform.weak_transition_stepI)
            with \<open>P' = P\<close> and \<open>P \<approx>\<cdot> Q'\<close> show "thesis"
              using \<open>\<And>Q'. Q \<Rightarrow>\<langle>\<alpha>\<^sub>S\<rangle>\<^sub>S Q' \<Longrightarrow> P' \<approx>\<cdot> Q' \<Longrightarrow> thesis\<close> by blast
          qed
        then show "\<exists>Q'. Q \<Rightarrow>\<langle>\<alpha>\<^sub>S\<rangle>\<^sub>S Q' \<and> P' \<approx>\<cdot> Q'"
          by auto
      qed
    ultimately show "?S \<and> ?T"
      by metis
  qed

  lemma S_transform_weakly_bisimilar_is_weak_bisimulation: "is_weak_bisimulation S_transform.weakly_bisimilar"
  unfolding is_weak_bisimulation_def
  proof
    show "symp S_transform.weakly_bisimilar"
      by (fact S_transform.weakly_bisimilar_symp)
  next
    have "\<forall>P Q \<phi>. P \<approx>\<cdot>\<^sub>S Q \<and> P \<turnstile> \<phi> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow> Q' \<and> P \<approx>\<cdot>\<^sub>S Q' \<and> Q' \<turnstile> \<phi>)" (is ?S)
    proof (clarify)
      fix P Q \<phi>
      assume bisim: "P \<approx>\<cdot>\<^sub>S Q" and valid: "P \<turnstile> \<phi>"
      from valid have "P \<Rightarrow>\<langle>Pred \<phi>\<rangle>\<^sub>S P"
        by (simp add: S_transition.Pred)
      moreover have "bn (Pred \<phi>) \<sharp>* Q"
        by (simp add: fresh_star_def)
      ultimately obtain Q'' where trans': "Q \<Rightarrow>\<langle>Pred \<phi>\<rangle>\<^sub>S Q''" and bisim': "P \<approx>\<cdot>\<^sub>S Q''"
        using bisim by (metis S_transform.weakly_bisimilar_weak_simulation_step)

      from trans' obtain Q' Q\<^sub>1 where trans\<^sub>1: "Q \<Rightarrow>\<^sub>S Q'" and trans\<^sub>2: "Q' \<rightarrow>\<^sub>S \<langle>Pred \<phi>, Q\<^sub>1\<rangle>" and trans\<^sub>3: "Q\<^sub>1 \<Rightarrow>\<^sub>S Q''"
        by (auto simp add: S_transform.observable_transition_def)
      from trans\<^sub>2 have eq: "Q\<^sub>1 = Q'" and "Q' \<turnstile> \<phi>"
        using S_transition_Pred_iff by blast+
      moreover from trans\<^sub>1 and trans\<^sub>3 and eq and bisim and bisim' have "P \<approx>\<cdot>\<^sub>S Q'"
        by (metis S_transform.weakly_bisimilar_equivp S_transform.weakly_bisimilar_tau_transition_weakly_bisimilar equivp_def)
      moreover from trans\<^sub>1 have "Q \<Rightarrow> Q'"
        by (metis S_transform_tau_transition_iff)
      ultimately show "\<exists>Q'. Q \<Rightarrow> Q' \<and> P \<approx>\<cdot>\<^sub>S Q' \<and> Q' \<turnstile> \<phi>"
        by metis
    qed
    moreover have "\<forall>P Q. P \<approx>\<cdot>\<^sub>S Q \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* Q \<longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q' \<and> P' \<approx>\<cdot>\<^sub>S Q'))" (is ?T)
      proof (clarify)
        fix P Q \<alpha> P'
        assume bisim: "P \<approx>\<cdot>\<^sub>S Q" and fresh: "bn \<alpha> \<sharp>* Q" and trans: "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
        from trans have "P \<rightarrow>\<^sub>S \<langle>Act \<alpha>,P'\<rangle>"
          by (fact S_transition.Act)
        with bisim and fresh obtain Q' where trans': "Q \<Rightarrow>\<langle>Act \<alpha>\<rangle>\<^sub>S Q'" and bisim': "P' \<approx>\<cdot>\<^sub>S Q'"
          by (metis S_transform.is_weak_bisimulation_def S_transform.weakly_bisimilar_is_weak_bisimulation bn_S_action.simps(1))
        from trans' have "Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q'"
          by (metis S_transform_weak_transition_iff)
        with bisim' show "\<exists>Q'. Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q' \<and> P' \<approx>\<cdot>\<^sub>S Q'"
          by metis
      qed
    ultimately show "?S \<and> ?T"
      by metis
  qed

  theorem S_transform_weakly_bisimilar_iff: "P \<approx>\<cdot>\<^sub>S Q \<longleftrightarrow> P \<approx>\<cdot> Q"
  proof
    assume "P \<approx>\<cdot>\<^sub>S Q"
    then show "P \<approx>\<cdot> Q"
      by (metis S_transform_weakly_bisimilar_is_weak_bisimulation weakly_bisimilar_def)
  next
    assume "P \<approx>\<cdot> Q"
    then show "P \<approx>\<cdot>\<^sub>S Q"
      by (metis S_transform.weakly_bisimilar_def weakly_bisimilar_is_S_transform_weak_bisimulation)
  qed

end


subsection \<open>Translation of (strong) formulas into formulas without predicates\<close>

text \<open>Since we defined formulas via a manual quotient construction, we also need to define the
$S$-transform via lifting from the underlying type of infinitely branching trees. As before, we
cannot use {\bf nominal\_function} because that generates proof obligations where, for formulas
of the form~@{term "Conj xset"}, the assumption that~@{term xset} has finite support is missing.\<close>

text \<open>The following auxiliary function returns trees (modulo $\alpha$-equivalence) rather than
formulas. This allows us to prove equivariance for \emph{all} argument trees, without an assumption
that they are (hereditarily) finitely supported. Further below--after this auxiliary function has
been lifted to (strong) formulas as arguments--we derive a version that returns formulas.\<close>

primrec S_transform_Tree :: "('idx,'pred::fs,'act::bn) Tree \<Rightarrow> ('idx, unit, ('act,'pred) S_action) Tree\<^sub>\<alpha>" where
  "S_transform_Tree (tConj tset) = Conj\<^sub>\<alpha> (map_bset S_transform_Tree tset)"
| "S_transform_Tree (tNot t) = Not\<^sub>\<alpha> (S_transform_Tree t)"
| "S_transform_Tree (tPred \<phi>) = Act\<^sub>\<alpha> (S_action.Pred \<phi>) (Conj\<^sub>\<alpha> bempty)"
| "S_transform_Tree (tAct \<alpha> t) = Act\<^sub>\<alpha> (S_action.Act \<alpha>) (S_transform_Tree t)"

lemma S_transform_Tree_eqvt [eqvt]: "p \<bullet> S_transform_Tree t = S_transform_Tree (p \<bullet> t)"
proof (induct t)
  case (tConj tset)
  then show ?case
    by simp (metis (no_types, hide_lams) bset.map_cong0 map_bset_eqvt permute_fun_def permute_minus_cancel(1))
qed simp_all

text \<open>@{const S_transform_Tree} respects $\alpha$-equivalence.\<close>

lemma alpha_Tree_S_transform_Tree:
  assumes "t1 =\<^sub>\<alpha> t2"
  shows "S_transform_Tree t1 = S_transform_Tree t2"
using assms proof (induction t1 t2 rule: alpha_Tree_induct')
  case (alpha_tConj tset1 tset2)
  then have "rel_bset (=) (map_bset S_transform_Tree tset1) (map_bset S_transform_Tree tset2)"
    by (simp add: bset.rel_map(1) bset.rel_map(2) bset.rel_mono_strong)
  then show ?case
    by (simp add: bset.rel_eq)
next
  case (alpha_tAct \<alpha>1 t1 \<alpha>2 t2)
  from \<open>tAct \<alpha>1 t1 =\<^sub>\<alpha> tAct \<alpha>2 t2\<close>
    obtain p where *: "(bn \<alpha>1, t1) \<approx>set alpha_Tree (supp_rel alpha_Tree) p (bn \<alpha>2, t2)"
      and **: "(bn \<alpha>1, \<alpha>1) \<approx>set (=) supp p (bn \<alpha>2, \<alpha>2)"
    by auto
  from * have fresh: "(supp_rel alpha_Tree t1 - bn \<alpha>1) \<sharp>* p" and alpha: "p \<bullet> t1 =\<^sub>\<alpha> t2" and eq: "p \<bullet> bn \<alpha>1 = bn \<alpha>2"
    by (auto simp add: alpha_set)
  from alpha_tAct.IH(2) have "supp_rel alpha_Tree (rep_Tree\<^sub>\<alpha> (S_transform_Tree t1)) \<subseteq> supp_rel alpha_Tree t1"
    by (metis (no_types, lifting) infinite_mono alpha_Tree_permute_rep_commute S_transform_Tree_eqvt mem_Collect_eq subsetI supp_rel_def)
  with fresh have fresh': "(supp_rel alpha_Tree (rep_Tree\<^sub>\<alpha> (S_transform_Tree t1)) - bn \<alpha>1) \<sharp>* p"
    by (meson DiffD1 DiffD2 DiffI fresh_star_def subsetCE)
  moreover from alpha have alpha': "p \<bullet> rep_Tree\<^sub>\<alpha> (S_transform_Tree t1) =\<^sub>\<alpha> rep_Tree\<^sub>\<alpha> (S_transform_Tree t2)"
    using alpha_tAct.IH(1) by (metis alpha_Tree_permute_rep_commute S_transform_Tree_eqvt)
  moreover from fresh' alpha' eq have "supp_rel alpha_Tree (rep_Tree\<^sub>\<alpha> (S_transform_Tree t1)) - bn \<alpha>1 = supp_rel alpha_Tree (rep_Tree\<^sub>\<alpha> (S_transform_Tree t2)) - bn \<alpha>2"
    by (metis (mono_tags) Diff_eqvt alpha_Tree_eqvt' alpha_Tree_eqvt_aux alpha_Tree_supp_rel atom_set_perm_eq)
  ultimately have "(bn \<alpha>1, rep_Tree\<^sub>\<alpha> (S_transform_Tree t1)) \<approx>set alpha_Tree (supp_rel alpha_Tree) p (bn \<alpha>2, rep_Tree\<^sub>\<alpha> (S_transform_Tree t2))"
    using eq by (simp add: alpha_set)
  moreover from ** have "(bn \<alpha>1, S_action.Act \<alpha>1) \<approx>set (=) supp p (bn \<alpha>2, S_action.Act \<alpha>2)"
    by (metis (mono_tags, lifting) S_Transform.supp_Act alpha_set permute_S_action.simps(1))
  ultimately have "Act\<^sub>\<alpha> (S_action.Act \<alpha>1) (S_transform_Tree t1) = Act\<^sub>\<alpha> (S_action.Act \<alpha>2) (S_transform_Tree t2)"
    by (auto simp add: Act\<^sub>\<alpha>_eq_iff)
  then show ?case
    by simp
qed simp_all

text \<open>$S$-transform for trees modulo $\alpha$-equivalence.\<close>

lift_definition S_transform_Tree\<^sub>\<alpha> :: "('idx,'pred::fs,'act::bn) Tree\<^sub>\<alpha> \<Rightarrow> ('idx, unit, ('act,'pred) S_action) Tree\<^sub>\<alpha>" is
    S_transform_Tree
  by (fact alpha_Tree_S_transform_Tree)

lemma S_transform_Tree\<^sub>\<alpha>_eqvt [eqvt]: "p \<bullet> S_transform_Tree\<^sub>\<alpha> t\<^sub>\<alpha> = S_transform_Tree\<^sub>\<alpha> (p \<bullet> t\<^sub>\<alpha>)"
  by transfer (simp)

lemma S_transform_Tree\<^sub>\<alpha>_Conj\<^sub>\<alpha> [simp]: "S_transform_Tree\<^sub>\<alpha> (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>) = Conj\<^sub>\<alpha> (map_bset S_transform_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>)"
  by (simp add: Conj\<^sub>\<alpha>_def' S_transform_Tree\<^sub>\<alpha>.abs_eq) (metis (no_types, lifting) S_transform_Tree\<^sub>\<alpha>.rep_eq bset.map_comp bset.map_cong0 comp_apply)

lemma S_transform_Tree\<^sub>\<alpha>_Not\<^sub>\<alpha> [simp]: "S_transform_Tree\<^sub>\<alpha> (Not\<^sub>\<alpha> t\<^sub>\<alpha>) = Not\<^sub>\<alpha> (S_transform_Tree\<^sub>\<alpha> t\<^sub>\<alpha>)"
  by transfer simp

lemma S_transform_Tree\<^sub>\<alpha>_Pred\<^sub>\<alpha> [simp]: "S_transform_Tree\<^sub>\<alpha> (Pred\<^sub>\<alpha> \<phi>) = Act\<^sub>\<alpha> (S_action.Pred \<phi>) (Conj\<^sub>\<alpha> bempty)"
  by transfer simp

lemma S_transform_Tree\<^sub>\<alpha>_Act\<^sub>\<alpha> [simp]: "S_transform_Tree\<^sub>\<alpha> (Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>) = Act\<^sub>\<alpha> (S_action.Act \<alpha>) (S_transform_Tree\<^sub>\<alpha> t\<^sub>\<alpha>)"
  by transfer simp

lemma finite_supp_map_bset_S_transform_Tree\<^sub>\<alpha> [simp]:
  assumes "finite (supp tset\<^sub>\<alpha>)"
  shows "finite (supp (map_bset S_transform_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>))"
proof -
  have "eqvt map_bset" and "eqvt S_transform_Tree\<^sub>\<alpha>"
    by (simp add: eqvtI)+
  then have "supp (map_bset S_transform_Tree\<^sub>\<alpha>) = {}"
    using supp_fun_eqvt supp_fun_app_eqvt by blast
  then have "supp (map_bset S_transform_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>) \<subseteq> supp tset\<^sub>\<alpha>"
    using supp_fun_app by blast
  with assms show "finite (supp (map_bset S_transform_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>))"
    by (metis finite_subset)
qed

lemma S_transform_Tree\<^sub>\<alpha>_preserves_hereditarily_fs:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "hereditarily_fs (S_transform_Tree\<^sub>\<alpha> t\<^sub>\<alpha>)"
using assms proof (induct rule: hereditarily_fs.induct)
  case (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>)
  then show ?case
    by (auto intro!: hereditarily_fs.Conj\<^sub>\<alpha>) (metis imageE map_bset.rep_eq)
next
  case (Not\<^sub>\<alpha> t\<^sub>\<alpha>)
  then show ?case
    by (simp add: hereditarily_fs.Not\<^sub>\<alpha>)
next
  case (Pred\<^sub>\<alpha> \<phi>)
  have "finite (supp bempty)"
    by (simp add: eqvtI supp_fun_eqvt)
  then show ?case
    using hereditarily_fs.Act\<^sub>\<alpha> finite_supp_implies_hereditarily_fs_Conj\<^sub>\<alpha> by fastforce
next
  case (Act\<^sub>\<alpha> t\<^sub>\<alpha> \<alpha>)
  then show ?case
    by (simp add: Formula.hereditarily_fs.Act\<^sub>\<alpha>)
qed

text \<open>$S$-transform for (strong) formulas.\<close>

lift_definition S_transform_formula :: "('idx,'pred::fs,'act::bn) formula \<Rightarrow> ('idx, unit, ('act,'pred) S_action) Tree\<^sub>\<alpha>" is
    S_transform_Tree\<^sub>\<alpha>
  .

lemma S_transform_formula_eqvt [eqvt]: "p \<bullet> S_transform_formula x = S_transform_formula (p \<bullet> x)"
  by transfer (simp)

lemma S_transform_formula_Conj [simp]:
  assumes "finite (supp xset)"
  shows "S_transform_formula (Conj xset) = Conj\<^sub>\<alpha> (map_bset S_transform_formula xset)"
  using assms by (simp add: Conj_def S_transform_formula_def bset.map_comp map_fun_def)

lemma S_transform_formula_Not [simp]: "S_transform_formula (Not x) = Not\<^sub>\<alpha> (S_transform_formula x)"
  by transfer simp

lemma S_transform_formula_Pred [simp]: "S_transform_formula (Formula.Pred \<phi>) = Act\<^sub>\<alpha> (S_action.Pred \<phi>) (Conj\<^sub>\<alpha> bempty)"
  by transfer simp

lemma S_transform_formula_Act [simp]: "S_transform_formula (Formula.Act \<alpha> x) = Formula.Act\<^sub>\<alpha> (S_action.Act \<alpha>) (S_transform_formula x)"
  by transfer simp

lemma S_transform_formula_hereditarily_fs [simp]: "hereditarily_fs (S_transform_formula x)"
  by transfer (fact S_transform_Tree\<^sub>\<alpha>_preserves_hereditarily_fs)

text \<open>Finally, we define the proper $S$-transform, which returns formulas instead of trees.\<close>

definition S_transform :: "('idx,'pred::fs,'act::bn) formula \<Rightarrow> ('idx, unit, ('act,'pred) S_action) formula" where
  "S_transform x = Abs_formula (S_transform_formula x)"

lemma S_transform_eqvt [eqvt]: "p \<bullet> S_transform x = S_transform (p \<bullet> x)"
  unfolding S_transform_def by simp

lemma finite_supp_map_bset_S_transform [simp]:
  assumes "finite (supp xset)"
  shows "finite (supp (map_bset S_transform xset))"
proof -
  have "eqvt map_bset" and "eqvt S_transform"
    by (simp add: eqvtI)+
  then have "supp (map_bset S_transform) = {}"
    using supp_fun_eqvt supp_fun_app_eqvt by blast
  then have "supp (map_bset S_transform xset) \<subseteq> supp xset"
    using supp_fun_app by blast
  with assms show "finite (supp (map_bset S_transform xset))"
    by (metis finite_subset)
qed

lemma S_transform_Conj [simp]:
  assumes "finite (supp xset)"
  shows "S_transform (Conj xset) = Conj (map_bset S_transform xset)"
  using assms unfolding S_transform_def by (simp, simp add: Conj_def bset.map_comp o_def)

lemma S_transform_Not [simp]: "S_transform (Not x) = Not (S_transform x)"
  unfolding S_transform_def by (simp add: Not.abs_eq eq_onp_same_args)

lemma S_transform_Pred [simp]: "S_transform (Formula.Pred \<phi>) = Formula.Act (S_action.Pred \<phi>) (Conj bempty)"
  unfolding S_transform_def by (simp add: Formula.Act_def Conj_rep_eq eqvtI supp_fun_eqvt)

lemma S_transform_Act [simp]: "S_transform (Formula.Act \<alpha> x) = Formula.Act (S_action.Act \<alpha>) (S_transform x)"
  unfolding S_transform_def by (simp, simp add: Formula.Act_def)

context nominal_ts
begin

  lemma valid_Conj_bempty [simp]: "P \<Turnstile> Conj bempty"
  by (simp add: bempty.rep_eq eqvtI supp_fun_eqvt)

  notation S_satisfies (infix "\<turnstile>\<^sub>S" 70)

  interpretation S_transform: nominal_ts "(\<turnstile>\<^sub>S)" "(\<rightarrow>\<^sub>S)"
  by unfold_locales (fact S_satisfies_eqvt, fact S_transition_eqvt)

  notation S_transform.valid (infix "\<Turnstile>\<^sub>S" 70)

  text \<open>The $S$-transform preserves satisfaction of formulas in the following sense:\<close>

  theorem valid_iff_valid_S_transform: shows "P \<Turnstile> x \<longleftrightarrow> P \<Turnstile>\<^sub>S S_transform x"
  proof (induct x arbitrary: P)
    case (Conj xset)
    then show ?case
      by auto (metis imageE map_bset.rep_eq, simp add: map_bset.rep_eq)
  next
    case (Not x)
    then show ?case by simp
  next
    case (Pred \<phi>)
    let ?\<phi> = "Formula.Pred \<phi> :: ('idx, 'pred, ('act,'pred) S_action) formula"
    have "bn (S_action.Pred \<phi> :: ('act,'pred) S_action) \<sharp>* P"
      by (simp add: fresh_star_def)
    then show ?case
      by (auto simp add: S_transform.valid_Act_fresh S_transition_Pred_iff)
  next
    case (Act \<alpha> x)
    show ?case
    proof
      assume "P \<Turnstile> Formula.Act \<alpha> x"
      then obtain \<alpha>' x' P' where eq: "Formula.Act \<alpha> x = Formula.Act \<alpha>' x'" and trans: "P \<rightarrow> \<langle>\<alpha>',P'\<rangle>" and valid: "P' \<Turnstile> x'"
        by (metis valid_Act)
      from eq obtain p where p_x: "p \<bullet> x = x'" and p_\<alpha>: "p \<bullet> \<alpha> = \<alpha>'"
        by (metis Act_eq_iff_perm)

      from valid have "-p \<bullet> P' \<Turnstile> x"
        using p_x by (metis valid_eqvt permute_minus_cancel(2))
      then have "-p \<bullet> P' \<Turnstile>\<^sub>S S_transform x"
        using Act.hyps(1) by metis
      then have "P' \<Turnstile>\<^sub>S S_transform x'"
        by (metis (no_types, lifting) p_x S_transform.valid_eqvt S_transform_eqvt permute_minus_cancel(1))

      with eq and trans show "P \<Turnstile>\<^sub>S S_transform (Formula.Act \<alpha> x)"
        using S_transform.valid_Act S_transition.Act by fastforce
    next
      assume *: "P \<Turnstile>\<^sub>S S_transform (Formula.Act \<alpha> x)"

      \<comment> \<open>rename~@{term "bn \<alpha>"} to avoid~@{term "P"}, without touching~@{term "Formula.Act \<alpha> x"}\<close>
      obtain p where 1: "(p \<bullet> bn \<alpha>) \<sharp>* P" and 2: "supp (Formula.Act \<alpha> x) \<sharp>* p"
      proof (rule at_set_avoiding2[of "bn \<alpha>" "P" "Formula.Act \<alpha> x", THEN exE])
        show "finite (bn \<alpha>)" by (fact bn_finite)
      next
        show "finite (supp P)" by (fact finite_supp)
      next
        show "finite (supp (Formula.Act \<alpha> x))" by (fact finite_supp)
      next
        show "bn \<alpha> \<sharp>* Formula.Act \<alpha> x" by simp
      qed metis
      from 2 have eq: "Formula.Act \<alpha> x = Formula.Act (p \<bullet> \<alpha>) (p \<bullet> x)"
        using supp_perm_eq by fastforce

      with * have "P \<Turnstile>\<^sub>S Formula.Act (S_action.Act (p \<bullet> \<alpha>)) (S_transform (p \<bullet> x))"
        by simp
      with 1 obtain P' where trans: "P \<rightarrow>\<^sub>S \<langle>S_action.Act (p \<bullet> \<alpha>),P'\<rangle>" and valid: "P' \<Turnstile>\<^sub>S S_transform (p \<bullet> x)"
        by (metis S_transform.valid_Act_fresh bn_S_action.simps(1) bn_eqvt)

      from valid have "-p \<bullet> P' \<Turnstile>\<^sub>S S_transform x"
        by (metis (no_types, hide_lams) S_transform.valid_eqvt S_transform_eqvt permute_minus_cancel(1))
      then have "-p \<bullet> P' \<Turnstile> x"
        using Act.hyps(1) by metis
      then have "P' \<Turnstile> p \<bullet> x"
        by (metis permute_minus_cancel(1) valid_eqvt)

      moreover from trans have "P \<rightarrow> \<langle>p \<bullet> \<alpha>,P'\<rangle>"
        using S_transition_Act_iff by blast

      ultimately show "P \<Turnstile> Formula.Act \<alpha> x"
        using eq valid_Act by blast
    qed
  qed

end

context indexed_nominal_ts
begin

  text \<open>The following (alternative) proof of the ``$\rightarrow$'' direction of theorem
  @{thm S_transform_bisimilar_iff}, namely that bisimilarity in the $S$-transform implies
  bisimilarity in the original transition system, uses the fact that the $S$-transform(ation)
  preserves satisfaction of formulas, together with the fact that bisimilarity (in the
  $S$-transform) implies logical equivalence, and equivalence (in the original transition system)
  implies bisimilarity. However, since we proved the latter in the context of indexed nominal
  transition systems, this proof requires an indexed nominal transition system.\<close>

  interpretation S_transform: indexed_nominal_ts "(\<turnstile>\<^sub>S)" "(\<rightarrow>\<^sub>S)"
    by unfold_locales (fact S_satisfies_eqvt, fact S_transition_eqvt, fact card_idx_perm, fact card_idx_state)

  notation S_transform.bisimilar (infix "\<sim>\<cdot>\<^sub>S" 100)

  theorem "P \<sim>\<cdot>\<^sub>S Q \<longrightarrow> P \<sim>\<cdot> Q"
  proof
    assume "P \<sim>\<cdot>\<^sub>S Q"
    then have "S_transform.logically_equivalent P Q"
      by (fact S_transform.bisimilarity_implies_equivalence)
    with valid_iff_valid_S_transform have "logically_equivalent P Q"
      using logically_equivalent_def S_transform.logically_equivalent_def by blast
    then show "P \<sim>\<cdot> Q"
      by (fact equivalence_implies_bisimilarity)
  qed

end


subsection \<open>Translation of weak formulas into formulas without predicates\<close>

context indexed_weak_nominal_ts
begin

  notation S_satisfies (infix "\<turnstile>\<^sub>S" 70)

  interpretation S_transform: indexed_weak_nominal_ts "S_action.Act \<tau>" "(\<turnstile>\<^sub>S)" "(\<rightarrow>\<^sub>S)"
    by unfold_locales (fact S_satisfies_eqvt, fact S_transition_eqvt, simp add: tau_eqvt, fact card_idx_perm, fact card_idx_state, fact card_idx_nat)

  notation S_transform.valid (infix "\<Turnstile>\<^sub>S" 70)
  notation S_transform.weakly_bisimilar (infix "\<approx>\<cdot>\<^sub>S" 100)

  text \<open>The $S$-transform of a weak formula is not necessarily a weak formula. However, the image of
    all weak formulas under the $S$-transform is adequate for weak bisimilarity.\<close>

  corollary "P \<approx>\<cdot>\<^sub>S Q \<longleftrightarrow> (\<forall>x. weak_formula x \<longrightarrow> P \<Turnstile>\<^sub>S S_transform x \<longleftrightarrow> Q \<Turnstile>\<^sub>S S_transform x)"
    by (meson valid_iff_valid_S_transform weak_bisimilarity_implies_weak_equivalence weak_equivalence_implies_weak_bisimilarity S_transform_weakly_bisimilar_iff weakly_logically_equivalent_def)

  text \<open>For every weak formula, there is an equivalent weak formula over the $S$-transform.\<close>

  corollary
    assumes "weak_formula x"
    obtains y where "S_transform.weak_formula y" and "\<forall>P. P \<Turnstile> x \<longleftrightarrow> P \<Turnstile>\<^sub>S y"
  proof -
    let ?S = "{P. P \<Turnstile> x}"

    \<comment> \<open>@{term ?S} is finitely supported\<close>
    have "supp x supports ?S"
      unfolding supports_def proof (clarify)
      fix a b
      assume a: "a \<notin> supp x" and b: "b \<notin> supp x"
      {
        fix P
        from a and b have "(a \<rightleftharpoons> b) \<bullet> x = x"
          by (simp add: fresh_def swap_fresh_fresh)
        then have "(a \<rightleftharpoons> b) \<bullet> P \<Turnstile> x \<longleftrightarrow> P \<Turnstile> x"
          by (metis permute_swap_cancel valid_eqvt)
      }
      note * = this
      show "(a \<rightleftharpoons> b) \<bullet> ?S = ?S"
        by auto (metis mem_Collect_eq mem_permute_iff permute_swap_cancel "*", simp add: Collect_eqvt permute_fun_def "*")
    qed
    then have "finite (supp ?S)"
      using finite_supp supports_finite by blast

    \<comment> \<open>@{term ?S} is closed under weak bisimilarity\<close>
    moreover {
      fix P Q
      assume "P \<in> ?S" and "P \<approx>\<cdot>\<^sub>S Q"
      with \<open>weak_formula x\<close> have "Q \<in> ?S"
        using S_transform_weakly_bisimilar_iff weak_bisimilarity_implies_weak_equivalence weakly_logically_equivalent_def by auto
    }

    ultimately show ?thesis
      using S_transform.weak_expressive_completeness that by (metis (no_types, lifting) mem_Collect_eq)
  qed

end

end
