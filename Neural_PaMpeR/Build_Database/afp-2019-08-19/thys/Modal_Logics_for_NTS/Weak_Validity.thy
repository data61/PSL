theory Weak_Validity
imports
  Weak_Formula
  Validity
begin

section \<open>Weak Validity\<close>

text \<open>Weak formulas are a subset of (strong) formulas, and the definition of validity is simply
taken from the latter.  Here we prove some useful lemmas about the validity of weak modalities.
These are similar to corresponding lemmas about the validity of the (strong) action modality.\<close>

context indexed_weak_nominal_ts
begin

  lemma valid_weak_tau_modality_iff_tau_steps:
    "P \<Turnstile> weak_tau_modality x \<longleftrightarrow> (\<exists>n. P \<Turnstile> tau_steps x n)"
  unfolding weak_tau_modality_def by (auto simp add: map_bset.rep_eq)

  lemma tau_steps_iff_tau_transition:
    "(\<exists>n. P \<Turnstile> tau_steps x n) \<longleftrightarrow> (\<exists>P'. P \<Rightarrow> P' \<and> P' \<Turnstile> x)"
  proof
    assume "\<exists>n. P \<Turnstile> tau_steps x n"      
    then obtain n where "P \<Turnstile> tau_steps x n"
      by meson
    then show "\<exists>P'. P \<Rightarrow> P' \<and> P' \<Turnstile> x"
      proof (induct n arbitrary: P)
        case 0
        then show ?case
          by simp (metis tau_refl)
      next
        case (Suc n)
        then obtain P' where "P \<rightarrow> \<langle>\<tau>, P'\<rangle>" and "P' \<Turnstile> tau_steps x n"
          by (auto simp add: valid_Act_fresh[OF bn_tau_fresh])
        with Suc.hyps show ?case
          using tau_step by blast
      qed
  next
    assume "\<exists>P'. P \<Rightarrow> P' \<and> P' \<Turnstile> x"
    then obtain P' where "P \<Rightarrow> P'" and "P' \<Turnstile> x"
      by meson
    then show "\<exists>n. P \<Turnstile> tau_steps x n"
      proof (induct)
        case (tau_refl P) then have "P \<Turnstile> tau_steps x 0"
          by simp
        then show ?case
          by meson
      next
        case (tau_step P P' P'')
        then obtain n where "P' \<Turnstile> tau_steps x n"
          by meson
        with \<open>P \<rightarrow> \<langle>\<tau>,P'\<rangle>\<close> have "P \<Turnstile> tau_steps x (Suc n)"
          by (auto simp add: valid_Act_fresh[OF bn_tau_fresh])
        then show ?case
          by meson
      qed
  qed

  lemma valid_weak_tau_modality:
    "P \<Turnstile> weak_tau_modality x \<longleftrightarrow> (\<exists>P'. P \<Rightarrow> P' \<and> P' \<Turnstile> x)"
  by (metis valid_weak_tau_modality_iff_tau_steps tau_steps_iff_tau_transition)

  lemma valid_weak_action_modality:
    "P \<Turnstile> (\<langle>\<langle>\<alpha>\<rangle>\<rangle>x) \<longleftrightarrow> (\<exists>\<alpha>' x' P'. Act \<alpha> x = Act \<alpha>' x' \<and> P \<Rightarrow>\<langle>\<alpha>'\<rangle> P' \<and> P' \<Turnstile> x')"
    (is "?l \<longleftrightarrow> ?r")
  proof (cases "\<alpha> = \<tau>")
    case True show ?thesis
    proof
      assume "?l"
      with \<open>\<alpha> = \<tau>\<close> obtain P' where trans: "P \<Rightarrow> P'" and valid: "P' \<Turnstile> x"
        by (metis valid_weak_tau_modality weak_action_modality_tau)
      from trans have "P \<Rightarrow>\<langle>\<tau>\<rangle> P'"
        by simp
      with \<open>\<alpha> = \<tau>\<close> and valid show "?r"
        by blast
    next
      assume "?r"
      then obtain \<alpha>' x' P' where eq: "Act \<alpha> x = Act \<alpha>' x'" and trans: "P \<Rightarrow>\<langle>\<alpha>'\<rangle> P'" and valid: "P' \<Turnstile> x'"
        by blast
      from eq have "\<alpha>' = \<tau> \<and> x' = x"
        using \<open>\<alpha> = \<tau>\<close> by simp
      with trans and valid have "P \<Rightarrow> P'" and "P' \<Turnstile> x"
        by simp+
      with \<open>\<alpha> = \<tau>\<close> show "?l"
        by (metis valid_weak_tau_modality weak_action_modality_tau)
    qed
  next
    case False show ?thesis
    proof
      assume "?l"
      with \<open>\<alpha> \<noteq> \<tau>\<close> obtain Q where trans: "P \<Rightarrow> Q" and valid: "Q \<Turnstile> Act \<alpha> (weak_tau_modality x)"
        by (metis valid_weak_tau_modality weak_action_modality_not_tau)
      from valid obtain \<alpha>' x' Q' where eq: "Act \<alpha> (weak_tau_modality x) = Act \<alpha>' x'" and trans': "Q \<rightarrow> \<langle>\<alpha>',Q'\<rangle>" and valid': "Q' \<Turnstile> x'"
        by (metis valid_Act)

      from eq obtain p where p_\<alpha>: "\<alpha>' = p \<bullet> \<alpha>" and p_x: "x' = p \<bullet> weak_tau_modality x"
        by (metis Act_eq_iff_perm)
      with eq have "Act \<alpha> x = Act \<alpha>' (p \<bullet> x)"
        using Act_weak_tau_modality_eq_iff by simp

      moreover from valid' and p_x have "Q' \<Turnstile> weak_tau_modality (p \<bullet> x)"
        by simp
      then obtain P' where trans'': "Q' \<Rightarrow> P'" and valid'': "P' \<Turnstile> p \<bullet> x"
        by (metis valid_weak_tau_modality)
      from trans and trans' and trans'' have "P \<Rightarrow>\<langle>\<alpha>'\<rangle> P'"
        by (metis observable_transitionI weak_transition_stepI)
      ultimately show "?r"
        using valid'' by blast
    next
      assume "?r"
      then obtain \<alpha>' x' P' where eq: "Act \<alpha> x = Act \<alpha>' x'" and trans: "P \<Rightarrow>\<langle>\<alpha>'\<rangle> P'" and valid: "P' \<Turnstile> x'"
        by blast
      with \<open>\<alpha> \<noteq> \<tau>\<close> have \<alpha>': "\<alpha>' \<noteq> \<tau>"
        using eq by (metis Act_tau_eq_iff)
      with trans obtain Q Q' where trans': "P \<Rightarrow> Q" and trans'': "Q \<rightarrow> \<langle>\<alpha>',Q'\<rangle>" and trans''': "Q' \<Rightarrow> P'"
        by (meson observable_transition_def weak_transition_def)
      from trans''' and valid have "Q' \<Turnstile> weak_tau_modality x'"
        by (metis valid_weak_tau_modality)
      with trans'' have "Q \<Turnstile> Act \<alpha>' (weak_tau_modality x')"
        by (metis valid_Act)
      with trans' and \<alpha>' have "P \<Turnstile> \<langle>\<langle>\<alpha>'\<rangle>\<rangle>x'"
        by (metis valid_weak_tau_modality weak_action_modality_not_tau)
      moreover from eq have "(\<langle>\<langle>\<alpha>\<rangle>\<rangle>x) = (\<langle>\<langle>\<alpha>'\<rangle>\<rangle>x')"
        by (metis weak_action_modality_eq)
      ultimately show "?l"
        by simp
    qed
  qed

  text \<open>The binding names in the alpha-variant that witnesses validity may be chosen fresh for any
  finitely supported context.\<close>

  lemma valid_weak_action_modality_strong:
    assumes "finite (supp X)"
    shows "P \<Turnstile> (\<langle>\<langle>\<alpha>\<rangle>\<rangle>x) \<longleftrightarrow> (\<exists>\<alpha>' x' P'. Act \<alpha> x = Act \<alpha>' x' \<and> P \<Rightarrow>\<langle>\<alpha>'\<rangle> P' \<and> P' \<Turnstile> x' \<and> bn \<alpha>' \<sharp>* X)"
  proof
    assume "P \<Turnstile> \<langle>\<langle>\<alpha>\<rangle>\<rangle>x"
    then obtain \<alpha>' x' P' where eq: "Act \<alpha> x = Act \<alpha>' x'" and trans: "P \<Rightarrow>\<langle>\<alpha>'\<rangle> P'" and valid: "P' \<Turnstile> x'"
      by (metis valid_weak_action_modality)
    show "\<exists>\<alpha>' x' P'. Act \<alpha> x = Act \<alpha>' x' \<and> P \<Rightarrow>\<langle>\<alpha>'\<rangle> P' \<and> P' \<Turnstile> x' \<and> bn \<alpha>' \<sharp>* X"
      proof (cases "\<alpha>' = \<tau>")
        case True
        then show ?thesis
          using eq and trans and valid and bn_tau_fresh by blast
      next
        case False
        with trans obtain Q Q' where trans': "P \<Rightarrow> Q" and trans'': "Q \<rightarrow> \<langle>\<alpha>', Q'\<rangle>" and trans''': "Q' \<Rightarrow> P'"
          by (metis weak_transition_def observable_transition_def)
        have "finite (bn \<alpha>')"
          by (fact bn_finite)
        moreover note \<open>finite (supp X)\<close>
        moreover have "finite (supp (Act \<alpha>' x', \<langle>\<alpha>',Q'\<rangle>))"
          by (metis finite_Diff finite_UnI finite_supp supp_Pair supp_abs_residual_pair)
        moreover have "bn \<alpha>' \<sharp>* (Act \<alpha>' x', \<langle>\<alpha>',Q'\<rangle>)"
          by (auto simp add: fresh_star_def fresh_def supp_Pair supp_abs_residual_pair)
        ultimately obtain p where fresh_X: "(p \<bullet> bn \<alpha>') \<sharp>* X" and "supp (Act \<alpha>' x', \<langle>\<alpha>',Q'\<rangle>) \<sharp>* p"
          by (metis at_set_avoiding2)
        then have "supp (Act \<alpha>' x') \<sharp>* p" and "supp \<langle>\<alpha>',Q'\<rangle> \<sharp>* p"
          by (metis fresh_star_Un supp_Pair)+
        then have 1: "Act (p \<bullet> \<alpha>') (p \<bullet> x') = Act \<alpha>' x'" and 2: "\<langle>p \<bullet> \<alpha>', p \<bullet> Q'\<rangle> = \<langle>\<alpha>',Q'\<rangle>"
          by (metis Act_eqvt supp_perm_eq, metis abs_residual_pair_eqvt supp_perm_eq)
        from trans' and trans'' and trans''' have "P \<Rightarrow>\<langle>p \<bullet> \<alpha>'\<rangle> (p \<bullet> P')"
          using 2 by (metis observable_transitionI tau_transition_eqvt weak_transition_stepI)
        then show ?thesis
          using eq and 1 and valid and fresh_X by (metis bn_eqvt valid_eqvt)
      qed
  next
    assume "\<exists>\<alpha>' x' P'. Act \<alpha> x = Act \<alpha>' x' \<and> P \<Rightarrow>\<langle>\<alpha>'\<rangle> P' \<and> P' \<Turnstile> x' \<and> bn \<alpha>' \<sharp>* X"
    then show "P \<Turnstile> \<langle>\<langle>\<alpha>\<rangle>\<rangle>x"
      by (metis valid_weak_action_modality)
  qed

  lemma valid_weak_action_modality_fresh:
    assumes "bn \<alpha> \<sharp>* P"
    shows "P \<Turnstile> (\<langle>\<langle>\<alpha>\<rangle>\<rangle>x) \<longleftrightarrow> (\<exists>P'. P \<Rightarrow>\<langle>\<alpha>\<rangle> P' \<and> P' \<Turnstile> x)"
  proof
    assume "P \<Turnstile> \<langle>\<langle>\<alpha>\<rangle>\<rangle>x"

    moreover have "finite (supp P)"
      by (fact finite_supp)
    ultimately obtain \<alpha>' x' P' where
      eq: "Act \<alpha> x = Act \<alpha>' x'" and trans: "P \<Rightarrow>\<langle>\<alpha>'\<rangle> P'" and valid: "P' \<Turnstile> x'" and fresh: "bn \<alpha>' \<sharp>* P"
      by (metis valid_weak_action_modality_strong)

    from eq obtain p where p_\<alpha>: "\<alpha>' = p \<bullet> \<alpha>" and p_x: "x' = p \<bullet> x" and supp_p: "supp p \<subseteq> bn \<alpha> \<union> p \<bullet> bn \<alpha>"
      by (metis Act_eq_iff_perm_renaming)

    from assms and fresh have "(bn \<alpha> \<union> p \<bullet> bn \<alpha>) \<sharp>* P"
      using p_\<alpha> by (metis bn_eqvt fresh_star_Un)
    then have "supp p \<sharp>* P"
      using supp_p by (metis fresh_star_def subset_eq)
    then have p_P: "-p \<bullet> P = P"
      by (metis perm_supp_eq supp_minus_perm)

    from trans have "P \<Rightarrow>\<langle>\<alpha>\<rangle> (-p \<bullet> P')"
      using p_P p_\<alpha> by (metis permute_minus_cancel(1) weak_transition_eqvt)
    moreover from valid have "-p \<bullet> P' \<Turnstile> x"
      using p_x by (metis permute_minus_cancel(1) valid_eqvt)
    ultimately show "\<exists>P'. P \<Rightarrow>\<langle>\<alpha>\<rangle> P' \<and> P' \<Turnstile> x"
      by meson
  next
    assume "\<exists>P'. P \<Rightarrow>\<langle>\<alpha>\<rangle> P' \<and> P' \<Turnstile> x" then show "P \<Turnstile> \<langle>\<langle>\<alpha>\<rangle>\<rangle>x"
      by (metis valid_weak_action_modality)
  qed

end

end
