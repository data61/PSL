theory Weak_Expressive_Completeness
imports
  Weak_Bisimilarity_Implies_Equivalence
  Weak_Equivalence_Implies_Bisimilarity
  Disjunction
begin

section \<open>Weak Expressive Completeness\<close>

context indexed_weak_nominal_ts
begin

  subsection \<open>Distinguishing weak formulas\<close>

  text \<open>Lemma \emph{distinguished\_bounded\_support} only shows the existence of a distinguishing
    weak formula, without stating what this formula looks like. We now define an explicit function
    that returns a distinguishing weak formula, in a way that this function is equivariant (on pairs
    of non-weakly-equivalent states).

    Note that this definition uses Hilbert's choice operator~$\varepsilon$, which is not necessarily
    equivariant. This is immediately remedied by a hull construction.\<close>

  definition distinguishing_weak_formula :: "'state \<Rightarrow> 'state \<Rightarrow> ('idx, 'pred, 'act) formula" where
    "distinguishing_weak_formula P Q \<equiv> Conj (Abs_bset {-p \<bullet> (\<some>x. weak_formula x \<and> supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))|p. True})"

  \<comment> \<open>just an auxiliary lemma that will be useful further below\<close>
  lemma distinguishing_weak_formula_card_aux:
    "|{-p \<bullet> (\<some>x. weak_formula x \<and> supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))|p. True}| <o natLeq +c |UNIV :: 'idx set|"
  proof -
    let ?some = "\<lambda>p. (\<some>x. weak_formula x \<and> supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))"
    let ?B = "{-p \<bullet> ?some p|p. True}"

    have "?B \<subseteq> (\<lambda>p. -p \<bullet> ?some p) ` UNIV"
      by auto
    then have "|?B| \<le>o |UNIV :: perm set|"
      by (rule surj_imp_ordLeq)
    also have "|UNIV :: perm set| <o |UNIV :: 'idx set|"
      by (metis card_idx_perm)
    also have "|UNIV :: 'idx set| \<le>o natLeq +c |UNIV :: 'idx set|"
      by (metis Cnotzero_UNIV ordLeq_csum2)
    finally show ?thesis .
  qed

  \<comment> \<open>just an auxiliary lemma that will be useful further below\<close>
  lemma distinguishing_weak_formula_supp_aux:
    assumes "\<not> (P \<equiv>\<cdot> Q)"
    shows "supp (Abs_bset {-p \<bullet> (\<some>x. weak_formula x \<and> supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))|p. True} :: _ set['idx]) \<subseteq> supp P"
  proof -
    let ?some = "\<lambda>p. (\<some>x. weak_formula x \<and> supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))"
    let ?B = "{-p \<bullet> ?some p|p. True}"

    {
      fix p
      from assms have "\<not> (p \<bullet> P \<equiv>\<cdot> p \<bullet> Q)"
        by (metis weakly_logically_equivalent_eqvt permute_minus_cancel(2))
      then have "supp (?some p) \<subseteq> supp (p \<bullet> P)"
        using distinguished_bounded_support by (metis (mono_tags, lifting) weakly_equivalent_iff_not_distinguished someI_ex)
    }
    note supp_some = this

    {
      fix x
      assume "x \<in> ?B"
      then obtain p where "x = -p \<bullet> ?some p"
        by blast
      with supp_some have "supp (p \<bullet> x) \<subseteq> supp (p \<bullet> P)"
        by simp
      then have "supp x \<subseteq> supp P"
        by (metis (full_types) permute_boolE subset_eqvt supp_eqvt)
    }
    note "*" = this
    have supp_B: "supp ?B \<subseteq> supp P"
      by (rule set_bounded_supp, fact finite_supp, cut_tac "*", blast)

    from supp_B and distinguishing_weak_formula_card_aux show ?thesis
      using supp_Abs_bset by blast
  qed

  lemma distinguishing_weak_formula_eqvt [simp]:
    assumes "\<not> (P \<equiv>\<cdot> Q)"
    shows "p \<bullet> distinguishing_weak_formula P Q = distinguishing_weak_formula (p \<bullet> P) (p \<bullet> Q)"
  proof -
    let ?some = "\<lambda>p. (\<some>x. weak_formula x \<and> supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))"
    let ?B = "{-p \<bullet> ?some p|p. True}"

    from assms have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp P"
      by (rule distinguishing_weak_formula_supp_aux)
    then have "finite (supp (Abs_bset ?B :: _ set['idx]))"
      using finite_supp rev_finite_subset by blast
    with distinguishing_weak_formula_card_aux have *: "p \<bullet> Conj (Abs_bset ?B) = Conj (Abs_bset (p \<bullet> ?B))"
      by simp

    let ?some' = "\<lambda>p'. (\<some>x. weak_formula x \<and> supp x \<subseteq> supp (p' \<bullet> p \<bullet> P) \<and> x distinguishes (p' \<bullet> p \<bullet> P) from (p' \<bullet> p \<bullet> Q))"
    let ?B' = "{-p' \<bullet> ?some' p'|p'. True}"

    have "p \<bullet> ?B = ?B'"
    proof
      {
        fix px
        assume "px \<in> p \<bullet> ?B"
        then obtain x where 1: "px = p \<bullet> x" and 2: "x \<in> ?B"
          by (metis (no_types, lifting) image_iff permute_set_eq_image)
        from 2 obtain p' where 3: "x = -p' \<bullet> ?some p'"
          by blast
        from 1 and 3 have "px = -(p' - p) \<bullet> ?some' (p' - p)"
          by simp
        then have "px \<in> ?B'"
          by blast
      }
      then show "p \<bullet> ?B \<subseteq> ?B'"
        by blast
    next
      {
        fix x
        assume "x \<in> ?B'"
        then obtain p' where "x = -p' \<bullet> ?some' p'"
          by blast
        then have "x = p \<bullet> -(p' + p) \<bullet> ?some (p' + p)"
          by (simp add: add.inverse_distrib_swap)
        then have "x \<in> p \<bullet> ?B"
          using mem_permute_iff by blast
      }
      then show "?B' \<subseteq> p \<bullet> ?B"
        by blast
    qed

    with "*" show ?thesis
      unfolding distinguishing_weak_formula_def by simp
  qed

  lemma supp_distinguishing_weak_formula:
    assumes "\<not> (P \<equiv>\<cdot> Q)"
    shows "supp (distinguishing_weak_formula P Q) \<subseteq> supp P"
  proof -
    let ?some = "\<lambda>p. (\<some>x. weak_formula x \<and> supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))"
    let ?B = "{- p \<bullet> ?some p|p. True}"

    from assms have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp P"
      by (rule distinguishing_weak_formula_supp_aux)
    moreover from this have "finite (supp (Abs_bset ?B :: _ set['idx]))"
      using finite_supp rev_finite_subset by blast
    ultimately show ?thesis
      unfolding distinguishing_weak_formula_def by simp
  qed

  lemma distinguishing_weak_formula_distinguishes:
    assumes "\<not> (P \<equiv>\<cdot> Q)"
    shows "(distinguishing_weak_formula P Q) distinguishes P from Q"
  proof -
    let ?some = "\<lambda>p. (\<some>x. weak_formula x \<and> supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))"
    let ?B = "{- p \<bullet> ?some p|p. True}"

    {
      fix p
      from assms have "\<not> (p \<bullet> P) \<equiv>\<cdot> (p \<bullet> Q)"
        by (metis permute_minus_cancel(2) weakly_logically_equivalent_eqvt)
      then have "(?some p) distinguishes (p \<bullet> P) from (p \<bullet> Q)"
        by (metis (mono_tags, lifting) distinguished_bounded_support weakly_equivalent_iff_not_distinguished someI_ex)
    }
    note some_distinguishes = this

    {
      fix P'
      from assms have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp P"
        by (rule distinguishing_weak_formula_supp_aux)
      then have "finite (supp (Abs_bset ?B :: _ set['idx]))"
        using finite_supp rev_finite_subset by blast
      with distinguishing_weak_formula_card_aux have "P' \<Turnstile> distinguishing_weak_formula P Q \<longleftrightarrow> (\<forall>x\<in>?B. P' \<Turnstile> x)"
        unfolding distinguishing_weak_formula_def by simp
    }
    note valid_distinguishing_formula = this

    {
      fix p
      have "P \<Turnstile> -p \<bullet> ?some p"
        by (metis (mono_tags) is_distinguishing_formula_def permute_minus_cancel(2) some_distinguishes valid_eqvt)
    }
    then have "P \<Turnstile> distinguishing_weak_formula P Q"
      using valid_distinguishing_formula by blast

    moreover have "\<not> Q \<Turnstile> distinguishing_weak_formula P Q"
      using valid_distinguishing_formula by (metis (mono_tags, lifting) is_distinguishing_formula_def mem_Collect_eq permute_minus_cancel(1) some_distinguishes valid_eqvt)

    ultimately show "(distinguishing_weak_formula P Q) distinguishes P from Q"
      using is_distinguishing_formula_def by blast
  qed

  lemma distinguishing_weak_formula_is_weak:
    assumes "\<not> (P \<equiv>\<cdot> Q)"
    shows "weak_formula (distinguishing_weak_formula P Q)"
  proof -
    let ?some = "\<lambda>p. (\<some>x. weak_formula x \<and> supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))"
    let ?B = "{- p \<bullet> ?some p|p. True}"

    from assms have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp P"
      by (rule distinguishing_weak_formula_supp_aux)
    then have "finite (supp (Abs_bset ?B :: _ set['idx]))"
      using finite_supp rev_finite_subset by blast

    moreover have "set_bset (Abs_bset ?B :: _ set['idx]) = ?B"
      using distinguishing_weak_formula_card_aux Abs_bset_inverse' by simp

    moreover
    {
      fix x
      assume "x \<in> ?B"
      then obtain p where "x = -p \<bullet> ?some p"
        by blast
      moreover from assms have "\<not> (p \<bullet> P) \<equiv>\<cdot> (p \<bullet> Q)"
        by (metis permute_minus_cancel(2) weakly_logically_equivalent_eqvt)
      then have "weak_formula (?some p)"
        by (metis (mono_tags, lifting) distinguished_bounded_support weakly_equivalent_iff_not_distinguished someI_ex)
      ultimately have "weak_formula x"
        by simp
    }

    ultimately show ?thesis
      unfolding distinguishing_weak_formula_def using wf_Conj by blast
  qed


  subsection \<open>Characteristic weak formulas\<close>
  
  text \<open>A \emph{characteristic weak formula} for a state~$P$ is valid for (exactly) those states
    that are weakly bisimilar to~$P$.\<close>

  definition characteristic_weak_formula :: "'state \<Rightarrow> ('idx, 'pred, 'act) formula" where
    "characteristic_weak_formula P \<equiv> Conj (Abs_bset {distinguishing_weak_formula P Q|Q. \<not> (P \<equiv>\<cdot> Q)})"

  \<comment> \<open>just an auxiliary lemma that will be useful further below\<close>
  lemma characteristic_weak_formula_card_aux:
    "|{distinguishing_weak_formula P Q|Q. \<not> (P \<equiv>\<cdot> Q)}| <o natLeq +c |UNIV :: 'idx set|"
  proof -
    let ?B = "{distinguishing_weak_formula P Q|Q. \<not> (P \<equiv>\<cdot> Q)}"

    have "?B \<subseteq> (distinguishing_weak_formula P) ` UNIV"
      by auto
    then have "|?B| \<le>o |UNIV :: 'state set|"
      by (rule surj_imp_ordLeq)
    also have "|UNIV :: 'state set| <o |UNIV :: 'idx set|"
      by (metis card_idx_state)
    also have "|UNIV :: 'idx set| \<le>o natLeq +c |UNIV :: 'idx set|"
      by (metis Cnotzero_UNIV ordLeq_csum2)
    finally show ?thesis .
  qed

  \<comment> \<open>just an auxiliary lemma that will be useful further below\<close>
  lemma characteristic_weak_formula_supp_aux:
    shows "supp (Abs_bset {distinguishing_weak_formula P Q|Q. \<not> (P \<equiv>\<cdot> Q)} :: _ set['idx]) \<subseteq> supp P"
  proof -
    let ?B = "{distinguishing_weak_formula P Q|Q. \<not> (P \<equiv>\<cdot> Q)}"

    {
      fix x
      assume "x \<in> ?B"
      then obtain Q where "x = distinguishing_weak_formula P Q" and "\<not> (P \<equiv>\<cdot> Q)"
        by blast
      with supp_distinguishing_weak_formula have "supp x \<subseteq> supp P"
        by metis
    }
    note "*" = this
    have supp_B: "supp ?B \<subseteq> supp P"
      by (rule set_bounded_supp, fact finite_supp, cut_tac "*", blast)

    from supp_B and characteristic_weak_formula_card_aux show ?thesis
      using supp_Abs_bset by blast
  qed

  lemma characteristic_weak_formula_eqvt (*[eqvt]*) [simp]:
    "p \<bullet> characteristic_weak_formula P = characteristic_weak_formula (p \<bullet> P)"
  proof -
    let ?B = "{distinguishing_weak_formula P Q|Q. \<not> (P \<equiv>\<cdot> Q)}"

    have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp P"
      by (fact characteristic_weak_formula_supp_aux)
    then have "finite (supp (Abs_bset ?B :: _ set['idx]))"
      using finite_supp rev_finite_subset by blast
    with characteristic_weak_formula_card_aux have *: "p \<bullet> Conj (Abs_bset ?B) = Conj (Abs_bset (p \<bullet> ?B))"
      by simp

    let ?B' = "{distinguishing_weak_formula (p \<bullet> P) Q|Q. \<not> ((p \<bullet> P) \<equiv>\<cdot> Q)}"

    have "p \<bullet> ?B = ?B'"
    proof
      {
        fix px
        assume "px \<in> p \<bullet> ?B"
        then obtain x where 1: "px = p \<bullet> x" and 2: "x \<in> ?B"
          by (metis (no_types, lifting) image_iff permute_set_eq_image)
        from 2 obtain Q where 3: "x = distinguishing_weak_formula P Q" and 4: "\<not> (P \<equiv>\<cdot> Q)"
          by blast
        with 1 have "px = distinguishing_weak_formula (p \<bullet> P) (p \<bullet> Q)"
          by simp
        moreover from 4 have "\<not> (p \<bullet> P) \<equiv>\<cdot> (p \<bullet> Q)"
          by (metis weakly_logically_equivalent_eqvt permute_minus_cancel(2))
        ultimately have "px \<in> ?B'"
          by blast
      }
      then show "p \<bullet> ?B \<subseteq> ?B'"
        by blast
    next
      {
        fix x
        assume "x \<in> ?B'"
        then obtain Q where 1: "x = distinguishing_weak_formula (p \<bullet> P) Q" and 2: "\<not> (p \<bullet> P) \<equiv>\<cdot> Q"
          by blast
        from 2 have "\<not> P \<equiv>\<cdot> (-p \<bullet> Q)"
          by (metis weakly_logically_equivalent_eqvt permute_minus_cancel(1))
        moreover from this and 1 have "x = p \<bullet> distinguishing_weak_formula P (-p \<bullet> Q)"
          by simp
        ultimately have "x \<in> p \<bullet> ?B"
          using mem_permute_iff by blast
      }
      then show "?B' \<subseteq> p \<bullet> ?B"
        by blast
    qed

    with "*" show ?thesis
      unfolding characteristic_weak_formula_def by simp
  qed

  lemma characteristic_weak_formula_eqvt_raw [simp]:
    "p \<bullet> characteristic_weak_formula = characteristic_weak_formula"
    by (simp add: permute_fun_def)

  lemma characteristic_weak_formula_is_weak:
    "weak_formula (characteristic_weak_formula P)"
  proof -
    let ?B = "{distinguishing_weak_formula P Q|Q. \<not> (P \<equiv>\<cdot> Q)}"

    have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp P"
      by (fact characteristic_weak_formula_supp_aux)
    then have "finite (supp (Abs_bset ?B :: _ set['idx]))"
      using finite_supp rev_finite_subset by blast

    moreover have "set_bset (Abs_bset ?B :: _ set['idx]) = ?B"
      using characteristic_weak_formula_card_aux Abs_bset_inverse' by simp

    moreover
    {
      fix x
      assume "x \<in> ?B"
      then have "weak_formula x"
        using distinguishing_weak_formula_is_weak by blast
    }

    ultimately show ?thesis
      unfolding characteristic_weak_formula_def using wf_Conj by presburger
  qed

  lemma characteristic_weak_formula_is_characteristic':
    "Q \<Turnstile> characteristic_weak_formula P \<longleftrightarrow> P \<equiv>\<cdot> Q"
  proof -
    let ?B = "{distinguishing_weak_formula P Q|Q. \<not> (P \<equiv>\<cdot> Q)}"

    {
      fix P'
      have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp P"
        by (fact characteristic_weak_formula_supp_aux)
      then have "finite (supp (Abs_bset ?B :: _ set['idx]))"
        using finite_supp rev_finite_subset by blast
      with characteristic_weak_formula_card_aux have "P' \<Turnstile> characteristic_weak_formula P \<longleftrightarrow> (\<forall>x\<in>?B. P' \<Turnstile> x)"
        unfolding characteristic_weak_formula_def by simp
    }
    note valid_characteristic_formula = this

    show ?thesis
    proof
      assume *: "Q \<Turnstile> characteristic_weak_formula P"
      show "P \<equiv>\<cdot> Q"
      proof (rule ccontr)
        assume "\<not> (P \<equiv>\<cdot> Q)"
        with "*" show False
          using distinguishing_weak_formula_distinguishes is_distinguishing_formula_def valid_characteristic_formula by auto
      qed
    next
      assume "P \<equiv>\<cdot> Q"
      moreover have "P \<Turnstile> characteristic_weak_formula P"
        using distinguishing_weak_formula_distinguishes is_distinguishing_formula_def valid_characteristic_formula by auto
      ultimately show "Q \<Turnstile> characteristic_weak_formula P"
        using weakly_logically_equivalent_def characteristic_weak_formula_is_weak by blast
    qed
  qed

  lemma characteristic_weak_formula_is_characteristic:
    "Q \<Turnstile> characteristic_weak_formula P \<longleftrightarrow> P \<approx>\<cdot> Q"
    using characteristic_weak_formula_is_characteristic' by (meson weak_bisimilarity_implies_weak_equivalence weak_equivalence_implies_weak_bisimilarity)


  subsection \<open>Weak expressive completeness\<close>
  
  text \<open>Every finitely supported set of states that is closed under weak bisimulation can be
    described by a weak formula; namely, by a disjunction of characteristic weak formulas.\<close>

  theorem weak_expressive_completeness:
    assumes "finite (supp S)"
    and "\<And>P Q. P \<in> S \<Longrightarrow> P \<approx>\<cdot> Q \<Longrightarrow> Q \<in> S"
    shows "P \<Turnstile> Disj (Abs_bset (characteristic_weak_formula ` S)) \<longleftrightarrow> P \<in> S"
    and "weak_formula (Disj (Abs_bset (characteristic_weak_formula ` S)))"
  proof -
    let ?B = "characteristic_weak_formula ` S"

    have "?B \<subseteq> characteristic_weak_formula ` UNIV"
      by auto
    then have "|?B| \<le>o |UNIV :: 'state set|"
      by (rule surj_imp_ordLeq)
    also have "|UNIV :: 'state set| <o |UNIV :: 'idx set|"
      by (metis card_idx_state)
    also have "|UNIV :: 'idx set| \<le>o natLeq +c |UNIV :: 'idx set|"
      by (metis Cnotzero_UNIV ordLeq_csum2)
    finally have card_B: "|?B| <o natLeq +c |UNIV :: 'idx set|" .

    have "eqvt image" and "eqvt characteristic_weak_formula"
      by (simp add: eqvtI)+
    then have supp_B: "supp ?B \<subseteq> supp S"
      using supp_fun_eqvt supp_fun_app supp_fun_app_eqvt by blast
    with card_B have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp S"
      using supp_Abs_bset by blast
    with \<open>finite (supp S)\<close> have "finite (supp (Abs_bset ?B :: _ set['idx]))"
      using finite_supp rev_finite_subset by blast

    with card_B have "P \<Turnstile> Disj (Abs_bset (characteristic_weak_formula ` S)) \<longleftrightarrow> (\<exists>x\<in>?B. P \<Turnstile> x)"
      by simp

    with \<open>\<And>P Q. P \<in> S \<Longrightarrow> P \<approx>\<cdot> Q \<Longrightarrow> Q \<in> S\<close> show "P \<Turnstile> Disj (Abs_bset (characteristic_weak_formula ` S)) \<longleftrightarrow> P \<in> S"
      using characteristic_weak_formula_is_characteristic characteristic_weak_formula_is_characteristic' weakly_logically_equivalent_def by fastforce

    \<comment> \<open>it remains to show that the disjunction is a weak formula\<close>

    have "eqvt Formula.Not"
      by (simp add: eqvtI)
    with supp_B and \<open>eqvt image\<close> have supp_Not_B: "supp (Formula.Not ` ?B) \<subseteq> supp S"
      using supp_fun_eqvt supp_fun_app supp_fun_app_eqvt by blast

    have "|Formula.Not ` ?B| \<le>o |?B|"
      by simp
    also note card_B
    finally have card_not_B: "|Formula.Not ` ?B| <o natLeq +c |UNIV :: 'idx set|" .

    with supp_Not_B have "supp (Abs_bset (Formula.Not ` ?B) :: _ set['idx]) \<subseteq> supp S"
      using supp_Abs_bset by blast
    with \<open>finite (supp S)\<close> have "finite (supp (Abs_bset (Formula.Not ` ?B) :: _ set['idx]))"
      using finite_supp rev_finite_subset by blast

    moreover have "\<And>x. x \<in> Formula.Not ` ?B \<Longrightarrow> weak_formula x"
      using characteristic_weak_formula_is_weak wf_Not by auto

    moreover from card_B have *: "map_bset Formula.Not (Abs_bset ?B :: _ set['idx]) = (Abs_bset (Formula.Not ` ?B) :: _ set['idx])"
      using map_bset.abs_eq[unfolded eq_onp_def] by blast

    moreover from card_not_B have "set_bset (Abs_bset (Formula.Not ` ?B) :: _ set['idx]) = Formula.Not ` ?B"
      by simp

    ultimately show "weak_formula (Disj (Abs_bset (characteristic_weak_formula ` S)))"
      unfolding Disj_def by (metis wf_Conj wf_Not)
  qed

end

end
