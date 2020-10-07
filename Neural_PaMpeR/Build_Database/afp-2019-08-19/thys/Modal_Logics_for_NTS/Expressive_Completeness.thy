theory Expressive_Completeness
imports
  Bisimilarity_Implies_Equivalence
  Equivalence_Implies_Bisimilarity
  Disjunction
begin

section \<open>Expressive Completeness\<close>

context indexed_nominal_ts
begin

  subsection \<open>Distinguishing formulas\<close>

  text \<open>Lemma \emph{distinguished\_bounded\_support} only shows the existence of a distinguishing
    formula, without stating what this formula looks like. We now define an explicit function that
    returns a distinguishing formula, in a way that this function is equivariant (on pairs of
    non-equivalent states).

    Note that this definition uses Hilbert's choice operator~$\varepsilon$, which is not necessarily
    equivariant. This is immediately remedied by a hull construction.\<close>

  definition distinguishing_formula :: "'state \<Rightarrow> 'state \<Rightarrow> ('idx, 'pred, 'act) formula" where
    "distinguishing_formula P Q \<equiv> Conj (Abs_bset {-p \<bullet> (\<some>x. supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))|p. True})"

  \<comment> \<open>just an auxiliary lemma that will be useful further below\<close>
  lemma distinguishing_formula_card_aux:
    "|{-p \<bullet> (\<some>x. supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))|p. True}| <o natLeq +c |UNIV :: 'idx set|"
  proof -
    let ?some = "\<lambda>p. (\<some>x. supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))"
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
  lemma distinguishing_formula_supp_aux:
    assumes "\<not> (P =\<cdot> Q)"
    shows "supp (Abs_bset {-p \<bullet> (\<some>x. supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))|p. True} :: _ set['idx]) \<subseteq> supp P"
  proof -
    let ?some = "\<lambda>p. (\<some>x. supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))"
    let ?B = "{-p \<bullet> ?some p|p. True}"

    {
      fix p
      from assms have "\<not> (p \<bullet> P =\<cdot> p \<bullet> Q)"
        by (metis logically_equivalent_eqvt permute_minus_cancel(2))
      then have "supp (?some p) \<subseteq> supp (p \<bullet> P)"
        using distinguished_bounded_support by (metis (mono_tags, lifting) equivalent_iff_not_distinguished someI_ex)
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

    from supp_B and distinguishing_formula_card_aux show ?thesis
      using supp_Abs_bset by blast
  qed

  lemma distinguishing_formula_eqvt [simp]:
    assumes "\<not> (P =\<cdot> Q)"
    shows "p \<bullet> distinguishing_formula P Q = distinguishing_formula (p \<bullet> P) (p \<bullet> Q)"
  proof -
    let ?some = "\<lambda>p. (\<some>x. supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))"
    let ?B = "{-p \<bullet> ?some p|p. True}"

    from assms have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp P"
      by (rule distinguishing_formula_supp_aux)
    then have "finite (supp (Abs_bset ?B :: _ set['idx]))"
      using finite_supp rev_finite_subset by blast
    with distinguishing_formula_card_aux have *: "p \<bullet> Conj (Abs_bset ?B) = Conj (Abs_bset (p \<bullet> ?B))"
      by simp

    let ?some' = "\<lambda>p'. (\<some>x. supp x \<subseteq> supp (p' \<bullet> p \<bullet> P) \<and> x distinguishes (p' \<bullet> p \<bullet> P) from (p' \<bullet> p \<bullet> Q))"
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
      unfolding distinguishing_formula_def by simp
  qed

  lemma supp_distinguishing_formula:
    assumes "\<not> (P =\<cdot> Q)"
    shows "supp (distinguishing_formula P Q) \<subseteq> supp P"
  proof -
    let ?some = "\<lambda>p. (\<some>x. supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))"
    let ?B = "{- p \<bullet> ?some p|p. True}"

    from assms have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp P"
      by (rule distinguishing_formula_supp_aux)
    moreover from this have "finite (supp (Abs_bset ?B :: _ set['idx]))"
      using finite_supp rev_finite_subset by blast
    ultimately show ?thesis
      unfolding distinguishing_formula_def by simp
  qed

  lemma distinguishing_formula_distinguishes:
    assumes "\<not> (P =\<cdot> Q)"
    shows "(distinguishing_formula P Q) distinguishes P from Q"
  proof -
    let ?some = "\<lambda>p. (\<some>x. supp x \<subseteq> supp (p \<bullet> P) \<and> x distinguishes (p \<bullet> P) from (p \<bullet> Q))"
    let ?B = "{- p \<bullet> ?some p|p. True}"

    {
      fix p
      have "(?some p) distinguishes (p \<bullet> P) from (p \<bullet> Q)"
        using assms 
        by (metis (mono_tags, lifting) is_distinguishing_formula_eqvt distinguished_bounded_support equivalent_iff_not_distinguished someI_ex)
    }
    note some_distinguishes = this

    {
      fix P'
      from assms have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp P"
        by (rule distinguishing_formula_supp_aux)
      then have "finite (supp (Abs_bset ?B :: _ set['idx]))"
        using finite_supp rev_finite_subset by blast
      with distinguishing_formula_card_aux have "P' \<Turnstile> distinguishing_formula P Q \<longleftrightarrow> (\<forall>x\<in>?B. P' \<Turnstile> x)"
        unfolding distinguishing_formula_def by simp
    }
    note valid_distinguishing_formula = this

    {
      fix p
      have "P \<Turnstile> -p \<bullet> ?some p"
        by (metis (mono_tags) is_distinguishing_formula_def permute_minus_cancel(2) some_distinguishes valid_eqvt)
    }
    then have "P \<Turnstile> distinguishing_formula P Q"
      using valid_distinguishing_formula by blast

    moreover have "\<not> Q \<Turnstile> distinguishing_formula P Q"
      using valid_distinguishing_formula by (metis (mono_tags, lifting) is_distinguishing_formula_def mem_Collect_eq permute_minus_cancel(1) some_distinguishes valid_eqvt)

    ultimately show "(distinguishing_formula P Q) distinguishes P from Q"
      using is_distinguishing_formula_def by blast
  qed


  subsection \<open>Characteristic formulas\<close>
  
  text \<open>A \emph{characteristic formula} for a state~$P$ is valid for (exactly) those states that are
    bisimilar to~$P$.\<close>

  definition characteristic_formula :: "'state \<Rightarrow> ('idx, 'pred, 'act) formula" where
    "characteristic_formula P \<equiv> Conj (Abs_bset {distinguishing_formula P Q|Q. \<not> (P =\<cdot> Q)})"

  \<comment> \<open>just an auxiliary lemma that will be useful further below\<close>
  lemma characteristic_formula_card_aux:
    "|{distinguishing_formula P Q|Q. \<not> (P =\<cdot> Q)}| <o natLeq +c |UNIV :: 'idx set|"
  proof -
    let ?B = "{distinguishing_formula P Q|Q. \<not> (P =\<cdot> Q)}"

    have "?B \<subseteq> (distinguishing_formula P) ` UNIV"
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
  lemma characteristic_formula_supp_aux:
    shows "supp (Abs_bset {distinguishing_formula P Q|Q. \<not> (P =\<cdot> Q)} :: _ set['idx]) \<subseteq> supp P"
  proof -
    let ?B = "{distinguishing_formula P Q|Q. \<not> (P =\<cdot> Q)}"

    {
      fix x
      assume "x \<in> ?B"
      then obtain Q where "x = distinguishing_formula P Q" and "\<not> (P =\<cdot> Q)"
        by blast
      with supp_distinguishing_formula have "supp x \<subseteq> supp P"
        by metis
    }
    note "*" = this
    have supp_B: "supp ?B \<subseteq> supp P"
      by (rule set_bounded_supp, fact finite_supp, cut_tac "*", blast)

    from supp_B and characteristic_formula_card_aux show ?thesis
      using supp_Abs_bset by blast
  qed

  lemma characteristic_formula_eqvt (*[eqvt]*) [simp]:
    "p \<bullet> characteristic_formula P = characteristic_formula (p \<bullet> P)"
  proof -
    let ?B = "{distinguishing_formula P Q|Q. \<not> (P =\<cdot> Q)}"

    have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp P"
      by (fact characteristic_formula_supp_aux)
    then have "finite (supp (Abs_bset ?B :: _ set['idx]))"
      using finite_supp rev_finite_subset by blast
    with characteristic_formula_card_aux have *: "p \<bullet> Conj (Abs_bset ?B) = Conj (Abs_bset (p \<bullet> ?B))"
      by simp

    let ?B' = "{distinguishing_formula (p \<bullet> P) Q|Q. \<not> ((p \<bullet> P) =\<cdot> Q)}"

    have "p \<bullet> ?B = ?B'"
    proof
      {
        fix px
        assume "px \<in> p \<bullet> ?B"
        then obtain x where 1: "px = p \<bullet> x" and 2: "x \<in> ?B"
          by (metis (no_types, lifting) image_iff permute_set_eq_image)
        from 2 obtain Q where 3: "x = distinguishing_formula P Q" and 4: "\<not> (P =\<cdot> Q)"
          by blast
        with 1 have "px = distinguishing_formula (p \<bullet> P) (p \<bullet> Q)"
          by simp
        moreover from 4 have "\<not> ((p \<bullet> P) =\<cdot> (p \<bullet> Q))"
          by (metis logically_equivalent_eqvt permute_minus_cancel(2))
        ultimately have "px \<in> ?B'"
          by blast
      }
      then show "p \<bullet> ?B \<subseteq> ?B'"
        by blast
    next
      {
        fix x
        assume "x \<in> ?B'"
        then obtain Q where 1: "x = distinguishing_formula (p \<bullet> P) Q" and 2: "\<not> ((p \<bullet> P) =\<cdot> Q)"
          by blast
        from 2 have "\<not> (P =\<cdot> (-p \<bullet> Q))"
          by (metis logically_equivalent_eqvt permute_minus_cancel(1))
        moreover from this and 1 have "x = p \<bullet> distinguishing_formula P (-p \<bullet> Q)"
          by simp
        ultimately have "x \<in> p \<bullet> ?B"
          using mem_permute_iff by blast
      }
      then show "?B' \<subseteq> p \<bullet> ?B"
        by blast
    qed

    with "*" show ?thesis
      unfolding characteristic_formula_def by simp
  qed

  lemma characteristic_formula_eqvt_raw [simp]:
    "p \<bullet> characteristic_formula = characteristic_formula"
    by (simp add: permute_fun_def)

  lemma characteristic_formula_is_characteristic':
    "Q \<Turnstile> characteristic_formula P \<longleftrightarrow> P =\<cdot> Q"
  proof -
    let ?B = "{distinguishing_formula P Q|Q. \<not> (P =\<cdot> Q)}"

    {
      fix P'
      have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp P"
        by (fact characteristic_formula_supp_aux)
      then have "finite (supp (Abs_bset ?B :: _ set['idx]))"
        using finite_supp rev_finite_subset by blast
      with characteristic_formula_card_aux have "P' \<Turnstile> characteristic_formula P \<longleftrightarrow> (\<forall>x\<in>?B. P' \<Turnstile> x)"
        unfolding characteristic_formula_def by simp
    }
    note valid_characteristic_formula = this

    show ?thesis
    proof
      assume *: "Q \<Turnstile> characteristic_formula P"
      show "P =\<cdot> Q"
      proof (rule ccontr)
        assume "\<not> (P =\<cdot> Q)"
        with "*" show False
          using distinguishing_formula_distinguishes is_distinguishing_formula_def valid_characteristic_formula by auto
      qed
    next
      assume "P =\<cdot> Q"
      moreover have "P \<Turnstile> characteristic_formula P"
        using distinguishing_formula_distinguishes is_distinguishing_formula_def valid_characteristic_formula by auto
      ultimately show "Q \<Turnstile> characteristic_formula P"
        using logically_equivalent_def by blast
    qed
  qed

  lemma characteristic_formula_is_characteristic:
    "Q \<Turnstile> characteristic_formula P \<longleftrightarrow> P \<sim>\<cdot> Q"
    using characteristic_formula_is_characteristic' by (meson bisimilarity_implies_equivalence equivalence_implies_bisimilarity)


  subsection \<open>Expressive completeness\<close>
  
  text \<open>Every finitely supported set of states that is closed under bisimulation can be described by
    a formula; namely, by a disjunction of characteristic formulas.\<close>

  theorem expressive_completeness:
    assumes "finite (supp S)"
    and "\<And>P Q. P \<in> S \<Longrightarrow> P \<sim>\<cdot> Q \<Longrightarrow> Q \<in> S"
    shows "P \<Turnstile> Disj (Abs_bset (characteristic_formula ` S)) \<longleftrightarrow> P \<in> S"
  proof -
    let ?B = "characteristic_formula ` S"

    have "?B \<subseteq> characteristic_formula ` UNIV"
      by auto
    then have "|?B| \<le>o |UNIV :: 'state set|"
      by (rule surj_imp_ordLeq)
    also have "|UNIV :: 'state set| <o |UNIV :: 'idx set|"
      by (metis card_idx_state)
    also have "|UNIV :: 'idx set| \<le>o natLeq +c |UNIV :: 'idx set|"
      by (metis Cnotzero_UNIV ordLeq_csum2)
    finally have card_B: "|?B| <o natLeq +c |UNIV :: 'idx set|" .

    have "eqvt image" and "eqvt characteristic_formula"
      by (simp add: eqvtI)+
    then have "supp ?B \<subseteq> supp S"
      using supp_fun_eqvt supp_fun_app supp_fun_app_eqvt by blast
    with card_B have "supp (Abs_bset ?B :: _ set['idx]) \<subseteq> supp S"
      using supp_Abs_bset by blast
    with \<open>finite (supp S)\<close> have "finite (supp (Abs_bset ?B :: _ set['idx]))"
      using finite_supp rev_finite_subset by blast
    with card_B have "P \<Turnstile> Disj (Abs_bset (characteristic_formula ` S)) \<longleftrightarrow> (\<exists>x\<in>?B. P \<Turnstile> x)"
      by simp

    with \<open>\<And>P Q. P \<in> S \<Longrightarrow> P \<sim>\<cdot> Q \<Longrightarrow> Q \<in> S\<close> show ?thesis
      using characteristic_formula_is_characteristic characteristic_formula_is_characteristic' logically_equivalent_def by fastforce
  qed

end

end
