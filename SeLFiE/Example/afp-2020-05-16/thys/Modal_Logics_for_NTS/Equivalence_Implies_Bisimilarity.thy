theory Equivalence_Implies_Bisimilarity
imports
  Logical_Equivalence
begin

section \<open>Logical Equivalence Implies Bisimilarity\<close>

context indexed_nominal_ts
begin

  definition is_distinguishing_formula :: "('idx, 'pred, 'act) formula \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    ("_ distinguishes _ from _" [100,100,100] 100)
  where
    "x distinguishes P from Q \<equiv> P \<Turnstile> x \<and> \<not> Q \<Turnstile> x"

  lemma is_distinguishing_formula_eqvt (*[eqvt]*):
    assumes "x distinguishes P from Q" shows "(p \<bullet> x) distinguishes (p \<bullet> P) from (p \<bullet> Q)"
  using assms unfolding is_distinguishing_formula_def
  by (metis permute_minus_cancel(2) valid_eqvt)

  lemma equivalent_iff_not_distinguished: "(P =\<cdot> Q) \<longleftrightarrow> \<not>(\<exists>x. x distinguishes P from Q)"
  by (metis (full_types) is_distinguishing_formula_def logically_equivalent_def valid_Not)

  text \<open>There exists a distinguishing formula for~@{term P} and~@{term Q} whose support is contained
  in~@{term "supp P"}.\<close>

  lemma distinguished_bounded_support:
    assumes "x distinguishes P from Q"
    obtains y where "supp y \<subseteq> supp P" and "y distinguishes P from Q"
  proof -
    let ?B = "{p \<bullet> x|p. supp P \<sharp>* p}"
    have "supp P supports ?B"
    unfolding supports_def proof (clarify)
      fix a b
      assume a: "a \<notin> supp P" and b: "b \<notin> supp P"
      have "(a \<rightleftharpoons> b) \<bullet> ?B \<subseteq> ?B"
      proof
        fix x'
        assume "x' \<in> (a \<rightleftharpoons> b) \<bullet> ?B"
        then obtain p where 1: "x' = (a \<rightleftharpoons> b) \<bullet> p \<bullet> x" and 2: "supp P \<sharp>* p"
          by (auto simp add: permute_set_def)
        let ?q = "(a \<rightleftharpoons> b) + p"
        from 1 have "x' = ?q \<bullet> x"
          by simp
        moreover from a and b and 2 have "supp P \<sharp>* ?q"
          by (metis fresh_perm fresh_star_def fresh_star_plus swap_atom_simps(3))
        ultimately show "x' \<in> ?B" by blast
      qed
      moreover have "?B \<subseteq> (a \<rightleftharpoons> b) \<bullet> ?B"
      proof
        fix x'
        assume "x' \<in> ?B"
        then obtain p where 1: "x' = p \<bullet> x" and 2: "supp P \<sharp>* p"
          by auto
        let ?q = "(a \<rightleftharpoons> b) + p"
        from 1 have "x' = (a \<rightleftharpoons> b) \<bullet> ?q \<bullet> x"
          by simp
        moreover from a and b and 2 have "supp P \<sharp>* ?q"
          by (metis fresh_perm fresh_star_def fresh_star_plus swap_atom_simps(3))
        ultimately show "x' \<in> (a \<rightleftharpoons> b) \<bullet> ?B"
          using mem_permute_iff by blast
      qed
      ultimately show "(a \<rightleftharpoons> b) \<bullet> ?B = ?B" ..
    qed
    then have supp_B_subset_supp_P: "supp ?B \<subseteq> supp P"
      by (metis (erased, lifting) finite_supp supp_is_subset)
    then have finite_supp_B: "finite (supp ?B)"
      using finite_supp rev_finite_subset by blast
    have "?B \<subseteq> (\<lambda>p. p \<bullet> x) ` UNIV"
      by auto
    then have "|?B| \<le>o |UNIV :: perm set|"
      by (rule surj_imp_ordLeq)
    also have "|UNIV :: perm set| <o |UNIV :: 'idx set|"
      by (metis card_idx_perm)
    also have "|UNIV :: 'idx set| \<le>o natLeq +c |UNIV :: 'idx set|"
      by (metis Cnotzero_UNIV ordLeq_csum2)
    finally have card_B: "|?B| <o natLeq +c |UNIV :: 'idx set|" .
    let ?y = "Conj (Abs_bset ?B) :: ('idx, 'pred, 'act) formula"
    from finite_supp_B and card_B and supp_B_subset_supp_P have "supp ?y \<subseteq> supp P"
      by simp
    moreover have "?y distinguishes P from Q"
      unfolding is_distinguishing_formula_def proof
        from assms show "P \<Turnstile> ?y"
          by (auto simp add: card_B finite_supp_B) (metis is_distinguishing_formula_def supp_perm_eq valid_eqvt)
      next
        from assms show "\<not> Q \<Turnstile> ?y"
          by (auto simp add: card_B finite_supp_B) (metis is_distinguishing_formula_def permute_zero fresh_star_zero)
      qed
    ultimately show ?thesis ..
  qed

  lemma equivalence_is_bisimulation: "is_bisimulation logically_equivalent"
  proof -
    have "symp logically_equivalent"
      by (metis logically_equivalent_def sympI)
    moreover
    {
      fix P Q \<phi> assume "P =\<cdot> Q" then have "P \<turnstile> \<phi> \<longrightarrow> Q \<turnstile> \<phi>"
        by (metis logically_equivalent_def valid_Pred)
    }
    moreover
    {
      fix P Q \<alpha> P' assume "P =\<cdot> Q" and "bn \<alpha> \<sharp>* Q" and "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
      then have "\<exists>Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> P' =\<cdot> Q'"
        proof -
          {
            let ?Q' = "{Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>}"
            assume "\<forall>Q'\<in>?Q'. \<not> P' =\<cdot> Q'"
            then have "\<forall>Q'\<in>?Q'. \<exists>x :: ('idx, 'pred, 'act) formula. x distinguishes P' from Q'"
              by (metis equivalent_iff_not_distinguished)
            then have "\<forall>Q'\<in>?Q'. \<exists>x :: ('idx, 'pred, 'act) formula. supp x \<subseteq> supp P' \<and> x distinguishes P' from Q'"
              by (metis distinguished_bounded_support)
            then obtain f :: "'state \<Rightarrow> ('idx, 'pred, 'act) formula" where
              *: "\<forall>Q'\<in>?Q'. supp (f Q') \<subseteq> supp P' \<and> (f Q') distinguishes P' from Q'"
              by metis
            have "supp (f ` ?Q') \<subseteq> supp P'"
              by (rule set_bounded_supp, fact finite_supp, cut_tac "*", blast)
            then have finite_supp_image: "finite (supp (f ` ?Q'))"
              using finite_supp rev_finite_subset by blast
            have "|f ` ?Q'| \<le>o |UNIV :: 'state set|"
              by (metis card_of_UNIV card_of_image ordLeq_transitive)
            also have "|UNIV :: 'state set| <o |UNIV :: 'idx set|"
              by (metis card_idx_state)
            also have "|UNIV :: 'idx set| \<le>o natLeq +c |UNIV :: 'idx set|"
              by (metis Cnotzero_UNIV ordLeq_csum2)
            finally have card_image: "|f ` ?Q'| <o natLeq +c |UNIV :: 'idx set|" .
            let ?y = "Conj (Abs_bset (f ` ?Q')) :: ('idx, 'pred, 'act) formula"
            have "P \<Turnstile> Act \<alpha> ?y"
              unfolding valid_Act proof (standard+)
                show "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>" by fact
              next
                {
                  fix Q'
                  assume "Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>"
                  with "*" have "P' \<Turnstile> f Q'"
                    by (metis is_distinguishing_formula_def mem_Collect_eq)
                }
                then show "P' \<Turnstile> ?y"
                  by (simp add: finite_supp_image card_image)
              qed
            moreover have "\<not> Q \<Turnstile> Act \<alpha> ?y"
              proof
                assume "Q \<Turnstile> Act \<alpha> ?y"
                then obtain Q' where 1: "Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>" and 2: "Q' \<Turnstile> ?y"
                  using \<open>bn \<alpha> \<sharp>* Q\<close> by (metis valid_Act_fresh)
                from 2 have "\<And>Q''. Q \<rightarrow> \<langle>\<alpha>,Q''\<rangle> \<longrightarrow> Q' \<Turnstile> f Q''"
                  by (simp add: finite_supp_image card_image)
                with 1 and "*" show False
                  using is_distinguishing_formula_def by blast
              qed
            ultimately have False
              by (metis \<open>P =\<cdot> Q\<close> logically_equivalent_def)
          }
          then show ?thesis by auto
        qed
    }
    ultimately show ?thesis
      unfolding is_bisimulation_def by metis
  qed

  theorem equivalence_implies_bisimilarity: assumes "P =\<cdot> Q" shows "P \<sim>\<cdot> Q"
  using assms by (metis bisimilar_def equivalence_is_bisimulation)

end

end
