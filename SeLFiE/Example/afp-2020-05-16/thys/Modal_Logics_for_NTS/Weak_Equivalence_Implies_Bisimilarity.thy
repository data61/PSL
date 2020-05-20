theory Weak_Equivalence_Implies_Bisimilarity
imports
  Weak_Logical_Equivalence
begin

section \<open>Weak Logical Equivalence Implies Weak Bisimilarity\<close>

context indexed_weak_nominal_ts
begin

  definition is_distinguishing_formula :: "('idx, 'pred, 'act) formula \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    ("_ distinguishes _ from _" [100,100,100] 100)
  where
    "x distinguishes P from Q \<equiv> P \<Turnstile> x \<and> \<not> Q \<Turnstile> x"

  lemma is_distinguishing_formula_eqvt (*[eqvt]*) [simp]:
    assumes "x distinguishes P from Q" shows "(p \<bullet> x) distinguishes (p \<bullet> P) from (p \<bullet> Q)"
  using assms unfolding is_distinguishing_formula_def
  by (metis permute_minus_cancel(2) valid_eqvt)

  lemma weakly_equivalent_iff_not_distinguished: "(P \<equiv>\<cdot> Q) \<longleftrightarrow> \<not>(\<exists>x. weak_formula x \<and> x distinguishes P from Q)"
  by (meson is_distinguishing_formula_def weakly_logically_equivalent_def valid_Not wf_Not)

  text \<open>There exists a distinguishing weak formula for~@{term P} and~@{term Q} whose support is
  contained in~@{term "supp P"}.\<close>

  lemma distinguished_bounded_support:
    assumes "weak_formula x" and "x distinguishes P from Q"
    obtains y where "weak_formula y" and "supp y \<subseteq> supp P" and "y distinguishes P from Q"
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
    have "weak_formula ?y"
    proof
      show "finite (supp (Abs_bset ?B :: _ set['idx]))"
        using finite_supp_B card_B by simp
    next
      fix x' assume "x' \<in> set_bset (Abs_bset ?B :: _ set['idx])"
      with card_B obtain p where "x' = p \<bullet> x"
        using Abs_bset_inverse mem_Collect_eq by auto
      then show "weak_formula x'"
        using \<open>weak_formula x\<close> by (metis weak_formula_eqvt)
    qed
    moreover from finite_supp_B and card_B and supp_B_subset_supp_P have "supp ?y \<subseteq> supp P"
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

  lemma weak_equivalence_is_weak_bisimulation: "is_weak_bisimulation weakly_logically_equivalent"
  proof -
    have "symp weakly_logically_equivalent"
      by (metis weakly_logically_equivalent_def sympI)
    moreover  \<comment> \<open>weak static implication\<close>
    {
      fix P Q \<phi> assume "P \<equiv>\<cdot> Q" and "P \<turnstile> \<phi>"
      then have "\<exists>Q'. Q \<Rightarrow> Q' \<and> P \<equiv>\<cdot> Q' \<and> Q' \<turnstile> \<phi>"
        proof -
          {
            let ?Q' = "{Q'. Q \<Rightarrow> Q' \<and> Q' \<turnstile> \<phi>}"
            assume "\<forall>Q'\<in>?Q'. \<not> P \<equiv>\<cdot> Q'"
            then have "\<forall>Q'\<in>?Q'. \<exists>x :: ('idx, 'pred, 'act) formula. weak_formula x \<and> x distinguishes P from Q'"
              by (metis weakly_equivalent_iff_not_distinguished)
            then have "\<forall>Q'\<in>?Q'. \<exists>x :: ('idx, 'pred, 'act) formula. weak_formula x \<and> supp x \<subseteq> supp P \<and> x distinguishes P from Q'"
              by (metis distinguished_bounded_support)
            then obtain f :: "'state \<Rightarrow> ('idx, 'pred, 'act) formula" where
              *: "\<forall>Q'\<in>?Q'. weak_formula (f Q') \<and> supp (f Q') \<subseteq> supp P \<and> (f Q') distinguishes P from Q'"
              by metis
            have "supp (f ` ?Q') \<subseteq> supp P"
              by (rule set_bounded_supp, fact finite_supp, cut_tac "*", blast)
            then have finite_supp_image: "finite (supp (f ` ?Q'))"
              using finite_supp rev_finite_subset by blast
            have "|f ` ?Q'| \<le>o |UNIV :: 'state set|"
              using card_of_UNIV card_of_image ordLeq_transitive by blast
            also have "|UNIV :: 'state set| <o |UNIV :: 'idx set|"
              by (metis card_idx_state)
            also have "|UNIV :: 'idx set| \<le>o natLeq +c |UNIV :: 'idx set|"
              by (metis Cnotzero_UNIV ordLeq_csum2)
            finally have card_image: "|f ` ?Q'| <o natLeq +c |UNIV :: 'idx set|" .

            let ?y = "Conj (Abs_bset (f ` ?Q')) :: ('idx, 'pred, 'act) formula"
            have "weak_formula ?y"
              proof (standard+)
                show "finite (supp (Abs_bset (f ` ?Q') :: _ set['idx]))"
                  using finite_supp_image card_image by simp
              next
                fix x assume "x \<in> set_bset (Abs_bset (f ` ?Q') :: _ set['idx])"
                with card_image obtain Q' where "Q' \<in> ?Q'" and "x = f Q'"
                  using Abs_bset_inverse imageE set_bset set_bset_to_set_bset by auto
                then show "weak_formula x"
                  using "*" by metis
              qed

            let ?z = "\<langle>\<langle>\<tau>\<rangle>\<rangle>(Conj (binsert (Pred \<phi>) (bsingleton ?y)))"
            have "weak_formula ?z"
              by standard (fact \<open>weak_formula ?y\<close>)
            moreover have "P \<Turnstile> ?z"
              proof -
                have "P \<Rightarrow>\<langle>\<tau>\<rangle> P"
                  by simp
                moreover
                {
                  fix Q'
                  assume "Q \<Rightarrow> Q' \<and> Q' \<turnstile> \<phi>"
                  with "*" have "P \<Turnstile> f Q'"
                    by (metis is_distinguishing_formula_def mem_Collect_eq)
                }
                with \<open>P \<turnstile> \<phi>\<close> have "P \<Turnstile> Conj (binsert (Pred \<phi>) (bsingleton ?y))"
                  by (simp add: binsert.rep_eq finite_supp_image card_image)
                ultimately show ?thesis
                  using valid_weak_action_modality by blast
              qed
            moreover have "\<not> Q \<Turnstile> ?z"
              proof
                assume "Q \<Turnstile> ?z"
                then obtain Q' where 1: "Q \<Rightarrow> Q'" and "Q' \<Turnstile> Conj (binsert (Pred \<phi>) (bsingleton ?y))"
                  using valid_weak_action_modality by auto
                then have 2: "Q' \<turnstile> \<phi>" and 3: "Q' \<Turnstile> ?y"
                  by (simp add: binsert.rep_eq finite_supp_image card_image)+
                from 3 have "\<And>Q''. Q \<Rightarrow> Q'' \<and> Q'' \<turnstile> \<phi> \<longrightarrow> Q' \<Turnstile> f Q''"
                  by (simp add: finite_supp_image card_image)
                with 1 and 2 and "*" show False
                  using is_distinguishing_formula_def by blast
              qed
            ultimately have False
              by (metis \<open>P \<equiv>\<cdot> Q\<close> weakly_logically_equivalent_def)
          }
          then show ?thesis
            by blast
        qed
    }
    moreover  \<comment> \<open>weak simulation\<close>
    {
      fix P Q \<alpha> P' assume "P \<equiv>\<cdot> Q" and "bn \<alpha> \<sharp>* Q" and "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
      then have "\<exists>Q'. Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q' \<and> P' \<equiv>\<cdot> Q'"
        proof -
          {
            let ?Q' = "{Q'. Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q'}"
            assume "\<forall>Q'\<in>?Q'. \<not> P' \<equiv>\<cdot> Q'"
            then have "\<forall>Q'\<in>?Q'. \<exists>x :: ('idx, 'pred, 'act) formula. weak_formula x \<and> x distinguishes P' from Q'"
              by (metis weakly_equivalent_iff_not_distinguished)
            then have "\<forall>Q'\<in>?Q'. \<exists>x :: ('idx, 'pred, 'act) formula. weak_formula x \<and> supp x \<subseteq> supp P' \<and> x distinguishes P' from Q'"
              by (metis distinguished_bounded_support)
            then obtain f :: "'state \<Rightarrow> ('idx, 'pred, 'act) formula" where
              *: "\<forall>Q'\<in>?Q'. weak_formula (f Q') \<and> supp (f Q') \<subseteq> supp P' \<and> (f Q') distinguishes P' from Q'"
              by metis
            have "supp P' supports (f ` ?Q')"
              unfolding supports_def proof (clarify)
                fix a b
                assume a: "a \<notin> supp P'" and b: "b \<notin> supp P'"
                have "(a \<rightleftharpoons> b) \<bullet> (f ` ?Q') \<subseteq> f ` ?Q'"
                proof
                  fix x
                  assume "x \<in> (a \<rightleftharpoons> b) \<bullet> (f ` ?Q')"
                  then obtain Q' where 1: "x = (a \<rightleftharpoons> b) \<bullet> f Q'" and 2: "Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q'"
                    by auto (metis (no_types, lifting) imageE image_eqvt mem_Collect_eq permute_set_eq_image)
                  with "*" and a and b have "a \<notin> supp (f Q')" and "b \<notin> supp (f Q')"
                    by auto
                  with 1 have "x = f Q'"
                    by (metis fresh_perm fresh_star_def supp_perm_eq swap_atom)
                  with 2 show "x \<in> f ` ?Q'"
                    by simp
                qed
                moreover have "f ` ?Q' \<subseteq> (a \<rightleftharpoons> b) \<bullet> (f ` ?Q')"
                proof
                  fix x
                  assume "x \<in> f ` ?Q'"
                  then obtain Q' where 1: "x = f Q'" and 2: "Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q'"
                    by auto
                  with "*" and a and b have "a \<notin> supp (f Q')" and "b \<notin> supp (f Q')"
                    by auto
                  with 1 have "x = (a \<rightleftharpoons> b) \<bullet> f Q'"
                    by (metis fresh_perm fresh_star_def supp_perm_eq swap_atom)
                  with 2 show "x \<in> (a \<rightleftharpoons> b) \<bullet> (f ` ?Q')"
                    using mem_permute_iff by blast
                qed
                ultimately show "(a \<rightleftharpoons> b) \<bullet> (f ` ?Q') = f ` ?Q'" ..
              qed
            then have supp_image_subset_supp_P': "supp (f ` ?Q') \<subseteq> supp P'"
              by (metis (erased, lifting) finite_supp supp_is_subset)
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
            have "weak_formula (\<langle>\<langle>\<alpha>\<rangle>\<rangle>?y)"
              proof (standard+)
                show "finite (supp (Abs_bset (f ` ?Q') :: _ set['idx]))"
                  using finite_supp_image card_image by simp
              next
                fix x assume "x \<in> set_bset (Abs_bset (f ` ?Q') :: _ set['idx])"
                with card_image obtain Q' where "Q' \<in> ?Q'" and "x = f Q'"
                  using Abs_bset_inverse imageE set_bset set_bset_to_set_bset by auto
                then show "weak_formula x"
                  using "*" by metis
              qed
            moreover have "P \<Turnstile> \<langle>\<langle>\<alpha>\<rangle>\<rangle>?y"
              unfolding valid_weak_action_modality proof (standard+)
                from \<open>P \<rightarrow> \<langle>\<alpha>,P'\<rangle>\<close> show "P \<Rightarrow>\<langle>\<alpha>\<rangle> P'"
                  by simp
              next
                {
                  fix Q'
                  assume "Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q'"
                  with "*" have "P' \<Turnstile> f Q'"
                    by (metis is_distinguishing_formula_def mem_Collect_eq)
                }
                then show "P' \<Turnstile> ?y"
                  by (simp add: finite_supp_image card_image)
              qed
            moreover have "\<not> Q \<Turnstile> \<langle>\<langle>\<alpha>\<rangle>\<rangle>?y"
              proof
                assume "Q \<Turnstile> \<langle>\<langle>\<alpha>\<rangle>\<rangle>?y"
                then obtain Q' where 1: "Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q'" and 2: "Q' \<Turnstile> ?y"
                  using \<open>bn \<alpha> \<sharp>* Q\<close> by (metis valid_weak_action_modality_fresh)
                from 2 have "\<And>Q''. Q \<Rightarrow>\<langle>\<alpha>\<rangle> Q'' \<longrightarrow> Q' \<Turnstile> f Q''"
                  by (simp add: finite_supp_image card_image)
                with 1 and "*" show False
                  using is_distinguishing_formula_def by blast
              qed
            ultimately have False
              by (metis \<open>P \<equiv>\<cdot> Q\<close> weakly_logically_equivalent_def)
          }
          then show ?thesis by auto
        qed
    }
    ultimately show ?thesis
      unfolding is_weak_bisimulation_def by metis
  qed

  theorem weak_equivalence_implies_weak_bisimilarity: assumes "P \<equiv>\<cdot> Q" shows "P \<approx>\<cdot> Q"
  using assms by (metis weakly_bisimilar_def weak_equivalence_is_weak_bisimulation)

end

end
