theory FL_Equivalence_Implies_Bisimilarity
imports
  FL_Logical_Equivalence
begin

section \<open>Logical Equivalence Implies \texorpdfstring{$F/L$}{F/L}-Bisimilarity\<close>

context indexed_effect_nominal_ts
begin

  definition is_distinguishing_formula :: "('idx, 'pred, 'act, 'effect) formula \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    ("_ distinguishes _ from _" [100,100,100] 100)
  where
    "x distinguishes P from Q \<equiv> P \<Turnstile> x \<and> \<not> Q \<Turnstile> x"

  lemma is_distinguishing_formula_eqvt (*[eqvt]*):
    assumes "x distinguishes P from Q" shows "(p \<bullet> x) distinguishes (p \<bullet> P) from (p \<bullet> Q)"
  using assms unfolding is_distinguishing_formula_def
  by (metis permute_minus_cancel(2) FL_valid_eqvt)

  lemma FL_equivalent_iff_not_distinguished:
    "FL_logically_equivalent F P Q \<longleftrightarrow> \<not>(\<exists>x. x \<in> \<A>[F] \<and> x distinguishes P from Q)"
  by (meson FL_logically_equivalent_def Not is_distinguishing_formula_def FL_valid_Not)

  text \<open>There exists a distinguishing formula for~@{term P} and~@{term Q} in~\<open>\<A>[F]\<close> whose
    support is contained in~@{term "supp (F,P)"}.\<close>

  lemma FL_distinguished_bounded_support:
    assumes "x \<in> \<A>[F]" and "x distinguishes P from Q"
    obtains y where "y \<in> \<A>[F]" and "supp y \<subseteq> supp (F,P)" and "y distinguishes P from Q"
  proof -
    let ?B = "{p \<bullet> x|p. supp (F,P) \<sharp>* p}"
    have "supp (F,P) supports ?B"
    unfolding supports_def proof (clarify)
      fix a b
      assume a: "a \<notin> supp (F,P)" and b: "b \<notin> supp (F,P)"
      have "(a \<rightleftharpoons> b) \<bullet> ?B \<subseteq> ?B"
      proof
        fix x'
        assume "x' \<in> (a \<rightleftharpoons> b) \<bullet> ?B"
        then obtain p where 1: "x' = (a \<rightleftharpoons> b) \<bullet> p \<bullet> x" and 2: "supp (F,P) \<sharp>* p"
          by (auto simp add: permute_set_def)
        let ?q = "(a \<rightleftharpoons> b) + p"
        from 1 have "x' = ?q \<bullet> x"
          by simp
        moreover from a and b and 2 have "supp (F,P) \<sharp>* ?q"
          by (metis fresh_perm fresh_star_def fresh_star_plus swap_atom_simps(3))
        ultimately show "x' \<in> ?B" by blast
      qed
      moreover have "?B \<subseteq> (a \<rightleftharpoons> b) \<bullet> ?B"
      proof
        fix x'
        assume "x' \<in> ?B"
        then obtain p where 1: "x' = p \<bullet> x" and 2: "supp (F,P) \<sharp>* p"
          by auto
        let ?q = "(a \<rightleftharpoons> b) + p"
        from 1 have "x' = (a \<rightleftharpoons> b) \<bullet> ?q \<bullet> x"
          by simp
        moreover from a and b and 2 have "supp (F,P) \<sharp>* ?q"
          by (metis fresh_perm fresh_star_def fresh_star_plus swap_atom_simps(3))
        ultimately show "x' \<in> (a \<rightleftharpoons> b) \<bullet> ?B"
          using mem_permute_iff by blast
      qed
      ultimately show "(a \<rightleftharpoons> b) \<bullet> ?B = ?B" ..
    qed
    then have supp_B_subset_supp_P: "supp ?B \<subseteq> supp (F,P)"
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

    let ?y = "Conj (Abs_bset ?B) :: ('idx, 'pred, 'act, 'effect) formula"

    from finite_supp_B and card_B and supp_B_subset_supp_P have "supp ?y \<subseteq> supp (F,P)"
      by simp
    moreover have "?y \<in> \<A>[F]"
      proof
        show "finite (supp (Abs_bset ?B :: (_,_,_,_) formula set['idx]))"
          using finite_supp_B card_B by simp
      next
        fix x'
        assume "x' \<in> set_bset (Abs_bset ?B :: (_,_,_,_) formula set['idx])"
        then obtain p where p_x: "x' = p \<bullet> x" and fresh_p: "supp (F,P) \<sharp>* p"
          using card_B by auto
        from fresh_p have "p \<bullet> F = F"
          using fresh_star_Pair fresh_star_supp_conv perm_supp_eq by blast
        with \<open>x \<in> \<A>[F]\<close> show "x' \<in> \<A>[F]"
          using p_x by (metis is_FL_formula_eqvt)
      qed
    moreover have "?y distinguishes P from Q"
      unfolding is_distinguishing_formula_def proof
        from \<open>x distinguishes P from Q\<close> show "P \<Turnstile> ?y"
          by (auto simp add: card_B finite_supp_B) (metis is_distinguishing_formula_def fresh_star_Un supp_Pair supp_perm_eq FL_valid_eqvt)
      next
        from \<open>x distinguishes P from Q\<close> show "\<not> Q \<Turnstile> ?y"
          by (auto simp add: card_B finite_supp_B) (metis is_distinguishing_formula_def permute_zero fresh_star_zero)
      qed
    ultimately show ?thesis
      using that by blast
  qed

  lemma FL_equivalence_is_L_bisimulation: "is_L_bisimulation FL_logically_equivalent"
  proof -
    {
      fix F have "symp (FL_logically_equivalent F)"
        by (rule sympI) (metis FL_logically_equivalent_def)
    }
    moreover
    {
      fix F P Q f \<phi>
      assume "FL_logically_equivalent F P Q" and "f \<in>\<^sub>f\<^sub>s F" and "\<langle>f\<rangle>P \<turnstile> \<phi>"
      then have "\<langle>f\<rangle>Q \<turnstile> \<phi>"
        by (metis FL_logically_equivalent_def Pred FL_valid_Pred)
    }
    moreover
    {
      fix F P Q f \<alpha> P'
      assume "FL_logically_equivalent F P Q" and "f \<in>\<^sub>f\<^sub>s F" and "bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F, f)" and "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
      then have "\<exists>Q'. \<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> FL_logically_equivalent (L (\<alpha>,F,f)) P' Q'"
        proof -
          {
            let ?Q' = "{Q'. \<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>}"
            assume "\<forall>Q'\<in>?Q'. \<not> FL_logically_equivalent (L (\<alpha>,F,f)) P' Q'"
            then have "\<forall>Q'\<in>?Q'. \<exists>x :: ('idx, 'pred, 'act, 'effect) formula. x \<in> \<A>[L (\<alpha>,F,f)] \<and> x distinguishes P' from Q'"
              by (metis FL_equivalent_iff_not_distinguished)
            then have "\<forall>Q'\<in>?Q'. \<exists>x :: ('idx, 'pred, 'act, 'effect) formula. x \<in> \<A>[L (\<alpha>,F,f)] \<and> supp x \<subseteq> supp (L (\<alpha>,F,f), P') \<and> x distinguishes P' from Q'"
              by (metis FL_distinguished_bounded_support)
            then obtain g :: "'state \<Rightarrow> ('idx, 'pred, 'act, 'effect) formula" where
              *: "\<forall>Q'\<in>?Q'. g Q' \<in> \<A>[L (\<alpha>,F,f)] \<and> supp (g Q') \<subseteq> supp (L (\<alpha>,F,f), P') \<and> (g Q') distinguishes P' from Q'"
              by metis
            have "supp (g ` ?Q') \<subseteq> supp (L (\<alpha>,F,f), P')"
              by (rule set_bounded_supp, fact finite_supp, cut_tac "*", blast)
            then have finite_supp_image: "finite (supp (g ` ?Q'))"
              using finite_supp rev_finite_subset by blast
            have "|g ` ?Q'| \<le>o |UNIV :: 'state set|"
              by (metis card_of_UNIV card_of_image ordLeq_transitive)
            also have "|UNIV :: 'state set| <o |UNIV :: 'idx set|"
              by (metis card_idx_state)
            also have "|UNIV :: 'idx set| \<le>o natLeq +c |UNIV :: 'idx set|"
              by (metis Cnotzero_UNIV ordLeq_csum2)
            finally have card_image: "|g ` ?Q'| <o natLeq +c |UNIV :: 'idx set|" .
            let ?y = "Conj (Abs_bset (g ` ?Q')) :: ('idx, 'pred, 'act, 'effect) formula"
            have "Act f \<alpha> ?y \<in> \<A>[F]"
              proof
                from \<open>f \<in>\<^sub>f\<^sub>s F\<close> show "f \<in>\<^sub>f\<^sub>s F" .
              next
                from \<open>bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F, f)\<close> show "bn \<alpha> \<sharp>* (F, f)"
                  using fresh_star_Pair by blast
              next
                show "Conj (Abs_bset (g ` ?Q')) \<in> \<A>[L (\<alpha>, F, f)]"
                  proof
                    show "finite (supp (Abs_bset (g ` ?Q') :: (_,_,_,_) formula set['idx]))"
                      using finite_supp_image card_image by simp
                  next
                    fix x'
                    assume "x' \<in> set_bset (Abs_bset (g ` ?Q') :: (_,_,_,_) formula set['idx])"
                    then obtain Q' where "x' = g Q'" and "\<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>"
                      using card_image by auto
                    with "*" show "x' \<in> \<A>[L (\<alpha>, F, f)]"
                      using mem_Collect_eq by blast
                  qed
              qed
            moreover have "P \<Turnstile> Act f \<alpha> ?y"
              unfolding FL_valid_Act proof (standard+)
                show "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle>" by fact
              next
                {
                  fix Q'
                  assume "\<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>"
                  with "*" have "P' \<Turnstile> g Q'"
                    by (metis is_distinguishing_formula_def mem_Collect_eq)
                }
                then show "P' \<Turnstile> ?y"
                  by (simp add: finite_supp_image card_image)
              qed
            moreover have "\<not> Q \<Turnstile> Act f \<alpha> ?y"
              proof
                assume "Q \<Turnstile> Act f \<alpha> ?y"
                then obtain Q' where 1: "\<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>" and 2: "Q' \<Turnstile> ?y"
                  using \<open>bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F, f)\<close> by (metis fresh_star_Pair FL_valid_Act_fresh)
                from 2 have "\<And>Q''. \<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q''\<rangle> \<longrightarrow> Q' \<Turnstile> g Q''"
                  by (simp add: finite_supp_image card_image)
                with 1 and "*" show False
                  using is_distinguishing_formula_def by blast
              qed
            ultimately have False
              by (metis \<open>FL_logically_equivalent F P Q\<close> FL_logically_equivalent_def)
          }
          then show ?thesis by auto
        qed
    }
    ultimately show ?thesis
      unfolding is_L_bisimulation_def by metis
  qed

  theorem FL_equivalence_implies_bisimilarity: assumes "FL_logically_equivalent F P Q" shows "P \<sim>\<cdot>[F] Q"
  using assms by (metis FL_bisimilar_def FL_equivalence_is_L_bisimulation)

end

end
