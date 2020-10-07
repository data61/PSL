(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Cardinality of Partial Equivalence Relations\<close>

theory Card_Partial_Equiv_Relations
imports
  Card_Equiv_Relations
begin

subsection \<open>Definition of Partial Equivalence Relation\<close>

definition partial_equiv :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"
where
  "partial_equiv A R = (R \<subseteq> A \<times> A \<and> sym R \<and> trans R)"

lemma partial_equivI:
  assumes "R \<subseteq> A \<times> A" "sym R" "trans R"
  shows "partial_equiv A R"
using assms unfolding partial_equiv_def by auto

lemma partial_equiv_iff:
  shows "partial_equiv A R \<longleftrightarrow> (\<exists>A' \<subseteq> A. equiv A' R)"
proof
  assume "partial_equiv A R"
  from \<open>partial_equiv A R\<close> have "R `` A \<subseteq> A"
    unfolding partial_equiv_def by blast
  moreover have "equiv (R `` A) R"
  proof (rule equivI)
    from \<open>partial_equiv A R\<close> show "sym R"
      unfolding partial_equiv_def by blast
    from \<open>partial_equiv A R\<close> show "trans R"
      unfolding partial_equiv_def by blast
    show "refl_on (R `` A) R"
    proof (rule refl_onI)
      show "R \<subseteq> R `` A \<times> R `` A"
      proof
        fix p
        assume "p \<in> R"
        obtain x y where "p = (x, y)" by fastforce
        moreover have "x \<in> R `` A"
          using \<open>p \<in> R\<close> \<open>p = (x, y)\<close> \<open>partial_equiv A R\<close>
            partial_equiv_def sym_def by fastforce
        moreover have "y \<in> R `` A"
          using \<open>p \<in> R\<close> \<open>p = (x, y)\<close> \<open>R `` A \<subseteq> A\<close> \<open>x \<in> R `` A\<close> by blast
        ultimately show "p \<in> R `` A \<times> R `` A" by auto
      qed
    next
      fix y
      assume "y \<in> R `` A"
      from this obtain x where "(x, y) \<in> R" by auto
      from \<open>(x, y) \<in> R\<close> have "(y, x) \<in> R"
        using \<open>sym R\<close> by (meson symE)
      from \<open>(x, y) \<in> R\<close> \<open>(y, x) \<in> R\<close> show "(y, y) \<in> R"
        using \<open>trans R\<close> by (meson transE)
    qed
  qed
  ultimately show "\<exists>A'\<subseteq>A. equiv A' R" by blast
next
  assume "\<exists>A'\<subseteq>A. equiv A' R"
  from this obtain A' where "A' \<subseteq> A" and "equiv A' R" by blast
  show "partial_equiv A R"
  proof (rule partial_equivI)
    from \<open>equiv A' R\<close> \<open>A' \<subseteq> A\<close> show "R \<subseteq> A \<times> A"
      using equiv_class_eq_iff by fastforce
    from \<open>equiv A' R\<close> show "sym R"
      using equivE by blast
    from \<open>equiv A' R\<close> show "trans R"
      using equivE by blast
  qed
qed

subsection \<open>Construction of all Partial Equivalence Relations for a Given Set\<close>

definition all_partial_equivs_on :: "'a set \<Rightarrow> (('a \<times> 'a) set) set"
where
  "all_partial_equivs_on A =
    do {
      k \<leftarrow> {0..card A};
      A' \<leftarrow> {A'. A' \<subseteq> A \<and> card A' = k};
      {R. equiv A' R}
    }"

lemma all_partial_equivs_on:
  assumes "finite A"
  shows "all_partial_equivs_on A = {R. partial_equiv A R}"
proof
  show "all_partial_equivs_on A \<subseteq> {R. partial_equiv A R}"
  proof
    fix R
    assume "R \<in> all_partial_equivs_on A"
    from this obtain A' where "A' \<subseteq> A" and "equiv A' R"
      unfolding all_partial_equivs_on_def by auto
    from this have "partial_equiv A R"
      using partial_equiv_iff by blast
    from this show "R \<in> {R. partial_equiv A R}" ..
  qed
next
  show "{R. partial_equiv A R} \<subseteq> all_partial_equivs_on A"
  proof
    fix R
    assume "R \<in> {R. partial_equiv A R}"
    from this obtain A' where "A' \<subseteq> A" and "equiv A' R"
      using partial_equiv_iff by (metis mem_Collect_eq)
    moreover have "card A' \<in> {0..card A}"
      using \<open>A' \<subseteq> A\<close> \<open>finite A\<close> by (simp add: card_mono)
    ultimately show "R \<in> all_partial_equivs_on A"
      unfolding all_partial_equivs_on_def
      by (auto simp del: atLeastAtMost_iff)
  qed
qed

subsection \<open>Injectivity of the Set Construction\<close>

lemma equiv_inject:
  assumes "equiv A R" "equiv B R"
  shows "A = B"
proof -
  from assms have "R \<subseteq> A \<times> A" "R \<subseteq> B \<times> B" by (simp add: equiv_type)+
  moreover from assms have "\<forall>x\<in>A. (x, x) \<in> R" "\<forall>x\<in>B. (x, x) \<in> R"
    by (simp add: eq_equiv_class)+
  ultimately show ?thesis
    using mem_Sigma_iff subset_antisym subset_eq by blast
qed

lemma injectivity:
  assumes "(A' \<subseteq> A \<and> card A' = k) \<and> (A'' \<subseteq> A \<and> card A'' = k')"
  assumes "equiv A' R \<and> equiv A'' R'"
  assumes "R = R'"
  shows "A' = A''" "k = k'"
proof -
  from \<open>R = R'\<close> assms(2) show "A' = A''"
    using equiv_inject by fast
  from this assms(1) show "k = k'" by simp
qed

subsection \<open>Cardinality Theorem of Partial Equivalence Relations\<close>

theorem card_partial_equiv:
  assumes "finite A"
  shows "card {R. partial_equiv A R} = Bell (card A + 1)"
proof -
  let ?expr = "do {
      k \<leftarrow> {0..card A};
      A' \<leftarrow> {A'. A' \<subseteq> A \<and> card A' = k};
      {R. equiv A' R}
    }"
  have "card {R. partial_equiv A R} = card (all_partial_equivs_on A)"
    using \<open>finite A\<close> by (simp add: all_partial_equivs_on)
  also have "card (all_partial_equivs_on A) = card ?expr"
    unfolding all_partial_equivs_on_def ..
  also have "card ?expr = (\<Sum>k = 0..card A. (card A choose k) * Bell k)"
  proof -
    let "?S \<bind> ?comp" = ?expr
    {
      fix k
      assume k: "k \<in> {..card A}"
      let ?expr = "?comp k"
      let "?S \<bind> ?comp" = ?expr
      have "finite ?S" using \<open>finite A\<close> by simp
      moreover {
        fix A'
        assume A': "A' \<in> {A'. A' \<subseteq> A \<and> card A' = k}"
        from this have "A' \<subseteq> A" and "card A' = k" by auto
        let ?expr = "?comp A'"
        have "finite A'"
          using \<open>finite A\<close> \<open>A' \<subseteq> A\<close> by (simp add: finite_subset)
        have "card ?expr = Bell k"
          using \<open>finite A\<close> \<open>finite A'\<close> \<open>A' \<subseteq> A\<close> \<open>card A' = k\<close>
          by (simp add: card_equiv_rel_eq_Bell)
        moreover have "finite ?expr"
          using \<open>finite A'\<close> by (simp add: finite_equiv)
        ultimately have "finite ?expr \<and> card ?expr = Bell k" by blast
      } note inner = this
      moreover have "disjoint_family_on ?comp ?S"
        by (injectivity_solver rule: injectivity(1))
      moreover have "card ?S = card A choose k"
        using \<open>finite A\<close> by (simp add: n_subsets)
      ultimately have "card ?expr = (card A choose k) * Bell k" (is "_ = ?formula")
        by (subst card_bind_constant) auto
      moreover have "finite ?expr"
        using \<open>finite ?S\<close> inner by (auto intro!: finite_bind)
      ultimately have "finite ?expr \<and> card ?expr = ?formula" by blast
    }
    moreover have "finite ?S" by simp
    moreover have "disjoint_family_on ?comp ?S"
      by (injectivity_solver rule: injectivity(2))
    ultimately show "card ?expr = (\<Sum>k = 0..card A. (card A choose k) * Bell k)"
      by (subst card_bind) auto
  qed
  also have "\<dots> = (\<Sum>k\<le>card A. (card A choose k) * Bell k)"
    by (auto intro: sum.cong)
  also have "\<dots> = Bell (card A + 1)"
    using Bell_recursive_eq by simp
  finally show ?thesis .
qed

end
