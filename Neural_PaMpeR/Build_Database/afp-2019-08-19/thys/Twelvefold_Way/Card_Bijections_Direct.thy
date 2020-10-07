(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Direct Proofs for Cardinality of Bijections\<close>

theory Card_Bijections_Direct
imports
  Equiv_Relations_on_Functions
  Twelvefold_Way_Core
begin

subsection \<open>Bijections from A to B up to a Permutation on A\<close>

subsubsection \<open>Equivalence Class\<close>

lemma bijections_in_domain_permutation:
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B"
proof -
  from assms obtain f where f: "f \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}"
    by (metis finite_same_card_bij_on_ext_funcset mem_Collect_eq)
  moreover have proj_f: "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} = domain_permutation A B `` {f}"
  proof
    from f show "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} \<subseteq> domain_permutation A B `` {f}"
      unfolding domain_permutation_def
      by (auto elim: obtain_domain_permutation_for_two_bijections)
  next
    show "domain_permutation A B `` {f} \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}"
    proof
      fix f'
      assume "f' \<in> domain_permutation A B `` {f}"
      have "(f', f) \<in> domain_permutation A B"
        using \<open>f' \<in> domain_permutation A B `` {f}\<close> equiv_domain_permutation[of A B]
        by (simp add: equiv_class_eq_iff)
      from this obtain p where "p permutes A" "\<forall>x\<in>A. f' x = f (p x)"
        unfolding domain_permutation_def by auto
      from this have "bij_betw (f \<circ> p) A B"
        using bij_betw_comp_iff f permutes_imp_bij by fastforce
      from this have "bij_betw f' A B"
        using \<open>\<forall>x\<in>A. f' x = f (p x)\<close>
        by (metis (mono_tags, lifting) bij_betw_cong comp_apply)
      moreover have "f' \<in> A \<rightarrow>\<^sub>E B"
        using \<open>f' \<in> domain_permutation A B `` {f}\<close>
        unfolding domain_permutation_def by auto
      ultimately show "f' \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}" by simp
    qed
  qed
  ultimately show ?thesis by (simp add: quotientI)
qed

lemma bij_betw_quotient_domain_permutation_eq:
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B = {{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}}"
proof
  show "{{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}} \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B"
    by (simp add: bijections_in_domain_permutation[OF assms])
next
  show "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B \<subseteq> {{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}}"
  proof
    fix F
    assume F_in: "F \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B"
    have "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B = {F \<in> ((A \<rightarrow>\<^sub>E B) // domain_permutation A B). univ (\<lambda>f. bij_betw f A B) F}"
      using equiv_domain_permutation[of A B] bij_betw_respects_domain_permutation[of A B] by (simp only: univ_preserves_predicate)
    from F_in this have "F \<in> (A \<rightarrow>\<^sub>E B) // domain_permutation A B"
      and "univ (\<lambda>f. bij_betw f A B) F"
      by blast+
    have "F = {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}"
    proof
      have "\<forall>f \<in> F. f \<in> A \<rightarrow>\<^sub>E B"
        using \<open>F \<in> (A \<rightarrow>\<^sub>E B) // domain_permutation A B\<close>
        by (metis ImageE equiv_class_eq_iff equiv_domain_permutation quotientE)
      moreover have "\<forall>f \<in> F. bij_betw f A B"
        using univ_predicate_impl_forall[OF equiv_domain_permutation bij_betw_respects_domain_permutation]
        using \<open>F \<in> (A \<rightarrow>\<^sub>E B) // domain_permutation A B\<close> \<open>univ (\<lambda>f. bij_betw f A B) F\<close>
        by auto
      ultimately show "F \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}" by auto
    next
      show "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} \<subseteq> F"
      proof
        fix f'
        assume "f' \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}"
        from this have "f' \<in> A \<rightarrow>\<^sub>E B" "bij_betw f' A B" by auto
          obtain f where "f \<in> A \<rightarrow>\<^sub>E B" and "F = domain_permutation A B `` {f}"
          using \<open>F \<in> (A \<rightarrow>\<^sub>E B) // domain_permutation A B\<close> by (auto elim: quotientE)
        have "bij_betw f A B"
          using univ_commute'[OF equiv_domain_permutation bij_betw_respects_domain_permutation]
          using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>F = domain_permutation A B `` {f}\<close> \<open>univ (\<lambda>f. bij_betw f A B) F\<close>
          by auto
        obtain p where "p permutes A" "\<forall>x\<in>A. f x = f' (p x)"
          using obtain_domain_permutation_for_two_bijections
          using \<open>bij_betw f A B\<close> \<open>bij_betw f' A B\<close> by blast
        from this \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close>
        have "(f, f') \<in> domain_permutation A B"
          unfolding domain_permutation_def by auto
        from this show "f' \<in> F"
          using \<open>F = domain_permutation A B `` {f}\<close> by simp
      qed
    qed
    from this show "F \<in> {{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}}" by simp
  qed
qed

subsubsection \<open>Cardinality\<close>

lemma
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B) = 1"
using bij_betw_quotient_domain_permutation_eq[OF assms] by auto

subsection \<open>Bijections from A to B up to a Permutation on B\<close>

subsubsection \<open>Equivalence Class\<close>

lemma bijections_in_range_permutation:
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B"
proof -
  from assms obtain f where f: "f \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}"
    by (metis finite_same_card_bij_on_ext_funcset mem_Collect_eq)
  moreover have proj_f: "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} = range_permutation A B `` {f}"
  proof
    from f show "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} \<subseteq> range_permutation A B `` {f}"
      unfolding range_permutation_def
      by (auto elim: obtain_range_permutation_for_two_bijections)
  next
    show "range_permutation A B `` {f} \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}"
    proof
      fix f'
      assume "f' \<in> range_permutation A B `` {f}"
      have "(f', f) \<in> range_permutation A B"
        using \<open>f' \<in> range_permutation A B `` {f}\<close> equiv_range_permutation[of A B]
        by (simp add: equiv_class_eq_iff)
      from this obtain p where "p permutes B" "\<forall>x\<in>A. f' x = p (f x)"
        unfolding range_permutation_def by auto
      from this have "bij_betw (p \<circ> f) A B"
        using bij_betw_comp_iff f permutes_imp_bij by fastforce
      from this have "bij_betw f' A B"
        using \<open>\<forall>x\<in>A. f' x = p (f x)\<close>
        by (metis (mono_tags, lifting) bij_betw_cong comp_apply)
      moreover have "f' \<in> A \<rightarrow>\<^sub>E B"
        using \<open>f' \<in> range_permutation A B `` {f}\<close>
        unfolding range_permutation_def by auto
      ultimately show "f' \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}" by simp
    qed
  qed
  ultimately show ?thesis by (simp add: quotientI)
qed

lemma bij_betw_quotient_range_permutation_eq:
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B = {{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}}"
proof
  show "{{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}} \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B"
    by (simp add: bijections_in_range_permutation[OF assms])
next
  show "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B \<subseteq> {{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}}"
  proof
    fix F
    assume F_in: "F \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B"
    have "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B = {F \<in> ((A \<rightarrow>\<^sub>E B) // range_permutation A B). univ (\<lambda>f. bij_betw f A B) F}"
      using equiv_range_permutation[of A B] bij_betw_respects_range_permutation[of A B] by (simp only: univ_preserves_predicate)
    from this F_in have "F \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B"
      and "univ (\<lambda>f. bij_betw f A B) F" by blast+
    have "F = {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}"
    proof
      have "\<forall>f \<in> F. f \<in> A \<rightarrow>\<^sub>E B"
        using \<open>F \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B\<close>
        by (metis ImageE equiv_class_eq_iff equiv_range_permutation quotientE)
      moreover have "\<forall>f \<in> F. bij_betw f A B"
        using univ_predicate_impl_forall[OF equiv_range_permutation bij_betw_respects_range_permutation]
        using \<open>F \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B\<close> \<open>univ (\<lambda>f. bij_betw f A B) F\<close>
        by auto
      ultimately show "F \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}" by auto
    next
      show "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} \<subseteq> F"
      proof
        fix f'
        assume "f' \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}"
        from this have "f' \<in> A \<rightarrow>\<^sub>E B" "bij_betw f' A B" by auto
          obtain f where "f \<in> A \<rightarrow>\<^sub>E B" and "F = range_permutation A B `` {f}"
          using \<open>F \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B\<close> by (auto elim: quotientE)
        have "bij_betw f A B"
          using univ_commute'[OF equiv_range_permutation bij_betw_respects_range_permutation]
          using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>F = range_permutation A B `` {f}\<close> \<open>univ (\<lambda>f. bij_betw f A B) F\<close>
          by auto
        obtain p where "p permutes B" "\<forall>x\<in>A. f x = p (f' x)"
          using obtain_range_permutation_for_two_bijections
          using \<open>bij_betw f A B\<close> \<open>bij_betw f' A B\<close> by blast
        from this \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close>
        have "(f, f') \<in> range_permutation A B"
          unfolding range_permutation_def by auto
        from this show "f' \<in> F"
          using \<open>F = range_permutation A B `` {f}\<close> by simp
      qed
    qed
    from this show "F \<in> {{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}}" by simp
  qed
qed

subsubsection \<open>Cardinality\<close>

lemma card_bijections_range_permutation_eq_1:
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B) = 1"
using bij_betw_quotient_range_permutation_eq[OF assms] by auto

subsection \<open>Bijections from A to B up to a Permutation on A and B\<close>

subsubsection \<open>Equivalence Class\<close>

lemma bijections_in_domain_and_range_permutation:
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B"
proof -
  from assms obtain f where f: "f \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}"
    by (metis finite_same_card_bij_on_ext_funcset mem_Collect_eq)
  moreover have proj_f: "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} = domain_and_range_permutation A B `` {f}"
  proof
    have "id permutes A" by (simp add: permutes_id)
    from f this show "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} \<subseteq> domain_and_range_permutation A B `` {f}"
      unfolding domain_and_range_permutation_def
      by (fastforce elim: obtain_range_permutation_for_two_bijections)
  next
    show "domain_and_range_permutation A B `` {f} \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}"
    proof
      fix f'
      assume "f' \<in> domain_and_range_permutation A B `` {f}"
      have "(f', f) \<in> domain_and_range_permutation A B"
        using \<open>f' \<in> domain_and_range_permutation A B `` {f}\<close> equiv_domain_and_range_permutation[of A B]
        by (simp add: equiv_class_eq_iff)
      from this obtain p\<^sub>A p\<^sub>B where "p\<^sub>A permutes A" "p\<^sub>B permutes B"
        and "\<forall>x\<in>A. f' x = p\<^sub>B (f (p\<^sub>A x))"
        unfolding domain_and_range_permutation_def by auto
      from this have "bij_betw (p\<^sub>B \<circ> f \<circ> p\<^sub>A) A B"
        using bij_betw_comp_iff f permutes_imp_bij
        by (metis (no_types, lifting) mem_Collect_eq)
      from this have "bij_betw f' A B"
        using \<open>\<forall>x\<in>A. f' x = p\<^sub>B (f (p\<^sub>A x))\<close>
        by (auto intro: bij_betw_congI)
      moreover have "f' \<in> A \<rightarrow>\<^sub>E B"
        using \<open>f' \<in> domain_and_range_permutation A B `` {f}\<close>
        unfolding domain_and_range_permutation_def by auto
      ultimately show "f' \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}" by simp
    qed
  qed
  ultimately show ?thesis by (simp add: quotientI)
qed

lemma bij_betw_quotient_domain_and_range_permutation_eq:
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B = {{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}}"
proof
  show "{{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}}
    \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B"
    using bijections_in_domain_and_range_permutation[OF assms] by auto
next
  show "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B \<subseteq> {{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}}"
  proof
    fix F
    assume F_in: "F \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B"
    have "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B = {F \<in> ((A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B). univ (\<lambda>f. bij_betw f A B) F}"
      using equiv_domain_and_range_permutation[of A B] bij_betw_respects_domain_and_range_permutation[of A B] by (simp only: univ_preserves_predicate)
    from F_in this have "F \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B"
      and "univ (\<lambda>f. bij_betw f A B) F" by blast+
    have "F = {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}"
    proof
      have "\<forall>f \<in> F. f \<in> A \<rightarrow>\<^sub>E B"
        using \<open>F \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B\<close>
        by (metis ImageE equiv_class_eq_iff equiv_domain_and_range_permutation quotientE)
      moreover have "\<forall>f \<in> F. bij_betw f A B"
        using univ_predicate_impl_forall[OF equiv_domain_and_range_permutation bij_betw_respects_domain_and_range_permutation]
        using \<open>F \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B\<close> \<open>univ (\<lambda>f. bij_betw f A B) F\<close>
        by auto
      ultimately show "F \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}" by auto
    next
      show "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} \<subseteq> F"
      proof
        fix f'
        assume "f' \<in> {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}"
        from this have "f' \<in> A \<rightarrow>\<^sub>E B" "bij_betw f' A B" by auto
          obtain f where "f \<in> A \<rightarrow>\<^sub>E B" and "F = domain_and_range_permutation A B `` {f}"
          using \<open>F \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B\<close> by (auto elim: quotientE)
        have "bij_betw f A B"
          using univ_commute'[OF equiv_domain_and_range_permutation bij_betw_respects_domain_and_range_permutation]
          using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>F = domain_and_range_permutation A B `` {f}\<close> \<open>univ (\<lambda>f. bij_betw f A B) F\<close>
          by auto
        obtain p where "p permutes A" "\<forall>x\<in>A. f x = f' (p x)"
          using obtain_domain_permutation_for_two_bijections
          using \<open>bij_betw f A B\<close> \<open>bij_betw f' A B\<close> by blast
        moreover have "id permutes B" by (simp add: permutes_id)
        moreover note \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close>
        ultimately have "(f, f') \<in> domain_and_range_permutation A B"
          unfolding domain_and_range_permutation_def id_def by auto
        from this show "f' \<in> F"
          using \<open>F = domain_and_range_permutation A B `` {f}\<close> by simp
      qed
    qed
    from this show "F \<in> {{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}}" by simp
  qed
qed

subsubsection \<open>Cardinality\<close>

lemma card_bijections_domain_and_range_permutation_eq_1:
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B) = 1"
using bij_betw_quotient_domain_and_range_permutation_eq[OF assms] by auto

end
