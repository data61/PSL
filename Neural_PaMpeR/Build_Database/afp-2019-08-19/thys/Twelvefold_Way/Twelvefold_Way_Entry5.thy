(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Injections from A to B up to a Permutation of A\<close>

theory Twelvefold_Way_Entry5
imports
  Equiv_Relations_on_Functions
begin

subsection \<open>Definition of Bijections\<close>

definition subset_of :: "'a set \<Rightarrow> ('a  \<Rightarrow> 'b) set \<Rightarrow> 'b set"
where
  "subset_of A F = univ (\<lambda>f. f ` A) F"

definition functions_of :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"
where
  "functions_of A B = {f \<in> A \<rightarrow>\<^sub>E B. f ` A = B}"

subsection \<open>Properties for Bijections\<close>

lemma functions_of_eq:
  assumes "finite A"
  assumes "f \<in> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}"
  shows "functions_of A (f ` A) = domain_permutation A B `` {f}"
proof
  have bij: "bij_betw f A (f ` A)"
    using assms by (simp add: bij_betw_imageI)
  show "functions_of A (f ` A) \<subseteq> domain_permutation A B `` {f}"
  proof
    fix f'
    assume "f' \<in> functions_of A (f ` A)"
    from this have "f' \<in> A \<rightarrow>\<^sub>E f ` A" and "f' ` A = f ` A"
      unfolding functions_of_def by auto
    from this assms have "f' \<in> A \<rightarrow>\<^sub>E B" and "inj_on f A"
      using PiE_mem by fastforce+
    moreover have "\<exists>p. p permutes A \<and> (\<forall>x\<in>A. f x = f' (p x))"
    proof
      let ?p = "\<lambda>x. if x \<in> A then inv_into A f' (f x) else x"
      show "?p permutes A \<and> (\<forall>x\<in>A. f x = f' (?p x))"
      proof
        show "?p permutes A"
        proof (rule bij_imp_permutes)
          show "bij_betw ?p A A"
          proof (rule bij_betw_imageI)
            show "inj_on ?p A"
            proof (rule inj_onI)
              fix a a'
              assume "a \<in> A" "a' \<in> A" "?p a = ?p a'"
              from this have "inv_into A f' (f a) = inv_into A f' (f a')" by auto
              from this \<open>a \<in> A\<close> \<open>a' \<in> A\<close> \<open>f' ` A = f ` A\<close> have "f a = f a'"
                using inv_into_injective by fastforce
              from this \<open>a \<in> A\<close> \<open>a' \<in> A\<close> show "a = a'"
                by (metis bij bij_betw_inv_into_left)
            qed
          next
            show "?p ` A = A"
            proof
              show "?p ` A \<subseteq> A"
                using \<open>f' ` A = f ` A\<close> by (simp add: image_subsetI inv_into_into)
            next
              show "A \<subseteq> ?p ` A"
              proof
                fix a
                assume "a \<in> A"
                have "inj_on f' A"
                  using \<open>finite A\<close> \<open>f' ` A = f ` A\<close> \<open>inj_on f A\<close>
                  by (simp add: card_image eq_card_imp_inj_on)
                from \<open>a \<in> A\<close> \<open>f' ` A = f ` A\<close> have "inv_into A f (f' a) \<in> A"
                  by (metis image_eqI inv_into_into)
                moreover have "a = inv_into A f' (f (inv_into A f (f' a)))"
                  using \<open>a \<in> A\<close> \<open>f' ` A = f ` A\<close> \<open>inj_on f' A\<close>
                  by (metis f_inv_into_f image_eqI inv_into_f_f)
                ultimately show "a \<in> ?p ` A" by auto
              qed
            qed
          qed
        next
          fix x
          assume "x \<notin> A"
          from this show "?p x = x" by simp
        qed
      next
        from \<open>f' ` A = f ` A\<close> show "\<forall>x\<in>A. f x = f' (?p x)"
          by (simp add: f_inv_into_f)
      qed
    qed
    moreover have "f \<in> A \<rightarrow>\<^sub>E B" using assms by auto
    ultimately show "f' \<in> domain_permutation A B `` {f}"
      unfolding domain_permutation_def by auto
  qed
next
  show "domain_permutation A B `` {f} \<subseteq> functions_of A (f ` A)"
  proof
    fix f'
    assume "f' \<in> domain_permutation A B `` {f}"
    from this obtain p where p: "p permutes A" "\<forall>x\<in>A. f x = f' (p x)"
      and "f \<in> A \<rightarrow>\<^sub>E B" "f' \<in> A \<rightarrow>\<^sub>E B"
      unfolding domain_permutation_def by auto
    have "f' ` A = f ` A"
    proof
      show "f' ` A \<subseteq> f ` A"
      proof
        fix x
        assume "x \<in> f' ` A"
        from this obtain x' where "x = f' x'" and "x' \<in> A" ..
        from this have "x = f (inv p x')"
          using p by (metis (mono_tags, lifting) permutes_in_image permutes_inverses(1))
        moreover have "inv p x' \<in> A"
          using p \<open>x' \<in> A\<close> by (simp add: permutes_in_image permutes_inv)
        ultimately show "x \<in> f ` A" ..
      qed
    next
      show "f ` A \<subseteq> f' ` A"
        using p permutes_in_image by fastforce
    qed
    moreover from this \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> have "f' \<in> A \<rightarrow>\<^sub>E f ` A" by auto
    ultimately show "f' \<in> functions_of A (f ` A)"
      unfolding functions_of_def by auto
  qed
qed

lemma subset_of:
  assumes "F \<in> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B"
  shows "subset_of A F \<subseteq> B" and "card (subset_of A F) = card A"
proof -
  from assms obtain f where F_eq: "F = (domain_permutation A B) `` {f}"
    and f: "f \<in> A \<rightarrow>\<^sub>E B" "inj_on f A"
    using mem_Collect_eq quotientE by force
  from this have "subset_of A (domain_permutation A B `` {f}) = f ` A"
    using equiv_domain_permutation image_respects_domain_permutation
    unfolding subset_of_def by (intro univ_commute') auto
  from this f F_eq show "subset_of A F \<subseteq> B" and "card (subset_of A F) = card A"
    by (auto simp add: card_image)
qed

lemma functions_of:
  assumes "finite A" "finite B" "X \<subseteq> B" "card X = card A"
  shows "functions_of A X \<in> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B"
proof -
  from assms obtain f where f: "f \<in> A \<rightarrow>\<^sub>E X \<and> bij_betw f A X"
    using \<open>finite A\<close> \<open>finite B\<close> by (metis finite_same_card_bij_on_ext_funcset finite_subset)
  from this have "X = f ` A" by (simp add: bij_betw_def)
  from f \<open>X \<subseteq> B\<close> have "f \<in> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}"
    by (auto simp add: bij_betw_imp_inj_on)
  have "functions_of A X = domain_permutation A B `` {f}"
    using \<open>finite A\<close> \<open>X = f ` A\<close> \<open>f \<in> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}\<close>
    by (simp add: functions_of_eq)
  from this show "functions_of A X \<in> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B"
    using \<open>f \<in> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}\<close> by (auto intro: quotientI)
qed

lemma subset_of_functions_of:
  assumes "finite A" "finite X" "card A = card X"
  shows "subset_of A (functions_of A X) = X"
proof -
  from assms obtain f where "f \<in> A \<rightarrow>\<^sub>E X" and "bij_betw f A X"
    using finite_same_card_bij_on_ext_funcset by blast
  from this have subset_of: "subset_of A (domain_permutation A X `` {f}) = f ` A"
    using equiv_domain_permutation image_respects_domain_permutation
    unfolding subset_of_def by (intro univ_commute') auto
  from \<open>bij_betw f A X\<close> have "inj_on f A" and "f ` A = X"
    by (auto simp add: bij_betw_def)
  have "subset_of A (functions_of A X) = subset_of A (functions_of A (f ` A))"
    using \<open>f ` A = X\<close> by simp
  also have "\<dots> = subset_of A (domain_permutation A X `` {f})"
    using \<open>finite A\<close> \<open>inj_on f A\<close> \<open>f \<in> A \<rightarrow>\<^sub>E X\<close> by (auto simp add: functions_of_eq)
  also have "\<dots> = f ` A"
    using \<open>inj_on f A\<close> \<open>f \<in> A \<rightarrow>\<^sub>E X\<close> by (simp add: subset_of)
  also have "\<dots> = X"
    using \<open>f ` A = X\<close> by simp
  finally show ?thesis .
qed

lemma functions_of_subset_of:
  assumes "finite A"
  assumes "F \<in> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B"
  shows "functions_of A (subset_of A F) = F"
using assms(2) proof (rule quotientE)
  fix f
  assume f: "f \<in> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}"
    and F_eq: "F = domain_permutation A B `` {f}"
  from this have "subset_of A (domain_permutation A B `` {f}) = f ` A"
    using equiv_domain_permutation image_respects_domain_permutation
    unfolding subset_of_def by (intro univ_commute') auto
  from this f F_eq \<open>finite A\<close> show "functions_of A (subset_of A F) = F"
    by (simp add: functions_of_eq)
qed

subsection \<open>Bijections\<close>

lemma bij_betw_subset_of:
  assumes "finite A" "finite B"
  shows "bij_betw (subset_of A) ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B) {X. X \<subseteq> B \<and> card X = card A}"
proof (rule bij_betw_byWitness[where f'="functions_of A"])
  show "\<forall>F\<in>{f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B. functions_of A (subset_of A F) = F"
    using \<open>finite A\<close> functions_of_subset_of by auto
  show "\<forall>X\<in>{X. X \<subseteq> B \<and> card X = card A}. subset_of A (functions_of A X) = X"
    using subset_of_functions_of \<open>finite A\<close> \<open>finite B\<close>
    by (metis (mono_tags) finite_subset mem_Collect_eq)
  show "subset_of A ` ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B) \<subseteq> {X. X \<subseteq> B \<and> card X = card A}"
    using subset_of by fastforce
  show "functions_of A ` {X. X \<subseteq> B \<and> card X = card A} \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B"
    using \<open>finite A\<close> \<open>finite B\<close> functions_of by auto
qed

lemma bij_betw_functions_of:
  assumes "finite A" "finite B"
  shows "bij_betw (functions_of A) {X. X \<subseteq> B \<and> card X = card A} ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B)"
proof (rule bij_betw_byWitness[where f'="subset_of A"])
  show "\<forall>F\<in>{f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B. functions_of A (subset_of A F) = F"
    using \<open>finite A\<close> functions_of_subset_of by auto
  show "\<forall>X\<in>{X. X \<subseteq> B \<and> card X = card A}. subset_of A (functions_of A X) = X"
    using subset_of_functions_of \<open>finite A\<close> \<open>finite B\<close>
    by (metis (mono_tags) finite_subset mem_Collect_eq)
  show "subset_of A ` ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B) \<subseteq> {X. X \<subseteq> B \<and> card X = card A}"
    using subset_of by fastforce
  show "functions_of A ` {X. X \<subseteq> B \<and> card X = card A} \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B"
    using \<open>finite A\<close> \<open>finite B\<close> functions_of by auto
qed

lemma bij_betw_mset_set:
  shows "bij_betw mset_set {A. finite A} {M. \<forall>x. count M x \<le> 1}"
proof (rule bij_betw_byWitness[where f'="set_mset"])
  show "\<forall>A\<in>{A. finite A}. set_mset (mset_set A) = A" by auto
  show "\<forall>M\<in>{M. \<forall>x. count M x \<le> 1}. mset_set (set_mset M) = M"
    by (auto simp add: mset_set_set_mset')
  show "mset_set ` {A. finite A} \<subseteq> {M. \<forall>x. count M x \<le> 1}"
    using nat_le_linear by fastforce
  show "set_mset ` {M. \<forall>x. count M x \<le> 1} \<subseteq> {A. finite A}" by auto
qed

lemma bij_betw_mset_set_card:
  assumes "finite A"
  shows "bij_betw mset_set {X. X \<subseteq> A \<and> card X = k} {M. M \<subseteq># mset_set A \<and> size M = k}"
proof (rule bij_betw_byWitness[where f'="set_mset"])
  show "\<forall>X\<in>{X. X \<subseteq> A \<and> card X = k}. set_mset (mset_set X) = X"
    using \<open>finite A\<close> rev_finite_subset[of A] by auto
  show "\<forall>M\<in>{M. M \<subseteq># mset_set A \<and> size M = k}. mset_set (set_mset M) = M"
    by (auto simp add: mset_set_set_mset)
  show "mset_set ` {X. X \<subseteq> A \<and> card X = k} \<subseteq> {M. M \<subseteq># mset_set A \<and> size M = k}"
    using \<open>finite A\<close> rev_finite_subset[of A]
    by (auto simp add: mset_set_subseteq_mset_set)
  show "set_mset ` {M. M \<subseteq># mset_set A \<and> size M = k} \<subseteq> {X. X \<subseteq> A \<and> card X = k}"
    using assms mset_subset_eqD card_set_mset by fastforce
qed

lemma bij_betw_mset_set_card':
  assumes "finite A"
  shows "bij_betw mset_set {X. X \<subseteq> A \<and> card X = k} {M. set_mset M \<subseteq> A \<and> size M = k \<and> (\<forall>x. count M x \<le> 1)}"
proof (rule bij_betw_byWitness[where f'="set_mset"])
  show "\<forall>X\<in>{X. X \<subseteq> A \<and> card X = k}. set_mset (mset_set X) = X"
    using \<open>finite A\<close> rev_finite_subset[of A] by auto
  show "\<forall>M\<in>{M. set_mset M \<subseteq> A \<and> size M = k \<and> (\<forall>x. count M x \<le> 1)}. mset_set (set_mset M) = M"
    by (auto simp add: mset_set_set_mset')
  show "mset_set ` {X. X \<subseteq> A \<and> card X = k} \<subseteq> {M. set_mset M \<subseteq> A \<and> size M = k \<and> (\<forall>x. count M x \<le> 1)}"
    using \<open>finite A\<close> rev_finite_subset[of A] by (auto simp add: count_mset_set_leq')
  show "set_mset ` {M. set_mset M \<subseteq> A \<and> size M = k \<and> (\<forall>x. count M x \<le> 1)} \<subseteq> {X. X \<subseteq> A \<and> card X = k}"
    by (auto simp add: card_set_mset')
qed

subsection \<open>Cardinality\<close>

lemma card_injective_functions_domain_permutation:
  assumes "finite A" "finite B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B) = card B choose card A"
proof -
  have "bij_betw (subset_of A) ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B) {X. X \<subseteq> B \<and> card X = card A}"
    using \<open>finite A\<close> \<open>finite B\<close> by (rule bij_betw_subset_of)
  from this have "card ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B) = card {X. X \<subseteq> B \<and> card X = card A}"
    by (rule bij_betw_same_card)
  also have "card {X. X \<subseteq> B \<and> card X = card A} = card B choose card A"
    using \<open>finite B\<close> by (rule n_subsets)
  finally show ?thesis .
qed

lemma card_multiset_only_sets:
  assumes "finite A"
  shows "card {M. M \<subseteq># mset_set A \<and> size M = k} = card A choose k"
proof -
  have "bij_betw mset_set {X. X \<subseteq> A \<and> card X = k} {M. M \<subseteq># mset_set A \<and> size M = k}"
    using \<open>finite A\<close> by (rule bij_betw_mset_set_card)
  from this have "card {M. M \<subseteq># mset_set A \<and> size M = k} = card {X. X \<subseteq> A \<and> card X = k}"
    by (simp add: bij_betw_same_card)
  also have " card {X. X \<subseteq> A \<and> card X = k} = card A choose k"
    using \<open>finite A\<close> by (rule n_subsets)
  finally show ?thesis .
qed

lemma card_multiset_only_sets':
  assumes "finite A"
  shows "card {M. set_mset M \<subseteq> A \<and> size M = k \<and> (\<forall>x. count M x \<le> 1)} = card A choose k"
proof -
  from \<open>finite A\<close> have "{M. set_mset M \<subseteq> A \<and> size M = k \<and> (\<forall>x. count M x \<le> 1)} =
    {M. M \<subseteq># mset_set A \<and> size M = k}"
    using msubset_mset_set_iff by auto
  from this \<open>finite A\<close> card_multiset_only_sets show ?thesis by simp
qed

end
