(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Injections from A to B up to a permutation on A and B\<close>

theory Twelvefold_Way_Entry11
imports Twelvefold_Way_Entry10
begin

subsection \<open>Properties for Bijections\<close>

lemma all_one_implies_inj_on:
  assumes "finite A" "finite B"
  assumes "\<forall>n. n\<in># N \<longrightarrow> n = 1" "number_partition (card A) N" "size N \<le> card B"
  assumes "f \<in> functions_of A B N"
  shows   "inj_on f A"
proof -
  from \<open>f \<in> functions_of A B N\<close> have "f \<in> A \<rightarrow>\<^sub>E B"
    and "N = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))"
    unfolding functions_of_def by auto
  from this \<open>\<forall>n. n\<in># N \<longrightarrow> n = 1\<close> have parts: "\<forall>b \<in> B. card {x \<in> A. f x = b} = 1 \<or> {x \<in> A. f x = b} = {}"
    using \<open>finite B\<close> by auto
  show "inj_on f A"
  proof
    fix x y
    assume a: "x \<in> A" "y \<in> A" "f x = f y"
    from \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>x \<in> A\<close> have "f x \<in> B" by auto
    from a have 1: "x \<in> {x' \<in> A. f x' = f x}" "y \<in> {x' \<in> A. f x' = f x}" by auto
    from this have 2: "card {x' \<in> A. f x' = f x} = 1"
      using parts \<open>f x \<in> B\<close> by blast
    from this have "is_singleton {x' \<in> A. f x' = f x}"
      by (simp add: is_singleton_altdef)
    from 1 this show "x = y"
      by (metis is_singletonE singletonD)
  qed
qed

lemma inj_on_implies_all_one:
  assumes "finite A" "finite B"
  assumes "F \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B"
  assumes "univ (\<lambda>f. inj_on f A) F"
  shows "\<forall>n. n\<in># number_partition_of A B F \<longrightarrow> n = 1"
proof -
  from \<open>F \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B\<close> obtain f where "f \<in> A \<rightarrow>\<^sub>E B"
    and F_eq: "F = domain_and_range_permutation A B `` {f}" using quotientE by blast
  have "number_partition_of A B F = univ (\<lambda>f. image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))) F"
    unfolding number_partition_of_def ..
  also have "\<dots> =  univ (\<lambda>f. image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))) (domain_and_range_permutation A B `` {f})"
    unfolding F_eq ..
  also have "\<dots> = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))"
    using \<open>finite B\<close> equiv_domain_and_range_permutation multiset_of_partition_cards_respects_domain_and_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
    by (subst univ_commute') auto
  finally have eq: "number_partition_of A B F = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))" .
  from iffD1[OF univ_commute', OF equiv_domain_and_range_permutation, OF inj_on_respects_domain_and_range_permutation, OF \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>]
    assms(4) have "inj_on f A" by (simp add: F_eq)
  have "\<forall>n. n \<in># image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})) \<longrightarrow> n = 1"
  proof -
    have "\<forall>b \<in> B. card {x \<in> A. f x = b} = 1 \<or> {x \<in> A. f x = b} = {}"
    proof
      fix b
      assume "b \<in> B"
      show "card {x \<in> A. f x = b} = 1 \<or> {x \<in> A. f x = b} = {}"
      proof (cases "b \<in> f ` A")
        assume "b \<in> f ` A"
        from \<open>inj_on f A\<close> this have "is_singleton {x \<in> A. f x = b}"
          by (auto simp add: inj_on_eq_iff intro: is_singletonI')
        from this have "card {x \<in> A. f x = b} = 1"
          by (subst is_singleton_altdef[symmetric])
        from this show ?thesis ..
      next
        assume "b \<notin> f ` A"
        from this have "{x \<in> A. f x = b} = {}" by auto
        from this show ?thesis ..
      qed
    qed
    from this show ?thesis
      using \<open>finite B\<close> by auto
  qed
  from this show "\<forall>n. n\<in># number_partition_of A B F \<longrightarrow> n = 1"
    unfolding eq by auto
qed

lemma functions_of_is_inj_on:
  assumes "finite A" "finite B"
  assumes "\<forall>n. n\<in># N \<longrightarrow> n = 1" "number_partition (card A) N" "size N \<le> card B"
  shows "univ (\<lambda>f. inj_on f A) (functions_of A B N)"
proof -
  have "functions_of A B N \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B"
    using assms functions_of by auto
  from this obtain f where eq_f: "functions_of A B N = domain_and_range_permutation A B `` {f}" and "f \<in> A \<rightarrow>\<^sub>E B"
    using quotientE by blast
  from eq_f have "f \<in> functions_of A B N"
    using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> equiv_domain_and_range_permutation equiv_class_self by fastforce
  have "inj_on f A"
    using \<open>f \<in> functions_of A B N\<close> assms all_one_implies_inj_on by blast
  from this show ?thesis
    unfolding eq_f using equiv_domain_and_range_permutation inj_on_respects_domain_and_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
    by (subst univ_commute') assumption+
qed

subsection \<open>Bijections\<close>

lemma bij_betw_number_partition_of:
  assumes "finite A" "finite B"
  shows "bij_betw (number_partition_of A B) ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B) {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition (card A) N \<and> size N \<le> card B}"
proof (rule bij_betw_byWitness[where f'="functions_of A B"])
  have quotient_eq: "{f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B = {F \<in> ((A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B). univ (\<lambda>f. inj_on f A) F}"
    using equiv_domain_and_range_permutation[of A B] inj_on_respects_domain_and_range_permutation[of A B] by (simp only: univ_preserves_predicate)
  show "\<forall>F\<in>{f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B.
       functions_of A B (number_partition_of A B F) = F"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp only: quotient_eq functions_of_number_partition_of)
  show "\<forall>N\<in> {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition (card A) N \<and> size N \<le> card B}. number_partition_of A B (functions_of A B N) = N"
    using \<open>finite A\<close> \<open>finite B\<close> number_partition_of_functions_of by auto
  show "number_partition_of A B ` ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B)
    \<subseteq> {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition (card A) N \<and> size N \<le> card B}"
    using \<open>finite A\<close> \<open>finite B\<close>
    by (auto simp add: quotient_eq number_partition_of inj_on_implies_all_one simp del: One_nat_def)
  show "functions_of A B ` {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition (card A) N \<and> size N \<le> card B}
    \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp add: quotient_eq intro: functions_of functions_of_is_inj_on)
qed

lemma bij_betw_functions_of:
  assumes "finite A" "finite B"
  shows "bij_betw (functions_of A B) {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition (card A) N \<and> size N \<le> card B} ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B)"
proof (rule bij_betw_byWitness[where f'="number_partition_of A B"])
  have quotient_eq: "{f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B = {F \<in> ((A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B). univ (\<lambda>f. inj_on f A) F}"
    using equiv_domain_and_range_permutation[of A B] inj_on_respects_domain_and_range_permutation[of A B] by (simp only: univ_preserves_predicate)
  show "\<forall>F\<in>{f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B.
       functions_of A B (number_partition_of A B F) = F"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp only: quotient_eq functions_of_number_partition_of)
  show "\<forall>N\<in> {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition (card A) N \<and> size N \<le> card B}. number_partition_of A B (functions_of A B N) = N"
    using \<open>finite A\<close> \<open>finite B\<close> number_partition_of_functions_of by auto
  show "number_partition_of A B ` ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B)
    \<subseteq> {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition (card A) N \<and> size N \<le> card B}"
    using \<open>finite A\<close> \<open>finite B\<close>
    by (auto simp add: quotient_eq number_partition_of inj_on_implies_all_one simp del: One_nat_def)
  show "functions_of A B ` {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition (card A) N \<and> size N \<le> card B}
    \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp add: quotient_eq intro: functions_of functions_of_is_inj_on)
qed

subsection \<open>Cardinality\<close>

lemma card_injective_functions_domain_and_range_permutation:
  assumes "finite A" "finite B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B) = iverson (card A \<le> card B)"
proof -
  have "bij_betw (number_partition_of A B) ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B) {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition (card A) N \<and> size N \<le> card B}"
     using \<open>finite A\<close> \<open>finite B\<close> by (rule bij_betw_number_partition_of)
  from this have "card ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B) = card {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition (card A) N \<and> size N \<le> card B}"
    by (rule bij_betw_same_card)
  also have "card {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition (card A) N \<and> size N \<le> card B} = iverson (card A \<le> card B)"
    by (rule card_number_partitions_with_only_parts_1)
  finally show ?thesis .
qed

end
