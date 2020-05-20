(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Surjections from A to B up to a Permutation on A and B\<close>

theory Twelvefold_Way_Entry12
imports Twelvefold_Way_Entry9 Twelvefold_Way_Entry10
begin

subsection \<open>Properties for Bijections\<close>

lemma size_eq_card_implies_surj_on:
  assumes "finite A" "finite B"
  assumes "size N = card B"
  assumes "f \<in> functions_of A B N"
  shows   "f ` A = B"
proof -
  from \<open>f \<in> functions_of A B N\<close> have "f \<in> A \<rightarrow>\<^sub>E B" and
    "N = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))"
    unfolding functions_of_def by auto
  from this \<open>size N = card B\<close> have "card ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) = card B" by simp
  from this \<open>finite B\<close> \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> show "f ` A = B"
    using card_eq_implies_surjective_on by blast
qed

lemma surj_on_implies_size_eq_card:
  assumes "finite A" "finite B"
  assumes "F \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B"
  assumes "univ (\<lambda>f. f ` A = B) F"
  shows "size (number_partition_of A B F) = card B"
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
  from iffD1[OF univ_commute', OF equiv_domain_and_range_permutation, OF surjective_respects_domain_and_range_permutation, OF \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>]
    assms(4) have "f ` A = B" by (simp add: F_eq)
  have "size (number_partition_of A B F) = size (image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})))"
    unfolding eq ..
  also have "\<dots> = card ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})" by simp
  also from \<open>f ` A = B\<close> have "\<dots> = card B"
    using surjective_on_implies_card_eq by auto
  finally show ?thesis .
qed

lemma functions_of_is_surj_on:
  assumes "finite A" "finite B"
  assumes "number_partition (card A) N" "size N = card B"
  shows "univ (\<lambda>f. f ` A = B) (functions_of A B N)"
proof -
  have "functions_of A B N \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B"
    using functions_of \<open>finite A\<close> \<open>finite B\<close> \<open>number_partition (card A) N \<close> \<open>size N = card B\<close>
    by fastforce
  from this obtain f where eq_f: "functions_of A B N = domain_and_range_permutation A B `` {f}" and "f \<in> A \<rightarrow>\<^sub>E B"
    using quotientE by blast
  from eq_f have "f \<in> functions_of A B N"
    using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> equiv_domain_and_range_permutation equiv_class_self by fastforce
  have "f ` A = B"
    using \<open>f \<in> functions_of A B N\<close> assms size_eq_card_implies_surj_on by blast
  from this show ?thesis
    unfolding eq_f using equiv_domain_and_range_permutation surjective_respects_domain_and_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
    by (subst univ_commute') assumption+
qed

subsection \<open>Bijections\<close>

lemma bij_betw_number_partition_of:
   assumes "finite A" "finite B"
  shows "bij_betw (number_partition_of A B) ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B) {N. number_partition (card A) N \<and> size N = card B}"
proof (rule bij_betw_byWitness[where f'="functions_of A B"])
  have quotient_eq: "{f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B = {F \<in> ((A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B). univ (\<lambda>f. f ` A = B) F}"
    using equiv_domain_and_range_permutation[of A B] surjective_respects_domain_and_range_permutation[of A B] by (simp only: univ_preserves_predicate)
  show "\<forall>F\<in>{f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B.
       functions_of A B (number_partition_of A B F) = F"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp only: quotient_eq functions_of_number_partition_of)
  show "\<forall>N\<in>{N. number_partition (card A) N  \<and> size N = card B}. number_partition_of A B (functions_of A B N) = N"
    using \<open>finite A\<close> \<open>finite B\<close> by (simp add: number_partition_of_functions_of)
  show "number_partition_of A B ` ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B)
    \<subseteq> {N. number_partition (card A) N  \<and> size N = card B}"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp add: quotient_eq number_partition_of surj_on_implies_size_eq_card)
  show "functions_of A B ` {N. number_partition (card A) N \<and> size N = card B}
    \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp add: quotient_eq intro: functions_of functions_of_is_surj_on)
qed

lemma bij_betw_functions_of:
   assumes "finite A" "finite B"
  shows "bij_betw (functions_of A B) {N. number_partition (card A) N \<and> size N = card B} ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B)"
proof (rule bij_betw_byWitness[where f'="number_partition_of A B"])
  have quotient_eq: "{f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B = {F \<in> ((A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B). univ (\<lambda>f. f ` A = B) F}"
    using equiv_domain_and_range_permutation[of A B] surjective_respects_domain_and_range_permutation[of A B] by (simp only: univ_preserves_predicate)
  show "\<forall>F\<in>{f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B.
       functions_of A B (number_partition_of A B F) = F"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp only: quotient_eq functions_of_number_partition_of)
  show "\<forall>N\<in>{N. number_partition (card A) N  \<and> size N = card B}. number_partition_of A B (functions_of A B N) = N"
    using \<open>finite A\<close> \<open>finite B\<close> by (simp add: number_partition_of_functions_of)
  show "number_partition_of A B ` ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B)
    \<subseteq> {N. number_partition (card A) N  \<and> size N = card B}"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp add: quotient_eq number_partition_of surj_on_implies_size_eq_card)
  show "functions_of A B ` {N. number_partition (card A) N \<and> size N = card B}
    \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp add: quotient_eq intro: functions_of functions_of_is_surj_on)
qed

subsection \<open>Cardinality\<close>

lemma card_surjective_functions_domain_and_range_permutation:
  assumes "finite A" "finite B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B) = Partition (card A) (card B)"
proof -
  have "bij_betw (number_partition_of A B) ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B) {N. number_partition (card A) N \<and> size N = card B}"
     using \<open>finite A\<close> \<open>finite B\<close> by (rule bij_betw_number_partition_of)
  from this have "card ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B) = card {N. number_partition (card A) N \<and> size N = card B}"
    by (rule bij_betw_same_card)
  also have "card {N. number_partition (card A) N \<and> size N = card B} = Partition (card A) (card B)"
    by (rule card_partitions_with_k_parts)
  finally show ?thesis .
qed

end
