(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Injections from A to B up to a Permutation on B\<close>

theory Twelvefold_Way_Entry8
imports Twelvefold_Way_Entry7
begin

subsection \<open>Properties for Bijections\<close>

lemma inj_on_implies_partitions_of:
  assumes "F \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B"
  assumes "univ (\<lambda>f. inj_on f A) F"
  shows "\<forall>X \<in> partitions_of A B F. card X = 1"
proof -
  from \<open>F \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B\<close> obtain f where "f \<in> A \<rightarrow>\<^sub>E B"
    and F_eq: "F = range_permutation A B `` {f}" using quotientE by blast
  from this \<open>univ (\<lambda>f. inj_on f A) F\<close> have "inj_on f A"
    using univ_commute'[OF equiv_range_permutation inj_on_respects_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>] by simp
  have "\<forall>X\<in>(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}. card X = 1"
  proof
    fix X
    assume "X \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
    from this obtain x where "X = {xa \<in> A. f xa = f x}" "x \<in> A" by auto
    from this have "X = {x}"
      using \<open>inj_on f A\<close> by (auto dest!: inj_onD)
    from this show "card X = 1" by simp
  qed
  from this show ?thesis
    unfolding partitions_of_def F_eq
    using equiv_range_permutation domain_partitions_respects_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
    by (subst univ_commute') assumption+
qed

lemma unique_part_eq_singleton:
  assumes "partition_on A P"
  assumes "\<forall>X\<in>P. card X = 1"
  assumes "x \<in> A"
  shows "(THE X. x \<in> X \<and> X \<in> P) = {x}"
proof -
  have "(THE X. x \<in> X \<and> X \<in> P) \<in> P"
    using \<open>partition_on A P\<close> \<open>x \<in> A\<close> by (simp add: partition_on_the_part_mem)
  from this have "card (THE X. x \<in> X \<and> X \<in> P) = 1"
    using \<open>\<forall>X\<in>P. card X = 1\<close> by auto
  moreover have "x \<in> (THE X. x \<in> X \<and> X \<in> P)"
    using \<open>partition_on A P\<close> \<open>x \<in> A\<close> by (simp add: partition_on_in_the_unique_part)
  ultimately show ?thesis
    by (metis card_1_singletonE singleton_iff)
qed

lemma functions_of_is_inj_on:
  assumes "finite A" "finite B" "partition_on A P" "card P \<le> card B"
  assumes "\<forall>X\<in>P. card X = 1"
  shows "univ (\<lambda>f. inj_on f A) (functions_of P A B)"
proof -
  have "functions_of P A B \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B"
    using functions_of \<open>finite A\<close> \<open>finite B\<close> \<open>partition_on A P\<close> \<open>card P \<le> card B\<close> by blast
  from this obtain f where eq_f: "functions_of P A B = range_permutation A B `` {f}" and "f \<in> A \<rightarrow>\<^sub>E B"
    using quotientE by blast
  from eq_f have "f \<in> functions_of P A B"
    using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> equiv_range_permutation equiv_class_self by fastforce
  from this have eq: "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = P"
    unfolding functions_of_def by auto
  have "inj_on f A"
  proof (rule inj_onI)
    fix x y
    assume "x \<in> A" "y \<in> A" "f x = f y"
    from \<open>x \<in> A\<close> have "x \<in> {x' \<in> A. f x' = f x}" by auto
    moreover from \<open>y \<in> A\<close> \<open>f x = f y\<close> have "y \<in> {x' \<in> A. f x' = f x}" by auto
    moreover have "card {x' \<in> A. f x' = f x} = 1"
    proof -
      from \<open>x \<in> A\<close> \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> have "f x \<in> B" by auto
      from this \<open>x \<in> A\<close> have "{x' \<in> A. f x' = f x} \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}" by auto
      from this \<open>\<forall>X\<in>P. card X = 1\<close> eq show ?thesis by auto
    qed
    ultimately show "x = y" by (metis card_1_singletonE singletonD)
  qed
  from this show ?thesis
    unfolding eq_f using equiv_range_permutation inj_on_respects_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
    by (subst univ_commute') assumption+
qed

subsection \<open>Bijections\<close>

lemma bij_betw_partitions_of:
  assumes "finite A" "finite B"
  shows "bij_betw (partitions_of A B) ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // range_permutation A B) {P. partition_on A P \<and> card P \<le> card B \<and> (\<forall>X\<in>P. card X = 1)}"
proof (rule bij_betw_byWitness[where f'="\<lambda>P. functions_of P A B"])
  have quotient_eq: "{f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // range_permutation A B = {F \<in> ((A \<rightarrow>\<^sub>E B) // range_permutation A B). univ (\<lambda>f. inj_on f A) F}"
    by (simp add: equiv_range_permutation inj_on_respects_range_permutation univ_preserves_predicate)
  show "\<forall>F\<in>{f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // range_permutation A B. functions_of (partitions_of A B F) A B = F"
    using \<open>finite B\<close> by (simp add: quotient_eq functions_of_partitions_of)
  show "\<forall>P\<in>{P. partition_on A P \<and> card P \<le> card B \<and> (\<forall>X\<in>P. card X = 1)}. partitions_of A B (functions_of P A B) = P"
    using \<open>finite A\<close> \<open>finite B\<close> by (simp add: partitions_of_functions_of)
  show "partitions_of A B ` ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // range_permutation A B) \<subseteq> {P. partition_on A P \<and> card P \<le> card B \<and> (\<forall>X\<in>P. card X = 1)}"
    using \<open>finite B\<close> quotient_eq partitions_of inj_on_implies_partitions_of by fastforce
  show "(\<lambda>P. functions_of P A B) ` {P. partition_on A P \<and> card P \<le> card B \<and> (\<forall>X\<in>P. card X = 1)} \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // range_permutation A B"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp add: quotient_eq intro: functions_of functions_of_is_inj_on)
qed

subsection \<open>Cardinality\<close>

lemma card_injective_functions_range_permutation:
  assumes "finite A" "finite B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // range_permutation A B) = iverson (card A \<le> card B)"
proof -
  obtain enum where "bij_betw enum {0..<card A} A"
    using \<open>finite A\<close> ex_bij_betw_nat_finite by blast
  have "bij_betw (partitions_of A B) ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // range_permutation A B) {P. partition_on A P \<and> card P \<le> card B \<and> (\<forall>X\<in>P. card X = 1)}"
    using \<open>finite A\<close> \<open>finite B\<close> by (rule bij_betw_partitions_of)
  from this have "card ({f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // range_permutation A B) = card {P. partition_on A P \<and> card P \<le> card B \<and> (\<forall>X\<in>P. card X = 1)}"
    by (rule bij_betw_same_card)
  also have "card {P. partition_on A P \<and> card P \<le> card B \<and> (\<forall>X\<in>P. card X = 1)} = iverson (card A \<le> card B)"
    using \<open>finite A\<close> by (rule card_partition_on_size1_eq_iverson)
  finally show ?thesis .
qed

end
