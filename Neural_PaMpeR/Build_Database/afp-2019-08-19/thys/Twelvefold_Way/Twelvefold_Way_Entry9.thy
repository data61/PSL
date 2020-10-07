(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Surjections from A to B up to a Permutation on B\<close>

theory Twelvefold_Way_Entry9
imports Twelvefold_Way_Entry7
begin

subsection \<open>Properties for Bijections\<close>

lemma surjective_on_implies_card_eq:
  assumes "f ` A = B"
  shows "card ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) = card B"
proof -
  from \<open>f ` A = B\<close> have "{} \<notin> (\<lambda>b. {x \<in> A. f x = b}) ` B" by auto
  from \<open>f ` A = B\<close> have "inj_on (\<lambda>b. {x \<in> A. f x = b}) B" by (fastforce intro: inj_onI)
  have "card ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) = card ((\<lambda>b. {x \<in> A. f x = b}) ` B)"
    using \<open>{} \<notin> (\<lambda>b. {x \<in> A. f x = b}) ` B\<close> by simp
  also have "\<dots> = card B"
    using \<open>inj_on (\<lambda>b. {x \<in> A. f x = b}) B\<close> by (rule card_image)
  finally show ?thesis .
qed

lemma card_eq_implies_surjective_on:
  assumes "finite B" "f \<in> A \<rightarrow>\<^sub>E B"
  assumes card_eq: "card ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) = card B"
  shows "f ` A = B"
proof
  from \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> show "f ` A \<subseteq> B" by auto
next
  show "B \<subseteq> f ` A"
  proof
    fix x
    assume "x \<in> B"
    have "{} \<notin> (\<lambda>b. {x \<in> A. f x = b}) ` B"
    proof (cases "card B \<ge> 1")
      assume "\<not> card B \<ge> 1"
      from this have "card B = 0" by simp
      from this \<open>finite B\<close> have "B = {}" by simp
      from this show ?thesis by simp
    next
      assume "card B \<ge> 1"
      show ?thesis
      proof (rule ccontr)
        assume "\<not> {} \<notin> (\<lambda>b. {x \<in> A. f x = b}) ` B"
        from this have "{} \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B" by simp
        moreover have "card ((\<lambda>b. {x \<in> A. f x = b}) ` B) \<le> card B"
          using \<open>finite B\<close> card_image_le by blast
        moreover have "finite ((\<lambda>b. {x \<in> A. f x = b}) ` B)"
          using \<open>finite B\<close> by auto
        ultimately have "card ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) \<le> card B - 1"
          by (auto simp add: card_Diff_singleton)
        from this card_eq \<open>card B \<ge> 1\<close> show False by auto
      qed
    qed
    from this \<open>x \<in> B\<close> show "x \<in> f ` A" by force
  qed
qed

lemma card_partitions_of:
  assumes "F \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B"
  assumes "univ (\<lambda>f. f ` A = B) F"
  shows "card (partitions_of A B F) = card B"
proof -
  from \<open>F \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B\<close> obtain f where "f \<in> A \<rightarrow>\<^sub>E B"
    and F_eq: "F = range_permutation A B `` {f}" using quotientE by blast
  from this \<open>univ (\<lambda>f. f ` A = B) F\<close> have "f ` A = B"
    using univ_commute'[OF equiv_range_permutation surj_on_respects_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>] by simp
  have "card (partitions_of A B F) = card (univ (\<lambda>f. (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) F)"
    unfolding partitions_of_def ..
  also have "\<dots> = card (univ (\<lambda>f. (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) (range_permutation A B `` {f}))"
    unfolding F_eq ..
  also have "\<dots> = card ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})"
    using equiv_range_permutation domain_partitions_respects_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
    by (subst univ_commute') auto
  also from \<open>f ` A = B\<close> have "\<dots> = card B"
    using surjective_on_implies_card_eq by auto
  finally show ?thesis .
qed

lemma functions_of_is_surj_on:
  assumes "finite A" "finite B"
  assumes "partition_on A P" "card P = card B"
  shows "univ (\<lambda>f. f ` A = B) (functions_of P A B)"
proof -
  have "functions_of P A B \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B"
    using functions_of \<open>finite A\<close> \<open>finite B\<close> \<open>partition_on A P\<close> \<open>card P = card B\<close> by fastforce
  from this obtain f where eq_f: "functions_of P A B = range_permutation A B `` {f}" and "f \<in> A \<rightarrow>\<^sub>E B"
    using quotientE by blast
  from eq_f have "f \<in> functions_of P A B"
    using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> equiv_range_permutation equiv_class_self by fastforce
  from \<open>f \<in> functions_of P A B\<close> have eq: "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = P"
    unfolding functions_of_def by auto
  from this have "card ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) = card B"
    using \<open>card P = card B\<close> by simp
  from \<open>finite B\<close> \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> this have "f ` A = B"
    using card_eq_implies_surjective_on by blast
  from this show ?thesis
    unfolding eq_f using equiv_range_permutation surj_on_respects_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
    by (subst univ_commute') assumption+
qed

subsection \<open>Bijections\<close>

lemma bij_betw_partitions_of:
  assumes "finite A" "finite B"
  shows "bij_betw (partitions_of A B) ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // range_permutation A B) {P. partition_on A P \<and> card P = card B}"
proof (rule bij_betw_byWitness[where f'="\<lambda>P. functions_of P A B"])
  have quotient_eq: "{f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // range_permutation A B = {F \<in> ((A \<rightarrow>\<^sub>E B) // range_permutation A B). univ (\<lambda>f. f ` A = B) F}"
  using equiv_range_permutation[of A B] surj_on_respects_range_permutation[of A B] by (simp only: univ_preserves_predicate)
  show "\<forall>F\<in>{f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // range_permutation A B. functions_of (partitions_of A B F) A B = F"
    using \<open>finite B\<close> by (simp add: functions_of_partitions_of quotient_eq)
  show "\<forall>P\<in>{P. partition_on A P \<and> card P = card B}. partitions_of A B (functions_of P A B) = P"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp add: partitions_of_functions_of)
  show "partitions_of A B ` ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // range_permutation A B) \<subseteq> {P. partition_on A P \<and> card P = card B}"
    using \<open>finite B\<close> quotient_eq card_partitions_of partitions_of by fastforce
  show "(\<lambda>P. functions_of P A B) ` {P. partition_on A P \<and> card P = card B} \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // range_permutation A B"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp add: quotient_eq intro: functions_of functions_of_is_surj_on)
qed

subsection \<open>Cardinality\<close>

lemma card_surjective_functions_range_permutation:
  assumes "finite A" "finite B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // range_permutation A B) = Stirling (card A) (card B)"
proof -
  have "bij_betw (partitions_of A B) ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // range_permutation A B) {P. partition_on A P \<and> card P = card B}"
    using \<open>finite A\<close> \<open>finite B\<close> by (rule bij_betw_partitions_of)
  from this have "card ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // range_permutation A B) = card {P. partition_on A P \<and> card P = card B}"
    by (rule bij_betw_same_card)
  also have "card {P. partition_on A P \<and> card P = card B} = Stirling (card A) (card B)"
    using \<open>finite A\<close> by (rule card_partition_on)
  finally show ?thesis .
qed

end
