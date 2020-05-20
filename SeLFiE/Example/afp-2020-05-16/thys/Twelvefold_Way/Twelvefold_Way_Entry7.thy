(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Functions from A to B up to a Permutation on B\<close>

theory Twelvefold_Way_Entry7
imports Equiv_Relations_on_Functions
begin

subsection \<open>Definition of Bijections\<close>

definition partitions_of :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set \<Rightarrow> 'a set set"
where
  "partitions_of A B F = univ (\<lambda>f. (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) F"

definition functions_of :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"
where
  "functions_of P A B = {f \<in> A \<rightarrow>\<^sub>E B. (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = P}"

subsection \<open>Properties for Bijections\<close>

lemma partitions_of:
  assumes "finite B"
  assumes "F \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B"
  shows "card (partitions_of A B F) \<le> card B"
  and "partition_on A (partitions_of A B F)"
proof -
  from \<open>F \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B\<close> obtain f where "f \<in> A \<rightarrow>\<^sub>E B"
    and F_eq: "F = range_permutation A B `` {f}" using quotientE by blast
  have "partitions_of A B F = univ (\<lambda>f. (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) F"
    unfolding partitions_of_def ..
  also have "\<dots> = univ (\<lambda>f. (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) (range_permutation A B `` {f})"
    unfolding F_eq ..
  also have "\<dots> = (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
    using equiv_range_permutation domain_partitions_respects_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
    by (subst univ_commute') auto
  finally have partitions_of_eq: "partitions_of A B F = (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}" .
  show "card (partitions_of A B F) \<le> card B"
  proof -
    have "card (partitions_of A B F) = card ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})"
      unfolding partitions_of_eq ..
    also have "\<dots> \<le> card ((\<lambda>b. {x \<in> A. f x = b}) ` B)"
      using \<open>finite B\<close> by (auto intro: card_mono)
    also have "\<dots> \<le> card B"
      using \<open>finite B\<close> by (rule card_image_le)
    finally show ?thesis .
  qed
  show "partition_on A (partitions_of A B F)"
  proof -
    have "partition_on A ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})"
      using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> by (auto intro!: partition_onI)
    from this show ?thesis
      unfolding partitions_of_eq .
  qed
qed

lemma functions_of:
  assumes "finite A" "finite B"
  assumes "partition_on A P"
  assumes "card P \<le> card B"
  shows "functions_of P A B \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B"
proof -
  obtain f where "f \<in> A \<rightarrow>\<^sub>E B" and r1: "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = P"
    using obtain_function_with_partition[OF \<open>finite A\<close> \<open>finite B\<close> \<open>partition_on A P\<close> \<open>card P \<le> card B\<close>]
    by blast
  have "functions_of P A B = range_permutation A B `` {f}"
  proof
    show "functions_of P A B \<subseteq> range_permutation A B `` {f}"
    proof
      fix f'
      assume "f' \<in> functions_of P A B"
      from this have "f' \<in> A \<rightarrow>\<^sub>E B" and r2: "(\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}} = P"
        unfolding functions_of_def by auto
      from r1 r2
      obtain p where "p permutes B \<and> (\<forall>x\<in>A. f x = p (f' x))"
        using partitions_eq_implies_permutes[OF \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close>] \<open>finite B\<close> by metis
      from this show "f' \<in> range_permutation A B `` {f}"
        using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close>
        unfolding range_permutation_def by auto
    qed
  next
    show "range_permutation A B `` {f} \<subseteq> functions_of P A B"
    proof
      fix f'
      assume "f' \<in> range_permutation A B `` {f}"
      from this have "(f, f') \<in> range_permutation A B" by auto
      from this have "f' \<in> A \<rightarrow>\<^sub>E B"
        unfolding range_permutation_def by auto
      from \<open>(f, f') \<in> range_permutation A B\<close> have
        "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = (\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}"
        using congruentD[OF domain_partitions_respects_range_permutation] by blast
      from \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> this r1 show "f' \<in> functions_of P A B"
        unfolding functions_of_def by auto
    qed
  qed
  from this \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> show ?thesis by (auto intro: quotientI)
qed

lemma functions_of_partitions_of:
  assumes "finite B"
  assumes "F \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B"
  shows "functions_of (partitions_of A B F) A B = F"
proof -
  from \<open>F \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B\<close> obtain f where "f \<in> A \<rightarrow>\<^sub>E B"
    and F_eq: "F = range_permutation A B `` {f}" using quotientE by blast
  have partitions_of_eq: "partitions_of A B F = (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
        unfolding partitions_of_def F_eq
        using equiv_range_permutation domain_partitions_respects_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
        by (subst univ_commute') auto
  show ?thesis
  proof
    show "functions_of (partitions_of A B F) A B \<subseteq> F"
    proof
      fix f'
      assume f': "f' \<in> functions_of (partitions_of A B F) A B"
      from this have "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = (\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}"
        unfolding functions_of_def by (auto simp add: partitions_of_eq)
      note \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
      moreover from f' have "f' \<in> A \<rightarrow>\<^sub>E B"
        unfolding functions_of_def by auto
      moreover obtain p where "p permutes B \<and> (\<forall>x\<in>A. f x = p (f' x))"
        using partitions_eq_implies_permutes[OF \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> \<open>finite B\<close>
          \<open>(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = (\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}\<close>]
        by metis
      ultimately show "f' \<in> F"
        unfolding F_eq range_permutation_def by auto
    qed
  next
    show "F \<subseteq> functions_of (partitions_of A B F) A B"
    proof
      fix f'
      assume "f' \<in> F"
      from this have "f' \<in> A \<rightarrow>\<^sub>E B"
        unfolding F_eq range_permutation_def by auto
      from \<open>f' \<in> F\<close> obtain p where "p permutes B" "\<forall>x\<in>A. f x = p (f' x)"
        unfolding F_eq range_permutation_def by auto
      have eq: "(\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}} = (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
      proof -
        have "(\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}} = (\<lambda>b. {x \<in> A. p (f' x) = b}) ` B - {{}}"
          using permutes_implies_inv_image_on_eq[OF \<open>p permutes B\<close>, of A f'] by simp
        also have "\<dots> =  (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
          using \<open>\<forall>x\<in>A. f x = p (f' x)\<close> by auto
        finally show ?thesis .
      qed
      from this \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> show "f' \<in> functions_of (partitions_of A B F) A B"
        unfolding functions_of_def partitions_of_eq by auto
    qed
  qed
qed

lemma partitions_of_functions_of:
  assumes "finite A" "finite B"
  assumes "partition_on A P"
  assumes "card P \<le> card B"
  shows "partitions_of A B (functions_of P A B) = P"
proof -
  have "functions_of P A B \<in> (A \<rightarrow>\<^sub>E B) // range_permutation A B"
    using \<open>finite A\<close> \<open>finite B\<close> \<open>partition_on A P\<close> \<open>card P \<le> card B\<close> by (rule functions_of)
  from this obtain f where "f \<in> A \<rightarrow>\<^sub>E B" and functions_of_eq: "functions_of P A B = range_permutation A B `` {f}"
    using quotientE by metis
  from functions_of_eq \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> have "f \<in> functions_of P A B"
    using equiv_range_permutation equiv_class_self by fastforce
  have "partitions_of A B (functions_of P A B) = univ (\<lambda>f. (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) (functions_of P A B)"
    unfolding partitions_of_def ..
  also have "\<dots> = univ (\<lambda>f. (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) (range_permutation A B `` {f})"
    unfolding \<open>functions_of P A B = range_permutation A B `` {f}\<close> ..
  also have "\<dots> = (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
    using equiv_range_permutation domain_partitions_respects_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
    by (subst univ_commute') auto
  also have "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = P"
    using \<open>f \<in> functions_of P A B\<close> unfolding functions_of_def by simp
  finally show ?thesis .
qed

subsection \<open>Bijections\<close>

lemma bij_betw_partitions_of:
  assumes "finite A" "finite B"
  shows "bij_betw (partitions_of A B) ((A \<rightarrow>\<^sub>E B) // range_permutation A B) {P. partition_on A P \<and> card P \<le> card B}"
proof (rule bij_betw_byWitness[where f'="\<lambda>P. functions_of P A B"])
  show "\<forall>F\<in>(A \<rightarrow>\<^sub>E B) // range_permutation A B. functions_of (partitions_of A B F) A B = F"
    using \<open>finite B\<close> by (simp add: functions_of_partitions_of)
  show "\<forall>P\<in>{P. partition_on A P \<and> card P \<le> card B}. partitions_of A B (functions_of P A B) = P"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp add: partitions_of_functions_of)
  show "partitions_of A B ` ((A \<rightarrow>\<^sub>E B) // range_permutation A B) \<subseteq> {P. partition_on A P \<and> card P \<le> card B}"
    using \<open>finite B\<close> partitions_of by auto
  show "(\<lambda>P. functions_of P A B) ` {P. partition_on A P \<and> card P \<le> card B} \<subseteq> (A \<rightarrow>\<^sub>E B) // range_permutation A B"
    using functions_of \<open>finite A\<close> \<open>finite B\<close> by auto
qed

subsection \<open>Cardinality\<close>

lemma
  assumes "finite A" "finite B"
  shows "card ((A \<rightarrow>\<^sub>E B) // range_permutation A B) = (\<Sum>j\<le>card B. Stirling (card A) j)"
proof -
  have "bij_betw (partitions_of A B) ((A \<rightarrow>\<^sub>E B) // range_permutation A B) {P. partition_on A P \<and> card P \<le> card B}"
    using \<open>finite A\<close> \<open>finite B\<close> by (rule bij_betw_partitions_of)
  from this have "card ((A \<rightarrow>\<^sub>E B) // range_permutation A B) = card {P. partition_on A P \<and> card P \<le> card B}"
    by (rule bij_betw_same_card)
  also have "card  {P. partition_on A P \<and> card P \<le> card B} = (\<Sum>j\<le>card B. Stirling (card A) j)"
    using \<open>finite A\<close> by (rule card_partition_on_at_most_size)
  finally show ?thesis .
qed

end
