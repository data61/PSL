(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Functions from A to B up to a Permutation on A and B\<close>

theory Twelvefold_Way_Entry10
imports Equiv_Relations_on_Functions
begin

subsection \<open>Definition of Bijections\<close>

definition number_partition_of :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set \<Rightarrow> nat multiset"
where
  "number_partition_of A B F = univ (\<lambda>f. image_mset (\<lambda>X. card X) (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))) F"

definition functions_of :: "'a set \<Rightarrow> 'b set \<Rightarrow> nat multiset \<Rightarrow> ('a \<Rightarrow> 'b) set"
where
  "functions_of A B N = {f \<in> A \<rightarrow>\<^sub>E B. image_mset (\<lambda>X. card X) (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})) = N}"

subsection \<open>Properties for Bijections\<close>

lemma card_setsum_partition:
  assumes "finite A" "finite B" "f \<in> A \<rightarrow>\<^sub>E B"
  shows "sum card ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) = card A"
proof -
  have "finite ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})"
    using \<open>finite B\<close> by blast
  moreover have "\<forall>X\<in>(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}. finite X"
    using \<open>finite A\<close> by auto
  moreover have "\<Union>((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) = A"
    using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> by auto
  ultimately show ?thesis
    by (subst card_Union_disjoint[symmetric]) (auto simp: pairwise_def disjnt_def)
qed

lemma number_partition_of:
  assumes "finite A" "finite B"
  assumes "F \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B"
  shows "number_partition (card A) (number_partition_of A B F)"
  and "size (number_partition_of A B F) \<le> card B"
proof -
  from \<open>F \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B\<close> obtain f where "f \<in> A \<rightarrow>\<^sub>E B"
    and F_eq: "F = domain_and_range_permutation A B `` {f}" using quotientE by blast
  have number_partition_of_eq: "number_partition_of A B F = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))"
  proof -
    have "number_partition_of A B F = univ (\<lambda>f. image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))) F"
      unfolding number_partition_of_def ..
    also have "\<dots> = univ (\<lambda>f. image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))) (domain_and_range_permutation A B `` {f})"
      unfolding F_eq ..
    also have "\<dots> = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))"
      using \<open>finite B\<close> equiv_domain_and_range_permutation multiset_of_partition_cards_respects_domain_and_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
      by (subst univ_commute') auto
    finally show ?thesis .
  qed
  show "number_partition (card A) (number_partition_of A B F)"
  proof -
    have "sum_mset (number_partition_of A B F) = card A"
      using number_partition_of_eq \<open>finite A\<close> \<open>finite B\<close> \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
      by (simp only: sum_unfold_sum_mset[symmetric] card_setsum_partition)
    moreover have "0 \<notin># number_partition_of A B F"
    proof -
      have "\<forall>X \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B. finite X"
        using \<open>finite A\<close> by simp
      from this have "\<forall>X \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}. card X \<noteq> 0" by auto
      from this show ?thesis
        using number_partition_of_eq \<open>finite B\<close> by (simp add: image_iff)
    qed
    ultimately show ?thesis unfolding number_partition_def by simp
  qed
  show "size (number_partition_of A B F) \<le> card B"
    using number_partition_of_eq \<open>finite A\<close> \<open>finite B\<close>
    by (metis (no_types, lifting) card_Diff1_le card_image_le finite_imageI le_trans size_image_mset size_mset_set)
qed

lemma functions_of:
  assumes "finite A" "finite B"
  assumes "number_partition (card A) N"
  assumes "size N \<le> card B"
  shows "functions_of A B N \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B"
proof -
  obtain f where "f \<in> A \<rightarrow>\<^sub>E B" and eq_N: "image_mset (\<lambda>X. card X) (mset_set (((\<lambda>b. {x \<in> A. f x = b})) ` B - {{}})) = N"
    using obtain_extensional_function_from_number_partition \<open>finite A\<close> \<open>finite B\<close> \<open>number_partition (card A) N\<close> \<open>size N \<le> card B\<close> by blast
  have "functions_of A B N = (domain_and_range_permutation A B) `` {f}"
  proof
    show "functions_of A B N \<subseteq> domain_and_range_permutation A B `` {f}"
    proof
      fix f'
      assume "f' \<in> functions_of A B N"
      from this have eq_N': "N = image_mset (\<lambda>X. card X) (mset_set (((\<lambda>b. {x \<in> A. f' x = b})) ` B - {{}}))"
        and "f' \<in> A \<rightarrow>\<^sub>E B"
        unfolding functions_of_def by auto
      from \<open>finite A\<close> \<open>finite B\<close> \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close>
      obtain p\<^sub>A p\<^sub>B where "p\<^sub>A permutes A" "p\<^sub>B permutes B" "\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))"
        using eq_N eq_N' multiset_of_partition_cards_eq_implies_permutes[of A B f f'] by blast
      from this show "f' \<in> domain_and_range_permutation A B `` {f}"
        using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close>
        unfolding domain_and_range_permutation_def by auto
    qed
  next
    show "domain_and_range_permutation A B `` {f} \<subseteq> functions_of A B N"
    proof
      fix f'
      assume "f' \<in> domain_and_range_permutation A B `` {f}"
      from this have in_equiv_relation: "(f, f') \<in> domain_and_range_permutation A B" by auto
      from eq_N \<open>finite B\<close> have "image_mset (\<lambda>X. card X) (mset_set (((\<lambda>b. {x \<in> A. f' x = b})) ` B - {{}})) = N"
        using congruentD[OF multiset_of_partition_cards_respects_domain_and_range_permutation in_equiv_relation]
        by metis
      moreover from \<open>(f, f') \<in> domain_and_range_permutation A B\<close> have "f' \<in> A \<rightarrow>\<^sub>E B"
        unfolding domain_and_range_permutation_def by auto
      ultimately show "f' \<in> functions_of A B N"
        unfolding functions_of_def by auto
    qed
  qed
  from this \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> show ?thesis by (auto intro: quotientI)
qed

lemma functions_of_number_partition_of:
  assumes "finite A" "finite B"
  assumes "F \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B"
  shows "functions_of A B (number_partition_of A B F) = F"
proof -
  from \<open>F \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B\<close> obtain f where "f \<in> A \<rightarrow>\<^sub>E B"
    and F_eq: "F = domain_and_range_permutation A B `` {f}" using quotientE by blast
  have "number_partition_of A B F = univ (\<lambda>f. image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))) F"
    unfolding number_partition_of_def ..
  also have "\<dots> = univ (\<lambda>f. image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))) (domain_and_range_permutation A B `` {f})"
    unfolding F_eq ..
  also have "\<dots> = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))"
    using \<open>finite B\<close>
    using equiv_domain_and_range_permutation multiset_of_partition_cards_respects_domain_and_range_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
    by (subst univ_commute') auto
  finally have number_partition_of_eq: "number_partition_of A B F = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))" .
  show ?thesis
  proof
    show "functions_of A B (number_partition_of A B F) \<subseteq> F"
    proof
      fix f'
      assume "f' \<in> functions_of A B (number_partition_of A B F)"
      from this have "f' \<in> A \<rightarrow>\<^sub>E B"
        and eq: "image_mset card (mset_set ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}})) = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))"
        unfolding functions_of_def by (auto simp add: number_partition_of_eq)
      note \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close>
      moreover obtain p\<^sub>A p\<^sub>B where "p\<^sub>A permutes A" "p\<^sub>B permutes B" "\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))"
        using \<open>finite A\<close> \<open>finite B\<close> \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> eq
          multiset_of_partition_cards_eq_implies_permutes[of A B f f']
        by metis
      ultimately show "f' \<in> F"
        unfolding F_eq domain_and_range_permutation_def by auto
    qed
  next
    show "F \<subseteq> functions_of A B (number_partition_of A B F)"
    proof
      fix f'
      assume "f' \<in> F"
      from \<open>f' \<in> F\<close> obtain p\<^sub>A p\<^sub>B where "p\<^sub>A permutes A" "p\<^sub>B permutes B" "\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))"
        unfolding F_eq domain_and_range_permutation_def by auto
      have eq: "image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})) = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}))"
      proof -
        have "(\<lambda>b. {x \<in> A. f x = b}) ` B = (\<lambda>b. {x \<in> A. p\<^sub>B (f' (p\<^sub>A x)) = b}) ` B"
          using \<open>\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))\<close> by auto
        from this have "image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})) =
          image_mset card (mset_set ((\<lambda>b. {x \<in> A. p\<^sub>B (f' (p\<^sub>A x)) = b}) ` B - {{}}))" by simp
        also have "\<dots> = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}))"
          using \<open>p\<^sub>A permutes A\<close> \<open>p\<^sub>B permutes B\<close> permutes_implies_multiset_of_partition_cards_eq by blast
        finally show ?thesis .
      qed
      moreover from \<open>f' \<in> F\<close> have "f' \<in> A \<rightarrow>\<^sub>E B"
        unfolding F_eq domain_and_range_permutation_def by auto
      ultimately show "f' \<in> functions_of A B (number_partition_of A B F)"
        unfolding functions_of_def number_partition_of_eq by auto
    qed
  qed
qed

lemma number_partition_of_functions_of:
  assumes "finite A" "finite B"
  assumes "number_partition (card A) N" "size N \<le> card B"
  shows "number_partition_of A B (functions_of A B N) = N"
proof -
  from assms have "functions_of A B N \<in> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B"
    using functions_of assms by fastforce
  from this obtain f where "f \<in> A \<rightarrow>\<^sub>E B" and "functions_of A B N = domain_and_range_permutation A B `` {f}"
    by (meson quotientE)
  from this have "f \<in> functions_of A B N"
    using equiv_domain_and_range_permutation equiv_class_self by fastforce
  have "number_partition_of A B (functions_of A B N) = univ (\<lambda>f. image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))) (functions_of A B N)"
    unfolding number_partition_of_def ..
  also have "\<dots> = univ (\<lambda>f.  image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))) (domain_and_range_permutation A B `` {f})"
    unfolding \<open>functions_of A B N = domain_and_range_permutation A B `` {f}\<close> ..
  also have "\<dots> = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}))"
    using \<open>finite B\<close> \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> equiv_domain_and_range_permutation
      multiset_of_partition_cards_respects_domain_and_range_permutation
    by (subst univ_commute') auto
  also have "image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})) = N"
    using \<open>f \<in> functions_of A B N\<close> unfolding functions_of_def by simp
  finally show ?thesis .
qed

subsection \<open>Bijections\<close>

lemma bij_betw_number_partition_of:
  assumes "finite A" "finite B"
  shows "bij_betw (number_partition_of A B) ((A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B) {N. number_partition (card A) N \<and> size N \<le> card B}"
proof (rule bij_betw_byWitness[where f'="\<lambda>M. functions_of A B M"])
  show "\<forall>F\<in>(A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B. functions_of A B (number_partition_of A B F) = F"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp add: functions_of_number_partition_of)
  show "\<forall>N\<in>{N. number_partition (card A) N \<and> size N \<le> card B}. number_partition_of A B (functions_of A B N) = N"
    using \<open>finite A\<close> \<open>finite B\<close> by (auto simp add: number_partition_of_functions_of)
  show "number_partition_of A B ` ((A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B) \<subseteq> {N. number_partition (card A) N \<and> size N \<le> card B}"
    using number_partition_of[of A B] \<open>finite A\<close> \<open>finite B\<close> by auto
  show "functions_of A B ` {N. number_partition (card A) N \<and> size N \<le> card B} \<subseteq> (A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B"
    using functions_of \<open>finite A\<close> \<open>finite B\<close> by blast
qed

subsection \<open>Cardinality\<close>

lemma card_domain_and_range_permutation:
  assumes "finite A" "finite B"
  shows "card ((A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B) = Partition (card A + card B) (card B)"
proof -
  have "bij_betw (number_partition_of A B) ((A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B) {N. number_partition (card A) N \<and> size N \<le> card B}"
    using \<open>finite A\<close> \<open>finite B\<close> by (rule bij_betw_number_partition_of)
  from this have "card ((A \<rightarrow>\<^sub>E B) // domain_and_range_permutation A B) = card {N. number_partition (card A) N \<and> size N \<le> card B}"
    by (rule bij_betw_same_card)
  also have "card {N. number_partition (card A) N \<and> size N \<le> card B} = Partition (card A + card B) (card B)"
    by (rule card_number_partitions_with_atmost_k_parts)
  finally show ?thesis .
qed

end
