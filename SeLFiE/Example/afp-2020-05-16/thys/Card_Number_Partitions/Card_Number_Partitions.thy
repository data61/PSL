(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Cardinality of Number Partitions\<close>

theory Card_Number_Partitions
imports Number_Partition
begin

subsection \<open>The Partition Function\<close>

fun Partition :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "Partition 0 0 = 1"
| "Partition 0 (Suc k) = 0"
| "Partition (Suc m) 0 = 0"
| "Partition (Suc m) (Suc k) = Partition m k + Partition (m - k) (Suc k)"

lemma Partition_less:
  assumes "m < k"
  shows "Partition m k = 0"
using assms by (induct m k rule: Partition.induct) auto

lemma Partition_sum_Partition_diff:
  assumes "k \<le> m"
  shows "Partition m k = (\<Sum>i\<le>k. Partition (m - k) i)"
using assms by (induct m k rule: Partition.induct) auto

lemma Partition_parts1:
  "Partition (Suc m) (Suc 0) = 1"
by (induct m) auto

lemma Partition_diag:
  "Partition (Suc m) (Suc m) = 1"
by (induct m) auto

lemma Partition_diag1:
  "Partition (Suc (Suc m)) (Suc m) = 1"
by (induct m) auto

lemma Partition_parts2:
  shows "Partition m 2 = m div 2"
proof (induct m rule: nat_less_induct)
  fix m
  assume hypothesis: "\<forall>n<m. Partition n 2 = n div 2"
  have "(m = 0 \<or> m = 1) \<or> m \<ge> 2" by auto
  from this show "Partition m 2 = m div 2"
  proof
    assume "m = 0 \<or> m = 1"
    from this show ?thesis by (auto simp add: numerals(2))
  next
    assume "2 \<le> m"
    from this obtain m' where m': "m = Suc (Suc m')" by (metis add_2_eq_Suc le_Suc_ex)
    from hypothesis this have "Partition m' 2 = m' div 2" by simp
    from this m' show ?thesis
      using Partition_parts1 Partition.simps(4)[of "Suc m'" "Suc 0"] div2_Suc_Suc
      by (simp add: numerals(2) del: Partition.simps)
  qed
qed

subsection \<open>Cardinality of Number Partitions\<close>

lemma set_rewrite1:
  "{p. p partitions Suc m \<and> sum p {..Suc m} = Suc k \<and> p 1 \<noteq> 0}
    = (\<lambda>p. p(1 := p 1 + 1)) ` {p. p partitions m \<and> sum p {..m} = k}" (is "?S = ?T")
proof
  {
    fix p
    assume assms: "p partitions Suc m" "sum p {..Suc m} = Suc k" "0 < p 1"
    have "p(1 := p 1 - 1) partitions m"
      using assms by (metis partitions_remove1 diff_Suc_1)
    moreover have "(\<Sum>i\<le>m. (p(1 := p 1 - 1)) i) = k"
      using assms by (metis count_remove1 diff_Suc_1)
    ultimately have "p(1 := p 1 - 1) \<in> {p. p partitions m \<and> sum p {..m} = k}" by simp
    moreover have "p = p(1 := p 1 - 1, 1 := (p(1 := p 1 - 1)) 1 + 1)"
      using \<open>0 < p 1\<close> by auto
    ultimately have "p \<in> (\<lambda>p. p(1 := p 1 + 1)) ` {p. p partitions m \<and> sum p {..m} = k}" by blast
  }
  from this show "?S \<subseteq> ?T" by blast
next
  {
    fix p
    assume assms: "p partitions m" "sum p {..m} = k"
    have "(p(1 := p 1 + 1)) partitions Suc m" (is ?g1)
      using assms by (metis partitions_insert1 Suc_eq_plus1 zero_less_one)
    moreover have "sum (p(1 := p 1 + 1)) {..Suc m} = Suc k" (is ?g2)
      using assms by (metis count_insert1 Suc_eq_plus1)
    moreover have "(p(1 := p 1 + 1)) 1 \<noteq> 0" (is ?g3) by auto
    ultimately have "?g1 \<and> ?g2 \<and> ?g3" by simp
  }
  from this show "?T \<subseteq> ?S" by auto
qed

lemma set_rewrite2:
  "{p. p partitions m \<and> sum p {..m} = k \<and> p 1 = 0}
    = (\<lambda>p. (\<lambda>i. p (i - 1))) ` {p. p partitions (m - k) \<and> sum p {..m - k} = k}"
  (is "?S = ?T")
proof
  {
    fix p
    assume assms: "p partitions m" "sum p {..m} = k" "p 1 = 0"
    have "(\<lambda>i. p (i + 1)) partitions m - k"
      using assms partitions_decrease1 by blast
    moreover from assms have "sum (\<lambda>i. p (i + 1)) {..m - k} = k"
      using assms count_decrease1 by blast
    ultimately have "(\<lambda>i. p (i + 1)) \<in> {p. p partitions m - k \<and> sum p {..m - k} = k}" by simp
    moreover have "p = (\<lambda>i. p ((i - 1) + 1))"
    proof (rule ext)
      fix i show "p i = p (i - 1 + 1)"
        using assms by (cases i) (auto elim!: partitionsE)
    qed
    ultimately have "p \<in> (\<lambda>p. (\<lambda>i. p (i - 1))) ` {p. p partitions m - k \<and> sum p {..m - k} = k}" by auto
  }
  from this show "?S \<subseteq> ?T" by auto
next
   {
     fix p
     assume assms: "p partitions m - k" "sum p {..m - k} = k"
     from assms have "(\<lambda>i. p (i - 1)) partitions m" (is ?g1)
       using partitions_increase1 by blast
     moreover from assms have "(\<Sum>i\<le>m. p (i - 1)) = k" (is ?g2)
       using count_increase1 by blast
     moreover from assms have "p 0 = 0" (is ?g3)
       by (auto elim!: partitionsE)
     ultimately have "?g1 \<and> ?g2 \<and> ?g3" by simp
   }
   from this show "?T \<subseteq> ?S" by auto
qed

theorem card_partitions_k_parts:
  "card {p. p partitions n \<and> (\<Sum>i\<le>n. p i) = k} = Partition n k"
proof (induct n k rule: Partition.induct)
  case 1
  have eq: "{p. p = (\<lambda>x. 0) \<and> p 0 = 0} = {(\<lambda>x. 0)}" by auto
  show "card {p. p partitions 0 \<and> sum p {..0} = 0} = Partition 0 0"
    by (simp add: partitions_zero eq)
next
  case (2 k)
  have eq: "{p. p = (\<lambda>x. 0) \<and> p 0 = Suc k} = {}" by auto
  show "card {p. p partitions 0 \<and> sum p {..0} = Suc k} = Partition 0 (Suc k)"
    by (simp add: partitions_zero eq)
next
  case (3 m)
  have eq: "{p. p partitions Suc m \<and> sum p {..Suc m} = 0} = {}"
    by (fastforce elim!: partitionsE simp add: le_Suc_eq)
  from this show "card {p. p partitions Suc m \<and> sum p {..Suc m} = 0} = Partition (Suc m) 0"
    by (simp only: Partition.simps card_empty)
next
  case (4 m k)
  let ?set1 = "{p. p partitions Suc m \<and> sum p {..Suc m} = Suc k \<and> p 1 \<noteq> 0}"
  let ?set2 = "{p. p partitions Suc m \<and> sum p {..Suc m} = Suc k \<and> p 1 = 0}"
  have "finite {p. p partitions Suc m}"
    by (simp add: finite_partitions)
  from this have finite_sets: "finite ?set1" "finite ?set2" by simp+
  have set_eq: "{p. p partitions Suc m \<and> sum p {..Suc m} = Suc k} = ?set1 \<union> ?set2" by auto
  have disjoint: "?set1 \<inter> ?set2 = {}" by auto
  have inj1: "inj_on (\<lambda>p. p(1 := p 1 + 1)) {p. p partitions m \<and> sum p {..m} = k}"
    by (auto intro!: inj_onI) (metis diff_Suc_1 fun_upd_idem_iff fun_upd_upd)
  have inj2: "inj_on (\<lambda>p i. p (i - 1)) {p. p partitions m - k \<and> sum p {..m - k} = Suc k}"
    by (auto intro!: inj_onI simp add: fun_eq_iff) (metis add_diff_cancel_right')
  have card1: "card ?set1 = Partition m k"
    using inj1 4(1) by (simp only: set_rewrite1 card_image)
  have card2: "card ?set2 = Partition (m - k) (Suc k)"
    using inj2 4(2) by (simp only: set_rewrite2 card_image diff_Suc_Suc)
  have "card {p. p partitions Suc m \<and> sum p {..Suc m} = Suc k} = Partition m k + Partition (m - k) (Suc k)"
    using finite_sets disjoint by (simp only: set_eq card_Un_disjoint card1 card2)
  from this show "card {p. p partitions Suc m \<and> sum p {..Suc m} = Suc k} = Partition (Suc m) (Suc k)"
    by auto
qed

theorem card_partitions:
  "card {p. p partitions n} = (\<Sum>k\<le>n. Partition n k)"
proof -
  have seteq: "{p. p partitions n} = \<Union>((\<lambda>k. {p. p partitions n \<and> (\<Sum>i\<le>n. p i) = k}) ` {..n})"
    by (auto intro: partitions_parts_bounded)
  have finite: "\<And>k. finite {p. p partitions n \<and> sum p {..n} = k}"
    by (simp add: finite_partitions)
  have "card {p. p partitions n} = card (\<Union>((\<lambda>k. {p. p partitions n \<and> (\<Sum>i\<le>n. p i) = k}) ` {..n}))"
    using finite by (simp add: seteq)
  also have "... = (\<Sum>x\<le>n. card {p. p partitions n \<and> sum p {..n} = x})"
    using finite by (subst card_UN_disjoint) auto
  also have "... = (\<Sum>k\<le>n. Partition n k)"
    by (simp add: card_partitions_k_parts)
  finally show ?thesis .
qed

lemma card_partitions_atmost_k_parts:
  "card {p. p partitions n \<and> sum p {..n} \<le> k} = Partition (n + k) k"
proof -
  have "card {p. p partitions n \<and> sum p {..n} \<le> k} =
    card (\<Union>((\<lambda>k'. {p. p partitions n \<and> sum p {..n} = k'}) ` {..k}))"
  proof -
    have "{p. p partitions n \<and> sum p {..n} \<le> k} =
      (\<Union>k'\<le>k. {p. p partitions n \<and> sum p {..n} = k'})" by auto
    from this show ?thesis by simp
  qed
  also have "card (\<Union>((\<lambda>k'. {p. p partitions n \<and> sum p {..n} = k'}) ` {..k})) =
    sum (\<lambda>k'. card {p. p partitions n \<and> sum p {..n} = k'}) {..k}"
    using finite_partitions_k_parts by (subst card_UN_disjoint) auto
  also have "\<dots> = sum (\<lambda>k'. Partition n k') {..k}"
    using card_partitions_k_parts by simp
  also have "\<dots> = Partition (n + k) k"
    using Partition_sum_Partition_diff by simp
  finally show ?thesis .
qed

subsection \<open>Cardinality of Number Partitions as Multisets of Natural Numbers\<close>

lemma bij_betw_multiset_number_partition_with_size:
  "bij_betw count {N. number_partition n N \<and> size N = k} {p. p partitions n \<and> sum p {..n} = k}"
proof (rule bij_betw_byWitness[where f'="Abs_multiset"])
  show "\<forall>N\<in>{N. number_partition n N \<and> size N = k}. Abs_multiset (count N) = N"
    using count_inverse by blast
  show "\<forall>p\<in>{p. p partitions n \<and> sum p {..n} = k}. count (Abs_multiset p) = p"
    by (auto simp add: multiset_def partitions_imp_finite_elements)
  show "count ` {N. number_partition n N \<and> size N = k} \<subseteq> {p. p partitions n \<and> sum p {..n} = k}"
    by (auto simp add: count_partitions_iff size_nat_multiset_eq) 
  show "Abs_multiset ` {p. p partitions n \<and> sum p {..n} = k} \<subseteq> {N. number_partition n N \<and> size N = k}"
    using partitions_iff_Abs_multiset size_nat_multiset_eq partitions_imp_multiset by fastforce
qed

lemma bij_betw_multiset_number_partition_with_atmost_size:
  "bij_betw count {N. number_partition n N \<and> size N \<le> k} {p. p partitions n \<and> sum p {..n} \<le> k}"
proof (rule bij_betw_byWitness[where f'="Abs_multiset"])
  show "\<forall>N\<in>{N. number_partition n N \<and> size N \<le> k}. Abs_multiset (count N) = N"
    using count_inverse by blast
  show "\<forall>p\<in>{p. p partitions n \<and> sum p {..n} \<le> k}. count (Abs_multiset p) = p"
    by (auto simp add: multiset_def partitions_imp_finite_elements)
  show "count ` {N. number_partition n N \<and> size N \<le> k} \<subseteq> {p. p partitions n \<and> sum p {..n} \<le> k}"
    by (auto simp add: count_partitions_iff size_nat_multiset_eq)
  show "Abs_multiset ` {p. p partitions n \<and> sum p {..n} \<le> k} \<subseteq> {N. number_partition n N\<and> size N \<le> k}"
    using partitions_iff_Abs_multiset size_nat_multiset_eq partitions_imp_multiset by fastforce
qed

theorem card_number_partitions_with_atmost_k_parts:
  shows "card {N. number_partition n N \<and> size N \<le> x} = Partition (n + x) x"
proof -
  have "bij_betw count {N. number_partition n N \<and> size N \<le> x} {p. p partitions n \<and> sum p {..n} \<le> x}"
    by (rule bij_betw_multiset_number_partition_with_atmost_size)
  from this have "card {N. number_partition n N \<and> size N \<le> x} = card {p. p partitions n \<and> sum p {..n} \<le> x}"
    by (rule bij_betw_same_card)
  also have "card {p. p partitions n \<and> sum p {..n} \<le> x} = Partition (n + x) x"
    by (rule card_partitions_atmost_k_parts)
  finally show ?thesis .
qed

theorem card_partitions_with_k_parts:
  "card {N. number_partition n N \<and> size N = k} = Partition n k"
proof -
  have "bij_betw count {N. number_partition n N \<and> size N = k} {p. p partitions n \<and> sum p {..n} = k}"
    by (rule bij_betw_multiset_number_partition_with_size)
  from this have "card {N. number_partition n N \<and> size N = k} = card {p. p partitions n \<and> sum p {..n} = k}"
    by (rule bij_betw_same_card)
  also have "\<dots> = Partition n k" by (rule card_partitions_k_parts)
  finally show ?thesis .
qed

subsection \<open>Cardinality of Number Partitions with only 1-parts\<close>

lemma number_partition1_eq_replicate_mset:
  "{N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition n N} = {replicate_mset n 1}"
proof
  show "{N. (\<forall>n. n \<in># N \<longrightarrow> n = 1) \<and> number_partition n N} \<subseteq> {replicate_mset n 1}"
  proof
    fix N
    assume N: "N \<in> {N. (\<forall>n. n \<in># N \<longrightarrow> n = 1) \<and> number_partition n N}"
    have "N = replicate_mset n 1"
    proof (rule multiset_eqI)
      fix i
      have "count N 1 = sum_mset N"
      proof cases
        assume "N = {#}"
        from this show ?thesis by auto
      next
        assume "N \<noteq> {#}"
        from this N have "1 \<in># N" by blast
        from this N show ?thesis
          by (auto simp add: sum_mset_sum_count sum.remove[where x="1"] simp del: One_nat_def)
      qed
      from N this show "count N i = count (replicate_mset n 1) i"
        unfolding number_partition_def by (auto intro: count_inI)
    qed
    from this show "N \<in> {replicate_mset n 1}" by simp
  qed
next
  show "{replicate_mset n 1} \<subseteq> {N. (\<forall>n. n \<in># N \<longrightarrow> n = 1) \<and> number_partition n N}"
    unfolding number_partition_def by auto
qed

lemma card_number_partitions_with_only_parts_1_eq_1:
  assumes "n \<le> x"
  shows "card {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition n N \<and> size N \<le> x} = 1" (is "card ?N = _")
proof -
  have "\<forall>N \<in> {N. (\<forall>n. n \<in># N \<longrightarrow> n = 1) \<and> number_partition n N}. size N = n"
    unfolding number_partition1_eq_replicate_mset by simp
  from this number_partition1_eq_replicate_mset \<open>n \<le> x\<close> have "?N = {replicate_mset n 1}" by auto
  from this show ?thesis by simp
qed

lemma card_number_partitions_with_only_parts_1_eq_0:
  assumes "x < n"
  shows "card {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition n N \<and> size N \<le> x} = 0" (is "card ?N = _")
proof -
  have "\<forall>N \<in> {N. (\<forall>n. n \<in># N \<longrightarrow> n = 1) \<and> number_partition n N}. size N = n"
    unfolding number_partition1_eq_replicate_mset by simp
  from this number_partition1_eq_replicate_mset\<open>x < n\<close> have "?N = {}" by auto
  from this show ?thesis by (simp only: card_empty)
qed

end
