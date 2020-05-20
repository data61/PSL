(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Number Partitions\<close>

theory Number_Partition
imports Additions_to_Main
begin

subsection \<open>Number Partitions as @{typ "nat => nat"} Functions\<close>

definition partitions :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" (infix "partitions" 50)
where
  "p partitions n = ((\<forall>i. p i \<noteq> 0 \<longrightarrow> 1 \<le> i \<and> i \<le> n) \<and> (\<Sum>i\<le>n. p i * i) = n)"

lemma partitionsI:
  assumes "\<And>i. p i \<noteq> 0 \<Longrightarrow> 1 \<le> i \<and> i \<le> n"
  assumes "(\<Sum>i\<le>n. p i * i) = n"
  shows "p partitions n"
using assms unfolding partitions_def by auto

lemma partitionsE:
  assumes "p partitions n"
  obtains "\<And>i. p i \<noteq> 0 \<Longrightarrow> 1 \<le> i \<and> i \<le> n" "(\<Sum>i\<le>n. p i * i) = n"
using assms unfolding partitions_def by auto

lemma partitions_zero:
  "p partitions 0 \<longleftrightarrow> p = (\<lambda>i. 0)"
unfolding partitions_def by auto

lemma partitions_one:
  "p partitions (Suc 0) \<longleftrightarrow> p = (\<lambda>i. 0)(1 := 1)"
unfolding partitions_def
by (auto split: if_split_asm) (auto simp add: fun_eq_iff)

subsection \<open>Bounds and Finiteness of Number Partitions\<close>

lemma partitions_imp_finite_elements:
  assumes "p partitions n"
  shows "finite {i. 0 < p i}"
proof -
  from assms have "{i. 0 < p i} \<subseteq> {..n}" by (auto elim: partitionsE)
  from this show ?thesis
    using rev_finite_subset by blast
qed

lemma partitions_imp_multiset:
  assumes "p partitions n"
  shows "p \<in> multiset"
using assms partitions_imp_finite_elements multiset_def by auto

lemma partitions_bounds:
  assumes "p partitions n"
  shows "p i \<le> n"
proof -
  from assms have index_bounds: "(\<forall>i. p i \<noteq> 0 \<longrightarrow> 1 \<le> i \<and> i \<le> n)"
    and sum: "(\<Sum>i\<le>n. p i * i) = n"
    unfolding partitions_def by auto
  show ?thesis
  proof (cases "1 \<le> i \<and> i \<le> n")
    case True
    from True have "{..n} = insert i {i'. i' \<le> n \<and> i' \<noteq> i}" by blast
    from sum[unfolded this] have "p i * i + (\<Sum>i\<in>{i'. i' \<le> n \<and> i' \<noteq> i}. p i * i) = n" by auto
    from this have "p i * i \<le> n" by linarith
    from this True show ?thesis using dual_order.trans by fastforce
  next
    case False
    from this index_bounds show ?thesis by fastforce
  qed
qed

lemma partitions_parts_bounded:
  assumes "p partitions n"
  shows "sum p {..n} \<le> n"
proof -
  {
    fix i
    assume "i \<le> n"
    from assms have "p i \<le> p i * i"
      by (auto elim!: partitionsE)
  }
  from this have "sum p {..n} \<le> (\<Sum>i\<le>n. p i * i)"
    by (auto intro: sum_mono)
  also from assms have n: "(\<Sum>i\<le>n. p i * i) = n"
    by (auto elim!: partitionsE)
  finally show ?thesis .
qed

lemma finite_partitions:
  "finite {p. p partitions n}"
proof -
  have "{p. p partitions n} \<subseteq> {f. (\<forall>i. f i \<le> n) \<and> (\<forall>i. n + 1 \<le> i \<longrightarrow> f i = 0)}"
    by (auto elim: partitions_bounds) (auto simp add: partitions_def)
  from this bound_domain_and_range_impl_finitely_many_functions[of n "n + 1"] show ?thesis
    by (simp add: finite_subset)
qed

lemma finite_partitions_k_parts:
  "finite {p. p partitions n \<and> sum p {..n} = k}"
by (simp add: finite_partitions)

lemma partitions_remaining_Max_part:
  assumes "p partitions n"
  assumes "0 < p k"
  shows "\<forall>i. n - k < i \<and> i \<noteq> k \<longrightarrow> p i = 0"
proof (clarify)
  fix i
  assume "n - k < i" "i \<noteq> k"
  show "p i = 0"
  proof (cases "i \<le> n")
    assume "i \<le> n"
    from assms have n: "(\<Sum>i\<le>n. p i * i) = n" and "k \<le> n"
      by (auto elim: partitionsE)
    have "(\<Sum>i\<le>n. p i * i) = p k * k + (\<Sum>i\<in>{..n}-{k}. p i * i)"
      using \<open>k \<le> n\<close> sum_atMost_remove_nat by blast
    also have "... = p i * i + p k * k + (\<Sum>i\<in>{..n}-{i, k}. p i * i)"
      using \<open>i \<le> n\<close> \<open>i \<noteq> k\<close>
      by (auto simp add: sum.remove[where x="i"]) (metis Diff_insert)
    finally have eq: "(\<Sum>i\<le>n. p i * i) = p i * i + p k * k + (\<Sum>i\<in>{..n} - {i, k}. p i * i)" .
    show "p i = 0"
    proof (rule ccontr)
      assume "p i \<noteq> 0"
      have upper_bound: "p i * i + p k * k \<le> n"
        using eq n by auto
      have lower_bound: "p i * i + p k * k > n"
        using \<open>n - k < i\<close> \<open>0 < p k\<close> \<open>k \<le> n\<close> \<open>p i \<noteq> 0\<close> mult_eq_if not_less by auto
      from upper_bound lower_bound show False by simp
    qed
  next
    assume "\<not> (i \<le> n)"
    from this show "p i = 0"
      using assms(1) by (auto elim: partitionsE)
  qed
qed

subsection \<open>Operations of Number Partitions\<close>

lemma partitions_remove1_bounds:
  assumes partitions: "p partitions n"
  assumes gr0: "0 < p k"
  assumes neq: "(p(k := p k - 1)) i \<noteq> 0"
  shows "1 \<le> i \<and> i \<le> n - k"
proof
    from partitions neq show "1 \<le> i"
      by (auto elim!: partitionsE split: if_split_asm)
next
  from partitions gr0 have n: "(\<Sum>i\<le>n. p i * i) = n" and "k \<le> n"
    by (auto elim: partitionsE)
  show "i \<le> n - k"
  proof cases
    assume "k \<le> n - k"
    from \<open>k \<le> n - k\<close> neq show ?thesis
      using  partitions_remaining_Max_part[OF partitions gr0] not_le by force
  next
    assume "\<not> k \<le> n - k"
    from this have "2 * k > n" by auto
    have "p k = 1"
    proof (rule ccontr)
      assume "p k \<noteq> 1"
      with gr0 have "p k \<ge> 2" by auto
      from this have "p k * k \<ge> 2 * k" by simp
      with \<open>2 * k > n\<close> have "p k * k > n" by linarith
      from \<open>k \<le> n\<close> this have "(\<Sum>i\<le>n. p i * i) > n"
        by (simp add: sum_atMost_remove_nat[of k])
      from this n show "False" by auto
    qed
    from neq this show ?thesis
      using partitions_remaining_Max_part[OF partitions gr0] leI
      by (auto split: if_split_asm) force
  qed
qed

lemma partitions_remove1:
  assumes partitions: "p partitions n"
  assumes gr0: "0 < p k"
  shows "p(k := p k - 1) partitions (n - k)"
proof (rule partitionsI)
  fix i
  assume "(p(k := p k - 1)) i \<noteq> 0"
  from this show "1 \<le> i \<and> i \<le> n - k" using partitions_remove1_bounds partitions gr0 by blast
next
  from partitions gr0 have "k \<le> n" by (auto elim: partitionsE)
  have "(\<Sum>i\<le>n - k. (p(k := p k - 1)) i * i) = (\<Sum>i\<le>n. (p(k := p k - 1)) i * i)"
    using partitions_remove1_bounds partitions gr0 by (auto intro!: sum.mono_neutral_left)
  also have "... = (p k - 1) * k + (\<Sum>i\<in>{..n} - {k}. (p(k := p k - 1)) i * i)"
    using \<open>k \<le> n\<close> by (simp add: sum_atMost_remove_nat[where k="k"])
  also have "... = p k * k + (\<Sum>i\<in>{..n} - {k}. p i * i) - k"
    using gr0 by (simp add: diff_mult_distrib)
  also have "... = (\<Sum>i\<le>n. p i * i) - k"
    using \<open>k \<le> n\<close> by (simp add: sum_atMost_remove_nat[of k])
  also from partitions have "... = n - k"
    by (auto elim: partitionsE)
  finally show "(\<Sum>i\<le>n - k. (p(k := p k - 1)) i * i) = n - k" .
qed

lemma partitions_insert1:
  assumes p: "p partitions n"
  assumes "k > 0"
  shows "(p(k := p k + 1)) partitions (n + k)"
proof (rule partitionsI)
  fix i
  assume "(p(k := p k + 1)) i \<noteq> 0"
  from p this \<open>k > 0\<close> show "1 \<le> i \<and> i \<le> n + k"
    by (auto elim!: partitionsE)
next
  have "(\<Sum>i\<le>n + k. (p(k := p k + 1)) i * i) = p k * k + (\<Sum>i\<in>{..n + k} - {k}. p i * i) + k"
    by (simp add: sum_atMost_remove_nat[of k])
  also have "... = p k * k + (\<Sum>i\<in>{..n} - {k}. p i * i) + k"
    using p by (auto intro!: sum.mono_neutral_right elim!: partitionsE)
  also have "... = (\<Sum>i\<le>n. p i * i) + k"
    using p by (cases "k \<le> n") (auto simp add: sum_atMost_remove_nat[of k] elim: partitionsE)
  also have "... = n + k"
    using p by (auto elim: partitionsE)
  finally show "(\<Sum>i\<le>n + k. (p(k := p k + 1)) i * i) = n + k" .
qed

lemma count_remove1:
  assumes "p partitions n"
  assumes "0 < p k"
  shows "(\<Sum>i\<le>n - k. (p(k := p k - 1)) i) = (\<Sum>i\<le>n. p i) - 1"
proof -
  have "k \<le> n" using assms by (auto elim: partitionsE)
  have "(\<Sum>i\<le>n - k. (p(k := p k - 1)) i) = (\<Sum>i\<le>n. (p(k := p k - 1)) i)"
    using partitions_remove1_bounds assms by (auto intro!: sum.mono_neutral_left)
  also have "(\<Sum>i\<le>n. (p(k := p k - 1)) i) = p k + (\<Sum>i\<in>{..n} - {k}. p i) - 1"
    using \<open>0 < p k\<close> \<open>k \<le> n\<close> by (simp add: sum_atMost_remove_nat[of k])
  also have "... = (\<Sum>i\<in>{..n}. p i) - 1"
    using \<open>k \<le> n\<close> by (simp add: sum_atMost_remove_nat[of k])
  finally show ?thesis .
qed

lemma count_insert1:
  assumes "p partitions n"
  shows "sum (p(k := p k + 1)) {..n + k} = (\<Sum>i\<le>n. p i) + 1"
proof -
  have "(\<Sum>i\<le>n + k. (p(k := p k + 1)) i) = p k + (\<Sum>i\<in>{..n + k} - {k}. p i) + 1"
    by (simp add: sum_atMost_remove_nat[of k])
  also have "... = p k + (\<Sum>i\<in>{..n} - {k}. p i) + 1"
    using assms by (auto intro!: sum.mono_neutral_right elim!: partitionsE)
  also have "... = (\<Sum>i\<le>n. p i) + 1"
    using assms by (cases "k \<le> n") (auto simp add: sum_atMost_remove_nat[of k] elim: partitionsE)
  finally show ?thesis .
qed

lemma partitions_decrease1:
  assumes p: "p partitions m"
  assumes sum: "sum p {..m} = k"
  assumes "p 1 = 0"
  shows "(\<lambda>i. p (i + 1)) partitions m - k"
proof -
  from p have "p 0 = 0" by (auto elim!: partitionsE)
  {
    fix i
    assume neq: "p (i + 1) \<noteq> 0"
    from p this \<open>p 1 = 0\<close> have "1 \<le> i"
      by (fastforce elim!: partitionsE simp add: le_Suc_eq)
    moreover have "i \<le> m - k"
    proof (rule ccontr)
      assume i_greater: "\<not> i \<le> m - k"
      from p have s: "(\<Sum>i\<le>m. p i * i) = m"
        by (auto elim!: partitionsE)
      from p sum have "k \<le> m"
        using partitions_parts_bounded by fastforce
      from neq p have "i + 1 \<le> m" by (auto elim!: partitionsE)
      from i_greater have "i > m - k" by simp
      have ineq1: "i + 1 > (m - k) + 1"
        using i_greater by simp
      have ineq21: "(\<Sum>j\<le>m. (p(i + 1 := p (i + 1) - 1)) j * j) \<ge> (\<Sum>j\<le>m. (p(i + 1 := p (i + 1) - 1)) j)"
        using \<open>p 0 = 0\<close> not_less by (fastforce intro!: sum_mono)
      have ineq22a: "(\<Sum>j\<le>m. (p(i + 1 := p (i + 1) - 1)) j) = (\<Sum>j\<le>m. p j) - 1"
        using \<open>i + 1 \<le> m\<close> neq by (simp add: sum.remove[where x="i + 1"])
      have ineq22: "(\<Sum>j\<le>m. (p(i + 1 := p (i + 1) - 1)) j) \<ge> k - 1"
        using sum neq ineq22a by auto
      have ineq2: "(\<Sum>j\<le>m. (p(i + 1 := p (i + 1) - 1)) j * j) \<ge> k - 1"
        using ineq21 ineq22 by auto
      have "(\<Sum>i\<le>m. p i * i) = p (i + 1) * (i + 1) + (\<Sum>i\<in>{..m} - {i + 1}. p i * i)"
        using \<open>i + 1 \<le> m\<close> neq
        by (subst sum.remove[where x="i + 1"]) auto
      also have "... = (i + 1) + (\<Sum>j\<le>m. (p(i + 1 := p (i + 1) - 1)) j * j)"
        using \<open>i + 1 \<le> m\<close> neq
        by (subst sum.remove[where x="i + 1" and g="\<lambda>j. (p(i + 1 := p (i + 1) - 1)) j * j"])
          (auto simp add: mult_eq_if)
      finally have "(\<Sum>i\<le>m. p i * i) = i + 1 + (\<Sum>j\<le>m. (p(i + 1 := p (i + 1) - 1)) j * j)" .
      moreover have "... > m" using ineq1 ineq2 \<open>k \<le> m\<close> \<open>p (i + 1) \<noteq> 0\<close> by linarith
      ultimately have "(\<Sum>i\<le>m. p i * i) > m" by simp
      from s this show False by simp
    qed
    ultimately have "1 \<le> i \<and> i \<le> m - k" ..
  } note bounds = this
  show "(\<lambda>i. p (i + 1)) partitions m - k"
  proof (rule partitionsI)
    fix i
    assume "p (i + 1) \<noteq> 0"
    from bounds this show "1 \<le> i \<and> i \<le> m - k" .
  next
    have geq: "\<forall>i. p i * i \<ge> p i"
      using \<open>p 0 = 0\<close> not_less by fastforce
    have "(\<Sum>i\<le>m - k. p (i + 1) * i) = (\<Sum>i\<le>m. p (i + 1) * i)"
      using bounds by (auto intro: sum.mono_neutral_left)
    also have "... = (\<Sum>i\<in>Suc ` {..m}. p i * (i - 1))"
      by (auto simp add: sum.reindex)
    also have "... = (\<Sum>i\<le>Suc m. p i * (i - 1))"
      using \<open>p 0 = 0\<close> by (simp add: atMost_Suc_eq_insert_0 zero_notin_Suc_image)
    also have "... = (\<Sum>i\<le>m. p i * (i - 1))"
      using p by (auto elim!: partitionsE)
    also have "... = (\<Sum>i\<le>m. p i * i - p i)"
      by (simp add: diff_mult_distrib2)
    also have "... = (\<Sum>i\<le>m. p i * i) - (\<Sum>i\<le>m. p i)"
      using geq by (simp only: sum_subtractf_nat)
    also have "... = m - k" using sum p by (auto elim!: partitionsE)
    finally show "(\<Sum>i\<le>m - k. p (i + 1) * i) = m - k" .
  qed
qed

lemma partitions_increase1:
  assumes partitions: "p partitions m - k"
  assumes k: "sum p {..m - k} = k"
  shows "(\<lambda>i. p (i - 1)) partitions m"
proof (rule partitionsI)
  fix i
  assume "p (i - 1) \<noteq> 0"
  from partitions this k show "1 \<le> i \<and> i \<le> m"
    by (cases k) (auto elim!: partitionsE)
next
  from k partitions have "k \<le> m"
    using linear partitions_zero by force
  have eq_0: "\<forall>i>m - k. p i = 0" using partitions by (auto elim!: partitionsE)
  from partitions have s: "(\<Sum>i\<le>m - k. p i * i) = m - k" by (auto elim!: partitionsE)
  have "(\<Sum>i\<le>m. p (i - 1) * i) = (\<Sum>i\<le>Suc m. p (i - 1) * i)"
    using partitions k by (cases k) (auto elim!: partitionsE)
  also have "(\<Sum>i\<le>Suc m. p (i - 1) * i) = (\<Sum>i\<le>m. p i * (i + 1))"
    by (subst sum.atMost_Suc_shift) simp
  also have "... = (\<Sum>i\<le>m - k. p i * (i + 1))"
    using eq_0 by (auto intro: sum.mono_neutral_right)
  also have "... = (\<Sum>i\<le>m - k. p i * i) + (\<Sum>i\<le>m - k. p i)" by (simp add: sum.distrib)
  also have "... = m - k + k" using s k by simp
  also have "... = m" using \<open>k \<le> m\<close> by simp
  finally show "(\<Sum>i\<le>m. p (i - 1) * i) = m" .
qed

lemma count_decrease1:
  assumes p: "p partitions m"
  assumes sum: "sum p {..m} = k"
  assumes "p 1 = 0"
  shows "sum (\<lambda>i. p (i + 1)) {..m - k} = k"
proof -
  from p have "p 0 = 0" by (auto elim!: partitionsE)
  have "sum (\<lambda>i. p (i + 1)) {..m - k} = sum (\<lambda>i. p (i + 1)) {..m}"
    using partitions_decrease1[OF assms]
    by (auto intro: sum.mono_neutral_left elim!: partitionsE)
  also have "\<dots> = sum (\<lambda>i. p (i + 1)) {0..m}" by (simp add: atLeast0AtMost)
  also have "\<dots> = sum (\<lambda>i. p i) {Suc 0.. Suc m}"
    by (simp only: One_nat_def add_Suc_right add_0_right sum.shift_bounds_cl_Suc_ivl)
  also have "\<dots> = sum (\<lambda>i. p i) {.. Suc m}"
    using \<open>p 0 = 0\<close> by (simp add: atLeast0AtMost sum_shift_lb_Suc0_0)
  also have "\<dots> = sum (\<lambda>i. p i) {.. m}"
    using p by (auto elim!: partitionsE)
  also have "\<dots> = k"
    using sum by simp
  finally show ?thesis .
qed

lemma count_increase1:
  assumes partitions: "p partitions m - k"
  assumes k: "sum p {..m - k} = k"
  shows "(\<Sum>i\<le>m. p (i - 1)) = k"
proof -
  have "p 0 = 0" using partitions by (auto elim!: partitionsE)
  have "(\<Sum>i\<le>m. p (i - 1)) = (\<Sum>i\<in>{1..m}. p (i - 1))"
    using \<open>p 0 = 0\<close> by (auto intro: sum.mono_neutral_cong_right)
  also have "(\<Sum>i\<in>{1..m}. p (i - 1)) = (\<Sum>i\<le>m - 1. p i)"
  proof (cases m)
    case 0
    from this show ?thesis using \<open>p 0 = 0\<close> by simp
  next
    case (Suc m')
    {
      fix x assume "Suc 0 \<le> x" "x \<le> m"
      from this Suc have "x \<in> Suc ` {..m'}"
        by (auto intro!: image_eqI[where x="x - 1"])
    }
    from this Suc show ?thesis
      by (intro sum.reindex_cong[of Suc]) auto
  qed
  also have "(\<Sum>i\<le>m - 1. p i) = (\<Sum>i\<le>m. p i)"
  proof -
    {
      fix i
      assume "0 < p i" "i \<le> m"
      from assms this have "i \<le> m - 1"
        using \<open>p 0 = 0\<close> partitions_increase1 by (cases k) (auto elim!: partitionsE)
    }
    from this show ?thesis
      by (auto intro: sum.mono_neutral_cong_left)
  qed
  also have "... = (\<Sum>i\<le>m - k. p i)"
    using partitions by (auto intro: sum.mono_neutral_right elim!: partitionsE)
  also have "... = k" using k by auto
  finally show ?thesis .
qed

subsection \<open>Number Partitions as Multisets on Natural Numbers\<close>

definition number_partition :: "nat \<Rightarrow> nat multiset \<Rightarrow> bool"
where
  "number_partition n N = (sum_mset N = n \<and> 0 \<notin># N)"

subsubsection \<open>Relationship to Definition on Functions\<close>

lemma count_partitions_iff:
  "count N partitions n \<longleftrightarrow> number_partition n N"
proof
  assume "count N partitions n"
  from this have "(\<forall>i. count N i \<noteq> 0 \<longrightarrow> 1 \<le> i \<and> i \<le> n)" "(\<Sum>i\<le>n. count N i * i) = n"
    unfolding Number_Partition.partitions_def by auto
  moreover from this have "set_mset N \<subseteq> {..n}" by auto
  moreover have "finite {..n}" by auto
  ultimately have "sum_mset N = n"
    using sum_mset_sum_count sum_mset_eq_sum_on_supersets by presburger
  moreover have "0 \<notin># N"
    using \<open>\<forall>i. count N i \<noteq> 0 \<longrightarrow> 1 \<le> i \<and> i \<le> n\<close> by auto
  ultimately show "number_partition n N"
    unfolding number_partition_def by auto
next
  assume "number_partition n N"
  from this have "sum_mset N = n" and "0 \<notin># N"
    unfolding number_partition_def by auto
  {
    fix i
    assume "count N i \<noteq> 0"
    have "1 \<le> i \<and> i \<le> n"
    proof
      from \<open>0 \<notin># N\<close> \<open>count N i \<noteq> 0\<close> show "1 \<le> i"
        using Suc_le_eq by auto
      from \<open>sum_mset N = n\<close> \<open>count N i \<noteq> 0\<close> show "i \<le> n"
        using multi_member_split by fastforce
    qed
  }
  moreover from \<open>sum_mset N = n\<close> have "(\<Sum>i\<le>n. count N i * i) = n"
    by (metis atMost_iff calculation finite_atMost not_in_iff subsetI sum_mset_eq_sum_on_supersets sum_mset_sum_count)
  ultimately show "count N partitions n"
    by (rule partitionsI) auto
qed

lemma partitions_iff_Abs_multiset:
  "p partitions n \<longleftrightarrow> finite {x. 0 < p x} \<and> number_partition n (Abs_multiset p)"
proof
  assume "p partitions n"
  from this have bounds: "(\<forall>i. p i \<noteq> 0 \<longrightarrow> 1 \<le> i \<and> i \<le> n)"
    and sum: "(\<Sum>i\<le>n. p i * i) = n"
  unfolding partitions_def by auto
  from \<open>p partitions n\<close> have "p \<in> multiset" by (rule partitions_imp_multiset)
  from \<open>p partitions n\<close> have "finite {x. 0 < p x}"
    by (rule partitions_imp_finite_elements)
  moreover from \<open>p \<in> multiset\<close> bounds have "\<not> 0 \<in># Abs_multiset p"
    using count_eq_zero_iff by force
  moreover from \<open>p \<in> multiset\<close> this sum have "sum_mset (Abs_multiset p) = n"
  proof -
    have "(\<Sum>i\<in>{x. 0 < p x}. p i * i) = (\<Sum>i\<le>n. p i * i)"
      using bounds by (auto intro: sum.mono_neutral_cong_left)
    from \<open>p \<in> multiset\<close> this sum show "sum_mset (Abs_multiset p) = n"
      by (simp add: sum_mset_sum_count set_mset_Abs_multiset)
  qed
  ultimately show "finite {x. 0 < p x} \<and> number_partition n (Abs_multiset p)"
    unfolding number_partition_def by auto
next
  assume "finite {x. 0 < p x} \<and> number_partition n (Abs_multiset p)"
  from this have "finite {x. 0 < p x}" "0 \<notin># Abs_multiset p" "sum_mset (Abs_multiset p) = n"
    unfolding number_partition_def by auto
  from \<open>finite {x. 0 < p x}\<close> have "p \<in> multiset" by (simp add: multiset_def)
  from \<open>p \<in> multiset\<close> have "(\<Sum>i\<in>{x. 0 < p x}. p i * i) = n"
    using \<open> sum_mset (Abs_multiset p) = n\<close>
    by (simp add: sum_mset_sum_count set_mset_Abs_multiset)
  have bounds: "\<And>i. p i \<noteq> 0 \<Longrightarrow> 1 \<le> i \<and> i \<le> n"
  proof
    fix i
    assume "p i \<noteq> 0"
    from \<open>\<not> 0 \<in># Abs_multiset p\<close> \<open>p \<in> multiset\<close> have "p 0 = 0"
      using count_inI by force
    from this \<open>p i \<noteq> 0\<close> show "1 \<le> i"
      by (metis One_nat_def leI less_Suc0)
    show "i \<le> n"
    proof (rule ccontr)
      assume "\<not> i \<le> n"
      from this have "i > n"
        using le_less_linear by blast
      from this \<open>p i \<noteq> 0\<close> have "p i * i > n"
        by (auto simp add: less_le_trans)
      from \<open>p i \<noteq> 0\<close> have "(\<Sum>i\<in>{x. 0 < p x}. p i * i) = p i * i + (\<Sum>i\<in>{x. 0 < p x} - {i}. p i * i)"
        using \<open>finite {x. 0 < p x}\<close>
        by (subst sum.insert_remove[symmetric]) (auto simp add: insert_absorb)
      also from \<open>p i * i > n\<close> have "\<dots> > n" by auto
      finally show False using \<open>(\<Sum>i\<in>{x. 0 < p x}. p i * i) = n\<close> by blast
    qed
  qed
  moreover have "(\<Sum>i\<le>n. p i * i) = n"
  proof -
    have "(\<Sum>i\<le>n. p i * i) = (\<Sum>i\<in>{x. 0 < p x}. p i * i)"
      using bounds by (auto intro: sum.mono_neutral_cong_right)
    from this show ?thesis
      using \<open>(\<Sum>i\<in>{x. 0 < p x}. p i * i) = n\<close> by simp
  qed
  ultimately show "p partitions n" by (auto intro: partitionsI)
qed


lemma size_nat_multiset_eq:
  fixes N :: "nat multiset"
  assumes "number_partition n N"
  shows "size N = sum (count N) {..n}"
proof -
  have "set_mset N \<subseteq> {..sum_mset N}"
    by (auto dest: multi_member_split)
  have "size N = sum (count N) (set_mset N)"
    by (rule size_multiset_overloaded_eq)
  also have "\<dots> = sum (count N) {..sum_mset N}"
    using \<open>set_mset N \<subseteq> {..sum_mset N}\<close>
    by (auto intro: sum.mono_neutral_cong_left count_inI)
  finally show ?thesis
    using \<open>number_partition n N\<close>
    unfolding number_partition_def by auto
qed

end
