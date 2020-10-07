(* Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com>
   Dedicated to Sandra H. for a wonderful relaxing summer
*)

section \<open>Euler's Partition Theorem\<close>

theory Euler_Partition
imports
  Main
  Card_Number_Partitions.Number_Partition
begin

subsection \<open>Preliminaries\<close>

subsubsection \<open>Additions to Divides Theory\<close>

lemma power_div_nat:
  assumes "c \<le> b"
  assumes "a > 0"
  shows  "(a :: nat) ^ b div a ^ c = a ^ (b - c)"
by (metis assms nonzero_mult_div_cancel_right le_add_diff_inverse2 less_not_refl2 power_add power_not_zero)

subsubsection \<open>Additions to Groups-Big Theory\<close>

lemma sum_div:
  assumes "finite A"
  assumes "\<And>a. a \<in> A \<Longrightarrow> (b::'b::euclidean_semiring) dvd f a"
  shows "(\<Sum>a\<in>A. f a) div b = (\<Sum>a\<in>A. (f a) div b)"
using assms
proof (induct)
  case insert from this show ?case by auto (subst div_add; auto intro!: dvd_sum)
qed (auto)

lemma sum_mod:
  assumes "finite A"
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a mod b = (0::'b::unique_euclidean_semiring)"
  shows "(\<Sum>a\<in>A. f a) mod b = 0"
using assms by induct (auto simp add: mod_add_eq [symmetric])

subsubsection \<open>Additions to Set-Interval Theory\<close>

lemma geometric_sum_2nat:
  "(\<Sum>i<n. (2::nat) ^ i) = (2 ^ n - 1)"
by (induct n) auto

subsubsection \<open>Additions to Nat Theory or Power Theory\<close>

lemma n_leq_2_pow_n:
  "n \<le> 2 ^ n"
proof (induct n)
  case (Suc n)
  from this have approx: "2 * n \<le> 2 ^ Suc n" by auto
  show ?case
  proof (cases n)
    case 0
    from this show ?thesis by simp
  next
    case Suc
    from this show ?thesis by (intro le_trans[OF _ approx]) simp
  qed
qed (simp)

subsubsection \<open>Additions to Finite-Set Theory\<close>

lemma finite_exponents:
  "finite {i. 2 ^ i \<le> (n::nat)}"
proof -
  have "{i::nat. 2 ^ i \<le> n} \<subseteq> {..n}"
    using dual_order.trans n_leq_2_pow_n by auto
  from this show ?thesis by (simp add: finite_subset)
qed

subsection \<open>Binary Encoding of Natural Numbers\<close>

definition bitset :: "nat \<Rightarrow> nat set"
where
  "bitset n = {i. odd (n div (2 ^ i))}"

lemma in_bitset_bound:
  "b \<in> bitset n \<Longrightarrow> 2 ^ b \<le> n"
unfolding bitset_def using not_less by fastforce

lemma in_bitset_bound_weak:
  "b \<in> bitset n \<Longrightarrow> b \<le> n"
by (auto dest: in_bitset_bound intro: le_trans n_leq_2_pow_n)

lemma finite_bitset:
  "finite (bitset n)"
proof -
  have "bitset n \<subseteq> {..n}" by (auto dest: in_bitset_bound_weak)
  from this show ?thesis using finite_subset by auto
qed

lemma bitset_0:
  "bitset 0 = {}"
unfolding bitset_def by auto

lemma binary_induct [case_names zero even odd]:
  assumes "P (0 :: nat)"
  assumes "\<And>n. P n \<Longrightarrow> P (2 * n)"
  assumes "\<And>n. P n \<Longrightarrow> P (2 * n + 1)"
  shows "\<And>n. P n"
using assms parity_induct by auto

lemma bitset_2n: "bitset (2 * n) = Suc ` (bitset n)"
proof (rule set_eqI)
  fix x
  show "(x \<in> bitset (2 * n)) = (x \<in> Suc ` bitset n)"
    unfolding bitset_def by (cases x) auto
qed

lemma bitset_Suc:
  assumes "even n"
  shows "bitset (n + 1) = insert 0 (bitset n)"
proof (rule set_eqI)
  fix x
  from assms show "(x \<in> bitset (n + 1)) = (x \<in> insert 0 (bitset n))"
    unfolding bitset_def by (cases x) (auto simp add: Divides.div_mult2_eq)
qed

lemma bitset_2n1:
  "bitset (2 * n + 1) = insert 0 (Suc ` (bitset n))"
by (subst bitset_Suc) (auto simp add: bitset_2n)

lemma sum_bitset:
  "(\<Sum>i\<in>bitset n. 2 ^ i) = n"
proof (induct rule: binary_induct)
  case zero
  show ?case by (auto simp add: bitset_0)
next
  case (even n)
  from this show ?case
    by (simp add: bitset_2n sum.reindex sum_distrib_left[symmetric])
next
  case (odd n)
  have "(\<Sum>i\<in>bitset (2 * n + 1). 2 ^ i) = (\<Sum>i\<in>insert 0 (Suc ` bitset n). 2 ^ i)"
    by (simp only: bitset_2n1)
  also have "... = 2 ^ 0 + (\<Sum>i\<in>Suc ` bitset n. 2 ^ i)"
    by (subst sum.insert) (auto simp add: finite_bitset)
  also have "... = 2 * n + 1"
    using odd by (simp add: sum.reindex sum_distrib_left[symmetric])
  finally show ?case .
qed

lemma binarysum_div:
  assumes "finite B"
  shows "(\<Sum>i\<in>B. (2::nat) ^ i) div 2 ^ j = (\<Sum>i\<in>B. if i < j then 0 else 2 ^ (i - j))"
  (is "_ = (\<Sum>i\<in>_. ?f i)")
proof -
  have split_B: "B = {i\<in>B. i < j} \<union> {i\<in>B. j \<le> i}" by auto
  have bound: "(\<Sum>i | i \<in> B \<and> i < j. (2::nat) ^ i) < 2 ^ j"
  proof (rule order.strict_trans1)
    show "(\<Sum>i | i \<in> B \<and> i < j. (2::nat) ^ i) \<le> (\<Sum>i<j. 2 ^ i)" by (auto intro: sum_mono2)
    show "... < 2 ^ j" by (simp add: geometric_sum_2nat)
  qed
  from this have zero: "(\<Sum>i | i \<in> B \<and> i < j. (2::nat) ^ i) div (2 ^ j) = 0" by (elim div_less)
  from assms have mod0: "(\<Sum>i | i \<in> B \<and> j \<le> i. (2::nat) ^ i) mod 2 ^ j = 0"
    by (auto intro!: sum_mod simp add: le_imp_power_dvd)
  from assms have "(\<Sum>i\<in>B. (2::nat) ^ i) div (2 ^ j) = ((\<Sum>i | i \<in> B \<and> i < j. 2 ^ i) + (\<Sum>i | i \<in> B \<and> j \<le> i. 2 ^ i)) div 2 ^ j"
    by (subst sum.union_disjoint[symmetric]) (auto simp add: split_B[symmetric])
  also have "... = (\<Sum>i | i \<in> B \<and> j \<le> i. 2 ^ i) div 2 ^ j"
    by (simp add: div_add1_eq zero mod0)
  also have "... = (\<Sum>i | i \<in> B \<and> j \<le> i. 2 ^ i div 2 ^ j)"
    using assms by (subst sum_div) (auto simp add: sum_div le_imp_power_dvd)
  also have "... = (\<Sum>i | i \<in> B \<and> j \<le> i. 2 ^ (i - j))"
    by (rule sum.cong[OF refl]) (auto simp add: power_div_nat)
  also have "... = (\<Sum>i\<in>B. ?f i)"
    using assms by (subst split_B; subst sum.union_disjoint) auto
  finally show ?thesis .
qed

lemma odd_iff:
  assumes "finite B"
  shows "odd (\<Sum>i\<in>B. if i < x then (0::nat) else 2 ^ (i - x)) = (x \<in> B)" (is "odd (\<Sum>i\<in>_. ?s i) = _")
proof -
  from assms have even: "even (\<Sum>i\<in>B - {x}. ?s i)"
    by (subst dvd_sum) auto
  show ?thesis
  proof
    assume "odd (\<Sum>i\<in>B. ?s i)"
    from this even show "x \<in> B" by (cases "x \<in> B") auto
  next
    assume "x \<in> B"
    from assms this have "(\<Sum>i\<in>B. ?s i) = 1 + (\<Sum>i\<in>B-{x}. ?s i)"
      by (auto simp add: sum.remove)
    from assms this even show "odd (\<Sum>i\<in>B. ?s i)" by auto
  qed
qed

lemma bitset_sum:
  assumes "finite B"
  shows "bitset (\<Sum>i\<in>B. 2 ^ i) = B"
using assms unfolding bitset_def by (simp add: binarysum_div odd_iff)

subsection \<open>Decomposition of a Number into a Power of Two and an Odd Number\<close>

function (sequential) index :: "nat \<Rightarrow> nat"
where
  "index 0 = 0"
| "index n = (if odd n then 0 else Suc (index (n div 2)))"
by (pat_completeness) auto

termination
proof
  show "wf {(x::nat, y). x < y}" by (simp add: wf)
next
  fix n show "(Suc n div 2, Suc n) \<in> {(x, y). x < y}" by simp
qed

function (sequential) oddpart :: "nat \<Rightarrow> nat"
where
  "oddpart 0 = 0"
| "oddpart n = (if odd n then n else oddpart (n div 2))"
by pat_completeness auto

termination
proof
  show "wf {(x::nat, y). x < y}" by (simp add: wf)
next
  fix n show "(Suc n div 2, Suc n) \<in> {(x, y). x < y}" by simp
qed

lemma odd_oddpart:
  "odd (oddpart n) \<longleftrightarrow> n \<noteq> 0"
by (induct n rule: index.induct) auto

lemma index_oddpart_decomposition:
  "n = 2 ^ (index n) * oddpart n"
proof (induct n rule: index.induct)
  case (2 n)
  from this show "Suc n = 2 ^ index (Suc n) * oddpart (Suc n)"
    by (simp add: mult.assoc)
qed (simp)

lemma oddpart_leq:
  "oddpart n \<le> n"
by (induct n rule: index.induct) (simp, metis div_le_dividend le_Suc_eq le_trans oddpart.simps(2))

lemma index_oddpart_unique:
  assumes "odd (m :: nat)" "odd m'"
  shows "(2 ^ i * m = 2 ^ i' * m') \<longleftrightarrow> (i = i' \<and> m = m')"
proof (induct i arbitrary: i')
  case 0
  from assms show ?case by auto
next
  case (Suc _ i')
  from assms this show ?case by (cases i') auto
qed

lemma index_oddpart:
  assumes "odd m"
  shows "index (2 ^ i * m) = i" "oddpart (2 ^ i * m) = m"
using index_oddpart_unique[where i=i and m=m and m'="oddpart (2 ^ i * m)" and i'="index (2 ^ i * m)"]
  assms odd_oddpart index_oddpart_decomposition by force+

subsection \<open>Partitions With Only Distinct and Only Odd Parts\<close>

definition odd_of_distinct :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where
  "odd_of_distinct p = (\<lambda>i. if odd i then (\<Sum>j | p (2 ^ j * i) = 1. 2 ^ j) else 0)"

definition distinct_of_odd :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where
  "distinct_of_odd p = (\<lambda>i. if index i \<in> bitset (p (oddpart i)) then 1 else 0)"

lemma odd:
  "odd_of_distinct p i \<noteq> 0 \<Longrightarrow> odd i"
unfolding odd_of_distinct_def by auto

lemma distinct_distinct_of_odd:
  "distinct_of_odd p i \<le> 1"
unfolding distinct_of_odd_def by auto

lemma odd_of_distinct:
  assumes "odd_of_distinct p i \<noteq> 0"
  assumes "\<And>i. p i \<noteq> 0 \<Longrightarrow> i \<le> n"
  shows "1 \<le> i \<and> i \<le> n"
proof
  from assms(1) odd have "odd i"
    by simp
  then show "1 \<le> i"
    by (auto elim: oddE)
next
  from assms(1) obtain j where "p (2 ^ j * i) > 0"
    by (auto simp add: odd_of_distinct_def split: if_splits) fastforce
  with assms(2) have "i \<le> 2 ^ j * i" "2 ^ j * i \<le> n"
    by simp_all
  then show "i \<le> n"
    by (rule order_trans)
qed

lemma distinct_of_odd:
  assumes "\<And>i. p i * i \<le> n" "\<And>i. p i \<noteq> 0 \<Longrightarrow> odd i"
  assumes "distinct_of_odd p i \<noteq> 0"
  shows "1 \<le> i \<and> i \<le> n"
proof
  from assms(3) have index: "index i \<in> bitset (p (oddpart i))"
    unfolding distinct_of_odd_def by (auto split: if_split_asm)
  have "i \<noteq> 0"
  proof
    assume zero: "i = 0"
    from assms(2) have "p 0 = 0" by auto
    from index zero this show "False" by (auto simp add: bitset_0)
  qed
  from this show "1 \<le> i" by auto
  from assms(1) have leq_n: "p (oddpart i) * oddpart i \<le> n" by auto
  from index have "2 ^ index i \<le> p (oddpart i)" by (rule in_bitset_bound)
  from this leq_n show "i \<le> n"
    by (subst index_oddpart_decomposition[of i]) (meson dual_order.trans eq_imp_le mult_le_mono)
qed

lemma odd_distinct:
  assumes "\<And>i. p i \<noteq> 0 \<Longrightarrow> odd i"
  shows "odd_of_distinct (distinct_of_odd p) = p"
using assms unfolding odd_of_distinct_def distinct_of_odd_def
by (auto simp add: fun_eq_iff index_oddpart sum_bitset)

lemma distinct_odd:
  assumes "\<And>i. p i \<noteq> 0 \<Longrightarrow> 1 \<le> i \<and> i \<le> n" "\<And>i. p i \<le> 1"
  shows "distinct_of_odd (odd_of_distinct p) = p"
proof -
  from assms have "{i. p i = 1} \<subseteq> {..n}" by auto
  from this have finite: "finite {i. p i = 1}" by (simp add: finite_subset)
  have "\<And>x j. x > 0 \<Longrightarrow> p (2 ^ j * oddpart x) = 1 \<Longrightarrow>
    index (2 ^ j * oddpart x) \<in> index ` {i. p i = 1 \<and> oddpart x = oddpart i}"
    by (rule imageI) (auto intro: imageI simp add: index_oddpart odd_oddpart)
  from this have eq: "\<And>x. x > 0 \<Longrightarrow> {j. p (2 ^ j * oddpart x) = 1} = index ` {i. p i = 1 \<and> oddpart x = oddpart i}"
    by (auto simp add: index_oddpart odd_oddpart index_oddpart_decomposition[symmetric])
  from finite have all_finite: "\<And>x. x > 0 \<Longrightarrow> finite {j. p (2 ^ j * oddpart x) = 1}"
    unfolding eq by auto
  show ?thesis
  proof
    fix x
    from assms(1) have p0: "p 0 = 0" by auto
    show "distinct_of_odd (odd_of_distinct p) x = p x"
    proof (cases "x > 0")
      case False
      from this p0 show ?thesis
        unfolding odd_of_distinct_def distinct_of_odd_def
        by (auto simp add: odd_oddpart bitset_0)
    next
      case True
      from p0 assms(2)[of x] all_finite[OF True] show ?thesis
        unfolding odd_of_distinct_def distinct_of_odd_def
        by (auto simp add: odd_oddpart bitset_0 bitset_sum index_oddpart_decomposition[symmetric])
    qed
  qed
qed

lemma sum_distinct_of_odd:
  assumes "\<And>i. p i \<noteq> 0 \<Longrightarrow> 1 \<le> i \<and> i \<le> n"
  assumes "\<And>i. p i * i \<le> n"
  assumes "\<And>i. p i \<noteq> 0 \<Longrightarrow> odd i"
  shows "(\<Sum>i\<le>n. distinct_of_odd p i * i) = (\<Sum>i\<le>n. p i * i)"
proof -
  {
    fix m
    assume odd: "odd (m :: nat)"
    have finite: "finite {k. 2 ^ k * m \<le> n \<and> k \<in> bitset (p m)}" by (simp add: finite_bitset)
    have "(\<Sum>i | \<exists>k. i = 2 ^ k * m \<and> i \<le> n. distinct_of_odd p i * i) =
      (\<Sum>i | \<exists>k. i = 2 ^ k * m \<and> i \<le> n. if index i \<in> bitset (p (oddpart i)) then i else 0)"
      unfolding distinct_of_odd_def by (auto intro: sum.cong)
    also have "... = (\<Sum>i | \<exists>k. i = 2 ^ k * m \<and> k \<in> bitset (p m) \<and> i \<le> n. i)"
      using odd by (intro sum.mono_neutral_cong_right) (auto simp add: index_oddpart)
    also have "... = (\<Sum>k | 2 ^ k * m \<le> n \<and> k \<in> bitset (p m). 2 ^ k * m)"
      using odd by (auto intro!: sum.reindex_cong[OF _ _ refl] inj_onI)
    also have "... = (\<Sum>k\<in>bitset (p m). 2 ^ k * m)"
      using assms(2)[of m] finite dual_order.trans in_bitset_bound
      by (fastforce intro!: sum.mono_neutral_cong_right)
    also have "... = (\<Sum>k\<in>bitset (p m). 2 ^ k) * m"
      by (subst sum_distrib_right) auto
    also have "... = p m * m"
      by (auto simp add: sum_bitset)
    finally have "(\<Sum>i | \<exists>k. i = 2 ^ k * m \<and> i \<le> n. distinct_of_odd p i * i) = p m * m" .
  } note inner_eq = this

  have set_eq: "{i. 1 \<le> i \<and> i \<le> n} = \<Union>((\<lambda>m. {i. \<exists>k. i = (2 ^ k) * m \<and> i \<le> n}) ` {m. m \<le> n \<and> odd m})"
  proof -
    {
      fix x
      assume "1 \<le> x" "x \<le> n"
      from this oddpart_leq[of x] have "oddpart x \<le> n \<and> odd (oddpart x) \<and> (\<exists>k. 2 ^ index x * oddpart x = 2 ^ k * oddpart x)"
        by (auto simp add: odd_oddpart)
      from this have "\<exists>m\<le>n. odd m \<and> (\<exists>k. x = 2 ^ k * m)"
        by (auto simp add: index_oddpart_decomposition[symmetric])
    }
    from this show ?thesis by (auto simp add: Suc_leI odd_pos)
  qed
  let ?S = "(\<lambda>m. {i. \<exists>k. i = 2 ^ k * m \<and> i \<le> n}) ` {m. m \<le> n \<and> odd m}"
  have no_overlap: "\<forall>A\<in>?S. \<forall>B\<in>?S. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
    by (auto simp add: index_oddpart_unique)
  have inj: "inj_on (\<lambda>m. {i. (\<exists>k. i = 2 ^ k * m) \<and> i \<le> n}) {m. m \<le> n \<and> odd m}"
    unfolding inj_on_def by auto (force simp add: index_oddpart_unique)
  have reindex: "\<And>F. (\<Sum>i | 1 \<le> i \<and> i \<le> n. F i) = (\<Sum>m | m \<le> n \<and> odd m. (\<Sum>i | \<exists>k. i = 2 ^ k * m \<and> i \<le> n. F i))"
    unfolding set_eq by (subst sum.Union_disjoint) (auto simp add: no_overlap intro: sum.reindex_cong[OF inj])
  have "(\<Sum>i\<le>n. distinct_of_odd p i * i) =  (\<Sum>i | 1 \<le> i \<and> i \<le> n. distinct_of_odd p i * i)"
    by (auto intro: sum.mono_neutral_right)
  also have "... = (\<Sum>m | m \<le> n \<and> odd m. \<Sum>i | \<exists>k. i = 2 ^ k * m \<and> i \<le> n. distinct_of_odd p i * i)"
    by (simp only: reindex)
  also have "... = (\<Sum>i | i \<le> n \<and> odd i. p i * i)"
    by (rule sum.cong[OF refl]; subst inner_eq) auto
  also have "... = (\<Sum>i\<le>n. p i * i)"
    using assms(3) by (auto intro: sum.mono_neutral_left)
  finally show ?thesis .
qed

lemma leq_n:
  assumes "\<forall>i. 0 < p i \<longrightarrow> 1 \<le> i \<and> i \<le> (n::nat)"
  assumes "(\<Sum>i\<le>n. p i * i) = n"
  shows "p i * i \<le> n"
proof (rule ccontr)
  assume "\<not> p i * i \<le> n"
  from this have gr_n: "p i * i > n" by auto
  from this assms(1) have "1 \<le> i \<and> i \<le> n" by force
  from this have "(\<Sum>j\<le>n. p j * j) = p i * i + (\<Sum>j | j \<le> n \<and> j \<noteq> i. p j * j)"
    by (subst sum.insert[symmetric]) (auto intro: sum.cong simp del: sum.insert)
  from this gr_n assms(2) show False by simp
qed

lemma distinct_of_odd_in_distinct_partitions:
  assumes "p \<in> {p. p partitions n \<and> (\<forall>i. p i \<noteq> 0 \<longrightarrow> odd i)}"
  shows "distinct_of_odd p \<in> {p. p partitions n \<and> (\<forall>i. p i \<le> 1)}"
proof
  have "distinct_of_odd p partitions n"
  proof (rule partitionsI)
    fix i assume "distinct_of_odd p i \<noteq> 0"
    from this assms show "1 \<le> i \<and> i \<le> n"
    unfolding partitions_def
    by (rule_tac distinct_of_odd) (auto simp add: leq_n)
  next
    from assms show "(\<Sum>i\<le>n. distinct_of_odd p i * i) = n"
      by (subst  sum_distinct_of_odd) (auto simp add: distinct_distinct_of_odd leq_n elim: partitionsE)
  qed
  moreover have "\<forall>i. distinct_of_odd p i \<le> 1"
    by (intro allI distinct_distinct_of_odd)
  ultimately show "distinct_of_odd p partitions n \<and> (\<forall>i. distinct_of_odd p i \<le> 1)" by simp
qed

lemma odd_of_distinct_in_odd_partitions:
  assumes "p \<in> {p. p partitions n \<and> (\<forall>i. p i \<le> 1)}"
  shows "odd_of_distinct p \<in> {p. p partitions n \<and> (\<forall>i. p i \<noteq> 0 \<longrightarrow> odd i)}"
proof
  from assms have distinct: "\<And>i. p i = 0 \<or> p i = 1"
    using le_imp_less_Suc less_Suc_eq_0_disj by fastforce
  from assms have set_eq: "{x. p x = 1} = {x \<in> {..n}. p x = 1}"
     unfolding partitions_def by auto
  from assms have sum: "(\<Sum>i\<le>n. p i * i) = n"
     unfolding partitions_def by auto
  {
    fix i
    assume i: "odd (i :: nat)"
    have 3: "inj_on index {x. p x = 1 \<and> oddpart x = i}"
      unfolding inj_on_def by auto (metis index_oddpart_decomposition)
    {
      fix j assume "p (2 ^ j * i) = 1"
      from this i have "j \<in> index ` {x. p x = 1 \<and> oddpart x = i}"
        by (auto simp add: index_oddpart(1, 2) intro!: image_eqI[where x="2 ^ j * i"])
    }
    from i this have "{j. p (2 ^ j * i) = 1} = index ` {x. p x = 1 \<and> oddpart x = i}"
      by (auto simp add: index_oddpart_decomposition[symmetric])
    from 3 this have "(\<Sum>j | p (2 ^ j * i) = 1. 2 ^ j) * i = (\<Sum>x | p x = 1 \<and> oddpart x = i. 2 ^ index x) * i"
      by (auto intro: sum.reindex_cong[where l = "index"])
    also have "... = (\<Sum>x | p x = 1 \<and> oddpart x = i. 2 ^ index x * oddpart x)"
      by (auto simp add: sum_distrib_right)
    also have "... = (\<Sum>x | p x = 1 \<and> oddpart x = i. x)"
       by (simp only: index_oddpart_decomposition[symmetric])
    also have "... \<le> (\<Sum>x | p x = 1. x)"
      using set_eq by (intro sum_mono2) auto
    also have "... = (\<Sum>x\<le>n. p x * x)"
      using distinct by (subst set_eq) (force intro!: sum.mono_neutral_cong_left)
    also have "... = n" using sum .
    finally have "(\<Sum>j | p (2 ^ j * i) = 1. 2 ^ j) * i \<le> n" .
  }
  from this have less_n: "\<And>i. odd_of_distinct p i * i \<le> n"
    unfolding odd_of_distinct_def by auto
  have "odd_of_distinct p partitions n"
  proof (rule partitionsI)
    fix i assume "odd_of_distinct p i \<noteq> 0"
    from this assms show "1 \<le> i \<and> i \<le> n"
      by (elim CollectE conjE partitionsE odd_of_distinct) auto
  next
    have "(\<Sum>i\<le>n. odd_of_distinct p i * i) = (\<Sum>i\<le>n. distinct_of_odd (odd_of_distinct p) i * i)"
      using assms less_n by (subst sum_distinct_of_odd) (auto elim!: partitionsE odd_of_distinct simp only: odd)
    also have "... = (\<Sum>i\<le>n. p i * i)" using assms
      by (auto elim!: partitionsE simp only:) (subst distinct_odd, auto)
    also with assms have "... = n" by (auto elim: partitionsE)
    finally show "(\<Sum>i\<le>n. odd_of_distinct p i * i) = n" .
  qed
  moreover have "\<forall>i. odd_of_distinct p i \<noteq> 0 \<longrightarrow> odd i"
    by (intro allI impI odd)
  ultimately show "odd_of_distinct p partitions n \<and> (\<forall>i. odd_of_distinct p i \<noteq> 0 \<longrightarrow> odd i)" by simp
qed

subsection \<open>Euler's Partition Theorem\<close>

theorem Euler_partition_theorem:
  "card {p. p partitions n \<and> (\<forall>i. p i \<le> 1)} = card {p. p partitions n \<and> (\<forall>i. p i \<noteq> 0 \<longrightarrow> odd i)}"
  (is "card ?distinct_partitions = card ?odd_partitions")
proof (rule card_bij_eq)
  from odd_of_distinct_in_odd_partitions show
    "odd_of_distinct ` ?distinct_partitions \<subseteq> ?odd_partitions" by auto
  moreover from distinct_of_odd_in_distinct_partitions show
    "distinct_of_odd ` ?odd_partitions \<subseteq> ?distinct_partitions" by auto
  moreover have "\<forall>p\<in>?distinct_partitions. distinct_of_odd (odd_of_distinct p) = p"
    by auto (subst distinct_odd; auto simp add: partitions_def)
  moreover have "\<forall>p\<in>?odd_partitions. odd_of_distinct (distinct_of_odd p) = p"
    by auto (subst odd_distinct; auto simp add: partitions_def)
  ultimately show "inj_on odd_of_distinct ?distinct_partitions"
    "inj_on distinct_of_odd ?odd_partitions"
    by (intro bij_betw_imp_inj_on bij_betw_byWitness; auto)+
  show "finite ?distinct_partitions" "finite ?odd_partitions"
    by (simp add: finite_partitions)+
qed

end
