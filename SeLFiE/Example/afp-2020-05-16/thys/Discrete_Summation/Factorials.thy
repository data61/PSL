
(* Authors: Amine Chaieb & Florian Haftmann, TU Muenchen with contributions by Lukas Bulwahn *)

section \<open>Falling factorials\<close>

theory Factorials
  imports Complex_Main "HOL-Library.Stirling"
begin

lemma pochhammer_0 [simp]: \<comment> \<open>TODO move\<close>
  "pochhammer 0 n = (0::nat)" if "n > 0"
  using that by (simp add: pochhammer_prod)

definition ffact :: "nat \<Rightarrow> 'a::comm_semiring_1_cancel \<Rightarrow> 'a"
  where "ffact n a = pochhammer (a + 1 - of_nat n) n"

lemma ffact_0 [simp]:
  "ffact 0 = (\<lambda>x. 1)"
  by (simp add: fun_eq_iff ffact_def)

lemma ffact_Suc:
  "ffact (Suc n) a = a * ffact n (a - 1)"
    for a :: "'a :: comm_ring_1"
  by (simp add: ffact_def pochhammer_prod prod.atLeast0_lessThan_Suc algebra_simps)

(* TODO: what's the right class here? *)
lemma ffact_Suc_rev:
  "ffact (Suc n) m = (m - of_nat n) * ffact n m"
    for m :: "'a :: {comm_semiring_1_cancel, ab_group_add}"
unfolding ffact_def pochhammer_rec by (simp add: diff_add_eq)

lemma ffact_nat_triv:
  "ffact n m = 0" if "m < n"
  using that by (simp add: ffact_def)

lemma ffact_Suc_nat:
  "ffact (Suc n) m = m * ffact n (m - 1)"
    for m :: nat
proof (cases "n \<le> m")
  case True
  then show ?thesis
    by (simp add: ffact_def pochhammer_prod algebra_simps prod.atLeast0_lessThan_Suc)
next
  case False
  then have "m < n"
    by simp
  then show ?thesis
    by (simp add: ffact_nat_triv)
qed

lemma ffact_Suc_rev_nat:
  "ffact (Suc n) m = (m - n) * ffact n m"
proof (cases "n \<le> m")
  case True
  then show ?thesis
    by (simp add: ffact_def pochhammer_rec Suc_diff_le)
next
  case False
  then have "m < n" by simp
  then show ?thesis by (simp add: ffact_nat_triv)
qed

lemma fact_div_fact_ffact:
  "fact n div fact m = ffact (n - m) n" if "m \<le> n"
proof -
  from that have "fact n = ffact (n - m) n * fact m"
    by (simp add: ffact_def pochhammer_product pochhammer_fact)
  moreover have "fact m dvd (fact n :: nat)"
    using that by (rule fact_dvd)
  ultimately show ?thesis
    by simp
qed

lemma fact_div_fact_ffact_nat:
  "fact n div fact (n - k) = ffact k n" if "k \<le> n"
using that by (simp add: fact_div_fact_ffact)

lemma ffact_fact:
  "ffact n (of_nat n) = (of_nat (fact n) :: 'a :: comm_ring_1)"
  by (induct n) (simp_all add: algebra_simps ffact_Suc)

lemma ffact_add_diff_assoc:
  "(a - of_nat n) * ffact n a + of_nat n * ffact n a = a * ffact n a"
    for a :: "'a :: comm_ring_1"
  by (simp add: algebra_simps)

lemma mult_ffact:
  "a * ffact n a = ffact (Suc n) a + of_nat n * ffact n a"
    for a :: "'a :: comm_ring_1"
proof -
  have "ffact (Suc n) a + of_nat n * (ffact n a) = (a - of_nat n) * (ffact n a) + of_nat n * (ffact n a)"
    using ffact_Suc_rev [of n] by auto
  also have "\<dots> = a * ffact n a" using ffact_add_diff_assoc by (simp add: algebra_simps)
  finally show ?thesis by simp
qed

(* TODO: what's the right class here? *)
lemma prod_ffact:
  fixes m :: "'a :: {ord, ring_1, comm_monoid_mult, comm_semiring_1_cancel}"
  shows "(\<Prod>i = 0..<n. m - of_nat i) = ffact n m"
proof -
  have "inj_on (\<lambda>j. j - 1) {1..n}"
    by (force intro: inj_on_diff_nat)
  moreover have "{0..<n} = (\<lambda>j. j - 1) ` {1..n}"
  proof -
    have "i \<in> (\<lambda>j. j - 1) ` {1..n}" if "i \<in> {0..<n}" for i
      using that by (auto intro: image_eqI[where x="i + 1"])
    from this show ?thesis by auto
  qed
  moreover have "m - of_nat (i - 1) = m + 1 - of_nat n + of_nat (n - i)" if "i \<in> {1..n}" for i
    using that by (simp add: of_nat_diff)
  ultimately have "(\<Prod>i = 0..<n. m - of_nat i) = (\<Prod>i = 1..n. m + 1 - of_nat n + of_nat (n - i))"
    by (rule prod.reindex_cong)
  from this show ?thesis
    unfolding ffact_def by (simp only: pochhammer_prod_rev)
qed

lemma prod_ffact_nat:
  fixes m :: nat
  shows "(\<Prod>i = 0..<n. m - i) = ffact n m"
proof cases
  assume "n \<le> m"
  have "inj_on (\<lambda>j. j - 1) {1..n}" by (force intro: inj_on_diff_nat)
  moreover have "{0..<n} = (\<lambda>j. j - 1) ` {1..n}"
  proof -
    have "i \<in> (\<lambda>j. j - 1) ` {1..n}" if "i \<in> {0..<n}" for i
      using that by (auto intro: image_eqI[where x="i + 1"])
    from this show ?thesis by auto
  qed
  ultimately have "(\<Prod>i = 0..<n. m - i) = (\<Prod>i = 1..n. (m + 1) - i)"
    by (auto intro: prod.reindex_cong[where l="\<lambda>i. i - 1"])
  from this \<open>n \<le> m\<close> show ?thesis
    unfolding ffact_def by (simp add: pochhammer_prod_rev)
next
  assume "\<not> n \<le> m"
  from this show ?thesis by (auto simp add: ffact_nat_triv)
qed

(* TODO: what's the right class here? *)
lemma prod_rev_ffact:
  fixes m :: "'a :: {ord, ring_1, comm_monoid_mult, comm_semiring_1_cancel}"
  shows "(\<Prod>i = 1..n. m - of_nat n + of_nat i) = ffact n m"
proof -
  have "inj_on (\<lambda>i. i + 1) {0..<n}" by simp
  moreover have "{1..n} = (\<lambda>i. i + 1) ` {0..<n}" by auto
  moreover have "m - of_nat n + of_nat (i + 1) = m + 1 - of_nat n + of_nat i" for i by simp
  ultimately have "(\<Prod>i = 1..n. m - of_nat n + of_nat i) = (\<Prod>i = 0..<n. m + 1 - of_nat n + of_nat i)"
    by (rule prod.reindex_cong[where l="\<lambda>i. i + 1"])
  from this show ?thesis
    unfolding ffact_def by (simp only: pochhammer_prod)
qed

lemma prod_rev_ffact_nat:
  fixes m :: nat
  assumes "n \<le> m"
  shows "(\<Prod>i = 1..n. m - n + i) = ffact n m"
proof -
  have "inj_on (\<lambda>i. i + 1) {0..<n}" by simp
  moreover have "{1..n} = (\<lambda>i. i + 1) ` {0..<n}" by auto
  moreover have "m - n + (i + 1) = m + 1 - n + i" for i
    using  \<open>n \<le> m\<close> by auto
  ultimately have "(\<Prod>i = 1..n. m - n + i) = (\<Prod>i = 0..<n. m + 1 - n + i)"
    by (rule prod.reindex_cong)
 from this show ?thesis
   unfolding ffact_def by (simp only: pochhammer_prod of_nat_id)
qed

lemma prod_rev_ffact_nat':
  fixes m :: nat
  assumes "n \<le> m"
  shows "\<Prod>{m - n + 1..m} = ffact n m"
proof -
  have "inj_on (\<lambda>i. m - n + i) {1::nat..n}" by (auto intro: inj_onI)
  moreover have "{m - n + 1..m} = (\<lambda>i. m - n + i) ` {1::nat..n}"
  proof -
    have "i \<in> (\<lambda>i. m + i - n) ` {Suc 0..n}" if "i \<in> {m - n + 1..m}" for i
      using that \<open>n \<le> m\<close> by (auto intro!: image_eqI[where x="i - (m - n)"])
    with \<open>n \<le> m\<close> show ?thesis by auto
  qed
  moreover have "m - n + i = m - n + i" for i ..
  ultimately have "\<Prod>{m - n + (1::nat)..m} = (\<Prod>i = 1..n. m - n + i)"
    by (rule prod.reindex_cong)
  from this show ?thesis
    using \<open>n \<le> m\<close> by (simp only: prod_rev_ffact_nat)
qed

lemma ffact_eq_fact_mult_binomial:
  "ffact k n = fact k * (n choose k)"
proof cases
  assume "k \<le> n"
  have "ffact k n = fact n div fact (n - k)"
    using \<open>k \<le> n\<close> by (simp add: fact_div_fact_ffact_nat)
  also have "\<dots> = fact k * (n choose k)"
    using \<open>k \<le> n\<close> by (simp add: binomial_fact_lemma[symmetric])
  finally show ?thesis .
next
  assume "\<not> k \<le> n"
  from this ffact_nat_triv show ?thesis by force
qed

lemma of_nat_ffact:
  "of_nat (ffact n m) = ffact n (of_nat m :: 'a :: comm_ring_1)"
proof (induct n arbitrary: m)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  show ?case
  proof (cases m)
    case 0
    then show ?thesis
      by (simp add: ffact_Suc_nat ffact_Suc)
  next
    case (Suc m)
    with Suc.hyps show ?thesis
      by (simp add: algebra_simps ffact_Suc_nat ffact_Suc)
  qed
qed

lemma of_int_ffact:
  "of_int (ffact n k) = ffact n (of_int k :: 'a :: comm_ring_1)"
proof (induct n arbitrary: k)
  case 0 then show ?case by simp
next
  case (Suc n k)
  then have "of_int (ffact n (k - 1)) = ffact n (of_int (k - 1) :: 'a)" .
  then show ?case
    by (simp add: ffact_Suc_nat ffact_Suc)
qed

lemma ffact_minus:
  fixes x :: "'a :: comm_ring_1"
  shows "ffact n (- x) = (- 1) ^ n * pochhammer x n"
proof -
  have "ffact n (- x) = pochhammer (- x + 1 - of_nat n) n"
    unfolding ffact_def ..
  also have "\<dots> = pochhammer (- x - of_nat n + 1) n"
    by (simp add: diff_add_eq)
  also have "\<dots> = (- 1) ^ n * pochhammer (- (- x)) n"
    by (rule pochhammer_minus')
  also have "\<dots> = (- 1) ^ n * pochhammer x n" by simp
  finally show ?thesis .
qed

text \<open>Conversion of natural potences into falling factorials and back\<close>

lemma monomial_ffact:
  "a ^ n = (\<Sum>k = 0..n. of_nat (Stirling n k) * ffact k a)"
    for a :: "'a :: comm_ring_1"
proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n)
  then have "a ^ Suc n = a * (\<Sum>k = 0..n. of_nat (Stirling n k) * ffact k a)"
    by simp
  also have "\<dots> = (\<Sum>k = 0..n. of_nat (Stirling n k) * (a * ffact k a))"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = (\<Sum>k = 0..n. of_nat (Stirling n k) * ffact (Suc k) a) +
    (\<Sum>k = 0..n. of_nat (Stirling n k) * (of_nat k * ffact k a))"
    by (simp add: sum.distrib algebra_simps mult_ffact)
  also have "\<dots> = (\<Sum>k = 0.. Suc n. of_nat (Stirling n k) * ffact (Suc k) a) +
    (\<Sum>k = 0..Suc n. of_nat ((Suc k) * (Stirling n (Suc k))) * (ffact (Suc k) a))"
  proof -
    have "(\<Sum>k = 0..n. of_nat (Stirling n k) * (of_nat k * ffact k a)) =
      (\<Sum>k = 0..n+2. of_nat (Stirling n k) * (of_nat k * ffact k a))" by simp
    also have "\<dots> = (\<Sum>k = Suc 0 .. Suc (Suc n). of_nat (Stirling n k) * (of_nat k * ffact k a)) "
      by (simp only: sum.atLeast_Suc_atMost [of 0 "n + 2"]) simp
    also have "\<dots> = (\<Sum>k = 0 .. Suc n. of_nat (Stirling n (Suc k)) * (of_nat (Suc k) * ffact (Suc k) a))"
      by (simp only: image_Suc_atLeastAtMost sum.shift_bounds_cl_Suc_ivl)
    also have "\<dots> = (\<Sum>k = 0 .. Suc n. of_nat ((Suc k) * Stirling n (Suc k)) * ffact (Suc k) a)"
      by (simp only: of_nat_mult algebra_simps)
    finally have "(\<Sum>k = 0..n. of_nat (Stirling n k) * (of_nat k * ffact k a)) =
      (\<Sum>k = 0..Suc n. of_nat (Suc k * Stirling n (Suc k)) * ffact (Suc k) a)"
      by simp
    then show ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>k = 0..n. of_nat (Stirling (Suc n) (Suc k)) * ffact (Suc k) a)"
    by (simp add: algebra_simps sum.distrib)
  also have "\<dots> = (\<Sum>k = Suc 0..Suc n. of_nat (Stirling (Suc n) k) * ffact k a)"
    by (simp only: image_Suc_atLeastAtMost sum.shift_bounds_cl_Suc_ivl)
  also have "\<dots> = (\<Sum>k = 0..Suc n. of_nat (Stirling (Suc n) k) * ffact k a)"
    by (simp only: sum.atLeast_Suc_atMost [of "0" "Suc n"]) simp
  finally show ?case by simp
qed

lemma ffact_monomial:
  "ffact n a = (\<Sum>k = 0..n. (- 1) ^ (n - k) * of_nat (stirling n k) * a ^ k)"
    for a :: "'a :: comm_ring_1"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  then have "ffact (Suc n) a = (a - of_nat n) * (\<Sum>k = 0..n. (- 1) ^ (n - k) * of_nat (stirling n k) * a ^ k)"
    by (simp add: ffact_Suc_rev)
  also have "\<dots> = (\<Sum>k = 0..n. (- 1) ^ (n - k) * of_nat (stirling n k) * a ^ (Suc k)) +
    (\<Sum>k = 0..n. (- 1) * (- 1) ^ (n - k) * of_nat (n * (stirling n k)) * a ^ k)"
    by (simp only: diff_conv_add_uminus distrib_right) (simp add: sum_distrib_left field_simps)
  also have "\<dots> = (\<Sum>k = 0..n. (- 1) ^ (Suc n - Suc k) * of_nat (stirling n k) * a ^ Suc k) +
  (\<Sum>k = 0..n. (- 1) ^ (Suc n - Suc k) * of_nat (n * stirling n (Suc k)) * a ^ Suc k)"
  proof -
    have "(\<Sum>k = 0..n. (- 1) * (- 1) ^ (n - k) * of_nat (n * stirling n k) * a ^ k) =
      (\<Sum>k = 0..n. (- 1) ^ (Suc n - k) * of_nat (n * stirling n k) * a ^ k)"
      by (simp add: Suc_diff_le)
    also have "\<dots> = (\<Sum>k = Suc 0..Suc n. (- 1) ^ (Suc n - k) * of_nat (n * stirling n k) * a ^ k)"
      by (simp add: sum.atLeast_Suc_atMost) (cases n; simp)
    also have "\<dots> = (\<Sum>k = 0..n. (- 1) ^ (Suc n - Suc k) * of_nat (n * stirling n (Suc k)) * a ^ Suc k)"
      by (simp only: sum.shift_bounds_cl_Suc_ivl)
    finally show ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>k = 0..n. (- 1) ^ (Suc n - Suc k) * of_nat (n * stirling n (Suc k) + stirling n k) * a ^ Suc k)"
    by (simp add: sum.distrib algebra_simps)
  also have "\<dots> = (\<Sum>k = 0..n. (- 1) ^ (Suc n - Suc k) * of_nat (stirling (Suc n) (Suc k)) * a ^ Suc k)"
    by (simp only: stirling.simps)
  also have "\<dots> = (\<Sum>k = Suc 0..Suc n. (- 1) ^ (Suc n - k) * of_nat (stirling (Suc n) k) * a ^ k)"
    by (simp only: sum.shift_bounds_cl_Suc_ivl)
  also have "\<dots> = (\<Sum>k = 0..Suc n. (- 1) ^ (Suc n - k) * of_nat (stirling (Suc n) k) * a ^ k)"
    by (simp add: sum.atLeast_Suc_atMost)
  finally show ?case .
qed

end
