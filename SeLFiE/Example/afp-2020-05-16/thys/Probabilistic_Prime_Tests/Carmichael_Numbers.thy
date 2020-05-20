(*
  File:     Carmichael_Numbers.thy
  Authors:  Daniel Stüwe

  Definition and basic properties of Carmichael numbers
*)
section \<open>Carmichael Numbers\<close>
theory Carmichael_Numbers
imports
  Residues_Nat
begin

text \<open>
  A Carmichael number is a composite number \<open>n\<close> that Fermat's test incorrectly labels
  as primes no matter which witness \<open>a\<close> is chosen (except in the case that \<open>a\<close> shares a
  factor with \<open>n\<close>). \cite{Carmichael_numbers, wiki:Carmichael_number}
\<close>
definition Carmichael_number :: "nat \<Rightarrow> bool" where
  "Carmichael_number n \<longleftrightarrow> n > 1 \<and> \<not>prime n \<and> (\<forall>a. coprime a n \<longrightarrow> [a ^ (n - 1) = 1] (mod n))"

lemma Carmichael_number_0[simp, intro]: "\<not>Carmichael_number 0"
  unfolding Carmichael_number_def by simp

lemma Carmichael_number_1[simp, intro]: "\<not>Carmichael_number 1"
  by (auto simp: Carmichael_number_def)

lemma Carmichael_number_Suc_0[simp, intro]: "\<not>Carmichael_number (Suc 0)"
  by (auto simp: Carmichael_number_def)

lemma Carmichael_number_not_prime: "Carmichael_number n \<Longrightarrow> \<not>prime n"
  by (auto simp: Carmichael_number_def)

lemma Carmichael_number_gt_3: "Carmichael_number n \<Longrightarrow> n > 3"
proof -
  assume *: "Carmichael_number n"
  hence "n > 1" by (auto simp: Carmichael_number_def)
  {
    assume "\<not>(n > 3)"
    with \<open>n > 1\<close> have "n = 2 \<or> n = 3" by auto
    with * and Carmichael_number_not_prime[of n] have False by auto
  }
  thus "n > 3" by auto
qed

text \<open>
  The proofs are inspired by \cite{Carmichael_numbers, Carmichael_number_square_free}.
\<close>
lemma Carmichael_number_imp_squarefree_aux:
  assumes "Carmichael_number n"
  assumes n: "n = p^r * l" and "prime p" "\<not>p dvd l"
  assumes "r > 1"
  shows False
proof -
  have "\<not> prime n" using \<open>Carmichael_number n\<close> unfolding Carmichael_number_def by blast

  have * : "[a^(n-1) = 1] (mod n)" if "coprime a n" for a
    using \<open>Carmichael_number n\<close> that
    unfolding Carmichael_number_def
    by blast

  have "1 \<le> n"
    unfolding n using \<open>prime p\<close> \<open>\<not> p dvd l\<close>
    by (auto intro: gre1I_nat)

  have "2 \<le> n"
  proof(cases "n = 1")
    case True
    then show ?thesis
      unfolding n using \<open>1 < r\<close> prime_gt_1_nat[OF \<open>prime p\<close>]
      by simp
  next
    case False
    then show ?thesis using \<open>1 \<le> n\<close> by linarith
  qed

  have "p < p^r"
    using prime_gt_1_nat[OF \<open>prime p\<close>] \<open>1 < r\<close>
    by (metis power_one_right power_strict_increasing_iff)

  hence "p < n" using \<open>1 \<le> n\<close> less_le_trans n by fastforce 

  then have [simp]: "{..n} - {0..Suc 0} = {2..n}" by auto

  obtain a where a: "[a = p + 1] (mod p^r)" "[a = 1] (mod l)"
    using binary_chinese_remainder_nat[of "p^r" l "p + 1" 1] 
    and \<open>prime p\<close> prime_imp_coprime_nat coprime_power_left_iff \<open>\<not>p dvd l\<close>
    by blast

  hence "coprime a n"
    using lucas_coprime_lemma[of 1 a l] cong_imp_coprime[of "p+1" a "p^r"] 
      and coprime_add_one_left cong_sym 
    unfolding \<open>n = p ^ r * l\<close> coprime_mult_right_iff coprime_power_right_iff power_one_right
    by blast

  hence "[a ^ (n - 1) = 1] (mod n)"
    using * by blast

  hence "[a ^ (n - 1) = 1] (mod p^r)"
    using n cong_modulus_mult_nat by blast

  hence A: "[a ^ n = a] (mod p^r)"
    using cong_scalar_right[of "a^(n-1)" 1 "p^r" a] \<open>1 \<le> n\<close>
    unfolding power_Suc2[symmetric]
    by simp

  have "r = Suc (Suc (r - 2))"
    using \<open>1 < r\<close> by linarith

  then have "p^r = p^2 * p^(r-2)"
    by (simp add: algebra_simps flip: power_add power_Suc)
   
  hence "[a ^ n = a] (mod p^2)" "[a = p + 1] (mod p^2)"
    using \<open>1 < r\<close> A cong_modulus_mult_nat \<open>[a = p + 1] (mod p^r)\<close>
    by algebra+

  hence 1: "[(p + 1) ^ n = (p + 1)] (mod p^2)"
    by (metis (mono_tags) cong_def power_mod)

  have "[(p + 1) ^ n = (\<Sum>k\<le>n. of_nat (n choose k) * p ^ k * 1 ^ (n - k))] (mod p^2)"
    using binomial[of p 1 n] by simp

  also have "(\<Sum>k\<le>n. of_nat (n choose k) * p ^ k * 1 ^ (n - k)) =
             (\<Sum>k = 0..1. (n choose k) * p ^ k) + (\<Sum>k\<in> {2..n}. of_nat (n choose k) * p ^ k * 1 ^ (n - k))"
    using \<open>2 \<le> n\<close> finite_atMost[of n]
    by (subst sum.subset_diff[where B = "{0..1}"]) auto

  also have "[(\<Sum>k = 0..1. (n choose k) * p ^ k) = 1] (mod p^2)"
    by (simp add: cong_altdef_nat \<open>p ^ r = p\<^sup>2 * p ^ (r - 2)\<close> n)

  also have "[(\<Sum>k\<in> {2..n}. of_nat (n choose k) * p ^ k * 1 ^ (n - k)) = 0] (mod p^2)"
    by (rule cong_eq_0_I) (clarsimp simp: cong_0_iff le_imp_power_dvd)

  finally have 2: "[(p + 1) ^ n = 1] (mod p^2)" by simp

  from cong_trans[OF cong_sym[OF 1] 2] 
  show ?thesis
    using prime_gt_1_nat[OF \<open>prime p\<close>]
    by (auto dest: residue_one_dvd[unfolded One_nat_def] simp add: cong_def numeral_2_eq_2)
qed

theorem Carmichael_number_imp_squarefree:
  assumes "Carmichael_number n"
  shows "squarefree n"
proof(rule squarefreeI, rule ccontr)
  fix x :: nat
  assume "x\<^sup>2 dvd n"
  from assms have "n > 0" using Carmichael_number_gt_3[of n] by auto
  from \<open>x\<^sup>2 dvd n\<close> and \<open>0 < n\<close> have "0 < x" by auto

  assume "\<not> is_unit x"
  then obtain p where "prime p" "p dvd x"
    using prime_divisor_exists[of x] \<open>0 < x\<close>
    by blast

  with \<open>x\<^sup>2 dvd n\<close> have "p^2 dvd n"
    by auto

  obtain l where n: "n = p ^ multiplicity p n * l"
    using multiplicity_dvd[of p n] by blast

  then have "\<not> p dvd l"
    using multiplicity_decompose'[where x = n and p = p]
    using \<open>prime p\<close> \<open>0 < n\<close>
    by (metis nat_dvd_1_iff_1 nat_mult_eq_cancel1 neq0_conv prime_prime_factor_sqrt zero_less_power)

  have "2 \<le> multiplicity p n"
    using \<open>p\<^sup>2 dvd n\<close> \<open>0 < n\<close> prime_gt_1_nat[OF \<open>prime p\<close>]
    by (auto intro!: multiplicity_geI simp: power2_eq_square)
    
  then show False 
    using Carmichael_number_imp_squarefree_aux[OF \<open>Carmichael_number n\<close> n] \<open>prime p\<close> \<open>\<not> p dvd l\<close>
    by auto
qed

corollary Carmichael_not_primepow:
  assumes "Carmichael_number n"
  shows   "\<not>primepow n"
  using Carmichael_number_imp_squarefree[of n] Carmichael_number_not_prime[of n] assms
        primepow_gt_0_nat[of n] by (auto simp: not_squarefree_primepow)

lemma Carmichael_number_imp_squarefree_alt_weak:
  assumes "Carmichael_number n"
  shows "\<exists>p l. (n = p * l) \<and> prime p \<and> \<not>p dvd l"
proof -
  from assms have "n > 1"
    using Carmichael_number_gt_3[of n] by simp
  have "squarefree n"
    using Carmichael_number_imp_squarefree assms 
    by blast

  obtain p l where "p * l = n" "prime p" "1 < p"
    using assms prime_divisor_exists_strong_nat prime_gt_1_nat
    unfolding Carmichael_number_def by blast

  then have "multiplicity p n = 1"
    using \<open>1 < n\<close> \<open>squarefree n\<close> and multiplicity_eq_zero_iff[of n p] squarefree_factorial_semiring''[of n]
    by auto

  then have "\<not>p dvd l"
    using \<open>1 < n\<close> \<open>prime p\<close> \<open>p * l = n\<close> multiplicity_decompose'[of n p]
    by force

  show ?thesis 
    using \<open>p * l = n\<close> \<open>prime p\<close> \<open>\<not>p dvd l\<close>
    by blast
qed

theorem Carmichael_number_odd:
  assumes "Carmichael_number n"
  shows   "odd n"
proof (rule ccontr)
  assume "\<not> odd n"
  hence "even n" by simp
  from assms have "n \<ge> 4" using Carmichael_number_gt_3[of n] by simp
  have "[(n - 1) ^ (n - 1) = n - 1] (mod n)"
    using \<open>even n\<close> and \<open>n \<ge> 4\<close> by (intro odd_pow_cong) auto

  then have "[(n - 1) ^ (n - 1) \<noteq> 1] (mod n)"
    using cong_trans[of 1 "(n - 1) ^ (n - 1)" n "n-1", OF cong_sym] \<open>4 \<le> n\<close>
    by (auto simp: cong_def)

  moreover have "coprime (n - 1) n"
    using \<open>n \<ge> 4\<close> coprime_diff_one_left_nat[of n] by auto

  ultimately show False
    using assms unfolding Carmichael_number_def by blast
qed

lemma Carmichael_number_imp_squarefree_alt:
  assumes "Carmichael_number n"
  shows "\<exists>p l. (n = p * l) \<and> prime p \<and> \<not>p dvd l \<and> 2 < l"
proof -
  obtain p l where [simp]: "(n = p * l)" and "prime p" "\<not>p dvd l"
    using Carmichael_number_imp_squarefree_alt_weak and assms by blast

  moreover have "odd n" using Carmichael_number_odd and assms by blast

  consider "l = 0 \<or> l = 2" | "l = 1" | "2 < l"
    by fastforce

  then have "2 < l" 
  proof cases
    case 1
    then show ?thesis
      using \<open>odd n\<close> by auto
  next
    case 2
    then show ?thesis
      using \<open>n = p * l\<close> \<open>prime p\<close> \<open>Carmichael_number n\<close>
      unfolding Carmichael_number_def by simp
  qed simp

  ultimately show ?thesis by blast
qed

lemma Carmichael_number_imp_dvd:
  fixes n :: nat
  assumes Carmichael_number: "Carmichael_number n" and "prime p" "p dvd n"
  shows "p - 1 dvd n - 1"
proof -
  have "\<not>prime n" using Carmichael_number unfolding Carmichael_number_def by blast
  obtain u where "n = p * u" using \<open>p dvd n\<close> by blast
  have "squarefree n" using Carmichael_number_imp_squarefree assms by blast
  then have "\<not>p dvd u"
    using \<open>prime p\<close> not_prime_unit[of p]
    unfolding power2_eq_square squarefree_def \<open>n = p * u\<close>
    by fastforce

  define R where "R = Residues_nat p"
  interpret residues_nat_prime p R
    by unfold_locales (simp_all only: \<open>prime p\<close> R_def)
  
  obtain a where a: "a \<in> {0<..<p}" "units.ord a = p - 1"
    using residues_prime_cyclic' \<open>prime p\<close> by metis
  from a have "a \<in> totatives p" by (auto simp: totatives_prime \<open>prime p\<close>)

  have "coprime p u"
    using \<open>prime p\<close> \<open>\<not> p dvd u\<close>
    by (simp add: prime_imp_coprime_nat) 

  then obtain x where "[x = a] (mod p)" "[x = 1] (mod u)" 
    using binary_chinese_remainder_nat[of p u a 1] by blast

  have "coprime x p"
    using \<open>a \<in> totatives p\<close> and cong_imp_coprime[OF cong_sym[OF \<open>[x = a] (mod p)\<close>]]
    by (simp add: coprime_commute totatives_def)
  moreover have "coprime x u" 
    using coprime_1_left and cong_imp_coprime[OF cong_sym[OF \<open>[x = 1] (mod u)\<close>]] by blast
  ultimately have "coprime x n"
    by (simp add: \<open>n = p * u\<close>)

  have "[a ^ (n - 1) = x ^ (n - 1)] (mod p)"
    using \<open>[x = a] (mod p)\<close> by (intro cong_pow) (auto simp: cong_sym_eq)
  also have "[x ^ (n - 1) = 1] (mod n)"
    using Carmichael_number \<open>coprime x n\<close> unfolding Carmichael_number_def by blast
  then have "[x ^ (n - 1) = 1] (mod p)"
    using \<open>n = p * u\<close> cong_modulus_mult_nat by blast 
  finally have "ord p a dvd n - 1"
    by (simp add: ord_divides [symmetric])
  also have "ord p a = p - 1"
    using a \<open>a \<in> totatives p\<close> by (simp add: units.ord_residue_mult_group)
  finally show ?thesis .    
qed

text \<open>
  The following lemma is also called Korselt's criterion.
\<close>
lemma Carmichael_numberI:
  fixes n :: nat
  assumes "\<not> prime n" "squarefree n" "1 < n" and
          DIV: "\<And>p. p \<in> prime_factors n \<Longrightarrow> p - 1 dvd n - 1"
  shows   "Carmichael_number n"
  unfolding Carmichael_number_def
proof (intro assms conjI allI impI)
  fix a :: nat assume "coprime a n"

  have n: "n = \<Prod>(prime_factors n)"
    using prime_factorization_nat and squarefree_factorial_semiring'[of n] \<open>1 < n\<close> \<open>squarefree n\<close>
    by fastforce

  have "x \<in># prime_factorization n \<Longrightarrow> y \<in># prime_factorization n \<Longrightarrow> x \<noteq> y \<Longrightarrow> coprime x y" for x y
    using in_prime_factors_imp_prime primes_coprime
    by blast

  moreover {
    fix p 
    assume p: "p \<in># prime_factorization n"

    have "\<not>p dvd a"
      using \<open>coprime a n\<close> p coprime_common_divisor_nat[of a n p]
      by (auto simp: in_prime_factors_iff)
    with p have "[a ^ (p - 1) = 1] (mod p)"
      by (intro fermat_theorem) auto
    hence "ord p a dvd p - 1"
      by (subst (asm) ord_divides)
    also from p have "p - 1 dvd n - 1"
      by (rule DIV)
    finally have "[a ^ (n - 1) = 1] (mod p)"
      by (subst ord_divides)
  }

  ultimately show "[a ^ (n - 1) = 1] (mod n)"
    using n coprime_cong_prod_nat by metis
qed

theorem Carmichael_number_iff:
  "Carmichael_number n \<longleftrightarrow>
     n \<noteq> 1 \<and> \<not>prime n \<and> squarefree n \<and> (\<forall>p\<in>prime_factors n. p - 1 dvd n - 1)"
proof -
  consider "n = 0" | "n = 1" | "n > 1" by force
  thus ?thesis using Carmichael_numberI[of n] Carmichael_number_imp_dvd[of n]
    by cases (auto simp: Carmichael_number_not_prime Carmichael_number_imp_squarefree)
qed

text \<open>
  Every Carmichael number has at least three distinct prime factors.
\<close>
theorem Carmichael_number_card_prime_factors:
  assumes "Carmichael_number n"
  shows   "card (prime_factors n) \<ge> 3"
proof (rule ccontr)
  from assms have "n > 3"
    using Carmichael_number_gt_3[of n] by simp
  assume "\<not>(card (prime_factors n) \<ge> 3)"
  moreover have "card (prime_factors n) \<noteq> 0"
    using assms Carmichael_number_gt_3[of n] by (auto simp: prime_factorization_empty_iff)
  moreover have "card (prime_factors n) \<noteq> 1"
    using assms by (auto simp: one_prime_factor_iff_primepow Carmichael_not_primepow)
  ultimately have "card (prime_factors n) = 2"
    by linarith
  then obtain p q where pq: "prime_factors n = {p, q}" "p \<noteq> q"
    by (auto simp: card_Suc_eq numeral_2_eq_2)
  hence "prime p" "prime q" by (auto simp: in_prime_factors_iff)

  have "n = \<Prod>(prime_factors n)"
    using assms by (subst squarefree_imp_prod_prime_factors_eq)
                   (auto simp: Carmichael_number_imp_squarefree)
  with pq have n_eq: "n = p * q" by simp

  have "p - 1 dvd n - 1" and "q - 1 dvd n - 1" using assms pq
    unfolding Carmichael_number_iff by blast+
  with \<open>prime p\<close> \<open>prime q\<close> \<open>n = p * q\<close> \<open>p \<noteq> q\<close> show False
  proof (induction p q rule: linorder_wlog)
    case (le p q)
    hence "p < q" by auto
    have "[q = 1] (mod q - 1)"
      using prime_gt_1_nat[of q] \<open>prime q\<close> by (simp add: cong_def le_mod_geq)
    hence "[p * q - 1 = p * 1 - 1] (mod q - 1)"
      using le prime_gt_1_nat[of p] by (intro cong_diff_nat cong_mult) auto
    hence "[p - 1 = n - 1] (mod q - 1)"
      by (simp add: \<open>n = p * q\<close> cong_sym_eq)
    also have "[n - 1 = 0] (mod q - 1)"
      using le by (simp add: cong_def)
    finally have "(p - 1) mod (q - 1) = 0"
      by (simp add: cong_def)
    also have "(p - 1) mod (q - 1) = p - 1"
      using prime_gt_1_nat[of p] \<open>prime p\<close> \<open>p < q\<close> by (intro mod_less) auto
    finally show False
      using prime_gt_1_nat[of p] \<open>prime p\<close> by simp
  qed (simp_all add: mult.commute)
qed

lemma Carmichael_number_iff':
  fixes n :: nat
  defines "P \<equiv> prime_factorization n"
  shows "Carmichael_number n \<longleftrightarrow>
           n > 1 \<and> size P \<noteq> 1 \<and> (\<forall>p\<in>#P. count P p = 1 \<and> p - 1 dvd n - 1)"
  unfolding Carmichael_number_iff
  by (cases "n = 0") (auto simp: P_def squarefree_factorial_semiring' count_prime_factorization)

text \<open>
  The smallest Carmichael number is 561, and it was found and proven so by
  Carmichael in 1910~\cite{carmichael1910note}.
\<close>
lemma Carmichael_number_561: "Carmichael_number 561" (is "Carmichael_number ?n")
proof -
  have [simp]: "prime_factorization (561 :: nat) = {#3, 11, 17#}"
    by (rule prime_factorization_eqI) auto
  show ?thesis by (subst Carmichael_number_iff') auto
qed

end