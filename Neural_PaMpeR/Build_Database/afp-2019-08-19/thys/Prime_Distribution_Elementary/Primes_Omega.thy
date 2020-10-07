(*
  File:    Primes_Omega.thy
  Author:  Manuel Eberl, TU München

  The primes \<omega> function (i.e. the number of distinct prime factors)
*)
section \<open>The Prime \<open>\<omega>\<close> function\<close>
theory Primes_Omega
  imports Dirichlet_Series.Dirichlet_Series Dirichlet_Series.Divisor_Count
begin

text \<open>
  The prime \<open>\<omega>\<close> function $\omega(n)$ counts the number of distinct prime factors of \<open>n\<close>.
\<close>

definition primes_omega :: "nat \<Rightarrow> nat" where
  "primes_omega n = card (prime_factors n)"

lemma primes_omega_prime [simp]: "prime p \<Longrightarrow> primes_omega p = 1"
  by (simp add: primes_omega_def prime_factorization_prime)

lemma primes_omega_0 [simp]: "primes_omega 0 = 0"
  by (simp add: primes_omega_def)

lemma primes_omega_1 [simp]: "primes_omega 1 = 0"
  by (simp add: primes_omega_def)

lemma primes_omega_Suc_0 [simp]: "primes_omega (Suc 0) = 0"
  by (simp add: primes_omega_def)

lemma primes_omega_power [simp]: "n > 0 \<Longrightarrow> primes_omega (x ^ n) = primes_omega x"
  by (simp add: primes_omega_def prime_factors_power)

lemma primes_omega_primepow [simp]: "primepow n \<Longrightarrow> primes_omega n = 1"
  by (auto simp: primepow_def)

lemma primes_omega_eq_0_iff: "primes_omega n = 0 \<longleftrightarrow> n = 0 \<or> n = 1"
  by (auto simp: primes_omega_def prime_factorization_empty_iff)

lemma primes_omega_pos [simp, intro]: "n > 1 \<Longrightarrow> primes_omega n > 0"
  by (cases "primes_omega n > 0") (auto simp: primes_omega_eq_0_iff)

lemma primes_omega_mult_coprime:
  assumes "coprime x y" "x > 0 \<or> y > 0"
  shows   "primes_omega (x * y) = primes_omega x + primes_omega y"
proof (cases "x = 0 \<or> y = 0")
  case False
  hence "prime_factors (x * y) = prime_factors x \<union> prime_factors y"
    by (subst prime_factorization_mult) auto
  also {
    have "prime_factors x \<inter> prime_factors y = set_mset (prime_factorization (gcd x y))"
      using False by (subst prime_factorization_gcd) auto
    also have "gcd x y = 1" using \<open>coprime x y\<close> by auto
    finally have "card (prime_factors x \<union> prime_factors y) = primes_omega x + primes_omega y"
      unfolding primes_omega_def by (intro card_Un_disjoint) (use False in auto)
  }
  finally show ?thesis by (simp add: primes_omega_def)
qed (use assms in auto)

lemma divisor_count_squarefree:
  assumes "squarefree n" "n > 0"
  shows   "divisor_count n = 2 ^ primes_omega n"
proof -
  have "divisor_count n = (\<Prod>p\<in>prime_factors n. Suc (multiplicity p n))"
    using assms by (subst divisor_count.prod_prime_factors') auto
  also have "\<dots> = (\<Prod>p\<in>prime_factors n. 2)"
    using assms assms by (intro prod.cong) (auto simp: squarefree_factorial_semiring')
  finally show ?thesis by (simp add: primes_omega_def)
qed

end