(*
    File:      More_Totient.thy
    Author:    Manuel Eberl, TU München
    
    Additional properties of Euler's totient function
*)
section \<open>Euler's $\phi$ function\<close>
theory More_Totient
  imports
    Moebius_Mu
    "HOL-Number_Theory.Number_Theory"
begin
  
lemma fds_totient_times_zeta: 
  "fds (\<lambda>n. of_nat (totient n) :: 'a :: comm_semiring_1) * fds_zeta = fds of_nat"
proof
  fix n :: nat assume n: "n > 0"
  have "fds_nth (fds (\<lambda>n. of_nat (totient n)) * fds_zeta) n = 
          dirichlet_prod (\<lambda>n. of_nat (totient n)) (\<lambda>_. 1) n"
    by (simp add: fds_nth_mult)
  also from n have "\<dots> = fds_nth (fds of_nat) n"
    by (simp add: fds_nth_fds dirichlet_prod_def totient_divisor_sum of_nat_sum [symmetric]
             del: of_nat_sum)
  finally show "fds_nth (fds (\<lambda>n. of_nat (totient n)) * fds_zeta) n = fds_nth (fds of_nat) n" .
qed

lemma fds_totient_times_zeta': "fds totient * fds_zeta = fds id"
  using fds_totient_times_zeta[where 'a = nat] by simp
  
lemma fds_totient: "fds (\<lambda>n. of_nat (totient n)) = fds of_nat * fds moebius_mu"
proof -
  have "fds (\<lambda>n. of_nat (totient n)) * fds_zeta * fds moebius_mu = fds of_nat * fds moebius_mu"
    by (simp add: fds_totient_times_zeta)
  also have "fds (\<lambda>n. of_nat (totient n)) * fds_zeta * fds moebius_mu = 
               fds (\<lambda>n. of_nat (totient n))"
    by (simp only: mult.assoc fds_zeta_times_moebius_mu mult_1_right)
  finally show ?thesis .
qed

lemma totient_conv_moebius_mu:
  "int (totient n) = dirichlet_prod moebius_mu int n"
proof (cases "n = 0")
  case False
  show ?thesis
    by (rule moebius_inversion)
       (insert False, simp_all add: of_nat_sum [symmetric] totient_divisor_sum del: of_nat_sum)
qed simp_all

interpretation totient: multiplicative_function totient
proof -
  have "multiplicative_function int" by standard simp_all
  hence "multiplicative_function (dirichlet_prod moebius_mu int)"
    by (intro multiplicative_dirichlet_prod moebius_mu.multiplicative_function_axioms)
  also have "dirichlet_prod moebius_mu int = (\<lambda>n. int (totient n))" 
    by (simp add: fun_eq_iff totient_conv_moebius_mu)
  finally show "multiplicative_function totient" by (rule multiplicative_function_of_natD)
qed

lemma even_prime_nat: "prime p \<Longrightarrow> even p \<Longrightarrow> p = (2::nat)"
  using prime_odd_nat[of p] prime_gt_1_nat[of p] by (cases "p = 2") auto

lemma twopow_dvd_totient:
  fixes n :: nat
  assumes "n > 0"
  defines "k \<equiv> card {p\<in>prime_factors n. odd p}"
  shows   "2 ^ k dvd totient n"
proof -
  define P where "P = {p\<in>prime_factors n. odd p}"
  define P' where "P' = {p\<in>prime_factors n. even p}"
  define r where "r = (\<lambda>p. multiplicity p n)"
  from \<open>n > 0\<close> have "totient n = (\<Prod>p\<in>prime_factors n. totient (p ^ r p))"
    unfolding r_def by (rule totient.prod_prime_factors)
  also have "prime_factors n = P \<union> P'"
    by (auto simp: P_def P'_def)
  also have "(\<Prod>p\<in>\<dots>. totient (p ^ r p)) =
               (\<Prod>p\<in>P. totient (p ^ r p)) * (\<Prod>p\<in>P'. totient (p ^ r p))"
    by (subst prod.union_disjoint) (auto simp: P_def P'_def)
  finally have eq: "totient n = \<dots>" .

  have "p ^ r p > 2" if "p \<in> P" for p
  proof -
    have "p \<noteq> 2" using that by (auto simp: P_def)
    moreover have "p > 1" using prime_gt_1_nat[of p] that by (auto simp: P_def)
    ultimately have "2 < p" by linarith
    also have "p = p ^ 1" by simp
    also have "p ^ 1 \<le> p ^ r p"
      using that prime_gt_1_nat[of p]
      by (intro power_increasing) (auto simp: P_def prime_factors_multiplicity r_def)
    finally show ?thesis .
  qed
  hence "(\<Prod>p\<in>P. 2) dvd (\<Prod>p\<in>P. totient (p ^ r p))"
    by (intro prod_dvd_prod totient_even)
  hence "2 ^ card P dvd (\<Prod>p\<in>P. totient (p ^ r p))"
    by simp
  also have "\<dots> dvd (\<Prod>p\<in>P. totient (p ^ r p)) * (\<Prod>p\<in>P'. totient (p ^ r p))"
    by simp
  also have "\<dots> = totient n"
    by (rule eq [symmetric])
  finally show ?thesis unfolding k_def P_def .
qed

lemma totient_conv_moebius_mu':
  assumes "n > (0::nat)"
  shows   "real (totient n) = real n * (\<Sum>d | d dvd n. moebius_mu d / real d)"
proof -
  have "real (totient n) = of_int (int (totient n))" by simp
  also have "int (totient n) = (\<Sum>d | d dvd n. moebius_mu d * int (n div d))"
    using totient_conv_moebius_mu by (simp add: dirichlet_prod_def assms)
  also have "real_of_int (\<Sum>d | d dvd n. moebius_mu d * int (n div d)) =
               (\<Sum>d | d dvd n. moebius_mu d * real (n div d))" by simp
  also have "\<dots> = (\<Sum>d | d dvd n. real n * moebius_mu d / real d)"
    by (rule sum.cong) (simp_all add: field_char_0_class.of_nat_div)
  also have "\<dots> = real n * (\<Sum>d | d dvd n. moebius_mu d / real d)"
    by (simp add: sum_distrib_left)
  finally show ?thesis .
qed

lemma totient_prime_power_Suc:
  assumes "prime p"
  shows   "totient (p ^ Suc n) = p ^ Suc n - p ^ n"
proof -
  have "totient (p ^ Suc n) = p ^ Suc n - card ((*) p ` {0<..p ^ n})"
    unfolding totient_def totatives_prime_power_Suc[OF assms]
    by (subst card_Diff_subset) (insert assms, auto simp: prime_gt_0_nat)
  also from assms have "card ((*) p ` {0<..p^n}) = p ^ n"
    by (subst card_image) (auto simp: inj_on_def)
  finally show ?thesis .
qed

interpretation totient: multiplicative_function' totient "\<lambda>p k. p ^ k - p ^ (k - 1)" "\<lambda>p. p - 1"
proof
  fix p k :: nat assume "prime p" "k > 0"
  thus "totient (p ^ k) = p ^ k - p ^ (k - 1)" 
    by (cases k) (simp_all add: totient_prime_power_Suc del: power_Suc)
qed simp_all

end
