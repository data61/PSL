(*
    File:      Divisor_Count.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>The divisor functions\<close>
theory Divisor_Count
imports
  Complex_Main
  "HOL-Number_Theory.Number_Theory"
  Dirichlet_Series
  More_Totient
  Moebius_Mu
begin
  
subsection \<open>The general divisor function\<close>
  
definition divisor_sigma :: "'a :: nat_power \<Rightarrow> nat \<Rightarrow> 'a" where
  "divisor_sigma x n = (\<Sum>d | d dvd n. nat_power d x)"
  
lemma divisor_sigma_0 [simp]: "divisor_sigma x 0 = 0"
  by (simp add: divisor_sigma_def)

lemma divisor_sigma_Suc_0 [simp]: "divisor_sigma x (Suc 0) = 1"
  by (simp add: divisor_sigma_def)

lemma divisor_sigma_1 [simp]: "divisor_sigma x 1 = 1"
  by simp

lemma fds_divisor_sigma: "fds (divisor_sigma x) = fds_zeta * fds_shift x fds_zeta"
  by (rule fds_eqI) (simp add: fds_nth_mult dirichlet_prod_altdef1 divisor_sigma_def)

interpretation divisor_sigma: multiplicative_function "divisor_sigma x"
proof -
  have "multiplicative_function (dirichlet_prod (\<lambda>n. if n = 0 then 0 else 1) 
           (\<lambda>n. if n = 0 then 0 else nat_power n x))" (is "multiplicative_function ?f")
    by (rule multiplicative_dirichlet_prod; standard)
       (simp_all add: nat_power_mult_distrib)
  also have "?f n = divisor_sigma x n" for n
    using fds_divisor_sigma[of x]
    by (cases "n = 0") (simp_all add: fds_eq_iff fds_nth_mult )
  hence "?f = divisor_sigma x" ..
  finally show "multiplicative_function (divisor_sigma x)" .
qed

lemma divisor_sigma_naive [code]:
  "divisor_sigma x n = (if n = 0 then 0 else fold_atLeastAtMost_nat
        (\<lambda>d acc. if d dvd n then nat_power d x + acc else acc) 1 n 0)"
proof (cases "n = 0")
  case False
  have "divisor_sigma x n = (\<Sum>d\<in>{1..n}. if d dvd n then nat_power d x else 0)"
    unfolding divisor_sigma_def using False by (intro sum.mono_neutral_cong_left) (auto elim: dvdE)
  also have "\<dots> = fold_atLeastAtMost_nat
        (\<lambda>d acc. (if d dvd n then nat_power d x else 0) + acc) 1 n 0"
    by (rule sum_atLeastAtMost_code)
  also have "(\<lambda>d acc. (if d dvd n then nat_power d x else 0) + acc) =
               (\<lambda>d acc. (if d dvd n then nat_power d x + acc else acc))"
    by (auto simp: fun_eq_iff)
  finally show ?thesis using False by simp
qed auto

lemma divisor_sigma_of_nat: "divisor_sigma (of_nat x) n = of_nat (divisor_sigma x n)"
proof (cases "n = 0")
  case False
  show ?thesis unfolding divisor_sigma_def of_nat_sum
    by (intro sum.cong refl, subst nat_power_of_nat) (insert False, auto elim: dvdE)
qed auto

lemma divisor_sigma_prime_power_field:
  fixes x :: "'a :: {field, nat_power}"
  assumes "prime p"
  shows   "divisor_sigma x (p ^ k) = 
             (if nat_power p x = 1 then of_nat (k + 1) else
             (nat_power p x ^ Suc k - 1) / (nat_power p x - 1))"
proof -
  have "divisor_sigma x (p ^ k) = (\<Sum>i\<le>k. nat_power (p^i) x)"
    unfolding divisor_sigma_def
    by (rule sum.reindex_bij_betw [symmetric])
       (insert assms, auto simp: bij_betw_def inj_on_def prime_gt_Suc_0_nat 
          divides_primepow_nat intro: le_imp_power_dvd)
  also have "\<dots> = (\<Sum>i\<le>k. nat_power p x ^ i)"
    using assms by (intro sum.cong refl) (simp_all add: prime_gt_0_nat nat_power_power_left)
  also have "\<dots> = (if nat_power p x = 1 then of_nat (k + 1) else
                    (nat_power p x ^ Suc k - 1) / (nat_power p x - 1))"
    using geometric_sum[of "nat_power p x" "Suc k"] unfolding lessThan_Suc_atMost
    by (auto split: if_splits)
  finally show ?thesis .
qed
  
lemma divisor_sigma_prime_power_nat:
  assumes "prime p"
  shows   "divisor_sigma x (p ^ k) = (if x = 0 then Suc k else
             (p ^ (x * Suc k) - 1) div (p ^ x - 1))"
proof (cases "x = 0")
  case True
  with assms have "nat_power p (real x) = 1" by simp
  hence "divisor_sigma (real x) (p ^ k) = real (Suc k)"
    by (subst divisor_sigma_prime_power_field) (simp_all del: nat_power_real_def add: assms)
  thus ?thesis unfolding divisor_sigma_of_nat by (subst (asm) of_nat_eq_iff) (insert True, simp)
next
  case False
  with assms have gt_1: "p ^ x > 1" 
    using power_gt1[of p "x - 1"] by (simp add: prime_gt_Suc_0_nat)
  hence not_one: "real p ^ x \<noteq> 1" 
    unfolding of_nat_power [symmetric] of_nat_eq_1_iff by (intro notI) simp
  from gt_1 have dvd: "p ^ x - 1 dvd p ^ (x * Suc k) - 1"
    using geometric_sum_nat_dvd[of "p ^ x" "Suc k"] assms
    by (simp add: power_mult prime_gt_Suc_0_nat power_add)
  have "divisor_sigma (real x) (p ^ k) =
          real (if x = 0 then Suc k else (p ^ (x * Suc k) - 1) div (p ^ x - 1))"
    by (subst divisor_sigma_prime_power_field [OF assms, where 'a = real])
       (insert assms False dvd not_one, auto simp del: power_Suc nat_power_real_def 
        simp: prime_gt_0_nat real_of_nat_div of_nat_diff prime_ge_Suc_0_nat power_mult [symmetric])
  thus ?thesis unfolding divisor_sigma_of_nat by (subst (asm) of_nat_eq_iff)
qed

interpretation divisor_sigma_field: 
  multiplicative_function' "divisor_sigma (x :: 'a :: {field, nat_power})"
    "\<lambda>p k. if nat_power p x = 1 then of_nat (Suc k) else 
        (nat_power p x ^ Suc k - 1) / (nat_power p x - 1)"
    "\<lambda>p. nat_power p x + 1"
  by standard (auto simp: divisor_sigma_prime_power_field prime_gt_0_nat field_simps)

interpretation divisor_sigma_real: 
  multiplicative_function' "divisor_sigma (x :: real)"
    "\<lambda>p k. if x = 0 then of_nat (Suc k) else ((real p powr x) ^ Suc k - 1) / (real p powr x - 1)"
    "\<lambda>p. real p powr x + 1"
proof (standard, goal_cases)
  case (1 p k)
  thus ?case
    by (auto simp: divisor_sigma_prime_power_field prime_gt_0_nat powr_def of_nat_eq_1_iff
                   exp_of_nat_mult [symmetric] mult_ac simp del: of_nat_Suc power_Suc)
next
  case (2 p)
  hence "real p powr x \<noteq> 1" if "x \<noteq> 0" by (auto simp: powr_def that prime_gt_0_nat of_nat_eq_1_iff)
  with 2 show ?case by (auto simp: field_simps)
qed

interpretation divisor_sigma_nat: 
  multiplicative_function' "divisor_sigma (x :: nat)"
    "\<lambda>p k. if x = 0 then Suc k else (p ^ (Suc k * x) - 1) div (p ^ x - 1)"
    "\<lambda>p. p ^ x + 1"
proof (standard, goal_cases)
  case (2 p)
  have "(p ^ (x + x) - 1) = (p ^ x + 1) * (p ^ x - 1)"
    by (simp add: algebra_simps power_add)
  moreover have "p ^ x > 1" if "x > 0" using that 2 one_less_power prime_gt_1_nat by blast
  ultimately show ?case using prime_ge_Suc_0_nat[of p] by auto
qed (auto simp: divisor_sigma_prime_power_nat mult_ac)

lemma divisor_sigma_prime:
  assumes "prime p"
  shows   "divisor_sigma x p = nat_power p x + 1"
proof -
  have "divisor_sigma x p = (\<Sum>d | d dvd p. nat_power d x)"
    by (simp add: divisor_sigma_def)
  also from assms have "{d. d dvd p} = {1, p}" by (auto simp: prime_nat_iff)
  also have "(\<Sum>d\<in>\<dots>. nat_power d x) = nat_power p x + 1"
    using assms by (subst sum.insert) (auto simp: add_ac)
  finally show ?thesis .
qed


subsection \<open>The divisor-counting function\<close>

definition divisor_count :: "nat \<Rightarrow> nat" where
  "divisor_count n = card {d. d dvd n}"

lemma divisor_count_0 [simp]: "divisor_count 0 = 0" 
  by (simp add: divisor_count_def)

lemma divisor_count_Suc_0 [simp]: "divisor_count (Suc 0) = 1"
  by (simp add: divisor_count_def)

lemma divisor_sigma_0_left_nat: "divisor_sigma 0 n = divisor_count n"
  by (simp add: divisor_sigma_def divisor_count_def)
    
lemma divisor_sigma_0_left: "divisor_sigma 0 n = of_nat (divisor_count n)"
  unfolding divisor_sigma_0_left_nat [symmetric] divisor_sigma_of_nat [symmetric] by simp

lemma divisor_count_altdef: "divisor_count n = divisor_sigma 0 n"
  by (simp add: divisor_sigma_0_left)

lemma divisor_count_naive [code]:
  "divisor_count n = (if n = 0 then 0 else 
     fold_atLeastAtMost_nat (\<lambda>d acc. if d dvd n then Suc acc else acc) 1 n 0)"
  using divisor_sigma_naive[of "0 :: nat" n] 
  by (simp split: if_splits add: divisor_count_altdef cong: if_cong)

interpretation divisor_count: multiplicative_function' divisor_count "\<lambda>p k. Suc k" "\<lambda>_. 2"
  by standard (simp_all add: divisor_count_altdef divisor_sigma.mult_coprime
                             divisor_sigma_nat.prime_power)

lemma divisor_count_dvd_mono:
  assumes "a dvd b" "b \<noteq> 0"
  shows   "divisor_count a \<le> divisor_count b"
  using assms by (auto simp: divisor_count_def intro!: card_mono intro: dvd_trans)


subsection \<open>The divisor sum function\<close>

definition divisor_sum :: "nat \<Rightarrow> nat" where
  "divisor_sum n = \<Sum>{d. d dvd n}"

lemma divisor_sum_0 [simp]: "divisor_sum 0 = 0" 
  by (simp add: divisor_sum_def)

lemma divisor_sum_Suc_0 [simp]: "divisor_sum (Suc 0) = Suc 0" 
  by (simp add: divisor_sum_def)

lemma divisor_sigma_1_left_nat: "divisor_sigma (Suc 0) n = divisor_sum n"
  by (simp add: divisor_sum_def divisor_sigma_def)

lemma divisor_sigma_1_left: "divisor_sigma 1 n = of_nat (divisor_sum n)"
  by (simp add: divisor_sum_def divisor_sigma_def)

lemma divisor_sum_altdef: "divisor_sum n = divisor_sigma 1 n"
  by (simp add: divisor_sigma_1_left_nat)
    
interpretation divisor_sum: 
  multiplicative_function' divisor_sum "\<lambda>p k. (p ^ Suc k - 1) div (p - 1)" "\<lambda>p. Suc p"
proof (standard, goal_cases)
  case (5 p)
  thus ?case using divisor_sigma_nat.prime_aux[of p 1]
    by (simp_all add: divisor_sum_altdef) 
qed (simp_all add: divisor_sum_altdef divisor_sigma_nat.prime_power divisor_sigma.mult_coprime)

lemma divisor_sum_dvd_mono:
  assumes "a dvd b" "b \<noteq> 0"
  shows   "divisor_sum a \<le> divisor_sum b"
  using assms 
  by (cases "a = 0") (auto simp: divisor_sum_def intro!: sum_le_included intro: dvd_trans)

lemma divisor_sum_naive [code]:
  "divisor_sum n = (if n = 0 then 0 else 
     fold_atLeastAtMost_nat (\<lambda>d acc. if d dvd n then d + acc else acc) 1 n 0)"
  using divisor_sigma_naive[of "Suc 0" n] 
  by (simp split: if_splits add: divisor_sum_altdef cong: if_cong)


lemma fds_divisor_count: "fds divisor_count = fds_zeta ^ 2"
  by (rule fds_eqI) 
     (simp add: fds_nth_mult dirichlet_prod_altdef1 divisor_count_def power2_eq_square)

lemma fds_shift_zeta_1: "fds_shift 1 fds_zeta = fds of_nat"
  by (rule fds_eqI) (simp add: fds_nth_mult)

lemma fds_shift_zeta_Suc_0: "fds_shift (Suc 0) fds_zeta = fds id"
  by (rule fds_eqI) (simp add: fds_nth_mult)

lemma fds_divisor_sum: "fds divisor_sum = fds_zeta * fds id"
  by (rule fds_eqI) (simp add: fds_nth_mult dirichlet_prod_altdef1 divisor_sum_def)
    

lemma fds_divisor_sum_eq_totient_times_d: "fds divisor_sum = fds totient * fds divisor_count"
proof -
  have "fds divisor_sum = fds_zeta * fds id" by (fact fds_divisor_sum)
  also have "fds id = fds totient * fds_zeta" by (rule fds_totient_times_zeta' [symmetric])
  also have "fds_zeta * \<dots> = fds totient * fds divisor_count"
    using fds_divisor_count by (simp add: power2_eq_square mult_ac)
  finally show ?thesis .
qed
   
lemma fds_divisor_sum_times_moebius_mu: 
  "fds (divisor_sigma (1 :: 'a :: {nat_power,comm_ring_1})) * fds moebius_mu = fds of_nat"
proof -
  have "fds (divisor_sigma 1) * fds moebius_mu = 
          fds of_nat * (fds_zeta * fds moebius_mu :: 'a fds)"
    by (subst mult.assoc [symmetric], subst fds_zeta_commutes [symmetric]) 
       (simp add: fds_divisor_sigma fds_shift_zeta_1)
  also have "fds_zeta * fds moebius_mu = (1 :: 'a fds)" by (fact fds_zeta_times_moebius_mu)
  finally show ?thesis by simp
qed

(* Theorem 2.20 *)
lemma inverse_divisor_sigma:
  fixes a :: "'a :: {field, nat_power}"
  shows "inverse (fds (divisor_sigma a)) = fds_shift a (fds moebius_mu) * fds moebius_mu"
proof -
  have "fds (divisor_sigma a) = fds_zeta * fds_shift a fds_zeta"
    by (simp add: fds_divisor_sigma)
  also have "inverse \<dots> = fds moebius_mu * inverse (fds_shift a fds_zeta)"
    by (simp add: fds_moebius_inverse_zeta inverse_mult_fds)
  also have "inverse (fds_shift a fds_zeta) =
               fds (\<lambda>n. moebius_mu n * fds_nth (fds_shift a fds_zeta) n)"
    by (intro completely_multiplicative_fds_inverse', unfold_locales)
       (auto simp: nat_power_mult_distrib)
  also have "\<dots> = fds_shift a (fds moebius_mu)"
    by (auto simp: fds_eq_iff)
  finally show ?thesis by (simp add: mult.commute)
qed

end
