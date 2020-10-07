(*
    File:      Liouville_Lambda.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>The Liouville $\lambda$ function\<close>
theory Liouville_Lambda
  imports 
    "HOL-Computational_Algebra.Computational_Algebra"
    "HOL-Number_Theory.Number_Theory"
    Dirichlet_Series
    Multiplicative_Function 
    Moebius_Mu
begin

definition liouville_lambda :: "nat \<Rightarrow> 'a :: comm_ring_1" where
  "liouville_lambda n = (if n = 0 then 0 else (-1) ^ size (prime_factorization n))"

interpretation liouville_lambda: completely_multiplicative_function' liouville_lambda "\<lambda>_. -1"
proof
  fix a b :: nat assume "a > 1" "b > 1"
  thus "liouville_lambda (a * b) = liouville_lambda a * liouville_lambda b"
    by (simp add: liouville_lambda_def prime_factorization_mult power_add)
qed (simp_all add: liouville_lambda_def prime_factorization_prime One_nat_def [symmetric] 
              del: One_nat_def)

lemma liouville_lambda_prime [simp]: "prime p \<Longrightarrow> liouville_lambda p = -1"
  by (simp add: liouville_lambda_def prime_factorization_prime)

lemma liouville_lambda_prime_power [simp]: "prime p \<Longrightarrow> liouville_lambda (p ^ k) = (-1) ^ k"
  by (simp add: liouville_lambda_def prime_factorization_prime_power)

lemma liouville_lambda_squarefree: "squarefree n \<Longrightarrow> liouville_lambda n = moebius_mu n"
  by (auto simp: liouville_lambda_def moebius_mu_squarefree_eq' intro!: Nat.gr0I)

lemma power_neg_one_If: "(-1) ^ n = (if even n then 1 else -1 :: 'a :: ring_1)"
  by (induction n) (simp_all split: if_splits)

lemma liouville_lambda_power_even: 
  "n > 0 \<Longrightarrow> even m \<Longrightarrow> liouville_lambda (n ^ m) = 1"
  by (subst liouville_lambda.power) (auto elim!: evenE simp: liouville_lambda_def power_neg_one_If)

lemma liouville_lambda_power_odd: 
  "odd m \<Longrightarrow> liouville_lambda (n ^ m) = liouville_lambda n"
  by (subst liouville_lambda.power) (auto elim!: oddE simp: liouville_lambda_def power_neg_one_If)
    
lemma liouville_lambda_power:
  "liouville_lambda (n ^ m) = 
     (if n = 0 \<and> m > 0 then 0 else if even m then 1 else liouville_lambda n)"
  by (auto simp: liouville_lambda_power_even liouville_lambda_power_odd power_0_left)
                                      
interpretation squarefree: multiplicative_function' 
  "ind squarefree" "\<lambda>p k. if k > 1 then 0 else 1" "\<lambda>_. 1"
proof
  fix p k :: nat assume "prime p" "k > 0"
  thus "ind squarefree (p ^ k) = (if 1 < k then 0 else 1 :: 'a)"
    by (cases "k = 1") (auto simp: squarefree_power_iff squarefree_prime ind_def)
qed (auto simp: squarefree_mult_coprime squarefree_power_iff ind_def dest: squarefree_multD 
          simp del: One_nat_def)
        

interpretation is_nth_power: multiplicative_function "ind (is_nth_power n)"
  by standard (auto simp: is_nth_power_mult_coprime_nat_iff)

interpretation is_nth_power: multiplicative_function' 
  "ind (is_nth_power n)" "\<lambda>p k. if n dvd k then 1 else 0" "\<lambda>_. if n = 1 then 1 else 0"
  by standard (simp_all add: is_nth_power_prime_power_nat_iff ind_def)

interpretation is_square: multiplicative_function "ind is_square"
  by standard (auto simp: is_nth_power_mult_coprime_nat_iff)

interpretation is_square: multiplicative_function' 
  "ind is_square" "\<lambda>p k. if even k then 1 else 0" "\<lambda>_. 0"
  by standard (simp_all add: is_nth_power_prime_power_nat_iff ind_def)


lemma liouville_lambda_divisors_sum:
  "(\<Sum>d | d dvd n. liouville_lambda d) = ind is_square n"
proof (rule multiplicative_function_eqI)
  show "multiplicative_function (\<lambda>n. (\<Sum>d | d dvd n. liouville_lambda d))"
    by (rule liouville_lambda.multiplicative_sum_divisors)
  show "multiplicative_function (ind is_square)"
    by (rule is_nth_power.multiplicative_function_axioms)
next
  fix p k :: nat assume pk: "prime p" "k > 0"
  hence p_gt_1: "p > 1" by (simp add: prime_gt_Suc_0_nat)
  have "(\<Sum>d | d dvd p ^ k. liouville_lambda d) = (\<Sum>d\<in>(\<lambda>i. p ^ i) ` {..k}. liouville_lambda d)"
    using pk by (intro sum.cong refl) (auto intro: le_imp_power_dvd simp: divides_primepow_nat)
  also from pk and p_gt_1 have "\<dots> = (\<Sum>i\<le>k. liouville_lambda (p ^ i))"
    by (subst sum.reindex) (auto simp: inj_on_def prime_gt_1_nat)
  also from pk have "\<dots> = (\<Sum>i\<le>k. (-1) ^ i)" by (intro sum.cong refl) simp
  also have "\<dots> = (if even k then 1 else 0)" by (induction k) auto
  also from pk have "\<dots> = ind is_square (p ^ k)" by (simp add: is_square.prime_power)
  finally show "(\<Sum>d | d dvd p ^ k. liouville_lambda d) = ind is_square (p ^ k)" .
qed

lemma fds_liouville_lambda_times_zeta: "fds liouville_lambda * fds_zeta = fds_ind is_square"
  by (rule fds_eqI) (simp add: liouville_lambda_divisors_sum fds_nth_mult dirichlet_prod_def)

lemma fds_liouville_lambda: "fds liouville_lambda = fds_ind is_square * fds moebius_mu"
proof -
  have "fds liouville_lambda * fds_zeta * fds moebius_mu = fds_ind is_square * fds moebius_mu"
    by (simp add: fds_liouville_lambda_times_zeta)
  also have "fds liouville_lambda * fds_zeta * fds moebius_mu = fds liouville_lambda"
    by (simp only: mult.assoc fds_zeta_times_moebius_mu mult_1_right)
  finally show ?thesis .
qed

lemma liouville_lambda_altdef:
  "liouville_lambda n = (\<Sum>d | d ^ 2 dvd n. moebius_mu (n div d ^ 2))"
proof (cases "n = 0")
  case False
  have "liouville_lambda n = fds_nth (fds liouville_lambda) n" by (simp add: fds_nth_fds)
  also have "fds liouville_lambda = fds_ind is_square * (fds moebius_mu :: 'a fds)" 
    by (rule fds_liouville_lambda)
  also have "fds_nth \<dots> n = (\<Sum>d | d dvd n. ind is_square d * moebius_mu (n div d))"
    by (simp add: fds_nth_mult dirichlet_prod_def)
  also have "\<dots> = (\<Sum>d \<in> (\<lambda>d. d^2) ` {d. d ^ 2 dvd n}. moebius_mu (n div d))" using False
    by (intro sum.mono_neutral_cong_right) (auto simp: ind_def is_nth_power_def)
  also have "\<dots> = (\<Sum>d | d ^ 2 dvd n. moebius_mu (n div d ^ 2))"
    by (subst sum.reindex) (auto simp: inj_on_def dest: power2_eq_imp_eq)
  finally show ?thesis .
qed auto

lemma abs_moebius_mu: "abs (moebius_mu n :: 'a :: linordered_idom) = ind squarefree n"
  by (auto simp: ind_def moebius_mu_def)

end
