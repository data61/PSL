(*
    File:      Moebius_Mu.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>The M\"{o}bius $\mu$ function\<close>
theory Moebius_Mu
imports
  Main
  "HOL-Number_Theory.Number_Theory"
  "HOL-Computational_Algebra.Squarefree"
  Dirichlet_Series
  Dirichlet_Misc
begin

definition moebius_mu :: "nat \<Rightarrow> 'a :: comm_ring_1" where
  "moebius_mu n = 
     (if squarefree n then (-1) ^ card (prime_factors n) else 0)"
  
lemma abs_moebius_mu_le: "abs (moebius_mu n :: 'a :: {linordered_idom}) \<le> 1"
  by (auto simp add: moebius_mu_def)

lemma moebius_commute: "x * moebius_mu n = moebius_mu n * x"
  by (cases "even (card (prime_factors n))") (auto simp: moebius_mu_def)

lemma dirichlet_prod_moebius_commute: 
  "dirichlet_prod f moebius_mu = dirichlet_prod moebius_mu f"
  by (subst dirichlet_prod_def, subst dirichlet_prod_altdef1) (simp add: moebius_commute)

lemma fds_moebius_commute: "x * fds moebius_mu = fds moebius_mu * x"
  by (simp add: fds_eq_iff fds_nth_mult dirichlet_prod_moebius_commute)

lemma of_int_moebius_mu [simp]: "of_int (moebius_mu n) = moebius_mu n"
  by (simp add: moebius_mu_def)
  
lemma minus_1_power_ring_neq_zero [simp]: "(- 1 :: 'a :: ring_1) ^ n \<noteq> 0"
  by (cases "even n") simp_all

lemma moebius_mu_0 [simp]: "moebius_mu 0 = 0"
  by (simp add: moebius_mu_def)

lemma fds_nth_fds_moebius_mu [simp]: "fds_nth (fds moebius_mu) = moebius_mu"
  by (simp add: fun_eq_iff fds_nth_fds)
    
lemma prime_factors_Suc_0 [simp]: "prime_factors (Suc 0) = {}"
  by (subst prime_factors_dvd) auto
  
lemma moebius_mu_Suc_0 [simp]: "moebius_mu (Suc 0) = 1"
  by (simp add: moebius_mu_def)
    
lemma moebius_mu_1 [simp]: "moebius_mu 1 = 1"
  by (simp add: moebius_mu_def)

lemma moebius_mu_eq_zero_iff: "moebius_mu n = 0 \<longleftrightarrow> \<not>squarefree n"
  by (simp add: moebius_mu_def)
    
lemma moebius_mu_not_squarefree [simp]: "\<not>squarefree n \<Longrightarrow> moebius_mu n = 0"
  by (simp add: moebius_mu_def)

lemma moebius_mu_power:
  assumes "a > 1" "n > 1"
  shows   "moebius_mu (a ^ n) = 0"
proof -
  from assms have "a ^ 2 dvd a ^ n" by (simp add: le_imp_power_dvd)
  with moebius_mu_eq_zero_iff[of "a ^ n"] and \<open>a > 1\<close> show ?thesis by (auto simp: squarefree_def)
qed
  
lemma moebius_mu_power':
  "moebius_mu (a ^ n) = (if a = 1 \<or> n = 0 then 1 else if n = 1 then moebius_mu a else 0)"
  by (cases "a = 0") (auto simp: power_0_left moebius_mu_power)

lemma moebius_mu_squarefree_eq: 
  "squarefree n \<Longrightarrow> moebius_mu n = (-1) ^ card (prime_factors n)"
  by (simp add: moebius_mu_def split: if_splits)

lemma moebius_mu_squarefree_eq': 
  assumes "squarefree n"
  shows   "moebius_mu n = (-1) ^ size (prime_factorization n)"
proof -
  let ?P = "prime_factorization n"
  from assms have [simp]: "n > 0" by (auto intro!: Nat.gr0I)
  have "size ?P = sum (count ?P) (set_mset ?P)" by (rule size_multiset_overloaded_eq)
  also from assms have "\<dots> = sum (\<lambda>_. 1) (set_mset ?P)"
    by (intro sum.cong refl, subst count_prime_factorization_prime)
       (auto simp: moebius_mu_eq_zero_iff squarefree_factorial_semiring')
  also have "\<dots> = card (set_mset ?P)" by simp
  finally show ?thesis by (simp add: moebius_mu_squarefree_eq[OF assms])
qed
 
lemma sum_moebius_mu_divisors:
  assumes "n > 1"
  shows   "(\<Sum>d | d dvd n. moebius_mu d) = (0 :: 'a :: comm_ring_1)"
proof -
  have "(\<Sum>d | d dvd n. moebius_mu d :: int) = 
          (\<Sum>d \<in> Prod ` {P. P \<subseteq> prime_factors n}. moebius_mu d)"
  proof (rule sum.mono_neutral_right; safe?)
    fix A assume A: "A \<subseteq> prime_factors n"
    from A have [simp]: "finite A" by (rule finite_subset) auto
    from A have A': "x > 0" "prime x" if "x \<in> A" for x using that 
      by (auto simp: prime_factors_multiplicity prime_gt_0_nat)
    from A' have A_nz: "\<Prod>A \<noteq> 0" by (intro notI) auto
    from A' have "prime_factorization (\<Prod>A) = sum prime_factorization A"
      by (subst prime_factorization_prod) (auto dest: finite_subset)
    also from A' have "\<dots> = sum (\<lambda>x. {#x#}) A"
      by (intro sum.cong refl) (auto simp: prime_factorization_prime)
    also have "\<dots> = mset_set A" by simp
    also from A have "\<dots> \<subseteq># mset_set (prime_factors n)"
      by (rule subset_imp_msubset_mset_set) simp_all
    also have "\<dots> \<subseteq># prime_factorization n" by (rule mset_set_set_mset_msubset)
    finally show "\<Prod>A dvd n" using A_nz
      by (intro prime_factorization_subset_imp_dvd) auto
  next
    fix x assume x: "x \<notin> Prod ` {P. P \<subseteq> prime_factors n}" "x dvd n"
    from x assms have [simp]: "x > 0" by (auto intro!: Nat.gr0I)
    {
      assume nz: "moebius_mu x \<noteq> 0"
      have "(\<Prod>(set_mset (prime_factorization x))) = (\<Prod>p\<in>prime_factors x. p ^ multiplicity p x)"
        using nz by (intro prod.cong refl)
                    (auto simp: moebius_mu_eq_zero_iff squarefree_factorial_semiring')
      also have "\<dots> = x" by (intro Primes.prime_factorization_nat [symmetric]) auto
      finally have "x = \<Prod>(prime_factors x)" "prime_factors x \<subseteq> prime_factors n"
        using dvd_prime_factors[of n x] assms \<open>x dvd n\<close> by auto
      hence "x \<in> Prod ` {P. P \<subseteq> prime_factors n}" by blast
      with x(1) have False by contradiction
    }
    thus "moebius_mu x = 0" by blast
  qed (insert assms, auto)
  also have "\<dots> = (\<Sum>P | P \<subseteq> prime_factors n. moebius_mu (\<Prod>P))"
    by (subst sum.reindex) (auto intro!: inj_on_Prod_primes dest: finite_subset)
  also have "\<dots> = (\<Sum>P | P \<subseteq> prime_factors n. (-1) ^ card P)"
  proof (intro sum.cong refl)
    fix P assume P: "P \<in> {P. P \<subseteq> prime_factors n}"
    hence [simp]: "finite P" by (auto dest: finite_subset)
    from P have prime: "prime p" if "p \<in> P" for p using that by (auto simp: prime_factors_dvd)
    hence "squarefree (\<Prod>P)"
      by (intro squarefree_prod_coprime prime_imp_coprime squarefree_prime)
         (auto simp: primes_dvd_imp_eq)
    hence "moebius_mu (\<Prod>P) = (-1) ^ card (prime_factors (\<Prod>P))"
      by (rule moebius_mu_squarefree_eq)
    also from P have "prime_factors (\<Prod>P) = P"
      by (subst prime_factors_prod) (auto simp: prime_factorization_prime prime)
    finally show  "moebius_mu (\<Prod>P) = (-1) ^ card P" .
  qed
  also have "{P. P \<subseteq> prime_factors n} = 
               {P. P \<subseteq> prime_factors n \<and> even (card P)} \<union> {P. P \<subseteq> prime_factors n \<and> odd (card P)}"
    (is "_ = ?A \<union> ?B") by blast
  also have "(\<Sum>P \<in> \<dots>. (-1) ^ card P) = (\<Sum>P \<in> ?A. (-1) ^ card P) + (\<Sum>P \<in> ?B. (-1) ^ card P)"
    by (intro sum.union_disjoint) auto
  also have "(\<Sum>P \<in> ?A. (-1) ^ card P :: int) = (\<Sum>P \<in> ?A. 1)" by (intro sum.cong refl) auto
  also have "\<dots> = int (card ?A)" by simp
  also have "(\<Sum>P \<in> ?B. (-1) ^ card P :: int) = (\<Sum>P \<in> ?B. -1)" by (intro sum.cong refl) auto
  also have "\<dots> = -int (card ?B)" by simp
  also have "card ?B = card ?A" 
    by (rule card_even_odd_subset [symmetric]) 
       (insert assms, auto simp: prime_factorization_empty_iff)
  also have "int (card ?A) + (- int (card ?A)) = 0" by simp
  finally have "(\<Sum>d | d dvd n. of_int (moebius_mu d) :: 'a) = 0"
    unfolding of_int_sum [symmetric] by (simp only: of_int_0)
  thus ?thesis by simp
qed

lemma sum_moebius_mu_divisors':
  "(\<Sum>d | d dvd n. moebius_mu d) = (if n = 1 then 1 else 0)"
proof -
  have "n = 0 \<or> n = 1 \<or> n > 1" by force
  thus ?thesis using sum_moebius_mu_divisors[of n] by auto
qed

lemma fds_zeta_times_moebius_mu: "fds_zeta * fds moebius_mu = 1"
proof
  fix n :: nat assume n: "n > 0"
  from n have "fds_nth (fds_zeta * fds moebius_mu :: 'a fds) n = (\<Sum>d | d dvd n. moebius_mu d)"
    unfolding fds_nth_mult dirichlet_prod_altdef1
    by (intro sum.cong refl) (auto simp: fds_nth_fds elim: dvdE)
  also have "\<dots> = fds_nth 1 n" by (simp add: sum_moebius_mu_divisors')
  finally show "fds_nth (fds_zeta * fds moebius_mu :: 'a fds) n = fds_nth 1 n" .
qed

lemma fds_moebius_inverse_zeta:
  "fds moebius_mu = inverse (fds_zeta :: 'a :: field fds)"
  by (rule fds_right_inverse_unique) (simp add: fds_zeta_times_moebius_mu)

lemma moebius_mu_formula_real: "(moebius_mu n :: real) = dirichlet_inverse (\<lambda>_. 1) 1 n"
proof -
  have "moebius_mu n = (fds_nth (fds moebius_mu) n :: real)" by simp
  also have "fds moebius_mu = (inverse fds_zeta :: real fds)" by (fact fds_moebius_inverse_zeta)
  also have "fds_nth \<dots> n = dirichlet_inverse (fds_nth fds_zeta) 1 n"
    unfolding fds_nth_inverse by simp
  also have "\<dots> = dirichlet_inverse (\<lambda>_. 1) 1 n" by (rule dirichlet_inverse_cong) simp_all
  finally show ?thesis .
qed

lemma moebius_mu_formula_int: "moebius_mu n = dirichlet_inverse (\<lambda>_. 1 :: int) 1 n"
proof -
  have "real_of_int (moebius_mu n) = moebius_mu n" by simp
  also have "\<dots> = dirichlet_inverse (\<lambda>_. 1) 1 n" by (fact moebius_mu_formula_real)
  also have "\<dots> = real_of_int (dirichlet_inverse (\<lambda>_. 1) 1 n)"
    by (induction n rule: dirichlet_inverse_induct) (simp_all add: dirichlet_inverse_gt_1)
  finally show ?thesis by (subst (asm) of_int_eq_iff)
qed

lemma moebius_mu_formula: "moebius_mu n = dirichlet_inverse (\<lambda>_. 1) 1 n"
  by (subst of_int_moebius_mu [symmetric], subst moebius_mu_formula_int)
     (simp add: of_int_dirichlet_inverse)

interpretation moebius_mu: multiplicative_function moebius_mu
proof -
  have "multiplicative_function (dirichlet_inverse (\<lambda>n. if n = 0 then 0 else 1 :: 'a) 1)"
    by (rule multiplicative_dirichlet_inverse, standard) simp_all
  also have "dirichlet_inverse (\<lambda>n. if n = 0 then 0 else 1 :: 'a) 1 = moebius_mu"
    by (auto simp: fun_eq_iff moebius_mu_formula)
  finally show "multiplicative_function (moebius_mu :: nat \<Rightarrow> 'a)" .
qed

interpretation moebius_mu: 
  multiplicative_function' moebius_mu "\<lambda>p k. if k = 1 then -1 else 0" "\<lambda>_. -1"
proof
  fix p k :: nat assume "prime p" "k > 0"
  moreover from this have "moebius_mu p = -1" 
    by (simp add: moebius_mu_def prime_factorization_prime squarefree_prime)
  ultimately show "moebius_mu (p ^ k) = (if k = 1 then - 1 else 0)"
    by (auto simp: moebius_mu_power')
qed auto
  
lemma moebius_mu_2 [simp]: "moebius_mu 2 = -1"
  and moebius_mu_3 [simp]: "moebius_mu 3 = -1"
  by (rule moebius_mu.prime; simp)+


lemma moebius_mu_code [code]:
  "moebius_mu n = of_int (dirichlet_inverse (\<lambda>_. 1 :: int) 1 n)"
  by (subst moebius_mu_formula_int [symmetric]) simp


lemma fds_moebius_inversion: "f = fds moebius_mu * g \<longleftrightarrow> g = f * fds_zeta"
proof
  assume "g = f * fds_zeta"
  hence "g * fds moebius_mu = f * (fds_zeta * fds moebius_mu)" by (simp add: mult_ac)
  also have "\<dots> = f" by (simp add: fds_zeta_times_moebius_mu)
  finally show "f = fds moebius_mu * g" by (simp add: mult_ac)
next
  assume "f = fds moebius_mu * g"
  hence "fds_zeta * f = fds_zeta * fds moebius_mu * g" by (simp add: mult_ac)
  also have "\<dots> = g" by (simp add: fds_zeta_times_moebius_mu)
  finally show "g = f * fds_zeta" by (simp add: mult_ac)
qed

lemma moebius_inversion:
  assumes "\<And>n. n > 0 \<Longrightarrow> g n = (\<Sum>d | d dvd n. f d)" "n > 0"
  shows   "f n = dirichlet_prod moebius_mu g n"
proof -
  from assms have "fds g = fds f * fds_zeta"
    by (intro fds_eqI) (simp add: fds_nth_mult dirichlet_prod_def)
  thus ?thesis using assms
    by (subst (asm) fds_moebius_inversion [symmetric]) (simp add: fds_eq_iff fds_nth_mult)
qed

lemma fds_mangoldt: "fds mangoldt = fds moebius_mu * fds (\<lambda>n. of_real (ln (real n)))"
  by (subst fds_moebius_inversion) (rule fds_mangoldt_times_zeta [symmetric])

(* 2.18 *)
lemma sum_divisors_moebius_mu_times_multiplicative:
  fixes f :: "nat \<Rightarrow> 'a :: {comm_ring_1}"
  assumes "multiplicative_function f" "n > 0"
  shows   "(\<Sum>d | d dvd n. moebius_mu d * f d) = (\<Prod>p\<in>prime_factors n. 1 - f p)"
proof -
  define g where "g = (\<lambda>n. \<Sum>d | d dvd n. moebius_mu d * f d)"
  define g' where "g' = dirichlet_prod (\<lambda>n. moebius_mu n * f n) (\<lambda>n. if n = 0 then 0 else 1)"
  interpret f: multiplicative_function f by fact
  have "multiplicative_function (\<lambda>n. if n = 0 then 0 else 1 :: 'a)"
    by standard auto
  interpret multiplicative_function g' unfolding g'_def
    by (intro multiplicative_dirichlet_prod multiplicative_function_mult
              moebius_mu.multiplicative_function_axioms assms) fact+

  have g'_primepow: "g' (p ^ k) = 1 - f p" if "prime p" "k > 0" for p k
  proof -
    have "g' (p ^ k) = (\<Sum>i\<le>k. moebius_mu (p ^ i) * f (p ^ i))"
      using that by (simp add: g'_def dirichlet_prod_prime_power)
    also have "\<dots> = (\<Sum>i\<in>{0, 1}. moebius_mu (p ^ i) * f (p ^ i))"
      using that by (intro sum.mono_neutral_right) (auto simp: moebius_mu_power')
    also have "\<dots> = 1 - f p"
      using that by (simp add: moebius_mu.prime)
    finally show ?thesis .
  qed

  have "g' n = g n"
    by (simp add: g_def g'_def dirichlet_prod_def)
  also from assms have "g' n = (\<Prod>p\<in>prime_factors n. g' (p ^ multiplicity p n))"
      by (intro prod_prime_factors) auto
  also have "\<dots> = (\<Prod>p\<in>prime_factors n. 1 - f p)"
    by (intro prod.cong) (auto simp: g'_primepow prime_factors_multiplicity)
  finally show ?thesis by (simp add: g_def)
qed
  

(* Theorem 2.17 *)
lemma completely_multiplicative_iff_inverse_moebius_mu:
  fixes f :: "nat \<Rightarrow> 'a :: {comm_ring_1, ring_no_zero_divisors}"
  assumes "multiplicative_function f"
  defines "g \<equiv> dirichlet_inverse f 1"
  shows   "completely_multiplicative_function f \<longleftrightarrow>
             (\<forall>n. g n = moebius_mu n * f n)"
proof -
  interpret multiplicative_function f by fact
  show ?thesis
  proof safe
    assume "completely_multiplicative_function f"
    then interpret completely_multiplicative_function f .
    have [simp]: "fds f \<noteq> 0" by (auto simp: fds_eq_iff)

    have "fds (\<lambda>n. moebius_mu n * f n) * fds f = 1"
    proof
      fix n :: nat
      have "fds_nth (fds (\<lambda>n. moebius_mu n * f n) * fds f) n =
              (\<Sum>(r, d) | r * d = n. moebius_mu r * f (r * d))"
        by (simp add: fds_eq_iff fds_nth_mult fds_nth_fds dirichlet_prod_altdef2 mult mult.assoc)
      also have "\<dots> = (\<Sum>(r, d) | r * d = n. moebius_mu r * f n)"
        by (intro sum.cong) auto
      also have "\<dots> = dirichlet_prod moebius_mu (\<lambda>_. 1) n * f n"
        by (simp add: dirichlet_prod_altdef2 sum_distrib_right case_prod_unfold mult)
      also have "dirichlet_prod moebius_mu (\<lambda>_. 1) n = fds_nth (fds moebius_mu * fds_zeta) n"
        by (simp add: fds_nth_mult)
      also have "fds moebius_mu * fds_zeta = 1"
        by (simp add: mult_ac fds_zeta_times_moebius_mu)
      also have "fds_nth 1 n * f n = fds_nth 1 n"
        by (auto simp: fds_eq_iff fds_nth_one)
      finally show "fds_nth (fds (\<lambda>n. moebius_mu n * f n) * fds f) n = fds_nth 1 n" .
    qed
    also have "1 = fds g * fds f"
      by (auto simp: fds_eq_iff g_def fds_nth_mult dirichlet_prod_inverse')
    finally have "fds g = fds (\<lambda>n. moebius_mu n * f n)"
      by (subst (asm) mult_cancel_right) auto
    thus "g n = moebius_mu n * f n" for n
      by (cases "n = 0") (auto simp: fds_eq_iff g_def)
  next
    assume g: "\<forall>n. g n = moebius_mu n * f n"
    show "completely_multiplicative_function f"
    proof (rule completely_multiplicativeI)
      fix p k :: nat assume pk: "prime p" "k > 0"
      show "f (p ^ k) = f p ^ k"
      proof (induction k)
        case (Suc k)
        have eq: "dirichlet_prod g f n = 0" if "n \<noteq> 1" for n
          unfolding g_def using dirichlet_prod_inverse'[of f 1] that by auto
        have "dirichlet_prod g f (p ^ Suc k) = 0"
          using pk by (intro eq) auto
        also have "dirichlet_prod g f (p ^ Suc k) = (\<Sum>i\<le>Suc k. g (p ^ i) * f (p ^ (Suc k - i)))"
          by (intro dirichlet_prod_prime_power) fact+
        also have "\<dots> = (\<Sum>i\<le>Suc k. moebius_mu (p ^ i) * f (p ^ i) * f (p ^ (Suc k - i)))"
          by (intro sum.cong refl, subst g) auto
        also have "\<dots> = (\<Sum>i\<in>{0, 1}. moebius_mu (p ^ i) * f (p ^ i) * f (p ^ (Suc k - i)))"
          using pk by (intro sum.mono_neutral_right) (auto simp: moebius_mu_power')
        also have "\<dots> = f (p ^ Suc k) - f p ^ Suc k"
          using pk Suc.IH by (auto simp: moebius_mu.prime)
        finally show "f (p ^ Suc k) = f p ^ Suc k" by simp
      qed auto
    qed
  qed
qed

lemma completely_multiplicative_fds_inverse:
  fixes f :: "nat \<Rightarrow> 'a :: field"
  assumes "completely_multiplicative_function f"
  shows   "inverse (fds f) = fds (\<lambda>n. moebius_mu n * f n)"
proof -
  interpret completely_multiplicative_function f by fact
  from assms show ?thesis
    by (subst (asm) completely_multiplicative_iff_inverse_moebius_mu)
       (auto simp: inverse_fds_def multiplicative_function_axioms)
qed

lemma completely_multiplicative_fds_inverse':
  fixes f :: "'a :: field fds"
  assumes "completely_multiplicative_function (fds_nth f)"
  shows   "inverse f = fds (\<lambda>n. moebius_mu n * fds_nth f n)"
proof -
  have "f = fds (fds_nth f)" by simp
  also have "inverse (fds (fds_nth f)) = fds (\<lambda>n. moebius_mu n * fds_nth f n)"
    by (intro completely_multiplicative_fds_inverse assms)
  finally show ?thesis by simp
qed
    

context
  includes fds_syntax
begin

lemma selberg_aux:
  "(\<chi> n. of_real ((ln n)\<^sup>2)) * fds moebius_mu =
     (fds mangoldt)\<^sup>2 - fds_deriv (fds mangoldt :: 'a :: {comm_ring_1,real_algebra_1} fds)"
proof -
  have "(\<chi> n. of_real (ln (real n) ^ 2)) = fds_deriv (fds_deriv fds_zeta :: 'a fds)"
    by (rule fds_eqI) (simp add: fds_nth_fds fds_nth_deriv power2_eq_square scaleR_conv_of_real)
  also have "\<dots> = (fds mangoldt ^ 2 - fds_deriv (fds mangoldt)) * fds_zeta"
    by (simp add: fds_deriv_zeta algebra_simps power2_eq_square)
  also have "\<dots> * fds moebius_mu = ((fds mangoldt)\<^sup>2 - fds_deriv (fds mangoldt)) * 
                                      (fds_zeta * fds moebius_mu)" by (simp add: mult_ac)
  also have "fds_zeta * fds moebius_mu = (1 :: 'a fds)" by (fact fds_zeta_times_moebius_mu)
  finally show ?thesis by simp
qed
  
lemma selberg_aux':
  "mangoldt n * of_real (ln n) + (mangoldt \<star> mangoldt) n =
     ((moebius_mu \<star> (\<lambda>b. of_real (ln b) ^ 2)) n
         :: 'a :: {comm_ring_1,real_algebra_1})" if "n > 0"
  using selberg_aux [symmetric] that 
  by (auto simp add: fds_eq_iff fds_nth_mult power2_eq_square fds_nth_deriv
        dirichlet_prod_commutes algebra_simps scaleR_conv_of_real)

end

end
