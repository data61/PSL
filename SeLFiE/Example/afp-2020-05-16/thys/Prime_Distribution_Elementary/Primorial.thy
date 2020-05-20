(*
  File:    Primorial.thy
  Author:  Manuel Eberl, TU München

  The primorial function x#, i.\,e. the product of all primes no greater than x.
*)
section \<open>The Primorial function\<close>
theory Primorial
  imports Prime_Distribution_Elementary_Library Primes_Omega
begin

subsection \<open>Definition and basic properties\<close>

definition primorial :: "real \<Rightarrow> nat" where
  "primorial x = \<Prod>{p. prime p \<and> real p \<le> x}"

lemma primorial_mono: "x \<le> y \<Longrightarrow> primorial x \<le> primorial y"
  unfolding primorial_def
  by (intro dvd_imp_le prod_dvd_prod_subset)
     (auto intro!: prod_pos finite_primes_le dest: prime_gt_0_nat)

lemma prime_factorization_primorial:
  "prime_factorization (primorial x) = mset_set {p. prime p \<and> real p \<le> x}"
proof (intro multiset_eqI)
  fix p :: nat
  note fin = finite_primes_le[of x]
  show "count (prime_factorization (primorial x)) p =
          count (mset_set {p. prime p \<and> real p \<le> x}) p"
  proof (cases "prime p")
    case True
    hence "count (prime_factorization (primorial x)) p =
             sum (multiplicity p) {p. prime p \<and> real p \<le> x}"
      unfolding primorial_def count_prime_factorization using fin
      by (subst prime_elem_multiplicity_prod_distrib) auto
    also from True have "\<dots> = sum (\<lambda>_. 1) (if p \<le> x then {p} else {})" using fin
      by (intro sum.mono_neutral_cong_right) (auto simp: prime_multiplicity_other split: if_splits)
    also have "\<dots> = count (mset_set {p. prime p \<and> real p \<le> x}) p"
      using True fin by auto
    finally show ?thesis .
  qed auto
qed

lemma prime_factors_primorial [simp]:
  "prime_factors (primorial x) = {p. prime p \<and> real p \<le> x}"
  unfolding prime_factorization_primorial using finite_primes_le[of x] by simp

lemma primorial_pos [simp, intro]: "primorial x > 0"
  unfolding primorial_def by (intro prod_pos) (auto dest: prime_gt_0_nat)

lemma primorial_neq_zero [simp]: "primorial x \<noteq> 0"
  by auto

lemma of_nat_primes_omega_primorial [simp]: "real (primes_omega (primorial x)) = primes_pi x"
  by (simp add: primes_omega_def primes_pi_def prime_sum_upto_def)

lemma primes_omega_primorial: "primes_omega (primorial x) = nat \<lfloor>primes_pi x\<rfloor>"
  by (simp add: primes_omega_def primes_pi_def prime_sum_upto_def)

lemma prime_dvd_primorial_iff: "prime p \<Longrightarrow> p dvd primorial x \<longleftrightarrow> p \<le> x"
  using finite_primes_le[of x]
  by (auto simp: primorial_def prime_dvd_prod_iff dest: primes_dvd_imp_eq)

lemma squarefree_primorial [intro]: "squarefree (primorial x)"
  unfolding primorial_def
  by (intro squarefree_prod_coprime) (auto simp: squarefree_prime intro: primes_coprime)

lemma primorial_ge: "primorial x \<ge> 2 powr primes_pi x"
proof -
  have "2 powr primes_pi x = real (\<Prod>p | prime p \<and> real p \<le> x. 2)"
    by (simp add: primes_pi_def prime_sum_upto_def powr_realpow)
  also have "(\<Prod>p | prime p \<and> real p \<le> x. 2) \<le> (\<Prod>p | prime p \<and> real p \<le> x. p)"
    by (intro prod_mono) (auto dest: prime_gt_1_nat)
  also have "\<dots> = primorial x" by (simp add: primorial_def)
  finally show ?thesis by simp
qed

lemma primorial_at_top: "filterlim primorial at_top at_top"
proof -
  have "filterlim (\<lambda>x. real (primorial x)) at_top at_top"
  proof (rule filterlim_at_top_mono)
    show "eventually (\<lambda>x. primorial x \<ge> 2 powr primes_pi x) at_top"
      by (intro always_eventually primorial_ge allI)
    have "filterlim (\<lambda>x. exp (ln 2 * primes_pi x)) at_top at_top"
      by (intro filterlim_compose[OF exp_at_top]
                filterlim_tendsto_pos_mult_at_top[OF tendsto_const] \<pi>_at_top) auto
    thus "filterlim (\<lambda>x. 2 powr primes_pi x) at_top at_top"
      by (simp add: powr_def mult_ac)
  qed
  thus ?thesis unfolding filterlim_sequentially_iff_filterlim_real [symmetric] .
qed

lemma totient_primorial:
  "real (totient (primorial x)) =
     real (primorial x) * (\<Prod>p | prime p \<and> real p \<le> x. 1 - 1 / real p)" for x
proof -
  have "real (totient (primorial x)) =
          primorial x * (\<Prod>p\<in>prime_factors (primorial x). 1 - 1 / p)"
    by (rule totient_formula2)
  thus ?thesis by simp
qed

lemma ln_primorial: "ln (primorial x) = primes_theta x"
proof -
  have "finite {p. prime p \<and> real p \<le> x}"
    by (rule finite_subset[of _ "{..nat \<lfloor>x\<rfloor>}"]) (auto simp: le_nat_iff le_floor_iff)
  thus ?thesis unfolding of_nat_prod primorial_def
    by (subst ln_prod) (auto dest: prime_gt_0_nat simp: \<theta>_def prime_sum_upto_def)
qed

lemma divisor_count_primorial: "divisor_count (primorial x) = 2 powr primes_pi x"
proof -
  have "divisor_count (primorial x) = (\<Prod>p | prime p \<and> real p \<le> x. divisor_count p)"
    unfolding primorial_def
    by (subst divisor_count.prod_coprime) (auto simp: primes_coprime)
  also have "\<dots> = (\<Prod>p | prime p \<and> real p \<le> x. 2)"
    by (intro prod.cong divisor_count.prime) auto
  also have "\<dots> = 2 powr primes_pi x"
    by (simp add: primes_pi_def prime_sum_upto_def powr_realpow)
  finally show ?thesis .
qed


subsection \<open>An alternative view on primorials\<close>

text \<open>
  The following function is an alternative representation of primorials; instead of taking
  the product of all primes up to a given real bound \<open>x\<close>, it takes the product of the first
  \<open>k\<close> primes. This is sometimes more convenient.
\<close>
definition primorial' :: "nat \<Rightarrow> nat" where
  "primorial' n = (\<Prod>k<n. nth_prime k)"

lemma primorial'_0 [simp]: "primorial' 0 = 1"
  and primorial'_1 [simp]: "primorial' 1 = 2"
  and primorial'_2 [simp]: "primorial' 2 = 6"
  and primorial'_3 [simp]: "primorial' 3 = 30"
  by (simp_all add: primorial'_def lessThan_nat_numeral)

lemma primorial'_Suc: "primorial' (Suc n) = nth_prime n * primorial' n"
  by (simp add: primorial'_def)

lemma primorial'_pos [intro]: "primorial' n > 0"
  unfolding primorial'_def by (auto intro: prime_gt_0_nat)

lemma primorial'_neq_0 [simp]: "primorial' n \<noteq> 0"
  by auto

lemma strict_mono_primorial': "strict_mono primorial'"
  unfolding strict_mono_Suc_iff
proof
  fix n :: nat
  have "primorial' n * 1 < primorial' n * nth_prime n"
    using prime_gt_1_nat[OF prime_nth_prime[of n]]
    by (intro mult_strict_left_mono) auto
  thus "primorial' n < primorial' (Suc n)"
    by (simp add: primorial'_Suc)
qed

lemma prime_factorization_primorial':
  "prime_factorization (primorial' k) = mset_set (nth_prime ` {..<k})"
proof -
  have "prime_factorization (primorial' k) = (\<Sum>i<k. prime_factorization (nth_prime i))"
    unfolding primorial'_def by (subst prime_factorization_prod) (auto intro: prime_gt_0_nat)
  also have "\<dots> = (\<Sum>i<k. {#nth_prime i#})"
    by (intro sum.cong prime_factorization_prime) auto
  also have "\<dots> = (\<Sum>p\<in>nth_prime ` {..<k}. {#p#})"
    by (subst sum.reindex) (auto intro: inj_onI)
  also have "\<dots> = mset_set (nth_prime ` {..<k})"
    by simp
  finally show ?thesis .
qed

lemma prime_factors_primorial': "prime_factors (primorial' k) = nth_prime ` {..<k}"
  by (simp add: prime_factorization_primorial')

lemma primes_omega_primorial' [simp]: "primes_omega (primorial' k) = k"
  unfolding primes_omega_def prime_factors_primorial' by (subst card_image) (auto intro: inj_onI)

lemma squarefree_primorial' [intro]: "squarefree (primorial' x)"
  unfolding primorial'_def
  by (intro squarefree_prod_coprime) (auto intro: squarefree_prime intro: primes_coprime)

lemma divisor_count_primorial' [simp]: "divisor_count (primorial' k) = 2 ^ k"
  by (subst divisor_count_squarefree) auto

lemma totient_primorial':
  "totient (primorial' k) = primorial' k * (\<Prod>i<k. 1 - 1 / nth_prime i)"
  unfolding totient_formula2 prime_factors_primorial'
  by (subst prod.reindex) (auto intro: inj_onI)

lemma primorial_conv_primorial': "primorial x = primorial' (nat \<lfloor>primes_pi x\<rfloor>)"
  unfolding primorial_def primorial'_def
proof (rule prod.reindex_bij_witness[of _ nth_prime "\<lambda>p. nat \<lfloor>primes_pi (real p)\<rfloor> - 1"])
  fix p assume p: "p \<in> {p. prime p \<and> real p \<le> x}"
  have [simp]: "primes_pi 2 = 1" by (auto simp: eval_\<pi>)
  have "primes_pi p \<ge> 1"
    using p \<pi>_mono[of 2 "real p"] by (auto dest!: prime_gt_1_nat)
  with p show "nth_prime (nat \<lfloor>primes_pi p\<rfloor> - 1) = p"
    using \<pi>_pos[of "real p"]
    by (intro nth_prime_eqI'')
       (auto simp: le_nat_iff le_floor_iff primes_pi_def prime_sum_upto_def of_nat_diff)
  from p have "nat \<lfloor>primes_pi (real p)\<rfloor> \<le> nat \<lfloor>primes_pi x\<rfloor>"
    by (intro nat_mono floor_mono \<pi>_mono) auto
  hence "nat \<lfloor>primes_pi (real p)\<rfloor> - 1 < nat \<lfloor>primes_pi x\<rfloor>"
    using \<open>primes_pi p \<ge> 1\<close> by linarith
  thus  "nat \<lfloor>primes_pi (real p)\<rfloor> - 1 \<in> {..<nat \<lfloor>primes_pi x\<rfloor>}" by simp
  show "nth_prime (nat \<lfloor>primes_pi (real p)\<rfloor> - 1) = p"
    using p \<open>primes_pi p \<ge> 1\<close>
    by (intro nth_prime_eqI'') (auto simp: le_nat_iff primes_pi_def prime_sum_upto_def)
next
  fix k assume k: "k \<in> {..<nat \<lfloor>primes_pi x\<rfloor>}"
  thus *: "nat \<lfloor>primes_pi (real (nth_prime k))\<rfloor> - 1 = k" by auto
  from k have "\<not>(x < 2)" by (intro notI) auto
  hence "x \<ge> 2" by simp
  have "real (nth_prime k) \<le> real (nth_prime (nat \<lfloor>primes_pi x\<rfloor> - 1))"
    using k by simp
  also have "\<dots> \<le> x"
    using nth_prime_partition''[of x] \<open>x \<ge> 2\<close> by auto
  finally show "nth_prime k \<in> {p. prime p \<and> real p \<le> x}"
    by auto
qed

lemma primorial'_conv_primorial:
  assumes "n > 0"
  shows   "primorial' n = primorial (nth_prime (n - 1))"
proof -
  have "primorial (nth_prime (n - 1)) = (\<Prod>k<nat (int (n - 1) + 1). nth_prime k)"
    by (simp add: primorial_conv_primorial' primorial'_def)
  also have "nat (int (n - 1) + 1) = n"
    using assms by auto
  finally show ?thesis by (simp add: primorial'_def)
qed


subsection \<open>Maximal compositeness of primorials\<close>

text \<open>
  Primorials are maximally composite, i.\,e.\ any number with \<open>k\<close> distinct prime factors
  is as least as big as the primorial with \<open>k\<close> distinct prime factors, and and number less
  than a primorial has strictly less prime factors.
\<close>

lemma nth_prime_le_prime_sequence:
  fixes p :: "nat \<Rightarrow> nat"
  assumes "strict_mono_on p {..<n}" and "\<And>k. k < n \<Longrightarrow> prime (p k)" and "k < n"
  shows   "nth_prime k \<le> p k"
  using assms(3)
proof (induction k)
  case 0
  hence "prime (p 0)" by (intro assms)
  hence "p 0 \<ge> 2" by (auto dest: prime_gt_1_nat)
  thus ?case by simp
next
  case (Suc k)
  have IH: "Suc (nth_prime k) \<le> Suc (p k)" using Suc by simp
  have "nth_prime (Suc k) = smallest_prime_beyond (Suc (nth_prime k))"
    by (simp add: nth_prime_Suc)
  also {
    have "Suc (nth_prime k) \<le> Suc (p k)" using Suc by simp
    also have "\<dots> \<le> smallest_prime_beyond (Suc (p k))"
      by (rule smallest_prime_beyond_le)
    finally have "smallest_prime_beyond (Suc (nth_prime k)) \<le> smallest_prime_beyond (Suc (p k))"
      by (rule smallest_prime_beyond_smallest[OF prime_smallest_prime_beyond])
  }
  also have "p k < p (Suc k)"
    using Suc by (intro strict_mono_onD[OF assms(1)]) auto
  hence "smallest_prime_beyond (Suc (p k)) \<le> p (Suc k)"
    using Suc.prems by (intro smallest_prime_beyond_smallest assms) auto
  finally show ?case .
qed

theorem primorial'_primes_omega_le:
  fixes n :: nat
  assumes n: "n > 0"
  shows "primorial' (primes_omega n) \<le> n"
proof (cases "n = 1")
  case True
  thus ?thesis by simp
next
  case False
  with assms have "n > 1" by simp
  define m where "m = primes_omega n"
  define P where "P = {p. prime p \<and> real p \<le> primes_pi n}"
  define ps where "ps = sorted_list_of_set (prime_factors n)"
  have set_ps: "set ps = prime_factors n" by (simp add: ps_def)
  have [simp]: "length ps = m" by (simp add: ps_def m_def primes_omega_def)
  have "sorted ps" "distinct ps" by (simp_all add: ps_def)
  hence mono: "strict_mono_on (\<lambda>k. ps ! k) {..<m}"
    by (intro strict_mono_onI le_neq_trans) (auto simp: sorted_nth_mono distinct_conv_nth)
  from \<open>n > 1\<close> have "m > 0"
    by (auto simp: m_def prime_factorization_empty_iff intro!: Nat.gr0I)

  have "primorial' m = (\<Prod>k<m. nth_prime k)"
    using \<open>m > 0\<close> by (simp add: of_nat_diff primorial'_def m_def)
  also have "(\<Prod>k<m. nth_prime k) \<le> (\<Prod>k<m. ps ! k ^ multiplicity (ps ! k) n)"
  proof (intro prod_mono conjI)
    fix i assume i: "i \<in> {..<m}"
    hence p: "ps ! i \<in> prime_factors n"
      using set_ps by (auto simp: set_conv_nth)
    with i set_ps have "nth_prime i \<le> ps ! i"
      by (intro nth_prime_le_prime_sequence[where n = m] mono) (auto simp: set_conv_nth)
    also have "\<dots> \<le> ps ! i ^ multiplicity (ps ! i) n"
      using p by (intro self_le_power) (auto simp: prime_factors_multiplicity dest: prime_gt_1_nat)
    finally show "nth_prime i \<le> \<dots>" .
  qed auto
  also have "\<dots> = (\<Prod>p\<in>(\<lambda>i. ps ! i) ` {..<m}. p ^ multiplicity p n)"
    using \<open>distinct ps\<close> by (subst prod.reindex) (auto intro!: inj_onI simp: distinct_conv_nth)
  also have "(\<lambda>i. ps ! i) ` {..<m} = set ps"
    by (auto simp: set_conv_nth)
  also have "set ps = prime_factors n"
    by (simp add: set_ps)
  also have "(\<Prod>p\<in>prime_factors n. p ^ multiplicity p n) = n"
    using \<open>n > 1\<close> by (intro prime_factorization_nat [symmetric]) auto
  finally show "primorial' m \<le> n" .
qed

lemma primes_omega_less_primes_omega_primorial:
  fixes n :: nat
  assumes n: "n > 0" and "n < primorial x"
  shows "primes_omega n < primes_omega (primorial x)"
proof (cases "n > 1")
  case False
  have [simp]: "primes_pi 2 = 1" by (simp add: eval_\<pi>)
  from False assms have [simp]: "n = 1" by auto
  from assms have "\<not>(x < 2)"
    by (intro notI) (auto simp: primorial_conv_primorial')
  thus ?thesis using assms \<pi>_mono[of 2 x] by auto
next
  case True
  define m where "m = primes_omega n"
  have le: "primorial' m \<le> n"
    using primorial'_primes_omega_le[of n] \<open>n > 1\<close> by (simp add: m_def primes_omega_def)
  also have "\<dots> < primorial x" by fact
  also have "\<dots> = primorial' (nat \<lfloor>primes_pi x\<rfloor>)"
    by (simp add: primorial_conv_primorial')
  finally have "m < nat \<lfloor>primes_pi x\<rfloor>"
    using strict_mono_less[OF strict_mono_primorial'] by simp
  hence "m < primes_pi x" by linarith
  also have "\<dots> = primes_omega (primorial x)" by simp
  finally show ?thesis unfolding m_def of_nat_less_iff .
qed

lemma primes_omega_le_primes_omega_primorial:
  fixes n :: nat
  assumes "n \<le> primorial x"
  shows   "primes_omega n \<le> primes_omega (primorial x)"
proof -
  consider "n = 0" | "n > 0" "n = primorial x" | "n > 0" "n \<noteq> primorial x" by force
  thus ?thesis
    by cases (use primes_omega_less_primes_omega_primorial[of n x] assms in auto)
qed

end