(*
  File:    Elementary_Prime_Bounds.thy
  Author:  Manuel Eberl, TU München

  Elementary bounds for the prime-counting function \<pi>(x) and the "n-th prime" function p_n
*)
section \<open>Elementary bounds on $\pi(x)$ and $p_n$\<close>
theory Elementary_Prime_Bounds
imports
  Prime_Number_Theorem.Prime_Counting_Functions
  Prime_Distribution_Elementary_Library
  More_Dirichlet_Misc
begin

text \<open>
  In this section, we will follow Apostol and give elementary proofs of Chebyshev-type
  lower and upper bounds for $\pi(x)$, i.\,e.\ $c_1 x/\ln x < \pi(x) < c_2 x/\ln x$. From
  this, similar bounds for $p_n$ follow as easy corollaries.
\<close>

(* TODO: Move stuff from Prime_Number_Theorem here *)

subsection \<open>Preliminary lemmas\<close>

text \<open>
  The following two estimates relating the central Binomial coefficient to powers
  of 2 and 4 form the starting point for Apostol's elementary bounds for $\pi(x)$:
\<close>
lemma twopow_le_central_binomial: "2 ^ n \<le> ((2 * n) choose n)"
proof -
  have "2 ^ n * fact n ^ 2 \<le> (fact (2 * n) :: nat)"
  proof (induction n)
    case (Suc n)
    have "(fact (2 * Suc n) :: nat) = (2 * n + 1) * (2 * n + 2) * fact (2 * n)"
      by (simp add: algebra_simps)
    
    have "2 ^ Suc n * fact (Suc n) ^ 2 = 2 ^ n * fact n ^ 2 * 2 * (n + 1) ^ 2"
      by (simp add: algebra_simps power2_eq_square)
    also have "\<dots> \<le> fact (2 * n) * 2 * (n + 1) ^ 2"
      by (intro mult_right_mono Suc.IH) auto
    also have "\<dots> = fact (2 * n) * (2 * (n + 1) ^ 2)"
      by (simp add: mult_ac)
    also have "\<dots> \<le> fact (2 * n) * ((2 * n + 1) * (2 * n + 2))"
      by (intro mult_left_mono) (auto simp: power2_eq_square)
    also have "\<dots> = fact (2 * Suc n)"
      by (simp add: algebra_simps)
    finally show ?case .
  qed simp_all
  also have "\<dots> = (2 * n choose n) * fact n ^ 2"
    using binomial_fact_lemma[of n "2 * n"] by (simp add: power2_eq_square mult_ac)
  finally show ?thesis by simp
qed

lemma fourpow_gt_central_binomial:
  assumes "n > 0"
  shows   "4 ^ n > ((2 * n) choose n)"
proof -
  have "(\<Sum>i\<in>{..2*n}-{n}. ((2 * n) choose i)) > 0"
    using assms by (intro sum_pos) (auto simp: subset_iff)
  hence "((2 * n) choose n) < (\<Sum>i\<in>{..2*n}-{n}. ((2 * n) choose i)) + ((2 * n) choose n)"
    by simp
  also have "\<dots> = (\<Sum>i \<in> insert n ({..2*n} - {n}). ((2 * n) choose i))"
    by (subst sum.insert) auto
  also have "insert n ({..2*n} - {n}) = {..2*n}" by auto
  also have "(\<Sum>i\<le>2*n. ((2 * n) choose i)) = (1 + 1) ^ (2 * n)"
    by (subst binomial) simp_all
  also have "\<dots> = 4 ^ n"
    by (subst power_mult) (simp add: eval_nat_numeral)
  finally show ?thesis .
qed


subsection \<open>Lower bound for $\pi(x)$\<close>

context
  includes prime_counting_notation
  fixes S :: "nat \<Rightarrow> nat \<Rightarrow> int"
  defines "S \<equiv> (\<lambda>n p. (\<Sum>m\<in>{0<..nat \<lfloor>log p (2*n)\<rfloor>}. \<lfloor>2*n/p^m\<rfloor> - 2 * \<lfloor>n/p^m\<rfloor>))"
begin

text \<open>
  We now first prove the bound $\pi(x) \geq \frac{1}{6} x/\ln x$ for $x\geq 2$.
  The constant could probably be improved for starting points greater than 2; this
  is true for most of the constants in this section.

  The first step is to show a slightly stronger bound for even numbers, where the
  constant is $\frac{1}{2}\ln 2 \approx 0.347$:
\<close>
lemma 
  fixes n :: nat
  assumes n: "n \<ge> 1"
  shows   \<pi>_bounds_aux: "ln (fact (2 * n)) - 2 * ln (fact n) =
                           prime_sum_upto (\<lambda>p. S n p * ln p) (2 * n)"
  and     \<pi>_lower_bound_ge_strong: "\<pi> (2 * n) \<ge> ln 2 / 2 * (2 * n) / ln (2 * n)"
proof -
  define L :: "real \<Rightarrow> nat \<Rightarrow> nat" where "L = (\<lambda>x p. legendre_aux x p)"
  have "ln (fact (2 * n)) - 2 * ln (fact n) = sum_upto ln (2 * n) - 2 * sum_upto ln n"
    by (simp add: ln_fact_conv_sum_upto)
  also have "\<dots> = prime_sum_upto (\<lambda>p. L (2 * n) p * ln p) (2 * n) -
                    2 * prime_sum_upto (\<lambda>p. L n p * ln p) n"
    by (subst (1 2) legendre_identity) (auto simp: L_def)
  also have "prime_sum_upto (\<lambda>p. L n p * ln p) n = prime_sum_upto (\<lambda>p. L n p * ln p) (2 * n)"
    unfolding prime_sum_upto_altdef2
    by (intro sum.mono_neutral_left[OF finite_subset[of _ "{..2*n}"]])
       (auto dest: prime_gt_0_nat legendre_aux_posD
             simp: legendre_aux_eq_0 L_def le_nat_iff le_floor_iff)
  also have "prime_sum_upto (\<lambda>p. L (2*n) p * ln p) (2*n) -
                 2 * prime_sum_upto (\<lambda>p. L n p * ln p) (2 * n) =
               prime_sum_upto (\<lambda>p. (real (L (2*n) p) - 2 * real (L n p)) * ln p) (2 * n)"
    by (simp add: ring_distribs sum_subtractf sum_distrib_left mult.assoc prime_sum_upto_def)
  also have "\<dots> = prime_sum_upto (\<lambda>p. of_int (S n p) * ln p) (2*n)"
    unfolding prime_sum_upto_def
  proof (intro sum.cong refl, goal_cases)
    case (1 p)
    define ub where "ub = nat \<lfloor>log p (2*n)\<rfloor>"
    from 1 have p: "prime p" "p > 1" "p \<le> 2 * n"
      using prime_gt_1_nat[of p] by auto
    have "L (2 * n) p = (\<Sum>m\<in>{0<..ub}. nat \<lfloor>2*n/p^m\<rfloor>)"
      unfolding L_def legendre_aux_altdef1 using p 1 by (auto simp: ub_def)
    moreover have "L n p = (\<Sum>m\<in>{0<..ub}. nat \<lfloor>n/p^m\<rfloor>)" unfolding L_def
    proof (intro legendre_aux_altdef2)
      have "real n = real p powr log p n"
        using n p by simp
      also have "log (real p) 2 > 0" using p by auto
      hence "log p n < 1 + of_int \<lfloor>log p 2 + log p n\<rfloor>" by linarith
      hence "real p powr log p n < real p powr Suc ub"
        unfolding ub_def using n p by (intro powr_less_mono) (auto simp: log_mult)
      also have "\<dots> = p ^ Suc ub"
        using p by (subst powr_realpow) auto
      finally show "real n < real p ^ Suc ub" by simp
    qed (use n p in auto)
    ultimately have "real (L (2 * n) p) - 2 * real (L n p) =
                       (\<Sum>m\<in>{0<..ub}. real (nat \<lfloor>2*n/p^m\<rfloor>) - 2 * real (nat \<lfloor>n/p^m\<rfloor>))"
      by (simp add: sum_subtractf sum_distrib_left)
    also have "\<dots> = of_int (\<Sum>m\<in>{0<..ub}. \<lfloor>2*n/p^m\<rfloor> - 2 * \<lfloor>n/p^m\<rfloor>)"
      unfolding of_int_sum by (intro sum.cong) auto
    finally show ?case by (simp add: ub_def S_def)
  qed
  finally show eq: "ln (fact (2 * n)) - 2 * ln (fact n) =
                      prime_sum_upto (\<lambda>p. S n p * ln p) (2 * n)" .

  have S_nonneg: "S n p \<ge> 0" for p
    unfolding S_def by (intro sum_nonneg) linarith
  have S_le: "S n p \<le> \<lfloor>log p (2*n)\<rfloor>" if "prime p" for p
  proof -
    have "S n p \<le> (\<Sum>m\<in>{0<..nat \<lfloor>log p (2*n)\<rfloor>}. 1)"
      unfolding S_def of_nat_mult of_nat_numeral by (intro sum_mono) linarith
    thus ?thesis using prime_gt_1_nat[of p] that n by auto
  qed

  have "n * ln 2 = ln (real (2 ^ n))"
    by (simp add: ln_realpow)
  also have "\<dots> \<le> ln (real ((2*n) choose n))"
    using twopow_le_central_binomial[of n]
    by (subst ln_le_cancel_iff; (unfold of_nat_le_iff)?) auto
  also have "\<dots> = ln (fact (2 * n)) - 2 * ln (fact n)"
    by (simp add: binomial_fact ln_div ln_mult)
  also have "\<dots> = prime_sum_upto (\<lambda>p. S n p * ln p) (2 * n)"
    by (fact eq)
  also have "\<dots> \<le> prime_sum_upto (\<lambda>p. \<lfloor>log p (2*n)\<rfloor> * ln p) (2 * n)"
    unfolding prime_sum_upto_def using S_le
    by (intro sum_mono mult_right_mono) (auto dest: prime_gt_0_nat)
  also have "\<dots> \<le> prime_sum_upto (\<lambda>p. ln (2 * n)) (2 * n)"
    unfolding prime_sum_upto_def
  proof (intro sum_mono)
    fix p assume "p \<in> {p. prime p \<and> real p \<le> real (2 * n)}"
    hence p: "p > 1" using prime_gt_1_nat[of p] by auto
    have "real_of_int \<lfloor>log p (2 * n)\<rfloor> = real_of_int \<lfloor>ln (2 * n) / ln p\<rfloor>"
      using p n by (simp add: log_def ln_mult)
    also have "\<dots> \<le> ln (2 * n) / ln p"
      by linarith
    also have "\<dots> * ln p = ln (2 * n)"
      using p by (simp add: field_simps)
    finally show "real_of_int \<lfloor>log p (2 * n)\<rfloor> * ln p \<le> ln (2 * n)"
      using p by simp
  qed
  also have "\<dots> = ln (2 * n) * \<pi> (2 * n)"
    by (simp add: \<pi>_def prime_sum_upto_def)
  finally show "\<pi> (2 * n) \<ge> (ln 2 / 2) * (2 * n) / ln (2 * n)"
    using n by (simp add: field_simps)
qed  

lemma ln_2_ge_56_81: "ln 2 \<ge> (56 / 81 :: real)"
  using ln_approx_bounds[of 2 2, simplified, simplified eval_nat_numeral, simplified] by simp

text \<open>
  The bound for any real number $x\geq 2$ follows fairly easily, although some ugly
  accounting for error terms has to be done.
\<close>
theorem \<pi>_lower_bound:
  fixes x :: real
  assumes x: "x \<ge> 2"
  shows   "\<pi> x > (1 / 6) * (x / ln x)"
proof (cases "even (nat \<lfloor>x\<rfloor>)")
  case True
  define n where "n = nat \<lfloor>x\<rfloor>"
  from True assms have n: "n \<ge> 2" "even n"
    by (auto simp: n_def le_nat_iff le_floor_iff)
  have "(1 / 6) * (x / ln x) < (ln 2 / 4) * (x / ln x)"
    using ln_2_ge_56_81 x by (intro mult_strict_right_mono) auto
  also have "ln 2 / 4 * (x / ln x) = (1 / 2) * (ln 2 / 2 * x / ln x)"
    by simp
  also have "\<dots> \<le> (1 - 1 / x) * (ln 2 / 2 * x / ln x)"
    by (intro mult_right_mono) (use assms in \<open>auto simp: field_simps\<close>)
  also have "(1 - 1 / x) * (ln 2 / 2 * x / ln x) = ln 2 / 2 * (x - 1) / ln x"
    using assms by (simp add: field_simps)
  also have "ln 2 / 2 * (x - 1) / ln x \<le> ln 2 / 2 * n / ln n"
    using x by (intro frac_le mult_mono mult_nonneg_nonneg) (auto simp: n_def)
  also have "ln 2 / 2 * n / ln n \<le> \<pi> n"
    using \<pi>_lower_bound_ge_strong[of "n div 2"] \<open>even n\<close> n by simp
  also have "\<pi> n = \<pi> x" by (simp add: n_def)
  finally show ?thesis .
next
  case False
  define n where "n = nat \<lfloor>x\<rfloor>"
  from False assms have n: "n \<ge> 2" "odd n"
    by (auto simp: n_def le_nat_iff le_floor_iff)
  then obtain k where [simp]: "n = 2 * k + 1"
    by (auto elim!: oddE)
  from n have k: "k > 0" by simp

  from k have "3 \<le> real n" by simp
  also have "real n \<le> x" unfolding n_def using x by linarith
  finally have "x \<ge> 3" .

  have "(1 / 6) * (x / ln x) = 1 / 6 * x / ln x"
    using x by (simp add: field_simps)
  also have "1 / 6 * x / ln x < ln 2 / 2 * (2 * k) / ln (2 * k)"
  proof (intro frac_less)
    have "x < real n + 1" unfolding n_def by linarith
    hence "1 / 6 * x < 1 / 6 * (n + 1)" by simp
    also {
      have *: "(3 * ln 2 - 1 :: real) \<ge> 1"
        using ln_2_ge_56_81 by simp
      hence "1 / (3 * ln 2 - 1 :: real) \<le> 1" by simp
      also have "1 \<le> real k" using k by simp
      finally have "1 / 6 * (n + 1) \<le> ln 2 / 2 * real (2 * k)"
        using * by (simp add: field_simps)
    }
    finally show "1 / 6 * x < ln 2 / 2 * real (2 * k)" .
  next
    have "real (2 * k) \<le> real n" by simp
    also have "\<dots> \<le> x" using x unfolding n_def by linarith
    finally show "ln (real (2 * k)) \<le> ln x" using k by simp
  qed (use k x in auto)
  also have "ln 2 / 2 * (2 * k) / ln (2 * k) \<le> \<pi> (2 * k)"
    by (rule \<pi>_lower_bound_ge_strong) (use \<open>k > 0\<close> in auto)
  also have "\<pi> (2 * k) \<le> \<pi> n"
    by (rule \<pi>_mono) auto
  also have "\<dots> = \<pi> x" unfolding n_def by simp
  finally show ?thesis .
qed

lemma \<pi>_at_top: "filterlim primes_pi at_top at_top"
proof (rule filterlim_at_top_mono)
  show "eventually (\<lambda>x. primes_pi x \<ge> 1 / 6 * (x / ln x)) at_top"
    using eventually_gt_at_top[of 2] by eventually_elim (intro less_imp_le \<pi>_lower_bound)
qed real_asymp


subsection \<open>Upper bound for $\vartheta(x)$\<close>

text \<open>
  In this section, we prove a linear upper bound for $\vartheta$. This is somewhat unnecessary
  because we already have a considerably better bound on $\vartheta(x)$ using a proof that has
  roughly the same complexity as this one and also only uses elementary means. Nevertheless,
  here is the proof from Apostol's book; it is quite nice and it would be a shame not to
  formalise it.

  The idea is to first show a bound for $\vartheta(2n)-\vartheta(n)$ and then deduce one for
  $\vartheta(2^n)$ from this by telescoping, which then yields one for general $x$ by
  monotonicity.
\<close>
lemma \<theta>_double_less:
  fixes n :: nat
  assumes n: "n > 0"
  shows "\<theta> (2 * real n) - \<theta> (real n) < real n * ln 4"
proof (cases "n \<ge> 2")
  case False
  with assms have "n = 1" by force
  moreover have "\<theta> 2 = ln 2" by (simp add: eval_\<theta>)
  ultimately show ?thesis by auto
next
  define P where "P = (\<lambda>n::nat. {p\<in>{0<..n}. prime p})"
  have \<theta>_eq: "\<theta> n = (\<Sum>p\<in>P n. ln p)" for n
    unfolding \<theta>_def prime_sum_upto_def
    by (intro sum.cong) (auto simp: P_def dest: prime_gt_0_nat)

  have "\<theta> (2 * n) - \<theta> n = (\<Sum>p \<in> P (2*n) - P n. ln p)"
    unfolding \<theta>_eq by (rule Groups_Big.sum_diff [symmetric]) (auto simp: P_def)

  also have "(\<Sum>p\<in>P (2*n) - P n. ln p) =
          (\<Sum>p\<in>P (2*n) - P n. (\<lfloor>2*n/p\<rfloor> - 2 * \<lfloor>n/p\<rfloor>) * ln p)"
  proof (intro sum.cong refl)
    fix p assume p: "p \<in> P (2*n) - P n"
    hence *: "real n / real p < 1" "real n / real p \<ge> 1 / 2" by (auto simp: P_def)
    from * have "\<lfloor>real n / real p\<rfloor> = 0" by linarith
    moreover from * have "\<lfloor>2 * real n / real p\<rfloor> = 1"
      by linarith
    ultimately show "ln p = (\<lfloor>2*n/p\<rfloor> - 2 * \<lfloor>n/p\<rfloor>) * ln p"
      by simp
  qed 

  also have "(\<Sum>p\<in>P (2*n) - P n. (\<lfloor>2*n/p\<rfloor> - 2 * \<lfloor>n/p\<rfloor>) * ln p) \<le>
          (\<Sum>p\<in>P (2*n). (\<lfloor>2*n/p\<rfloor> - 2 * \<lfloor>n/p\<rfloor>) * ln p)"
  proof (intro sum_mono2)
    fix p assume p: "p \<in> P (2 * n) - (P (2 * n) - P n)"
    have "2 * \<lfloor>real n / real p\<rfloor> \<le> \<lfloor>2 * (real n / real p)\<rfloor>"
      by linarith
    thus "0 \<le> real_of_int (\<lfloor>real (2 * n) / real p\<rfloor> - 2 * \<lfloor>real n / real p\<rfloor>) * ln (real p)"
      using p by (intro mult_nonneg_nonneg) (auto simp: P_def)
  qed (auto simp: P_def)

  also have *: "2 * real_of_int \<lfloor>real n / real p ^ m\<rfloor> \<le> 2 * real n / real p ^ m" for p m
    by linarith
  have "(\<Sum>m\<in>{1}. \<lfloor>2 * real n / real p ^ m\<rfloor> - 2 * \<lfloor>n / real p^m\<rfloor>) \<le> S n p"
    if "prime p" "p \<le> 2 * n" for p :: nat 
    unfolding S_def using prime_gt_1_nat[OF that(1)] that(2) n *[of p]
    by (intro sum_mono2) (auto dest: prime_gt_1_nat simp: le_nat_iff le_floor_iff)
  hence "(\<Sum>p\<in>P (2*n). (\<Sum>m\<in>{1}. \<lfloor>2*n/p^m\<rfloor> - 2 * \<lfloor>n/p^m\<rfloor>) * ln p) \<le> (\<Sum>p\<in>P (2*n). S n p * ln p)"
    by (intro sum_mono mult_right_mono; (unfold of_int_le_iff)?)
       (auto dest: prime_gt_1_nat simp: P_def)
  hence "(\<Sum>p\<in>P (2*n). (\<lfloor>2*n/p\<rfloor> - 2 * \<lfloor>n/p\<rfloor>) * ln p) \<le> (\<Sum>p\<in>P (2*n). S n p * ln p)"
    by simp

  also have "(\<Sum>p \<in> P (2*n). S n p * ln p) = prime_sum_upto (\<lambda>p. S n p * ln p) (2 * n)"
    unfolding P_def prime_sum_upto_def by (intro sum.cong) (auto simp: P_def dest: prime_gt_0_nat)
  also have "\<dots> = ln (fact (2 * n)) - 2 * ln (fact n)"
    by (rule \<pi>_bounds_aux [symmetric]) (use n in auto)
  also have "\<dots> = ln (real ((2*n) choose n))"
    by (simp add: binomial_fact ln_div ln_mult)
  also have "\<dots> < ln (real (4 ^ n))"
    by (subst ln_less_cancel_iff; (unfold of_nat_le_iff)?)
       (use fourpow_gt_central_binomial[of n] n in auto)
  also have "\<dots> = n * ln 4"
    by (simp add: ln_realpow)
  finally show ?thesis by simp
qed

lemma \<theta>_twopow_less: "\<theta> (2 ^ r) < 2 ^ (r + 1) * ln 2"
proof -
  have \<theta>_twopow_diff: "\<theta> (2 ^ Suc k) - \<theta> (2 ^ k) < 2 ^ Suc k * ln 2" for k
    using \<theta>_double_less[of "2 ^ k"] ln_realpow[of 2 2] by simp
  show "\<theta> (2 ^ r) < 2 ^ (r + 1) * ln 2"
  proof (cases "r > 0")
    case True
    have "(\<Sum>k<r. \<theta> (2 ^ Suc k) - \<theta> (2 ^ k)) < (\<Sum>k<r. 2 ^ Suc k * ln 2)"
      by (intro sum_strict_mono \<theta>_twopow_diff) (use \<open>r > 0\<close> in auto)
    also have "(\<Sum>k<r. \<theta> (2 ^ Suc k) - \<theta> (2 ^ k)) = \<theta> (2 ^ r)"
      by (subst sum_lessThan_telescope) auto
    also have "(\<Sum>k<r. 2 ^ Suc k * ln 2 :: real) = (\<Sum>k<r. 2 ^ k) * 2 * ln 2"
      by (simp add: sum_distrib_right sum_distrib_left mult_ac)
    also have "(\<Sum>k<r. 2 ^ k :: real) = 2 ^ r - 1"
      using geometric_sum[of "2 :: real"] by simp
    also have "\<dots> \<le> 2 ^ r" by simp
    finally show "\<theta> (2 ^ r) < 2 ^ (r + 1) * ln 2"
      by simp
  qed auto
qed

theorem \<theta>_upper_bound_weak:
  fixes n :: nat
  assumes n: "n > 0"
  shows   "\<theta> n < 4 * ln 2 * n"
proof -
  define r where "r = Discrete.log n"
  have "\<theta> n \<le> \<theta> (real (2 ^ Suc r))"
    unfolding r_def using log_exp2_ge[of n] by (intro \<theta>_mono, unfold of_nat_le_iff) auto
  also have "\<dots> < 4 * ln 2 * real (2 ^ r)"
    using \<theta>_twopow_less[of "r + 1"] by (simp add: mult_ac)
  also have "\<dots> \<le> 4 * ln 2 * real n" unfolding r_def
    by (intro mult_left_mono, unfold of_nat_le_iff, intro log_exp2_le) (use n in auto)
  finally show "\<theta> n < 4 * ln 2 * n" by simp
qed


subsection \<open>Upper bound for $\pi(x)$\<close>

text \<open>
  We use our upper bound for $\vartheta(x)$ (the strong one, not the one from the previous
  section) to derive an upper bound for $\pi(x)$.

  As a first step, we show the following lemma about the global maximum of the function
  $\ln x / x^c$ for $c > 0$:
\<close>
lemma \<pi>_upper_bound_aux:
  fixes c :: real
  assumes "c > 0"
  defines "f \<equiv> (\<lambda>x. x powr (-c) * ln x)"
  assumes x: "x > 0"
  shows "f x \<le> 1 / (c * exp 1)"
proof -
  define f' where "f' = (\<lambda>x. x powr (-c - 1) * (1 - c * ln x))"
  define z where "z = exp (1 / c)"
  have "z > 0" by (simp add: z_def)
  have deriv: "(f has_real_derivative f' t) (at t)" if "t > 0" for t
    unfolding f_def f'_def using that
    by (auto intro!: derivative_eq_intros simp: field_simps powr_diff powr_minus)
  have [simp]: "f z = 1 / (c * exp 1)"
    by (simp add: z_def f_def powr_def exp_minus field_simps)

  show ?thesis
  proof (cases x z rule: linorder_cases)
    assume x: "x < z"
    from x assms have t: "\<exists>t. t > x \<and> t < z \<and> f z - f x = (z - x) * f' t"
      by (intro MVT2 deriv) auto
    then obtain t where t: "t > x" "t < z" "f z - f x = (z - x) * f' t"
      by blast
    hence "ln t < ln z" using assms by simp
    also have "ln z = 1 / c" by (simp add: z_def)
    finally have "0 \<le> (z - x) * f' t"
      unfolding f'_def using \<open>c > 0\<close> x
      by (intro mult_nonneg_nonneg) (auto simp: z_def field_simps)
    also from t have "\<dots> = f z - f x" by (simp add: algebra_simps)
    finally show ?thesis by simp
  next
    assume x: "x > z"
    from x assms \<open>z > 0\<close> have t: "\<exists>t. t > z \<and> t < x \<and> f x - f z = (x - z) * f' t"
      by (intro MVT2 deriv) auto
    then obtain t where t: "t > z" "t < x" "f x - f z = (x - z) * f' t"
      by blast
    hence "ln z < ln t" using \<open>z > 0\<close> assms by simp
    also have "ln z = 1 / c" by (simp add: z_def)
    finally have "0 \<le> (z - x) * f' t"
      unfolding f'_def using \<open>c > 0\<close> x
      by (intro mult_nonpos_nonpos mult_nonneg_nonpos) (auto simp: z_def field_simps)
    also from t have "\<dots> = f z - f x" by (simp add: algebra_simps)
    finally show ?thesis by simp
  qed auto
qed

text \<open>
  Following Apostol, we first show a generic bound depending on some real-valued
  parameter \<open>\<alpha>\<close>:
\<close>
lemma \<pi>_upper_bound_strong:
  fixes \<alpha> :: real and n :: nat
  assumes n: "n \<ge> 2" and \<alpha>: "\<alpha> \<in> {0<..<1}"
  shows "\<pi> n < (1 / ((1 - \<alpha>) * exp 1) + ln 4 / \<alpha>) * n / ln n"
proof -
  have "real n powr \<alpha> \<le> real n powr 1"
    using assms n by (intro powr_mono) auto
  hence n': "real n powr \<alpha> \<le> real n" using n by simp

  define P where "P = (\<lambda>x. {p. prime p \<and> real p \<le> x})"
  define Q where "Q = {p. prime p \<and> real p \<in> {n powr \<alpha><..n}}"

  have finite_P [intro]: "finite (P x)" for x
  proof (cases "x \<ge> 0")
    case True
    hence "P x \<subseteq> {..nat \<lfloor>x\<rfloor>}"
      by (auto simp: le_nat_iff le_floor_iff P_def)
    thus ?thesis by (rule finite_subset) auto
  qed (auto simp: P_def)

  have P_subset: "P x \<subseteq> P y" if "x \<le> y" for x y
    using that by (auto simp: P_def)

  have "Q = P n - P (n powr \<alpha>)" by (auto simp: Q_def P_def)
  also have "card \<dots> = card (P n) - card (P (n powr \<alpha>))"
    by (intro card_Diff_subset finite_P P_subset n')
  also have "real \<dots> = \<pi> n - \<pi> (n powr \<alpha>)"
    by (subst of_nat_diff[OF card_mono[OF _ P_subset]])
       (use n' in \<open>auto simp: \<pi>_def prime_sum_upto_def P_def\<close>)
  finally have card_Q: "real (card Q) = \<pi> n - \<pi> (n powr \<alpha>)" .

  have "(\<pi> n - \<pi> (n powr \<alpha>)) * ln (n powr \<alpha>) = (\<Sum>p\<in>Q. ln (n powr \<alpha>))"
    using card_Q by simp
  also have "\<dots> \<le> (\<Sum>p\<in>Q. ln p)"
    using n \<alpha> by (intro sum_mono, subst ln_le_cancel_iff) (auto simp: Q_def dest: prime_gt_0_nat)
  also have "\<dots> \<le> \<theta> n"
    unfolding \<theta>_def prime_sum_upto_def by (intro sum_mono2) (auto simp: Q_def dest: prime_gt_1_nat)
  also have "\<dots> < ln 4 * real n"
    by (rule \<theta>_upper_bound) (use n in auto)
  finally have ineq: "(\<pi> n - \<pi> (n powr \<alpha>)) * ln (n powr \<alpha>) < ln 4 * n" .

  with n assms have "\<pi> n < \<pi> (n powr \<alpha>) + (ln 4 / \<alpha>) * n / ln n"
    by (simp add: field_simps ln_powr
             del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
  also have "\<pi> (n powr \<alpha>) \<le> n powr \<alpha>"
    by (rule \<pi>_le_self) auto
  also have "n powr \<alpha> + ln 4 / \<alpha> * n / ln n =
               (n powr (-(1 - \<alpha>)) * ln n + ln 4 / \<alpha>) * n / ln n"
    using n \<alpha> by (simp add: field_simps powr_diff
                       del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
  also have "n powr (-(1 - \<alpha>)) * ln n \<le> 1 / ((1 - \<alpha>) * exp 1)"
    by (intro \<pi>_upper_bound_aux) (use \<alpha> n in auto)
  hence "(n powr (-(1 - \<alpha>)) * ln n + ln 4 / \<alpha>) * n / ln n \<le>
           (1 / ((1 - \<alpha>) * exp 1) + ln 4 / \<alpha>) * n / ln n"
    using n \<alpha> by (intro divide_right_mono mult_right_mono add_mono) auto
  finally show "\<pi> n < (1 / ((1 - \<alpha>) * exp 1) + ln 4 / \<alpha>) * n / ln n"
    by simp
qed

text \<open>
  The choice $\alpha := \frac{2}{3}$ then leads to the upper bound $\pi(x) < cx/\ln x$
  with $c = 3(e^{-1} + \ln 2) \approx 3.183$. This is considerably stronger than
  Apostol's bound.
\<close>
theorem \<pi>_upper_bound:
  fixes x :: real
  assumes "x \<ge> 2"
  shows   "\<pi> x < 3 * (exp (-1) + ln 2) * x / ln x"
proof (cases "x \<ge> 3")
  case False
  have "\<pi> x = \<pi> (nat \<lfloor>x\<rfloor>)" by simp
  also from False and assms have "nat \<lfloor>x\<rfloor> = 2"
    by linarith
  finally have "\<pi> x = 1" by (simp add: eval_\<pi>)
  also have "\<dots> < 3 * (exp (-1) + ln 2) * exp 1"
    by (simp add: exp_minus field_simps add_pos_pos
             del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
  also have "\<dots> \<le> 3 * (exp (-1) + ln 2) * (x / ln x)"
    using \<pi>_upper_bound_aux[of 1 x] 
    by (intro mult_left_mono) (use assms in \<open>auto simp: field_simps powr_minus\<close>)
  finally show ?thesis
    using assms by (simp add: field_simps)
next
  case True
  define n where "n = nat \<lfloor>x\<rfloor>"
  from True have n: "n \<ge> 3" by (simp add: n_def le_nat_iff le_floor_iff)
  have "\<pi> x = \<pi> n"
    by (simp add: n_def)
  also have "\<pi> n < 3 * (exp (-1) + ln 2) * (n / ln n)"
    using \<pi>_upper_bound_strong[of n "2 / 3"] ln_realpow[of 2 2] n
    by (simp add: field_simps exp_minus
             del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
  also have "\<dots> \<le> 3 * (exp (-1) + ln 2) * (x / ln x)"
    using n True by (intro mult_left_mono divide_ln_mono) (auto simp: n_def)
  finally show ?thesis by (simp add: divide_simps)
qed

corollary \<pi>_upper_bound':
  fixes x :: real
  assumes "x \<ge> 2"
  shows   "\<pi> x < 443 / 139 * (x / ln x)"
proof -
  have "2.71828 \<le> 5837465777 / 2147483648 - inverse (2 ^ 32 :: real)"
    by simp
  also have "\<dots> \<le> exp (1 :: real)"
    using e_approx_32 by linarith
  finally have "exp 1 \<ge> (2.71828 :: real)" .
  hence e_m1: "exp (-1) \<le> (10^5 / 271828 :: real)" by (simp add: field_simps exp_minus)

  from assms have "\<pi> x < 3 * (exp (-1) + ln 2) * (x / ln x)"
    using \<pi>_upper_bound[of x] by (simp add: field_simps)
  also have "\<dots> \<le> 443 / 139 * (x / ln x)"
  proof (intro mult_right_mono)
    have "3 * (exp (-1) + ln 2 :: real) \<le> 3 * (10^5 / 271828 + 25 / 36)"
      using e_m1 by (intro mult_left_mono add_mono ln2_le_25_over_36)
                    (auto simp: exp_minus field_simps abs_if split: if_splits)
    also have "\<dots> \<le> 443 / 139" by simp
    finally show "3 * (exp (- 1) + ln 2 :: real) \<le> 443 / 139" by simp 
  qed (use assms in auto)
  finally show ?thesis .
qed

corollary \<pi>_upper_bound'':
  fixes x :: real
  assumes "x \<ge> 2"
  shows   "\<pi> x < 4 * (x / ln x)"
  by (rule less_le_trans[OF \<pi>_upper_bound'[OF assms] mult_right_mono]) (use assms in auto)

text \<open>
  In particular, we have now shown a weak version of the Prime Number Theorem, namely
  that $\pi(x) \in \Theta(x/\ln x)$:
\<close>
lemma \<pi>_bigtheta: "\<pi> \<in> \<Theta>(\<lambda>x. x / ln x)"
proof
  have "eventually (\<lambda>x. \<bar>\<pi> x\<bar> \<le> 3 * (exp (- 1) + ln 2) * \<bar>x / ln x\<bar>) at_top"
    using eventually_ge_at_top[of 2]
    by eventually_elim (use \<pi>_upper_bound in \<open>auto intro!: less_imp_le\<close>)
  thus "\<pi> \<in> O(\<lambda>x. x / ln x)"
    by (intro bigoI[where c = "3 * (exp (- 1) + ln 2)"]) auto
next
  have "eventually (\<lambda>x. \<bar>\<pi> x\<bar> \<ge> 1 / 6 * \<bar>x / ln x\<bar>) at_top"
    using eventually_ge_at_top[of 2]
    by eventually_elim (use \<pi>_lower_bound in \<open>auto intro!: less_imp_le\<close>)
  thus "\<pi> \<in> \<Omega>(\<lambda>x. x / ln x)"
    by (intro landau_omega.bigI[where c = "1 / 6"]) auto
qed


subsection \<open>Bounds for $p_n$\<close>

text \<open>
  By some rearrangements, the lower and upper bounds for $\pi(x)$ give rise to
  analogous bounds for $p_n$:
\<close>
lemma nth_prime_lower_bound_gen:
  assumes c: "c > 0" and n: "n > 0"
  assumes "\<And>n. n \<ge> 2 \<Longrightarrow> \<pi> (real n) < (1 / c) * (real n / ln (real n))"
  shows "nth_prime (n - 1) \<ge> c * (real n * ln (real n))"
proof -
  define p where "p = nth_prime (n - 1)"
  have "p \<ge> 2"
    by (simp add: p_def nth_prime_ge_2)
  have "p \<ge> n" using nth_prime_lower_bound[of "n - 1"] by (simp add: p_def)

  have "c * (n * ln n) \<le> c * (n * ln p)"
    using n c \<open>p \<ge> n\<close> by (intro mult_left_mono) auto
  also {
    from \<open>p \<ge> 2\<close> have "\<pi> (real p) < (1 / c) * (real p / ln (real p))"
      by (rule assms)
    also from n have "\<pi> (real p) = n"
      by (simp add: p_def)
    finally have "c * (n * ln p) < p"
      using c \<open>p \<ge> 2\<close> n by (simp add: field_simps)
  }
  finally show "nth_prime (n - 1) \<ge> c * (real n * ln (real n))"
    using c n by (simp add: p_def)
qed

corollary nth_prime_lower_bound:
  "n > 0 \<Longrightarrow> nth_prime (n - 1) \<ge> (139 / 443) * (n * ln n)"
  using \<pi>_upper_bound' by (intro nth_prime_lower_bound_gen) auto

corollary nth_prime_upper_bound:
  assumes n: "n > 0"
  shows   "nth_prime (n - 1) < 12 * (n * ln n + n * ln (12 / exp 1))"
proof -
  define p where "p = nth_prime (n - 1)"
  have "p \<ge> 2"
    by (simp add: p_def nth_prime_ge_2)

  have "(1 / 6) * (p / ln p) < \<pi> p"
    by (intro \<pi>_lower_bound) (use \<open>p \<ge> 2\<close> in auto)
  also have "\<dots> = n"
    using n by (simp add: p_def)
  finally have less: "p < 6 * n * ln p"
    using \<open>p \<ge> 2\<close> by (simp add: field_simps)

  also have "ln p \<le> (2 / exp 1) * sqrt p"
    using \<pi>_upper_bound_aux[of "1 / 2" p] \<open>p \<ge> 2\<close>
    by (simp add: field_simps powr_minus powr_half_sqrt)
  finally have "sqrt p * sqrt p < 12 / exp 1 * n * sqrt p"
    using n by simp
  hence "sqrt p < 12 / exp 1 * n"
    by (subst (asm) mult_less_cancel_right) (use \<open>p \<ge> 2\<close> in auto)
  hence "ln (sqrt p) < ln (12 / exp 1 * n)"
    using n \<open>p \<ge> 2\<close> by (subst ln_less_cancel_iff) auto
  also have "ln (sqrt p) = ln p / 2"
    using \<open>p \<ge> 2\<close> by (simp add: ln_sqrt)
  also have "ln (12 / exp 1 * n) = ln n + ln (12 / exp 1)"
    using n by (simp add: ln_div ln_mult)
  finally have ln_less: "ln p \<le> 2 * ln n + 2 * ln (12 / exp 1)"
    by simp

  have "p < 6 * n * ln p" by (fact less)
  also have "\<dots> \<le> 6 * n * (2 * ln n + 2 * ln (12 / exp 1))"
    by (intro mult_left_mono ln_less) auto
  also have "\<dots> = 12 * (n * ln n + n * ln (12 / exp 1))"
    by (simp add: algebra_simps)
  finally show ?thesis unfolding p_def .
qed

text \<open>
  We can thus also conclude that $p_n \sim n \ln n$:
\<close>
corollary nth_prime_bigtheta: "nth_prime \<in> \<Theta>(\<lambda>n. n * ln n)"
proof
  have "eventually (\<lambda>n. \<bar>nth_prime n\<bar> \<le>
           12 * \<bar>(n + 1) * ln (n + 1) + (n + 1) * ln (12 / exp 1)\<bar>) at_top"
    using eventually_ge_at_top[of 2]
  proof eventually_elim
    case (elim n)
    with nth_prime_upper_bound[of "n + 1"] show ?case by (auto simp: add_ac)
  qed
  hence "nth_prime \<in> O(\<lambda>n. (n + 1) * ln (n + 1) + (n + 1) * ln (12 / exp 1))"
    by (intro bigoI[where c = 12]) auto
  also have "(\<lambda>n. (n + 1) * ln (n + 1) + (n + 1) * ln (12 / exp 1)) \<in> O(\<lambda>n::nat. n * ln n)"
    by real_asymp
  finally show "nth_prime \<in> O(\<lambda>n. n * ln n)" .
next
  have "eventually (\<lambda>n. \<bar>nth_prime n\<bar> \<ge> 139 / 443 * \<bar>(n + 1) * ln (n + 1)\<bar>) at_top"
    using eventually_ge_at_top[of 2]
  proof eventually_elim
    case (elim n)
    with nth_prime_lower_bound[of "n + 1"] show ?case by (auto simp: add_ac)
  qed
  hence "nth_prime \<in> \<Omega>(\<lambda>n::nat. real (n + 1) * ln (real n + 1))"
    by (intro landau_omega.bigI[where c = "139 / 443"]) (auto simp: add_ac)
  also have "(\<lambda>n::nat. real (n + 1) * ln (real n + 1)) \<in> \<Omega>(\<lambda>n. n * ln n)"
    by real_asymp
  finally show "nth_prime \<in> \<Omega>(\<lambda>n. n * ln n)" .
qed

end

end