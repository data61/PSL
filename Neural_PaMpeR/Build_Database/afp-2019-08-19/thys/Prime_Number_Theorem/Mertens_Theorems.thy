(*
  File:     Mertens_Theorems.thy
  Author:   Manuel Eberl (TU München)

*)
section \<open>Mertens' Theorems\<close>
theory Mertens_Theorems
imports
  Prime_Counting_Functions
  "Stirling_Formula.Stirling_Formula"
begin

(*<*)
unbundle prime_counting_notation
(*>*)

text \<open>
  In this section, we will prove Mertens' First and Second Theorem. These are weaker results
  than the Prime Number Theorem, and we will derive them without using it.

  However, like Mertens himself, we will not only prove them \<^emph>\<open>asymptotically\<close>, but \<^emph>\<open>absolutely\<close>.
  This means that we will show that the remainder terms are not only ``Big-O'' of some bound, but
  we will give concrete (and reasonably tight) upper and lower bounds for them that hold on the 
  entire domain. This makes the proofs a bit more tedious.
\<close>

subsection \<open>Absolute Bounds for Mertens' First Theorem\<close>

text \<open>
  We have already shown the asymptotic form of Mertens' first theorem, i.\,e.\ 
  $\mathfrak{M}(n) = \ln n + O(1)$. We now want to obtain some absolute bounds on the $O(1)$
  remainder term using a more careful derivation than before.

  The precise bounds we will show are
  $\mathfrak {M}(n) - \ln n \in (-1-\frac{9}{\pi^2}; \ln 4] \approx (-1.9119; 1.3863]$ for
  \<open>n \<in> \<nat>\<close>.

  First, we need a simple lemma on the finiteness of exponents to consider in a sum
  of all prime powers up to a certain point:
\<close>
lemma exponents_le_finite:
  assumes "p > (1 :: nat)" "k > 0"
  shows   "finite {i. real (p ^ (k * i + l)) \<le> x}"
proof (rule finite_subset)
  show "{i. real (p ^ (k * i + l)) \<le> x} \<subseteq> {..nat \<lfloor>x\<rfloor>}"
  proof safe
    fix i assume i: "real (p ^ (k * i + l)) \<le> x"
    have "i < 2 ^ i" by (induction i) auto
    also from assms have "i \<le> k * i + l" by (cases k) auto
    hence "2 ^ i \<le> (2 ^ (k * i + l) :: nat)"
      using assms by (intro power_increasing) auto
    also have "\<dots> \<le> p ^ (k * i + l)" using assms by (intro power_mono) auto
    also have "real \<dots> \<le> x" using i by simp
    finally show "i \<le> nat \<lfloor>x\<rfloor>" by linarith
  qed
qed auto

text \<open>
  Next, we need the following bound on $\zeta'(2)$:
\<close>
lemma deriv_zeta_2_bound: "Re (deriv zeta 2) > -1"
proof -
  have "((\<lambda>x::real. ln (x + 3) * (x + 3) powr -2) has_integral (ln 3 + 1) / 3) (interior {0..})"
    using ln_powr_has_integral_at_top[of 1 0 3 "-2"]
    by (simp add: interior_real_atLeast powr_minus)
  hence "((\<lambda>x::real. ln (x + 3) * (x + 3) powr -2) has_integral (ln 3 + 1) / 3) {0..}"
    by (subst (asm) has_integral_interior) auto
  also have "?this \<longleftrightarrow> ((\<lambda>x::real. ln (x + 3) / (x + 3) ^ 2) has_integral (ln 3 + 1) / 3) {0..}"
    by (intro has_integral_cong) (auto simp: powr_minus field_simps) 
  finally have int: \<dots> .  
  have "exp (1 / 2 :: real) ^ 2 \<le> 2 ^ 2"
    using exp_le by (subst exp_double [symmetric]) simp_all
  hence exp_half: "exp (1 / 2 :: real) \<le> 2"
    by (rule power2_le_imp_le) auto

  have mono: "ln x / x ^ 2 \<le> ln y / y ^ 2" if "y \<ge> exp (1/2)" "x \<ge> y" for x y :: real
  proof (rule DERIV_nonpos_imp_nonincreasing[of _ _ "\<lambda>x. ln x / x ^ 2"])
    fix t assume t: "t \<ge> y" "t \<le> x"
    have "y > 0" by (rule less_le_trans[OF _ that(1)]) auto
    with t that have "ln t \<ge> ln (exp (1 / 2))"
      by (subst ln_le_cancel_iff) auto
    hence "ln t \<ge> 1 / 2" by (simp only: ln_exp)
    from t \<open>y > 0\<close> have "((\<lambda>x. ln x / x ^ 2) has_field_derivative ((1 - 2 * ln t) / t ^ 3)) (at t)"
      by (auto intro!: derivative_eq_intros simp: eval_nat_numeral field_simps)
    moreover have "(1 - 2 * ln t) / t ^ 3 \<le> 0"
      using t that \<open>y > 0\<close> \<open>ln t \<ge> 1 / 2\<close> by (intro divide_nonpos_pos) auto
    ultimately show "\<exists>f'. ((\<lambda>x. ln x / x ^ 2) has_field_derivative f') (at t) \<and> f' \<le> 0" by blast
  qed fact+

  have "fds_converges (fds_deriv fds_zeta) (2 :: complex)"
    by (intro fds_converges_deriv) auto
  hence "(\<lambda>n. of_real (-ln (real (Suc n)) / (of_nat (Suc n)) ^ 2)) sums deriv zeta 2"
    by (auto simp: fds_converges_altdef add_ac eval_fds_deriv_zeta fds_nth_deriv scaleR_conv_of_real 
             simp del: of_nat_Suc)
  note * = sums_split_initial_segment[OF sums_minus[OF sums_Re[OF this]], of 3]
    have "(\<lambda>n. ln (real (n+4)) / real (n+4) ^ 2) sums (-Re (deriv zeta 2) - (ln 2 / 4 + ln 3 / 9))"
      using * by (simp add: eval_nat_numeral)
  hence "-Re (deriv zeta 2) - (ln 2 / 4 + ln 3 / 9) =
            (\<Sum>n. ln (real (Suc n) + 3) / (real (Suc n) + 3) ^ 2)"
    by (simp_all add: sums_iff algebra_simps)
  also have "\<dots> \<le> (ln 3 + 1) / 3" using int exp_half
    by (intro decreasing_sum_le_integral divide_nonneg_pos mono) (auto simp: powr_minus field_simps)
  finally have "-Re (deriv zeta 2) \<le> (16 * ln 3 + 9 * ln 2 + 12) / 36"
    by simp
  also have "ln 3 \<le> (11 / 10 :: real)"
    using ln_approx_bounds[of 3 2] by (simp add: power_numeral_reduce numeral_2_eq_2)
  hence "(16 * ln 3 + 9 * ln 2 + 12) / 36 \<le> (16 * (11 / 10) + 9 * 25 / 36 + 12) / (36 :: real)"
    using ln2_le_25_over_36 by (intro add_mono mult_left_mono divide_right_mono) auto
  also have "\<dots> < 1" by simp
  finally show ?thesis by simp
qed

text \<open>
  Using the logarithmic derivative of Euler's product formula for $\zeta(s)$ at $s = 2$
  and the bound on $\zeta'(2)$ we have just derived, we can obtain the bound
  \[\sum_{p^i \leq x, i \geq 2} \frac{\ln p}{p^i} < \frac{9}{\pi^2}\ .\]
\<close>
lemma mertens_remainder_aux_bound:
  fixes x :: real
  defines "R \<equiv> (\<Sum>(p,i) | prime p \<and> i > 1 \<and> real (p ^ i) \<le> x. ln (real p) / p ^ i)"
  shows   "R < 9 / pi\<^sup>2"
proof -
  define S' where "S' = {(p, i). prime p \<and> i > 1 \<and> real (p ^ i) \<le> x}"
  define S'' where "S'' = {(p, i). prime p \<and> i > 1 \<and> real (p ^ Suc i) \<le> x}"

  have finite_row: "finite {i. i > 1 \<and> real (p ^ (i + k)) \<le> x}" if p: "prime p" for p k
  proof (rule finite_subset)
    show "{i. i > 1 \<and> real (p ^ (i + k)) \<le> x} \<subseteq> {..nat \<lfloor>x\<rfloor>}"
    proof safe
      fix i assume i: "i > 1" "real (p ^ (i + k)) \<le> x"
      have "i < 2 ^ (i + k)" by (induction i) auto
      also from p have "\<dots> \<le> p ^ (i + k)" by (intro power_mono) (auto dest: prime_gt_1_nat) 
      also have "real \<dots> \<le> x" using i by simp
      finally show "i \<le> nat \<lfloor>x\<rfloor>" by linarith
    qed
  qed auto

  have "S'' \<subseteq> S'" unfolding S''_def S'_def
  proof safe
    fix p i assume pi: "prime p" "real (p ^ Suc i) \<le> x" "i > 1"
    have "real (p ^ i) \<le> real (p ^ Suc i)"
      using pi unfolding of_nat_le_iff by (intro power_increasing) (auto dest: prime_gt_1_nat)
    also have "\<dots> \<le> x" by fact
    finally show "real (p ^ i) \<le> x" .
  qed

  have S'_alt:  "S' = (SIGMA p:{p. prime p \<and> real p \<le> x}. {i. i > 1 \<and> real (p ^ i) \<le> x})"
    unfolding S'_def
  proof safe
    fix p i assume "prime p" "real (p ^ i) \<le> x" "i > 1"
    hence "p ^ 1 \<le> p ^ i"
      by (intro power_increasing) (auto dest: prime_gt_1_nat)
    also have "real \<dots> \<le> x" by fact
    finally show "real p \<le> x" by simp
  qed

  have finite: "finite {p. prime p \<and> real p \<le> x}"
    by (rule finite_subset[OF _ finite_Nats_le_real[of x]]) (auto dest: prime_gt_0_nat)
  have "finite S'" unfolding S'_alt using finite_row[of _ 0]
    by (intro finite_SigmaI finite) auto

  have "R \<le> 3 / 2 * (\<Sum>(p, i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ i))"
  proof -
    have "R = (\<Sum>y\<in>{0, 1}. \<Sum>z | z \<in> S' \<and> snd z mod 2 = y. ln (real (fst z)) / real (fst z ^ snd z))"
      using \<open>finite S'\<close> by (subst sum.group) (auto simp: case_prod_unfold R_def S'_def)
    also have "\<dots> = (\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ i)) +
                    (\<Sum>(p,i) | (p, i) \<in> S' \<and> odd i. ln (real p) / real (p ^ i))"
      unfolding even_iff_mod_2_eq_zero odd_iff_mod_2_eq_one by (simp add: case_prod_unfold)
    also have "(\<Sum>(p,i) | (p, i) \<in> S' \<and> odd i. ln (real p) / real (p ^ i)) =
                 (\<Sum>(p,i) | (p, i) \<in> S'' \<and> even i. ln (real p) / real (p ^ Suc i))"
      by (intro sum.reindex_bij_witness[of _ "\<lambda>(p,i). (p, Suc i)" "\<lambda>(p,i). (p, i - 1)"])
         (auto simp: case_prod_unfold S'_def S''_def elim: oddE simp del: power_Suc)
    also have "\<dots> \<le> (\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ Suc i))"
      using \<open>S'' \<subseteq> S'\<close> unfolding case_prod_unfold
      by (intro sum_mono2 divide_nonneg_pos ln_ge_zero finite_subset[OF _ \<open>finite S'\<close>])
         (auto simp: S'_def S''_def case_prod_unfold dest: prime_gt_0_nat simp del: power_Suc)
    also have "\<dots> \<le> (\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (2 * p ^ i))"
      unfolding case_prod_unfold
      by (intro sum_mono divide_left_mono) (auto simp: S'_def dest!: prime_gt_1_nat)
    also have "\<dots> = (1 / 2) * (\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ i))"
      by (subst sum_distrib_left) (auto simp: case_prod_unfold)
    also have "(\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ i)) + \<dots> =
                   3 / 2 * (\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ i))"
      by simp
    finally show ?thesis by simp
  qed

  also have "(\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ i)) =
               (\<Sum>p | prime p \<and> real p \<le> x. ln (real p) * 
                 (\<Sum>i | i > 0 \<and> even i \<and> real (p ^ i) \<le> x. (1 / real p) ^ i))"
   unfolding sum_distrib_left
  proof (subst sum.Sigma[OF _ ballI])
    fix p assume p: "p \<in> {p. prime p \<and> real p \<le> x}"
    thus "finite {i. 0 < i \<and> even i \<and> real (p ^ i) \<le> x}"
      by (intro finite_subset[OF _ exponents_le_finite[of p 1 0 x]]) (auto dest: prime_gt_1_nat)
  qed (auto intro!: sum.cong finite_subset[OF _ finite_Nats_le_real[of x]]
            dest: prime_gt_0_nat simp: S'_alt power_divide)
  also have "\<dots> \<le> (\<Sum>p | prime p \<and> real p \<le> x. ln (real p) / (real p ^ 2 - 1))"
  proof (rule sum_mono)
    fix p assume p: "p \<in> {p. prime p \<and> real p \<le> x}"
    have "p > 1" using p by (auto dest: prime_gt_1_nat)
    have "(\<Sum>i | i > 0 \<and> even i \<and> real (p ^ i) \<le> x. (1 / real p) ^ i) =
            (\<Sum>i | real (p ^ (2 * i + 2)) \<le> x. (1 / real p) ^ (2 * i)) / real p ^ 2"
      (is "_ = ?S / _") unfolding sum_divide_distrib
      by (rule sum.reindex_bij_witness[of _ "\<lambda>i. 2 * Suc i" "\<lambda>i. (i - 2) div 2"])
         (insert \<open>p > 1\<close>, auto simp: numeral_3_eq_3 power2_eq_square power_diff
                 algebra_simps elim!: evenE)
    also have "?S = (\<Sum>i | real (p ^ (2 * i + 2)) \<le> x. (1 / real p ^ 2) ^ i)"
      by (subst power_mult) (simp_all add: algebra_simps power_divide)
    also have "\<dots> \<le> (\<Sum>i. (1 / real p ^ 2) ^ i)"
      using exponents_le_finite[of p 2 2 x] \<open>p > 1\<close>
      by (intro sum_le_suminf) (auto simp: summable_geometric_iff)
    also have "\<dots> = real p ^ 2 / (real p ^ 2 - 1)"
      using \<open>p > 1\<close> by (subst suminf_geometric) (auto simp: field_simps)
    also have "\<dots> / real p ^ 2 = 1 / (real p ^ 2 - 1)"
      using \<open>p > 1 \<close> by (simp add: divide_simps)
    finally have "(\<Sum>i | 0 < i \<and> even i \<and> real (p ^ i) \<le> x. (1 / real p) ^ i) \<le>
                     1 / (real p ^ 2 - 1)" (is "?lhs \<le> ?rhs")
      using \<open>p > 1\<close> by (simp add: divide_right_mono)
    thus "ln (real p) * ?lhs \<le> ln (real p) / (real p ^ 2 - 1)"
      using \<open>p > 1\<close> by (simp add: divide_simps)
  qed
  also have "\<dots> = (\<Sum>\<^sub>a p | prime p \<and> real p \<le> x. ln (real p) / (real p ^ 2 - 1))"
    using finite by (intro infsetsum_finite [symmetric]) auto
  also have "\<dots> \<le> (\<Sum>\<^sub>a p | prime p. ln (real p) / (real p ^ 2 - 1))"
    using eval_fds_logderiv_zeta_real[of 2] finite
    by (intro infsetsum_mono_neutral_left divide_nonneg_pos) (auto simp: dest: prime_gt_1_nat)
  also have "\<dots> = -Re (deriv zeta (of_real 2) / zeta (of_real 2))"
    by (subst eval_fds_logderiv_zeta_real) auto
  also have "\<dots> = (-Re (deriv zeta 2)) * (6 / pi\<^sup>2)"
    by (simp add: zeta_even_numeral)
  also have "\<dots> < 1 * (6 / pi\<^sup>2)"
    using deriv_zeta_2_bound by (intro mult_strict_right_mono) auto
  also have "3 / 2 * \<dots> = 9 / pi\<^sup>2" by simp
  finally show ?thesis by simp
qed

text \<open>
  We now consider the equation
  \[\ln (n!) = \sum_{k\leq n} \Lambda(k) \left\lfloor\frac{n}{k}\right\rfloor\]
  and estimate both sides in different ways. The left-hand-side can be estimated
  using Stirling's formula, and we can simplify the right-hand side to
  \[\sum_{k\leq n} \Lambda(k) \left\lfloor\frac{n}{k}\right\rfloor =
      \sum_{p^i \leq x, i \geq 1} \ln p \left\lfloor\frac{n}{p^i}\right\rfloor\]
  and then split the sum into those $p^i$ with $i = 1$ and those with $i \geq 2$.
  Applying the bound we have just shown and some more routine estimates, we obtain the
  following reasonably strong version of Mertens' First Theorem on the naturals:
  $\mathfrak M(n) - \ln(n) \in (-1-\frac{9}{\pi^2}; \ln 4]$
\<close>
theorem mertens_bound_strong:
  fixes n :: nat assumes n: "n > 0"
  shows   "\<MM> n - ln n \<in> {-1 - 9 / pi\<^sup>2<..ln 4}"
proof (cases "n \<ge> 3")
  case False
  with n consider "n = 1" | "n = 2" by force
  thus ?thesis
  proof cases
    assume [simp]: "n = 1"
    have "-1 + (-9 / pi\<^sup>2) < 0"
      by (intro add_neg_neg divide_neg_pos) auto
    thus ?thesis by simp
  next
    assume [simp]: "n = 2"
    have eq: "\<MM> n - ln n = -ln 2 / 2" by (simp add: eval_\<MM>)
    have "-1 - 9 / pi ^ 2 + ln 2 / 2 \<le> -1 - 9 / 4 ^ 2 + 25 / 36 / 2"
      using pi_less_4 ln2_le_25_over_36
      by (intro diff_mono add_mono divide_left_mono divide_right_mono power_mono) auto
    also have "\<dots> < 0" by simp
    finally have "-ln 2 / 2 > -1 - 9 / pi\<^sup>2" by simp
    moreover {
      have "-ln 2 / 2 \<le> (0::real)" by (intro divide_nonpos_pos) auto
      also have "\<dots> \<le> ln 4" by simp
      finally have "-ln 2 / 2 \<le> ln (4 :: real)" by simp
    }
    ultimately show ?thesis unfolding eq by simp
  qed

next
  case True
  hence n: "n \<ge> 3" by simp
  have finite: "finite {(p, i). prime p \<and> i \<ge> 1 \<and> p ^ i \<le> n}"
  proof (rule finite_subset)
    show "{(p, i). prime p \<and> i \<ge> 1 \<and> p ^ i \<le> n}
            \<subseteq> {..nat \<lfloor>root 1 (real n)\<rfloor>} \<times> {..nat \<lfloor>log 2 (real n)\<rfloor>}"
      using primepows_le_subset[of "real n" 1] n unfolding of_nat_le_iff by auto
  qed auto

  define r where "r = prime_sum_upto (\<lambda>p. ln (real p) * frac (real n / real p)) n"
  define R where "R = (\<Sum>(p,i) | prime p \<and> i > 1 \<and> p ^ i \<le> n. ln (real p) * real (n div (p ^ i)))"
  define R' where "R' = (\<Sum>(p,i) | prime p \<and> i > 1 \<and> p ^ i \<le> n. ln (real p) / p ^ i)"
  have [simp]: "ln (4 :: real) = 2 * ln 2"
    using ln_realpow[of 2 2] by simp
  from pi_less_4 have "ln pi \<le> ln 4" by (subst ln_le_cancel_iff) auto
  also have "\<dots> = 2 * ln 2" by simp
  also have "\<dots> \<le> 2 * (25 / 36)" by (intro mult_left_mono ln2_le_25_over_36) auto
  finally have ln_pi: "ln pi \<le> 25 / 18" by simp
  have "ln 3 \<le> ln (4::nat)" by (subst ln_le_cancel_iff) auto
  also have "\<dots> = 2 * ln 2" by simp
  also have "\<dots> \<le> 2 * (25 / 36)" by (intro mult_left_mono ln2_le_25_over_36) auto
  finally have ln_3: "ln (3::real) \<le> 25 / 18" by simp
  
  have "R / n = (\<Sum>(p,i) | prime p \<and> i > 1 \<and> p ^ i \<le> n. ln (real p) * (real (n div (p ^ i)) / n))"
    by (simp add: R_def sum_divide_distrib field_simps case_prod_unfold)
  also have "\<dots> \<le> (\<Sum>(p,i) | prime p \<and> i > 1 \<and> p ^ i \<le> n. ln (real p) * (1 / p ^ i))"
    unfolding R'_def case_prod_unfold using n
    by (intro sum_mono mult_left_mono) (auto simp: field_simps real_of_nat_div dest: prime_gt_0_nat)
  also have "\<dots> = R'" by (simp add: R'_def)
  also have "R' < 9 / pi\<^sup>2"
    unfolding R'_def using mertens_remainder_aux_bound[of n] by simp
  finally have "R / n < 9 / pi\<^sup>2" .
  moreover have "R \<ge> 0"
    unfolding R_def by (intro sum_nonneg mult_nonneg_nonneg) (auto dest: prime_gt_0_nat)
  ultimately have R_bounds: "R / n \<in> {0..<9 / pi\<^sup>2}" by simp

  have "ln (fact n :: real) \<le> ln (2 * pi * n) / 2 + n * ln n - n + 1 / (12 * n)"
    using ln_fact_bounds(2)[of n] n by simp
  also have "\<dots> / n - ln n = -1 + (ln 2 + ln pi) / (2 * n) + (ln n / n) / 2 + 1 / (12 * real n ^ 2)"
    using n by (simp add: power2_eq_square field_simps ln_mult)
  also have "\<dots> \<le> -1 + (ln 2 + ln pi) / (2 * 3) + (ln 3 / 3) / 2 + 1 / (12 * 3\<^sup>2)"
    using exp_le n pi_gt3
    by (intro add_mono divide_right_mono divide_left_mono mult_mono
              mult_pos_pos ln_x_over_x_mono power_mono) auto
  also have "\<dots> \<le> -1 + (25 / 36 + 25 / 18) / (2 * 3) + (25 / 18 / 3) / 2 + 1 / (12 * 3\<^sup>2)"
    using ln_pi ln2_le_25_over_36 ln_3 by (intro add_mono divide_left_mono divide_right_mono) auto
  also have "\<dots> \<le> 0" by simp
  finally have "ln n - ln (fact n) / n \<ge> 0" using n by (simp add: divide_right_mono)
  have "-ln (fact n) \<le> -ln (2 * pi * n) / 2 - n * ln n + n"
    using ln_fact_bounds(1)[of n] n by simp
  also have "ln n + \<dots> / n = -ln (2 * pi) / (2 * n) - (ln n / n) / 2 + 1"
    using n by (simp add: field_simps ln_mult)
  also have "\<dots> \<le> 0 - 0 + 1"
    using pi_gt3 n by (intro add_mono diff_mono) auto
  finally have upper: "ln n - ln (fact n) / n \<le> 1"
    using n by (simp add: divide_right_mono)
  with \<open>ln n - ln (fact n) / n \<ge> 0\<close> have fact_bounds: "ln n - ln (fact n) / n \<in> {0..1}" by simp

  have "r \<le> prime_sum_upto (\<lambda>p. ln p * 1) n"
    using less_imp_le[OF frac_lt_1] unfolding r_def \<theta>_def prime_sum_upto_def
    by (intro sum_mono mult_left_mono) (auto simp: dest: prime_gt_0_nat)
  also have "\<dots> = \<theta> n" by (simp add: \<theta>_def)
  also have "\<dots> < ln 4 * n" using n by (intro \<theta>_upper_bound) auto
  finally have "r / n < ln 4" using n by (simp add: field_simps)
  moreover have "r \<ge> 0" unfolding r_def prime_sum_upto_def
    by (intro sum_nonneg mult_nonneg_nonneg) (auto dest: prime_gt_0_nat)
  ultimately have r_bounds: "r / n \<in> {0..<ln 4}" by simp

  have "ln (fact n :: real) = sum_upto (\<lambda>k. mangoldt k * real (n div k)) (real n)"
    by (simp add: ln_fact_conv_sum_upto_mangoldt)
  also have "\<dots> = (\<Sum>(p,i) | prime p \<and> i > 0 \<and> real (p ^ i) \<le> real n.
                       ln (real p) * real (n div (p ^ i)))"
    by (intro sum_upto_primepows) (auto simp: mangoldt_non_primepow)
  also have "{(p, i). prime p \<and> i > 0 \<and> real (p ^ i) \<le> real n} =
               {(p, i). prime p \<and> i = 1 \<and> p \<le> n} \<union>
               {(p, i). prime p \<and> i > 1 \<and> (p ^ i) \<le> n}" unfolding of_nat_le_iff
    by (auto simp: not_less le_Suc_eq)
  also have "(\<Sum>(p,i)\<in>\<dots>. ln (real p) * real (n div (p ^ i))) =
               (\<Sum>(p,i) | prime p \<and> i = 1 \<and> p \<le> n. ln (real p) * real (n div (p ^ i))) + R"
    (is "_ = ?S + _")
    by (subst sum.union_disjoint) (auto intro!: finite_subset[OF _ finite] simp: R_def)
  also have "?S = prime_sum_upto (\<lambda>p. ln (real p) * real (n div p)) n"
    unfolding prime_sum_upto_def
    by (intro sum.reindex_bij_witness[of _ "\<lambda>p. (p, 1)" fst]) auto
  also have "\<dots> = prime_sum_upto (\<lambda>p. ln (real p) * real n / real p) n - r"
    unfolding r_def prime_sum_upto_def sum_subtractf[symmetric] using n
    by (intro sum.cong) (auto simp: frac_def real_of_nat_div algebra_simps)
  also have "prime_sum_upto (\<lambda>p. ln (real p) * real n / real p) n = n * \<MM> n"
    by (simp add: primes_M_def sum_distrib_left sum_distrib_right prime_sum_upto_def field_simps)
  finally have "\<MM> n - ln n = ln (fact n) / n - ln n + r / n - R / n"
    using n by (simp add: field_simps)
  hence "ln n - \<MM> n = ln n - ln (fact n) / n - r / n + R / n"
    by simp
  with fact_bounds r_bounds R_bounds show "\<MM> n - ln n \<in> {-1 - 9 / pi\<^sup>2<..ln 4}"
    by simp
qed

text \<open>
  As a simple corollary, we obtain a similar bound on the reals.
\<close>
lemma mertens_bound_real_strong:
  fixes x :: real assumes x: "x \<ge> 1"
  shows   "\<MM> x - ln x \<in> {-1 - 9 / pi ^ 2 - ln (1 + frac x / real (nat \<lfloor>x\<rfloor>)) <.. ln 4}"
proof -
  have "\<MM> x - ln x \<le> \<MM> (real (nat \<lfloor>x\<rfloor>)) - ln (real (nat \<lfloor>x\<rfloor>))"
    using assms by simp
  also have "\<dots> \<le> ln 4"
    using mertens_bound_strong[of "nat \<lfloor>x\<rfloor>"] assms by simp
  finally have "\<MM> x - ln x \<le> ln 4" .

  from assms have pos: "real_of_int \<lfloor>x\<rfloor> \<noteq> 0" by linarith
  have "frac x / real (nat \<lfloor>x\<rfloor>) \<ge> 0"
    using assms by (intro divide_nonneg_pos) auto
  moreover have "frac x / real (nat \<lfloor>x\<rfloor>) \<le> 1 / 1"
    using assms frac_lt_1[of x] by (intro frac_le) auto
  ultimately have *: "frac x / real (nat \<lfloor>x\<rfloor>) \<in> {0..1}" by auto
  have "ln x - ln (real (nat \<lfloor>x\<rfloor>)) = ln (x / real (nat \<lfloor>x\<rfloor>))"
    using assms by (subst ln_div) auto
  also have "x / real (nat \<lfloor>x\<rfloor>) = 1 + frac x / real (nat \<lfloor>x\<rfloor>)"
    using assms pos by (simp add: frac_def field_simps)
  finally have "\<MM> x - ln x > -1-9/pi^2-ln (1 + frac x / real (nat \<lfloor>x\<rfloor>))"
    using mertens_bound_strong[of "nat \<lfloor>x\<rfloor>"] x by simp
  with \<open>\<MM> x - ln x \<le> ln 4\<close> show ?thesis by simp
qed

text \<open>
  We weaken this estimate a bit to obtain nicer bounds:
\<close>
lemma mertens_bound_real':
  fixes x :: real assumes x: "x \<ge> 1"
  shows   "\<MM> x - ln x \<in> {-2<..25/18}"
proof -
  have "\<MM> x - ln x \<le> ln 4"
    using mertens_bound_real_strong[of x] x by simp
  also have "\<dots> \<le> 25 / 18"
    using ln_realpow[of 2 2] ln2_le_25_over_36 by simp
  finally have "\<MM> x - ln x \<le> 25 / 18" .

  have ln2: "ln (2 :: real) \<in> {2/3..25/36}"
    using ln_approx_bounds[of 2 1] by (simp add: eval_nat_numeral)
  have ln3: "ln (3::real) \<in> {1..10/9}"
    using ln_approx_bounds[of 3 1] by (simp add: eval_nat_numeral)
  have ln5: "ln (5::real) \<in> {4/3..76/45}"
    using ln_approx_bounds[of 5 1] by (simp add: eval_nat_numeral)
  have ln7: "ln (7::real) \<in> {3/2..15/7}"
    using ln_approx_bounds[of 7 1] by (simp add: eval_nat_numeral)
  have ln11: "ln (11::real) \<in> {5/3..290/99}"
    using ln_approx_bounds[of 11 1] by (simp add: eval_nat_numeral)

  \<comment> \<open>Choosing the lower bound -2 is somewhat arbitrary here; it is a trade-off between getting
      a reasonably tight bound and having to make lots of case distinctions. To get -2 as a lower
      bound, we have to show the cases up to \<open>x = 11\<close> by case distinction,\<close>
  have "\<MM> x - ln x > -2"
  proof (cases "x \<ge> 11")
    case False
    hence "x \<in> {1..<2} \<or> x \<in> {2..<3} \<or> x \<in> {3..<5} \<or> x \<in> {5..<7} \<or> x \<in> {7..<11}"
      using x by force
    thus ?thesis
    proof (elim disjE)
      assume x: "x \<in> {1..<2}"
      hence "ln x - \<MM> x \<le> ln 2 - 0"
        by (intro diff_mono) auto
      also have "\<dots> < 2" using ln2_le_25_over_36 by simp
      finally show ?thesis by simp
    next
      assume x: "x \<in> {2..<3}"
      hence [simp]: "\<lfloor>x\<rfloor> = 2" by (intro floor_unique) auto
      from x have "ln x - \<MM> x \<le> ln 3 - ln 2 / 2"
        by (intro diff_mono) (auto simp: eval_\<MM>)
      also have "\<dots> = ln (9 / 2) / 2" using ln_realpow[of 3 2] by (simp add: ln_div)
      also have "\<dots> < 2" using ln_approx_bounds[of "9 / 2" 1] by (simp add: eval_nat_numeral)
      finally show ?thesis by simp
    next
      assume x: "x \<in> {3..<5}"
      hence "\<MM> 3 = \<MM> x"
        unfolding primes_M_def
        by (intro prime_sum_upto_eqI'[where a' = 3 and b' = 4])
           (auto simp: nat_le_iff le_numeral_iff nat_eq_iff floor_eq_iff)
      also have "\<MM> 3 = ln 2 / 2 + ln 3 / 3"
        by (simp add: eval_\<MM> eval_nat_numeral mark_out_code)
      finally have [simp]: "\<MM> x = ln 2 / 2 + ln 3 / 3" ..
      from x have "ln x - \<MM> x \<le> ln 5 - (ln 2 / 2 + ln 3 / 3)"
        by (intro diff_mono) auto
      also have "\<dots> < 2" using ln2 ln3 ln5 by simp
      finally show ?thesis by simp
    next
      assume x: "x \<in> {5..<7}"
      hence "\<MM> 5 = \<MM> x"
        unfolding primes_M_def
        by (intro prime_sum_upto_eqI'[where a' = 5 and b' = 6])
           (auto simp: nat_le_iff le_numeral_iff nat_eq_iff floor_eq_iff)
      also have "\<MM> 5 = ln 2 / 2 + ln 3 / 3 + ln 5 / 5"
        by (simp add: eval_\<MM> eval_nat_numeral mark_out_code)
      finally have [simp]: "\<MM> x = ln 2 / 2 + ln 3 / 3 + ln 5 / 5" ..
      from x have "ln x - \<MM> x \<le> ln 7 - (ln 2 / 2 + ln 3 / 3 + ln 5 / 5)"
        by (intro diff_mono) auto
      also have "\<dots> < 2" using ln2 ln3 ln5 ln7 by simp
      finally show ?thesis by simp
    next
      assume x: "x \<in> {7..<11}"
      hence "\<MM> 7 = \<MM> x"
        unfolding primes_M_def
        by (intro prime_sum_upto_eqI'[where a' = 7 and b' = 10])
           (auto simp: nat_le_iff le_numeral_iff nat_eq_iff floor_eq_iff)
      also have "\<MM> 7 = ln 2 / 2 + ln 3 / 3 + ln 5 / 5 + ln 7 / 7"
        by (simp add: eval_\<MM> eval_nat_numeral mark_out_code)
      finally have [simp]: "\<MM> x = ln 2 / 2 + ln 3 / 3 + ln 5 / 5 + ln 7 / 7" ..
      from x have "ln x - \<MM> x \<le> ln 11 - (ln 2 / 2 + ln 3 / 3 + ln 5 / 5 + ln 7 / 7)"
        by (intro diff_mono) auto
      also have "\<dots> < 2" using ln2 ln3 ln5 ln7 ln11 by simp
      finally show ?thesis by simp
    qed
  next
    case True
    have "ln x - \<MM> x \<le> 1 + 9/pi^2 + ln (1 + frac x / real (nat \<lfloor>x\<rfloor>))"
      using mertens_bound_real_strong[of x] x by simp
    also have "1 + frac x / real (nat \<lfloor>x\<rfloor>) \<le> 1 + 1 / 11"
      using True frac_lt_1[of x] by (intro add_mono frac_le) auto
    hence "ln (1 + frac x / real (nat \<lfloor>x\<rfloor>)) \<le> ln (1 + 1 / 11)"
      using x by (subst ln_le_cancel_iff) (auto intro!: add_pos_nonneg)
    also have "\<dots> = ln (12 / 11)" by simp
    also have "\<dots> \<le> 1585 / 18216"
      using ln_approx_bounds[of "12 / 11" 1] by (simp add: eval_nat_numeral)
    also have "9 / pi ^ 2 \<le> 9 / 3.141592653588 ^ 2"
      using pi_approx by (intro divide_left_mono power_mono mult_pos_pos) auto
    also have "1 + \<dots> + 1585 / 18216 < 2"
      by (simp add: power2_eq_square)
    finally show ?thesis by simp
  qed
  with \<open>\<MM> x - ln x \<le> 25 / 18\<close> show ?thesis by simp
qed

corollary mertens_first_theorem:
  fixes x :: real assumes x: "x \<ge> 1"
  shows   "\<bar>\<MM> x - ln x\<bar> < 2"
  using mertens_bound_real'[of x] x by (simp add: abs_if)


subsection \<open>Mertens' Second Theorem\<close>

text \<open>
  Mertens' Second Theorem concerns the asymptotics of the Prime Harmonic Series, namely
  \[\sum\limits_{p \leq x} \frac{1}{p} = \ln\ln x + M + O\left(\frac{1}{\ln x}\right)\]
  where $M \approx 0.261497$ is the Meissel--Mertens constant.

  We define the constant in the following way:
\<close>
definition meissel_mertens where
  "meissel_mertens = 1 - ln (ln 2) + integral {2..} (\<lambda>t. (\<MM> t - ln t) / (t * ln t ^ 2))"

text \<open>
  We will require the value of the integral
  $\int_a^\infty \frac{t}{\ln^2 t} \textrm{d}t = \frac{1}{\ln a}$
  as an upper bound on the remainder term:
\<close>
lemma integral_one_over_x_ln_x_squared:
  assumes a: "(a::real) > 1"
  shows "set_integrable lborel {a<..} (\<lambda>t. 1 / (t * ln t ^ 2))" (is ?th1)
    and "set_lebesgue_integral lborel {a<..} (\<lambda>t. 1 / (t * ln t ^ 2)) = 1 / ln a" (is ?th2)
    and "((\<lambda>t. 1 / (t * (ln t)\<^sup>2)) has_integral 1 / ln a) {a<..}" (is ?th3)
proof -
  have cont: "isCont (\<lambda>t. 1 / (t * (ln t)\<^sup>2)) x" if "x > a" for x
    using that a by (auto intro!: continuous_intros)
  have deriv: "((\<lambda>x. -1 / ln x) has_real_derivative 1 / (x * (ln x)\<^sup>2)) (at x)" if "x > a" for x
    using that a by (auto intro!: derivative_eq_intros simp: power2_eq_square field_simps)
  have lim1: "(((\<lambda>x. - 1 / ln x) \<circ> real_of_ereal) \<longlongrightarrow> -(1 / ln a)) (at_right (ereal a))"
    unfolding ereal_tendsto_simps using a by (real_asymp simp: field_simps)
  have lim2: "(((\<lambda>x. - 1 / ln x) \<circ> real_of_ereal) \<longlongrightarrow> 0) (at_left \<infinity>)"
    unfolding ereal_tendsto_simps using a by (real_asymp simp: field_simps)

  have "set_integrable lborel (einterval a \<infinity>) (\<lambda>t. 1 / (t * ln t ^ 2))"
    by (rule interval_integral_FTC_nonneg[OF _ deriv cont _ lim1 lim2]) (use a in auto)
  thus ?th1 by simp
  have "interval_lebesgue_integral lborel (ereal a) \<infinity> (\<lambda>t. 1 / (t * ln t ^ 2)) = 0 - (-(1 / ln a))"
    by (rule interval_integral_FTC_nonneg[OF _ deriv cont _ lim1 lim2]) (use a in auto)
  thus ?th2 by (simp add: interval_integral_to_infinity_eq)

  have "((\<lambda>t. 1 / (t * ln t ^ 2)) has_integral
           set_lebesgue_integral lebesgue {a<..} (\<lambda>t. 1 / (t * ln t ^ 2))) {a<..}"
    using \<open>?th1\<close> by (intro has_integral_set_lebesgue)
                    (auto simp: set_integrable_def integrable_completion)
  also have "set_lebesgue_integral lebesgue {a<..} (\<lambda>t. 1 / (t * ln t ^ 2)) = 1 / ln a"
    using \<open>?th2\<close> unfolding set_lebesgue_integral_def by (subst integral_completion) auto
  finally show ?th3 .
qed

text \<open>
  We show that the integral in our definition of the Meissel--Mertens constant is
  well-defined and give an upper bound for its tails:
\<close>
lemma
  assumes "a > (1 :: real)"
  defines "r \<equiv> (\<lambda>t. (\<MM> t - ln t) / (t * ln t ^ 2))"
  shows integrable_meissel_mertens:  "set_integrable lborel {a<..} r"
    and meissel_mertens_integral_le: "norm (integral {a<..} r) \<le> 2 / ln a"
proof -
  have *: "((\<lambda>t. 2 * (1 / (t * ln t ^ 2))) has_integral 2 * (1 / ln a)) {a<..}"
    using assms by (intro has_integral_mult_right integral_one_over_x_ln_x_squared) auto
  show "set_integrable lborel {a<..} r" unfolding set_integrable_def
  proof (rule Bochner_Integration.integrable_bound[OF _ _ AE_I2])
    have "integrable lborel (\<lambda>t::real. indicator {a<..} t * (2 * (1 / (t * ln t ^ 2))))"
      using integrable_mult_right[of 2, 
              OF integral_one_over_x_ln_x_squared(1)[of a, unfolded set_integrable_def]] assms
      by (simp add: algebra_simps)
    thus "integrable lborel (\<lambda>t::real. indicator {a<..} t *\<^sub>R (2 / (t * ln t ^ 2)))"
      by simp
    fix x :: real
    show "norm (indicat_real {a<..} x *\<^sub>R r x) \<le>
            norm (indicat_real {a<..} x *\<^sub>R (2 / (x * ln x ^ 2)))"
    proof (cases "x > a")
      case True
      thus ?thesis
      unfolding norm_scaleR norm_mult r_def norm_divide using mertens_first_theorem[of x] assms
        by (intro mult_mono frac_le divide_nonneg_pos) (auto simp: indicator_def)
    qed (auto simp: indicator_def)
  qed (auto simp: r_def)
  hence "r integrable_on {a<..}"
    by (simp add: set_borel_integral_eq_integral(1))
  hence "norm (integral {a<..} r) \<le> integral {a<..} (\<lambda>x. 2 * (1 / (x * ln x ^ 2)))"
  proof (rule integral_norm_bound_integral)
    show  "(\<lambda>x. 2 * (1 / (x * (ln x)\<^sup>2))) integrable_on {a<..}"
      using * by (simp add: has_integral_iff)
    fix x assume "x \<in> {a<..}"
    hence "norm (r x) \<le> 2 / (x * (ln x)\<^sup>2)"
      unfolding r_def norm_divide using mertens_first_theorem[of x] assms
      by (intro mult_mono frac_le divide_nonneg_pos) (auto simp: indicator_def)
    thus "norm (r x) \<le> 2* (1 / (x * ln x ^ 2))" by simp
  qed
  also have "\<dots> = 2 / ln a"
    using * by (simp add: has_integral_iff)
  finally show "norm (integral {a<..} r) \<le> 2 / ln a" .
qed

lemma integrable_on_meissel_mertens:
  assumes "A \<subseteq> {1..}" "Inf A > 1" "A \<in> sets borel"
  shows   "(\<lambda>t. (\<MM> t - ln t) / (t * ln t ^ 2)) integrable_on A"
proof -
  from assms obtain x where x: "1 < x" "x < Inf A"
    using dense by blast
  from assms have "bdd_below A" by (intro bdd_belowI[of _ 1]) auto
  hence "A \<subseteq> {Inf A..}" by (auto simp: cInf_lower)
  also have "\<dots> \<subseteq> {x<..}" using x by auto
  finally have *: "A \<subseteq> {x<..}" .
  have "set_integrable lborel A (\<lambda>t. (\<MM> t - ln t) / (t * ln t ^ 2))"
    by (rule set_integrable_subset[OF integrable_meissel_mertens[of x]]) (use x * assms in auto)
  thus ?thesis by (simp add: set_borel_integral_eq_integral(1))
qed

lemma meissel_mertens_bounds: "\<bar>meissel_mertens - 1 + ln (ln 2)\<bar> \<le> 2 / ln 2"
proof -
  have *: "{2..} - {2<..} = {2::real}" by auto
  also have "negligible \<dots>" by simp
  finally have "integral {2..} (\<lambda>t. (\<MM> t - ln t) / (t * (ln t)\<^sup>2)) =
                  integral {2<..} (\<lambda>t. (\<MM> t - ln t) / (t * (ln t)\<^sup>2))"
    by (intro sym[OF integral_subset_negligible]) auto
  also have "norm \<dots> \<le> 2 / ln 2"
    by (rule meissel_mertens_integral_le) auto
  finally show "\<bar>meissel_mertens - 1 + ln (ln 2)\<bar> \<le> 2 / ln 2"
    by (simp add: meissel_mertens_def)
qed

text \<open>
  Finally, obtaining Mertens' second theorem from the first one is nothing but a routine
  summation by parts, followed by a use of the above bound:
\<close>
theorem mertens_second_theorem:
  defines "f \<equiv> prime_sum_upto (\<lambda>p. 1 / p)"
  shows   "\<And>x. x \<ge> 2 \<Longrightarrow> \<bar>f x - ln (ln x) - meissel_mertens\<bar> \<le> 4 / ln x"
    and   "(\<lambda>x. f x - ln (ln x) - meissel_mertens) \<in> O(\<lambda>x. 1 / ln x)"
proof -
  define r where "r = (\<lambda>t. (\<MM> t - ln t) / (t * ln t ^ 2))"

  {
    fix x :: real assume x: "x > 2"
    have "((\<lambda>t. \<MM> t * (-1 / (t * ln t ^ 2))) has_integral \<MM> x * (1 / ln x) - \<MM> 2 * (1 / ln 2) -
            (\<Sum>n\<in>real -` {2<..x}. ind prime n * (ln n / real n) * (1 / ln n))) {2..x}"
      unfolding primes_M_def prime_sum_upto_altdef1 using x
      by (intro partial_summation_strong[of "{}"])
         (auto intro!: continuous_intros derivative_eq_intros simp: power2_eq_square
               simp flip: has_field_derivative_iff_has_vector_derivative)
    also have "\<MM> x * (1 / ln x) - \<MM> 2 * (1 / ln 2) - 
                 (\<Sum>n\<in>real -` {2<..x}. ind prime n * (ln n / n) * (1 / ln n)) =
               \<MM> x / ln x - (\<Sum>n\<in>insert 2 (real -` {2<..x}). ind prime n * (ln n / n) * (1 / ln n))" 
      (is "_ = _ - ?S")
      by (subst sum.insert)
         (auto simp: primes_M_def finite_vimage_real_of_nat_greaterThanAtMost eval_prime_sum_upto)
    also have "?S = f x"
      unfolding f_def prime_sum_upto_altdef1 sum_upto_def using x
      by (intro sum.mono_neutral_cong_left) (auto simp: not_less numeral_2_eq_2 le_Suc_eq)
    finally have "((\<lambda>t. -\<MM> t / (t * ln t ^ 2)) has_integral (\<MM> x / ln x - f x)) {2..x}"
      by simp
    from has_integral_neg[OF this]
      have "((\<lambda>t. \<MM> t / (t * ln t ^ 2)) has_integral (f x - \<MM> x / ln x)) {2..x}" by simp
    hence "((\<lambda>t. \<MM> t / (t * ln t ^ 2) - 1 / (t * ln t)) has_integral
             (f x - \<MM> x / ln x - (ln (ln x) - ln (ln 2)))) {2..x}" using x
      by (intro has_integral_diff fundamental_theorem_of_calculus)
         (auto simp flip: has_field_derivative_iff_has_vector_derivative
               intro!: derivative_eq_intros)
    also have "?this \<longleftrightarrow> (r has_integral (f x - \<MM> x / ln x - (ln (ln x) - ln (ln 2)))) {2..x}"
      by (intro has_integral_cong) (auto simp: r_def field_simps power2_eq_square)
    finally have \<dots> .
  } note integral = this

  define R\<^sub>\<MM> where "R\<^sub>\<MM> = (\<lambda>x. \<MM> x - ln x)"
  have \<MM>: "\<MM> x = ln x + R\<^sub>\<MM> x" for x by (simp add: R\<^sub>\<MM>_def)
  define I where "I = (\<lambda>x. integral {x..} r)"
  define C where "C = (1 - ln (ln 2) + I 2)"
  have C_altdef: "C = meissel_mertens"
    by (simp add: I_def r_def C_def meissel_mertens_def)

  show bound: " \<bar>f x - ln (ln x) - meissel_mertens\<bar> \<le> 4 / ln x" if x: "x \<ge> 2" for x
  proof (cases "x = 2")
    case True
    hence "\<bar>f x - ln (ln x) - meissel_mertens\<bar> = \<bar>1 / 2 - ln (ln 2) - meissel_mertens\<bar>"
      by (simp add: f_def eval_prime_sum_upto )
    also have "\<dots> \<le> 2 / ln 2 + 1 / 2"
      using meissel_mertens_bounds by linarith
    also have "\<dots> \<le> 2 / ln 2 + 2 / ln 2" using ln2_le_25_over_36
      by (intro add_mono divide_left_mono) auto
    finally show ?thesis using True by simp
  next
    case False
    hence x: "x > 2" using x by simp
    have "integral {2..x} r + I x = integral ({2..x} \<union> {x..}) r" unfolding I_def r_def using x
      by (intro integral_Un [symmetric] integrable_on_meissel_mertens) (auto simp: max_def r_def)
    also have "{2..x} \<union> {x..} = {2..}" using x by auto
    finally have *: "integral {2..x} r = I 2 - I x" unfolding I_def by simp
    have eq: "f x - ln (ln x) - C = R\<^sub>\<MM> x / ln x - I x"
      using integral[OF x] x by (auto simp: C_def field_simps \<MM> has_integral_iff *)
    also have "\<bar>\<dots>\<bar> \<le> \<bar>R\<^sub>\<MM> x / ln x\<bar> + norm (I x)"
      unfolding real_norm_def by (rule abs_triangle_ineq4)
    also have "\<bar>R\<^sub>\<MM> x / ln x\<bar> \<le> 2 / \<bar>ln x\<bar>"
      unfolding R\<^sub>\<MM>_def abs_divide using mertens_first_theorem[of x] x
      by (intro divide_right_mono) auto
    also have "{x..} - {x<..} = {x}" and "{x<..} \<subseteq> {x..}" by auto
    hence "I x = integral {x<..} r" unfolding I_def
      by (intro integral_subset_negligible [symmetric]) simp_all
    also have "norm \<dots> \<le> 2 / ln x"
      using meissel_mertens_integral_le[of x] x by (simp add: r_def)
    finally show "\<bar>f x - ln (ln x) - meissel_mertens\<bar> \<le> 4 / ln x"
      using x by (simp add: C_altdef)
  qed

  have "(\<lambda>x. f x - ln (ln x) - C) \<in> O(\<lambda>x. 1 / ln x)"
  proof (intro landau_o.bigI[of 4] eventually_mono[OF eventually_ge_at_top[of 2]])
    fix x :: real assume x: "x \<ge> 2"
    with bound[OF x] show "norm (f x - ln (ln x) - C) \<le> 4 * norm (1 / ln x)"
      by (simp add: C_altdef)
  qed (auto intro!: add_pos_nonneg)
  thus "(\<lambda>x. f x - ln (ln x) - meissel_mertens) \<in> O(\<lambda>x. 1 / ln x)"
    by (simp add: C_altdef)
qed

corollary prime_harmonic_asymp_equiv: "prime_sum_upto (\<lambda>p. 1 / p) \<sim>[at_top] (\<lambda>x. ln (ln x))"
proof -
  define f where "f = prime_sum_upto (\<lambda>p. 1 / p)"
  have "(\<lambda>x. f x - ln (ln x) - meissel_mertens + meissel_mertens) \<in> o(\<lambda>x. ln (ln x))"
    unfolding f_def
    by (rule sum_in_smallo[OF landau_o.big_small_trans[OF mertens_second_theorem(2)]]) real_asymp+
  hence "(\<lambda>x. f x - ln (ln x)) \<in> o(\<lambda>x. ln (ln x))"
    by simp
  thus ?thesis unfolding f_def
    by (rule smallo_imp_asymp_equiv)
qed

text \<open>
  As a corollary, we get the divergence of the prime harmonic series.
\<close>
corollary prime_harmonic_diverges: "filterlim (prime_sum_upto (\<lambda>p. 1 / p)) at_top at_top"
  using asymp_equiv_symI[OF prime_harmonic_asymp_equiv]
  by (rule asymp_equiv_at_top_transfer) real_asymp

(*<*)
unbundle no_prime_counting_notation
(*>*)

end