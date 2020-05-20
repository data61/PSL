section \<open>The Laurent series expansion of $\zeta$ at 1\<close>
theory Zeta_Laurent_Expansion
  imports Zeta_Function
begin

text \<open>
  In this section, we shall derive the Laurent series expansion of $\zeta(s)$ at $s = 1$, which
  is of the form 
    \[\zeta(s) = \frac{1}{s-1} + \sum_{n=0}^\infty \frac{(-1)^n\,\gamma_n}{n!} (s-1)^n\]
  where the $\gamma_n$ are the \<^emph>\<open>Stieltjes constants\<close>. Notably, $\gamma_0$ is equal to
  the Euler--Mascheroni constant $\gamma$.
\<close>

subsection \<open>Definition of the Stieltjes constants\<close>

text \<open>
  We define the Stieltjes constants by their infinite series form, since it is fairly
  easy to show the convergence of the series by the comparison test.
\<close>
definition%important stieltjes_gamma :: "nat \<Rightarrow> 'a :: real_algebra_1" where
  "stieltjes_gamma n =
     of_real (\<Sum>k. ln (k+1) ^ n / (k+1) - (ln (k+2) ^ (n+1) - ln (k+1) ^ (n + 1)) / (n + 1))"

lemma stieltjes_gamma_0 [simp]: "stieltjes_gamma 0 = euler_mascheroni"
  using euler_mascheroni_sum_real by (simp add: sums_iff stieltjes_gamma_def field_simps)

lemma stieltjes_gamma_summable:
  "summable (\<lambda>k. ln (k+1) ^ n / (k+1) - (ln (k+2) ^ (n+1) - ln (k+1) ^ (n + 1)) / (n + 1))"
    (is "summable ?f")
proof (rule summable_comparison_test_bigo)
  (* TODO: good real_asymp example *)
  (* TODO: investigate how to make this more automatic *)
  have "eventually (\<lambda>x::real. ln x ^ n - ln x ^ (n+1) * (inverse (ln x) * (1 + real n)) *
           inverse (real n + 1) = 0) at_top"
    using eventually_gt_at_top[of 1] by eventually_elim (auto simp: field_simps)
  thus "?f \<in> O(\<lambda>k. k powr (-3/2))"
    by real_asymp
qed (simp_all add: summable_real_powr_iff)

lemma of_real_stieltjes_gamma [simp]: "of_real (stieltjes_gamma k) = stieltjes_gamma k"
  by (simp add: stieltjes_gamma_def)

lemma sums_stieltjes_gamma:
  "(\<lambda>k. ln (k+1) ^ n / (k+1) - (ln (k+2) ^ (n+1) - ln (k+1) ^ (n + 1)) / (n + 1))
     sums stieltjes_gamma n"
  using stieltjes_gamma_summable[of n] unfolding stieltjes_gamma_def by (simp add: summable_sums)

text \<open>
  We can now derive the alternative definition of the Stieltjes constants as a limit.
  This limit can also be written in the Euler--MacLaurin-style form
  \[\lim\limits_{m\to\infty} \left(\sum\limits_{k=1}^m \frac{\ln^n k}{k} - 
       \int_1^m \frac{\ln^n x}{x}\,\text{d}x\right)\,,\]
  which is perhaps a bit more illuminating.
\<close>
lemma stieltjes_gamma_real_limit_form:
  "(\<lambda>m. (\<Sum>k = 1..m. ln (real k) ^ n / real k) - ln (real m) ^ (n + 1) / real (n + 1))
     \<longlonglongrightarrow> stieltjes_gamma n"
proof -
  have "(\<lambda>m::nat. \<Sum>k<m.  ln (k+1) ^ n / (k+1) - (ln (k+2) ^ (n+1) - ln (k+1) ^ (n + 1)) / (n + 1))
          \<longlonglongrightarrow> stieltjes_gamma n"
    using sums_stieltjes_gamma[of n] by (simp add: add_ac sums_def)
  also have "(\<lambda>m::nat. \<Sum>k<m.  ln (k+1) ^ n / (k+1) - (ln (k+2) ^ (n+1) - ln (k+1) ^ (n + 1)) / (n + 1)) =
        (\<lambda>m::nat. (\<Sum>k=1..m. ln k ^ n / k) - ln (m + 1) ^ (n + 1) / (n + 1))"
    (is "?lhs = ?rhs")
  proof (rule ext, goal_cases)
    fix m :: nat
    have "(\<Sum>k<m. ln (k+1) ^ n / (k+1) - (ln (k+2) ^ (n+1) - ln (k+1) ^ (n + 1)) / (n + 1)) =
            (\<Sum>k<m. ln (k+1) ^ n / (k+1)) -
            (\<Sum>k<m. ln (Suc k+1) ^ (n+1) - ln (k+1) ^ (n + 1)) / (n + 1)"
      by (simp add: sum_subtractf flip: sum_divide_distrib)
    also have "(\<Sum>k<m. ln (k+1) ^ n / (k+1)) = (\<Sum>k=1..m. ln k ^ n / k)"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>k. k-1" Suc]) auto
    also have "(\<Sum>k<m. ln (Suc k+1) ^ (n+1) - ln (k+1) ^ (n + 1)) = ln (m + 1) ^ (n + 1)"
      by (subst sum_lessThan_telescope) simp_all
    finally show "?lhs m = ?rhs m" .
  qed
  finally have *: "(\<lambda>m. (\<Sum>k = 1..m. ln k ^ n / k) - ln (m + 1) ^ (n + 1) / (n + 1))
                     \<longlonglongrightarrow> stieltjes_gamma n" .
  have **: "(\<lambda>m. ln (m + 1) ^ (n + 1) / (n + 1) - ln m ^ (n + 1) / (n + 1)) \<longlonglongrightarrow> 0"
    by real_asymp
  from tendsto_add[OF * **] show ?thesis by (simp add: algebra_simps)
qed

lemma stieltjes_gamma_limit_form:
  "(\<lambda>m. of_real ((\<Sum>k=1..m. ln (real k) ^ n / real k) - ln (real m) ^ (n + 1) / real (n + 1)))
     \<longlonglongrightarrow> (stieltjes_gamma n :: 'a :: real_normed_algebra_1)"
proof -
  have "(\<lambda>m.  of_real ((\<Sum>k=1..m. ln (real k) ^ n / real k) - ln m ^ (n + 1) / real (n + 1)))
          \<longlonglongrightarrow> (of_real (stieltjes_gamma n) :: 'a)"
    using stieltjes_gamma_real_limit_form[of n] by (intro tendsto_of_real) (auto simp: add_ac)
  thus ?thesis by simp
qed

lemma stieltjes_gamma_real_altdef:
  "(stieltjes_gamma n :: real) =
     lim (\<lambda>m. (\<Sum>k = 1..m. ln (real k) ^ n / real k) -
              ln (real m) ^ (n + 1) / real (n + 1))"
  by (rule sym, rule limI, rule stieltjes_gamma_real_limit_form)


subsection \<open>Proof of the Laurent expansion\<close>

text \<open>
  We shall follow the proof by Briggs and Chowla~\cite{briggs55}, which examines the entire
  function $g(s) = (2^{1-s}-1)\zeta(s)$. They determine the value of $g^{(k)}(1)$ in two
  different ways: First by the Dirichlet series of $g$ and then by its power series expansion 
  around 1. We shall do the same here.  
\<close>

context
  fixes g and G1 G2 G2' G :: "complex fps" and A :: "nat \<Rightarrow> complex"
  defines "g \<equiv> perzeta (1 / 2)"
  defines "G1 \<equiv> fps_shift 1 (fps_exp (-ln 2 :: complex) - 1)"
  defines "G2 \<equiv> fps_expansion (\<lambda>s. (s - 1) * pre_zeta 1 s + 1) 1"
  defines "G2' \<equiv> fps_expansion (pre_zeta 1) 1"
  defines "G \<equiv> G1 * G2"
  defines "A \<equiv> fps_nth G2"
begin

text \<open>
  @{term "G1"}, @{term "G2"}, @{term "G2'"}, and @{term "G2"} are the formal power series
  expansions of functions around \<open>s = 1\<close> of the entire functions

    \<^item> $(2^{1-s} - 1) / (s - 1)$, 

    \<^item> $(s - 1) \zeta(s)$,

    \<^item> $\zeta(s) - \frac{1}{s-1}$,

    \<^item> $(2^{1-s}-1) \zeta(s)$,

  respectively.

  Our goal is to determine the coefficients of @{term G2'}, and we shall do so
  by determining the coefficients of @{term G2} (which are the same, but shifted by 1).
  This in turn will be done by determining the coefficients of @{term "G = G1 * G2"}.

  Note that $(2^{1-s} - 1) \zeta(s)$ is written as @{term "perzeta (1/2)"} in Isabelle
  (using the periodic \<open>\<zeta>\<close> function) and the analytic continuation of $\zeta(s) - \frac{1}{s-1}$
  is written as @{term "pre_zeta 1 s"} (@{const pre_zeta} is an artefact from the definition of
  @{const zeta}, which comes in useful here).
\<close>

lemma stieltjes_gamma_aux1: "(\<lambda>n. (-1)^(n+1) * ln(n+1)^k / (n+1)) sums ((-1)^k * (deriv^^k) g 1)"
proof -
  define H where "H = fds_perzeta (1 / 2)"
  have conv: "conv_abscissa H < 1" unfolding H_def
    by (rule le_less_trans[OF conv_abscissa_perzeta']) (use fraction_not_in_ints[of 2 1] in auto)
  have [simp]: "eval_fds H s = g s" if "Re s > 0" for s
    unfolding H_def g_def using fraction_not_in_ints[of 2 1] that
    by (subst perzeta_altdef2) auto
  have ev: "eventually (\<lambda>s. s \<in> {s. Re s > 0}) (nhds 1)"
    by (intro eventually_nhds_in_open open_halfspace_Re_gt) auto
  have [simp]: "(deriv ^^ k) (eval_fds H) 1 = (deriv ^^ k) g 1"
    by (intro higher_deriv_cong_ev eventually_mono[OF ev]) auto

  have "fds_converges ((fds_deriv ^^ k) H) 1"
    by (intro fds_converges le_less_trans[OF conv_abscissa_higher_deriv_le])
       (use conv in \<open>simp add: one_ereal_def\<close>)
  hence "(\<lambda>n. fds_nth ((fds_deriv ^^ k) H) (n+1) / real (n+1)) sums eval_fds ((fds_deriv ^^ k) H) 1"
    by (simp add: fds_converges_altdef)
  also have "eval_fds ((fds_deriv ^^ k) H) 1 = (deriv ^^ k) (eval_fds H) 1"
    using conv by (intro eval_fds_higher_deriv) (auto simp: one_ereal_def)
  also have "(\<lambda>n. fds_nth ((fds_deriv ^^ k) H) (n+1) / real (n+1)) =
               (\<lambda>n. (-1)^k * (-1)^(n+1) * ln (real (n+1)) ^ k / (n+1))"
    by (auto simp: fds_nth_higher_deriv algebra_simps H_def fds_perzeta_one_half Ln_Reals_eq)
  finally have "(\<lambda>n. (- 1) ^ k * complex_of_real ((-1)^(n+1) * ln (real (n+1)) ^ k / real (n+1))) sums
                   ((deriv ^^ k) g 1)" by (simp add: algebra_simps)

  hence "(\<lambda>n. (-1)^k * ((-1)^k * complex_of_real ((-1)^(n+1) * ln (real (n+1)) ^ k / real (n+1)))) sums
                     ((-1)^k * (deriv ^^ k) g 1)" by (intro sums_mult)
  also have "(\<lambda>n. (-1)^k * ((-1)^k * complex_of_real ((-1)^(n+1) * ln (real (n+1)) ^ k / real (n+1)))) =
             (\<lambda>n. complex_of_real ((-1)^(n+1) * ln (real (n+1)) ^ k / real (n+1)))"
    by (intro ext) auto
  finally show ?thesis .
qed

lemma stieltjes_gamma_aux2: "(deriv^^k) g 1 = fact k * fps_nth G k" 
  and stieltjes_gamma_aux3: "G2 = fps_X * G2' + 1"
proof -
  have [simp]: "fps_conv_radius G1 = \<infinity>"
    using fps_conv_radius_diff[of "fps_exp (-Ln 2)" 1] by (simp add: G1_def)
  have "fps_conv_radius G2 \<ge> \<infinity>"
    unfolding G2_def by (intro conv_radius_fps_expansion holomorphic_intros) auto
  hence [simp]: "fps_conv_radius G2 = \<infinity>"
    by simp
  have "fps_conv_radius G2' \<ge> \<infinity>"
    unfolding G2'_def by (intro conv_radius_fps_expansion holomorphic_intros) auto
  hence [simp]: "fps_conv_radius G2' = \<infinity>"
    by simp
  have [simp]: "fps_conv_radius G = \<infinity>"
    using fps_conv_radius_mult[of G1 G2] by (simp add: G_def)

  have eval_G1: "eval_fps G1 (s - 1) =
                   (if s = 1 then -ln 2 else (2 powr (1 - s) - 1) / (s - 1))" for s
      unfolding G1_def using fps_conv_radius_diff[of "fps_exp (-Ln 2)" 1]
      by (subst eval_fps_shift)
         (auto intro!: subdegree_geI simp: eval_fps_diff powr_def exp_diff exp_minus algebra_simps)
  have eval_G2: "eval_fps G2 (s - 1) = (s - 1) * pre_zeta 1 s + 1" for s
    unfolding G2_def by (subst eval_fps_expansion[where r = \<infinity>]) (auto intro!: holomorphic_intros)
  have eval_G: "eval_fps G (s - 1) = g s" for s
    unfolding G_def by (simp add: eval_fps_mult eval_G1 eval_G2 g_def perzeta_one_half_left')
  have eval_G': "eval_fps G s = g (1 + s)" for s
    using eval_G[of "s + 1"] by (simp add: add_ac)
  have eval_G2': "eval_fps G2' (s - 1) = pre_zeta 1 s" for s
    unfolding G2'_def by (intro eval_fps_expansion[where r = \<infinity>]) (auto intro!: holomorphic_intros)

  show "G2 = fps_X * G2' + 1"
  proof (intro eval_fps_eqD always_eventually allI)
    have *: "fps_conv_radius (fps_X * G2') = \<infinity>"
      using fps_conv_radius_mult[of fps_X G2'] by simp
    from * show "fps_conv_radius (fps_X * G2' + 1) > 0"
      using fps_conv_radius_add[of "fps_X * G2'" 1] by auto
    show "eval_fps G2 s = eval_fps (fps_X * G2' + 1) s" for s
      using * eval_G2[of "1 + s"] eval_G2'[of "1 + s"]
      by (simp add: eval_fps_add eval_fps_mult)
  qed auto

  have "G = fps_expansion g 1"
  proof (rule eval_fps_eqD)
    have "fps_conv_radius (fps_expansion g 1) \<ge> \<infinity>"
      using fraction_not_in_ints[of 2 1]
      by (intro conv_radius_fps_expansion) (auto intro!: holomorphic_intros simp: g_def)
    thus "fps_conv_radius (fps_expansion g 1) > 0" by simp
  next
    have "eval_fps (fps_expansion g 1) z = g (1 + z)" for z
      using fraction_not_in_ints[of 2 1]
      by (subst eval_fps_expansion'[where r = \<infinity>]) (auto simp: g_def intro!: holomorphic_intros)
    thus "eventually (\<lambda>z. eval_fps G z = eval_fps (fps_expansion g 1) z) (nhds 0)"
      by (simp add: eval_G')
  qed auto
  thus "(deriv ^^ k) g 1 = fact k * fps_nth G k"
    by (simp add: fps_eq_iff fps_expansion_def)
qed

lemma stieltjes_gamma_aux4: "fps_nth G k = (\<Sum>i=1..k+1. (-ln 2)^i * A (k-(i-1)) / fact i)"
proof -
  have "fps_nth G k = (\<Sum>i\<le>k. fps_nth G1 i * A (k - i))"
    unfolding G_def fps_mult_nth A_def by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>i\<le>k. (-ln 2)^(i+1) * A (k - i) / fact (i+1))"
    by (simp add: G1_def algebra_simps)
  also have "\<dots> = (\<Sum>i=1..k+1. (-ln 2)^i * A (k-(i-1)) / fact i)"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>i. i-1" Suc]) (auto simp: Suc_diff_Suc)
  finally show ?thesis .
qed

lemma stieltjes_gamma_aux5: "(\<Sum>t<k. (k choose t) * Ln 2 ^ (k - t) * stieltjes_gamma t) -
             ln 2 ^ (k+1) / of_nat (k+1) = (-1) ^ k * (deriv ^^ k) g 1"
proof -
  define h where "h = (\<lambda>k x. (\<Sum>n=1..x. ln(real n)^k / real n) -
                         ln (real x)^(k+1) / real(k+1) - stieltjes_gamma k)"
  have h_eq: "(\<Sum>n=1..x. ln n ^ k / n) = ln x^(k+1) / real (k+1) + stieltjes_gamma k + h k x"
    for k x :: nat by (simp add: h_def)
  define h' where "h' = (\<lambda>x. \<Sum>t=0..k. (k choose t) * ln 2 ^ (k - t) * h t x)"
  define S1 where "S1 = (\<lambda>x. (\<Sum>t=0..k. (k choose t) * ln 2 ^ (k - t) * ln x ^ (t + 1) / (t + 1)))"
  define S2 where "S2 = (\<lambda>x. (\<Sum>t=0..k. (k choose t) * ln 2 ^ (k - t) * ln x ^ (t + 1) / (k + 1)))"

  have [THEN filterlim_compose, tendsto_intros]: "h t \<longlonglongrightarrow> 0" for t
    using tendsto_diff[OF stieltjes_gamma_real_limit_form[of t] tendsto_const[of "stieltjes_gamma t"]]
    by (simp add: h_def)

  have eq: "(\<Sum>n=1..2 * x. (-1)^(n+1) * ln n ^ k / n) =
              ln 2 ^ (k+1) / real (k+1) -
              (\<Sum>t<k. (k choose t) * ln 2 ^ (k-t) * stieltjes_gamma t) + h k (2*x) - h' x"
    (is "?lhs x = ?rhs x") if "x > 0" for x :: nat
  proof -
    have "2 * (\<Sum>n=1..x. ln (2*n)^k/(2*n)) =
           (\<Sum>n=1..x. \<Sum>t=0..k. 1/n * (k choose t) * ln 2 ^ (k-t) * ln n ^ t)"
      unfolding sum_distrib_left
    proof (rule sum.cong)
      fix n :: nat assume n: "n \<in> {1..x}"
      have "2 * (ln (2*n)^k / (2*n)) = 1/n * (ln n + ln 2) ^ k"
        using n by (simp add: ln_mult add_ac)
      also have "(ln n + ln 2) ^ k = (\<Sum>t=0..k. (k choose t) * ln 2 ^ (k-t) * ln n ^ t)"
        by (subst binomial_ring, rule sum.cong) auto
      also have "1/n * \<dots> = (\<Sum>t=0..k. 1/n * (k choose t) * ln 2 ^ (k-t) * ln n ^ t)"
        by (subst sum_distrib_left) (simp add: mult_ac)
      finally show "2 * (ln (2*n)^k / (2*n)) = \<dots>" .
    qed auto
    also have "\<dots> = (\<Sum>t=0..k. \<Sum>n=1..x. 1/n * (k choose t) * ln 2 ^ (k-t) * ln n ^ t)"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>t=0..k. (k choose t) * ln 2 ^ (k - t) *
                      (ln x ^ (t+1) / (t+1) + stieltjes_gamma t + h t x))"
    proof (rule sum.cong)
      fix t :: nat assume t: "t \<in> {0..k}"
      have "(\<Sum>n=1..x. 1/n * (k choose t) * ln 2 ^ (k-t) * ln n ^ t) =
            (k choose t) * ln 2 ^ (k - t) * (\<Sum>n=1..x. ln n ^ t / n)"
        by (subst sum_distrib_left) (simp add: mult_ac)
      also have "(\<Sum>n=1..x. ln n ^ t / n) = ln x ^ (t+1) / (t+1) + stieltjes_gamma t + h t x"
        using h_eq[of t] by simp
      finally show "(\<Sum>n=1..x. 1/n * (k choose t) * ln 2 ^ (k-t) * ln n ^ t) =
                      (k choose t) * ln 2 ^ (k - t) * \<dots>" .
    qed simp_all
    also have "\<dots> = (\<Sum>t=0..k. (k choose t) / (t + 1) * ln 2 ^ (k - t) * ln x ^ (t + 1)) +
                    (\<Sum>t=0..k. (k choose t) * ln 2 ^ (k - t) * stieltjes_gamma t) + h' x"
      by (simp add: ring_distribs sum.distrib h'_def)
    also have "(\<Sum>t=0..k. (k choose t) / (t + 1) * ln 2 ^ (k - t) * ln x ^ (t + 1)) =
               (\<Sum>t=0..k. (Suc k choose Suc t) / (k + 1) * ln 2 ^ (k - t) * ln x ^ (t + 1))"
    proof (intro sum.cong refl, goal_cases)
      case (1 t)
      have "of_nat (k choose t) * (of_nat (k + 1) :: real) = of_nat ((k choose t) * (k + 1))"
        by (simp only: of_nat_mult)
      also have "(k choose t) * (k + 1) = (Suc k choose Suc t) * (t + 1)"
        using Suc_times_binomial_eq[of k t] by (simp add: algebra_simps)
      also have "of_nat \<dots> = of_nat (Suc k choose Suc t) * (of_nat (t + 1) :: real)"
        by (simp only: of_nat_mult)
      finally have *: "of_nat (k choose t) / of_nat (t + 1) =
                         (of_nat (Suc k choose Suc t) / (k + 1) :: real)"
        by (simp add: divide_simps flip: of_nat_Suc del: binomial_Suc_Suc)
      show ?case by (simp only: *)
    qed
    also have "\<dots> = (\<Sum>t=1..Suc k. (Suc k choose t) / (k + 1) * ln 2 ^ (Suc k - t) * ln x ^ t)"
      by (intro sum.reindex_bij_witness[of _ "\<lambda>t. t-1" Suc]) auto
    also have "{1..Suc k} = {..Suc k} - {0}" by auto
    also have "(\<Sum>t\<in>\<dots>. (Suc k choose t) / (k + 1) * ln 2 ^ (Suc k - t) * ln x ^ t) =
                 (\<Sum>t\<le>Suc k. (Suc k choose t) / (k + 1) * ln 2 ^ (Suc k - t) * ln x ^ t) -
                   ln 2 ^ Suc k / (k + 1)"
      by (subst sum_diff1) auto
    also have "(\<Sum>t\<le>Suc k. (Suc k choose t) / (k + 1) * ln 2 ^ (Suc k - t) * ln x ^ t) =
               (ln x + ln 2) ^ Suc k / (k + 1)"
      unfolding binomial_ring by (subst sum_divide_distrib) (auto simp: algebra_simps)
    also have "ln x + ln 2 = ln (2 * x)"
      using \<open>x > 0\<close> by (simp add: ln_mult)
    finally have eq1: "2 * (\<Sum>n=1..x. ln (real (2*n))^k / real (2*n)) =
                         ln (real (2*x))^(k+1) / real (k+1) - ln 2^(k+1) / real (k+1) +
                         (\<Sum>t=0..k. (k choose t) * ln 2^(k - t) * stieltjes_gamma t) + h' x"
      by (simp add: algebra_simps)

    have eq2: "(\<Sum>n=1..2*x. ln n ^ k / n) = ln (real (2*x))^(k+1) / real (k+1) + stieltjes_gamma k + h k (2*x)"
      by (simp only: h_eq)

    have "(\<Sum>n=1..2*x. (-1)^(n+1) * ln n ^ k / n) =
          (\<Sum>n=1..2*x. ln n ^ k / n - 2 * (if even n then ln n ^ k / n else 0))"
      by (intro sum.cong) auto
    also have "\<dots> = (\<Sum>n=1..2*x. ln n ^ k / n) -
                    2 * (\<Sum>n=1..2*x. if even n then ln n ^ k / n else 0)"
      by (simp only: sum_subtractf sum_distrib_left)
    also have "(\<Sum>n=1..2*x. if even n then ln n ^ k / n else 0) =
               (\<Sum>n | n \<in> {1..2*x} \<and> even n. ln n ^ k / n)"
      by (intro sum.mono_neutral_cong_right) auto
    also have "\<dots> = (\<Sum>n=1..x. ln (real (2*n)) ^ k / real (2*n))"
      by (intro sum.reindex_bij_witness[of _ "\<lambda>n. 2*n" "\<lambda>n. n div 2"]) auto
    also have "(\<Sum>n=1..2*x. ln n ^ k / n) - 2 * \<dots> =
                 ln 2^(k+1) / real (k+1) -
                ((\<Sum>t=0..k. (k choose t) * ln 2^(k - t) * stieltjes_gamma t) - stieltjes_gamma k) +
                h k (2*x) - h' x"
      using arg_cong2[OF eq1 eq2, of "(-)"] by simp
    also have "{0..k} = insert k {..<k}" by auto
    also have "(\<Sum>t\<in>\<dots>. (k choose t) * ln 2^(k - t) * stieltjes_gamma t) - stieltjes_gamma k =
                 (\<Sum>t<k. (k choose t) * ln 2^(k - t) * stieltjes_gamma t)"
      by (subst sum.insert) auto
    finally show ?thesis .
  qed

  have "?rhs \<longlonglongrightarrow> ln 2 ^ (k+1) / real (k+1) -
                            (\<Sum>t<k. (k choose t) * ln 2 ^ (k-t) * stieltjes_gamma t)"
    unfolding h'_def by (rule tendsto_eq_intros refl mult_nat_left_at_top filterlim_ident | simp)+
  moreover have "eventually (\<lambda>x. ?rhs x = ?lhs x) sequentially"
    using eventually_gt_at_top[of 0] by eventually_elim (simp only: eq)
  ultimately have *: "?lhs \<longlonglongrightarrow> ln 2 ^ (k+1) / real (k+1) -
                                   (\<Sum>t<k. (k choose t) * ln 2 ^ (k-t) * stieltjes_gamma t)"
    by (rule Lim_transform_eventually)
  also have "(\<lambda>x. \<Sum>n=1..2*x. (-1)^(n+1) * ln (real n)^k / real n) = 
             (\<lambda>x. \<Sum>n<2*x. -((-1)^(n+1) * ln (real (n+1))^k / real (n+1)))"
    by (intro ext sum.reindex_bij_witness[of _ Suc "\<lambda>n. n - 1"]) (auto simp: power_diff)
  also have "\<dots> = (\<lambda>x. -(\<Sum>n<2*x. ((-1)^(n+1) * ln (real (n+1))^k / real (n+1))))"
    by (subst sum_negf) auto
  finally have *: "\<dots> \<longlonglongrightarrow> (ln 2 ^ (k+1) / real (k+1) -
                              (\<Sum>t<k. (k choose t) * ln 2 ^ (k - t) * stieltjes_gamma t))" .
  have lim1: "(\<lambda>x. (\<Sum>n<2*x. complex_of_real ((-1)^(n+1) * ln (real (n+1))^k / real (n+1))))
              \<longlonglongrightarrow> -(ln 2 ^ (k+1) / of_nat (k+1) -
                      (\<Sum>t<k. (k choose t) * ln 2 ^ (k - t) * stieltjes_gamma t))"
    (is "?lhs' \<longlonglongrightarrow> _")
    using tendsto_of_real[OF tendsto_minus[OF *], where ?'a = complex]
    by (simp add: Ln_Reals_eq)

  moreover have "?lhs' \<longlonglongrightarrow> ((- 1) ^ k * (deriv ^^ k) g 1)"
  proof -
    have **: "filterlim (\<lambda>n::nat. 2 * n) sequentially sequentially" by real_asymp
    have "(\<lambda>x. (\<Sum>n<2*x. complex_of_real ((-1)^(n+1) * ln (real (n+1))^k / real (n+1))))
              \<longlonglongrightarrow> ((- 1) ^ k * (deriv ^^ k) g 1)"
      by (rule filterlim_compose[OF _ **]) (use stieltjes_gamma_aux1 in \<open>simp add: sums_def\<close>)
    thus ?thesis .
  qed

  ultimately have "-(ln 2 ^ (k+1) / of_nat (k+1) -
                      (\<Sum>t<k. (k choose t) * ln 2 ^ (k - t) * stieltjes_gamma t)) =
                   (-1) ^ k * (deriv ^^ k) g 1"
    by (rule LIMSEQ_unique)
  thus ?thesis by (simp add: Ln_Reals_eq)
qed

lemma stieltjes_gamma_aux6: "(\<Sum>t<k. (k choose t) * Ln 2 ^ (k - t) * stieltjes_gamma t) -
                  Ln 2 ^ (k + 1) / of_nat (k + 1) =
                (-1)^k * fact k * (\<Sum>i=1..k+1. (-Ln 2) ^ i * A (k-(i-1)) / fact i)"
proof -
  have "(\<Sum>t<k. (k choose t) * Ln 2 ^ (k - t) * stieltjes_gamma t) -
          Ln 2 ^ (k + 1) / of_nat (k + 1) = (- 1) ^ k * (deriv ^^ k) g 1"
    using stieltjes_gamma_aux5[of k] .
  also have "(deriv ^^ k) g 1 = fact k * fps_nth G k"
    by (rule stieltjes_gamma_aux2)
  also have "fps_nth G k = (\<Sum>i=1..k + 1. (-Ln 2) ^ i * A (k - (i - 1)) / fact i)"
    by (rule stieltjes_gamma_aux4)
  finally show ?thesis by (simp add: mult_ac)
qed

theorem higher_deriv_pre_zeta_1_1: "(deriv ^^ k) (pre_zeta 1) 1 = (-1) ^ k * stieltjes_gamma k"
proof -
  have eq: "A k = (if k = 0 then 1 else (-1)^(k+1) * stieltjes_gamma (k - 1) / fact (k - 1))" for k
  proof (induction k rule: less_induct)
    case (less k)
    show ?case
    proof (cases "k = 0")
      case True
      with stieltjes_gamma_aux6[of 0] show ?thesis by simp
    next
      case False
      have "k * Ln 2 * stieltjes_gamma (k - 1) +
             (\<Sum>t<k-1. (k choose t) * Ln 2 ^ (k - t) * stieltjes_gamma t) =
             (\<Sum>t\<in>insert (k-1) {..<k-1}. (k choose t) * Ln 2 ^ (k - t) * stieltjes_gamma t)"
        using False by (subst sum.insert) auto
      also have "insert (k-1) {..<k-1} = {..<k}" using False by auto
      also have "(\<Sum>t<k. of_nat (k choose t) * Ln 2 ^ (k - t) * stieltjes_gamma t) =
              Ln 2 ^ (k + 1) / of_nat (k + 1) +
              (- 1) ^ k * fact k * (\<Sum>i = 1..k + 1. (- Ln 2) ^ i * A (k - (i - 1)) / fact i)"
        using stieltjes_gamma_aux6[of k] by (simp add: algebra_simps)
      also have "{1..k+1} = {1,k+1} \<union> {2..k}" by auto
      also have "(- 1) ^ k * fact k * (\<Sum>i\<in>\<dots>. (- Ln 2) ^ i * A (k - (i - 1)) / fact i) =
                 (\<Sum>i=2..k. (-1)^k * fact k * (- Ln 2) ^ i * A (k - (i - 1)) / fact i)
                   -Ln 2 * A k * (- 1) ^ k * fact k +
                   (-Ln 2)^(k+1) * A 0 / fact (k+1) * (- 1) ^ k * fact k"
        using False by (subst sum.union_disjoint)
                       (auto simp: algebra_simps sum_distrib_left sum_distrib_right)
      also have "(\<Sum>i=2..k. (-1)^k * fact k * (-Ln 2) ^ i * A (k-(i-1)) / fact i) =
                 (\<Sum>i<k-1. (k choose i) * Ln 2 ^ (k-i) * stieltjes_gamma i)"
        using False
        by (intro sum.reindex_bij_witness[of _ "\<lambda>i. k - i" "\<lambda>i. k - i"])
           (auto simp: binomial_fact Suc_diff_le less field_simps power_neg_one_If)
      finally have "k * Ln 2 * stieltjes_gamma (k - 1) =
                       (-1)^(k+1) * fact k * Ln 2 * A k"
        using False by (simp add: less power_minus')
      also have "\<dots> * (-1)^(k+1) / fact k / Ln 2 = A k"
        by simp
      also have "k * Ln 2 * stieltjes_gamma (k - 1) * (-1)^(k+1) / fact k / Ln 2 =
                   (-1)^(k+1) * stieltjes_gamma (k - 1) / fact (k - 1)"
        using False by (simp add: field_simps fact_reduce)
      finally have "A k = (- 1) ^ (k + 1) * stieltjes_gamma (k - 1) / fact (k - 1)" ..
      thus ?thesis using False by simp
    qed
  qed
  
  have "fps_nth G2' k = fps_nth G2 (Suc k)"
    by (simp add: stieltjes_gamma_aux3)
  also have "\<dots> = A (Suc k)"
    by (simp add: A_def)
  also have "\<dots> = (-1) ^ k * stieltjes_gamma k / fact k"
    by (simp add: eq)
  finally show "(deriv ^^ k) (pre_zeta 1) 1 = (-1) ^ k * stieltjes_gamma k"
    by (simp add: G2'_def fps_eq_iff fps_expansion_def)
qed

corollary pre_zeta_1_1 [simp]: "pre_zeta 1 1 = euler_mascheroni"
  using higher_deriv_pre_zeta_1_1[of 0] by simp

corollary zeta_minus_pole_limit: "(\<lambda>s. zeta s - 1 / (s - 1)) \<midarrow>1\<rightarrow> euler_mascheroni"
proof (rule Lim_transform_eventually)
  show "eventually (\<lambda>s. pre_zeta 1 s = zeta s - 1 / (s - 1)) (at 1)"
    by (auto simp: zeta_minus_pole_eq [symmetric] eventually_at_filter)
  have "isCont (pre_zeta 1) 1"
    by (intro continuous_intros) auto
  thus "pre_zeta 1 \<midarrow>1\<rightarrow> euler_mascheroni"
    by (simp add: isCont_def)
qed

corollary fps_expansion_pre_zeta_1_1:
  "fps_expansion (pre_zeta 1) 1 = Abs_fps (\<lambda>n. (-1)^n * stieltjes_gamma n / fact n)"
  by (simp add: fps_expansion_def higher_deriv_pre_zeta_1_1)

end

end