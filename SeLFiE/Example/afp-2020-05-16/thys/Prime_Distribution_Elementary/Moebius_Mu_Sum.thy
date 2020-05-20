(*
  File:    Moebius_Mu_Sum.thy
  Author:  Manuel Eberl, TU München

  Properties of the summatory Möbius \<mu> function, including its relationship to
  the Prime Number Theorem.
*)
section \<open>The summatory Möbius \<open>\<mu>\<close> function\<close>
theory Moebius_Mu_Sum
imports
  More_Dirichlet_Misc
  Dirichlet_Series.Partial_Summation
  Prime_Number_Theorem.Prime_Counting_Functions
  Dirichlet_Series.Arithmetic_Summatory_Asymptotics
  Shapiro_Tauberian
  Partial_Zeta_Bounds
  Prime_Number_Theorem.Prime_Number_Theorem_Library
  Prime_Distribution_Elementary_Library
begin

text \<open>
  In this section, we shall examine the summatory Möbius \<open>\<mu>\<close> function
  $M(x) := \sum_{n\leq x} \mu(n)$. The main result is that $M(x) \in o(x)$ is equivalent
  to the Prime Number Theorem.
\<close>

context
  includes prime_counting_notation
  fixes M H :: "real \<Rightarrow> real"
  defines "M \<equiv> sum_upto moebius_mu"
  defines "H \<equiv> sum_upto (\<lambda>n. moebius_mu n * ln n)"
begin

lemma sum_upto_moebius_mu_integral: "x > 1 \<Longrightarrow> ((\<lambda>t. M t / t) has_integral M x * ln x - H x) {1..x}"
  and sum_upto_moebius_mu_integrable: "a \<ge> 1 \<Longrightarrow> (\<lambda>t. M t / t) integrable_on {a..b}"
proof -
  {
    fix a b :: real
    assume ab: "a \<ge> 1" "a < b"
    have "((\<lambda>t. M t * (1 / t)) has_integral M b * ln b - M a * ln a -
            (\<Sum>n\<in>real -` {a<..b}. moebius_mu n * ln (real n))) {a..b}"
      unfolding M_def using ab
      by (intro partial_summation_strong [where X = "{}"])
         (auto intro!: derivative_eq_intros continuous_intros
               simp flip: has_field_derivative_iff_has_vector_derivative)
  } note * = this
  {
    fix x :: real assume x: "x > 1"
    have "(\<Sum>n\<in>real -` {1<..x}. moebius_mu n * ln (real n)) = H x"
      unfolding H_def sum_upto_def by (intro sum.mono_neutral_cong_left) (use x in auto)
    thus "((\<lambda>t. M t / t) has_integral M x * ln x - H x) {1..x}" using *[of 1 x] x by simp
  }
  {
    fix a b :: real assume ab: "a \<ge> 1"
    show "(\<lambda>t. M t / t) integrable_on {a..b}"
      using *[of a b] ab
      by (cases a b rule: linorder_cases) (auto intro: integrable_negligible)
  }
qed

lemma sum_moebius_mu_bound:
  assumes "x \<ge> 0"
  shows   "\<bar>M x\<bar> \<le> x"
proof -
  have "\<bar>M x\<bar> \<le> sum_upto (\<lambda>n. \<bar>moebius_mu n\<bar>) x"
    unfolding M_def sum_upto_def by (rule sum_abs)
  also have "\<dots> \<le> sum_upto (\<lambda>n. 1) x"
    unfolding sum_upto_def by (intro sum_mono) (auto simp: moebius_mu_def)
  also have "\<dots> \<le> x" using assms
    by (simp add: sum_upto_altdef)
  finally show ?thesis .
qed

lemma sum_moebius_mu_aux1: "(\<lambda>x. M x / x - H x / (x * ln x)) \<in> O(\<lambda>x. 1 / ln x)"
proof -
  define R where "R = (\<lambda>x. integral {1..x} (\<lambda>t. M t / t))"
  have "eventually (\<lambda>x. M x / x - H x / (x * ln x) = R x / (x * ln x)) at_top"
    using eventually_gt_at_top[of 1]
  proof eventually_elim
    case (elim x)
    thus ?case
      using sum_upto_moebius_mu_integral[of x] by (simp add: R_def has_integral_iff field_simps)
  qed
  hence "(\<lambda>x. M x / x - H x / (x * ln x)) \<in> \<Theta>(\<lambda>x. R x / (x * ln x))"
    by (intro bigthetaI_cong)
  also have "(\<lambda>x. R x / (x * ln x)) \<in> O(\<lambda>x. x / (x * ln x))"
  proof (intro landau_o.big.divide_right)
    have "M \<in> O(\<lambda>x. x)"
      using sum_moebius_mu_bound
      by (intro bigoI[where c = 1] eventually_mono[OF eventually_ge_at_top[of 0]]) auto
    hence "(\<lambda>t. M t / t) \<in> O(\<lambda>t. 1)"
      by (simp add: landau_divide_simps)
    thus "R \<in> O(\<lambda>x. x)"
      unfolding R_def
      by (intro integral_bigo[where g' = "\<lambda>_. 1"])
         (auto simp: filterlim_ident has_integral_iff intro!: sum_upto_moebius_mu_integrable)
  qed (intro eventually_mono[OF eventually_gt_at_top[of 1]], auto)
  also have "(\<lambda>x::real. x / (x * ln x)) \<in> \<Theta>(\<lambda>x. 1 / ln x)"
    by real_asymp
  finally show ?thesis .
qed

(* 4.13 *)
lemma sum_moebius_mu_aux2: "((\<lambda>x. M x / x - H x / (x * ln x)) \<longlongrightarrow> 0) at_top"
proof -
  have "(\<lambda>x. M x / x - H x / (x * ln x)) \<in> O(\<lambda>x. 1 / ln x)"
    by (rule sum_moebius_mu_aux1)
  also have "(\<lambda>x. 1 / ln x) \<in> o(\<lambda>_. 1 :: real)"
    by real_asymp
  finally show ?thesis by (auto dest!: smalloD_tendsto)
qed

lemma sum_moebius_mu_ln_eq: "H = (\<lambda>x. - dirichlet_prod' moebius_mu \<psi> x)"
proof
  fix x :: real
  have "fds mangoldt = (fds_deriv (fds moebius_mu) * fds_zeta :: real fds)"
    using fds_mangoldt' by (simp add: mult_ac)
  hence eq: "fds_deriv (fds moebius_mu) = fds moebius_mu * (fds mangoldt :: real fds)"
    by (subst (asm) fds_moebius_inversion [symmetric])
  have "-H x = sum_upto (\<lambda>n. -ln n * moebius_mu n) x"
    by (simp add: H_def sum_upto_def sum_negf mult_ac)
  also have "\<dots> = sum_upto (\<lambda>n. dirichlet_prod moebius_mu mangoldt n) x"
    using eq by (intro sum_upto_cong) (auto simp: fds_eq_iff fds_nth_deriv fds_nth_mult)
  also have "\<dots> = dirichlet_prod' moebius_mu \<psi> x"
    by (subst sum_upto_dirichlet_prod) (simp add: primes_psi_def dirichlet_prod'_def)
  finally show "H x = -dirichlet_prod' moebius_mu \<psi> x"
    by simp
qed

(* 4.14 *)
theorem PNT_implies_sum_moebius_mu_sublinear:
  assumes "\<psi> \<sim>[at_top] (\<lambda>x. x)"
  shows   "M \<in> o(\<lambda>x. x)"
proof -
  have "((\<lambda>x. H x / (x * ln x)) \<longlongrightarrow> 0) at_top"
  proof (rule tendstoI)
    fix \<epsilon>' :: real assume \<epsilon>': "\<epsilon>' > 0"
    define \<epsilon> where "\<epsilon> = \<epsilon>' / 2"
    from \<epsilon>' have \<epsilon>: "\<epsilon> > 0" by (simp add: \<epsilon>_def)
    from assms have "((\<lambda>x. \<psi> x / x) \<longlongrightarrow> 1) at_top"
      by (elim asymp_equivD_strong) (auto intro!: eventually_mono[OF eventually_gt_at_top[of 0]])
    from tendstoD[OF this \<epsilon>] have "eventually (\<lambda>x. \<bar>\<psi> x / x - 1\<bar> < \<epsilon>) at_top"
      by (simp add: dist_norm)
    hence "eventually (\<lambda>x. \<bar>\<psi> x - x\<bar> < \<epsilon> * x) at_top"
      using eventually_gt_at_top[of 0] by eventually_elim (auto simp: abs_if field_simps)
    then obtain A' where A': "\<And>x. x \<ge> A' \<Longrightarrow> \<bar>\<psi> x - x\<bar> < \<epsilon> * x"
      by (auto simp: eventually_at_top_linorder)
    define A where "A = max 2 A'"
    from A' have A: "A \<ge> 2" "\<And>x. x \<ge> A \<Longrightarrow> \<bar>\<psi> x - x\<bar> < \<epsilon> * x"
      by (auto simp: A_def)
  
    have H_bound: "\<bar>H x\<bar> / (x * ln x) \<le> (1 + \<epsilon> + \<psi> A) / ln x + \<epsilon>" if "x \<ge> A" for x
    proof -
      from \<open>x \<ge> A\<close> have "x \<ge> 2" using A(1) by linarith
      note x = \<open>x \<ge> A\<close> \<open>x \<ge> 2\<close>
  
      define y where "y = nat \<lfloor>floor (x / A)\<rfloor>"
      have "real y = real_of_int \<lfloor>x / A\<rfloor>" using A x by (simp add: y_def)
      also have "real_of_int \<lfloor>x / A\<rfloor> \<le> x / A" by linarith
      also have "\<dots> \<le> x" using x A(1) by (simp add: field_simps)
      finally have "y \<le> x" .
      have "y \<ge> 1" using x A(1) by (auto simp: y_def le_nat_iff le_floor_iff)
      note y = \<open>y \<ge> 1\<close> \<open>y \<le> x\<close>
  
      define S1 where [simp]: "S1 = sum_upto (\<lambda>m. moebius_mu m * \<psi> (x / m)) y"
      define S2 where [simp]: "S2 = (\<Sum>m | m > y \<and> real m \<le> x. moebius_mu m * \<psi> (x / m))"
  
      have fin: "finite {m. y < m \<and> real m \<le> x}"
        by (rule finite_subset[of _ "{..nat \<lfloor>x\<rfloor>}"]) (auto simp: le_nat_iff le_floor_iff)
      have "H x = -dirichlet_prod' moebius_mu \<psi> x"
        by (simp add: sum_moebius_mu_ln_eq)
      also have "dirichlet_prod' moebius_mu \<psi> x =
                   (\<Sum>m | m > 0 \<and> real m \<le> x. moebius_mu m * \<psi> (x / m))"
        unfolding dirichlet_prod'_def sum_upto_def ..
      also have "{m. m > 0 \<and> real m \<le> x} = {0<..y} \<union> {m. y < m \<and> real m \<le> x}"
        using x y A(1) by auto
      also have "(\<Sum>m\<in>\<dots>. moebius_mu m * \<psi> (x / m)) = S1 + S2"
        unfolding dirichlet_prod'_def sum_upto_def S1_def S2_def using fin
        by (subst sum.union_disjoint) (auto intro: sum.cong)
      finally have abs_H_eq: "\<bar>H x\<bar> = \<bar>S1 + S2\<bar>" by simp
  
      define S1_1 where [simp]: "S1_1 = sum_upto (\<lambda>m. moebius_mu m / m) y"
      define S1_2 where [simp]: "S1_2 = sum_upto (\<lambda>m. moebius_mu m * (\<psi> (x / m) - x / m)) y"
  
      have "\<bar>S1\<bar> = \<bar>x * S1_1 + S1_2\<bar>"
        by (simp add: sum_upto_def sum_distrib_left sum_distrib_right
                      mult_ac sum_subtractf ring_distribs)
      also have "\<dots> \<le> x * \<bar>S1_1\<bar> + \<bar>S1_2\<bar>"
        by (rule order.trans[OF abs_triangle_ineq]) (use x in \<open>simp add: abs_mult\<close>)
      also have "\<dots> \<le> x * 1 + \<epsilon> * x * (ln x + 1)"
      proof (intro add_mono mult_left_mono)
        show "\<bar>S1_1\<bar> \<le> 1"
          using abs_sum_upto_moebius_mu_over_n_le[of y] by simp
      next
        have "\<bar>S1_2\<bar> \<le> sum_upto (\<lambda>m. \<bar>moebius_mu m * (\<psi> (x / m) - x / m)\<bar>) y"
          unfolding S1_2_def sum_upto_def by (rule sum_abs)
        also have "\<dots> \<le> sum_upto (\<lambda>m. 1 * (\<epsilon> * (x / m))) y"
          unfolding abs_mult sum_upto_def
        proof (intro sum_mono mult_mono less_imp_le[OF A(2)])
          fix m assume m: "m \<in> {i. 0 < i \<and> real i \<le> real y}"
          hence "real m \<le> real y" by simp
          also from x A(1) have "\<dots> = of_int \<lfloor>x / A\<rfloor>" by (simp add: y_def)
          also have "\<dots> \<le> x / A" by linarith
          finally show "A \<le> x / real m" using A(1) m by (simp add: field_simps)
        qed (auto simp: moebius_mu_def field_simps)
        also have "\<dots> = \<epsilon> * x * (\<Sum>i\<in>{0<..y}. inverse (real i))"
          by (simp add: sum_upto_altdef sum_distrib_left divide_simps)
        also have "(\<Sum>i\<in>{0<..y}. inverse (real i)) = harm (nat \<lfloor>y\<rfloor>)"
          unfolding harm_def by (intro sum.cong) auto
        also have "\<dots> \<le> ln (nat \<lfloor>y\<rfloor>) + 1"
          by (rule harm_le) (use y in auto)
        also have "ln (nat \<lfloor>y\<rfloor>) \<le> ln x"
          using y by simp
        finally show "\<bar>S1_2\<bar> \<le> \<epsilon> * x * (ln x + 1)" using \<epsilon> x by simp
      qed (use x in auto)
      finally have S1_bound: "\<bar>S1\<bar> \<le> x + \<epsilon> * x * ln x + \<epsilon> * x"
        by (simp add: algebra_simps)
      
      have "\<bar>S2\<bar> \<le> (\<Sum>m | y < m \<and> real m \<le> x. \<bar>moebius_mu m * \<psi> (x / m)\<bar>)"
        unfolding S2_def by (rule sum_abs)
      also have "\<dots> \<le> (\<Sum>m | y < m \<and> real m \<le> x. 1 * \<psi> A)"
        unfolding abs_mult using y
      proof (intro sum_mono mult_mono)
        fix m assume m: "m \<in> {m. y < m \<and> real m \<le> x}"
        hence "y < m" by simp
        moreover have "y = of_int \<lfloor>x / A\<rfloor>" using x A(1) by (simp add: y_def)
        ultimately have "\<lfloor>x / A\<rfloor> < m" by simp
        hence "x / A \<le> real m" by linarith
        hence "\<psi> (x / real m) \<le> \<psi> A"
          using m A(1) by (intro \<psi>_mono) (auto simp: field_simps)
        thus "\<bar>\<psi> (x / real m)\<bar> \<le> \<psi> A"
          by (simp add: \<psi>_nonneg)
      qed (auto simp: moebius_mu_def \<psi>_nonneg field_simps intro!: \<psi>_mono)
      also have "\<dots> \<le> sum_upto (\<lambda>_. 1 * \<psi> A) x"
        unfolding sum_upto_def by (intro sum_mono2) auto
      also have "\<dots> = real (nat \<lfloor>x\<rfloor>) * \<psi> A"
        by (simp add: sum_upto_altdef)
      also have "\<dots> \<le> x * \<psi> A"
        using x by (intro mult_right_mono) auto
      finally have S2_bound: "\<bar>S2\<bar> \<le> x * \<psi> A" .
  
      have "\<bar>H x\<bar> \<le> \<bar>S1\<bar> + \<bar>S2\<bar>" using abs_H_eq by linarith
      also have "\<dots> \<le> x + \<epsilon> * x * ln x + \<epsilon> * x + x * \<psi> A"
        by (intro add_mono S1_bound S2_bound)
      finally have "\<bar>H x\<bar> \<le> (1 + \<epsilon> + \<psi> A) * x + \<epsilon> * x * ln x"
        by (simp add: algebra_simps)
      thus "\<bar>H x\<bar> / (x * ln x) \<le> (1 + \<epsilon> + \<psi> A) / ln x + \<epsilon>"
        using x by (simp add: field_simps)
    qed
  
    have "eventually (\<lambda>x. \<bar>H x\<bar> / (x * ln x) \<le> (1 + \<epsilon> + \<psi> A) / ln x + \<epsilon>) at_top"
      using eventually_ge_at_top[of A] by eventually_elim (use H_bound in auto)
    moreover have "eventually (\<lambda>x. (1 + \<epsilon> + \<psi> A) / ln x + \<epsilon> < \<epsilon>') at_top"
      unfolding \<epsilon>_def using \<epsilon>' by real_asymp
    moreover have "eventually (\<lambda>x. \<bar>H x\<bar> / (x * ln x) = \<bar>H x / (x * ln x)\<bar>) at_top"
      using eventually_gt_at_top[of 1] by eventually_elim (simp add: abs_mult)
    ultimately have "eventually (\<lambda>x. \<bar>H x / (x * ln x)\<bar> < \<epsilon>') at_top"
      by eventually_elim simp
    thus "eventually (\<lambda>x. dist (H x / (x * ln x)) 0 < \<epsilon>') at_top"
      by (simp add: dist_norm)
  qed
  hence "(\<lambda>x. H x / (x * ln x)) \<in> o(\<lambda>_. 1)"
    by (intro smalloI_tendsto) auto
  hence "(\<lambda>x. H x / (x * ln x) + (M x / x - H x / (x * ln x))) \<in> o(\<lambda>_. 1)"
  proof (rule sum_in_smallo)
    have "(\<lambda>x. M x / x - H x / (x * ln x)) \<in> O(\<lambda>x. 1 / ln x)"
      by (rule sum_moebius_mu_aux1)
    also have "(\<lambda>x::real. 1 / ln x) \<in> o(\<lambda>_. 1)"
      by real_asymp
    finally show "(\<lambda>x. M x / x - H x / (x * ln x)) \<in> o(\<lambda>_. 1)" .
  qed
  thus ?thesis by (simp add: landau_divide_simps)
qed

(* 4.15 *)
theorem sum_moebius_mu_sublinear_imp_PNT:
  assumes "M \<in> o(\<lambda>x. x)"
  shows   "\<psi> \<sim>[at_top] (\<lambda>x. x)"
proof -
  define \<sigma> :: "nat \<Rightarrow> real" where [simp]: "\<sigma> = (\<lambda>n. real (divisor_count n))"
  define C where [simp]: "C = (euler_mascheroni :: real)"
  define f :: "nat \<Rightarrow> real" where "f = (\<lambda>n. \<sigma> n - ln n - 2 * C)"
  define F where [simp]: "F = sum_upto f"
  write moebius_mu ("\<mu>")

  \<comment> \<open>The proof is based on the fact that $\psi(x)-x$ can be approximated fairly well by
      the Dirichlet product $\sum_{n\leq x} \sum_{d\mid n} \mu(d) f(n/d)$:\<close>
  have eq: "\<psi> x - x = -sum_upto (dirichlet_prod \<mu> f) x - frac x - 2 * C" if x: "x \<ge> 1" for x
  proof -
    have "\<lfloor>x\<rfloor> - \<psi> x - 2 * C =
            sum_upto (\<lambda>_. 1) x - sum_upto mangoldt x - sum_upto (\<lambda>n. if n = 1 then 2 * C else 0) x"
      using x by (simp add: sum_upto_altdef \<psi>_def le_nat_iff le_floor_iff)
    also have "\<dots> = sum_upto (\<lambda>n. 1 - mangoldt n - (if n = 1 then 2 * C else 0)) x"
      by (simp add: sum_upto_def sum_subtractf)
    also have "\<dots> = sum_upto (dirichlet_prod \<mu> f) x"
      by (intro sum_upto_cong refl moebius_inversion)
         (auto simp: divisor_count_def sum_subtractf mangoldt_sum f_def)
    finally show "\<psi> x - x = -sum_upto (dirichlet_prod \<mu> f) x - frac x - 2 * C"
      by (simp add: algebra_simps frac_def)
  qed

  \<comment> \<open>We now obtain a bound of the form \<open>\<bar>F x\<bar> \<le> B * sqrt x\<close>.\<close>
  have "F \<in> O(sqrt)"
  proof -
    have "F \<in> \<Theta>(\<lambda>x. (sum_upto \<sigma> x - (x * ln x + (2 * C - 1) * x)) -
                      (sum_upto ln x - x * ln x + x) + 2 * C * frac x)" (is "_ \<in> \<Theta>(?rhs)")
      by (intro bigthetaI_cong eventually_mono[OF eventually_ge_at_top[of 1]])
         (auto simp: sum_upto_altdef sum_subtractf f_def frac_def algebra_simps sum.distrib)
    also have "?rhs \<in> O(sqrt)"
    proof (rule sum_in_bigo, rule sum_in_bigo)
      show "(\<lambda>x. sum_upto \<sigma> x - (x * ln x + (2 * C - 1) * x)) \<in> O(sqrt)"
        unfolding C_def \<sigma>_def by (rule summatory_divisor_count_asymptotics)
      show "(\<lambda>x. sum_upto (\<lambda>x. ln (real x)) x - x * ln x + x) \<in> O(sqrt)"
        by (rule landau_o.big.trans[OF sum_upto_ln_stirling_weak_bigo]) real_asymp
    qed (use euler_mascheroni_pos in real_asymp)
    finally show ?thesis .
  qed
  hence "(\<lambda>n. F (real n)) \<in> O(sqrt)"
    by (rule landau_o.big.compose) real_asymp
  from natfun_bigoE[OF this, of 1] obtain B :: real
    where B: "B > 0" "\<And>n. n \<ge> 1 \<Longrightarrow> \<bar>F (real n)\<bar> \<le> B * sqrt (real n)"
    by auto
  have B': "\<bar>F x\<bar> \<le> B * sqrt x" if "x \<ge> 1" for x
  proof -
    have "\<bar>F x\<bar> \<le> B * sqrt (nat \<lfloor>x\<rfloor>)"
      using B(2)[of "nat \<lfloor>x\<rfloor>"] that by (simp add: sum_upto_altdef le_nat_iff le_floor_iff)
    also have "\<dots> \<le> B * sqrt x"
      using B(1) that by (intro mult_left_mono) auto
    finally show ?thesis .
  qed

  \<comment> \<open>Next, we obtain a good bound for $\sum_{n\leq x} \frac{1}{\sqrt{n}}$.\<close>
  from zeta_partial_sum_le_pos''[of "1 / 2"] obtain A 
    where A: "A > 0" "\<And>x. x \<ge> 1 \<Longrightarrow> \<bar>sum_upto (\<lambda>n. 1 / sqrt n) x\<bar> \<le> A * sqrt x"
    by (auto simp: max_def powr_half_sqrt powr_minus field_simps)

  \<comment> \<open>Finally, we show that $\sum_{n\leq x} \sum_{d\mid n} \mu(d) f(n/d) \in o(x)$.\<close>
  have "sum_upto (dirichlet_prod \<mu> f) \<in> o(\<lambda>x. x)"
  proof (rule landau_o.smallI)
    fix \<epsilon> :: real
    assume \<epsilon>: "\<epsilon> > 0"
  
    have *: "eventually (\<lambda>x. \<bar>sum_upto (dirichlet_prod \<mu> f) x\<bar> \<le> \<epsilon> * x) at_top"
      if b: "b \<ge> 1" "A * B / sqrt b \<le> \<epsilon> / 3" "B / sqrt b \<le> \<epsilon> / 3" for b
    proof -
      define K :: real where "K = sum_upto (\<lambda>n. \<bar>f n\<bar> / n) b"
      have "C \<noteq> (1 / 2)" using euler_mascheroni_gt_19_over_33 by auto
      hence K: "K > 0" unfolding K_def f_def sum_upto_def
        by (intro sum_pos2[where i = 1]) (use \<open>b \<ge> 1\<close> in auto)
      have "eventually (\<lambda>x. \<bar>M x / x\<bar> < \<epsilon> / 3 / K) at_top"
        using smalloD_tendsto[OF assms] \<epsilon> K by (auto simp: tendsto_iff dist_norm)
      then obtain c' where c': "\<And>x. x \<ge> c' \<Longrightarrow> \<bar>M x / x\<bar> < \<epsilon> / 3 / K"
        by (auto simp: eventually_at_top_linorder)
      define c where "c = max 1 c'"
      have c: "\<bar>M x\<bar> < \<epsilon> / 3 / K * x" if "x \<ge> c" for x
        using c'[of x] that by (simp add: c_def field_simps)
  
      show "eventually (\<lambda>x. \<bar>sum_upto (dirichlet_prod \<mu> f) x\<bar> \<le> \<epsilon> * x) at_top"
        using eventually_ge_at_top[of "b * c"] eventually_ge_at_top[of 1] eventually_ge_at_top[of b]
      proof eventually_elim
        case (elim x)
        define a where "a = x / b"
        from elim \<open>b \<ge> 1\<close> have ab: "a \<ge> 1" "b \<ge> 1" "a * b = x"
          by (simp_all add: a_def field_simps)
        from ab have "a * 1 \<le> a * b" by (intro mult_mono) auto
        hence "a \<le> x" by (simp add: ab(3))
        from ab have "a * 1 \<le> a * b" and "1 * b \<le> a * b" by (intro mult_mono; simp)+
        hence "a \<le> x" "b \<le> x" by (simp_all add: ab(3))
        have "a = x / b" "b = x / a" using ab by (simp_all add: field_simps)
  
        have "sum_upto (dirichlet_prod \<mu> f) x =
                sum_upto (\<lambda>n. \<mu> n * F (x / n)) a + sum_upto (\<lambda>n. M (x / n) * f n) b - M a * F b"
          unfolding M_def F_def by (rule hyperbola_method) (use ab in auto)
        also have "\<bar>\<dots>\<bar> \<le> \<epsilon> / 3 * x + \<epsilon> / 3 * x + \<epsilon> / 3 * x"
        proof (rule order.trans[OF abs_triangle_ineq4] order.trans[OF abs_triangle_ineq] add_mono)+
          have "\<bar>sum_upto (\<lambda>n. \<mu> n * F (x / real n)) a\<bar> \<le> sum_upto (\<lambda>n. \<bar>\<mu> n * F (x / real n)\<bar>) a"
            unfolding sum_upto_def by (rule sum_abs)
          also have "\<dots> \<le> sum_upto (\<lambda>n. 1 * (B * sqrt (x / real n))) a"
            unfolding sum_upto_def abs_mult using \<open>a \<le> x\<close>
            by (intro sum_mono mult_mono B') (auto simp: moebius_mu_def)
          also have "\<dots> = B * sqrt x * sum_upto (\<lambda>n. 1 / sqrt n) a"
            by (simp add: sum_upto_def sum_distrib_left real_sqrt_divide)
          also have "\<dots> \<le> B * sqrt x * \<bar>sum_upto (\<lambda>n. 1 / sqrt n) a\<bar>"
            using B(1) \<open>x \<ge> 1\<close> by (intro mult_left_mono) auto
          also have "\<dots> \<le> B * sqrt x * (A * sqrt a)"
            using \<open>a \<ge> 1\<close> B(1) \<open>x \<ge> 1\<close> by (intro mult_left_mono A) auto
          also have "\<dots> = A * B / sqrt b * x"
            using ab \<open>x \<ge> 1\<close>\<open>x \<ge> 1\<close> by (subst \<open>a = x / b\<close>) (simp_all add: field_simps real_sqrt_divide)
          also have "\<dots> \<le> \<epsilon> / 3 * x" using \<open>x \<ge> 1\<close> by (intro mult_right_mono b) auto
          finally show "\<bar>sum_upto (\<lambda>n. \<mu> n * F (x / n)) a\<bar> \<le> \<epsilon> / 3 * x" .
        next
          have "\<bar>sum_upto (\<lambda>n. M (x / n) * f n) b\<bar> \<le> sum_upto (\<lambda>n. \<bar>M (x / n) * f n\<bar>) b"
            unfolding sum_upto_def by (rule sum_abs)
          also have "\<dots> \<le> sum_upto (\<lambda>n. \<epsilon> / 3 / K * (x / n) * \<bar>f n\<bar>) b"
            unfolding sum_upto_def abs_mult
          proof (intro sum_mono mult_right_mono)
            fix n assume n: "n \<in> {n. n > 0 \<and> real n \<le> b}"
            have "c \<ge> 0" by (simp add: c_def)
            with n have "c * n \<le> c * b" by (intro mult_left_mono) auto
            also have "\<dots> \<le> x" using \<open>b * c \<le> x\<close> by (simp add: algebra_simps)
            finally show "\<bar>M (x / real n)\<bar> \<le> \<epsilon> / 3 / K * (x / real n)"
              by (intro less_imp_le[OF c]) (use n in \<open>auto simp: field_simps\<close>)
          qed auto
          also have "\<dots> = \<epsilon> / 3 * x / K * sum_upto (\<lambda>n. \<bar>f n\<bar> / n) b"
            by (simp add: sum_upto_def sum_distrib_left)
          also have "\<dots> = \<epsilon> / 3 * x"
            unfolding K_def [symmetric] using K by simp
          finally show "\<bar>sum_upto (\<lambda>n. M (x / real n) * f n) b\<bar> \<le> \<epsilon> / 3 * x" .
        next
          have "\<bar>M a * F b\<bar> \<le> a * (B * sqrt b)"
            unfolding abs_mult using ab by (intro mult_mono sum_moebius_mu_bound B') auto
          also have "\<dots> = B / sqrt b * x"
            using ab(1,2) by (simp add: real_sqrt_mult \<open>b = x / a\<close> real_sqrt_divide field_simps)
          also have "\<dots> \<le> \<epsilon> / 3 * x" using \<open>x \<ge> 1\<close> by (intro mult_right_mono b) auto
          finally show "\<bar>M a * F b\<bar> \<le> \<epsilon> / 3 * x" .
        qed
        also have "\<dots> = \<epsilon> * x" by simp
        finally show ?case .
      qed
    qed
    
    have "eventually (\<lambda>b::real. b \<ge> 1 \<and> A * B / sqrt b \<le> \<epsilon> / 3 \<and> B / sqrt b \<le> \<epsilon> / 3) at_top"
      using \<epsilon> by (intro eventually_conj; real_asymp)
    then obtain b where "b \<ge> 1" "A * B / sqrt b \<le> \<epsilon> / 3" "B / sqrt b \<le> \<epsilon> / 3"
      by (auto simp: eventually_at_top_linorder)
    from *[OF this] have "eventually (\<lambda>x. \<bar>sum_upto (dirichlet_prod \<mu> f) x\<bar> \<le> \<epsilon> * x) at_top" .
    thus "eventually (\<lambda>x. norm (sum_upto (dirichlet_prod \<mu> f) x) \<le> \<epsilon> * norm x) at_top"
      using eventually_ge_at_top[of 0] by eventually_elim simp
  qed

  have "(\<lambda>x. \<psi> x - x) \<in> \<Theta>(\<lambda>x. -(sum_upto (dirichlet_prod \<mu> f) x + (frac x + 2 * C)))"
    by (intro bigthetaI_cong eventually_mono[OF eventually_ge_at_top[of 1]], subst eq) auto
  hence "(\<lambda>x. \<psi> x - x) \<in> \<Theta>(\<lambda>x. sum_upto (dirichlet_prod \<mu> f) x + (frac x + 2 * C))"
    by (simp only: landau_theta.uminus)
  also have "(\<lambda>x. sum_upto (dirichlet_prod \<mu> f) x + (frac x + 2 * C)) \<in> o(\<lambda>x. x)"
    using \<open>sum_upto (dirichlet_prod \<mu> f) \<in> o(\<lambda>x. x)\<close> by (rule sum_in_smallo) real_asymp+
  finally show ?thesis by (rule smallo_imp_asymp_equiv)
qed


text \<open>
  We now turn to a related fact: For the weighted sum $A(x) := \sum_{n\leq x} \mu(n)/n$, the
  asymptotic relation $A(x)\in o(1)$ is also equivalent to the Prime Number Theorem.
  Like Apostol, we only show one direction, namely that $A(x)\in o(1)$ implies the PNT.
\<close>

context
  fixes A defines "A \<equiv> sum_upto (\<lambda>n. moebius_mu n / n)"
begin

lemma sum_upto_moebius_mu_integral': "x > 1 \<Longrightarrow> (A has_integral x * A x - M x) {1..x}"
  and sum_upto_moebius_mu_integrable': "a \<ge> 1 \<Longrightarrow> A integrable_on {a..b}"
proof -
  {
    fix a b :: real
    assume ab: "a \<ge> 1" "a < b"
    have "((\<lambda>t. A t * 1) has_integral A b * b - A a * a -
            (\<Sum>n\<in>real -` {a<..b}. moebius_mu n / n * n)) {a..b}"
      unfolding M_def A_def using ab
      by (intro partial_summation_strong [where X = "{}"])
         (auto intro!: derivative_eq_intros continuous_intros
               simp flip: has_field_derivative_iff_has_vector_derivative)
  } note * = this
  {
    fix x :: real assume x: "x > 1"
    have [simp]: "A 1 = 1" by (simp add: A_def)
    have "(\<Sum>n\<in>real -` {1<..x}. moebius_mu n / n * n) =
            (\<Sum>n\<in>insert 1 (real -` {1<..x}). moebius_mu n / n * n) - 1"
      using finite_vimage_real_of_nat_greaterThanAtMost[of 1 x] by (subst sum.insert) auto
    also have "insert 1 (real -` {1<..x}) = {n. n > 0 \<and> real n \<le> x}"
      using x by auto
    also have "(\<Sum>n | 0 < n \<and> real n \<le> x. moebius_mu n / real n * real n) = M x"
      unfolding M_def sum_upto_def by (intro sum.cong) auto
    finally show "(A has_integral x * A x - M x) {1..x}" using *[of 1 x] x by (simp add: mult_ac)
  }
  {
    fix a b :: real assume ab: "a \<ge> 1"
    show "A integrable_on {a..b}"
      using *[of a b] ab
      by (cases a b rule: linorder_cases) (auto intro: integrable_negligible)
  }
qed

(* 4.16 *)
theorem sum_moebius_mu_div_n_smallo_imp_PNT:
  assumes smallo: "A \<in> o(\<lambda>_. 1)"
  shows   "M \<in> o(\<lambda>x. x)" and "\<psi> \<sim>[at_top] (\<lambda>x. x)"
proof -
  have "eventually (\<lambda>x. M x = x * A x - integral {1..x} A) at_top"
    using eventually_gt_at_top[of 1]
    by eventually_elim (use sum_upto_moebius_mu_integral' in \<open>simp add: has_integral_iff\<close>)
  hence "M \<in> \<Theta>(\<lambda>x. x * A x - integral {1..x} A)"
    by (rule bigthetaI_cong)
  also have "(\<lambda>x. x * A x - integral {1..x} A) \<in> o(\<lambda>x. x)"
  proof (intro sum_in_smallo)
    from smallo show "(\<lambda>x. x * A x) \<in> o(\<lambda>x. x)"
      by (simp add: landau_divide_simps)
    show "(\<lambda>x. integral {1..x} A) \<in> o(\<lambda>x. x)"
      by (intro integral_smallo[OF smallo] sum_upto_moebius_mu_integrable')
         (auto intro!: derivative_eq_intros filterlim_ident)
  qed
  finally show "M \<in> o(\<lambda>x. x)" .
  thus "\<psi> \<sim>[at_top] (\<lambda>x. x)"
    by (rule sum_moebius_mu_sublinear_imp_PNT)
qed

end

end

end