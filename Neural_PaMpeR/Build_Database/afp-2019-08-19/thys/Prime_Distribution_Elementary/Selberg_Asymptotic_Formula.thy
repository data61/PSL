(*
  File:    Selberg_Asymptotic_Formula.thy
  Author:  Manuel Eberl, TU München

  Selberg's asymptotic formula, which is an important ingredient in the elementary
  proof of the Prime Number Theorem by Selberg and Erdős.
*)
section \<open>Selberg's asymptotic formula\<close>
theory Selberg_Asymptotic_Formula
imports
  More_Dirichlet_Misc
  Prime_Number_Theorem.Prime_Counting_Functions
  Shapiro_Tauberian
  Euler_MacLaurin.Euler_MacLaurin_Landau
  Partial_Zeta_Bounds
begin

text \<open>
  Following Apostol, we first show an inversion formula: Consider a function $f(x)$ for 
  $x\in\mathbb{R}_{{}>\,0}$. Define $g(x) := \ln x \cdot \sum_{n\leq x} f(x / n)$. Then:
  \[f(x) \ln x + \sum_{n\leq x} \Lambda(n) f(x/n) = \sum_{n\leq x} \mu(n) g(x/n)\]
\<close>
(* 4.17 *)
locale selberg_inversion =
  fixes F G :: "real \<Rightarrow> 'a :: {real_algebra_1, comm_ring_1}"
  defines "G \<equiv> (\<lambda>x. of_real (ln x) * sum_upto (\<lambda>n. F (x / n)) x)"
begin  

lemma eq:
  assumes "x \<ge> 1"
  shows "F x * of_real (ln x) + dirichlet_prod' mangoldt F x = dirichlet_prod' moebius_mu G x"
proof -
  have "F x * of_real (ln x) =
          dirichlet_prod' (\<lambda>n. if n = 1 then 1 else 0) (\<lambda>x. F x * of_real (ln x)) x"
    by (subst dirichlet_prod'_one_left) (use \<open>x \<ge> 1\<close> in auto)
  also have "\<dots> = dirichlet_prod' (\<lambda>n. \<Sum>d | d dvd n. moebius_mu d) (\<lambda>x. F x * of_real (ln x)) x"
    by (intro dirichlet_prod'_cong refl, subst sum_moebius_mu_divisors') auto
  finally have eq1: "F x * of_real (ln x) = \<dots>" .

  have eq2: "dirichlet_prod' mangoldt F x =
               dirichlet_prod' (dirichlet_prod moebius_mu (\<lambda>n. of_real (ln (real n)))) F x"
  proof (intro dirichlet_prod'_cong refl)
    fix n :: nat assume n: "n > 0"
    thus "mangoldt n = dirichlet_prod moebius_mu (\<lambda>n. of_real (ln (real n)) :: 'a) n"
      by (intro moebius_inversion mangoldt_sum [symmetric]) auto
  qed

  have "F x * of_real (ln x) + dirichlet_prod' mangoldt F x =
          sum_upto (\<lambda>n. F (x / n) * (\<Sum>d | d dvd n.
            moebius_mu d * of_real (ln (x / n) + ln (n div d)))) x"
    unfolding eq1 eq2 unfolding dirichlet_prod'_def sum_upto_def
    by (simp add: algebra_simps sum.distrib dirichlet_prod_def sum_distrib_left sum_distrib_right)
  also have "\<dots> = sum_upto (\<lambda>n. F (x / n) * (\<Sum>d | d dvd n. moebius_mu d * of_real (ln (x / d)))) x"
    using \<open>x \<ge> 1\<close> by (intro sum_upto_cong refl arg_cong2[where f = "\<lambda>x y. x * y"] sum.cong)
                     (auto elim!: dvdE simp: ln_div ln_mult)
  also have "\<dots> = sum_upto (\<lambda>n. \<Sum>d | d dvd n. moebius_mu d * of_real (ln (x / d)) * F (x / n)) x"
    by (simp add: sum_distrib_left sum_distrib_right mult_ac)
  also have "\<dots> = (\<Sum>(n,d)\<in>(SIGMA n:{n. n > 0 \<and> real n \<le> x}. {d. d dvd n}).
                    moebius_mu d * of_real (ln (x / d)) * F (x / n))"
    unfolding sum_upto_def by (subst sum.Sigma) (auto simp: case_prod_unfold)
  also have "\<dots> = (\<Sum>(d,q)\<in>(SIGMA d:{d. d > 0 \<and> real d \<le> x}. {q. q > 0 \<and> real q \<le> x / d}).
                    moebius_mu d * of_real (ln (x / d)) * F (x / (q * d)))"
    by (rule sum.reindex_bij_witness[of _ "\<lambda>(d,q). (d * q, d)" "\<lambda>(n,d). (d, n div d)"])
       (auto simp: Real.real_of_nat_div field_simps dest: dvd_imp_le)
  also have "\<dots> = sum_upto (\<lambda>d. moebius_mu d * of_real (ln (x / d)) *
                                  sum_upto (\<lambda>q. F (x / (q * d))) (x / d)) x"
    by (subst sum.Sigma [symmetric]) (auto simp: sum_upto_def sum_distrib_left)
  also have "\<dots> = dirichlet_prod' moebius_mu G x"
    by (simp add: dirichlet_prod'_def G_def mult_ac)
  finally show ?thesis .
qed

end

text \<open>
  We can now show Selberg's formula
  \[\psi(x)\ln x + \sum_{n\leq x} \Lambda(n)\psi(x/n) = 2x\ln x + O(x)\ .\]
\<close>
(* 4.18 *)
theorem selberg_asymptotic_formula:
  includes prime_counting_notation
  shows    "(\<lambda>x. \<psi> x * ln x + dirichlet_prod' mangoldt \<psi> x) =o
               (\<lambda>x. 2 * x * ln x) +o O(\<lambda>x. x)"
proof -
  define C :: real where [simp]: "C = euler_mascheroni"
  define F2 :: "real \<Rightarrow> real" where [simp]: "F2 = (\<lambda>x. x - C - 1)"
  define G1 where "G1 = (\<lambda>x. ln x * sum_upto (\<lambda>n. \<psi> (x / n)) x)"
  define G2 where "G2 = (\<lambda>x. ln x * sum_upto (\<lambda>n. F2 (x / n)) x)"

  interpret F1: selberg_inversion \<psi> G1
    by unfold_locales (simp_all add: G1_def)
  interpret F2: selberg_inversion F2 G2
    by unfold_locales (simp_all add: G2_def)

  have G1_bigo: "(\<lambda>x. G1 x - (x * ln x ^ 2 - x * ln x)) \<in> O(\<lambda>x. ln x ^ 2)"
  proof -
    have "(\<lambda>x. ln x * (sum_upto (\<lambda>n. \<psi> (x / n)) x - x * ln x + x)) \<in> O(\<lambda>x. ln x * ln x)" 
      by (intro landau_o.big.mult_left sum_upto_\<psi>_x_over_n_asymptotics)
    thus ?thesis by (simp add: power2_eq_square G1_def algebra_simps)
  qed

  have G2_bigo: "(\<lambda>x. G2 x - (x * ln x ^ 2 - x * ln x)) \<in> O(ln)"
  proof -
  define R1 :: "real \<Rightarrow> real" where "R1 = (\<lambda>x. x * ln x * (harm (nat \<lfloor>x\<rfloor>) - (ln x + C)))"
  define R2 :: "real \<Rightarrow> real" where "R2 = (\<lambda>x. (C + 1) * ln x * frac x)"
    have "(\<lambda>x. G2 x - (x * ln x ^ 2 - x * ln x)) \<in> \<Theta>(\<lambda>x. R1 x + R2 x)"
    proof (intro bigthetaI_cong eventually_mono[OF eventually_ge_at_top[of 1]])
      fix x :: real assume x: "x \<ge> 1"
      have "G2 x = x * ln x * sum_upto (\<lambda>n. 1 / n) x - (C + 1) * \<lfloor>x\<rfloor> * ln x"
        using x by (simp add: G2_def sum_upto_altdef sum_subtractf
                              sum_distrib_left sum_distrib_right algebra_simps)
      also have "sum_upto (\<lambda>n. 1 / n) x = harm (nat \<lfloor>x\<rfloor>)"
        using x unfolding sum_upto_def harm_def
        by (intro sum.cong) (auto simp: field_simps le_nat_iff le_floor_iff)
      also have "x * ln x * harm (nat \<lfloor>x\<rfloor>) - (C + 1) * \<lfloor>x\<rfloor> * ln x =
                   x * ln x ^ 2 - x * ln x + R1 x + R2 x"
        by (simp add: R1_def R2_def algebra_simps frac_def power2_eq_square)
      finally show "G2 x - (x * ln x ^ 2 - x * ln x) = R1 x + R2 x" by simp
    qed
    also have "(\<lambda>x. R1 x + R2 x) \<in> O(ln)"
    proof (intro sum_in_bigo)
      have "(\<lambda>x::real. ln x - ln (nat \<lfloor>x\<rfloor>)) \<in> O(\<lambda>x. ln x - ln (x - 1))"
      proof (intro bigoI[of _ 1] eventually_mono[OF eventually_ge_at_top[of 2]])
        fix x :: real assume x: "x \<ge> 2"
        thus "norm (ln x - ln (nat \<lfloor>x\<rfloor>)) \<le> 1 * norm (ln x - ln (x - 1))" by auto
      qed
      also have "(\<lambda>x::real. ln x - ln (x - 1)) \<in> O(\<lambda>x. 1 / x)" by real_asymp
      finally have bigo_ln_floor: "(\<lambda>x::real. ln x - ln (nat \<lfloor>x\<rfloor>)) \<in> O(\<lambda>x. 1 / x)" .
  
      have "(\<lambda>x. harm (nat \<lfloor>x\<rfloor>) - (ln (nat \<lfloor>x\<rfloor>) + C)) \<in> O(\<lambda>x. 1 / nat \<lfloor>x\<rfloor>)"
        unfolding C_def using harm_expansion_bigo_simple2
        by (rule landau_o.big.compose) (* TODO: real_asymp should be able to do this *)
           (auto intro!: filterlim_compose[OF filterlim_nat_sequentially filterlim_floor_sequentially])
      also have "(\<lambda>x. 1 / nat \<lfloor>x\<rfloor>) \<in> O(\<lambda>x. 1 / x)" by real_asymp
      finally have "(\<lambda>x. harm (nat \<lfloor>x\<rfloor>) - (ln (nat \<lfloor>x\<rfloor>) + C) - (ln x - ln (nat \<lfloor>x\<rfloor>)))
                       \<in> O(\<lambda>x. 1 / x)" by (rule sum_in_bigo[OF _bigo_ln_floor])
      hence "(\<lambda>x. harm (nat \<lfloor>x\<rfloor>) - (ln x + C)) \<in> O(\<lambda>x. 1 / x)" by (simp add: algebra_simps)
      hence "(\<lambda>x. x * ln x * (harm (nat \<lfloor>x\<rfloor>) - (ln x + C))) \<in> O(\<lambda>x. x * ln x * (1 / x))"
        by (intro landau_o.big.mult_left)
      thus "R1 \<in> O(ln)" by (simp add: landau_divide_simps R1_def)
    next
      have "R2 \<in> O(\<lambda>x. 1 * ln x * 1)" (* TODO: real_asymp? *)
        unfolding R2_def by (intro landau_o.big.mult landau_o.big_refl) real_asymp+
      thus "R2 \<in> O(ln)" by (simp add: R2_def)
    qed
    finally show "(\<lambda>x. G2 x - (x * (ln x)\<^sup>2 - x * ln x)) \<in> O(ln)" .
  qed
  hence G2_bigo': "(\<lambda>x. G2 x - (x * (ln x)\<^sup>2 - x * ln x)) \<in> O(\<lambda>x. ln x ^ 2)"
    by (rule landau_o.big.trans) real_asymp+

  \<comment> \<open>Now things become a bit hairy. In order to show that the `Big-O' bound is actually
      valid for all \<open>x \<ge> 1\<close>, we need to show that \<open>G1 x - G2 x\<close> is bounded on any compact
      interval starting at 1.\<close>
  have "\<exists>c>0. \<forall>x\<ge>1. \<bar>G1 x - G2 x\<bar> \<le> c * \<bar>sqrt x\<bar>"
  proof (rule bigoE_bounded_real_fun)
    have "(\<lambda>x. G1 x - G2 x) \<in> O(\<lambda>x. ln x ^ 2)"
      using sum_in_bigo(2)[OF G1_bigo G2_bigo'] by simp
    also have "(\<lambda>x::real. ln x ^ 2) \<in> O(sqrt)" by real_asymp
    finally show "(\<lambda>x. G1 x - G2 x) \<in> O(sqrt)" .
  next
    fix x :: real assume "x \<ge> 1"
    thus "\<bar>sqrt x\<bar> \<ge> 1" by simp
  next
    fix b :: real assume b: "b \<ge> 1"
    show "bounded ((\<lambda>x. G1 x - G2 x) ` {1..b})"
    proof (rule boundedI, safe)
      fix x assume x: "x \<in> {1..b}"
      have "\<bar>G1 x - G2 x\<bar> = \<bar>ln x * sum_upto (\<lambda>n. \<psi> (x / n) - F2 (x / n)) x\<bar>"
        by (simp add: G1_def G2_def sum_upto_def sum_distrib_left ring_distribs sum_subtractf)
      also have "\<dots> = ln x * \<bar>sum_upto (\<lambda>n. \<psi> (x / n) - F2 (x / n)) x\<bar>"
        using x b by (simp add: abs_mult)
      also have "\<bar>sum_upto (\<lambda>n. \<psi> (x / n) - F2 (x / n)) x\<bar> \<le>
                   sum_upto (\<lambda>n. \<bar>\<psi> (x / n) - F2 (x / n)\<bar>) x"
        unfolding sum_upto_def by (rule sum_abs)
      also have "\<dots> \<le> sum_upto (\<lambda>n. \<psi> x + (x + C + 1)) x"
        unfolding sum_upto_def
      proof (intro sum_mono)
        fix n assume n: "n \<in> {n. n > 0 \<and> real n \<le> x}"
        hence le: "x / n \<le> x / 1" by (intro divide_left_mono) auto
        thus "\<bar>\<psi> (x / n) - F2 (x / n)\<bar> \<le> \<psi> x + (x + C + 1)"
          unfolding F2_def using euler_mascheroni_pos x le \<psi>_nonneg \<psi>_mono[of "x / n" x]
          by (intro order.trans[OF abs_triangle_ineq]
                    order.trans[OF abs_triangle_ineq4] add_mono) auto
      qed
      also have "\<dots> = (\<psi> x + (x + C + 1)) * \<lfloor>x\<rfloor>"
        using x by (simp add: sum_upto_altdef)
      also have "ln x * ((\<psi> x + (x + C + 1)) * real_of_int \<lfloor>x\<rfloor>) \<le>
                   ln b * ((\<psi> b + (b + C + 1)) * real_of_int \<lfloor>b\<rfloor>)"
        using euler_mascheroni_pos x
        by (intro mult_mono add_mono order.refl \<psi>_mono add_nonneg_nonneg mult_nonneg_nonneg
                     \<psi>_nonneg) (auto intro: floor_mono)
      finally show "norm (G1 x - G2 x) \<le> ln b * ((\<psi> b + (b + C + 1)) * real_of_int \<lfloor>b\<rfloor>)"
        using x by (simp add: mult_left_mono)
    qed
  qed auto
  then obtain A where A: "A > 0" "\<And>x. x \<ge> 1 \<Longrightarrow> \<bar>G1 x - G2 x\<bar> \<le> A * sqrt x" by auto

  \<comment> \<open>The rest of the proof now consists merely of combining some asymptotic estimates.\<close>
  have "(\<lambda>x. (\<psi> x - F2 x) * ln x + sum_upto (\<lambda>n. mangoldt n * (\<psi> (x / n) - F2 (x / n))) x)
          \<in> \<Theta>(\<lambda>x. sum_upto (\<lambda>n. moebius_mu n * (G1 (x / n) - G2 (x / n))) x)"
  proof (intro bigthetaI_cong eventually_mono[OF eventually_ge_at_top[of 1]])
    fix x :: real assume x: "x \<ge> 1"
    have "(\<psi> x - F2 x) * ln x + sum_upto (\<lambda>n. mangoldt n * (\<psi> (x / n) - F2 (x / n))) x =
            (\<psi> x * of_real (ln x) + dirichlet_prod' mangoldt \<psi> x) -
            (F2 x * of_real (ln x) + dirichlet_prod' mangoldt F2 x)"
      by (simp add: algebra_simps dirichlet_prod'_def sum_upto_def sum_subtractf sum.distrib)
    also have "\<dots> = sum_upto (\<lambda>n. moebius_mu n * (G1 (x / n) - G2 (x / n))) x"
      unfolding F1.eq[OF x] F2.eq[OF x]
      by (simp add: dirichlet_prod'_def sum_upto_def sum_subtractf sum.distrib algebra_simps)
    finally show "(\<psi> x - F2 x) * ln x + sum_upto (\<lambda>n. mangoldt n * (\<psi> (x/n) - F2 (x/n))) x = \<dots>" .
  qed
  also have "(\<lambda>x. sum_upto (\<lambda>n. moebius_mu n * (G1 (x / n) - G2 (x / n))) x) \<in>
               O(\<lambda>x. A * sqrt x * sum_upto (\<lambda>x. x powr (-1/2)) x)"
  proof (intro bigoI eventually_mono[OF eventually_ge_at_top[of 1]])
    fix x :: real assume x: "x \<ge> 1"
    have "\<bar>sum_upto (\<lambda>n. moebius_mu n * (G1 (x / n) - G2 (x / n))) x\<bar> \<le>
            sum_upto (\<lambda>n. \<bar>moebius_mu n * (G1 (x / n) - G2 (x / n))\<bar>) x"
      unfolding sum_upto_def by (rule sum_abs)
    also have "\<dots> \<le> sum_upto (\<lambda>n. 1 * (A * sqrt (x / n))) x"
      unfolding sum_upto_def abs_mult by (intro A sum_mono mult_mono) (auto simp: moebius_mu_def)
    also have "\<dots> = A * sqrt x * sum_upto (\<lambda>x. x powr (-1/2)) x"
      using x by (simp add: sum_upto_def powr_minus powr_half_sqrt sum_distrib_left
                            sum_distrib_right real_sqrt_divide field_simps)
    also have "\<dots> \<le> \<bar>A * sqrt x * sum_upto (\<lambda>x. x powr (-1/2)) x\<bar>" by simp
    finally show "norm (sum_upto (\<lambda>n. moebius_mu n * (G1 (x / n) - G2 (x / n))) x) \<le>
                    1 * norm (A * sqrt x * sum_upto (\<lambda>x. x powr (-1/2)) x)" by simp
  qed
  also have "(\<lambda>x. A * sqrt x * sum_upto (\<lambda>x. x powr (-1/2)) x) \<in> O(\<lambda>x. 1 * sqrt x * x powr (1/2))"
    using zeta_partial_sum_le_pos_bigo[of "1 / 2"]
    by (intro landau_o.big.mult ) (auto simp: max_def)
  also have "(\<lambda>x::real. 1 * sqrt x * x powr (1/2)) \<in> O(\<lambda>x. x)"
    by real_asymp
  finally have bigo: "(\<lambda>x. (\<psi> x - F2 x) * ln x + sum_upto (\<lambda>n. mangoldt n * (\<psi> (x/n) - F2 (x/n))) x)
                        \<in> O(\<lambda>x. x)" (is "?h \<in> _") .

  let ?R = "\<lambda>x. sum_upto (\<lambda>n. mangoldt n / n) x"
  let ?lhs = "\<lambda>x. \<psi> x * ln x + dirichlet_prod' mangoldt \<psi> x"

  note bigo
  also have "?h = (\<lambda>x. ?lhs x - (x * ln x - (C + 1) * (ln x + \<psi> x)) - x * ?R x)"
    by (rule ext) (simp add: algebra_simps dirichlet_prod'_def  sum_distrib_right \<psi>_def
                             sum_upto_def sum_subtractf sum.distrib sum_distrib_left)
  finally have "(\<lambda>x. ?lhs x - (x * ln x - (C + 1) * (ln x + \<psi> x)) - x * ?R x + x * (?R x - ln x))
                    \<in> O(\<lambda>x. x)" (is "?h' \<in> _")
  proof (rule sum_in_bigo)
    have "(\<lambda>x. x * (sum_upto (\<lambda>n. mangoldt n / real n) x - ln x)) \<in> O(\<lambda>x. x * 1)"
      by (intro landau_o.big.mult_left \<psi>.asymptotics)
    thus "(\<lambda>x. x * (sum_upto (\<lambda>n. mangoldt n / real n) x - ln x)) \<in> O(\<lambda>x. x)" by simp
  qed
  also have "?h' = (\<lambda>x. ?lhs x - (2 * x * ln x - (C + 1) * (ln x + \<psi> x)))"
    by (simp add: fun_eq_iff algebra_simps)
  finally have "(\<lambda>x. ?lhs x - (2*x*ln x - (C+1) * (ln x + \<psi> x)) - (C+1) * (ln x + \<psi> x)) \<in> O(\<lambda>x. x)"
  proof (rule sum_in_bigo)
    have "(\<lambda>x. ln x + \<psi> x) \<in> O(\<lambda>x. x)"
      by (intro sum_in_bigo bigthetaD1[OF \<psi>.bigtheta]) real_asymp+
    thus "(\<lambda>x. (C + 1) * (ln x + \<psi> x)) \<in> O(\<lambda>x. x)" by simp
  qed
  also have "(\<lambda>x. ?lhs x - (2*x*ln x - (C+1) * (ln x + \<psi> x)) - (C+1) * (ln x + \<psi> x)) =
               (\<lambda>x. ?lhs x - 2 * x * ln x)" by (simp add: algebra_simps)
  finally show ?thesis
    by (subst set_minus_plus [symmetric]) (simp_all add: fun_diff_def algebra_simps)
qed

end