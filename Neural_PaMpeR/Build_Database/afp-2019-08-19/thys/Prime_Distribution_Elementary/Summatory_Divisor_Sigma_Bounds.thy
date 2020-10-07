(*
  File:    Summatory_Divisor_Sigma_Bounds.thy
  Author:  Manuel Eberl, TU München

  Asymptotic expansions for the sums over the divisor function \<sigma>_x.
*)
section \<open>The asymptotics of the summatory divisor $\sigma$ function\<close>
theory Summatory_Divisor_Sigma_Bounds
  imports Partial_Zeta_Bounds More_Dirichlet_Misc
begin

text \<open>
  In this section, we analyse the asymptotic behaviour of the summatory divisor functions
  $\sum_{n\leq x} \sigma_\alpha(n)$ for real \<open>\<alpha>\<close>. This essentially tells us what the average value
  of these functions is for large \<open>x\<close>.

  The case \<open>\<alpha> = 0\<close> is not treated here since $\sigma_0$ is simply the divisor function,
  for which precise asymptotics are already available in the AFP.
\<close>

subsection \<open>Case 1: $\alpha = 1$\<close>

text \<open>
  If \<open>\<alpha> = 1\<close>, $\sigma_\alpha(n)$ is simply the sum of all divisors of \<open>n\<close>. Here, the asymptotics is
  \[\sum_{n\leq x} \sigma_1(n) = \frac{\pi^2}{12} x^2 + O(x\ln x)\ .\]
\<close>
theorem summatory_divisor_sum_asymptotics:
  "sum_upto divisor_sum =o (\<lambda>x. pi\<^sup>2 / 12 * x ^ 2) +o O(\<lambda>x. x * ln x)"
proof -
  define \<zeta> where "\<zeta> = Re (zeta 2)"
  define R1 where "R1 = (\<lambda>x. sum_upto real x - x\<^sup>2 / 2)"
  define R2 where "R2 = (\<lambda>x. sum_upto (\<lambda>d. 1 / d\<^sup>2) x - (\<zeta> - 1 / x))"
  obtain c1 where c1: "c1 > 0" "\<And>x. x \<ge> 1 \<Longrightarrow> \<bar>R1 x\<bar> \<le> c1 * x"
    using zeta_partial_sum_le_neg[of 1] by (auto simp: R1_def)
  obtain c2 where c2: "c2 > 0" "\<And>x. x \<ge> 1 \<Longrightarrow> \<bar>R2 x\<bar> \<le> c2 / x\<^sup>2"
    using zeta_partial_sum_le_pos[of 2]
     by (auto simp: \<zeta>_def R2_def powr_minus field_simps
              simp del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)

  have le: "\<bar>sum_upto divisor_sum x - \<zeta> / 2 * x\<^sup>2\<bar> \<le> c2 / 2 + x / 2 + c1 * x * (ln x + 1)"
    if x: "x \<ge> 1" for x
  proof -
    have div_le: "real (a div b) \<le> x" if "a \<le> x" for a b :: nat
      by (rule order.trans[OF _ that(1)]) auto
 
    have "real (sum_upto divisor_sum x) = sum_upto (dirichlet_prod real (\<lambda>_. 1)) x"
      by (simp add: divisor_sigma_conv_dirichlet_prod [abs_def] 
                    sum_upto_def divisor_sigma_1_left [symmetric])
    also have "\<dots> = sum_upto (\<lambda>n. \<Sum>d | d dvd n. real d) x"
      by (simp add: dirichlet_prod_def)
    also have "\<dots> = (\<Sum>(n, d) \<in> (SIGMA n:{n. n > 0 \<and> real n \<le> x}. {d. d dvd n}). real d)"
      unfolding sum_upto_def by (subst sum.Sigma) auto
    also have "\<dots> = (\<Sum>(d, q) \<in> (SIGMA d:{d. d > 0 \<and> real d \<le> x}. {q. q > 0 \<and> real q \<le> x / d}). real q)"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>(d, q). (d * q, q)" "\<lambda>(n, d). (n div d, d)"])
         (use div_le in \<open>auto simp: field_simps\<close>)
    also have "\<dots> = sum_upto (\<lambda>d. sum_upto real (x / d)) x"
      by (simp add: sum_upto_def sum.Sigma)
    also have "\<dots> = x\<^sup>2 * sum_upto (\<lambda>d. 1 / d\<^sup>2) x / 2 + sum_upto (\<lambda>d. R1 (x / d)) x"
      by (simp add: R1_def sum_upto_def sum.distrib sum_subtractf sum_divide_distrib
                    power_divide sum_distrib_left)
    also have "sum_upto (\<lambda>d. 1 / d\<^sup>2) x = \<zeta> - 1 / x + R2 x"
      by (simp add: R2_def)
    finally have eq: "real (sum_upto divisor_sum x) =
                        x\<^sup>2 * (\<zeta> - 1 / x + R2 x) / 2 + sum_upto (\<lambda>d. R1 (x / real d)) x" .
  
    have "real (sum_upto divisor_sum x) - \<zeta> / 2 * x\<^sup>2 =
            x\<^sup>2 / 2 * R2 x - x / 2 + sum_upto (\<lambda>d. R1 (x / real d)) x" using x
      by (subst eq)
         (simp add: field_simps power2_eq_square del: div_diff div_add
               del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
    also have "\<bar>\<dots>\<bar> \<le> c2 / 2 + x / 2 + c1 * x * (ln x + 1)"
    proof (rule order.trans[OF abs_triangle_ineq] order.trans[OF abs_triangle_ineq4] add_mono)+
      have "\<bar>x\<^sup>2 / 2 * R2 x\<bar> = x\<^sup>2 / 2 * \<bar>R2 x\<bar>"
        using x by (simp add: abs_mult)
      also have "\<dots> \<le> x\<^sup>2 / 2 * (c2 / x\<^sup>2)"
        using x by (intro mult_left_mono c2) auto
      finally show "\<bar>x\<^sup>2 / 2 * R2 x\<bar> \<le> c2 / 2"
        using x by simp
    next
      have "\<bar>sum_upto (\<lambda>d. R1 (x / real d)) x\<bar> \<le> sum_upto (\<lambda>d. \<bar>R1 (x / real d)\<bar>) x"
        unfolding sum_upto_def by (rule sum_abs)
      also have "\<dots> \<le> sum_upto (\<lambda>d. c1 * (x / real d)) x"
        unfolding sum_upto_def by (intro sum_mono c1) auto
      also have "\<dots> = c1 * x * sum_upto (\<lambda>d. 1 / real d) x"
        by (simp add: sum_upto_def sum_distrib_left)
      also have "sum_upto (\<lambda>d. 1 / real d) x = harm (nat \<lfloor>x\<rfloor>)"
        unfolding sum_upto_altdef harm_def by (intro sum.cong) (auto simp: field_simps)
      also have "\<dots> \<le> ln (nat \<lfloor>x\<rfloor>) + 1"
        by (rule harm_le) (use x in \<open>auto simp: le_nat_iff\<close>)
      also have "ln (nat \<lfloor>x\<rfloor>) \<le> ln x" using x by simp
      finally show "\<bar>sum_upto (\<lambda>d. R1 (x / real d)) x\<bar> \<le> c1 * x * (ln x + 1)"
        using c1(1) x by simp
    qed (use x in auto)
    finally show "\<bar>sum_upto divisor_sum x - \<zeta> / 2 * x\<^sup>2\<bar> \<le> c2 / 2 + x / 2 + c1 * x * (ln x + 1)" .
  qed

  have "eventually (\<lambda>x. \<bar>sum_upto divisor_sum x - \<zeta> / 2 * x\<^sup>2\<bar> \<le>
                            c2 / 2 + x / 2 + c1 * x * (ln x + 1)) at_top"
    using eventually_ge_at_top[of 1] by eventually_elim (use le in auto)
  hence "eventually (\<lambda>x. \<bar>sum_upto divisor_sum x - \<zeta> / 2 * x\<^sup>2\<bar> \<le>
                              \<bar>c2 / 2 + x / 2 + c1 * x * (ln x + 1)\<bar>) at_top"
    by eventually_elim linarith
  hence "(\<lambda>x. sum_upto divisor_sum x - \<zeta> / 2 * x\<^sup>2) \<in> O(\<lambda>x. c2 / 2 + x / 2 + c1 * x * (ln x + 1))"
    by (intro landau_o.bigI[of 1]) auto
  also have "(\<lambda>x. c2 / 2 + x / 2 + c1 * x * (ln x + 1)) \<in> O(\<lambda>x. x * ln x)"
    by real_asymp
  finally show ?thesis
    by (subst set_minus_plus [symmetric])
       (simp_all add: fun_diff_def algebra_simps \<zeta>_def zeta_even_numeral)
qed


subsection \<open>Case 2: $\alpha > 0$, $\alpha \neq 1$\<close>

(* TODO: Unify *)
text \<open>
  Next, we consider the case $\alpha > 0$ and $\alpha\neq 1$. We then have:
  \[\sum_{n\leq x} \sigma_\alpha(n) = \frac{\zeta(\alpha + 1)}{\alpha + 1} x^{\alpha + 1} +
       O\left(x^{\text{max}(1,\alpha)}\right)\]
\<close>
theorem summatory_divisor_sigma_asymptotics_pos:
  fixes \<alpha> :: real
  assumes \<alpha>: "\<alpha> > 0" "\<alpha> \<noteq> 1"
  defines "\<zeta> \<equiv> Re (zeta (\<alpha> + 1))"
  shows  "sum_upto (divisor_sigma \<alpha>) =o
            (\<lambda>x. \<zeta> / (\<alpha> + 1) * x powr (\<alpha> + 1)) +o O(\<lambda>x. x powr max 1 \<alpha>)"
proof -
  define R1 where "R1 = (\<lambda>x. sum_upto (\<lambda>d. real d powr \<alpha>) x - x powr (\<alpha> + 1) / (\<alpha> + 1))"
  define R2 where "R2 = (\<lambda>x. sum_upto (\<lambda>d. d powr (-\<alpha> - 1)) x - (\<zeta> - x powr -\<alpha> / \<alpha>))"
  define R3 where "R3 = (\<lambda>x. sum_upto (\<lambda>d. d powr -\<alpha>) x - x powr (1 - \<alpha>) / (1 - \<alpha>))"
  obtain c1 where c1: "c1 > 0" "\<And>x. x \<ge> 1 \<Longrightarrow> \<bar>R1 x\<bar> \<le> c1 * x powr \<alpha>"
    using zeta_partial_sum_le_neg[of \<alpha>] \<alpha> by (auto simp: R1_def add_ac)
  obtain c2 where c2: "c2 > 0" "\<And>x. x \<ge> 1 \<Longrightarrow> \<bar>R2 x\<bar> \<le> c2 * x powr (-\<alpha>-1)"
    using zeta_partial_sum_le_pos[of "\<alpha> + 1"] \<alpha> by (auto simp: \<zeta>_def R2_def)
  obtain c3 where c3: "c3 > 0" "\<And>x. x \<ge> 1 \<Longrightarrow> \<bar>R3 x\<bar> \<le> c3"
    using zeta_partial_sum_le_pos'[of "\<alpha>"] \<alpha> by (auto simp: R3_def)
  define ub :: "real \<Rightarrow> real" where
    "ub = (\<lambda>x. x / (\<alpha> * (\<alpha> + 1)) + c2 / (\<alpha> + 1) + c1 * (1 / (1 - \<alpha>) * x + c3 * x powr \<alpha>))"

  have le: "\<bar>sum_upto (divisor_sigma \<alpha>) x - \<zeta> / (\<alpha> + 1) * x powr (\<alpha> + 1)\<bar> \<le> ub x"
    if x: "x \<ge> 1" for x
  proof -
    have div_le: "real (a div b) \<le> x" if "a \<le> x" for a b :: nat
      by (rule order.trans[OF _ that(1)]) auto
 
    have "sum_upto (divisor_sigma \<alpha>) x =
            sum_upto (dirichlet_prod (\<lambda>n. real n powr \<alpha>) (\<lambda>_. 1)) x"
      by (simp add: divisor_sigma_conv_dirichlet_prod [abs_def] 
                    sum_upto_def divisor_sigma_1_left [symmetric])
    also have "\<dots> = sum_upto (\<lambda>n. \<Sum>d | d dvd n. real d powr \<alpha>) x"
      by (simp add: dirichlet_prod_def)
    also have "\<dots> = (\<Sum>(n, d) \<in> (SIGMA n:{n. n > 0 \<and> real n \<le> x}. {d. d dvd n}). real d powr \<alpha>)"
      unfolding sum_upto_def by (subst sum.Sigma) auto
    also have "\<dots> = (\<Sum>(d, q) \<in> (SIGMA d:{d. d > 0 \<and> real d \<le> x}. {q. q > 0 \<and> real q \<le> x / d}). real q powr \<alpha>)"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>(d, q). (d * q, q)" "\<lambda>(n, d). (n div d, d)"])
         (use div_le in \<open>auto simp: field_simps\<close>)
    also have "\<dots> = sum_upto (\<lambda>d. sum_upto (\<lambda>q. q powr \<alpha>) (x / d)) x"
      by (simp add: sum_upto_def sum.Sigma)
    also have "\<dots> = x powr (\<alpha> + 1) * sum_upto (\<lambda>d. 1 / d powr (\<alpha> + 1)) x / (\<alpha> + 1) +
                    sum_upto (\<lambda>d. R1 (x / d)) x"
      by (simp add: R1_def sum_upto_def sum.distrib sum_subtractf sum_divide_distrib
                    powr_divide sum_distrib_left)
    also have "sum_upto (\<lambda>d. 1 / d powr (\<alpha> + 1)) x = \<zeta> - x powr -\<alpha> / \<alpha> + R2 x"
      by (simp add: R2_def powr_minus field_simps powr_diff powr_add)
    finally have eq: "sum_upto (divisor_sigma \<alpha>) x =
       x powr (\<alpha> + 1) * (\<zeta> - x powr -\<alpha> / \<alpha> + R2 x) / (\<alpha> + 1) + sum_upto (\<lambda>d. R1 (x / d)) x" .
  
    have "sum_upto (divisor_sigma \<alpha>) x - \<zeta> / (\<alpha> + 1) * x powr (\<alpha> + 1) =
            -x / (\<alpha> * (\<alpha> + 1)) + x powr (\<alpha> + 1) / (\<alpha> + 1) * R2 x + sum_upto (\<lambda>d. R1 (x / d)) x"
      using x \<alpha>
      by (subst eq, simp add: divide_simps
                         del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
         (simp add: field_simps power2_eq_square powr_add powr_minus del: div_diff div_add
               del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
    also have "\<bar>\<dots>\<bar> \<le> ub x" unfolding ub_def
    proof (rule order.trans[OF abs_triangle_ineq] order.trans[OF abs_triangle_ineq4] add_mono)+
      have "\<bar>x powr (\<alpha> + 1) / (\<alpha> + 1) * R2 x\<bar> = x powr (\<alpha> + 1) / (\<alpha> + 1) * \<bar>R2 x\<bar>"
        using x \<alpha> by (simp add: abs_mult)
      also have "\<dots> \<le> x powr (\<alpha> + 1) / (\<alpha> + 1) * (c2 * x powr (-\<alpha>-1))"
        using x \<alpha> by (intro mult_left_mono c2) auto
      also have "\<dots> = c2 / (\<alpha> + 1)"
        using \<alpha> x by (simp add: field_simps powr_diff powr_minus powr_add)
      finally show "\<bar>x powr (\<alpha> + 1) / (\<alpha> + 1) * R2 x\<bar> \<le> c2 / (\<alpha> + 1)" .
    next
      have "\<bar>sum_upto (\<lambda>d. R1 (x / real d)) x\<bar> \<le> sum_upto (\<lambda>d. \<bar>R1 (x / real d)\<bar>) x"
        unfolding sum_upto_def by (rule sum_abs)
      also have "\<dots> \<le> sum_upto (\<lambda>d. c1 * (x / real d) powr \<alpha>) x"
        unfolding sum_upto_def by (intro sum_mono c1) auto
      also have "\<dots> = c1 * x powr \<alpha> * sum_upto (\<lambda>d. 1 / real d powr \<alpha>) x"
        by (simp add: sum_upto_def sum_distrib_left powr_divide)
      also have "sum_upto (\<lambda>d. 1 / real d powr \<alpha>) x = x powr (1-\<alpha>) / (1-\<alpha>) + R3 x"
        using x by (simp add: R3_def powr_minus field_simps)
      also have "c1 * x powr \<alpha> * (x powr (1 - \<alpha>) / (1 - \<alpha>) + R3 x) =
                   c1 / (1 - \<alpha>) * x + c1 * x powr \<alpha> * R3 x"
        using x by (simp add: powr_diff divide_simps
                    del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
                   (simp add: field_simps)
      also have "c1 * x powr \<alpha> * R3 x \<le> c1 * x powr \<alpha> * c3"
        using x c1(1) c3(2)[of x] by (intro mult_left_mono) auto
      finally show "\<bar>sum_upto (\<lambda>d. R1 (x / d)) x\<bar> \<le> c1 * (1 / (1 - \<alpha>) * x + c3 * x powr \<alpha>)"
        by (simp add: field_simps)
    qed (use \<alpha> x in simp_all)
    finally show "\<bar>sum_upto (divisor_sigma \<alpha>) x - \<zeta> / (\<alpha> + 1) * x powr (\<alpha> + 1)\<bar> \<le> ub x" .
  qed

  have "eventually (\<lambda>x. \<bar>sum_upto (divisor_sigma \<alpha>) x - \<zeta> / (\<alpha>+1) * x powr (\<alpha>+1)\<bar> \<le> ub x) at_top"
    using eventually_ge_at_top[of 1] by eventually_elim (use le in auto)
  hence "eventually (\<lambda>x. \<bar>sum_upto (divisor_sigma \<alpha>) x - \<zeta>/(\<alpha>+1) * x powr (\<alpha>+1)\<bar> \<le> \<bar>ub x\<bar>) at_top"
    by eventually_elim linarith
  hence "(\<lambda>x. sum_upto (divisor_sigma \<alpha>) x - \<zeta>/(\<alpha>+1) * x powr (\<alpha>+1)) \<in> O(ub)"
    by (intro landau_o.bigI[of 1]) auto
  also have "ub \<in> O(\<lambda>x. x powr max 1 \<alpha>)"
    using \<alpha> unfolding ub_def by (cases "\<alpha> \<ge> 1"; real_asymp)
  finally show ?thesis
    by (subst set_minus_plus [symmetric])
       (simp_all add: fun_diff_def algebra_simps \<zeta>_def zeta_even_numeral)
qed


subsection \<open>Case 3: $\alpha < 0$\<close>

text \<open>
  Last, we consider the case of a negative exponent. We have for $\alpha > 0$:
  \[\sum_{n\leq x} \sigma_{-\alpha}(n) = \zeta(\alpha + 1)x + O(R(x))\]
  where $R(x) = \ln x$ if $\alpha = 1$ and $R(x) = x^{\text{max}(0, 1-\alpha)}$ otherwise.
\<close>
theorem summatory_divisor_sigma_asymptotics_neg:
  fixes \<alpha> :: real
  assumes \<alpha>: "\<alpha> > 0"
  defines "\<delta> \<equiv> max 0 (1 - \<alpha>)"
  defines "\<zeta> \<equiv> Re (zeta (\<alpha> + 1))"
  shows  "sum_upto (divisor_sigma (-\<alpha>)) =o (if \<alpha> = 1 then (\<lambda>x. pi\<^sup>2/6 * x) +o O(ln)
                                                     else (\<lambda>x. \<zeta> * x) +o O(\<lambda>x. x powr \<delta>))"
proof -
  define Ra where "Ra = (\<lambda>x. -sum_upto (\<lambda>d. d powr (-\<alpha>) * frac (x / d)) x)"
  define R1 where "R1 = (\<lambda>x. sum_upto (\<lambda>d. real d powr (-\<alpha>)) x - (x powr (1 - \<alpha>) / (1 - \<alpha>) + \<zeta>))"
  define R2 where "R2 = (\<lambda>x. sum_upto (\<lambda>d. d powr (-\<alpha> - 1)) x - (\<zeta> - x powr -\<alpha> / \<alpha>))"
  define R3 where "R3 = (\<lambda>x. sum_upto (\<lambda>d. d powr -\<alpha>) x - x powr (1 - \<alpha>) / (1 - \<alpha>))"
  obtain c2 where c2: "c2 > 0" "\<And>x. x \<ge> 1 \<Longrightarrow> \<bar>R2 x\<bar> \<le> c2 * x powr (-\<alpha>-1)"
    using zeta_partial_sum_le_pos[of "\<alpha> + 1"] \<alpha> by (auto simp: \<zeta>_def R2_def)
  define ub :: "real \<Rightarrow> real" where
    "ub = (\<lambda>x. x powr (1 - \<alpha>) / \<alpha> + c2 * x powr - \<alpha> + \<bar>Ra x\<bar>)"

  have le: "\<bar>sum_upto (divisor_sigma (-\<alpha>)) x - \<zeta> * x\<bar> \<le> ub x"
    if x: "x \<ge> 1" for x
  proof -
    have div_le: "real (a div b) \<le> x" if "a \<le> x" for a b :: nat
      by (rule order.trans[OF _ that(1)]) auto
 
    have "sum_upto (divisor_sigma (-\<alpha>)) x =
            sum_upto (dirichlet_prod (\<lambda>n. real n powr (-\<alpha>)) (\<lambda>_. 1)) x"
      by (simp add: divisor_sigma_conv_dirichlet_prod [abs_def] 
                    sum_upto_def divisor_sigma_1_left [symmetric])
    also have "\<dots> = sum_upto (\<lambda>n. \<Sum>d | d dvd n. real d powr (-\<alpha>)) x"
      by (simp add: dirichlet_prod_def)
    also have "\<dots> = (\<Sum>(n, d) \<in> (SIGMA n:{n. n > 0 \<and> real n \<le> x}. {d. d dvd n}). real d powr (-\<alpha>))"
      unfolding sum_upto_def by (subst sum.Sigma) auto
    also have "\<dots> = (\<Sum>(d, q) \<in> (SIGMA d:{d. d > 0 \<and> real d \<le> x}. {q. q > 0 \<and> real q \<le> x / d}).
                         real d powr (-\<alpha>))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>(d, q). (d * q, d)" "\<lambda>(n, d). (d, n div d)"])
         (use div_le in \<open>auto simp: field_simps dest: dvd_imp_le\<close>)
    also have "\<dots> = sum_upto (\<lambda>d. sum_upto (\<lambda>q. d powr (-\<alpha>)) (x / d)) x"
      by (simp add: sum_upto_def sum.Sigma [symmetric])
    also have "\<dots> = sum_upto (\<lambda>d. d powr (-\<alpha>) * \<lfloor>x / d\<rfloor>) x"
      using x by (simp add: sum_upto_altdef mult_ac)
    also have "\<dots> = x * sum_upto (\<lambda>d. d powr (-\<alpha>) / d) x + Ra x"
      by (simp add: frac_def sum_distrib_left sum_distrib_right
                    sum_subtractf sum_upto_def algebra_simps Ra_def)
    also have "sum_upto (\<lambda>d. d powr (-\<alpha>) / d) x = sum_upto (\<lambda>d. d powr (-\<alpha> - 1)) x"
      by (simp add: powr_diff powr_minus powr_add field_simps)
    also have "\<dots> = \<zeta> - x powr - \<alpha> / \<alpha> + R2 x"
      by (simp add: R2_def)
    finally have "sum_upto (divisor_sigma (-\<alpha>)) x - \<zeta> * x = -(x powr (1 - \<alpha>) / \<alpha>) + x * R2 x + Ra x"
      using x \<alpha> by (simp add: powr_diff powr_minus field_simps)

    also have "\<bar>\<dots>\<bar> \<le> x powr (1 - \<alpha>) / \<alpha> + c2 * x powr -\<alpha> + \<bar>Ra x\<bar>"
    proof (rule order.trans[OF abs_triangle_ineq] order.trans[OF abs_triangle_ineq4] add_mono)+
      from x have "\<bar>x * R2 x\<bar> \<le> x * \<bar>R2 x\<bar>"
        by (simp add: abs_mult)
      also from x have "\<dots> \<le> x * (c2 * x powr (-\<alpha> - 1))"
        by (intro mult_left_mono c2) auto
      also have "\<dots> = c2 * x powr -\<alpha>"
        using x by (simp add: field_simps powr_minus powr_diff)
      finally show "\<bar>x * R2 x\<bar> \<le> \<dots>" .
    qed (use x \<alpha> in auto)
    finally show "\<bar>sum_upto (divisor_sigma (- \<alpha>)) x - \<zeta> * x\<bar> \<le> ub x"
      by (simp add: ub_def)
  qed

  have "eventually (\<lambda>x. \<bar>sum_upto (divisor_sigma (-\<alpha>)) x - \<zeta> * x\<bar> \<le> ub x) at_top"
    using eventually_ge_at_top[of 1] by eventually_elim (use le in auto)
  hence "eventually (\<lambda>x. \<bar>sum_upto (divisor_sigma (-\<alpha>)) x - \<zeta> * x\<bar> \<le> \<bar>ub x\<bar>) at_top"
    by eventually_elim linarith
  hence bigo: "(\<lambda>x. sum_upto (divisor_sigma (-\<alpha>)) x - \<zeta> * x) \<in> O(ub)"
    by (intro landau_o.bigI[of 1]) auto

  define ub' :: "real \<Rightarrow> real" where "ub' = sum_upto (\<lambda>n. real n powr - \<alpha>)"
  have "\<bar>Ra x\<bar> \<le> \<bar>ub' x\<bar>" if "x \<ge> 1" for x
  proof -
    have "\<bar>Ra x\<bar> \<le> sum_upto (\<lambda>n. \<bar>real n powr -\<alpha> * frac (x / n)\<bar>) x"
      unfolding Ra_def abs_minus sum_upto_def by (rule sum_abs)
    also have "\<dots> \<le> sum_upto (\<lambda>n. real n powr -\<alpha> * 1) x"
      unfolding abs_mult sum_upto_def
      by (intro sum_mono mult_mono) (auto intro: less_imp_le[OF frac_lt_1])
    finally show ?thesis by (simp add: ub'_def)
  qed
  hence "Ra \<in> O(ub')"
    by (intro bigoI[of _ 1] eventually_mono[OF eventually_ge_at_top[of 1]]) auto
  also have "ub' \<in> O(\<lambda>x. if \<alpha> = 1 then ln x else x powr \<delta>)"
  proof (cases "\<alpha> = 1")
    case [simp]: True
    have "sum_upto (\<lambda>n. 1 / n) \<in> O(ln)"
      by (intro asymp_equiv_imp_bigo harm_asymp_equiv)
    thus ?thesis by (simp add: ub'_def powr_minus field_simps)
  next
    case False
    have "sum_upto (\<lambda>n. real n powr - \<alpha>) \<in> O(\<lambda>x. x powr \<delta>)"
      using assms False unfolding \<delta>_def by (intro zeta_partial_sum_pos_bigtheta bigthetaD1)
    thus ?thesis
      using zeta_partial_sum_neg_asymp_equiv[of \<alpha>] \<alpha> False by (simp add: ub'_def)
  qed
  finally have Ra_bigo: "Ra \<in> \<dots>" .

  show ?thesis
  proof (cases "\<alpha> = 1")
    case [simp]: True
    with Ra_bigo have Ra: "(\<lambda>x. \<bar>Ra x\<bar>) \<in> O(ln)" by simp
    note bigo
    also have "ub \<in> O(\<lambda>x. ln x)"
      unfolding ub_def by (intro sum_in_bigo Ra) real_asymp+
    finally have "sum_upto (divisor_sigma (-\<alpha>)) =o (\<lambda>x. (pi\<^sup>2 / 6) * x) +o O(ln)"
      by (subst set_minus_plus [symmetric])
         (simp_all add: fun_diff_def algebra_simps \<zeta>_def zeta_even_numeral)
    thus ?thesis by (simp only: True refl if_True)
  next
    case False
    with Ra_bigo have Ra: "(\<lambda>x. \<bar>Ra x\<bar>) \<in> O(\<lambda>x. x powr \<delta>)" by simp
    have *: "(\<lambda>x. x powr (1 - \<alpha>) / \<alpha>) \<in> O(\<lambda>x. x powr \<delta>)"
            "(\<lambda>x. c2 * x powr - \<alpha>) \<in> O(\<lambda>x. x powr \<delta>)"
      unfolding \<delta>_def using \<alpha> False by (cases "\<alpha> > 1"; real_asymp)+

    note bigo
    also have "ub \<in> O(\<lambda>x. x powr \<delta>)"
      unfolding ub_def using \<alpha> False by (intro sum_in_bigo Ra *)
    finally have "sum_upto (divisor_sigma (-\<alpha>)) =o (\<lambda>x. \<zeta> * x) +o O(\<lambda>x. x powr \<delta>)"
      by (subst set_minus_plus [symmetric])
         (simp_all add: fun_diff_def algebra_simps \<zeta>_def zeta_even_numeral)
    thus ?thesis by (simp only: False refl if_False)
  qed
qed

end