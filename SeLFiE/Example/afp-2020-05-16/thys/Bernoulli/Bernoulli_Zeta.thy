section \<open>Bernoulli numbers and the zeta function at positive integers\<close>
theory Bernoulli_Zeta
imports 
  "HOL-Complex_Analysis.Complex_Analysis"
  Bernoulli_FPS
begin

(* TODO: Move *)
lemma joinpaths_cong: "f = f' \<Longrightarrow> g = g' \<Longrightarrow> f +++ g = f' +++ g'"
  by simp

lemma linepath_cong: "a = a' \<Longrightarrow> b = b' \<Longrightarrow> linepath a b = linepath a' b'"
  by simp

text \<open>
  The analytic continuation of the exponential generating function of the Bernoulli numbers
  is $\frac{z}{e^z - 1}$, which has simple poles at all $2ki\pi$ for $k\in\mathbb{Z}\setminus\{0\}$.
  We will need the residue at these poles:
\<close>
lemma residue_bernoulli:
  assumes "n \<noteq> 0"
  shows   "residue (\<lambda>z. 1 / (z ^ m * (exp z - 1))) (2 * pi * real_of_int n * \<i>) = 
             1 / (2 * pi * real_of_int n * \<i>) ^ m"
proof -
  have "residue (\<lambda>z. (1 / z ^ m) / (exp z - 1)) (2 * pi * real_of_int n * \<i>) =
          1 / (2 * pi * real_of_int n * \<i>) ^ m / 1"
    using exp_integer_2pi[of "real_of_int n"] and assms
    by (rule_tac residue_simple_pole_deriv[where s="-{0}"])
       (auto intro!: holomorphic_intros derivative_eq_intros connected_open_delete_finite 
             simp add: mult_ac connected_punctured_universe)
  thus ?thesis by (simp add: divide_simps)
qed

text \<open>
  At positive integers greater than 1, the Riemann zeta function is simply the infinite
  sum $\zeta(n) = \sum_{k=1}^\infty k^{-n}$. For even $n$, this quantity can also be
  expressed in terms of Bernoulli numbers.

  To show this, we employ a similar strategy as in the meromorphic asymptotics approach:
  We apply the Residue Theorem to the exponential generating function of the Bernoulli numbers:
  \[\sum_{n=0}^\infty \frac{B_n}{n!} z^n = \frac{z}{e^z - 1}\]
  Recall that this function has poles at $2ki\pi$ for $k\in\mathbb{Z}\setminus\{0\}$.
  In the meromorphic asymptotics case, we integrated along a circle of radius $3i\pi$ in order
  to get the dominant singularities $2i\pi$ and $-2i\pi$. Now, however, we will not use a 
  fixed integration path, but we let the integration path become bigger and bigger. 
  Because the integrand decays relatively quickly if $n > 1$, the integral vanishes in the limit 
  and we obtain not just an asymptotic formula, but an exact representation of $B_n$ as an 
  infinite sum.

  For odd $n$, we have $B_n = 0$, but for even $n$, the residues at $2ki\pi$ and $-2ki\pi$ 
  combine nicely to $2\cdot(-2k\pi)^{-n}$, and after some simplification we get the formula
  for $B_n$.

  Another difference to the meromorphic asymptotics is that we now use a rectangle instead
  of a circle as the integration path. For the asymptotics, only a big-oh bound was needed
  for the integral over one fixed integration path, and the circular path was very convenient.
  However, now we need to explicitly bound the integral for a whole sequence of integration paths
  that grow in size, and bounding $e^z - 1$ for $z$ on a circle is very tedious. On a rectangle,
  this term can be bounded much more easily. Still, we have to do this separately for all four
  edges of the rectangle, which will be a bit tedious.
\<close>
theorem nat_even_power_sums_complex:
  assumes n': "n' > 0"
  shows   "(\<lambda>k. 1 / of_nat (Suc k) ^ (2*n') :: complex) sums
             of_real ((-1) ^ Suc n' * bernoulli (2*n') * (2 * pi) ^ (2 * n') / (2 * fact (2*n')))"
proof -
  define n where "n = 2 * n'"
  from n' have n: "n \<ge> 2" "even n" by (auto simp: n_def)
  define zeta :: complex where "zeta = (\<Sum>k. 1 / of_nat (Suc k) ^ n)"

  have "summable (\<lambda>k. 1 / of_nat (Suc k) ^ n :: complex)"
    using inverse_power_summable[of n] n
    by (subst summable_Suc_iff) (simp add: divide_simps)
  hence "(\<lambda>k. \<Sum>i<k. 1 / of_nat (Suc i) ^ n) \<longlonglongrightarrow> zeta"
    by (subst (asm) summable_sums_iff) (simp add: sums_def zeta_def)
  also have "(\<lambda>k. \<Sum>i<k. 1 / of_nat (Suc i) ^ n) = (\<lambda>k. \<Sum>i\<in>{0<..k}. 1 / of_nat i ^ n)"
    by (intro ext sum.reindex_bij_witness[of _ "\<lambda>n. n - 1" Suc]) auto
  finally have zeta_limit: "(\<lambda>k. \<Sum>i\<in>{0<..k}. 1 / of_nat i ^ n) \<longlonglongrightarrow> zeta" .

  \<comment> \<open>This is the exponential generating function of the Bernoulli numbers.\<close>
  define f where "f = (\<lambda>z::complex. if z = 0 then 1 else z / (exp z - 1))"

  \<comment> \<open>We will integrate over this function, since its residue at the origin
      is the $n$-th coefficient of @{term f}. Note that it has singularities
      at all points $2ik\pi$ for $k\in\mathbb{Z}$.\<close>
  define g where "g = (\<lambda>z::complex. 1 / (z ^ n * (exp z - 1)))"

  \<comment> \<open>We integrate along a rectangle of width $2m$ and height $2(2m+1)\pi$
      with its centre at the origin. The benefit of the rectangular path is that
      it is easier to bound the value of the exponential appearing in the integrand.
      The horizontal lines of the rectangle are always right in the middle between 
      two adjacent singularities.\<close>
  define \<gamma> :: "nat \<Rightarrow> real \<Rightarrow> complex" 
    where "\<gamma> = (\<lambda>m. rectpath (-real m - real (2*m+1)*pi*\<i>) (real m + real (2*m+1)*pi*\<i>))"

  \<comment> \<open>This set is a convex open enclosing set the contains our path.\<close>
  define A where "A = (\<lambda>m::nat. box (-(real m+1) - (2*m+2)*pi*\<i>) (real m+1 + (2*m+2)*pi*\<i>))"

  \<comment> \<open>These are all the singularities in the enclosing inside the path
      (and also inside @{term A}).\<close>
  define S where "S = (\<lambda>m::nat. (\<lambda>n. 2 * pi * of_int n * \<i>) ` {-m..m})"

  \<comment> \<open>Any singularity in @{term A} is of the form $2ki\pi$ where $|k| \leq m$.\<close>
  have int_bound: "k \<in> {-int m..int m}" if "2 * pi * k * \<i> \<in> A m" for k m
  proof -
    from that have "(-real (Suc m)) * (2 * pi) < real_of_int k * (2 * pi) \<and> 
                        real (Suc m) * (2 * pi) > real_of_int k * (2 * pi)"
      by (auto simp: A_def in_box_complex_iff algebra_simps)
    hence "-real (Suc m) < real_of_int k \<and> real_of_int k < real (Suc m)"
      by simp
    also have "-real (Suc m) = real_of_int (-int (Suc m))" by simp
    also have "real (Suc m) = real_of_int (int (Suc m))" by simp
    also have "real_of_int (- int (Suc m)) < real_of_int k \<and> 
                 real_of_int k < real_of_int (int (Suc m)) \<longleftrightarrow> k \<in> {-int m..int m}" 
      by (subst of_int_less_iff) auto
    finally show "k \<in> {-int m..int m}" .
  qed

  have zeros: "\<exists>k\<in>{-int m..int m}. z = 2 * pi * of_int k * \<i>" if "z \<in> A m" "exp z = 1" for z m
  proof -
    from that(2) obtain k where z_eq: "z = 2 * pi * of_int k * \<i>"
      unfolding exp_eq_1 by (auto simp: complex_eq_iff)
    with int_bound[of k] and that(1) show ?thesis by auto
  qed
  have zeros': "z ^ n * (exp z - 1) \<noteq> 0" if "z \<in> A m - S m" for z m
    using zeros[of z] that by (auto simp: S_def)

  \<comment> \<open>The singularities all lie strictly inside the integration path.\<close>
  have subset: "S m \<subseteq> box (-real m - real(2*m+1)*pi*\<i>) (real m + real(2*m+1)*pi*\<i>)" if "m > 0" for m
  proof (rule, goal_cases)
    case (1 z)
    then obtain k :: int where k: "k \<in> {-int m..int m}" "z = 2 * pi * k * \<i>"
      unfolding S_def by blast
    have "2 * pi * -m + -pi < 2 * pi * k + 0"
      using k by (intro add_le_less_mono mult_left_mono) auto
    moreover have "2 * pi * k + 0 < 2 * pi * m + pi"
      using k by (intro add_le_less_mono mult_left_mono) auto
    ultimately show ?case using k \<open>m > 0\<close>
      by (auto simp: A_def in_box_complex_iff algebra_simps)
  qed
  from n and zeros' have holo: "g holomorphic_on A m - S m" for m
    unfolding g_def by (intro holomorphic_intros) auto

  \<comment> \<open>The integration path lies completely inside $A$ and does not cross
      any singularities.\<close>
  have path_subset: "path_image (\<gamma> m) \<subseteq> A m - S m" if "m > 0" for m
  proof -
    have "path_image (\<gamma> m) \<subseteq> cbox (-real m - (2 * m + 1) * pi * \<i>) (real m + (2 * m + 1) * pi * \<i>)"
      unfolding \<gamma>_def by (rule path_image_rectpath_subset_cbox) auto
    also have "\<dots> \<subseteq> A m" unfolding A_def
      by (subst subset_box_complex) auto
    finally have "path_image (\<gamma> m) \<subseteq> A m" .
    moreover have "path_image (\<gamma> m) \<inter> S m = {}"
    proof safe
      fix z assume z: "z \<in> path_image (\<gamma> m)" "z \<in> S m"
      from this(2) obtain k :: int where k: "z = 2 * pi * k * \<i>"
        by (auto simp: S_def)
      hence [simp]: "Re z = 0" by simp
      from z(1) have "\<bar>Im z\<bar> = of_int (2*m+1) * pi"
        using \<open>m > 0\<close> by (auto simp: \<gamma>_def path_image_rectpath)
      also have "\<bar>Im z\<bar> = of_int (2 * \<bar>k\<bar>) * pi"
        by (simp add: k abs_mult)
      finally have "2 * \<bar>k\<bar> = 2 * m + 1"
        by (subst (asm) mult_cancel_right, subst (asm) of_int_eq_iff) simp
      hence False by presburger
      thus "z \<in> {}" ..
    qed
    ultimately show "path_image (\<gamma> m) \<subseteq> A m - S m" by blast
  qed

  \<comment> \<open>We now obtain a closed form for the Bernoulli numbers using the integral.\<close>
  have eq: "(\<Sum>x\<in>{0<..m}. 1 / of_nat x ^ n) =
              contour_integral (\<gamma> m) g * (2 * pi * \<i>) ^ n / (4 * pi * \<i>) -
              complex_of_real (bernoulli n / fact n) * (2 * pi * \<i>) ^ n / 2" 
    if m: "m > 0" for m
  proof -
    \<comment> \<open>We relate the formal power series of the Bernoulli numbers to the
        corresponding complex function.\<close>
    have "subdegree (fps_exp 1 - 1 :: complex fps) = 1"
      by (intro subdegreeI) auto
    hence expansion: "f has_fps_expansion bernoulli_fps" 
      unfolding f_def bernoulli_fps_def by (auto intro!: fps_expansion_intros)

    \<comment> \<open>We use the Residue Theorem to explicitly compute the integral.\<close>
    have "contour_integral (\<gamma> m) g =
             2 * pi * \<i> * (\<Sum>z\<in>S m. winding_number (\<gamma> m) z * residue g z)"
    proof (rule Residue_theorem)
      have "cbox (-real m - (2 * m + 1) * pi * \<i>) (real m + (2 * m + 1) * pi * \<i>) \<subseteq> A m"
        unfolding A_def by (subst subset_box_complex) simp_all
      thus "\<forall>z. z \<notin> A m \<longrightarrow> winding_number (\<gamma> m) z = 0" unfolding \<gamma>_def
        by (intro winding_number_rectpath_outside allI impI) auto
    qed (insert holo path_subset m, auto simp: \<gamma>_def A_def S_def intro: convex_connected)
    \<comment> \<open>Clearly, all the winding numbers are 1\<close>
    also have "winding_number (\<gamma> m) z = 1" if "z \<in> S m" for z
      unfolding \<gamma>_def using subset[of m] that m by (subst winding_number_rectpath) blast+
    hence "(\<Sum>z\<in>S m. winding_number (\<gamma> m) z * residue g z) = (\<Sum>z\<in>S m. residue g z)"
      by (intro sum.cong) simp_all
    also have "\<dots> = (\<Sum>k=-int m..int m. residue g (2 * pi * of_int k * \<i>))"
      unfolding S_def by (subst sum.reindex) (auto simp: inj_on_def o_def)
    also have "{-int m..int m} = insert 0 ({-int m..int m}-{0})"
      by auto
    also have "(\<Sum>k\<in>\<dots>. residue g (2 * pi * of_int k * \<i>)) = 
                 residue g 0 + (\<Sum>k\<in>{-int m..m}-{0}. residue g (2 * pi * of_int k * \<i>))"
      by (subst sum.insert) auto
    \<comment> \<open>The residue at the origin is just the $n$-th coefficient of $f$.\<close>
    also have "residue g 0 = residue (\<lambda>z. f z / z ^ Suc n) 0" unfolding f_def g_def
      by (intro residue_cong eventually_mono[OF eventually_at_ball[of 1]]) auto
    also have "\<dots> = fps_nth bernoulli_fps n"
      by (rule residue_fps_expansion_over_power_at_0 [OF expansion])
    also have "\<dots> = of_real (bernoulli n / fact n)" 
      by simp
    also have "(\<Sum>k\<in>{-int m..m}-{0}. residue g (2 * pi * of_int k * \<i>)) = 
                 (\<Sum>k\<in>{-int m..m}-{0}. 1 / of_int k ^ n) / (2 * pi * \<i>) ^ n"
    proof (subst sum_divide_distrib, intro refl sum.cong, goal_cases)
      case (1 k)
      hence *: "residue g (2 * pi * of_int k * \<i>) = 1 / (2 * complex_of_real pi * of_int k * \<i>) ^ n"
        unfolding g_def by (subst residue_bernoulli) auto
      thus ?case using 1 by (subst *) (simp add: divide_simps power_mult_distrib)
    qed
    also have "(\<Sum>k\<in>{-int m..m}-{0}. 1 / of_int k ^ n) =
                 (\<Sum>(a,b)\<in>{0<..m}\<times>{-1,1::int}. 1 / of_int (int a) ^ n :: complex)" using n
      by (intro sum.reindex_bij_witness[of _ "\<lambda>k. snd k * int (fst k)" "\<lambda>k. (nat \<bar>k\<bar>,sgn k)"])
         (auto split: if_splits simp: abs_if)
    also have "\<dots> = (\<Sum>x\<in>{0<..m}. 2 / of_nat x ^ n)"
      using n by (subst sum.Sigma [symmetric]) auto
    also have "\<dots> = (\<Sum>x\<in>{0<..m}. 1 / of_nat x ^ n) * 2"
      by (simp add: sum_distrib_right)
    finally show ?thesis 
      by (simp add: field_simps)
  qed

  \<comment> \<open>The ugly part: We have to prove a bound on the integral by splitting
      it into four integrals over lines and bounding each part separately.\<close>
  have "eventually (\<lambda>m. norm (contour_integral (\<gamma> m) g) \<le> 
          ((4 + 12 * pi) + 6 * pi / m) / real m ^ (n - 1)) sequentially"
    using eventually_gt_at_top[of "1::nat"]
  proof eventually_elim
    case (elim m)
    let ?c = "(2*m+1) * pi * \<i>"
    define I where "I = (\<lambda>p1 p2. contour_integral (linepath p1 p2) g)"
    define p1 p2 p3 p4 where "p1 = -real m - ?c" and "p2 = real m - ?c" 
                         and "p3 = real m + ?c" and "p4 = -real m + ?c"
    have eq: "\<gamma> m = linepath p1 p2 +++ linepath p2 p3 +++ linepath p3 p4 +++ linepath p4 p1"
      (is "\<gamma> m = ?\<gamma>'") unfolding \<gamma>_def rectpath_def Let_def
      by (intro joinpaths_cong linepath_cong) 
         (simp_all add: p1_def p2_def p3_def p4_def complex_eq_iff)
    have integrable: "g contour_integrable_on \<gamma> m" using elim
      by (intro contour_integrable_holomorphic_simple[OF holo _ _ path_subset])
         (auto simp: \<gamma>_def A_def S_def intro!: finite_imp_closed)
    have "norm (contour_integral (\<gamma> m) g) = norm (I p1 p2 + I p2 p3 + I p3 p4 + I p4 p1)"
      unfolding I_def by (insert integrable, unfold eq)
                         (subst contour_integral_join; (force simp: add_ac)?)+
    also have "\<dots> \<le> norm (I p1 p2) + norm (I p2 p3) + norm (I p3 p4) + norm (I p4 p1)"
      by (intro norm_triangle_mono order.refl)

    also have "norm (I p1 p2) \<le> 1 / real m ^ n * norm (p2 - p1)" (is "_ \<le> ?B1 * _")
      unfolding I_def
    proof (intro contour_integral_bound_linepath)
      fix z assume z: "z \<in> closed_segment p1 p2"
      define a where "a = Re z"
      from z have z: "z = a - (2*m+1) * pi * \<i>"
        by (subst (asm) closed_segment_same_Im)
           (auto simp: p1_def p2_def complex_eq_iff a_def)
      have "real m * 1 \<le> (2*m+1) * pi"
        using pi_ge_two by (intro mult_mono) auto
      also have "(2*m+1) * pi = \<bar>Im z\<bar>" by (simp add: z)
      also have "\<bar>Im z\<bar> \<le> norm z" by (rule abs_Im_le_cmod)
      finally have "norm z \<ge> m" by simp
      moreover {
        have "exp z - 1 = -of_real (exp a + 1)" using exp_integer_2pi_plus1[of m]
          by (simp add: z exp_diff algebra_simps exp_of_real)
        also have "norm \<dots> \<ge> 1"
          unfolding norm_minus_cancel norm_of_real by simp
        finally have "norm (exp z - 1) \<ge> 1" .
      }
      ultimately have "norm z ^ n * norm (exp z - 1) \<ge> real m ^ n * 1"
        by (intro mult_mono power_mono) auto
      thus "norm (g z) \<le> 1 / real m ^ n" using elim
        by (simp add: g_def divide_simps norm_divide norm_mult norm_power mult_less_0_iff)
    qed (insert integrable, auto simp: eq)
    also have "norm (p2 - p1) = 2 * m" by (simp add: p2_def p1_def)

    also have "norm (I p3 p4) \<le> 1 / real m ^ n * norm (p4 - p3)" (is "_ \<le> ?B3 * _")
      unfolding I_def
    proof (intro contour_integral_bound_linepath)
      fix z assume z: "z \<in> closed_segment p3 p4"
      define a where "a = Re z"
      from z have z: "z = a + (2*m+1) * pi * \<i>"
        by (subst (asm) closed_segment_same_Im)
           (auto simp: p3_def p4_def complex_eq_iff a_def)
      have "real m * 1 \<le> (2*m+1) * pi"
        using pi_ge_two by (intro mult_mono) auto
      also have "(2*m+1) * pi = \<bar>Im z\<bar>" by (simp add: z)
      also have "\<bar>Im z\<bar> \<le> norm z" by (rule abs_Im_le_cmod)
      finally have "norm z \<ge> m" by simp
      moreover {
        have "exp z - 1 = -of_real (exp a + 1)" using exp_integer_2pi_plus1[of m]
          by (simp add: z exp_add algebra_simps exp_of_real)
        also have "norm \<dots> \<ge> 1"
          unfolding norm_minus_cancel norm_of_real by simp
        finally have "norm (exp z - 1) \<ge> 1" .
      }
      ultimately have "norm z ^ n * norm (exp z - 1) \<ge> real m ^ n * 1"
        by (intro mult_mono power_mono) auto
      thus "norm (g z) \<le> 1 / real m ^ n" using elim
        by (simp add: g_def divide_simps norm_divide norm_mult norm_power mult_less_0_iff)
    qed (insert integrable, auto simp: eq)
    also have "norm (p4 - p3) = 2 * m" by (simp add: p4_def p3_def)

    also have "norm (I p2 p3) \<le> (1 / real m ^ n) * norm (p3 - p2)" (is "_ \<le> ?B2 * _")
      unfolding I_def
    proof (rule contour_integral_bound_linepath)
      fix z assume z: "z \<in> closed_segment p2 p3"
      define b where "b = Im z"
      from z have z: "z = m + b * \<i>"
        by (subst (asm) closed_segment_same_Re)
           (auto simp: p2_def p3_def algebra_simps complex_eq_iff b_def)
      from elim have "2 \<le> 1 + real m" by simp
      also have "\<dots> \<le> exp (real m)" by (rule exp_ge_add_one_self)
      also have "exp (real m) - 1 = norm (exp z) - norm (1::complex)"
        by (simp add: z)
      also have "\<dots> \<le> norm (exp z - 1)"
        by (rule norm_triangle_ineq2)
      finally have "norm (exp z - 1) \<ge> 1" by simp
      moreover have "norm z \<ge> m"
        using z and abs_Re_le_cmod[of z] by simp
      ultimately have "norm z ^ n * norm (exp z - 1) \<ge> real m ^ n * 1" using elim
        by (intro mult_mono power_mono) (auto simp: z)
      thus "norm (g z) \<le> 1 / real m ^ n" using n and elim
        by (simp add: g_def norm_mult norm_divide norm_power divide_simps mult_less_0_iff)
    qed (insert integrable, auto simp: eq)
    also have "p3 - p2 = of_real (2*(2*real m+1)*pi) * \<i>" by (simp add: p2_def p3_def)
    also have "norm \<dots> = 2 * (2 * real m + 1) * pi"
      unfolding norm_mult norm_of_real by simp

    also have "norm (I p4 p1) \<le> (2 / real m ^ n) * norm (p1 - p4)" (is "_ \<le> ?B4 * _")
      unfolding I_def
    proof (rule contour_integral_bound_linepath)
      fix z assume z: "z \<in> closed_segment p4 p1"
      define b where "b = Im z"
      from z have z: "z = -real m + b * \<i>"
        by (subst (asm) closed_segment_same_Re)
           (auto simp: p1_def p4_def algebra_simps b_def complex_eq_iff)
      from elim have "2 \<le> 1 + real m" by simp
      also have "\<dots> \<le> exp (real m)" by (rule exp_ge_add_one_self)
      finally have "1 / 2 \<le> 1 - exp (-real m)"
        by (subst exp_minus) (simp add: field_simps)
      also have "1 - exp (-real m) = norm (1::complex) - norm (exp z)"
        by (simp add: z)
      also have "\<dots> \<le> norm (exp z - 1)"
        by (subst norm_minus_commute, rule norm_triangle_ineq2)
      finally have "norm (exp z - 1) \<ge> 1 / 2" by simp
      moreover have "norm z \<ge> m"
        using z and abs_Re_le_cmod[of z] by simp
      ultimately have "norm z ^ n * norm (exp z - 1) \<ge> real m ^ n * (1 / 2)" using elim
        by (intro mult_mono power_mono) (auto simp: z)
      thus "norm (g z) \<le> 2 / real m ^ n" using n and elim
        by (simp add: g_def norm_mult norm_divide norm_power divide_simps mult_less_0_iff)
    qed (insert integrable, auto simp: eq)
    also have "p1 - p4 = -of_real (2*(2*real m+1)*pi) * \<i>" 
      by (simp add: p1_def p4_def algebra_simps)
    also have "norm \<dots> = 2 * (2 * real m + 1) * pi"
      unfolding norm_mult norm_of_real norm_minus_cancel by simp

    also have "?B1 * (2*m) + ?B2 * (2*(2*real m+1)*pi) + ?B3 * (2*m) + ?B4 * (2*(2*real m+1)*pi) =
                 (4 * m + 6 * (2 * m + 1) * pi) / real m ^ n"
      by (simp add: divide_simps)
    also have "(4 * m + 6 * (2 * m + 1) * pi) = (4 + 12 * pi) * m + 6 * pi"
      by (simp add: algebra_simps)
    also have "\<dots> / real m ^ n = ((4 + 12 * pi) + 6 * pi / m) / real m ^ (n - 1)"
      using n by (cases n) (simp_all add: divide_simps)
    finally show "cmod (contour_integral (\<gamma> m) g) \<le> \<dots>" by simp
  qed

  \<comment> \<open>It is clear that this bound goes to 0 since @{prop "n \<ge> 2"}.\<close>
  moreover have "(\<lambda>m. (4 + 12 * pi + 6 * pi / real m) / real m ^ (n - 1)) \<longlonglongrightarrow> 0"
    by (rule real_tendsto_divide_at_top tendsto_add tendsto_const 
          filterlim_real_sequentially filterlim_pow_at_top | use n in simp)+
  ultimately have *: "(\<lambda>m. contour_integral (\<gamma> m) g) \<longlonglongrightarrow> 0"
    by (rule Lim_null_comparison)

  \<comment> \<open>Since the infinite sum over the residues can expressed using the
      zeta function, we have now related the Bernoulli numbers at even
      positive integers to the zeta function.\<close>

  have "(\<lambda>m. contour_integral (\<gamma> m) g * (2 * pi * \<i>) ^ n / (4 * pi * \<i>) -
             of_real (bernoulli n / fact n) * (2 * pi * \<i>) ^ n / 2) \<longlonglongrightarrow>
           0 * (2 * pi * \<i>) ^ n / (4 * pi * \<i>) - 
           of_real (bernoulli n / fact n) * (2 * pi * \<i>) ^ n / 2"
    using n by (intro tendsto_intros * zeta_limit) auto
  also have "?this \<longleftrightarrow> (\<lambda>m. \<Sum>k\<in>{0<..m}. 1 / of_nat k ^ n) \<longlonglongrightarrow> 
               - of_real (bernoulli n / fact n) * (2 * pi * \<i>) ^ n / 2"
    by (intro filterlim_cong eventually_mono [OF eventually_gt_at_top[of "0::nat"]])
       (use eq in simp_all)
  finally have "(\<lambda>m. \<Sum>k\<in>{0<..m}. 1 / of_nat k ^ n)
                   \<longlonglongrightarrow> - of_real (bernoulli n / fact n) * (of_real (2 * pi) * \<i>) ^ n / 2" 
    (is "_ \<longlonglongrightarrow> ?L") .
  also have "(\<lambda>m. \<Sum>k\<in>{0<..m}. 1 / of_nat k ^ n) = (\<lambda>m. \<Sum>k\<in>{..<m}. 1 / of_nat (Suc k) ^ n)"
    by (intro ext sum.reindex_bij_witness[of _ Suc "\<lambda>n. n - 1"]) auto
  also have "\<dots> \<longlonglongrightarrow> ?L \<longleftrightarrow> (\<lambda>k. 1 / of_nat (Suc k) ^ n) sums ?L"
    by (simp add: sums_def)
  also have "(2 * pi * \<i>) ^ n = (2 * pi) ^ n * (-1) ^ n'"
    by (simp add: n_def divide_simps power_mult_distrib power_mult power_minus')
  also have "- of_real (bernoulli n / fact n) * \<dots> / 2 =
               of_real ((-1) ^ Suc n' * bernoulli (2*n') * (2*pi)^(2*n') / (2 * fact (2*n')))"
    by (simp add: n_def divide_simps)
  finally show ?thesis unfolding n_def .
qed

corollary nat_even_power_sums_real:
  assumes n': "n' > 0"
  shows   "(\<lambda>k. 1 / real (Suc k) ^ (2*n')) sums
             ((-1) ^ Suc n' * bernoulli (2*n') * (2 * pi) ^ (2 * n') / (2 * fact (2*n')))"
    (is "?f sums ?L")
proof -
  have "(\<lambda>k. complex_of_real (?f k)) sums complex_of_real ?L"
    using nat_even_power_sums_complex[OF assms] by simp
  thus ?thesis by (simp only: sums_of_real_iff)
qed

text \<open>
  We can now also easily determine the signs of Bernoulli numbers: the above formula 
  clearly shows that the signs of $B_{2n}$ alternate as $n$ increases, and we already know
  that $B_{2n+1} = 0$ for any positive $n$. A lot of other facts about the signs of
  Bernoulli numbers follow.
\<close>
corollary sgn_bernoulli_even:
  assumes "n > 0"
  shows   "sgn (bernoulli (2 * n)) = (-1) ^ Suc n"
proof -
  have *: "(\<lambda>k. 1 / real (Suc k) ^ (2 * n)) sums
             ((- 1) ^ Suc n * bernoulli (2 * n) * (2 * pi) ^ (2 * n) / (2 * fact (2 * n)))"
    using assms by (rule nat_even_power_sums_real)
  from * have "0 < (\<Sum>k. 1 / real (Suc k) ^ (2*n))"
    by (intro suminf_pos) (auto simp: sums_iff)
  hence "sgn (\<Sum>k. 1 / real (Suc k) ^ (2*n)) = 1"
    by simp
  also have "(\<Sum>k. 1 / real (Suc k) ^ (2*n)) = 
               (- 1) ^ Suc n * bernoulli (2 * n) * (2 * pi) ^ (2 * n) / (2 * fact (2 * n))"
    using * by (simp add: sums_iff)
  also have "sgn \<dots> = (-1) ^ Suc n * sgn (bernoulli (2 * n))"
    by (simp add: sgn_mult)
  finally show ?thesis
    by (simp add: minus_one_power_iff split: if_splits)
qed

corollary bernoulli_even_nonzero: "even n \<Longrightarrow> bernoulli n \<noteq> 0"
  using sgn_bernoulli_even[of "n div 2"] by (cases "n = 0") (auto elim!: evenE)

corollary sgn_bernoulli: 
  "sgn (bernoulli n) = 
     (if n = 0 then 1 else if n = 1 then -1 else if odd n then 0 else (-1) ^ Suc (n div 2))"
  using sgn_bernoulli_even [of "n div 2"] by (auto simp: bernoulli_odd_eq_0)

corollary bernoulli_zero_iff: "bernoulli n = 0 \<longleftrightarrow> odd n \<and> n \<noteq> 1"
  by (auto simp: bernoulli_even_nonzero bernoulli_odd_eq_0)

corollary bernoulli'_zero_iff: "(bernoulli' n = 0) \<longleftrightarrow> (n \<noteq> 1 \<and> odd n)"
  by (auto simp: bernoulli'_def bernoulli_zero_iff)

corollary bernoulli_pos_iff: "bernoulli n > 0 \<longleftrightarrow> n = 0 \<or> n mod 4 = 2"
proof -
  have "bernoulli n > 0 \<longleftrightarrow> sgn (bernoulli n) = 1"
    by (simp add: sgn_if)
  also have "\<dots> \<longleftrightarrow> n = 0 \<or> even n \<and> odd (n div 2)"
    by (subst sgn_bernoulli) auto
  also have "even n \<and> odd (n div 2) \<longleftrightarrow> n mod 4 = 2"
    by presburger
  finally show ?thesis .
qed

corollary bernoulli_neg_iff: "bernoulli n < 0 \<longleftrightarrow> n = 1 \<or> n > 0 \<and> 4 dvd n"
proof -
  have "bernoulli n < 0 \<longleftrightarrow> sgn (bernoulli n) = -1"
    by (simp add: sgn_if)
  also have "\<dots> \<longleftrightarrow> n = 1 \<or> n > 0 \<and> even n \<and> even (n div 2)"
    by (subst sgn_bernoulli) (auto simp: minus_one_power_iff)
  also have "even n \<and> even (n div 2) \<longleftrightarrow> 4 dvd n"
    by presburger
  finally show ?thesis .
qed


text \<open>
  We also get the solution of the Basel problem (the sum over all squares of positive
  integers) and any `Basel-like' problem with even exponent. The case of odd exponents
  is much more complicated and no similarly nice closed form is known for these.
\<close>

corollary nat_squares_sums: "(\<lambda>n. 1 / (n+1) ^ 2) sums (pi ^ 2 / 6)"
  using nat_even_power_sums_real[of 1] by (simp add: fact_numeral)

corollary nat_power4_sums: "(\<lambda>n. 1 / (n+1) ^ 4) sums (pi ^ 4 / 90)"
  using nat_even_power_sums_real[of 2] by (simp add: fact_numeral)

corollary nat_power6_sums: "(\<lambda>n. 1 / (n+1) ^ 6) sums (pi ^ 6 / 945)"
  using nat_even_power_sums_real[of 3] by (simp add: fact_numeral)

corollary nat_power8_sums: "(\<lambda>n. 1 / (n+1) ^ 8) sums (pi ^ 8 / 9450)"
  using nat_even_power_sums_real[of 4] by (simp add: fact_numeral)

end
