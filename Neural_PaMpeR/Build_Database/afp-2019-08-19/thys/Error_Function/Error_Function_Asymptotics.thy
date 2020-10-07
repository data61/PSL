(*
  File:     Error_Function_Asymptotics.thy
  Author:   Manuel Eberl, TU München

  The asymptotics of the real error function
*)
subsection \<open>Asymptotics\<close>
theory Error_Function_Asymptotics
  imports Error_Function Landau_Symbols.Landau_More
begin

lemma real_powr_eq_powerI:
  "x > 0 \<Longrightarrow> y = real y' \<Longrightarrow> x powr y = x ^ y'"
  by (simp add: powr_realpow)

definition erf_remainder_integral where
  "erf_remainder_integral n x =
     lim (\<lambda>m. integral {x..x + real m} (\<lambda>t. exp (-(t^2)) / t ^ (2*n)))"

text \<open>
  The following is the remainder term in the asymptotic expansion of @{term erfc}.
\<close>
definition erf_remainder where
  "erf_remainder n x =
     ((-1)^n * 2 * fact (2*n)) / (sqrt pi * 4 ^ n * fact n) *
     erf_remainder_integral n x"
  

lemma erf_remainder_integral_aux_nonneg:
  "x > 0 \<Longrightarrow> integral {x..x + real m} (\<lambda>t. exp (-(t^2)) / t ^ (2*n)) \<ge> 0"
  by (intro integral_nonneg integrable_continuous_real) (auto intro!: continuous_intros)

lemma erf_remainder_integral_aux_bound:
  assumes "x > 0"
  shows   "norm (integral {x..x + real m} (\<lambda>t. exp (-t\<^sup>2) / t ^ (2*n))) \<le> exp (-x\<^sup>2) / x ^ (2*n+1)"
    and   "integral {x..x + real m} (\<lambda>t. exp (-t\<^sup>2) / t ^ (2*n)) \<le> exp (-x\<^sup>2) / x ^ (2*n+1)"
proof -
  have "norm (integral {x..x + real m} (\<lambda>t. exp (-t\<^sup>2) / t ^ (2*n))) \<le>
          integral {x..x + real m} (\<lambda>t. exp (-x*t) / x ^ (2*n))"
  proof (intro integral_norm_bound_integral ballI)
    fix t assume t: "t \<in> {x..x + real m}"
    from t have "norm (exp (-t\<^sup>2) / t ^ (2*n)) = exp (-t\<^sup>2) / t ^ (2*n)" by simp
    also have "\<dots> \<le> exp (-x*t) / x ^ (2*n)" using t assms
      by (intro frac_le) (simp_all add: self_le_power power2_eq_square power_mono)
    finally show "norm (exp (-t\<^sup>2) / t ^ (2*n)) \<le> \<dots>" by simp
  qed (insert assms, auto intro!: continuous_intros integrable_continuous_real)
  also have "\<dots> = -exp (-x*(x + real m)) / x ^ (2*n+1) - (-exp (-x*x) / x ^ (2*n+1))"
    using assms
    by (intro integral_unique fundamental_theorem_of_calculus)
       (auto simp: has_field_derivative_iff_has_vector_derivative [symmetric]
             intro!: derivative_eq_intros)
  also have "\<dots> \<le> exp (-x\<^sup>2) / x ^ (2*n+1)" using assms by (simp add: power2_eq_square)
  finally show *: "norm (integral {x..x + real m} (\<lambda>t. exp (-t\<^sup>2) / t ^ (2*n))) \<le>
                      exp (-x\<^sup>2) / x ^ (2*n+1)" .
  have "integral {x..x + real m} (\<lambda>t. exp (-t\<^sup>2) / t ^ (2*n)) \<le>
          norm (integral {x..x + real m} (\<lambda>t. exp (-t\<^sup>2) / t ^ (2*n)))" by simp
  also note *
  finally show "integral {x..x + real m} (\<lambda>t. exp (-t\<^sup>2) / t ^ (2*n)) \<le> exp (-x\<^sup>2) / x ^ (2*n+1)" .
qed

lemma convergent_erf_remainder_integral:
  assumes "x > 0"
  shows   "convergent (\<lambda>m. integral {x..x + real m} (\<lambda>t. exp (-(t^2)) / t ^ (2*n)))"
proof (intro Bseq_mono_convergent BseqI'; clarify?)
  fix m :: nat
  show "norm (integral {x..x + real m} (\<lambda>t. exp (-t\<^sup>2) / t ^ (2*n))) \<le> exp (-x\<^sup>2) / x ^ (2*n+1)"
    using assms by (rule erf_remainder_integral_aux_bound)
qed (insert assms, auto intro!: integral_subset_le integrable_continuous_real continuous_intros)

lemma LIMSEQ_erf_remainder_integral:
  "x > 0 \<Longrightarrow> (\<lambda>m. integral {x..x + real m} (\<lambda>t. exp (-(t^2)) / t ^ (2*n))) \<longlonglongrightarrow>
                 erf_remainder_integral n x"
  using convergent_erf_remainder_integral[of x]
  by (simp add: convergent_LIMSEQ_iff erf_remainder_integral_def)


text \<open>
  We show some bounds on the remainder term.
\<close>
lemma
  assumes "x > 0"
  shows   erf_remainder_integral_nonneg: "erf_remainder_integral n x \<ge> 0"
    and   erf_remainder_integral_bound:  "erf_remainder_integral n x \<le> exp (-x\<^sup>2) / x ^ (2*n+1)"
proof -
  note * = LIMSEQ_erf_remainder_integral[OF assms]
  show "erf_remainder_integral n x \<ge> 0"
    by (intro tendsto_le[OF _ * tendsto_const] always_eventually
          erf_remainder_integral_aux_nonneg allI assms sequentially_bot)
  show "erf_remainder_integral n x \<le> exp (-x\<^sup>2) / x ^ (2*n+1)"
    by (intro tendsto_le[OF _ tendsto_const *] always_eventually
          erf_remainder_integral_aux_bound allI assms sequentially_bot)
qed

lemma erf_remainder_integral_bigo: 
  "erf_remainder_integral n \<in> O(\<lambda>x. exp (-x\<^sup>2) / x ^ (2*n+1))"
  using erf_remainder_integral_nonneg erf_remainder_integral_bound
  by (auto intro!: bigoI[of _ 1] eventually_mono [OF eventually_gt_at_top[of "0::real"]])
  
theorem erf_remainder_bigo: "erf_remainder n \<in> O(\<lambda>x. exp (-x\<^sup>2) / x ^ (2*n+1))"
  using erf_remainder_integral_bigo[of n] by (simp add: erf_remainder_def [abs_def])


text \<open>
  Next, we unroll the remainder term to develop the asymptotic expansion.
\<close>
lemma erf_remainder_integral_0_conv_erfc:
  assumes "(x::real) > 0"
  shows   "erf_remainder_integral 0 x = sqrt pi / 2 * erfc x"
proof -
  have "(\<lambda>m. sqrt pi / 2 * (erf (x + real m) - erf x)) \<longlonglongrightarrow> sqrt pi / 2 * erfc x"
    (is "filterlim ?f _ _") unfolding erfc_def
    by (intro tendsto_intros filterlim_tendsto_add_at_top[OF 
          tendsto_const filterlim_real_sequentially])
  also have "?f = (\<lambda>m. integral {x..x+real m} (\<lambda>t. exp (-t\<^sup>2)))"
    by (auto simp: fun_eq_iff integral_unique[OF integral_exp_minus_squared_real])
  finally have "(\<lambda>m. integral {x..x + real m} (\<lambda>t. exp (- t\<^sup>2))) \<longlonglongrightarrow> sqrt pi / 2 * erfc x" .
  moreover have "(\<lambda>m. integral {x..x + real m} (\<lambda>t. exp (- t\<^sup>2))) \<longlonglongrightarrow> erf_remainder_integral 0 x"
    using LIMSEQ_erf_remainder_integral[of x 0] assms by simp
  ultimately show "erf_remainder_integral 0 x = sqrt pi / 2 * erfc x"
    by (intro LIMSEQ_unique)
qed

text \<open>
  The first remainder is the @{term erfc} function itself.
\<close>
lemma erf_remainder_0_conv_erfc: "x > 0 \<Longrightarrow> erf_remainder 0 x = erfc x"
  by (simp add: erf_remainder_def erf_remainder_integral_0_conv_erfc)    

text \<open>
  Also, the following recurrence allows us to get the next term of the asymptotic expansion.
\<close>
lemma erf_remainder_integral_conv_Suc:
  assumes "x > 0"
  shows   "erf_remainder_integral n x = exp (-x\<^sup>2) / (2*x^(2*n+1)) -
             real (2*n+1) / 2 * erf_remainder_integral (Suc n) x"
proof -
  let ?A = "\<lambda>m. {x..x + real m}"
  let ?J = "\<lambda>m n. integral {x..x+real m} (\<lambda>t. exp(-t\<^sup>2) / t ^ (2*n))"
  define I where
    "I = (\<lambda>m. exp (- (x + real m)\<^sup>2) / (- 2 * (x + real m) ^ (2 * n + 1)) -
              exp (- x\<^sup>2) * inverse (- 2 * x ^ (2 * n + 1)) - real (2*n+1)/2 * ?J m (Suc n))"

  have I_eq: "I = (\<lambda>m. integral (?A m) (\<lambda>t. exp (- t\<^sup>2) / t ^ (2 * n)))"
  proof
    fix m :: nat
    have "((\<lambda>t. (-2*t*exp (-(t^2))) * inverse (-2*t^(2*n+1))) has_integral I m) (?A m)"
    proof (rule integration_by_parts[OF bounded_bilinear_mult])
      fix t assume t: "t \<in> ?A m"
      with assms show "((\<lambda>t. exp (-(t^2))) has_vector_derivative -2*t*exp (-(t^2))) (at t)"
        by (auto simp: has_field_derivative_iff_has_vector_derivative [symmetric]
                       field_simps intro!: derivative_eq_intros)
      from assms t have "((\<lambda>t. -(1/2) * t powr (-2*n-1)) has_field_derivative
                           (2*n+1)/2 * t powr (-2*n-2)) (at t)"
        by (auto intro!: derivative_eq_intros simp: field_simps powr_numeral power2_eq_square
                         powr_minus powr_divide [symmetric] powr_add)
      also have "?this \<longleftrightarrow> ((\<lambda>t. inverse (-2*t^(2*n+1))) has_field_derivative
                              (2*n+1)/2 / t ^ (2*Suc n)) (at t)" using t
        using eventually_nhds_in_open[of "{0<..}" t] assms
        by (intro DERIV_cong_ev refl)
           (auto elim!: eventually_mono simp: powr_minus field_simps powr_diff
                        powr_realpow power2_eq_square intro!: real_powr_eq_powerI)
      finally show "((\<lambda>t. inverse (-2*t^(2*n+1))) has_vector_derivative
                              (2*n+1)/2 / t ^ (2*Suc n)) (at t)"
        by (simp add: has_field_derivative_iff_has_vector_derivative)
    next
      have "((\<lambda>t. real (2*n+1)/2 * (exp (- t\<^sup>2) / t ^ (2 * Suc n))) has_integral
             real (2*n+1)/2 * ?J m (Suc n)) (?A m)" (is "(?f has_integral ?a) _")
        using assms
        by (intro has_integral_mult_right integrable_integral integrable_continuous_real)
           (auto intro!: continuous_intros)
      also have "?f = (\<lambda>t. exp (- t\<^sup>2) * (real (2 * n + 1) / 2 / t ^ (2 * Suc n)))"
        by (simp add: fun_eq_iff field_simps)
      also have "?a = exp (- (x + real m)\<^sup>2) * inverse (- 2 * (x + real m) ^ (2 * n + 1)) -
                          exp (- x\<^sup>2) * inverse (- 2 * x ^ (2 * n + 1)) - I m" using assms
        by (simp add: I_def algebra_simps inverse_eq_divide)
      finally show "((\<lambda>t. exp (- t\<^sup>2) * (real (2 * n + 1) / 2 / t ^ (2 * Suc n))) has_integral \<dots>)
                      {x..x + real m}" .
    qed (insert assms, auto intro!: continuous_intros)
    hence "I m = integral {x..x + real m} (\<lambda>t. - 2*t*exp (- t\<^sup>2) * inverse (-2*t^(2 * n + 1)))"
      by (simp add: has_integral_iff)
    also have "\<dots> = integral {x..x + real m} (\<lambda>t. exp (- t\<^sup>2) / t ^ (2*n))"
      using assms by (intro integral_cong) (simp_all add: field_simps)
    finally show "I m = \<dots>" .
  qed

  have "filterlim (\<lambda>m. (-exp (- (x + real m)\<^sup>2)) / (2 * (x + real m) ^ (2 * n + 1)))
          (nhds 0) at_top"
    by (rule real_tendsto_divide_at_top filterlim_real_sequentially tendsto_minus
             filterlim_compose[OF exp_at_bot] filterlim_compose[OF filterlim_uminus_at_bot_at_top]
             filterlim_pow_at_top filterlim_tendsto_add_at_top tendsto_const filterlim_ident
             filterlim_tendsto_pos_mult_at_top | simp)+
  hence *: "filterlim (\<lambda>m. (exp (- (x + real m)\<^sup>2)) / (-2 * (x + real m) ^ (2 * n + 1)))
              (nhds 0) at_top" by (simp add: add_ac)
  have "I \<longlonglongrightarrow> 0 - exp (- x\<^sup>2) * inverse (- 2 * x ^ (2 * n + 1)) -
                  real (2 * n + 1) / 2 * erf_remainder_integral (Suc n) x"
    unfolding I_def
    by (intro tendsto_diff * tendsto_const tendsto_mult LIMSEQ_erf_remainder_integral assms)
  moreover from LIMSEQ_erf_remainder_integral[OF assms, of n] I_eq
    have "I \<longlonglongrightarrow> erf_remainder_integral n x"  by simp
  ultimately have "0 - exp (- x\<^sup>2) * inverse (- 2 * x ^ (2 * n + 1)) - real (2 * n + 1) / 2 *
                     erf_remainder_integral (Suc n) x = erf_remainder_integral n x"
    by (rule LIMSEQ_unique)
  thus ?thesis by (simp add: field_simps)
qed

lemma erf_remainder_conv_Suc:
  assumes "x > 0"
  shows   "erf_remainder n x = (- 1) ^ n * fact (2 * n) / (sqrt pi * 4 ^ n * fact n) *
                    exp (- x\<^sup>2) / (x ^ (2 * n + 1)) + erf_remainder (Suc n) x"
proof -
  have "erf_remainder n x =
          (- 1) ^ n * 2 * fact (2 * n) / (sqrt pi * 4 ^ n * fact n) *
             exp (- x\<^sup>2) / (2 * x ^ (2 * n + 1)) + -(
          (- 1) ^ n * 2 * fact (2 * n) / (sqrt pi * 4 ^ n * fact n) *
            real (2 * n + 1) / 2 * erf_remainder_integral (Suc n) x)" (is "_ = ?A + ?B")
    unfolding erf_remainder_def using assms
    by (subst erf_remainder_integral_conv_Suc)
       (auto simp: assms algebra_simps simp del: power_Suc)
  also have "?B = erf_remainder (Suc n) x"
    by (simp add: divide_simps erf_remainder_def)
  also have "?A = (- 1) ^ n * fact (2 * n) / (sqrt pi * 4 ^ n * fact n) *
                    exp (- x\<^sup>2) / (x ^ (2 * n + 1))"
    by (simp add: divide_simps)
  finally show ?thesis .
qed

text \<open>
  Finally, this gives us the full asymptotic expansion for @{term erfc}:
\<close>
theorem erfc_unroll:
  assumes "x > 0"
  shows   "erfc x = exp (-x\<^sup>2) / sqrt pi * 
             (\<Sum>i<n. (-1)^i * fact (2*i) / (4^i*fact i) / x^(2*i+1)) + erf_remainder n x"
proof (induction n)
  case (Suc n)
  note Suc.IH
  also note erf_remainder_conv_Suc[OF assms, of n]
  also have "exp (- x\<^sup>2) / sqrt pi *
               (\<Sum>i<n. (- 1) ^ i * fact (2 * i) / (4 ^ i * fact i) / x ^ (2*i+1)) +
                 ((- 1) ^ n * fact (2*n) / (sqrt pi * 4 ^ n * fact n) * exp (- x\<^sup>2) / x^(2*n+1) +
                 erf_remainder (Suc n) x) =
               exp (- x\<^sup>2) / sqrt pi *
                 (\<Sum>i<Suc n. (- 1) ^ i * fact (2 * i) / (4 ^ i * fact i) / x ^ (2 * i + 1)) +
                 erf_remainder (Suc n) x"
    by (subst sum.lessThan_Suc) (simp add: algebra_simps)
  finally show ?case .
qed (auto simp: assms erf_remainder_0_conv_erfc)
  


text \<open>
  For convenience, we define another auxiliary function that is more suitable for use in an 
  automated expansion framework, since it has a simple asymptotic expansion in powers of $x$.
\<close>
definition erfc_aux where "erfc_aux x = exp (x\<^sup>2) * sqrt pi * erfc x"
definition erf_remainder' where "erf_remainder' n x = exp (x\<^sup>2) * sqrt pi * erf_remainder n x"

lemma erfc_aux_unroll: 
  "x > 0 \<Longrightarrow> 
     erfc_aux x = (\<Sum>i<n. (-1)^i * fact (2*i) / (4^i*fact i) / x^(2*i+1)) + erf_remainder' n x"
  using erfc_unroll[of x n] 
  by (simp add: erfc_aux_def erf_remainder'_def exp_minus field_simps del: of_nat_Suc)

lemma erf_remainder'_bigo: "erf_remainder' n \<in> O(\<lambda>x. 1 / x ^ (2*n+1))"
proof -
  have "(\<lambda>x. exp (x\<^sup>2) * erf_remainder n x) \<in> O(\<lambda>x. exp (x\<^sup>2) * (exp (-x\<^sup>2) / x ^ (2*n+1)))"
    by (intro landau_o.big.mult erf_remainder_bigo) simp_all
  thus ?thesis by (simp add: exp_minus erf_remainder'_def [abs_def])
qed

lemma has_field_derivative_erfc_aux: 
    "(erfc_aux has_field_derivative (2 * x * erfc_aux x - 2)) (at x)"
  by (auto simp: erfc_aux_def [abs_def] exp_minus field_simps intro!: derivative_eq_intros)

end
