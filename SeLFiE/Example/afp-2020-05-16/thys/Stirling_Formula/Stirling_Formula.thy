(*
  File:    Stirling_Formula.thy
  Author:  Manuel Eberl

  A proof of Stirling's formula, i.e. an asymptotic approximation of
  the Gamma function and the factorial.
*)
section \<open>Stirling's Formula\<close>
theory Stirling_Formula
imports
  "HOL-Analysis.Analysis"
  "Landau_Symbols.Landau_More"
begin

context
begin

text \<open>
  First, we define the $S_n^*$ from Jameson's article:
\<close>
private definition S' :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "S' n x = 1/(2*x) + (\<Sum>r=1..<n. 1/(of_nat r+x)) + 1 /(2*(n + x))"

text \<open>
  Next, the trapezium (also called $T$ in Jameson's article):
\<close>
private definition T :: "real \<Rightarrow> real" where
  "T x = 1/(2*x) + 1/(2*(x+1))"

text \<open>
  Now we define The difference $\Delta(x)$:
\<close>
private definition D :: "real \<Rightarrow> real" where
  "D x = T x - ln (x + 1) + ln x"

private lemma S'_telescope_trapezium:
  assumes "n > 0"
  shows   "S' n x = (\<Sum>r<n. T (of_nat r + x))"
proof (cases n)
  case (Suc m)
  hence m: "Suc m = n" by simp
  have "(\<Sum>r<n. T (of_nat r + x)) = 
          (\<Sum>r<Suc m. 1 / (2 * real r + 2 * x)) + (\<Sum>r<n. 1 / (2 * real (Suc r) + 2 * x))"
    unfolding m by (simp add: T_def sum.distrib algebra_simps)
  also have "(\<Sum>r<Suc m. 1 / (2 * real r + 2 * x)) = 
               1/(2*x) + (\<Sum>r<m. 1 / (2 * real (Suc r) + 2 * x))" (is "_ = ?a + ?S")
    by (subst sum.lessThan_Suc_shift) simp
  also have "(\<Sum>r<n. 1 / (2 * real (Suc r) + 2 * x)) = 
               ?S + 1 / (2*(real m + x + 1))" (is "_ = _ + ?b") by (simp add: Suc)
  also have "?a + ?S + (?S + ?b) = 2*?S + ?a + ?b" by (simp add: add_ac)
  also have "2 * ?S = (\<Sum>r=0..<m. 1 / (real (Suc r) + x))" 
    unfolding sum_distrib_left by (intro sum.cong) (auto simp add: divide_simps)
  also have "(\<Sum>r=0..<m. 1 / (real (Suc r) + x)) = (\<Sum>r=Suc 0..<Suc m. 1 / (real r + x))"
    by (subst sum.atLeast_Suc_lessThan_Suc_shift) simp_all
  also have "\<dots> = (\<Sum>r=1..<n. 1 / (real r + x))" unfolding m by simp
  also have "\<dots> + ?a + ?b = S' n x" by (simp add: S'_def Suc)
  finally show ?thesis ..
qed (insert assms, simp_all)

private lemma stirling_trapezium:
  assumes x: "(x::real) > 0"
  shows   "D x \<in> {0 .. 1/(12*x^2) - 1/(12 * (x+1)^2)}"
proof -
  define y where "y = 1 / (2*x + 1)"
  from x have y: "y > 0" "y < 1" by (simp_all add: divide_simps y_def)

  from x have "D x = T x - ln ((x + 1) / x)" by (subst ln_div) (simp_all add: D_def)
  also from x have "(x + 1) / x = 1 + 1 / x" by (simp add: field_simps)
  finally have D: "D x = T x - ln (1 + 1/x)" .

  from y have "(\<lambda>n. y * y^n) sums (y * (1 / (1 - y)))" 
    by (intro geometric_sums sums_mult) simp_all
  hence "(\<lambda>n. y ^ Suc n) sums (y / (1 - y))" by simp
  also from x have "y / (1 - y) = 1 / (2*x)" by (simp add: y_def divide_simps)
  finally have *: "(\<lambda>n. y ^ Suc n) sums (1 / (2*x))" .

  from y have "(\<lambda>n. (-y) * (-y)^n) sums ((-y) * (1 / (1 - (-y))))" 
    by (intro geometric_sums sums_mult) simp_all
  hence "(\<lambda>n. (-y) ^ Suc n) sums (-(y / (1 + y)))" by simp
  also from x have "y / (1 + y) = 1 / (2*(x+1))" by (simp add: y_def divide_simps)
  finally have **: "(\<lambda>n. (-y) ^ Suc n) sums (-(1 / (2*(x+1))))" .

  from sums_diff[OF * **] have sum1: "(\<lambda>n. y ^ Suc n - (-y) ^ Suc n) sums T x"
    by (simp add: T_def)
  
  from y have "abs y < 1" "abs (-y) < 1" by simp_all
  from sums_diff[OF this[THEN ln_series']]
    have "(\<lambda>n. y ^ n / real n - (-y) ^ n / real n) sums (ln (1 + y) - ln (1 - y))" by simp
  also from y have "ln (1 + y) - ln (1 - y) = ln ((1 + y) / (1 - y))" by (simp add: ln_div)
  also from x have "(1 + y) / (1 - y) = 1 + 1/x" by (simp add: divide_simps y_def)
  finally have "(\<lambda>n. y^n / real n - (-y)^n / real n) sums ln (1 + 1/x)" .
  hence sum2: "(\<lambda>n. y^Suc n / real (Suc n) - (-y)^Suc n / real (Suc n)) sums ln (1 + 1/x)"
    by (subst sums_Suc_iff) simp

  from sum2 sum1 have "ln (1 + 1/x) \<le> T x"
  proof (rule sums_le [OF allI, rotated])
    fix n :: nat
    show "y ^ Suc n / real (Suc n) - (-y) ^ Suc n / real (Suc n) \<le> y^Suc n - (-y) ^ Suc n"
    proof (cases "even n")
      case True
      hence eq: "A - (-y) ^ Suc n / B = A + y ^ Suc n / B" "A - (-y) ^ Suc n = A + y ^ Suc n"
        for A B by simp_all
      from y show ?thesis unfolding eq
        by (intro add_mono) (auto simp: divide_simps)
    qed simp_all
  qed
  hence "D x \<ge> 0" by (simp add: D)

  define c where "c = (\<lambda>n. if even n then 2 * (1 - 1 / real (Suc n)) else 0)"
  note sums_diff[OF sum1 sum2]
  also have "(\<lambda>n. y ^ Suc n - (-y) ^ Suc n - (y ^ Suc n / real (Suc n) - 
                   (-y) ^ Suc n / real (Suc n))) = (\<lambda>n. c n * y ^ Suc n)"
    by (intro ext) (simp add: c_def algebra_simps)
  finally have sum3: "(\<lambda>n. c n * y ^ Suc n) sums D x" by (simp add: D)
  
  from y have "(\<lambda>n. y^2 * (of_nat (Suc n) * y^n)) sums (y^2 * (1 / (1 - y)^2))"
    by (intro sums_mult geometric_deriv_sums) simp_all
  hence "(\<lambda>n. of_nat (Suc n) * y^(n+2)) sums (y^2 / (1 - y)^2)" 
    by (simp add: algebra_simps power2_eq_square)
  also from x have "y^2 / (1 - y)^2 = 1 / (4*x^2)" by (simp add: y_def divide_simps)
  finally have *: "(\<lambda>n. real (Suc n) * y ^ (Suc (Suc n))) sums (1 / (4 * x\<^sup>2))" by simp

  from y have "(\<lambda>n. y^2 * (of_nat (Suc n) * (-y)^n)) sums (y^2 * (1 / (1 - -y)^2))"
    by (intro sums_mult geometric_deriv_sums) simp_all
  hence "(\<lambda>n. of_nat (Suc n) * (-y)^(n+2)) sums (y^2 / (1 + y)^2)"
    by (simp add: algebra_simps power2_eq_square)
  also from x have "y^2 / (1 + y)^2 = 1 / (2^2*(x+1)^2)" 
    unfolding power_mult_distrib [symmetric] by (simp add: y_def divide_simps add_ac)
  finally have **: "(\<lambda>n. real (Suc n) * (- y) ^ (Suc (Suc n))) sums (1 / (4 * (x + 1)\<^sup>2))" by simp
  
  define d where "d = (\<lambda>n. if even n then 2 * real n else 0)"
  note sums_diff[OF * **]
  also have "(\<lambda>n. real (Suc n) * y^(Suc (Suc n)) - real (Suc n) * (-y)^(Suc (Suc n))) = 
                 (\<lambda>n. d (Suc n) * y ^ Suc (Suc n))"
    by (intro ext) (simp_all add: d_def)
  finally have "(\<lambda>n. d n * y ^ Suc n) sums (1 / (4 * x\<^sup>2) - 1 / (4 * (x + 1)\<^sup>2))" 
    by (subst (asm) sums_Suc_iff) (simp add: d_def)
  from sums_mult[OF this, of "1/3"] x
    have sum4: "(\<lambda>n. d n / 3 * y ^ Suc n) sums (1 / (12 * x^2) - 1 / (12 * (x + 1)^2))"
    by (simp add: field_simps)
  
  have "D x \<le> (1 / (12 * x^2) - 1 / (12 * (x + 1)^2))"
  proof (intro sums_le [OF _ sum3 sum4] allI)
    fix n :: nat
    define c' :: "nat \<Rightarrow> real" 
      where "c' = (\<lambda>n. if odd n \<or> n = 0 then 0 else if n = 2 then 4/3 else 2)"
    show "c n * y ^ Suc n \<le> d n / 3 * y ^ Suc n"
    proof (intro mult_right_mono)
      have "c n \<le> c' n" by (simp add: c_def c'_def)
      also consider "n = 0" | "n = 1" | "n = 2" | "n \<ge> 3" by force
      hence "c' n \<le> d n / 3" by cases (simp_all add: c'_def d_def)
      finally show "c n \<le> d n / 3" .
    qed (insert y, simp)
  qed

  with \<open>D x \<ge> 0\<close> show ?thesis by simp
qed  

text \<open>
  The following functions correspond to the $p_n(x)$ from the article.
  The special case $n = 0$ would not, strictly speaking, be necessary, but 
  it allows some theorems to work even without the precondition $n \neq 0$:
\<close>
private definition p :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "p n x = (if n = 0 then 1/x else (\<Sum>r<n. D (real r + x)))"

text \<open>
  We can write the Digamma function in terms of @{term S'}:
\<close>
private lemma S'_LIMSEQ_Digamma:
  assumes x: "x \<noteq> 0"
  shows   "(\<lambda>n. ln (real n) - S' n x - 1/(2*x)) \<longlonglongrightarrow> Digamma x"
proof -
  define c where "c = (\<lambda>n. ln (real n) - (\<Sum>r<n. inverse (x + real r)))"
  have "eventually (\<lambda>n. 1 / (2 * (x + real n)) = c n - (ln (real n) - S' n x - 1/(2*x))) at_top"
    using eventually_gt_at_top[of "0::nat"]
  proof eventually_elim
    fix n :: nat
    assume n: "n > 0"
    have "c n - (ln (real n) - S' n x - 1/(2*x)) = 
            -(\<Sum>r<n. inverse (real r + x)) + (1/x + (\<Sum>r=1..<n. inverse (real r + x))) + 1/(2*(real n + x))"
      using x by (simp add: S'_def c_def field_simps)
    also have "1/x + (\<Sum>r=1..<n. inverse (real r + x)) = (\<Sum>r<n. inverse (real r + x))"
      unfolding lessThan_atLeast0 using n 
      by (subst (2) sum.atLeast_Suc_lessThan) (simp_all add: field_simps)
    finally show "1 / (2 * (x + real n)) = c n - (ln (real n) - S' n x - 1/(2*x))" by simp
  qed
  moreover have "(\<lambda>n. 1 / (2 * (x + real n))) \<longlonglongrightarrow> 0"
    by (rule real_tendsto_divide_at_top tendsto_const filterlim_tendsto_pos_mult_at_top
          filterlim_tendsto_add_at_top filterlim_real_sequentially | simp)+
  ultimately have "(\<lambda>n. c n - (ln (real n) - S' n x - 1/(2*x))) \<longlonglongrightarrow> 0"
    by (blast intro: Lim_transform_eventually)
  from tendsto_minus[OF this] have "(\<lambda>n. (ln (real n) - S' n x - 1/(2*x)) - c n) \<longlonglongrightarrow> 0" by simp
  moreover from Digamma_LIMSEQ[OF x] have "c \<longlonglongrightarrow> Digamma x" by (simp add: c_def) 
  ultimately show "(\<lambda>n. ln (real n) - S' n x - 1/(2*x)) \<longlonglongrightarrow> Digamma x"
    by (rule Lim_transform [rotated])
qed

text \<open>
  Moreover, we can give an expansion of @{term S'} with the @{term p} as variation terms.
\<close>
private lemma S'_approx: 
  "S' n x = ln (real n + x) - ln x + p n x"
proof (cases "n = 0")
  case True
  thus ?thesis by (simp add: p_def S'_def)
next
  case False
  hence "S' n x = (\<Sum>r<n. T (real r + x))"
    by (subst S'_telescope_trapezium) simp_all
  also have "\<dots> = (\<Sum>r<n. ln (real r + x + 1) - ln (real r + x) + D (real r + x))"
    by (simp add: D_def)
  also have "\<dots> = (\<Sum>r<n. ln (real (Suc r) + x) - ln (real r + x)) + p n x"
    using False by (simp add: sum.distrib add_ac p_def)
  also have "(\<Sum>r<n. ln (real (Suc r) + x) - ln (real r + x)) = ln (real n + x) - ln x"
    by (subst sum_lessThan_telescope) simp_all
  finally show ?thesis .
qed

text \<open>
  We define the limit of the @{term p} (simply called $p(x)$ in Jameson's article):
\<close>
private definition P :: "real \<Rightarrow> real" where
  "P x = (\<Sum>n. D (real n + x))"

private lemma D_summable:
  assumes x: "x > 0"
  shows   "summable (\<lambda>n. D (real n + x))"
proof -
  have *: "summable (\<lambda>n. 1 / (12 * (x + real n)\<^sup>2) - 1 / (12 * (x + real (Suc n))\<^sup>2))"
    by (rule telescope_summable' real_tendsto_divide_at_top tendsto_const 
             filterlim_tendsto_pos_mult_at_top filterlim_pow_at_top
             filterlim_tendsto_add_at_top filterlim_real_sequentially | simp)+
  show "summable (\<lambda>n. D (real n + x))" 
  proof (rule summable_comparison_test[OF _ *], rule exI[of _ 2], safe)
    fix n :: nat assume "n \<ge> 2"
    show "norm (D (real n + x)) \<le> 1 / (12 * (x + real n)^2) - 1 / (12 * (x + real (Suc n))^2)"
      using stirling_trapezium[of "real n + x"] x by (auto simp: algebra_simps)
  qed
qed

private lemma p_LIMSEQ:
  assumes x: "x > 0"
  shows   "(\<lambda>n. p n x) \<longlonglongrightarrow> P x"
proof (rule Lim_transform_eventually)
  from D_summable[OF x] have "(\<lambda>n. D (real n + x)) sums P x" unfolding P_def
    by (simp add: sums_iff)
  then show "(\<lambda>n. \<Sum>r<n. D (real r + x)) \<longlonglongrightarrow> P x" by (simp add: sums_def)
  moreover from eventually_gt_at_top[of 1]
  show "eventually (\<lambda>n. (\<Sum>r<n. D (real r + x)) = p n x) at_top"
    by eventually_elim (auto simp: p_def)
qed

text \<open>
  This gives us an expansion of the Digamma function:
\<close>
lemma Digamma_approx:
  assumes x: "(x :: real) > 0"
  shows   "Digamma x = ln x - 1 / (2 * x) - P x"
proof -
  have "eventually (\<lambda>n. ln (inverse (1 + x / real n)) + ln x - 1/(2*x) - p n x =
          ln (real n) - S' n x - 1/(2*x)) at_top"
    using eventually_gt_at_top[of "1::nat"]
  proof eventually_elim
    fix n :: nat assume n: "n > 1"
    have "ln (real n) - S' n x = ln ((real n) / (real n + x)) + ln x - p n x"
      using assms n unfolding S'_approx by (subst ln_div) (auto simp: algebra_simps)
    also from n have "real n / (real n + x) = inverse (1 + x / real n)" by (simp add: field_simps)
    finally show "ln (inverse (1 + x / real n)) + ln x - 1/(2*x) - p n x = 
                    ln (real n) - S' n x - 1/(2*x)" by simp
  qed
  moreover have "(\<lambda>n. ln (inverse (1 + x / real n)) + ln x - 1/(2*x) - p n x) 
                   \<longlonglongrightarrow> ln (inverse (1 + 0)) + ln x - 1/(2*x) - P x"
    by (rule tendsto_intros p_LIMSEQ x real_tendsto_divide_at_top 
          filterlim_real_sequentially | simp)+
  hence "(\<lambda>n. ln (inverse (1 + x / real n)) + ln x - 1/(2*x) - p n x) 
             \<longlonglongrightarrow> ln x - 1/(2*x) - P x" by simp
  ultimately have "(\<lambda>n. ln (real n) - S' n x - 1 / (2 * x)) \<longlonglongrightarrow> ln x - 1/(2*x) - P x"
    by (blast intro: Lim_transform_eventually)
  moreover from x have "(\<lambda>n. ln (real n) - S' n x - 1 / (2 * x)) \<longlonglongrightarrow> Digamma x"
    by (intro S'_LIMSEQ_Digamma) simp_all
  ultimately show "Digamma x = ln x - 1 / (2 * x) - P x"
    by (rule LIMSEQ_unique [rotated])
qed

text \<open>
  Next, we derive some bounds on @{term "P"}:
\<close>
private lemma p_ge_0: "x > 0 \<Longrightarrow> p n x \<ge> 0"
  using stirling_trapezium[of "real n + x" for n]
  by (auto simp add: p_def intro!: sum_nonneg)

private lemma P_ge_0: "x > 0 \<Longrightarrow> P x \<ge> 0"
  by (rule tendsto_lowerbound[OF p_LIMSEQ]) 
     (insert p_ge_0[of x], simp_all)

private lemma p_upper_bound:
  assumes "x > 0" "n > 0"
  shows "p n x \<le> 1/(12*x^2)"
proof -
  from assms have "p n x = (\<Sum>r<n. D (real r + x))"
    by (simp add: p_def)
  also have "\<dots> \<le> (\<Sum>r<n. 1/(12*(real r + x)^2) - 1/(12 * (real (Suc r) + x)^2))"
    using stirling_trapezium[of "real r + x" for r] assms 
    by (intro sum_mono) (simp add: add_ac)
  also have "\<dots> = 1 / (12 * x\<^sup>2) - 1 / (12 * (real n + x)\<^sup>2)"
    by (subst sum_lessThan_telescope') simp
  also have "\<dots> \<le> 1 / (12 * x^2)" by simp
  finally show ?thesis .
qed

private lemma P_upper_bound:
  assumes "x > 0"
  shows   "P x \<le> 1/(12*x^2)"
proof (rule tendsto_upperbound)
  show "eventually (\<lambda>n. p n x \<le> 1 / (12 * x^2)) at_top"
    using eventually_gt_at_top[of 0] 
    by eventually_elim (use p_upper_bound[of x] assms in auto)
  show "(\<lambda>n. p n x) \<longlonglongrightarrow> P x"
    by (simp add: assms p_LIMSEQ)
qed auto


text \<open>
  We can now use this approximation of the Digamma function to approximate
  @{term ln_Gamma} (since the former is the derivative of the latter). 
  We therefore define the function $g$ from Jameson's article, which measures 
  the difference between @{term ln_Gamma} and its approximation:
\<close>

private definition g :: "real \<Rightarrow> real" where
  "g x = ln_Gamma x - (x - 1/2) * ln x + x"

private lemma DERIV_g: "x > 0 \<Longrightarrow> (g has_field_derivative -P x) (at x)"
  unfolding g_def [abs_def] using Digamma_approx[of x]
  by (auto intro!: derivative_eq_intros simp: field_simps)

private lemma isCont_P: 
  assumes "x > 0"
  shows   "isCont P x"
proof -
  define D' :: "real \<Rightarrow> real"
    where "D' = (\<lambda>x. - 1 / (2 * x^2 * (x+1)^2))"
  have DERIV_D: "(D has_field_derivative D' x) (at x)" if "x > 0" for x
    unfolding D_def [abs_def] D'_def T_def
    by (insert that, (rule derivative_eq_intros refl | simp)+)
       (simp add: power2_eq_square divide_simps,  (simp add: algebra_simps)?)
  note this [THEN DERIV_chain2, derivative_intros]
  
  have "(P has_field_derivative (\<Sum>n. D' (real n + x))) (at x)"
    unfolding P_def [abs_def]
  proof (rule has_field_derivative_series')
    show "convex {x/2<..}" by simp
  next
    fix n :: nat and y :: real assume y: "y \<in> {x/2<..}"
    with assms have "y > 0" by simp
    thus "((\<lambda>a. D (real n + a)) has_real_derivative D' (real n + y)) (at y within {x/2<..})"
      by (auto intro!: derivative_eq_intros)
  next
    from assms D_summable[of x] show "summable (\<lambda>n. D (real n + x))" by simp
  next
    show "uniformly_convergent_on {x/2<..} (\<lambda>n x. \<Sum>i<n. D' (real i + x))"
    proof (rule Weierstrass_m_test')
      fix n :: nat and y :: real
      assume y: "y \<in> {x/2<..}"
      with assms have "y > 0" by auto
      have "norm (D' (real n + y)) = (1 / (2 * (y + real n)^2)) * (1 / (y + real (Suc n))^2)"
        by (simp add: D'_def add_ac)
      also from y assms have "\<dots> \<le> (1 / (2 * (x/2)^2)) * (1 / (real (Suc n))^2)"
        by (intro mult_mono divide_left_mono power_mono) simp_all
      also have "1 / (real (Suc n))^2 = inverse ((real (Suc n))^2)" by (simp add: field_simps)
      finally show "norm (D' (real n + y)) \<le> (1 / (2 * (x/2)^2)) * inverse ((real (Suc n))^2)" .
    next
      show "summable (\<lambda>n. (1 / (2 * (x/2)^2)) * inverse ((real (Suc n))^2))"
        by (subst summable_Suc_iff, intro summable_mult inverse_power_summable) simp_all
    qed
  qed (insert assms, simp_all add: interior_open)
  thus ?thesis by (rule DERIV_isCont)
qed

private lemma P_continuous_on [THEN continuous_on_subset]: "continuous_on {0<..} P"
  by (intro continuous_at_imp_continuous_on ballI isCont_P) auto

private lemma P_integrable:
  assumes a: "a > 0"
  shows   "P integrable_on {a..}"
proof -
  define f where "f = (\<lambda>n x. if x \<in> {a..real n} then P x else 0)"
  show "P integrable_on {a..}"
  proof (rule dominated_convergence)
    fix n :: nat
    from a have "P integrable_on {a..real n}"
      by (intro integrable_continuous_real P_continuous_on) auto
    hence "f n integrable_on {a..real n}"
      by (rule integrable_eq) (simp add: f_def)
    thus "f n integrable_on {a..}"
      by (rule integrable_on_superset) (auto simp: f_def)
  next
    fix n :: nat
    show "norm (f n x) \<le> of_real (1/12) * (1 / x^2)" if "x \<in> {a..}" for x
      using a P_ge_0 P_upper_bound by (auto simp: f_def)
  next
    show "(\<lambda>x::real. of_real (1/12) * (1 / x^2)) integrable_on {a..}"
      using has_integral_inverse_power_to_inf[of 2 a] a
      by (intro integrable_on_cmult_left) auto
  next
    show "(\<lambda>n. f n x) \<longlonglongrightarrow> P x" if "x\<in>{a..}" for x
    proof -
      have "eventually (\<lambda>n. real n \<ge> x) at_top"
        using filterlim_real_sequentially by (simp add: filterlim_at_top)
      with that have "eventually (\<lambda>n. f n x = P x) at_top"
        by (auto elim!: eventually_mono simp: f_def)
      thus "(\<lambda>n. f n x) \<longlonglongrightarrow> P x" by (simp add: tendsto_eventually)
    qed
  qed
qed

private definition c :: real where "c = integral {1..} (\<lambda>x. -P x) + g 1"

text \<open>
  We can now give bounds on @{term g}:
\<close>
private lemma g_bounds:
  assumes x: "x \<ge> 1"
  shows   "g x \<in> {c..c + 1/(12*x)}"
proof -
  from assms have int_nonneg: "integral {x..} P \<ge> 0"
    by (intro Henstock_Kurzweil_Integration.integral_nonneg P_integrable)
       (auto simp: P_ge_0)
  have int_upper_bound: "integral {x..} P \<le> 1/(12*x)"
  proof (rule has_integral_le)
    from x show "(P has_integral integral {x..} P) {x..}"
      by (intro integrable_integral P_integrable) simp_all
    from x has_integral_mult_right[OF has_integral_inverse_power_to_inf[of 2 x], of "1/12"]
      show "((\<lambda>x. 1/(12*x^2)) has_integral (1/(12*x))) {x..}" by (simp add: field_simps)
  qed (insert P_upper_bound x, simp_all)

  note DERIV_g [THEN DERIV_chain2, derivative_intros]
  from assms have int1: "((\<lambda>x. -P x) has_integral (g x - g 1)) {1..x}"
    by (intro fundamental_theorem_of_calculus)
       (auto simp: has_field_derivative_iff_has_vector_derivative [symmetric]
             intro!: derivative_eq_intros)
  from x have int2: "((\<lambda>x. -P x) has_integral integral {x..} (\<lambda>x. -P x)) {x..}"
    by (intro integrable_integral integrable_neg P_integrable) simp_all
  from has_integral_Un[OF int1 int2] x
    have "((\<lambda>x. - P x) has_integral g x - g 1 - integral {x..} P) ({1..x} \<union> {x..})"
    by (simp add: max_def)
  also from x have "{1..x} \<union> {x..} = {1..}" by auto
  finally have "((\<lambda>x. -P x) has_integral g x - g 1 - integral {x..} P) {1..}" .
  moreover have "((\<lambda>x. -P x) has_integral integral {1..} (\<lambda>x. -P x)) {1..}"
    by (intro integrable_integral integrable_neg P_integrable) simp_all
  ultimately have "g x - g 1 - integral {x..} P = integral {1..} (\<lambda>x. -P x)"
    by (simp add: has_integral_unique)
  hence "g x = c + integral {x..} P" by (simp add: c_def algebra_simps)
  with int_upper_bound int_nonneg show "g x \<in> {c..c + 1/(12*x)}" by simp
qed


text \<open>
  Finally, we have bounds on @{term ln_Gamma}, @{term Gamma}, and @{term fact}.
\<close>
private lemma ln_Gamma_bounds_aux:
  "x \<ge> 1 \<Longrightarrow> ln_Gamma x \<ge> c + (x - 1/2) * ln x - x"
  "x \<ge> 1 \<Longrightarrow> ln_Gamma x \<le> c + (x - 1/2) * ln x - x + 1/(12*x)"
  using g_bounds[of x] by (simp_all add: g_def)

private lemma Gamma_bounds_aux:
  assumes x: "x \<ge> 1"
  shows   "Gamma x \<ge> exp c * x powr (x - 1/2) / exp x"
          "Gamma x \<le> exp c * x powr (x - 1/2) / exp x * exp (1/(12*x))"
proof -
  have "exp (ln_Gamma x) \<ge> exp (c + (x - 1/2) * ln x - x)"
    by (subst exp_le_cancel_iff, rule ln_Gamma_bounds_aux) (simp add: x)
  with x show "Gamma x \<ge> exp c * x powr (x - 1/2) / exp x"
    by (simp add: Gamma_real_pos_exp exp_add exp_diff powr_def del: exp_le_cancel_iff)
next
  have "exp (ln_Gamma x) \<le> exp (c + (x - 1/2) * ln x - x + 1/(12*x))"
    by (subst exp_le_cancel_iff, rule ln_Gamma_bounds_aux) (simp add: x)
  with x show "Gamma x \<le> exp c * x powr (x - 1/2) / exp x * exp (1/(12*x))"
    by (simp add: Gamma_real_pos_exp exp_add exp_diff powr_def del: exp_le_cancel_iff)
qed

private lemma Gamma_asymp_equiv_aux: 
  "Gamma \<sim>[at_top] (\<lambda>x. exp c * x powr (x - 1/2) / exp x)"
proof (rule asymp_equiv_sandwich)
  include asymp_equiv_notation
  show "eventually (\<lambda>x. exp c * x powr (x - 1/2) / exp x \<le> Gamma x) at_top"
       "eventually (\<lambda>x. exp c * x powr (x - 1/2) / exp x * exp (1/(12*x)) \<ge> Gamma x) at_top"
    using eventually_ge_at_top[of "1::real"]
    by (eventually_elim; use Gamma_bounds_aux in force)+
  have "((\<lambda>x::real. exp (1 / (12 * x))) \<longlongrightarrow> exp 0) at_top"
    by (rule tendsto_intros real_tendsto_divide_at_top filterlim_tendsto_pos_mult_at_top)+
       (simp_all add: filterlim_ident)
  hence "(\<lambda>x. exp (1 / (12 * x))) \<sim> (\<lambda>x. 1 :: real)"
    by (intro asymp_equivI') simp_all
  hence "(\<lambda>x. exp c * x powr (x - 1 / 2) / exp x * 1) \<sim>
          (\<lambda>x. exp c * x powr (x - 1 / 2) / exp x * exp (1 / (12 * x)))"
    by (intro asymp_equiv_mult asymp_equiv_refl) (simp add: asymp_equiv_sym)
  thus "(\<lambda>x. exp c * x powr (x - 1 / 2) / exp x) \<sim>
          (\<lambda>x. exp c * x powr (x - 1 / 2) / exp x * exp (1 / (12 * x)))" by simp
qed simp_all

private lemma exp_1_powr_real [simp]: "exp (1::real) powr x = exp x"
  by (simp add: powr_def)

private lemma fact_asymp_equiv_aux:
  "fact \<sim>[at_top] (\<lambda>x. exp c * sqrt (real x) * (real x / exp 1) powr real x)"
proof -
  include asymp_equiv_notation
  have "fact \<sim> (\<lambda>n. Gamma (real (Suc n)))" by (simp add: Gamma_fact)
  also have "eventually (\<lambda>n. Gamma (real (Suc n)) = real n * Gamma (real n)) at_top"
    using eventually_gt_at_top[of "0::nat"]
    by eventually_elim (insert Gamma_plus1[of "real n" for n], 
                        auto simp: add_ac of_nat_in_nonpos_Ints_iff)
  also have "(\<lambda>n. Gamma (real n)) \<sim> (\<lambda>n. exp c * real n powr (real n - 1/2) / exp (real n))"
    by (rule asymp_equiv_compose'[OF Gamma_asymp_equiv_aux] filterlim_real_sequentially)+
  also have "eventually (\<lambda>n. real n * (exp c * real n powr (real n - 1 / 2) / exp (real n)) =
               exp c * sqrt (real n) * (real n / exp 1) powr real n) at_top"
    using eventually_gt_at_top[of "0::nat"]
  proof eventually_elim
    fix n :: nat assume n: "n > 0"
    thus "real n * (exp c * real n powr (real n - 1 / 2) / exp (real n)) =
            exp c * sqrt (real n) * (real n / exp 1) powr real n"
      by (subst powr_diff) (simp_all add: powr_divide powr_half_sqrt field_simps)
  qed
  finally show ?thesis by - (simp_all add: asymp_equiv_mult)
qed

text \<open>
  We still need to determine the constant term @{term c}, which we do using Wallis' 
  product formula: $$\prod_{n=1}^\infty \frac{4n^2}{4n^2-1} = \frac{\pi}{2}$$
\<close>
private lemma powr_mult_2: "(x::real) > 0 \<Longrightarrow> x powr (y * 2) = (x^2) powr y"
  by (subst mult.commute, subst powr_powr [symmetric]) (simp add: powr_numeral)

private lemma exp_mult_2: "exp (y * 2 :: real) = exp y * exp y"
  by (subst exp_add [symmetric]) simp

private lemma exp_c: "exp c = sqrt (2*pi)"
proof -
  include asymp_equiv_notation
  define p where "p = (\<lambda>n. \<Prod>k=1..n. (4*real k^2) / (4*real k^2 - 1))"

  have p_0 [simp]: "p 0 = 1" by (simp add: p_def)
  have p_Suc: "p (Suc n) = p n * (4 * real (Suc n)^2) / (4 * real (Suc n)^2 - 1)"
    for n unfolding p_def by (subst prod.nat_ivl_Suc') simp_all
  have p: "p = (\<lambda>n. 16 ^ n * fact n ^ 4 / (fact (2 * n))\<^sup>2 / (2 * real n + 1))"
  proof
    fix n :: nat
    have "p n = (\<Prod>k=1..n. (2*real k)^2 / (2*real k - 1) / (2 * real k + 1))"
      unfolding p_def by (intro prod.cong refl) (simp add: field_simps power2_eq_square)
    also have "\<dots> = (\<Prod>k=1..n. (2*real k)^2 / (2*real k - 1)) / (\<Prod>k=1..n. (2 * real (Suc k) - 1))"
      by (simp add: prod_dividef prod.distrib add_ac)
    also have "(\<Prod>k=1..n. (2 * real (Suc k) - 1)) = (\<Prod>k=Suc 1..Suc n. (2 * real k - 1))"
      by (subst prod.atLeast_Suc_atMost_Suc_shift) simp_all
    also have "\<dots> = (\<Prod>k=1..n. (2 * real k - 1)) * (2 * real n + 1)"
      by (induction n) (simp_all add: prod.nat_ivl_Suc')
    also have "(\<Prod>k = 1..n. (2 * real k)\<^sup>2 / (2 * real k - 1)) / \<dots> =
                 (\<Prod>k = 1..n. (2 * real k)^2 / (2 * real k - 1)^2) / (2 * real n + 1)"
      unfolding power2_eq_square by (simp add: prod.distrib prod_dividef)
    also have "(\<Prod>k = 1..n. (2 * real k)^2 / (2 * real k - 1)^2) =
                 (\<Prod>k = 1..n. (2 * real k)^4 / ((2*real k)*(2 * real k - 1))^2)"
      by (rule prod.cong) (simp_all add: power2_eq_square eval_nat_numeral)
    also have "\<dots> = 16^n * fact n^4 / (\<Prod>k=1..n. (2*real k) * (2*real k - 1))^2"
      by (simp add: prod.distrib prod_dividef fact_prod
            prod_power_distrib [symmetric] prod_constant)
    also have "(\<Prod>k=1..n. (2*real k) * (2*real k - 1)) = fact (2*n)"
      by (induction n) (simp_all add: algebra_simps prod.nat_ivl_Suc')
    finally show "p n = 16 ^ n * fact n ^ 4 / (fact (2 * n))\<^sup>2 / (2 * real n + 1)" .
  qed

  have "p \<sim> (\<lambda>n. 16 ^ n * fact n ^ 4 / (fact (2 * n))\<^sup>2 / (2 * real n + 1))"
    by (simp add: p)
  also have "\<dots> \<sim> (\<lambda>n. 16^n * (exp c * sqrt (real n) * (real n / exp 1) powr real n)^4 /
                       (exp c * sqrt (real (2*n)) * (real (2*n) / exp 1) powr real (2*n))^2 /
                       (2 * real n + 1))" (is "_ \<sim> ?f")
    by (intro asymp_equiv_mult asymp_equiv_divide asymp_equiv_refl mult_nat_left_at_top
              fact_asymp_equiv_aux asymp_equiv_power asymp_equiv_compose'[OF fact_asymp_equiv_aux]) 
       simp_all
  also have "eventually (\<lambda>n. \<dots> n = exp c ^ 2 / (4 + 2/n)) at_top"
    using eventually_gt_at_top[of "0::nat"]
  proof eventually_elim
    fix n :: nat assume n: "n > 0"
    have [simp]: "16^n = 4^n * (4^n :: real)" by (simp add: power_mult_distrib [symmetric])
    from n have "?f n = exp c ^ 2 * (n / (2*(2*n+1)))"
      by (simp add: power_mult_distrib divide_simps powr_mult real_sqrt_power_even)
         (simp add: field_simps power2_eq_square eval_nat_numeral powr_mult_2 
                    exp_mult_2 powr_realpow)
    also from n have "\<dots> = exp c ^ 2 / (4 + 2/n)" by (simp add: field_simps)
    finally show "?f n = \<dots>" .
  qed
  also have "(\<lambda>x. 4 + 2 / real x) \<sim> (\<lambda>x. 4)"
    by (subst asymp_equiv_add_right) auto
  finally have "p \<longlonglongrightarrow> exp c ^ 2 / 4" 
    by (rule asymp_equivD_const) (simp_all add: asymp_equiv_divide)
  moreover have "p \<longlonglongrightarrow> pi / 2" unfolding p_def by (rule wallis)
  ultimately have "exp c ^ 2 / 4 = pi / 2" by (rule LIMSEQ_unique)
  hence "2 * pi = exp c ^ 2" by simp
  also have "sqrt (exp c ^ 2) = exp c" by simp
  finally show "exp c = sqrt (2 * pi)" ..
qed

private lemma c: "c = ln (2*pi) / 2"
proof -
  note exp_c [symmetric]
  also have "ln (exp c) = c" by simp
  finally show ?thesis by (simp add: ln_sqrt)
qed


text \<open>
  This gives us the final bounds:
\<close>
theorem Gamma_bounds:
  assumes "x \<ge> 1"
  shows   "Gamma x \<ge> sqrt (2*pi/x) * (x / exp 1) powr x" (is ?th1)
          "Gamma x \<le> sqrt (2*pi/x) * (x / exp 1) powr x * exp (1 / (12 * x))" (is ?th2)
proof -
  from assms have "exp c * x powr (x - 1/2) / exp x = sqrt (2*pi/x) * (x / exp 1) powr x"
    by (subst powr_diff)
       (simp add: exp_c real_sqrt_divide powr_divide powr_half_sqrt field_simps)
  with Gamma_bounds_aux[OF assms] show ?th1 ?th2 by simp_all
qed

theorem ln_Gamma_bounds:
  assumes "x \<ge> 1"
  shows   "ln_Gamma x \<ge> ln (2*pi/x) / 2 + x * ln x - x" (is ?th1)
          "ln_Gamma x \<le> ln (2*pi/x) / 2 + x * ln x - x + 1/(12*x)" (is ?th2)
proof -
  from ln_Gamma_bounds_aux[OF assms] assms show ?th1 ?th2
    by (simp_all add: c field_simps ln_div)
  from assms have "exp c * x powr (x - 1/2) / exp x = sqrt (2*pi/x) * (x / exp 1) powr x"
    by (subst powr_diff)
       (simp add: exp_c real_sqrt_divide powr_divide powr_half_sqrt field_simps)
qed

theorem fact_bounds:
  assumes "n > 0"
  shows   "(fact n :: real) \<ge> sqrt (2*pi*n) * (n / exp 1) ^ n" (is ?th1)
          "(fact n :: real) \<le> sqrt (2*pi*n) * (n / exp 1) ^ n * exp (1 / (12 * n))" (is ?th2)
proof -
  from assms have n: "real n \<ge> 1" by simp
  from assms Gamma_plus1[of "real n"]
    have "real n * Gamma (real n) = Gamma (real (Suc n))" 
    by (simp add: of_nat_in_nonpos_Ints_iff add_ac)
  also have "Gamma (real (Suc n)) = fact n" by (subst Gamma_fact [symmetric]) simp
  finally have *: "fact n = real n * Gamma (real n)" by simp
  
  have "2*pi/n = 2*pi*n / n^2" by (simp add: power2_eq_square)
  also have "sqrt \<dots> = sqrt (2*pi*n) / n" by (subst real_sqrt_divide) simp_all
  also have "real n * \<dots> = sqrt (2*pi*n)" by simp
  finally have **: "real n * sqrt (2*pi/real n) = sqrt (2*pi*real n)" .

  note *
  also note Gamma_bounds(2)[OF n]
  also have "real n * (sqrt (2 * pi / real n) * (real n / exp 1) powr real n * 
                  exp (1 / (12 * real n))) = 
               (real n * sqrt (2*pi/n)) * (n / exp 1) powr n * exp (1 / (12 * n))" 
    by (simp add: algebra_simps)
  also from n have "(real n / exp 1) powr real n = (real n / exp 1) ^ n"
    by (subst powr_realpow) simp_all
  also note **
  finally show ?th2 by - (insert assms, simp_all)

  have "sqrt (2*pi*n) * (n / exp 1) powr n = n * (sqrt (2*pi/n) * (n / exp 1) powr n)"
    by (subst ** [symmetric]) (simp add: field_simps)
  also from assms have "\<dots> \<le> real n * Gamma (real n)"
    by (intro mult_left_mono Gamma_bounds(1)) simp_all
  also from n have "(real n / exp 1) powr real n = (real n / exp 1) ^ n"
    by (subst powr_realpow) simp_all
  also note * [symmetric]
  finally show ?th1 .
qed

theorem ln_fact_bounds:
  assumes "n > 0"
  shows   "ln (fact n :: real) \<ge> ln (2*pi*n)/2 + n * ln n - n" (is ?th1)
          "ln (fact n :: real) \<le> ln (2*pi*n)/2 + n * ln n - n + 1/(12*real n)" (is ?th2)
proof -
  have "ln (fact n :: real) \<ge> ln (sqrt (2*pi*real n)*(real n/exp 1)^n)"
    using fact_bounds(1)[OF assms] assms by (subst ln_le_cancel_iff) auto
  also from assms have "ln (sqrt (2*pi*real n)*(real n/exp 1)^n) = ln (2*pi*n)/2 + n * ln n - n"
    by (simp add: ln_mult ln_div ln_realpow ln_sqrt field_simps)
  finally show ?th1 .
next
  have "ln (fact n :: real) \<le> ln (sqrt (2*pi*real n) * (real n/exp 1)^n * exp (1/(12*real n)))"
    using fact_bounds(2)[OF assms] assms by (subst ln_le_cancel_iff) auto
  also from assms have "\<dots> = ln (2*pi*n)/2 + n * ln n - n + 1/(12*real n)" 
    by (simp add: ln_mult ln_div ln_realpow ln_sqrt field_simps)
  finally show ?th2 .
qed

theorem Gamma_asymp_equiv: 
  "Gamma \<sim>[at_top] (\<lambda>x. sqrt (2*pi/x) * (x / exp 1) powr x :: real)"
proof -
  note Gamma_asymp_equiv_aux
  also have "eventually (\<lambda>x. exp c * x powr (x - 1/2) / exp x = 
               sqrt (2*pi/x) * (x / exp 1) powr x) at_top"
    using eventually_gt_at_top[of "0::real"]
  proof eventually_elim
    fix x :: real assume x: "x > 0"
    thus "exp c * x powr (x - 1/2) / exp x = sqrt (2*pi/x) * (x / exp 1) powr x"
      by (subst powr_diff) 
         (simp add: exp_c powr_half_sqrt powr_divide field_simps real_sqrt_divide)
  qed
  finally show ?thesis .
qed

theorem fact_asymp_equiv: 
  "fact \<sim>[at_top] (\<lambda>n. sqrt (2*pi*n) * (n / exp 1) ^ n :: real)"
proof -
  note fact_asymp_equiv_aux
  also have "eventually (\<lambda>n. exp c * sqrt (real n) = sqrt (2 * pi * real n)) at_top"
    using eventually_gt_at_top[of "0::nat"] by eventually_elim (simp add: exp_c real_sqrt_mult)
  also have "eventually (\<lambda>n. (n / exp 1) powr n = (n / exp 1) ^ n) at_top"
    using eventually_gt_at_top[of "0::nat"] by eventually_elim (simp add: powr_realpow)
  finally show ?thesis .
qed

end

end
