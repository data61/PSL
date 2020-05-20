(*
  File:     Polya_Vinogradov.thy
  Authors:  Rodrigo Raya, EPFL; Manuel Eberl, TUM

  The Pólya–Vinogradov inequality, both the general case and the stronger variant for
  primitive characters.
*)
section \<open>The Pólya--Vinogradov Inequality\<close>
theory Polya_Vinogradov
imports
  Gauss_Sums
  "Dirichlet_Series.Divisor_Count"
begin

unbundle no_vec_lambda_notation

subsection \<open>The case of primitive characters\<close>

text \<open>
  We first prove a stronger variant of the Pólya--Vinogradov inequality for primitive characters.
  The fully general variant will then simply be a corollary of this. First, we need some bounds on
  logarithms, exponentials, and the harmonic numbers:
\<close>

(* TODO: Move? *)
lemma ln_add_one_self_less_self:
  fixes x :: real
  assumes "x > 0" 
  shows "ln (1 + x) < x"
proof -
  have "0 \<le> x" "0 < x" "exp x > 0" "1+x > 0" using assms by simp+
  have "1 + x < 1 + x + x\<^sup>2 / 2"
    using \<open>0 < x\<close> by auto
  also have "\<dots> \<le> exp x"
    using exp_lower_Taylor_quadratic[OF \<open>0 \<le> x\<close>] by blast
  finally have "1 + x < exp (x)" by blast
  then have "ln (1 + x) < ln (exp (x))" 
    using ln_less_cancel_iff[OF \<open>1+x > 0\<close> \<open>exp(x) > 0\<close>] by auto
  also have "\<dots> = x" using ln_exp by blast
  finally show ?thesis by auto
qed

lemma exp_1_bounds:
  assumes "x > (0::real)"
  shows   "exp 1 > (1 + 1 / x) powr x" and "exp 1 < (1 + 1 / x) powr (x+1)"
proof -
  have "ln (1 + 1 / x) < 1 / x"
    using ln_add_one_self_less_self assms by simp
  thus "exp 1 > (1 + 1 / x) powr x" using assms
    by (simp add: field_simps powr_def)
next
  have "1 < (x + 1) * ln ((x + 1) / x)" (is "_ < ?f x")
  proof (rule DERIV_neg_imp_decreasing_at_top[where ?f = ?f])
    fix t assume t: "x \<le> t"
    have "(?f has_field_derivative (ln (1 + 1 / t) - 1 / t)) (at t)"
      using t assms by (auto intro!: derivative_eq_intros simp:divide_simps)
    moreover have "ln (1 + 1 / t) - 1 / t < 0"
      using ln_add_one_self_less_self[of "1 / t"] t assms by auto
    ultimately show "\<exists>y. ((\<lambda>t. (t + 1) * ln ((t + 1) / t)) has_real_derivative y) (at t) \<and> y < 0"
      by blast
  qed real_asymp
  thus "exp 1 < (1 + 1 / x) powr (x + 1)"
    using assms by (simp add: powr_def field_simps)
qed

lemma harm_aux_ineq_1:
  fixes k :: real
  assumes "k > 1"
  shows "1 / k < ln (1 + 1 / (k - 1))" 
proof -   
  have "k-1 > 0" \<open>k > 0\<close> using assms by simp+
  from exp_1_bounds(2)[OF \<open>k-1 > 0\<close>]
  have "exp 1 < (1 + 1 / (k - 1)) powr k" by simp
  then have n_z: "(1 + 1 / (k - 1)) powr k > 0" 
      using assms not_exp_less_zero by auto
  
  have "(1::real) = ln (exp(1))" using ln_exp by auto
  also have "\<dots> < ln ((1 + 1 / (k - 1)) powr k)"
    using ln_less_cancel_iff[of "exp(1)",simplified,OF \<open>(1 + 1 / (k - 1)) powr k > 0\<close>]
          exp_1_bounds[OF \<open>k - 1 > 0\<close>] by simp
  also have "\<dots> = k * ln (1 + 1 / (k - 1))" 
    using ln_powr n_z by simp
  finally have "1 < k * ln (1 + 1 / (k - 1))" 
    by blast
  then show ?thesis using assms by (simp add: field_simps)
qed

lemma harm_aux_ineq_2_lemma:
  assumes "x \<ge> (0::real)"
  shows   "1 < (x + 1) * ln (1 + 2 / (2 * x + 1))"
proof -
  have "0 < ln (1+2/(2*x+1)) - 1 / (x + 1)" (is "_ < ?f x")
  proof (rule DERIV_neg_imp_decreasing_at_top[where ?f = ?f])
    fix t assume t: "x \<le> t"
    from assms t have "3 + 8 * t + 4 * t^2 > 0"
      by (intro add_pos_nonneg) auto
    hence *: "3 + 8 * t + 4 * t^2 \<noteq> 0"
      by auto
    have "(?f has_field_derivative (-1 / ((1 + t)^2 * (3 + 8 * t + 4 * t ^ 2)))) (at t)"
      apply (insert assms t *, (rule derivative_eq_intros refl | simp add: add_pos_pos)+)
      apply (auto simp: divide_simps)
      apply (auto simp: algebra_simps power2_eq_square)
      done
    moreover have "-1 / ((1 + t)^2 * (3 + 8 * t + 4 * t^2)) < 0"
      using t assms by (intro divide_neg_pos mult_pos_pos add_pos_nonneg) auto
    ultimately show "\<exists>y. (?f has_real_derivative y) (at t) \<and> y < 0"
      by blast
  qed real_asymp
  thus "1 < (x + 1) * ln (1+2/(2*x+1))"
    using assms by (simp add: field_simps)
qed

lemma harm_aux_ineq_2:
  fixes k :: real
  assumes "k \<ge> 1"
  shows   "1 / (k + 1) < ln (1 + 2 / (2 * k + 1))" 
proof -
  have "k > 0" using assms by auto
  have "1 < (k + 1) * ln (1 + 2 / (2 * k + 1))"
    using harm_aux_ineq_2_lemma assms by simp
  then show ?thesis 
    by (simp add: \<open>0 < k\<close> add_pos_pos mult.commute mult_imp_div_pos_less)
qed

lemma nat_0_1_induct [case_names 0 1 step]:
  assumes "P 0" "P 1" "\<And>n. n \<ge> 1 \<Longrightarrow> P n \<Longrightarrow> P (Suc n)"
  shows   "P n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case 
    using assms(3)[OF _ less.IH[of "n - 1"]]
    by (cases "n \<le> 1")
      (insert assms(1-2),auto simp: eval_nat_numeral le_Suc_eq)
qed

lemma harm_less_ln:
  fixes m :: nat
  assumes "m > 0"
  shows   "harm m < ln (2 * m + 1)" 
  using assms
proof (induct m rule: nat_0_1_induct)
  case 0
  then show ?case by blast
next
  case 1
  have "harm 1 = (1::real)" unfolding harm_def by simp
  have "harm 1 < ln (3::real)" 
    by (subst \<open>harm 1 = 1\<close>,subst ln3_gt_1,simp)
  then show ?case by simp
next
  case (step n)
  have "harm (n+1) = harm n + 1/(n+1)"
    by ((subst Suc_eq_plus1[symmetric])+,subst harm_Suc,subst inverse_eq_divide,blast)
  also have "\<dots> < ln (real (2 * n + 1)) + 1/(n+1)"
    using step(1-2) by auto
  also have "\<dots> < ln (real (2 * n + 1)) + ln (1+2/(2*n+1))"
  proof -
    from step(1) have "real n \<ge> 1" by simp
    have "1 / real (n + 1) < ln (1 + 2 / real (2 * n + 1))"
      using harm_aux_ineq_2[OF \<open>1 \<le> (real n)\<close>]  by (simp add: add.commute)
    then show ?thesis by auto
  qed
  also have "\<dots> = ln ((2 * n + 1) * (1+2/(2*n+1)))"
    by (rule ln_mult[symmetric],simp,simp add: field_simps)
  also have "\<dots> = ln (2*(n+1)+1)"
  proof -
    have "(2 * n + 1) * (1+2/(2*n+1)) = 2*(n+1)+1"
      by (simp add: field_simps)
    then show ?thesis by presburger
  qed
  finally show ?case by simp
qed
(* END TODO *)
  

text\<open>Theorem 8.21\<close>
theorem (in primitive_dchar) polya_vinogradov_inequality_primitive:
  fixes x :: nat
  shows "norm (\<Sum>m=1..x. \<chi> m) < sqrt n * ln n"
proof -
  define \<tau> :: complex where "\<tau> = gauss_sum 1 div sqrt n"
  have \<tau>_mod: "norm \<tau> = 1" using fourier_primitive(2)
    by (simp add: \<tau>_def)
  {
    fix m
    have "\<chi> m = (\<tau> div sqrt n) * (\<Sum>k = 1..n. (cnj (\<chi> k)) * unity_root n (-m*k))"
    using fourier_primitive(1)[of m] \<tau>_def by blast}
    note chi_expr = this
    have "(\<Sum>m = 1..x. \<chi>(m)) = (\<Sum>m = 1..x. (\<tau> div sqrt n) * (\<Sum>k = 1..n. (cnj (\<chi> k)) * unity_root n (-m*k)))"
      by(rule sum.cong[OF refl]) (use chi_expr in blast)
    also have "\<dots> = (\<Sum>m = 1..x. (\<Sum>k = 1..n. (\<tau> div sqrt n) * ((cnj (\<chi> k)) * unity_root n (-m*k))))"
      by (rule sum.cong,simp,simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>k = 1..n. (\<Sum>m = 1..x. (\<tau> div sqrt n) * ((cnj (\<chi> k)) * unity_root n (-m*k))))"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>k = 1..n. (\<tau> div sqrt n) *  (cnj (\<chi> k) * (\<Sum>m = 1..x. unity_root n (-m*k))))"
      by (rule sum.cong,simp,simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>k = 1..<n. (\<tau> div sqrt n) * (cnj (\<chi> k) * (\<Sum>m = 1..x. unity_root n (-m*k))))"
      using n by (intro sum.mono_neutral_right) (auto intro: eq_zero)
    also have "\<dots> = (\<tau> div sqrt n) * (\<Sum>k = 1..<n. (cnj (\<chi> k) * (\<Sum>m = 1..x. unity_root n (-m*k))))"
      by (simp add: sum_distrib_left)
    finally have "(\<Sum>m = 1..x. \<chi>(m)) = (\<tau> div sqrt n) * (\<Sum>k = 1..<n. (cnj (\<chi> k) * (\<Sum>m = 1..x. unity_root n (-m*k))))"
      by blast
    hence eq: "sqrt n * (\<Sum>m=1..x. \<chi>(m)) = \<tau> * (\<Sum>k=1..<n. (cnj (\<chi> k) * (\<Sum>m=1..x. unity_root n (-m*k))))"
      by auto
    define f where "f = (\<lambda>k. (\<Sum>m = 1..x. unity_root n (-m*k)))"
    
    hence "(sqrt n) * norm(\<Sum>m = 1..x. \<chi>(m)) = norm(\<tau> * (\<Sum>k=1..<n. (cnj (\<chi> k) * (\<Sum>m = 1..x. unity_root n (-m*k)))))"
    proof -
      have "norm(sqrt n * (\<Sum>m=1..x. \<chi>(m))) = norm (sqrt n) * norm((\<Sum>m = 1..x. \<chi>(m)))"
        by (simp add: norm_mult)
      also have "\<dots> = (sqrt n) * norm((\<Sum>m = 1..x. \<chi>(m)))"
        by simp
      finally have 1: "norm((sqrt n) * (\<Sum>m = 1..x. \<chi>(m))) = (sqrt n) * norm((\<Sum>m = 1..x. \<chi>(m)))"
        by blast
      then show ?thesis using eq by algebra
    qed
    also have "\<dots> = norm (\<Sum>k = 1..<n. (cnj (\<chi> k) * (\<Sum>m = 1..x. unity_root n (-m*k))))"
      by (simp add: norm_mult \<tau>_mod)
    also have "\<dots> \<le> (\<Sum>k = 1..<n. norm (cnj (\<chi> k) * (\<Sum> m = 1..x. unity_root n (-m*k))))"
      using norm_sum by blast
    also have "\<dots> = (\<Sum>k = 1..<n. norm (cnj (\<chi> k)) * norm((\<Sum> m = 1..x. unity_root n (-m*k))))"
      by (rule sum.cong,simp, simp add: norm_mult)
    also have "\<dots> \<le> (\<Sum>k = 1..<n. norm((\<Sum>m = 1..x. unity_root n (-m*k))))"
    proof -
      show ?thesis
      proof (rule sum_mono)
        fix k
        assume "k \<in> {1..<n}" 
        define sum_aux :: real where "sum_aux = norm (\<Sum>m=1..x. unity_root n (- int m * int k))"
        have "sum_aux \<ge> 0" unfolding sum_aux_def by auto
        have "norm (cnj (\<chi> k)) \<le> 1" using norm_le_1[of k] by simp
        then have "norm (cnj (\<chi> k)) * sum_aux \<le> 1 * sum_aux"
          using \<open>sum_aux \<ge> 0\<close> by (simp add: mult_left_le_one_le)
        then show " norm (cnj (\<chi> k)) *
           norm (\<Sum>m = 1..x. unity_root n (- int m * int k))
           \<le> norm (\<Sum>m = 1..x. unity_root n (- int m * int k))"
          unfolding sum_aux_def by argo
      qed
    qed
    also have "\<dots> = (\<Sum>k = 1..<n. norm(f k))"
      using f_def by blast
    finally have 24: "(sqrt n) * norm(\<Sum>m = 1..x. \<chi>(m)) \<le> (\<Sum>k = 1..<n. norm(f k))"
      by blast
    
    {
      fix k :: int
      have "f(n-k) = cnj(f(k))"
      proof -
        have "f(n-k) = (\<Sum>m = 1..x. unity_root n (-m*(n-k)))"
          unfolding f_def by blast
        also have "\<dots> = (\<Sum>m = 1..x. unity_root n (m*k))"
        proof (rule sum.cong,simp)
          fix xa
          assume "xa \<in> {1..x}" 
          have "(k * int xa - int n * int xa) mod int n = (k * int xa - 0) mod int n"
            by (intro mod_diff_cong) auto
          thus "unity_root n (-int xa * (int n - k)) = unity_root n (int xa * k)"
            unfolding ring_distribs by (intro unity_root_cong) (auto simp: cong_def algebra_simps)
        qed
        also have "\<dots> = cnj(f(k))"
        proof -
          have "cnj(f(k)) = cnj (\<Sum>m = 1..x. unity_root n (- int m * k))"
            unfolding f_def by blast
          also have "cnj (\<Sum>m = 1..x. unity_root n (- int m * k)) = 
                (\<Sum>m = 1..x. cnj(unity_root n (- int m * k)))"
            by (rule cnj_sum)
          also have "\<dots> = (\<Sum>m = 1..x. unity_root n (int m * k))"
            by (intro sum.cong) (auto simp: unity_root_uminus)
          finally show ?thesis by auto
        qed
        finally show "f(n-k) = cnj(f(k))" by blast      
      qed
      hence "norm(f(n-k)) = norm(cnj(f(k)))" by simp
      hence "norm(f(n-k)) = norm(f(k))" by auto
    }
    note eq = this
    have 25: 
      "odd n \<Longrightarrow> (\<Sum>k = 1..n - 1. norm (f (int k))) \<le>
                    2 * (\<Sum>k = 1..(n-1) div 2. norm (f (int k)))" 
      "even n \<Longrightarrow> (\<Sum>k = 1..n - 1. norm (f (int k))) \<le>
                    2 * (\<Sum>k = 1..(n-2) div 2. norm (f (int k))) + norm(f(n div 2))"
    proof -
      assume "odd n" 
      define g where "g = (\<lambda>k. norm (f k))"
      have "(n-1) div 2  = n div 2" using \<open>odd n\<close> n 
        using div_mult_self1_is_m[OF pos2,of "n-1"] 
              odd_two_times_div_two_nat[OF \<open>odd n\<close>] by linarith      
      have "(\<Sum>i=1..n-1. g i) = (\<Sum>i\<in>{1..n div 2}\<union>{n div 2<..n-1}. g i)"
        using n by (intro sum.cong,auto) 
      also have "\<dots> = (\<Sum>i\<in>{1..n div 2}. g i) + (\<Sum>i\<in>{n div 2<..n-1}. g i)"
        by (subst sum.union_disjoint,auto)
      also have "(\<Sum>i\<in>{n div 2<..n-1}. g i) = (\<Sum>i\<in>{1..n - (n div 2 + 1)}. g (n - i))"
        by (rule sum.reindex_bij_witness[of _ "\<lambda>i. n - i" "\<lambda>i. n - i"],auto) 
      also have "\<dots> \<le> (\<Sum>i\<in>{1..n div 2}. g (n - i))"
        by (intro sum_mono2,simp,auto simp add: g_def)
      finally have 1: "(\<Sum>i=1..n-1. g i) \<le> (\<Sum>i=1..n div 2. g i + g (n - i))"
        by (simp add: sum.distrib)
      have "(\<Sum>i=1..n div 2. g i + g (n - i)) = (\<Sum>i=1..n div 2. 2 * g i)"
        unfolding g_def
        apply(rule sum.cong,simp)
        using eq int_ops(6) by force
      also have "\<dots> = 2 * (\<Sum>i=1..n div 2. g i)"
        by (rule sum_distrib_left[symmetric])
      finally have 2: "(\<Sum>i=1..n div 2. g i + g (n - i)) = 2 * (\<Sum>i=1..n div 2. g i)"
        by blast
      from 1 2 have "(\<Sum>i=1..n-1. g i) \<le> 2 * (\<Sum>i=1..n div 2. g i)" by algebra
      then show "(\<Sum>n = 1..n - 1. norm (f (int n))) \<le> 2 * (\<Sum>n = 1..(n-1) div 2. norm (f (int n)))" 
        unfolding g_def \<open>(n-1) div 2 = n div 2\<close> by blast
    next
      assume "even n" 
      define g where "g = (\<lambda>n. norm (f (n)))"
      have "(n-2) div 2 = n div 2 - 1" using \<open>even n\<close> n by simp
      have "(\<Sum>i=1..n-1. g i) = (\<Sum>i\<in>{1..<n div 2}\<union> {n div 2} \<union> {n div 2<..n-1}. g i)"
        using n by (intro sum.cong,auto) 
      also have "\<dots> = (\<Sum>i\<in>{1..<n div 2}. g i) + (\<Sum>i\<in>{n div 2<..n-1}. g i) + g(n div 2)"
        by (subst sum.union_disjoint,auto)
      also have "(\<Sum>i\<in>{n div 2<..n-1}. g i) = (\<Sum>i\<in>{1..n - (n div 2+1)}. g (n - i))"
        by (rule sum.reindex_bij_witness[of _ "\<lambda>i. n - i" "\<lambda>i. n - i"],auto) 
      also have "\<dots> \<le> (\<Sum>i\<in>{1..<n div 2}. g (n - i))"
      proof (intro sum_mono2,simp)
        have "n - n div 2 = n div 2" using \<open>even n\<close> n by auto
        then have "n - (n div 2 + 1) < n div 2" 
          using n by (simp add: divide_simps)
        then show "{1..n - (n div 2 + 1)} \<subseteq> {1..<n div 2}" by fastforce
      qed auto
      finally have 1: "(\<Sum>i=1..n-1. g i) \<le> (\<Sum>i=1..<n div 2. g i + g (n - i)) + g(n div 2)"
        by (simp add: sum.distrib)
      have "(\<Sum>i=1..<n div 2. g i + g (n - i)) = (\<Sum>i=1..<n div 2. 2 * g i)"
        unfolding g_def
        apply(rule sum.cong,simp)
        using eq int_ops(6) by force
      also have "\<dots> = 2 * (\<Sum>i=1..<n div 2. g i)"
        by (rule sum_distrib_left[symmetric])
      finally have 2: "(\<Sum>i=1..<n div 2. g i + g (n - i)) = 2 * (\<Sum>i=1..<n div 2. g i)"
        by blast
      from 1 2 have 3: "(\<Sum>i=1..n-1. g i) \<le> 2 * (\<Sum>i=1..<n div 2. g i) + g(n div 2)" by algebra
      then have "(\<Sum>i=1..n-1. g i) \<le> 2 * (\<Sum>i=1..(n-2) div 2. g i) + g(n div 2)" 
      proof -
        have "{1..<n div 2} = {1..(n-2) div 2}" by auto
        then have "(\<Sum>i=1..<n div 2. g i) = (\<Sum>i=1..(n-2) div 2. g i)" 
          by (rule sum.cong,simp)
        then show ?thesis using 3 by presburger
      qed
      then show "(\<Sum>k = 1..n - 1. norm (f (int k))) \<le> 2 * (\<Sum>n = 1..(n-2) div 2. norm (f (int n))) + g(n div 2)" 
        unfolding g_def by blast
    qed
    
    (* expression for each f(n) *)
    {fix k :: int
    assume "1 \<le> k" "k \<le> n div 2" 
    have "k \<le> n - 1"
      using \<open>k \<le> n div 2\<close> n by linarith
    define y where "y = unity_root n (-k)"
    define z where "z = exp (-(pi*k/n)* \<i>)"
    have "z^2 = exp (2*(-(pi*k/n)* \<i>))"
      unfolding z_def using exp_double[symmetric] by blast
    also have "\<dots> = y"
      unfolding y_def unity_root_conv_exp by (simp add: algebra_simps)
    finally have z_eq: "y = z^2" by blast
    have z_not_0: "z \<noteq> 0" 
      using z_eq by (simp add: z_def)
    
    then have "y \<noteq> 1" 
      using unity_root_eq_1_iff_int \<open>1 \<le> k\<close> \<open>k \<le> n - 1\<close> not_less
            unity_root_eq_1_iff_int y_def zdvd_not_zless by auto
    
    have "f(k) = (\<Sum>m = 1..x . y^m)" 
      unfolding f_def y_def 
      by (subst unity_root_pow,rule sum.cong,simp,simp add: algebra_simps)
    also have sum: "\<dots> = (\<Sum>m = 1..<x+1 . y^m)"
      by (rule sum.cong,fastforce,simp)
    also have "\<dots> = (\<Sum>m = 0..<x+1 . y^m) - 1"
      by (subst (2) sum.atLeast_Suc_lessThan) auto
    also have "\<dots> = (y^(x+1) - 1) div (y - 1) - 1"
      using geometric_sum[OF \<open>y \<noteq> 1\<close>, of "x+1"] by (simp add: atLeast0LessThan)   
    also have "\<dots> = (y^(x+1) - 1 - (y-1)) div (y - 1)"
    proof -
      have "y - 1 \<noteq> 0" using \<open>y \<noteq> 1\<close> by simp
      show ?thesis
        using divide_diff_eq_iff[OF \<open>y - 1 \<noteq> 0\<close>, of "(y^(x+1) - 1)" 1] by auto
    qed
    also have "\<dots> = (y^(x+1) - y) div (y - 1)"
      by (simp add: algebra_simps)
    also have "\<dots> = y * (y^x - 1) div (y - 1)"
      by (simp add: algebra_simps)
    also have "\<dots> = z^2 * ((z^2)^x - 1) div (z^2 - 1)"
      unfolding z_eq by blast
    also have "\<dots> = z^2 * (z^(2*x) - 1) div (z^2 - 1)"
      by (subst power_mult[symmetric, of z 2 x],blast) 
    also have "\<dots> = z^(x+1)*((z ^x -inverse(z^x))) / (z - inverse(z))"
    proof -
      have "z^x \<noteq> 0" using z_not_0 by auto
      have 1: "z ^ (2 * x) - 1 = z^x*(z ^x -inverse(z^x))"
        by (simp add: semiring_normalization_rules(36) right_inverse[OF \<open>z^x \<noteq> 0\<close>]  right_diff_distrib')
      have 2: "z\<^sup>2 - 1 = z*(z - inverse(z))" 
        by (simp add: right_diff_distrib' semiring_normalization_rules(29) right_inverse[OF \<open>z \<noteq> 0\<close>])
    
      have 3: "z\<^sup>2 * (z^x / z) = z^(x+1)"
      proof -
        have "z\<^sup>2 * (z^x / z) = z\<^sup>2 * (z^x * inverse z)"
          by (simp add: inverse_eq_divide)
        also have "\<dots> = z^(x+1)"
          by (simp add: algebra_simps power2_eq_square right_inverse[OF \<open>z \<noteq> 0\<close>])
        finally show ?thesis by blast
      qed
      have "z\<^sup>2 * (z ^ (2 * x) - 1) / (z\<^sup>2 - 1) =
            z\<^sup>2 * (z^x*(z ^x -inverse(z^x))) / (z*(z - inverse(z)))"
        by (subst 1, subst 2,blast) 
      also have "\<dots> =  (z\<^sup>2 * (z^x / z)) * ((z ^x -inverse(z^x))) / (z - inverse(z))"
        by simp
      also have "\<dots> = z^(x+1) *((z ^x -inverse(z^x))) / (z - inverse(z))"
        by (subst 3,simp) 
      finally show ?thesis by simp
    qed
    finally have "f(k) = z^(x+1) *((z ^x -inverse(z^x))) / (z - inverse(z))" by blast
    
    (* inequality for each f(k) *)
    then have "norm(f(k)) = norm(z^(x+1) * (((z ^x -inverse(z^x))) / (z - inverse(z))))" by auto
    also have "\<dots> = norm(z^(x+1)) * norm(((z ^x -inverse(z^x))) / (z - inverse(z)))"
      using norm_mult by blast
    also have "\<dots> = norm(((z ^x -inverse(z^x))) / (z - inverse(z)))"
    proof -
      have "norm(z) = 1" 
        unfolding z_def by auto
      have "norm(z^(x+1)) = 1"
        by (subst norm_power,simp add: \<open>norm(z) = 1\<close>)
      then show ?thesis by simp
    qed
    also have "\<dots> = norm((exp (-(x*pi*k/n)* \<i>) - exp ((x*pi*k/n)* \<i>)) div 
                     (exp (-(pi*k/n)* \<i>) - exp ((pi*k/n)* \<i>)))"
    proof -
      have 1: "z ^ x = exp (-(x*pi*k/n)* \<i>)"
        unfolding z_def
        by (subst exp_of_nat_mult[symmetric],simp add: algebra_simps)
      have "inverse (z ^ x) = inverse (exp (-(x*pi*k/n)* \<i>))"
        using \<open>z ^ x = exp (-(x*pi*k/n)* \<i>)\<close> by auto
      also have "\<dots> = (exp ((x*pi*k/n)* \<i>))"
        by (simp add: exp_minus)
      finally have 2: "inverse(z^x) = exp ((x*pi*k/n)* \<i>)" by simp
      have 3: "inverse z = exp ((pi*k/n)* \<i>)"
        by (simp add: exp_minus z_def)
      show ?thesis using 1 2 3 z_def by simp
    qed
    also have "\<dots> = norm((sin (x*pi*k/n)) div (sin (pi*k/n)))"
    proof -
      have num: "(exp (-(x*pi*k/n)* \<i>) - exp ((x*pi*k/n)* \<i>)) = (-2*\<i>* sin((x*pi*k/n)))" 
      proof -
        have 1: "exp (-(x*pi*k/n)* \<i>) = cos(-(x*pi*k/n)) + \<i> * sin(-(x*pi*k/n))"
                "exp ((x*pi*k/n)* \<i>) = cos((x*pi*k/n)) + \<i> * sin((x*pi*k/n))"
          using Euler Im_complex_of_real Im_divide_of_nat Im_i_times Re_complex_of_real
                complex_Re_of_int complex_i_mult_minus exp_zero mult.assoc mult.commute by force+
        have "(exp (-(x*pi*k/n)* \<i>) - exp ((x*pi*k/n)* \<i>)) =
              (cos(-(x*pi*k/n)) + \<i> * sin(-(x*pi*k/n))) -
              (cos((x*pi*k/n)) + \<i> * sin((x*pi*k/n)))"
          using 1 by argo
        also have "\<dots> = -2*\<i>* sin((x*pi*k/n))" by simp
        finally show ?thesis by blast  
      qed
    
      have den: "(exp (-(pi*k/n)* \<i>) - exp ((pi*k/n)* \<i>)) = -2*\<i>* sin((pi*k/n))"
      proof -
        have 1: "exp (-(pi*k/n)* \<i>) = cos(-(pi*k/n)) + \<i> * sin(-(pi*k/n))"
                "exp ((pi*k/n)* \<i>) = cos((pi*k/n)) + \<i> * sin((pi*k/n))"
          using Euler Im_complex_of_real Im_divide_of_nat Im_i_times Re_complex_of_real 
                complex_Re_of_int complex_i_mult_minus exp_zero mult.assoc mult.commute by force+
        have "(exp (-(pi*k/n)* \<i>) - exp ((pi*k/n)* \<i>)) =
              (cos(-(pi*k/n)) + \<i> * sin(-(pi*k/n))) -
              (cos((pi*k/n)) + \<i> * sin((pi*k/n)))"
          using 1 by argo
        also have "\<dots> = -2*\<i>* sin((pi*k/n))" by simp
        finally show ?thesis by blast  
      qed 
    
      have "norm((exp (-(x*pi*k/n)* \<i>) - exp ((x*pi*k/n)* \<i>)) div 
                     (exp (-(pi*k/n)* \<i>) - exp ((pi*k/n)* \<i>))) =
            norm((-2*\<i>* sin((x*pi*k/n))) div (-2*\<i>* sin((pi*k/n))))"
        using num den by presburger
      also have "\<dots> = norm(sin((x*pi*k/n)) div sin((pi*k/n)))"
        by (simp add: norm_divide)
      finally show ?thesis by blast
    qed
    also have "\<dots> = norm((sin (x*pi*k/n))) div norm((sin (pi*k/n)))"
      by (simp add: norm_divide)
    also have "\<dots> \<le> 1 div norm((sin (pi*k/n)))"
    proof -
      have "norm((sin (pi*k/n))) \<ge> 0" by simp
      have "norm (sin (x*pi*k/n)) \<le> 1" by simp
      then show ?thesis   
        using divide_right_mono[OF \<open>norm (sin (x*pi*k/n)) \<le> 1\<close> \<open>norm((sin (pi*k/n))) \<ge> 0\<close>]
        by blast
    qed
    finally have 26: "norm(f(k)) \<le> 1 div norm((sin (pi*k/n)))"
      by blast
    
    (* inequality with sin *)
    {
      fix t
      assume "t \<ge> 0" "t \<le> pi div 2"
      then have "t \<in> {0..pi div 2}" by auto 
      have "convex_on {0..pi/2} (\<lambda>x. -sin x)"
       by (rule convex_on_realI[where f' = "\<lambda>x. - cos x"])
          (auto intro!: derivative_eq_intros simp: cos_monotone_0_pi_le)
      from convex_onD_Icc'[OF this \<open>t \<in> {0..pi div 2}\<close>] have "sin(t) \<ge> (2 div pi)*t" by simp
    }
    note sin_ineq = this
    
    have sin_ineq_inst: "sin ((pi*k) / n) \<ge> (2 * k) / n"
    proof -
      have "pi / n \<ge> 0" by simp
      have 1: "(pi*k) / n \<ge> 0" using \<open>1 \<le> k\<close> by auto
      have "(pi*k)/n = (pi / n) * k" by simp
      also have "\<dots> \<le> (pi / n) * (n / 2)" 
        using mult_left_mono[of "k" "n / 2" "pi / n"] 
              \<open>k \<le> n div 2\<close> \<open>0 \<le> pi / real n\<close> by linarith
      also have "\<dots> \<le> pi / 2" 
        by (simp add: divide_simps)     
      finally have 2: "(pi*k)/n \<le> pi / 2" by auto
      
      have "(2 / pi) * (pi * k / n) \<le> sin((pi * k) / n)"
        using sin_ineq[OF 1 2] by blast
      then show "sin((pi * k) / n) \<ge> (2*k) / n" 
        by auto
    qed
    
    from 26 have "norm(f(k)) \<le> 1 div abs((sin (pi*k/n)))" by simp
    also have "\<dots> \<le> 1 / abs((2*k) / n)" 
    proof -
      have "sin (pi*k/n) \<ge> (2*k) / n" using sin_ineq_inst by simp
      moreover have "(2*k) / n > 0" using n \<open>1 \<le> k\<close> by auto
      ultimately have "abs((sin (pi*k/n))) \<ge> abs((2*k)/n)" by auto
      have "abs((2*k)/n) > 0" using \<open>(2*k)/n > 0\<close> by linarith
      then show "1 div abs((sin (pi*k/n))) \<le> 1 / abs(((2*k)/n))"
        using \<open>abs((2*k)/n) > 0\<close> \<open>abs((sin (pi*k/n))) \<ge> abs(((2*k)/n))\<close>
        by (intro frac_le) auto
    qed
    also have "\<dots> = n / (2*k)" using \<open>k \<ge> 1\<close> by simp
    finally have "norm(f(k)) \<le> n / (2*k)" by blast
  }
  note ineq = this

  (* inequality for the odd and even case*)
  have "sqrt n * norm (sum \<chi> {1..x}) < n * ln n"
  proof (cases "even n")
    case True
    have "norm (f(n div 2)) \<le> 1" 
    proof -
      have "int (n div 2) \<ge> 1" using n \<open>even n\<close> by auto
      show ?thesis
        using ineq[OF \<open>int (n div 2) \<ge> 1\<close>] True n by force
    qed
    from 24 have "sqrt n * norm (sum \<chi> {1..x}) 
               \<le> (\<Sum>k = 1..<n. norm (f (int k)))" by blast
    also have "\<dots> = (\<Sum>k = 1..n-1. norm (f (int k)))"
      by (intro sum.cong) auto
    also have "\<dots> \<le> 2 * (\<Sum>k = 1..(n - 2) div 2. norm (f (int k))) + norm(f(n div 2))"
      using 25(2)[OF True] by blast
    also have "\<dots> \<le>  real n * (\<Sum>k = 1..(n - 2) div 2. 1 / k) + norm(f(n div 2))"
    proof -
      have "(\<Sum>k = 1..(n - 2) div 2. norm (f (int k))) \<le> (\<Sum>k = 1..(n - 2) div 2. real n div (2*k))"
      proof (rule sum_mono)
        fix k
        assume "k \<in> {1..(n - 2) div 2}"
        then have "1 \<le> int k" "int k \<le> n div 2" by auto
        show "norm (f (int k)) \<le> real n / (2*k)" 
          using ineq[OF \<open>1 \<le> int k\<close> \<open>int k \<le> n div 2\<close>] by auto
      qed
      also have "\<dots> = (\<Sum>k = 1..(n - 2) div 2. (real n div 2) * (1 / k))"
        by (rule sum.cong,auto)
      also have "\<dots> = (real n div 2) * (\<Sum>k = 1..(n - 2) div 2. 1 / k)"
        using sum_distrib_left[symmetric] by fast
      finally have "(\<Sum>k = 1..(n - 2) div 2. norm (f (int k))) \<le> 
                  (real n div 2) * (\<Sum>k = 1..(n - 2) div 2. 1 / k)"
        by blast
      then show ?thesis by argo
    qed
    also have "\<dots> = real n * harm ((n - 2) div 2) + norm(f(n div 2))"
      unfolding harm_def inverse_eq_divide by simp
    also have "\<dots> < n * ln n"
    proof (cases "n = 2")   
      case True 
      have "real n * harm ((n - 2) div 2) + norm (f (int (n div 2))) \<le> 1" 
        using \<open>n = 2\<close> \<open>norm (f (int (n div 2))) \<le> 1\<close>
        unfolding harm_def by simp
      moreover have "real n * ln (real n) \<ge> 4 / 3" 
        using \<open>n = 2\<close> ln2_ge_two_thirds by auto
      ultimately show ?thesis by argo                
    next
      case False
      have "n > 3" using n \<open>n \<noteq> 2\<close> \<open>even n\<close> by auto
      then have "(n-2) div 2 > 0" by simp
      then have "harm ((n - 2) div 2) < ln (real (2 * ((n - 2) div 2) + 1))"
        using harm_less_ln by blast
      also have "\<dots> = ln (real (n - 1))" 
        using \<open>even n\<close> \<open>n > 3\<close> by simp      
      finally have 1: "harm ((n - 2) div 2) < ln (real (n - 1))"
        by blast
      then have "real n * harm ((n - 2) div 2) < real n * ln (real (n - 1))"
        using n by simp
      then have "real n * harm ((n - 2) div 2) + norm (f (int (n div 2)))
            < real n * ln (real (n - 1)) + 1"
        using \<open>norm (f (int (n div 2))) \<le> 1\<close> by argo
      also have "\<dots> = real n * ln (real (n - 1)) + real n * 1 / real n"
        using n by auto
      also have "\<dots> < real n * ln (real (n - 1)) + real n * ln (1 + 1 / (real n - 1))"
      proof -
        have "real n > 1" "real n > 0" using n by simp+
        then have "real n * (1 / real n) < real n * ln (1 + 1 / (real n - 1))"
          by (intro mult_strict_left_mono harm_aux_ineq_1) auto
        then show ?thesis by auto         
      qed
      also have "\<dots> = real n * ( ln (real (n - 1)) + ln (1 + 1 / (real n - 1)))"
        by argo
      also have "\<dots> = real n * ( ln (real (n - 1) * (1 + 1 / (real n - 1))))"
      proof -
        have "real (n - 1) > 0" "1 + 1 / (real n - 1) > 0"  
          using n by (auto simp add: add_pos_nonneg)
        show ?thesis 
          by (subst ln_mult [OF \<open>real (n - 1) > 0\<close> \<open>1 + 1 / (real n - 1) > 0\<close>,symmetric],blast)          
      qed
      also have "\<dots> = real n * ln n"
        using n by (auto simp add: divide_simps)
      finally show ?thesis by blast
    qed
    finally show ?thesis by blast
  next
    case False
    from 24 have "sqrt n * norm (sum \<chi> {1..x}) \<le> (\<Sum>k= 1..<n. norm (f (int k)))"
      by blast
    also have "\<dots> = (\<Sum>k= 1..n-1. norm (f (int k)))"
      by (intro sum.cong) auto
    also have "\<dots> \<le> 2 * (\<Sum>k = 1..(n - 1) div 2. norm (f (int k)))"
      using 25(1)[OF False] by blast
    also have "\<dots> \<le> real n * (\<Sum>k = 1..(n - 1) div 2. 1 / k)"
    proof -
      have "(\<Sum>k = 1..(n - 1) div 2. norm (f (int k))) \<le> (\<Sum>k = 1..(n - 1) div 2. real n div (2*k))"
      proof (rule sum_mono)
        fix k
        assume "k \<in> {1..(n - 1) div 2}"
        then have "1 \<le> int k" "int k \<le> n div 2" by auto
        show "norm (f (int k)) \<le> real n / (2*k)" 
          using ineq[OF \<open>1 \<le> int k\<close> \<open>int k \<le> n div 2\<close>] by auto
      qed
      also have "\<dots> = (\<Sum>k = 1..(n - 1) div 2. (n / 2) * (1 / k))"
        by (rule sum.cong,auto)
      also have "\<dots> = (n / 2) * (\<Sum>k = 1..(n - 1) div 2. 1 / k)"
        using sum_distrib_left[symmetric] by fast
      finally have "(\<Sum>k = 1..(n - 1) div 2. norm (f (int k))) \<le> 
                  (real n div 2) * (\<Sum>k = 1..(n - 1) div 2. 1 / k)"
        by blast
      then show ?thesis by argo
    qed
    also have "\<dots> = real n * harm ((n - 1) div 2)"
      unfolding harm_def inverse_eq_divide by simp
    also have "\<dots> < n * ln n"
    proof -
      have "n > 2" using n \<open>odd n\<close> by presburger
      then have "(n-1) div 2 > 0" by auto
      then have "harm ((n - 1) div 2) < ln (real (2 * ((n - 1) div 2) + 1))"
        using harm_less_ln by blast
      also have "\<dots> = ln (real n)" using \<open>odd n\<close> by simp
      finally show ?thesis using n by simp 
    qed
    finally show ?thesis by blast
  qed
  
  then have 1: "sqrt n * norm (sum \<chi> {1..x}) < n * ln n"
    by blast
  show  "norm (sum \<chi> {1..x}) < sqrt n * ln n"
  proof -
    have 2: "norm (sum \<chi> {1..x}) * sqrt n < n * ln n"
      using 1 by argo
    have "sqrt n > 0" using n by simp
    have 3: "(n * ln n) / sqrt n = sqrt n * ln n"
      using n by (simp add: field_simps)
    show "norm (sum \<chi> {1..x}) < sqrt n * ln n"
      using mult_imp_less_div_pos[OF \<open>sqrt n > 0\<close> 2] 3 by argo
  qed
qed


subsection \<open>General case\<close>

text \<open>
  We now first prove the inequality for the general case in terms of the divisor function:
\<close>
theorem (in dcharacter) polya_vinogradov_inequality_explicit:
  assumes nonprincipal: "\<chi> \<noteq> principal_dchar n"
  shows   "norm (sum \<chi> {1..x}) < sqrt conductor * ln conductor * divisor_count (n div conductor)"
proof -
  write primitive_extension ("\<Phi>")
  write conductor ("c")
  interpret \<Phi>: primitive_dchar c "residue_mult_group c" primitive_extension
    using primitive_primitive_extension nonprincipal by metis

  have *: "k \<le> x div b \<longleftrightarrow> b * k \<le> x" if "b > 0" for b k
    by (metis that antisym_conv div_le_mono div_mult_self1_is_m
              less_imp_le not_less times_div_less_eq_dividend)
  have **: "a > 0" if "a dvd n" for a
    using n that by (auto intro!: Nat.gr0I)

  from nonprincipal have "(\<Sum>m=1..x. \<chi> m) = (\<Sum>m | m \<in> {1..x} \<and> coprime m n. \<Phi> m)"
    by (intro sum.mono_neutral_cong_right) (auto simp: eq_zero_iff principal_decomposition)
  also have "\<dots> = (\<Sum>m=1..x. \<Phi> m * (\<Sum>d | d dvd gcd m n. moebius_mu d))"
    by (subst sum_moebius_mu_divisors', intro sum.mono_neutral_cong_left)
       (auto simp: coprime_iff_gcd_eq_1 simp del: coprime_imp_gcd_eq_1)
  also have "\<dots> = (\<Sum>m=1..x. \<Sum>d | d dvd gcd m n. \<Phi> m * moebius_mu d)"
    by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>m=1..x. \<Sum>d | d dvd m \<and> d dvd n. \<Phi> m * moebius_mu d)"
    by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>(m, d)\<in>(SIGMA m:{1..x}. {d. d dvd m \<and> d dvd n}). \<Phi> m * moebius_mu d)"
    using n by (subst sum.Sigma) auto
  also have "\<dots> = (\<Sum>(d, q)\<in>(SIGMA d:{d. d dvd n}. {1..x div d}). moebius_mu d * \<Phi> (d * q))"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>(d,q). (d * q, d)" "\<lambda>(m,d). (d, m div d)"])
       (auto simp: * ** Suc_le_eq)
  also have "\<dots> = (\<Sum>d | d dvd n. moebius_mu d * \<Phi> d * (\<Sum>q=1..x div d. \<Phi> q))"
    using n by (subst sum.Sigma [symmetric]) (auto simp: sum_distrib_left mult.assoc)
  finally have eq: "(\<Sum>m=1..x. \<chi> m) = \<dots>" .

  have "norm (\<Sum>m=1..x. \<chi> m) \<le>
          (\<Sum>d | d dvd n. norm (moebius_mu d * \<Phi> d) * norm (\<Sum>q=1..x div d. \<Phi> q))"
    unfolding eq by (intro sum_norm_le) (simp add: norm_mult)
  also have "\<dots> < (\<Sum>d | d dvd n. norm (moebius_mu d * \<Phi> d) * (sqrt c * ln c))"
    (is "sum ?lhs _ < sum ?rhs _")
  proof (rule sum_strict_mono_ex1)
    show "\<forall>d\<in>{d. d dvd n}. ?lhs d \<le> ?rhs d"
      by (intro ballI mult_left_mono less_imp_le[OF \<Phi>.polya_vinogradov_inequality_primitive]) auto
    show "\<exists>d\<in>{d. d dvd n}. ?lhs d < ?rhs d"
      by (intro bexI[of _ 1] mult_strict_left_mono \<Phi>.polya_vinogradov_inequality_primitive) auto
  qed (use n in auto)
  also have "\<dots> = sqrt c * ln c * (\<Sum>d | d dvd n. norm (moebius_mu d * \<Phi> d))"
    by (simp add: sum_distrib_left sum_distrib_right mult_ac)
  also have "(\<Sum>d | d dvd n. norm (moebius_mu d * \<Phi> d)) =
               (\<Sum>d | d dvd n \<and> squarefree d \<and> coprime d c. 1)"
    using n by (intro sum.mono_neutral_cong_right)
               (auto simp: moebius_mu_def \<Phi>.eq_zero_iff norm_mult norm_power \<Phi>.norm)
  also have "\<dots> = card {d. d dvd n \<and> squarefree d \<and> coprime d c}"
    by simp
  also have "card {d. d dvd n \<and> squarefree d \<and> coprime d c} \<le> card {d. d dvd (n div c)}"
  proof (intro card_mono; safe?)
    show "finite {d. d dvd (n div c)}"
      using dvd_div_eq_0_iff[of c n] n conductor_dvd by (intro finite_divisors_nat) auto
  next
    fix d assume d: "d dvd n" "squarefree d" "coprime d c"
    hence "d > 0" by (intro Nat.gr0I) auto
    show "d dvd (n div c)"
    proof (rule multiplicity_le_imp_dvd)
      fix p :: nat assume p: "prime p"
      show "multiplicity p d \<le> multiplicity p (n div c)"
      proof (cases "p dvd d")
        assume "p dvd d"
        with d \<open>d > 0\<close> p have "multiplicity p d = 1"
          by (auto simp: squarefree_factorial_semiring' in_prime_factors_iff)
        moreover have "p dvd (n div c)"
        proof -
          have "p dvd c * (n div c)"
            using \<open>p dvd d\<close> \<open>d dvd n\<close> conductor_dvd by auto
          moreover have "\<not>(p dvd c)"
            using d p \<open>p dvd d\<close> coprime_common_divisor not_prime_unit by blast
          ultimately show "p dvd (n div c)"
            using p prime_dvd_mult_iff by blast
        qed
        hence "multiplicity p (n div c) \<ge> 1"
          using n p conductor_dvd dvd_div_eq_0_iff[of c n]
          by (intro multiplicity_geI) (auto intro: Nat.gr0I)
        ultimately show ?thesis by simp
      qed (auto simp: not_dvd_imp_multiplicity_0)
    qed (use \<open>d > 0\<close> in simp_all)
  qed
  also have "card {d. d dvd (n div c)} = divisor_count (n div c)"
    by (simp add: divisor_count_def)
  finally show "norm (sum \<chi> {1..x}) < sqrt c * ln c * divisor_count (n div c)"
    using conductor_gr_0 by (simp add: mult_left_mono)
qed

(* TODO: Move? *)
text \<open>
  Next, we obtain a suitable upper bound on the number of divisors of \<open>n\<close>:
\<close>
lemma divisor_count_upper_bound_aux:
  fixes n :: nat
  shows "divisor_count n \<le> 2 * card {d. d dvd n \<and> d \<le> sqrt n}"
proof (cases "n = 0")
  case False
  hence n: "n > 0" by simp
  have *: "x > 0" if "x dvd n" for x
    using that n by (auto intro!: Nat.gr0I)
  have **: "real n = sqrt (real n) * sqrt (real n)"
    by simp
  have ***: "n < x * sqrt n \<longleftrightarrow> sqrt n < x" "x * sqrt n < n \<longleftrightarrow> x < sqrt n" for x
    by (metis ** n of_nat_0_less_iff real_mult_less_iff1 real_sqrt_gt_0_iff)+

  have "divisor_count n = card {d. d dvd n}"
    by (simp add: divisor_count_def)
  also have "{d. d dvd n} = {d. d dvd n \<and> d \<le> sqrt n} \<union> {d. d dvd n \<and> d > sqrt n}"
    by auto
  also have "card \<dots> = card {d. d dvd n \<and> d \<le> sqrt n} + card {d. d dvd n \<and> d > sqrt n}"
    using n by (subst card_Un_disjoint) auto
  also have "bij_betw (\<lambda>d. n div d) {d. d dvd n \<and> d > sqrt n} {d. d dvd n \<and> d < sqrt n}"
    using n by (intro bij_betwI[of _ _ _ "\<lambda>d. n div d"])
               (auto simp: Real.real_of_nat_div real_sqrt_divide field_simps * ***)
  hence "card {d. d dvd n \<and> d > sqrt n} = card {d. d dvd n \<and> d < sqrt n}"
    by (rule bij_betw_same_card)
  also have "\<dots> \<le> card {d. d dvd n \<and> d \<le> sqrt n}"
    using n by (intro card_mono) auto
  finally show "divisor_count n \<le> 2 * \<dots>" by simp
qed auto

lemma divisor_count_upper_bound:
  fixes n :: nat
  shows "divisor_count n \<le> 2 * nat \<lfloor>sqrt n\<rfloor>"
proof (cases "n = 0")
  case False
  have "divisor_count n \<le> 2 * card {d. d dvd n \<and> d \<le> sqrt n}"
    by (rule divisor_count_upper_bound_aux)
  also have "card {d. d dvd n \<and> d \<le> sqrt n} \<le> card {1..nat \<lfloor>sqrt n\<rfloor>}"
    using False by (intro card_mono) (auto simp: le_nat_iff le_floor_iff Suc_le_eq intro!: Nat.gr0I)
  also have "\<dots> = nat \<lfloor>sqrt n\<rfloor>" by simp
  finally show ?thesis by simp
qed auto

lemma divisor_count_upper_bound':
  fixes n :: nat
  shows "real (divisor_count n) \<le> 2 * sqrt n"
proof -
  have "real (divisor_count n) \<le> 2 * real (nat \<lfloor>sqrt n\<rfloor>)"
    using divisor_count_upper_bound[of n] by linarith
  also have "\<dots> \<le> 2 * sqrt n"
    by simp
  finally show ?thesis .
qed
(* END TODO *)


text \<open>
  We are now ready to prove the `regular' Pólya--Vinogradov inequality.

  Apostol formulates it in the following way (Theorem 13.15, notation adapted):
  `If \<open>\<chi>\<close> is any nonprincipal character mod \<open>n\<close>, then for all \<open>x \<ge> 2\<close> we have
  $\sum_{m\leq x} \chi(m) = O(\sqrt{n}\log n)$.'

  The precondition \<open>x \<ge> 2\<close> here is completely unnecessary. The `Big-O' notation is somewhat
  problematic since it does not make explicit in what way the variables are quantified
  (in particular the \<open>x\<close> and the \<open>\<chi>\<close>). The statement of the theorem in this way (for a fixed
  character \<open>\<chi>\<close>) seems to suggest that \<open>n\<close> is fixed here, which would make the use of `Big-O'
  completely vacuous, since it is an asymptotic statement about \<open>n\<close>.

  We therefore decided to formulate the inequality in the following more explicit way,
  even giving an explicit constant factor:
\<close>
theorem (in dcharacter) polya_vinogradov_inequality:
  assumes nonprincipal: "\<chi> \<noteq> principal_dchar n"
  shows   "norm (\<Sum>m=1..x. \<chi> m) < 2 * sqrt n * ln n"
proof -
  have "n div conductor > 0"
    using n conductor_dvd dvd_div_eq_0_iff[of conductor n] by auto
  have "norm (\<Sum>m=1..x. \<chi> m) < sqrt conductor * ln conductor * divisor_count (n div conductor)"
    using nonprincipal by (rule polya_vinogradov_inequality_explicit)
  also have "\<dots> \<le> sqrt conductor * ln conductor * (2 * sqrt (n div conductor))"
    using conductor_gr_0 \<open>n div conductor > 0\<close>
    by (intro mult_left_mono divisor_count_upper_bound') (auto simp: Suc_le_eq)
  also have "sqrt (n div conductor) = sqrt n / sqrt conductor"
    using conductor_dvd by (simp add: Real.real_of_nat_div real_sqrt_divide)
  also have "sqrt conductor * ln conductor * (2 * (sqrt n / sqrt conductor)) =
               2 * sqrt n * ln conductor"
    using conductor_gr_0 n by (simp add: algebra_simps)
  also have "\<dots> \<le> 2 * sqrt n * ln n"
    using conductor_le_modulus conductor_gr_0 by (intro mult_left_mono) auto
  finally show ?thesis .
qed

unbundle vec_lambda_notation

end