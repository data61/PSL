(*
  File:    Shapiro_Tauberian.thy
  Author:  Manuel Eberl, TU München

  Shapiro's Tauberian theorem
  (see Section 4.6 of Apostol's Introduction to Analytic Number Theory)
*)
section \<open>Shapiro's Tauberian Theorem\<close>
theory Shapiro_Tauberian
imports
  More_Dirichlet_Misc
  Prime_Number_Theorem.Prime_Counting_Functions
  Prime_Distribution_Elementary_Library
begin

subsection \<open>Proof\<close>

text \<open>
  Given an arithmeticla function $a(n)$, Shapiro's Tauberian theorem relates the sum
  $\sum_{n\leq x} a(n)$ to the weighted sums $\sum_{n\leq x} a(n) \lfloor\frac{x}{n}\rfloor$
  and $\sum_{n\leq x} a(n)/n$.

  More precisely, it shows that if $\sum_{n\leq x} a(n) \lfloor\frac{x}{n}\rfloor = x\ln x + O(x)$,
  then:
  \<^item> $\sum_{n\leq x} \frac{a(n)}{n} = \ln x + O(1)$
  \<^item> $\sum_{n\leq x} a(n) \leq Bx$ for some constant $B\geq 0$ and all $x\geq 0$
  \<^item> $\sum_{n\leq x} a(n) \geq Cx$ for some constant $C>0$ and all $x\geq 1/C$
\<close>

locale shapiro_tauberian =
  fixes a :: "nat \<Rightarrow> real" and A S T :: "real \<Rightarrow> real"
  defines "A \<equiv> sum_upto (\<lambda>n. a n / n)"
  defines "S \<equiv> sum_upto a"
  defines "T \<equiv> (\<lambda>x. dirichlet_prod' a floor x)"
  assumes a_nonneg:      "\<And>n. n > 0 \<Longrightarrow> a n \<ge> 0"
  assumes a_asymptotics: "(\<lambda>x. T x - x * ln x) \<in> O(\<lambda>x. x)"
begin

lemma fin: "finite X" if "X \<subseteq> {n. real n \<le> x}" for X x
  by (rule finite_subset[of _ "{..nat \<lfloor>x\<rfloor>}"]) (use that in \<open>auto simp: le_nat_iff le_floor_iff\<close>)

lemma S_mono: "S x \<le> S y" if "x \<le> y" for x y 
  unfolding S_def sum_upto_def using that by (intro sum_mono2 fin[of _ y] a_nonneg) auto

lemma split:
  fixes f :: "nat \<Rightarrow> real"
  assumes "\<alpha> \<in> {0..1}"
  shows   "sum_upto f x = sum_upto f (\<alpha>*x) + (\<Sum>n | n > 0 \<and> real n \<in> {\<alpha>*x<..x}. f n)"
proof (cases "x > 0")
  case False
  hence *: "{n. n > 0 \<and> real n \<le> x} = {}" "{n. n > 0 \<and> real n \<in> {\<alpha>*x<..x}} = {}"
    using mult_right_mono[of \<alpha> 1 x] assms by auto
  have "\<alpha> * x \<le> 0"
    using False assms by (intro mult_nonneg_nonpos) auto
  hence **: "{n. n > 0 \<and> real n \<le> \<alpha> * x} = {}"
    by auto
  show ?thesis
    unfolding sum_upto_def * ** by auto
next
  case True
  have "sum_upto f x = (\<Sum>n | n > 0 \<and> real n \<le> x. f n)"
    by (simp add: sum_upto_def)
  also have "{n. n > 0 \<and> real n \<le> x} =
                {n. n > 0 \<and> real n \<le> \<alpha>*x} \<union> {n. n > 0 \<and> real n \<in> {\<alpha>*x<..x}}"
    using assms True mult_right_mono[of \<alpha> 1 x] by (force intro: order_trans)
  also have "(\<Sum>n\<in>\<dots>. f n) = sum_upto f (\<alpha>*x) + (\<Sum>n | n > 0 \<and> real n \<in> {\<alpha>*x<..x}. f n)"
    by (subst sum.union_disjoint) (auto intro: fin simp: sum_upto_def)
  finally show ?thesis .
qed

lemma S_diff_T_diff: "S x - S (x / 2) \<le> T x - 2 * T (x / 2)"
proof -
  note fin = fin[of _ x]
  have T_diff_eq:
    "T x - 2 * T (x / 2) = sum_upto (\<lambda>n. a n * (\<lfloor>x / n\<rfloor> - 2 * \<lfloor>x / (2 * n)\<rfloor>)) (x / 2) +
        (\<Sum>n | n > 0 \<and> real n \<in> {x/2<..x}. a n * \<lfloor>x / n\<rfloor>)"
    unfolding T_def dirichlet_prod'_def
    by (subst split[where \<alpha> = "1/2"])
       (simp_all add: sum_upto_def sum_subtractf ring_distribs
                      sum_distrib_left sum_distrib_right mult_ac)
 
  have "S x - S (x / 2) = (\<Sum>n | n > 0 \<and> real n \<in> {x/2<..x}. a n)"
    unfolding S_def by (subst split[where \<alpha> = "1 / 2"]) (auto simp: sum_upto_def)
  also have "\<dots> = (\<Sum>n | n > 0 \<and> real n \<in> {x/2<..x}. a n * \<lfloor>x / n\<rfloor>)"
  proof (intro sum.cong)
    fix n assume "n \<in> {n. n > 0 \<and> real n \<in> {x/2<..x}}"
    hence "x / n \<ge> 1" "x / n < 2" by (auto simp: field_simps)
    hence "\<lfloor>x / n\<rfloor> = 1" by linarith
    thus "a n = a n * \<lfloor>x / n\<rfloor>" by simp
  qed auto
  also have "\<dots> = 0 + \<dots>" by simp
  also have "0 \<le> sum_upto (\<lambda>n. a n * (\<lfloor>x / n\<rfloor> - 2 * \<lfloor>x / (2 * n)\<rfloor>)) (x / 2)"
    unfolding sum_upto_def
  proof (intro sum_nonneg mult_nonneg_nonneg a_nonneg)
    fix n assume "n \<in> {n. n > 0 \<and> real n \<le> x / 2}"
    hence "x / real n \<ge> 2" by (auto simp: field_simps)
    thus "real_of_int (\<lfloor>x / n\<rfloor> - 2 * \<lfloor>x / (2 * n)\<rfloor>) \<ge> 0"
      using le_mult_floor[of 2 "x / (2 * n)"] by (simp add: mult_ac)
  qed auto
  also have "\<dots> + (\<Sum>n | n > 0 \<and> real n \<in> {x/2<..x}. a n * \<lfloor>x / n\<rfloor>) = T x - 2 * T (x / 2)"
    using T_diff_eq ..
  finally show "S x - S (x / 2) \<le> T x - 2 * T (x / 2)" by simp
qed

lemma
  shows diff_bound_strong: "\<exists>c\<ge>0. \<forall>x\<ge>0. x * A x - T x \<in> {0..c*x}"
    and asymptotics:       "(\<lambda>x. A x - ln x) \<in> O(\<lambda>_. 1)"
    and upper:             "\<exists>c\<ge>0. \<forall>x\<ge>0. S x \<le> c * x"
    and lower:             "\<exists>c>0. \<forall>x\<ge>1/c. S x \<ge> c * x"
    and bigtheta:          "S \<in> \<Theta>(\<lambda>x. x)"
proof -
  \<comment> \<open>We first prove the third case, i.\,e.\ the upper bound for \<open>S\<close>.\<close>
  have "(\<lambda>x. S x - S (x / 2)) \<in> O(\<lambda>x. T x - 2 * T (x / 2))"
  proof (rule le_imp_bigo_real)
    show "eventually (\<lambda>x. S x - S (x / 2) \<ge> 0) at_top"
      using eventually_ge_at_top[of 0]
    proof eventually_elim
      case (elim x)
      thus ?case using S_mono[of "x / 2" x] by simp
    qed
  next
    show "eventually (\<lambda>x. S x - S (x / 2) \<le> 1 * (T x - 2 * T (x / 2))) at_top"
      using S_diff_T_diff by simp
  qed auto
  also have "(\<lambda>x. T x - 2 * T (x / 2)) \<in> O(\<lambda>x. x)"
  proof -
    have "(\<lambda>x. T x - 2 * T (x / 2)) = 
            (\<lambda>x. (T x - x * ln x) - 2 * (T (x / 2) - (x / 2) * ln (x / 2)) 
              + x * (ln x - ln (x / 2)))" by (simp add: algebra_simps)
    also have "\<dots> \<in> O(\<lambda>x. x)"
    proof (rule sum_in_bigo, rule sum_in_bigo)
      show "(\<lambda>x. T x - x * ln x) \<in> O(\<lambda>x. x)" by (rule a_asymptotics)
    next
      have "(\<lambda>x. T (x / 2) - (x / 2) * ln (x / 2)) \<in> O(\<lambda>x. x / 2)"
        using a_asymptotics by (rule landau_o.big.compose) real_asymp+
      thus "(\<lambda>x. 2 * (T (x / 2) - x / 2 * ln (x / 2))) \<in> O(\<lambda>x. x)"
        unfolding cmult_in_bigo_iff by (subst (asm) landau_o.big.cdiv) auto
    qed real_asymp+
    finally show ?thesis .
  qed
  finally have S_diff_bigo: "(\<lambda>x. S x - S (x / 2)) \<in> O(\<lambda>x. x)" .

  obtain c1 where c1: "c1 \<ge> 0" "\<And>x. x \<ge> 0 \<Longrightarrow> S x \<le> c1 * x"
  proof -
    from S_diff_bigo have "(\<lambda>n. S (real n) - S (real n / 2)) \<in> O(\<lambda>n. real n)"
      by (rule landau_o.big.compose) real_asymp
    from natfun_bigoE[OF this, of 1] obtain c
      where "c > 0" "\<forall>n\<ge>1. \<bar>S (real n) - S (real n / 2)\<bar> \<le> c * real n" by auto
    hence c: "S (real n) - S (real n / 2) \<le> c * real n" if "n \<ge> 1" for n
      using S_mono[of "real n" "2 * real n"] that by auto
    have c_twopow: "S (2 ^ Suc n / 2) - S (2 ^ n / 2) \<le> c * 2 ^ n" for n
      using c[of "2 ^ n"] by simp 

    have S_twopow_le: "S (2 ^ k) \<le> 2 * c * 2 ^ k" for k
    proof -
      have [simp]: "{0<..Suc 0} = {1}" by auto
      have "(\<Sum>r<Suc k. S (2 ^ Suc r / 2) - S (2 ^ r / 2)) \<le> (\<Sum>r<Suc k. c * 2 ^ r)"
        by (intro sum_mono c_twopow)
      also have "(\<Sum>r<Suc k. S (2 ^ Suc r / 2) - S (2 ^ r / 2)) = S (2 ^ k)"
        by (subst sum_lessThan_telescope) (auto simp: S_def sum_upto_altdef)
      also have "(\<Sum>r<Suc k. c * 2 ^ r) = c * (\<Sum>r<Suc k. 2 ^ r)"
        unfolding sum_distrib_left ..
      also have "(\<Sum>r<Suc k. 2 ^ r :: real) = 2^Suc k - 1"
        by (subst geometric_sum) auto
      also have "c * \<dots> \<le> c * 2 ^ Suc k"
        using \<open>c > 0\<close> by (intro mult_left_mono) auto
      finally show "S (2 ^ k) \<le> 2 * c * 2 ^ k" by simp
    qed

    have S_le: "S x \<le> 4 * c * x" if "x \<ge> 0" for x
    proof (cases "x \<ge> 1")
      case False
      with that have "x \<in> {0..<1}" by auto
      thus ?thesis using \<open>c > 0\<close> by (auto simp: S_def sum_upto_altdef)
    next
      case True
      hence x: "x \<ge> 1" by simp
      define n where "n = nat \<lfloor>log 2 x\<rfloor>"
      have "2 powr real n \<le> 2 powr (log 2 x)"
        unfolding n_def using x by (intro powr_mono) auto
      hence ge: "2 ^ n \<le> x" using x by (subst (asm) powr_realpow) auto

      have "2 powr real (Suc n) > 2 powr (log 2 x)"
        unfolding n_def using x by (intro powr_less_mono) linarith+
      hence less: "2 ^ (Suc n) > x" using x by (subst (asm) powr_realpow) auto

      have "S x \<le> S (2 ^ Suc n)"
        using less by (intro S_mono) auto
      also have "\<dots> \<le> 2 * c * 2 ^ Suc n"
        by (intro S_twopow_le)
      also have "\<dots> = 4 * c * 2 ^ n"
        by simp
      also have "\<dots> \<le> 4 * c * x"
        by (intro mult_left_mono ge) (use x \<open>c > 0\<close> in auto)
      finally show "S x \<le> 4 * c * x" .
    qed

    with that[of "4 * c"] and \<open>c > 0\<close> show ?thesis by auto
  qed
  thus "\<exists>c\<ge>0. \<forall>x\<ge>0. S x \<le> c * x" by auto

  \<comment> \<open>The asymptotics of \<open>A\<close> follows from this immediately:\<close>
  have a_strong: "x * A x - T x \<in> {0..c1 * x}" if x: "x \<ge> 0" for x
  proof -
    have "sum_upto (\<lambda>n. a n * frac (x / n)) x \<le> sum_upto (\<lambda>n. a n * 1) x" unfolding sum_upto_def
      by (intro sum_mono mult_left_mono a_nonneg) (auto intro: less_imp_le frac_lt_1)
    also have "\<dots> = S x" unfolding S_def by simp
    also from x have "\<dots> \<le> c1 * x" by (rule c1)
    finally have "sum_upto (\<lambda>n. a n * frac (x / n)) x \<le> c1 * x" .
    moreover have "sum_upto (\<lambda>n. a n * frac (x / n)) x \<ge> 0"
      unfolding sum_upto_def by (intro sum_nonneg mult_nonneg_nonneg a_nonneg) auto
    ultimately have "sum_upto (\<lambda>n. a n * frac (x / n)) x \<in> {0..c1*x}" by auto
    also have "sum_upto (\<lambda>n. a n * frac (x / n)) x = x * A x - T x"
      by (simp add: T_def A_def sum_upto_def sum_subtractf frac_def algebra_simps
                    sum_distrib_left sum_distrib_right dirichlet_prod'_def)
    finally show ?thesis .
  qed
  thus "\<exists>c\<ge>0. \<forall>x\<ge>0. x * A x - T x \<in> {0..c*x}"
    using \<open>c1 \<ge> 0\<close> by (intro exI[of _ c1]) auto
  hence "(\<lambda>x. x * A x - T x) \<in> O(\<lambda>x. x)"
    using a_strong \<open>c1 \<ge> 0\<close>
    by (intro le_imp_bigo_real[of c1] eventually_mono[OF eventually_ge_at_top[of 1]]) auto
  from this and a_asymptotics have "(\<lambda>x. (x * A x - T x) + (T x - x * ln x)) \<in> O(\<lambda>x. x)"
    by (rule sum_in_bigo)
  hence "(\<lambda>x. x * (A x - ln x)) \<in> O(\<lambda>x. x * 1)"
    by (simp add: algebra_simps)
  thus bigo: "(\<lambda>x. A x - ln x) \<in> O(\<lambda>x. 1)"
    by (subst (asm) landau_o.big.mult_cancel_left) auto

  \<comment> \<open>It remains to show the lower bound for \<open>S\<close>.\<close>
  define R where "R = (\<lambda>x. A x - ln x)"
  obtain M where M: "\<And>x. x \<ge> 1 \<Longrightarrow> \<bar>R x\<bar> \<le> M"
  proof -
    have "(\<lambda>n. R (real n)) \<in> O(\<lambda>_. 1)"
      using bigo unfolding R_def by (rule landau_o.big.compose) real_asymp
    from natfun_bigoE[OF this, of 0] obtain M where M: "M > 0" "\<And>n. \<bar>R (real n)\<bar> \<le> M"
      by auto

    have "\<bar>R x\<bar> \<le> M + ln 2" if x: "x \<ge> 1" for x
    proof -
      define n where "n = nat \<lfloor>x\<rfloor>"
      have "\<bar>R x - R (real n)\<bar> = ln (x / n)"
        using x by (simp add: R_def A_def sum_upto_altdef n_def ln_div)
      also {
        have "x \<le> real n + 1"
          unfolding n_def by linarith
        also have "1 \<le> real n"
          using x unfolding n_def by simp
        finally have "ln (x / n) \<le> ln 2"
          using x by (simp add: field_simps)
      }
      finally have "\<bar>R x\<bar> \<le> \<bar>R (real n)\<bar> + ln 2"
        by linarith
      also have "\<bar>R (real n)\<bar> \<le> M"
        by (rule M)
      finally show "\<bar>R x\<bar> \<le> M + ln 2" by simp
    qed
    with that[of "M + ln 2"] show ?thesis by blast
  qed
  have "M \<ge> 0" using M[of 1] by simp
  
  have A_diff_ge: "A x - A (\<alpha>*x) \<ge> -ln \<alpha> - 2 * M"
    if \<alpha>: "\<alpha> \<in> {0<..<1}" and "x \<ge> 1 / \<alpha>" for x \<alpha> :: real
  proof -
    from that have "1 < inverse \<alpha> * 1" by (simp add: field_simps)
    also have "\<dots> \<le> inverse \<alpha> * (\<alpha> * x)"
      using \<open>x \<ge> 1 / \<alpha>\<close> and \<alpha> by (intro mult_left_mono) (auto simp: field_simps)
    also from \<alpha> have "\<dots> = x" by simp
    finally have "x > 1" .
    note x = this \<open>x >= 1 / \<alpha>\<close>

    have "-ln \<alpha> - M - M \<le> -ln \<alpha> - \<bar>R x\<bar> - \<bar>R (\<alpha>*x)\<bar>"
      using x \<alpha> by (intro diff_mono M) (auto simp: field_simps)
    also have "\<dots> \<le> -ln \<alpha> + R x - R (\<alpha>*x)"
      by linarith
    also have "\<dots> = A x - A (\<alpha>*x)"
      using \<alpha> x by (simp add: R_def ln_mult)
    finally show "A x - A (\<alpha>*x) \<ge> -ln \<alpha> - 2 * M" by simp
  qed
    
  define \<alpha> where "\<alpha> = exp (-2*M-1)"
  have "\<alpha> \<in> {0<..<1}"
    using \<open>M \<ge> 0\<close> by (auto simp: \<alpha>_def)

  have S_ge: "S x \<ge> \<alpha> * x" if x: "x \<ge> 1 / \<alpha>" for x
  proof -
    have "1 = -ln \<alpha> - 2 * M"
      by (simp add: \<alpha>_def)
    also have "\<dots> \<le> A x - A (\<alpha>*x)"
      by (intro A_diff_ge) fact+
    also have "\<dots> = (\<Sum>n | n > 0 \<and> real n \<in> {\<alpha>*x<..x}. a n / n)"
      unfolding A_def using \<open>\<alpha> \<in> {0<..<1}\<close> by (subst split[where \<alpha> = \<alpha>]) auto
    also have "\<dots> \<le> (\<Sum>n | n > 0 \<and> real n \<in> {\<alpha>*x<..x}. a n / (\<alpha>*x))"
      using x \<open>\<alpha> \<in> {0<..<1}\<close> by (intro sum_mono divide_left_mono a_nonneg) auto
    also have "\<dots> = (\<Sum>n | n > 0 \<and> real n \<in> {\<alpha>*x<..x}. a n) / (\<alpha>*x)"
      by (simp add: sum_divide_distrib)
    also have "\<dots> \<le> S x / (\<alpha>*x)"
      using x \<open>\<alpha> \<in> {0<..<1}\<close> unfolding S_def sum_upto_def
      by (intro divide_right_mono sum_mono2 a_nonneg) (auto simp: field_simps)
    finally show "S x \<ge> \<alpha> * x"
      using \<open>\<alpha> \<in> {0<..<1}\<close> x by (simp add: field_simps)
  qed
  thus "\<exists>c>0. \<forall>x\<ge>1/c. S x \<ge> c * x"
    using \<open>\<alpha> \<in> {0<..<1}\<close> by (intro exI[of _ \<alpha>]) auto

  have S_nonneg: "S x \<ge> 0" for x
    unfolding S_def sum_upto_def by (intro sum_nonneg a_nonneg) auto
  have "eventually (\<lambda>x. \<bar>S x\<bar> \<ge> \<alpha> * \<bar>x\<bar>) at_top"
    using eventually_ge_at_top[of "max 0 (1 / \<alpha>)"]
  proof eventually_elim
    case (elim x)
    with S_ge[of x] elim show ?case by auto
  qed
  hence "S \<in> \<Omega>(\<lambda>x. x)"
    using \<open>\<alpha> \<in> {0<..<1}\<close> by (intro landau_omega.bigI[of \<alpha>]) auto
  moreover have "S \<in> O(\<lambda>x. x)"
  proof (intro bigoI eventually_mono[OF eventually_ge_at_top[of 0]])
    fix x :: real assume "x \<ge> 0"
    thus "norm (S x) \<le> c1 * norm x"
      using c1(2)[of x] by (auto simp: S_nonneg)
  qed
  ultimately show "S \<in> \<Theta>(\<lambda>x. x)"
    by (intro bigthetaI)
qed

end


subsection \<open>Applications to the Chebyshev functions\<close>

(* 3.16 *)
text \<open>
  We can now apply Shapiro's Tauberian theorem to \<^term>\<open>\<psi>\<close> and \<^term>\<open>\<theta>\<close>.
\<close>
lemma dirichlet_prod_mangoldt1_floor_bigo:
  includes prime_counting_notation
  shows "(\<lambda>x. dirichlet_prod' (\<lambda>n. ind prime n * ln n) floor x - x * ln x) \<in> O(\<lambda>x. x)"
proof -
  \<comment> \<open>This is a perhaps somewhat roundabout way of proving this statement. We show this using
      the asymptotics of \<open>\<MM>\<close>: $\mathfrak{M}(x) = \ln x + O(1)$
     
      We proved this before (which was a bit of work, but not that much).
      Apostol, on the other hand, shows the following statement first and then deduces the
      asymptotics of \<open>\<MM>\<close> with Shapiro's Tauberian theorem instead. This might save a bit of
      work, but it is probably negligible.\<close>
  define R where "R = (\<lambda>x. sum_upto (\<lambda>i. ind prime i * ln i * frac (x / i)) x)"
  have *: "R x \<in> {0..ln 4 * x}" if "x \<ge> 1" for x
  proof -
    have "R x \<le> \<theta> x"
      unfolding R_def prime_sum_upto_altdef1 sum_upto_def \<theta>_def
      by (intro sum_mono) (auto simp: ind_def less_imp_le[OF frac_lt_1] dest!: prime_gt_1_nat)
    also have "\<dots> < ln 4 * x"
      by (rule \<theta>_upper_bound) fact+
    finally have "R x \<le> ln 4 * x" by auto
    moreover have "R x \<ge> 0" unfolding R_def sum_upto_def
      by (intro sum_nonneg mult_nonneg_nonneg) (auto simp: ind_def)
    ultimately show ?thesis by auto
  qed
  have "eventually (\<lambda>x. \<bar>R x\<bar> \<le> ln 4 * \<bar>x\<bar>) at_top"
    using eventually_ge_at_top[of 1] by eventually_elim (use * in auto)
  hence "R \<in> O(\<lambda>x. x)" by (intro landau_o.bigI[of "ln 4"]) auto

  have "(\<lambda>x. dirichlet_prod' (\<lambda>n. ind prime n * ln n) floor x - x * ln x) =
          (\<lambda>x. x * (\<MM> x - ln x) - R x)"
    by (auto simp: primes_M_def dirichlet_prod'_def prime_sum_upto_altdef1 sum_upto_def
                   frac_def sum_subtractf sum_distrib_left sum_distrib_right algebra_simps R_def)
  also have "\<dots> \<in> O(\<lambda>x. x)"
  proof (rule sum_in_bigo)
    have "(\<lambda>x. x * (\<MM> x - ln x)) \<in> O(\<lambda>x. x * 1)"
      by (intro landau_o.big.mult mertens_bounded) auto
    thus "(\<lambda>x. x * (\<MM> x - ln x)) \<in> O(\<lambda>x. x)" by simp
  qed fact+
  finally show ?thesis .
qed

lemma dirichlet_prod'_mangoldt_floor_asymptotics:
  "(\<lambda>x. dirichlet_prod' mangoldt floor x - x * ln x + x) \<in> O(ln)"
proof -
  have "dirichlet_prod' mangoldt floor = (\<lambda>x. sum_upto ln x)"
    unfolding sum_upto_ln_conv_sum_upto_mangoldt dirichlet_prod'_def
    by (intro sum_upto_cong' ext) auto
  hence "(\<lambda>x. dirichlet_prod' mangoldt floor x - x * ln x + x) = (\<lambda>x. sum_upto ln x - x * ln x + x)"
    by simp
  also have "\<dots> \<in> O(ln)"
    by (rule sum_upto_ln_stirling_weak_bigo)
  finally show "(\<lambda>x. dirichlet_prod' mangoldt (\<lambda>x. real_of_int \<lfloor>x\<rfloor>) x - x * ln x + x) \<in> O(ln)" .
qed

(* 4.9 *)
interpretation \<psi>: shapiro_tauberian mangoldt "sum_upto (\<lambda>n. mangoldt n / n)" primes_psi
  "dirichlet_prod' mangoldt floor"
proof unfold_locales
  have "dirichlet_prod' mangoldt floor = (\<lambda>x. sum_upto ln x)"
    unfolding sum_upto_ln_conv_sum_upto_mangoldt dirichlet_prod'_def
    by (intro sum_upto_cong' ext) auto
  hence "(\<lambda>x. dirichlet_prod' mangoldt floor x - x * ln x + x) = (\<lambda>x. sum_upto ln x - x * ln x + x)"
    by simp
  also have "\<dots> \<in> O(ln)"
    by (rule sum_upto_ln_stirling_weak_bigo)
  also have "ln \<in> O(\<lambda>x::real. x)" by real_asymp
  finally have "(\<lambda>x. dirichlet_prod' mangoldt (\<lambda>x. real_of_int \<lfloor>x\<rfloor>) x - x * ln x + x - x)
                   \<in> O(\<lambda>x. x)" by (rule sum_in_bigo) auto
  thus "(\<lambda>x. dirichlet_prod' mangoldt (\<lambda>x. real_of_int \<lfloor>x\<rfloor>) x - x * ln x) \<in> O(\<lambda>x. x)" by simp
qed (simp_all add: primes_psi_def mangoldt_nonneg)

thm \<psi>.asymptotics \<psi>.upper \<psi>.lower


(* 4.10 *)
interpretation \<theta>: shapiro_tauberian "\<lambda>n. ind prime n * ln n" 
  "sum_upto (\<lambda>n. ind prime n * ln n / n)" primes_theta "dirichlet_prod' (\<lambda>n. ind prime n * ln n) floor"
proof unfold_locales
  fix n :: nat show "ind prime n * ln n \<ge> 0"
    by (auto simp: ind_def dest: prime_gt_1_nat)
next
  show "(\<lambda>x. dirichlet_prod' (\<lambda>n. ind prime n * ln n) floor x - x * ln x) \<in> O(\<lambda>x. x)"
    by (rule dirichlet_prod_mangoldt1_floor_bigo)
qed (simp_all add: primes_theta_def mangoldt_nonneg prime_sum_upto_altdef1[abs_def])

thm \<theta>.asymptotics \<theta>.upper \<theta>.lower

(* 4.11 *)
lemma sum_upto_\<psi>_x_over_n_asymptotics:
        "(\<lambda>x. sum_upto (\<lambda>n. primes_psi (x / n)) x - x * ln x + x) \<in> O(ln)"
  and sum_upto_\<theta>_x_over_n_asymptotics:
        "(\<lambda>x. sum_upto (\<lambda>n. primes_theta (x / n)) x - x * ln x) \<in> O(\<lambda>x. x)"
  using dirichlet_prod_mangoldt1_floor_bigo dirichlet_prod'_mangoldt_floor_asymptotics
  by (simp_all add: dirichlet_prod'_floor_conv_sum_upto primes_theta_def
                    primes_psi_def prime_sum_upto_altdef1)

end