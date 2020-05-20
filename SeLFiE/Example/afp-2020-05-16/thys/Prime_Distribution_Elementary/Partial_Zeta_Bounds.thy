(*
  File:    Partial_Zeta_Bounds.thy
  Author:  Manuel Eberl, TU München

  Asymptotic bounds on sums over k^(-s) for k=1..n, for fixed s and variable n.
*)
section \<open>Bounds on partial sums of the $\zeta$ function\<close>
theory Partial_Zeta_Bounds
imports
  Euler_MacLaurin.Euler_MacLaurin_Landau
  Zeta_Function.Zeta_Function
  Prime_Number_Theorem.Prime_Number_Theorem_Library
  Prime_Distribution_Elementary_Library
begin

(* TODO: This does not necessarily require the full complex zeta function. *)

text \<open>
  We employ Euler--MacLaurin's summation formula to obtain asymptotic estimates
  for the partial sums of the Riemann $\zeta(s)$ function for fixed real $a$, i.\,e.\ the function
  \[f(n) = \sum_{k=1}^n k^{-s}\ .\]
  We distinguish various cases. The case $s = 1$ is simply the Harmonic numbers and is
  treated apart from the others.
\<close>
lemma harm_asymp_equiv: "sum_upto (\<lambda>n. 1 / n) \<sim>[at_top] ln"
proof -
  have "sum_upto (\<lambda>n. n powr -1) \<sim>[at_top] (\<lambda>x. ln (\<lfloor>x\<rfloor> + 1))"
  proof (rule asymp_equiv_sandwich)
    have "eventually (\<lambda>x. sum_upto (\<lambda>n. n powr -1) x \<in> {ln (\<lfloor>x\<rfloor> + 1)..ln \<lfloor>x\<rfloor> + 1}) at_top"
      using eventually_ge_at_top[of 1]
    proof eventually_elim
      case (elim x)
      have "sum_upto (\<lambda>n. real n powr -1) x = harm (nat \<lfloor>x\<rfloor>)"
        unfolding sum_upto_altdef harm_def by (intro sum.cong) (auto simp: field_simps powr_minus)
      also have "\<dots> \<in> {ln (\<lfloor>x\<rfloor> + 1)..ln \<lfloor>x\<rfloor> + 1}"
        using elim harm_le[of "nat \<lfloor>x\<rfloor>"] ln_le_harm[of "nat \<lfloor>x\<rfloor>"]
        by (auto simp: le_nat_iff le_floor_iff)
      finally show ?case by simp
    qed
    thus "eventually (\<lambda>x. sum_upto (\<lambda>n. n powr -1) x \<ge> ln (\<lfloor>x\<rfloor> + 1)) at_top"
         "eventually (\<lambda>x. sum_upto (\<lambda>n. n powr -1) x \<le> ln \<lfloor>x\<rfloor> + 1) at_top"
      by (eventually_elim; simp)+
  qed real_asymp+
  also have "\<dots> \<sim>[at_top] ln" by real_asymp
  finally show ?thesis by (simp add: powr_minus field_simps)
qed

lemma
  fixes s :: real
  assumes s: "s > 0" "s \<noteq> 1"
  shows   zeta_partial_sum_bigo_pos:
            "(\<lambda>n. (\<Sum>k=1..n. real k powr -s) - real n powr (1 - s) / (1 - s) - Re (zeta s))
                \<in> O(\<lambda>x. real x powr -s)"
    and   zeta_partial_sum_bigo_pos':
            "(\<lambda>n. \<Sum>k=1..n. real k powr -s) =o
               (\<lambda>n. real n powr (1 - s) / (1 - s) + Re (zeta s)) +o O(\<lambda>x. real x powr -s)"
proof -
  define F where "F = (\<lambda>x. x powr (1 - s) / (1 - s))"
  define f where "f = (\<lambda>x. x powr -s)"
  define f' where "f' = (\<lambda>x. -s * x powr (-s-1))"
  define z where "z = Re (zeta s)"
  
  interpret euler_maclaurin_nat' F f "(!) [f, f']" 1 0 z "{}"
  proof
    have "(\<lambda>b. (\<Sum>k=1..b. real k powr -s) - real b powr (1 - s) / (1 - s) - real b powr -s / 2)
             \<longlonglongrightarrow> Re (zeta s) - 0"
    proof (intro tendsto_diff)
      let ?g = "\<lambda>b. (\<Sum>i<b. complex_of_real (real i + 1) powr - complex_of_real s) -
                             of_nat b powr (1 - complex_of_real s) / (1 - complex_of_real s)"
      have "\<forall>\<^sub>F b in at_top. Re (?g b) = (\<Sum>k=1..b. real k powr -s) - real b powr (1 - s) / (1 - s)"
        using eventually_ge_at_top[of 1]
      proof eventually_elim
        case (elim b)
        have "(\<Sum>k=1..b. real k powr -s) = (\<Sum>k<b. real (Suc k) powr -s) "
          by (intro sum.reindex_bij_witness[of _ Suc "\<lambda>n. n - 1"]) auto
        also have "\<dots> - real b powr (1 - s) / (1 - s) = Re (?g b)"
          by (auto simp: powr_Reals_eq add_ac)
        finally show ?case ..
      qed
      moreover have "(\<lambda>b. Re (?g b)) \<longlonglongrightarrow> Re (zeta s)"
        using hurwitz_zeta_critical_strip[of "of_real s" 1] s
        by (intro tendsto_intros) (simp add: zeta_def)
      ultimately show "(\<lambda>b. (\<Sum>k=1..b. real k powr -s) - real b powr (1 - s) / (1 - s)) \<longlonglongrightarrow> Re (zeta s)" 
        by (blast intro: Lim_transform_eventually)
    qed (use s in real_asymp)
    thus "(\<lambda>b. (\<Sum>k = 1..b. f (real k)) - F (real b) -
              (\<Sum>i<2 * 0 + 1. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R ([f, f'] ! i) (real b)))
            \<longlonglongrightarrow> z" by (simp add: f_def F_def z_def)
  qed (use \<open>s \<noteq> 1\<close> in
         \<open>auto intro!: derivative_eq_intros continuous_intros 
               simp flip: has_field_derivative_iff_has_vector_derivative
               simp: F_def f_def f'_def nth_Cons split: nat.splits\<close>)

  {
    fix n :: nat assume n: "n \<ge> 1"
    have "(\<Sum>k=1..n. real k powr -s) =
            n powr (1 - s) / (1 - s) + z + 1/2 * n powr -s -
            EM_remainder 1 f' (int n)"
      using euler_maclaurin_strong_nat'[of n] n by (simp add: F_def f_def)
  } note * = this

  have "(\<lambda>n. (\<Sum>k=1..n. real k powr -s) - n powr (1 - s) / (1 - s) - z) \<in>
          \<Theta>(\<lambda>n. 1/2 * n powr -s - EM_remainder 1 f' (int n))"
    using * by (intro bigthetaI_cong eventually_mono[OF eventually_ge_at_top[of 1]]) auto
  also have "(\<lambda>n. 1/2 * n powr -s - EM_remainder 1 f' (int n)) \<in> O(\<lambda>n. n powr -s)"
  proof (intro sum_in_bigo)
    have "(\<lambda>x. norm (EM_remainder 1 f' (int x))) \<in> O(\<lambda>x. real x powr - s)"
    proof (rule EM_remainder_strong_bigo_nat[where a = 1 and Y = "{}"])
      fix x :: real assume "x \<ge> 1"
      show "norm (f' x) \<le> s * x powr (-s-1)"
        using s by (simp add: f'_def)
    next
      from s show "((\<lambda>x. x powr -s) \<longlongrightarrow> 0) at_top" by real_asymp
    qed (auto simp: f'_def intro!: continuous_intros derivative_eq_intros)
    thus "(\<lambda>x. EM_remainder 1 f' (int x)) \<in> O(\<lambda>x. real x powr -s)"
      by simp
  qed real_asymp+
  finally show "(\<lambda>n. (\<Sum>k=1..n. real k powr -s) - real n powr (1 - s) / (1 - s) - z)
                  \<in> O(\<lambda>x. real x powr -s)" .
  thus"(\<lambda>n. \<Sum>k=1..n. real k powr -s) =o
           (\<lambda>n. real n powr (1 - s) / (1 - s) + z) +o O(\<lambda>x. real x powr -s)"
    by (subst set_minus_plus [symmetric]) (simp_all add: fun_diff_def algebra_simps)
qed

lemma zeta_tail_bigo:
  fixes s :: real
  assumes s: "s > 1"
  shows   "(\<lambda>n. Re (hurwitz_zeta (real n + 1) s)) \<in> O(\<lambda>x. real x powr (1 - s))"
proof -
  have [simp]: "complex_of_real (Re (zeta s)) = zeta s"
    using zeta_real[of s] by (auto elim!: Reals_cases)
    
  from s have s': "s > 0" "s \<noteq> 1" by auto
  have "(\<lambda>n. -Re (hurwitz_zeta (real n + 1) s) - real n powr (1 - s) / (1 - s)
              + real n powr (1 - s) / (1 - s))
          \<in> O(\<lambda>x. real x powr (1 - s))"
  proof (rule sum_in_bigo)
    have "(\<lambda>n. -Re (hurwitz_zeta (real n + 1) s) - real n powr (1 - s) / (1 - s)) =
            (\<lambda>n. (\<Sum>k=1..n. real k powr -s) - real n powr (1 - s) / (1 - s) - Re (zeta s))"
      (is "?lhs = ?rhs")
    proof
      fix n :: nat
      have "hurwitz_zeta (1 + real n) s = zeta s - (\<Sum>k<n. real (Suc k) powr -s)"
        by (subst hurwitz_zeta_shift) (use assms in \<open>auto simp: zeta_def powr_Reals_eq\<close>)
      also have "(\<Sum>k<n. real (Suc k) powr -s) = (\<Sum>k=1..n. real k powr -s)"
        by (rule sum.reindex_bij_witness[of _ "\<lambda>k. k - 1" Suc]) auto
      finally show "?lhs n = ?rhs n" by (simp add: add_ac)
    qed
    also have "\<dots> \<in> O(\<lambda>x. real x powr (-s))"
      by (rule zeta_partial_sum_bigo_pos) (use s in auto)
    also have "(\<lambda>x. real x powr (-s)) \<in> O(\<lambda>x. real x powr (1-s))"
      by real_asymp
    finally show "(\<lambda>n. -Re (hurwitz_zeta (real n + 1) s) - real n powr (1 - s) / (1 - s)) \<in> \<dots>" .
  qed (use s in real_asymp)
  thus ?thesis by simp
qed

lemma zeta_tail_bigo':
  fixes s :: real
  assumes s: "s > 1"
  shows   "(\<lambda>n. Re (hurwitz_zeta (real n) s)) \<in> O(\<lambda>x. real x powr (1 - s))"
proof -
  have "(\<lambda>n. Re (hurwitz_zeta (real n) s)) \<in> \<Theta>(\<lambda>n. Re (hurwitz_zeta (real (n - 1) + 1) s))"
    by (intro bigthetaI_cong eventually_mono[OF eventually_ge_at_top[of 1]])
       (auto simp: of_nat_diff)
  also have "(\<lambda>n. Re (hurwitz_zeta (real (n - 1) + 1) s)) \<in> O(\<lambda>x. real (x - 1) powr (1 - s))"
    by (rule landau_o.big.compose[OF zeta_tail_bigo[OF assms]]) real_asymp
  also have "(\<lambda>x. real (x - 1) powr (1 - s)) \<in> O(\<lambda>x. real x powr (1 - s))"
    by real_asymp
  finally show ?thesis .
qed

lemma
  fixes s :: real
  assumes s: "s > 0"
  shows   zeta_partial_sum_bigo_neg:
            "(\<lambda>n. (\<Sum>i=1..n. real i powr s) - n powr (1 + s) / (1 + s)) \<in> O(\<lambda>n. n powr s)"
    and   zeta_partial_sum_bigo_neg':
            "(\<lambda>n. (\<Sum>i=1..n. real i powr s)) =o (\<lambda>n. n powr (1 + s) / (1 + s)) +o O(\<lambda>n. n powr s)"
proof -
  define F where "F = (\<lambda>x. x powr (1 + s) / (1 + s))"
  define f where "f = (\<lambda>x. x powr s)"
  define f' where "f' = (\<lambda>x. s * x powr (s - 1))"

  have "(\<Sum>i=1..n. f (real i)) - F n =
          1 / 2 - F 1 + f n / 2 + EM_remainder' 1 f' 1 (real n)" if n: "n \<ge> 1" for n
  proof -
    have "(\<Sum>i\<in>{1<..n}. f (real i)) - integral {real 1..real n} f =
            (\<Sum>k<1. (bernoulli' (Suc k) / fact (Suc k)) *\<^sub>R (([f, f'] ! k) (real n) -
                ([f, f'] ! k) (real 1))) + EM_remainder' 1 ([f, f'] ! 1) (real 1) (real n)"
      by (rule euler_maclaurin_strong_raw_nat[where Y = "{}"])
         (use \<open>s > 0\<close> \<open>n \<ge> 1\<close> in
           \<open>auto intro!: derivative_eq_intros continuous_intros 
                 simp flip: has_field_derivative_iff_has_vector_derivative
                 simp: F_def f_def f'_def nth_Cons split: nat.splits\<close>)
    also have "(\<Sum>i\<in>{1<..n}. f (real i)) = (\<Sum>i\<in>insert 1 {1<..n}. f (real i)) - f 1"
      using n by (subst sum.insert) auto
    also from n have "insert 1 {1<..n} = {1..n}" by auto
    finally have "(\<Sum>i=1..n. f (real i)) - F n = f 1 + (integral {1..real n} f - F n) +
                    (f (real n) - f 1) / 2 + EM_remainder' 1 f' 1 (real n)" by simp
    hence "(\<Sum>i=1..n. f (real i)) - F n = 1 / 2 + (integral {1..real n} f - F n) +
              f (real n) / 2 + EM_remainder' 1 f' 1 (real n)"
      using s by (simp add: f_def diff_divide_distrib)
    also have "(f has_integral (F (real n) - F 1)) {1..real n}" using assms n
      by (intro fundamental_theorem_of_calculus)
         (auto simp flip: has_field_derivative_iff_has_vector_derivative simp: F_def f_def
               intro!: derivative_eq_intros continuous_intros)
    hence "integral {1..real n} f - F n = - F 1"
      by (simp add: has_integral_iff)
    also have "1 / 2 + (-F 1) + f (real n) / 2 = 1 / 2 - F 1 + f n / 2"
      by simp
    finally show ?thesis .
  qed

  hence "(\<lambda>n. (\<Sum>i=1..n. f (real i)) - F n) \<in>
           \<Theta>(\<lambda>n. 1 / 2 - F 1 + f n / 2 + EM_remainder' 1 f' 1 (real n))"
    by (intro bigthetaI_cong eventually_mono[OF eventually_ge_at_top[of 1]])
  also have "(\<lambda>n. 1 / 2 - F 1 + f n / 2 + EM_remainder' 1 f' 1 (real n))
               \<in> O(\<lambda>n. real n powr s)"
    unfolding F_def f_def
  proof (intro sum_in_bigo)
    have "(\<lambda>x. integral {1..real x} (\<lambda>t. pbernpoly 1 t *\<^sub>R f' t)) \<in> O(\<lambda>n. 1 / s * real n powr s)"
    proof (intro landau_o.big.compose[OF integral_bigo])
      have "(\<lambda>x. pbernpoly 1 x * f' x) \<in> O(\<lambda>x. 1 * x powr (s - 1))"
        by (intro landau_o.big.mult pbernpoly_bigo) (auto simp: f'_def)
      thus "(\<lambda>x. pbernpoly 1 x *\<^sub>R f' x) \<in> O(\<lambda>x. x powr (s - 1))"
        by simp
      from s show "filterlim (\<lambda>a. 1 / s * a powr s) at_top at_top" by real_asymp
    next
      fix a' x :: real assume "a' \<ge> 1" "a' \<le> x"
      thus "(\<lambda>a. pbernpoly 1 a *\<^sub>R f' a) integrable_on {a'..x}"
        by (intro integrable_EM_remainder') (auto intro!: continuous_intros simp: f'_def)
    qed (use s in \<open>auto intro!: filterlim_real_sequentially continuous_intros derivative_eq_intros\<close>)
    thus "(\<lambda>x. EM_remainder' 1 f' 1 (real x)) \<in> O(\<lambda>n. real n powr s)"
      using \<open>s > 0\<close> by (simp add: EM_remainder'_def)
  qed (use \<open>s > 0\<close> in real_asymp)+
  finally show "(\<lambda>n. (\<Sum>i=1..n. real i powr s) - n powr (1 + s) / (1 + s)) \<in> O(\<lambda>n. n powr s)"
    by (simp add: f_def F_def)
  thus "(\<lambda>n. (\<Sum>i=1..n. real i powr s)) =o (\<lambda>n. n powr (1 + s) / (1 + s)) +o O(\<lambda>n. n powr s)"
    by (subst set_minus_plus [symmetric]) (simp_all add: fun_diff_def algebra_simps)
qed

lemma zeta_partial_sum_le_pos:
  assumes "s > 0" "s \<noteq> 1"
  defines "z \<equiv> Re (zeta (complex_of_real s))"
  shows   "\<exists>c>0. \<forall>x\<ge>1. \<bar>sum_upto (\<lambda>n. n powr -s) x - (x powr (1-s) / (1-s) + z)\<bar> \<le> c * x powr -s"
proof (rule sum_upto_asymptotics_lift_nat_real)
  show "(\<lambda>n. (\<Sum>k = 1..n. real k powr - s) - (real n powr (1 - s) / (1 - s) + z))
          \<in> O(\<lambda>n. real n powr - s)"
    using zeta_partial_sum_bigo_pos[OF assms(1,2)] unfolding z_def
    by (simp add: algebra_simps)

  from assms have "s < 1 \<or> s > 1" by linarith
  thus "(\<lambda>n. real n powr (1 - s) / (1 - s) + z - (real (Suc n) powr (1 - s) / (1 - s) + z))
          \<in> O(\<lambda>n. real n powr - s)"
    by standard (use \<open>s > 0\<close> in \<open>real_asymp+\<close>)
  show "(\<lambda>n. real n powr - s) \<in> O(\<lambda>n. real (Suc n) powr - s)"
    by real_asymp
  show "mono_on (\<lambda>a. a powr - s) {1..} \<or> mono_on (\<lambda>x. - (x powr - s)) {1..}"
    using assms by (intro disjI2) (auto intro!: mono_onI powr_mono2')

  from assms have "s < 1 \<or> s > 1" by linarith
  hence "mono_on (\<lambda>a. a powr (1 - s) / (1 - s) + z) {1..}"
  proof
    assume "s < 1"
    thus ?thesis using \<open>s > 0\<close>
      by (intro mono_onI powr_mono2 divide_right_mono add_right_mono) auto
  next
    assume "s > 1"
    thus ?thesis
      by (intro mono_onI le_imp_neg_le add_right_mono divide_right_mono_neg powr_mono2') auto
  qed
  thus "mono_on (\<lambda>a. a powr (1 - s) / (1 - s) + z) {1..} \<or>
        mono_on (\<lambda>x. - (x powr (1 - s) / (1 - s) + z)) {1..}" by blast
qed auto

lemma zeta_partial_sum_le_pos':
  assumes "s > 0" "s \<noteq> 1"
  defines "z \<equiv> Re (zeta (complex_of_real s))"
  shows   "\<exists>c>0. \<forall>x\<ge>1. \<bar>sum_upto (\<lambda>n. n powr -s) x - x powr (1-s) / (1-s)\<bar> \<le> c"
proof -
  have "\<exists>c>0. \<forall>x\<ge>1. \<bar>sum_upto (\<lambda>n. n powr -s) x - x powr (1-s) / (1-s)\<bar> \<le> c * 1"
  proof (rule sum_upto_asymptotics_lift_nat_real)
    have "(\<lambda>n. (\<Sum>k = 1..n. real k powr - s) - (real n powr (1 - s) / (1 - s) + z))
            \<in> O(\<lambda>n. real n powr - s)"
      using zeta_partial_sum_bigo_pos[OF assms(1,2)] unfolding z_def
      by (simp add: algebra_simps)
    also have "(\<lambda>n. real n powr -s) \<in> O(\<lambda>n. 1)"
      using assms by real_asymp
    finally have "(\<lambda>n. (\<Sum>k = 1..n. real k powr - s) - real n powr (1 - s) / (1 - s) - z)
                     \<in> O(\<lambda>n. 1)" by (simp add: algebra_simps)
    hence "(\<lambda>n. (\<Sum>k = 1..n. real k powr - s) - real n powr (1 - s) / (1 - s) - z + z) \<in> O(\<lambda>n. 1)"
      by (rule sum_in_bigo) auto
    thus "(\<lambda>n. (\<Sum>k = 1..n. real k powr - s) - (real n powr (1 - s) / (1 - s))) \<in> O(\<lambda>n. 1)"
      by simp
  
    from assms have "s < 1 \<or> s > 1" by linarith
    thus "(\<lambda>n. real n powr (1 - s) / (1 - s) - (real (Suc n) powr (1 - s) / (1 - s))) \<in> O(\<lambda>n. 1)"
      by standard (use \<open>s > 0\<close> in \<open>real_asymp+\<close>)
    show "mono_on (\<lambda>a. 1) {1..} \<or> mono_on (\<lambda>x::real. -1 :: real) {1..}"
      using assms by (intro disjI2) (auto intro!: mono_onI powr_mono2')
  
    from assms have "s < 1 \<or> s > 1" by linarith
    hence "mono_on (\<lambda>a. a powr (1 - s) / (1 - s)) {1..}"
    proof
      assume "s < 1"
      thus ?thesis using \<open>s > 0\<close>
        by (intro mono_onI powr_mono2 divide_right_mono add_right_mono) auto
    next
      assume "s > 1"
      thus ?thesis
        by (intro mono_onI le_imp_neg_le add_right_mono divide_right_mono_neg powr_mono2') auto
    qed
    thus "mono_on (\<lambda>a. a powr (1 - s) / (1 - s)) {1..} \<or>
          mono_on (\<lambda>x. - (x powr (1 - s) / (1 - s))) {1..}" by blast
  qed auto
  thus ?thesis by simp
qed

lemma zeta_partial_sum_le_pos'':
  assumes "s > 0" "s \<noteq> 1"
  shows   "\<exists>c>0. \<forall>x\<ge>1. \<bar>sum_upto (\<lambda>n. n powr -s) x\<bar> \<le> c * x powr max 0 (1 - s)"
proof -
  from zeta_partial_sum_le_pos'[OF assms] obtain c where
    c: "c > 0" "\<And>x. x \<ge> 1 \<Longrightarrow> \<bar>sum_upto (\<lambda>x. real x powr - s) x - x powr (1 - s) / (1 - s)\<bar> \<le> c"
    by auto

  {
    fix x :: real assume x: "x \<ge> 1"
    have "\<bar>sum_upto (\<lambda>x. real x powr - s) x\<bar> \<le> \<bar>x powr (1 - s) / (1 - s)\<bar> + c"
      using c(1) c(2)[OF x] x by linarith
    also have "\<bar>x powr (1 - s) / (1 - s)\<bar> = x powr (1 - s) / \<bar>1 - s\<bar>"
      using assms by simp
    also have "\<dots> \<le> x powr max 0 (1 - s) / \<bar>1 - s\<bar>"
      using x by (intro divide_right_mono powr_mono) auto
    also have "c = c * x powr 0" using x by simp
    also have "c * x powr 0 \<le> c * x powr max 0 (1 - s)"
      using c(1) x by (intro mult_left_mono powr_mono) auto
    also have "x powr max 0 (1 - s) / \<bar>1 - s\<bar> + c * x powr max 0 (1 - s) =
                 (1 / \<bar>1 - s\<bar> + c) * x powr max 0 (1 - s)"
      by (simp add: algebra_simps)
    finally have "\<bar>sum_upto (\<lambda>x. real x powr - s) x\<bar> \<le> (1 / \<bar>1 - s\<bar> + c) * x powr max 0 (1 - s)"
      by simp
  }
  moreover have "(1 / \<bar>1 - s\<bar> + c) > 0"
    using c assms by (intro add_pos_pos divide_pos_pos) auto
  ultimately show ?thesis by blast
qed

lemma zeta_partial_sum_le_pos_bigo:
  assumes "s > 0" "s \<noteq> 1"
  shows   "(\<lambda>x. sum_upto (\<lambda>n. n powr -s) x) \<in> O(\<lambda>x. x powr max 0 (1 - s))"
proof -
  from zeta_partial_sum_le_pos''[OF assms] obtain c
    where "\<forall>x\<ge>1. \<bar>sum_upto (\<lambda>n. n powr -s) x\<bar> \<le> c * x powr max 0 (1 - s)" by auto
  thus ?thesis
    by (intro bigoI[of _ c] eventually_mono[OF eventually_ge_at_top[of 1]]) auto
qed
    
lemma zeta_partial_sum_01_asymp_equiv:
  assumes "s \<in> {0<..<1}"
  shows "sum_upto (\<lambda>n. n powr -s) \<sim>[at_top] (\<lambda>x. x powr (1 - s) / (1 - s))"
proof -
  from zeta_partial_sum_le_pos'[of s] assms obtain c where
    c: "c > 0" "\<forall>x\<ge>1. \<bar>sum_upto (\<lambda>x. real x powr -s) x - x powr (1 - s) / (1 - s)\<bar> \<le> c" by auto
  hence "(\<lambda>x. sum_upto (\<lambda>x. real x powr -s) x - x powr (1 - s) / (1 - s)) \<in> O(\<lambda>_. 1)"
    by (intro bigoI[of _ c] eventually_mono[OF eventually_ge_at_top[of 1]]) auto
  also have "(\<lambda>_. 1) \<in> o(\<lambda>x. x powr (1 - s) / (1 - s))"
    using assms by real_asymp
  finally show ?thesis
    by (rule smallo_imp_asymp_equiv)
qed

lemma zeta_partial_sum_gt_1_asymp_equiv:
  assumes "s > 1"
  defines "\<zeta> \<equiv> Re (zeta s)"
  shows "sum_upto (\<lambda>n. n powr -s) \<sim>[at_top] (\<lambda>x. \<zeta>)"
proof -
  have [simp]: "\<zeta> \<noteq> 0"
    using assms zeta_Re_gt_1_nonzero[of s] zeta_real[of s] by (auto elim!: Reals_cases)
  from zeta_partial_sum_le_pos[of s] assms obtain c where
    c: "c > 0" "\<forall>x\<ge>1. \<bar>sum_upto (\<lambda>x. real x powr -s) x - (x powr (1 - s) / (1 - s) + \<zeta>)\<bar> \<le>
                        c * x powr -s" by (auto simp: \<zeta>_def)
  hence "(\<lambda>x. sum_upto (\<lambda>x. real x powr -s) x - \<zeta> - x powr (1 - s) / (1 - s)) \<in> O(\<lambda>x. x powr -s)"
    by (intro bigoI[of _ c] eventually_mono[OF eventually_ge_at_top[of 1]]) auto
  also have "(\<lambda>x. x powr -s) \<in> o(\<lambda>_. 1)"
    using \<open>s > 1\<close> by real_asymp
  finally have "(\<lambda>x. sum_upto (\<lambda>x. real x powr -s) x - \<zeta> - x powr (1 - s) / (1 - s) +
             x powr (1 - s) / (1 - s)) \<in> o(\<lambda>_. 1)"
    by (rule sum_in_smallo) (use \<open>s > 1\<close> in real_asymp)
  thus ?thesis by (simp add: smallo_imp_asymp_equiv)
qed

lemma zeta_partial_sum_pos_bigtheta:
  assumes "s > 0" "s \<noteq> 1"
  shows   "sum_upto (\<lambda>n. n powr -s) \<in> \<Theta>(\<lambda>x. x powr max 0 (1 - s))"
proof (cases "s > 1")
  case False
  thus ?thesis
    using asymp_equiv_imp_bigtheta[OF zeta_partial_sum_01_asymp_equiv[of s]] assms
    by (simp add: max_def)
next
  case True
  have [simp]: "Re (zeta s) \<noteq> 0"
    using True zeta_Re_gt_1_nonzero[of s] zeta_real[of s] by (auto elim!: Reals_cases)
  show ?thesis
    using True asymp_equiv_imp_bigtheta[OF zeta_partial_sum_gt_1_asymp_equiv[of s]]
    by (simp add: max_def)
qed

lemma zeta_partial_sum_le_neg:
  assumes "s > 0"
  shows   "\<exists>c>0. \<forall>x\<ge>1. \<bar>sum_upto (\<lambda>n. n powr s) x - x powr (1 + s) / (1 + s)\<bar> \<le> c * x powr s"
proof (rule sum_upto_asymptotics_lift_nat_real)
  show "(\<lambda>n. (\<Sum>k = 1..n. real k powr s) - (real n powr (1 + s) / (1 + s)))
          \<in> O(\<lambda>n. real n powr s)"
    using zeta_partial_sum_bigo_neg[OF assms(1)] by (simp add: algebra_simps)

  show "(\<lambda>n. real n powr (1 + s) / (1 + s) - (real (Suc n) powr (1 + s) / (1 + s)))
          \<in> O(\<lambda>n. real n powr s)"
    using assms by real_asymp
  show "(\<lambda>n. real n powr s) \<in> O(\<lambda>n. real (Suc n) powr s)"
    by real_asymp
  show "mono_on (\<lambda>a. a powr s) {1..} \<or> mono_on (\<lambda>x. - (x powr s)) {1..}"
    using assms by (intro disjI1) (auto intro!: mono_onI powr_mono2)
  show "mono_on (\<lambda>a. a powr (1 + s) / (1 + s)) {1..} \<or>
        mono_on (\<lambda>x. - (x powr (1 + s) / (1 + s))) {1..}"
    using assms by (intro disjI1 divide_right_mono powr_mono2 mono_onI) auto
qed auto

lemma zeta_partial_sum_neg_asymp_equiv:
  assumes "s > 0"
  shows "sum_upto (\<lambda>n. n powr s) \<sim>[at_top] (\<lambda>x. x powr (1 + s) / (1 + s))"
proof -
  from zeta_partial_sum_le_neg[of s] assms obtain c where
    c: "c > 0" "\<forall>x\<ge>1. \<bar>sum_upto (\<lambda>x. real x powr s) x - x powr (1 + s) / (1 + s)\<bar> \<le> c * x powr s"
    by auto
  hence "(\<lambda>x. sum_upto (\<lambda>x. real x powr s) x - x powr (1 + s) / (1 + s)) \<in> O(\<lambda>x. x powr s)"
    by (intro bigoI[of _ c] eventually_mono[OF eventually_ge_at_top[of 1]]) auto
  also have "(\<lambda>x. x powr s) \<in> o(\<lambda>x. x powr (1 + s) / (1 + s))"
    using assms by real_asymp
  finally show ?thesis
    by (rule smallo_imp_asymp_equiv)
qed

end