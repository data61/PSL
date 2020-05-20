section \<open>Connection of Euler--MacLaurin summation to Landau symbols\<close>
theory Euler_MacLaurin_Landau
imports 
  Euler_MacLaurin
  Landau_Symbols.Landau_More
begin

subsection \<open>$O$-bound for the remainder term\<close>  

text \<open>
  Landau symbols allow us to state the bounds on the remainder terms 
  from the Euler--MacLaurin formula a bit more nicely.
\<close>

lemma
  fixes f :: "real \<Rightarrow> 'a :: {real_normed_field, banach}"
    and g g' :: "real \<Rightarrow> real"
  assumes fin:     "finite Y"
  assumes cont_f:  "continuous_on {a..} f"
  assumes cont_g:  "continuous_on {a..} g"
  assumes cont_g': "continuous_on {a..} g'"
  assumes limit_g: "(g \<longlongrightarrow> 0) at_top"
  assumes f_bound: "\<And>x. x \<ge> a \<Longrightarrow> norm (f x) \<le> g' x"
  assumes deriv:   "\<And>x. x \<in> {a..} - Y \<Longrightarrow> (g has_field_derivative -g' x) (at x)"
  shows   EM_remainder_strong_bigo_int: "(\<lambda>x::int. norm (EM_remainder n f x)) \<in> O(g)"
    and   EM_remainder_strong_bigo_nat: "(\<lambda>x::nat. norm (EM_remainder n f x)) \<in> O(g)"
proof -
  from bounded_pbernpoly[of n] obtain D where D: "\<forall>x. \<bar>pbernpoly n x\<bar> \<le> D" by auto
  from norm_EM_remainder_le_strong_int'[OF fin D assms(2-)]
    have *: "\<And>x. x \<ge> a \<longrightarrow> norm (EM_remainder n f x) \<le> D / fact n * g x" by auto
  have **: "eventually (\<lambda>x::int. norm (EM_remainder n f x) \<le> abs (D / fact n) * abs (g x)) at_top"
    using eventually_ge_at_top[of "ceiling a"]
  proof eventually_elim
    case (elim x)
    with *[of x] have "norm (EM_remainder n f x) \<le> D / fact n * g x" by (simp add: ceiling_le_iff)
    also have "\<dots> \<le> abs (D / fact n * g x)" by (rule abs_ge_self)
    also have "\<dots> = abs (D / fact n) * abs (g x)" by (simp add: abs_mult)
    finally show ?case .
  qed
  thus "(\<lambda>x::int. norm (EM_remainder n f x)) \<in> O(g)"
    by (intro bigoI[of _ "abs D / fact n"]) (auto elim!: eventually_mono)
  hence "(\<lambda>x::nat. norm (EM_remainder n f (int x))) \<in> O(\<lambda>x. g (of_int (int x)))"
    by (rule landau_o.big.compose) (fact filterlim_int_sequentially)
  thus "(\<lambda>x::nat. norm (EM_remainder n f x)) \<in> O(g)" by simp
qed


subsection \<open>Asymptotic expansion of the harmonic numbers\<close>

text \<open>
  We can now show the asymptotic expansion
  \[H_n = \ln n + \gamma + \frac{1}{2n} - \sum_{i=1}^m \frac{B_{2i}}{2i} n^{-2i} + O(n^{-2m-2})\]
\<close>

lemma harm_remainder_bigo:
  assumes "N > 0"
  shows   "harm_remainder N \<in> O(\<lambda>n. 1 / real n ^ (2 * N + 1))"
proof -
  from harm_remainder_bound[OF assms] guess C ..
  thus ?thesis
    by (intro bigoI[of _ C] eventually_mono[OF eventually_ge_at_top[of 1]]) auto
qed

lemma harm_expansion_bigo:
  fixes N :: nat
  defines "T \<equiv> \<lambda>n. ln n + euler_mascheroni + 1 / (2*n) -
                     (\<Sum>i=1..N. bernoulli (2*i) / ((2*i) * n ^ (2*i)))"
  defines "S \<equiv> (\<lambda>n. bernoulli (2*(Suc N)) / ((2*Suc N) * real n ^ (2*Suc N)))"
  shows "(\<lambda>n. harm n - T n) \<in> O(\<lambda>n. 1 / real n ^ (2 * N + 2))"
proof -
  have "(\<lambda>n. harm n - T n) \<in> \<Theta>(\<lambda>n. -S n - harm_remainder (Suc N) n)"
    by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of "0::nat"]]) 
       (auto simp: T_def harm_expansion[of _ "Suc N"] S_def)
  also have "(\<lambda>n. -S n - harm_remainder (Suc N) n) \<in> O(\<lambda>n. 1 / real n ^ (2 * N + 2))"
  proof (intro sum_in_bigo)
    show "(\<lambda>x. - S x) \<in> O(\<lambda>n. 1 / real n ^ (2 * N + 2))" unfolding S_def
      by (rule landau_o.big.compose[OF _ filterlim_real_sequentially]) simp
    have "harm_remainder (Suc N) \<in> O(\<lambda>n. 1 / real n ^ (2 * Suc N + 1))"
      by (rule harm_remainder_bigo) simp_all
    also have "(\<lambda>n. 1 / real n ^ (2 * Suc N + 1)) \<in> O(\<lambda>n. 1 / real n ^ (2 * N + 2))"
      by (rule landau_o.big.compose[OF _ filterlim_real_sequentially]) simp
    finally show "harm_remainder (Suc N) \<in> \<dots>" .
  qed
  finally show ?thesis .
qed

lemma harm_expansion_bigo_simple1:
  "(\<lambda>n. harm n - (ln n + euler_mascheroni + 1 / (2 * n))) \<in> O(\<lambda>n. 1 / n ^ 2)"
  using harm_expansion_bigo[of 0] by (simp add: power2_eq_square)

lemma harm_expansion_bigo_simple2:
  "(\<lambda>n. harm n - (ln n + euler_mascheroni)) \<in> O(\<lambda>n. 1 / n)"
proof -
  have "(\<lambda>n. harm n - (ln n + euler_mascheroni + 1 / (2 * n)) + 1 / (2 * n)) \<in> O(\<lambda>n. 1 / n)"
  proof (rule sum_in_bigo)
    have "(\<lambda>n. harm n - (ln n + euler_mascheroni + 1 / (2 * n))) \<in> O(\<lambda>n. 1 / real n ^ 2)"
      using harm_expansion_bigo_simple1 by simp
    also have "(\<lambda>n. 1 / real n ^ 2) \<in> O(\<lambda>n. 1 / real n)"
      by (rule landau_o.big.compose[OF _ filterlim_real_sequentially]) simp_all
    finally show "(\<lambda>n. harm n - (ln n + euler_mascheroni + 1 / (2 * n))) \<in> O(\<lambda>n. 1 / n)" by simp
  qed simp_all
  thus ?thesis by (simp add: algebra_simps)
qed

lemma harm_expansion_bigo_simple':
  "harm =o (\<lambda>n. ln n + euler_mascheroni + 1 / (2 * n)) +o O(\<lambda>n. 1 / n ^ 2)"
  using harm_expansion_bigo_simple1
  by (subst set_minus_plus [symmetric]) (simp_all add: fun_diff_def)


subsection \<open>Asymptotic expansion of the sum of inverse squares\<close>

text \<open>
  Similarly to before, we show
  \[\sum_{i=1}^n \frac{1}{i^2} = \frac{\pi^2}{6} - \frac{1}{n} + \frac{1}{2n^2} - 
     \sum_{i=1}^m B_{2i} n^{-2i-1} + O(n^{-2m-3})\]  
\<close>

context
  fixes R :: "nat \<Rightarrow> nat \<Rightarrow> real"
  defines "R \<equiv> (\<lambda>N n. EM_remainder (2*N+1) (\<lambda>x. -fact (2*N+2) / x ^ (2*N+3)) (int n))"
begin

lemma sum_inverse_squares_remainder_bigo:
  assumes "N > 0"
  shows   "R N \<in> O(\<lambda>n. 1 / real n ^ (2 * N + 2))"
proof -
  from sum_inverse_squares_remainder_bound[OF assms] guess C ..
  thus ?thesis
    by (intro bigoI[of _ C] eventually_mono[OF eventually_ge_at_top[of 1]]) (auto simp: R_def)
qed

lemma sum_inverse_squares_expansion_bigo:
  fixes N :: nat
  defines "T \<equiv> \<lambda>n. pi ^ 2 / 6 - 1 / n + 1 / (2*n ^ 2) -
                     (\<Sum>i=1..N. bernoulli (2*i) / (n ^ (2*i+1)))"
  defines "S \<equiv> (\<lambda>n. bernoulli (2*(Suc N)) / (real n ^ (2*N+3)))"
  shows "(\<lambda>n. (\<Sum>i=1..n. 1 / real i ^ 2) - T n) \<in> O(\<lambda>n. 1 / real n ^ (2 * N + 3))"
proof -
  have 3: "3 = Suc (Suc (Suc 0))" by simp
  have "(\<lambda>n. (\<Sum>i=1..n. 1 / real i ^ 2) - T n) \<in> \<Theta>(\<lambda>n. -S n - R (Suc N) n)" unfolding R_def
    by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of "0::nat"]])
       (auto simp: T_def sum_inverse_squares_expansion[of _ "Suc N"] S_def 3
             simp del: One_nat_def)
  also have "(\<lambda>n. -S n - R (Suc N) n) \<in> O(\<lambda>n. 1 / real n ^ (2 * N + 3))"
  proof (intro sum_in_bigo)
    show "(\<lambda>x. - S x) \<in> O(\<lambda>n. 1 / real n ^ (2 * N + 3))" unfolding S_def
      by (rule landau_o.big.compose[OF _ filterlim_real_sequentially]) simp
    have "R (Suc N) \<in> O(\<lambda>n. 1 / real n ^ (2 * Suc N + 2))"
      by (rule sum_inverse_squares_remainder_bigo) simp_all
    also have "2 * Suc N + 2 = 2 * N + 4" by simp
    also have "(\<lambda>n. 1 / real n ^ (2 * N + 4)) \<in> O(\<lambda>n. 1 / real n ^ (2 * N + 3))"
      by (rule landau_o.big.compose[OF _ filterlim_real_sequentially]) simp
    finally show "R (Suc N) \<in> \<dots>" .
  qed
  finally show ?thesis .
qed

lemma sum_inverse_squares_expansion_bigo_simple:
  "(\<lambda>n. (\<Sum>i=1..n. 1 / real i ^ 2) - (pi ^ 2 / 6 - 1 / n + 1 / (2*n^2))) \<in> O(\<lambda>n. 1 / n ^ 3)"
  using sum_inverse_squares_expansion_bigo[of 0] by (simp add: power2_eq_square)

lemma sum_inverse_squares_expansion_bigo_simple':
  "(\<lambda>n. (\<Sum>i=1..n. 1 / real i ^ 2)) =o (\<lambda>n. pi ^ 2 / 6 - 1 / n + 1 / (2*n^2)) +o O(\<lambda>n. 1 / n^3)"
  using sum_inverse_squares_expansion_bigo_simple
  by (subst set_minus_plus [symmetric]) (simp_all add: fun_diff_def)

end

end
