(*
    File:      Partial_Summation.thy
    Author:    Manuel Eberl, TU München
    
    The partial summation rule as given by Apostol in "Introduction to Analytic Number Theory"
*)
section \<open>Partial summation\<close>
theory Partial_Summation
  imports
    "HOL-Analysis.Analysis"
    Arithmetic_Summatory
begin

lemma finite_vimage_real_of_nat_greaterThanAtMost: "finite (real -` {y<..x})"
proof (rule finite_subset)
  show "real -` {y<..x} \<subseteq> {nat \<lfloor>y\<rfloor>..nat \<lceil>x\<rceil>}"
    by (cases "x \<ge> 0"; cases "y \<ge> 0")
        (auto simp: nat_le_iff le_nat_iff le_ceiling_iff floor_le_iff)
qed auto

context
  fixes a :: "nat \<Rightarrow> 'a :: {banach, real_normed_algebra}"
  fixes f f' :: "real \<Rightarrow> 'a"
  fixes A
  fixes X :: "real set"
  fixes x y :: real
  defines "A \<equiv> sum_upto a"
  assumes fin: "finite X"
  assumes xy: "0 \<le> y" "y < x"
  assumes deriv: "\<And>z. z \<in> {y..x} - X \<Longrightarrow> (f has_vector_derivative f' z) (at z)"
  assumes cont_f: "continuous_on {y..x} f"
begin

lemma partial_summation_strong:
  "((\<lambda>t. A t * f' t) has_integral 
       (A x * f x - A y * f y - (\<Sum>n \<in> real -` {y<..x}. a n * f n))) {y..x}"
proof -
  define chi :: "nat \<Rightarrow> real \<Rightarrow> real" where "chi = (\<lambda>n t. if n \<le> t then 1 else 0)"
  have "((\<lambda>t. sum_upto (\<lambda>n. a n * (chi n t *\<^sub>R f' t)) x) has_integral 
          (sum_upto (\<lambda>n. a n * (f x - f (max n y))) x)) {y..x}" (is "(_ has_integral ?I) _")
    unfolding sum_upto_def
  proof (intro has_integral_sum ballI finite_Nats_le_real, goal_cases)
    case (1 n)
    have "(f' has_integral (f x - f (max n y))) {max n y..x}"
      using xy 1
      by (intro fundamental_theorem_of_calculus_strong[OF fin])
         (auto intro!: continuous_on_subset[OF cont_f] deriv)
    also have "?this \<longleftrightarrow> ((\<lambda>t. (if t \<in> {max n y..x} then 1 else 0) *\<^sub>R f' t) 
                  has_integral (f x - f (max n y))) {max n y..x}"
      by (intro has_integral_cong) (simp_all add: chi_def)
    finally have "((\<lambda>t. (if t \<in> {max n y..x} then 1 else 0) *\<^sub>R f' t) 
                     has_integral (f x - f (max n y))) {y..x}"
      by (rule has_integral_on_superset) auto
    also have "?this \<longleftrightarrow> ((\<lambda>t. chi n t *\<^sub>R f' t) has_integral (f x - f (max n y))) {y..x}"
      by (intro has_integral_cong) (auto simp: chi_def)
    finally show ?case by (intro has_integral_mult_right)
  qed
  also have "?this \<longleftrightarrow> ((\<lambda>t. A t * f' t) has_integral ?I) {y..x}"
    unfolding sum_upto_def A_def chi_def sum_distrib_right using xy
    by (intro has_integral_cong sum.mono_neutral_cong_right finite_Nats_le_real) auto
  also have "sum_upto (\<lambda>n. a n * (f x - f (max (real n) y))) x =
               A x * f x - (\<Sum>n | n > 0 \<and> real n \<le> x.  a n * f (max (real n) y))"
    by (simp add: sum_upto_def ring_distribs sum_subtractf sum_distrib_right A_def)
  also have "{n. n > 0 \<and> real n \<le> x} = {n. n > 0 \<and> real n \<le> y} \<union> real -` {y<..x}"
    using xy by auto
  also have "sum (\<lambda>n. a n * f (max (real n) y)) \<dots> = 
               (\<Sum>n | 0 < n \<and> real n \<le> y. a n * f (max (real n) y)) +
               (\<Sum>n \<in> real -` {y<..x}. a n * f (max (real n) y))" (is "_ = ?S1 + ?S2")
    by (intro sum.union_disjoint finite_Nats_le_real finite_vimage_real_of_nat_greaterThanAtMost) 
       auto
  also have "?S1 = sum_upto (\<lambda>n. a n * f y) y" unfolding sum_upto_def 
    by (intro sum.cong refl) (auto simp: max_def)
  also have "\<dots> = A y * f y" by (simp add: A_def sum_upto_def sum_distrib_right)
  also have "?S2 = (\<Sum>n \<in> real -` {y<..x}. a n * f n)"
    by (intro sum.cong refl) (auto simp: max_def)
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma partial_summation_integrable_strong: 
        "(\<lambda>t. A t * f' t) integrable_on {y..x}"
  and partial_summation_strong': 
        "(\<Sum>n\<in>real -` {y<..x}. a n * f n) = 
            A x * f x - A y * f y - integral {y..x} (\<lambda>t. A t * f' t)"
  using partial_summation_strong by (simp_all add: has_integral_iff algebra_simps)

end


context
  fixes a :: "nat \<Rightarrow> 'a :: {banach, real_normed_algebra}"
  fixes f f' :: "real \<Rightarrow> 'a"
  fixes A
  fixes X :: "real set"
  fixes x :: real
  defines "A \<equiv> sum_upto a"
  assumes fin: "finite X"
  assumes x: "x > 0"
  assumes deriv: "\<And>z. z \<in> {0..x} - X \<Longrightarrow> (f has_vector_derivative f' z) (at z)"
  assumes cont_f: "continuous_on {0..x} f"
begin

lemma partial_summation_sum_upto_strong:
  "((\<lambda>t. A t * f' t) has_integral (A x * f x - sum_upto (\<lambda>n. a n * f n) x)) {0..x}"
proof -
  have "(\<Sum>n\<in>real -` {0<..x}. a n * f n) = sum_upto (\<lambda>n. a n * f n) x"
    unfolding sum_upto_def by (intro sum.cong refl) auto
  thus ?thesis
  using partial_summation_strong[OF fin order.refl x deriv cont_f, of a]
  by (simp_all add: A_def)
qed

lemma partial_summation_integrable_sum_upto_strong: 
        "(\<lambda>t. A t * f' t) integrable_on {0..x}"
  and partial_summation_sum_upto_strong': 
        "sum_upto (\<lambda>n. a n * f n) x = 
            A x * f x - integral {0..x} (\<lambda>t. A t * f' t)"
  using partial_summation_sum_upto_strong by (simp_all add: has_integral_iff algebra_simps)
  
end

end
