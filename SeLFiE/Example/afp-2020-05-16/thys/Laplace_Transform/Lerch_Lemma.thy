section \<open>Lerch Lemma\<close>
theory Lerch_Lemma
  imports
     "HOL-Analysis.Analysis"
begin

text \<open>The main tool to prove uniqueness of the Laplace transform.\<close>

lemma lerch_lemma_real:
  fixes h::"real \<Rightarrow> real"
  assumes h_cont[continuous_intros]: "continuous_on {0 .. 1} h"
  assumes int_0: "\<And>n. ((\<lambda>u. u ^ n * h u) has_integral 0) {0 .. 1}"
  assumes u: "0 \<le> u" "u \<le> 1"
  shows "h u = 0"
proof -
  from Stone_Weierstrass_uniform_limit[OF compact_Icc h_cont]
  obtain g where g: "uniform_limit {0..1} g h sequentially" "polynomial_function (g n)" for n
    by blast
  then have rpf_g: "real_polynomial_function (g n)" for n
    by (simp add: real_polynomial_function_eq)

  let ?P = "\<lambda>n x. h x * g n x"
  have continuous_on_g[continuous_intros]: "continuous_on s (g n)" for s n
    by (rule continuous_on_polymonial_function) fact
  have P_cont: "continuous_on {0 .. 1} (?P n)" for n
    by (auto intro!: continuous_intros)
  have "uniform_limit {0 .. 1} (\<lambda>n x. h x * g n x) (\<lambda>x. h x * h x) sequentially"
    by (auto intro!: uniform_limit_intros g assms compact_imp_bounded compact_continuous_image)

  from uniform_limit_integral[OF this P_cont]
  obtain I J where
    I: "(\<And>n. (?P n has_integral I n) {0..1})"
    and J: "((\<lambda>x. h x * h x) has_integral J) {0..1}"
    and IJ: "I \<longlonglongrightarrow> J"
    by auto

  have "(?P n has_integral 0) {0..1}" for n
  proof -
    from real_polynomial_function_imp_sum[OF rpf_g]
    obtain gn ga where "g n = (\<lambda>x. \<Sum>i\<le>gn. ga i * x ^ i)" by metis
    then have "?P n x = (\<Sum>i\<le>gn. x ^ i * h x * ga i)" for x
      by (auto simp: sum_distrib_left algebra_simps)
    moreover have "((\<lambda>x. \<dots> x) has_integral 0) {0 .. 1}"
      by (auto intro!: has_integral_sum[THEN has_integral_eq_rhs] has_integral_mult_left assms)
    ultimately show ?thesis by simp
  qed
  with I have "I n = 0" for n
    using has_integral_unique by blast
  with IJ J have "((\<lambda>x. h x * h x) has_integral 0) (cbox 0 1)"
    by (metis (full_types) LIMSEQ_le_const LIMSEQ_le_const2 box_real(2) dual_order.antisym order_refl)
  with _ _ have "h u * h u = 0"
    by (rule has_integral_0_cbox_imp_0) (auto intro!: continuous_intros u)
  then show "h u = 0"
    by simp
qed

lemma lerch_lemma:
  fixes h::"real \<Rightarrow> 'a::euclidean_space"
  assumes [continuous_intros]: "continuous_on {0 .. 1} h"
  assumes int_0: "\<And>n. ((\<lambda>u. u ^ n *\<^sub>R h u) has_integral 0) {0 .. 1}"
  assumes u: "0 \<le> u" "u \<le> 1"
  shows "h u = 0"
proof (rule euclidean_eqI)
  fix b::'a assume "b \<in> Basis"
  have "continuous_on {0 .. 1} (\<lambda>x. h x \<bullet> b)"
    by (auto intro!: continuous_intros)
  moreover
  from \<open>b \<in> Basis\<close> have "((\<lambda>u. u ^ n * (h u \<bullet> b)) has_integral 0) {0 .. 1}" for n
    using int_0[of n] has_integral_componentwise_iff[of "\<lambda>u. u ^ n *\<^sub>R h u" 0 "{0 .. 1}"]
    by auto
  moreover note u
  ultimately show "h u \<bullet> b = 0 \<bullet> b"
    unfolding inner_zero_left
    by (rule lerch_lemma_real)
qed

end
