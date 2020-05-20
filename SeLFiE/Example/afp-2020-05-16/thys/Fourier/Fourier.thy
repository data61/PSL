section\<open>The basics of Fourier series\<close>

text\<open>Ported from HOL Light; thanks to Manuel Eberl for help with the real asymp proof methods\<close>

theory "Fourier"
  imports Periodic Square_Integrable "HOL-Real_Asymp.Real_Asymp" Confine Fourier_Aux2
begin

subsection\<open>Orthonormal system of L2 functions and their Fourier coefficients\<close>

definition orthonormal_system :: "'a::euclidean_space set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where "orthonormal_system S w \<equiv> \<forall>m n. l2product S (w m) (w n) = (if m = n then 1 else 0)"

definition orthonormal_coeff :: "'a::euclidean_space set \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real"
  where "orthonormal_coeff S w f n = l2product S (w n) f"

lemma orthonormal_system_eq: "orthonormal_system S w \<Longrightarrow> l2product S (w m) (w n) = (if m = n then 1 else 0)"
  by (simp add: orthonormal_system_def)

lemma orthonormal_system_l2norm:
   "orthonormal_system S w \<Longrightarrow> l2norm S (w i) = 1"
  by (simp add: l2norm_def orthonormal_system_def)

lemma orthonormal_partial_sum_diff:
  assumes os: "orthonormal_system S w" and w: "\<And>i. (w i) square_integrable S"
    and f: "f square_integrable S" and "finite I"
  shows "(l2norm S (\<lambda>x. f x - (\<Sum>i\<in>I. a i * w i x)))\<^sup>2 =
        (l2norm S f)\<^sup>2 + (\<Sum>i\<in>I. (a i)\<^sup>2) -  2 * (\<Sum>i\<in>I. a i * orthonormal_coeff S w f i)"
proof -
  have "S \<in> sets lebesgue"
    using f square_integrable_def by blast
  then have "(\<lambda>x. \<Sum>i\<in>I. a i * w i x) square_integrable S"
    by (intro square_integrable_sum square_integrable_lmult w \<open>finite I\<close>)
  with assms show ?thesis
    apply (simp add: l2norm_pow_2 orthonormal_coeff_def orthonormal_system_def)
    apply (simp add: l2product_rdiff l2product_sym
           l2product_rsum l2product_rmult algebra_simps power2_eq_square if_distrib [of "\<lambda>x. _ * x"])
    done
qed

lemma orthonormal_optimal_partial_sum:
  assumes "orthonormal_system S w" "\<And>i. (w i) square_integrable S"
          "f square_integrable S" "finite I"
  shows "l2norm S (\<lambda>x. f x - (\<Sum>i\<in>I. orthonormal_coeff S w f i * w i x))
       \<le> l2norm S (\<lambda>x. f x - (\<Sum>i\<in>I. a i * w i x))"
proof -
  have "2 * (a i * l2product S f(w i)) \<le> (a i)\<^sup>2 + (l2product S f(w i))\<^sup>2" for i
    using sum_squares_bound [of "a i" "l2product S f(w i)"]
    by (force simp: algebra_simps)
  then have *: "2 * (\<Sum>i\<in>I. a i * l2product S f(w i)) \<le> (\<Sum>i\<in>I. (a i)\<^sup>2 + (l2product S f(w i))\<^sup>2)"
    by (simp add: sum_distrib_left sum_mono)
  have S: "S \<in> sets lebesgue"
    using assms square_integrable_def by blast
  with assms * show ?thesis
    apply (simp add: l2norm_le square_integrable_sum square_integrable_diff square_integrable_lmult flip: l2norm_pow_2)
    apply (simp add: orthonormal_coeff_def orthonormal_partial_sum_diff)
    apply (simp add: l2product_sym power2_eq_square sum.distrib)
    done
qed

lemma Bessel_inequality:
  assumes "orthonormal_system S w" "\<And>i. (w i) square_integrable S"
    "f square_integrable S" "finite I"
  shows "(\<Sum>i\<in>I. (orthonormal_coeff S w f i)\<^sup>2) \<le> (l2norm S f)\<^sup>2"
  using orthonormal_partial_sum_diff [OF assms, of "orthonormal_coeff S w f"]
  apply (simp add: algebra_simps flip: power2_eq_square)
  by (metis (lifting) add_diff_cancel_left' diff_ge_0_iff_ge zero_le_power2)

lemma Fourier_series_square_summable:
  assumes os: "orthonormal_system S w" and w: "\<And>i. (w i) square_integrable S"
    and f: "f square_integrable S"
  shows "summable (confine (\<lambda>i. (orthonormal_coeff S w f i) ^ 2) I)"
proof -
  have "incseq (\<lambda>n. \<Sum>i\<in>I \<inter> {..n}. (orthonormal_coeff S w f i)\<^sup>2)"
    by (auto simp: incseq_def intro: sum_mono2)
  moreover have "\<And>i. (\<Sum>i\<in>I \<inter> {..i}. (orthonormal_coeff S w f i)\<^sup>2) \<le> (l2norm S f)\<^sup>2"
    by (simp add: Bessel_inequality assms)
  ultimately obtain L where "(\<lambda>n. \<Sum>i\<in>I \<inter> {..n}. (orthonormal_coeff S w f i)\<^sup>2) \<longlonglongrightarrow> L"
    using incseq_convergent by blast
  then have "\<forall>r>0. \<exists>no. \<forall>n\<ge>no. \<bar>(\<Sum>i\<in>{..n} \<inter> I. (orthonormal_coeff S w f i)\<^sup>2) - L\<bar> < r"
    by (simp add: LIMSEQ_iff Int_commute)
  then show ?thesis
    by (auto simp: summable_def sums_confine_le LIMSEQ_iff)
qed

lemma orthonormal_Fourier_partial_sum_diff_squared:
  assumes os: "orthonormal_system S w" and w: "\<And>i. (w i) square_integrable S"
    and f: "f square_integrable S" and "finite I"
  shows "(l2norm S (\<lambda>x. f x -(\<Sum>i\<in>I. orthonormal_coeff S w f i * w i x)))\<^sup>2 =
         (l2norm S f)\<^sup>2 - (\<Sum>i\<in>I. (orthonormal_coeff S w f i)\<^sup>2)"
  using orthonormal_partial_sum_diff [OF assms, where a = "orthonormal_coeff S w f"]
  by (simp add: power2_eq_square)


lemma Fourier_series_l2_summable:
  assumes os: "orthonormal_system S w" and w: "\<And>i. (w i) square_integrable S"
    and f: "f square_integrable S"
  obtains g where "g square_integrable S"
                  "(\<lambda>n. l2norm S (\<lambda>x. (\<Sum>i\<in>I \<inter> {..n}. orthonormal_coeff S w f i * w i x) - g x))
                   \<longlonglongrightarrow> 0"
proof -
  have S: "S \<in> sets lebesgue"
    using f square_integrable_def by blast
  let ?\<Theta> = "\<lambda>A x. (\<Sum>i\<in>I \<inter> A. orthonormal_coeff S w f i * w i x)"
  let ?\<Psi> = "confine (\<lambda>i. (orthonormal_coeff S w f i)\<^sup>2) I"
  have si: "?\<Theta> A square_integrable S" if "finite A" for A
    by (force intro: square_integrable_lmult w square_integrable_sum S that)
  have "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. l2norm S (\<lambda>x. ?\<Theta> {..m} x - ?\<Theta> {..n} x) < e"
    if "e > 0" for e
  proof -
    have "summable ?\<Psi>"
      by (rule Fourier_series_square_summable [OF os w f])
    then have "Cauchy (\<lambda>n. sum ?\<Psi> {..n})"
      by (simp add: summable_def sums_def_le convergent_eq_Cauchy)
    then obtain M where M: "\<And>m n. \<lbrakk>m\<ge>M; n\<ge>M\<rbrakk> \<Longrightarrow> dist (sum ?\<Psi> {..m}) (sum ?\<Psi> {..n}) < e\<^sup>2"
      using \<open>e > 0\<close> unfolding Cauchy_def by (drule_tac x="e^2" in spec) auto
    have "\<lbrakk>m\<ge>M; n\<ge>M\<rbrakk> \<Longrightarrow> l2norm S (\<lambda>x. ?\<Theta> {..m} x - ?\<Theta> {..n} x) < e" for m n
    proof (induct m n rule: linorder_class.linorder_wlog)
      case (le m n)
      have sum_diff: "sum f(I \<inter> {..n}) - sum f(I \<inter> {..m}) = sum f(I \<inter> {Suc m..n})" for f :: "nat \<Rightarrow> real"
      proof -
        have "(I \<inter> {..n}) =  (I \<inter> {..m} \<union> I \<inter> {Suc m..n})" "(I \<inter> {..m}) \<inter> (I \<inter> {Suc m..n}) = {}"
          using le by auto
        then show ?thesis
          by (simp add: algebra_simps flip: sum.union_disjoint)
      qed
      have "(l2norm S (\<lambda>x. ?\<Theta> {..n} x - ?\<Theta> {..m} x))^2
            \<le> \<bar>(\<Sum>i\<in>I \<inter> {..n}. (orthonormal_coeff S w f i)\<^sup>2) - (\<Sum>i\<in>I \<inter> {..m}. (orthonormal_coeff S w f i)\<^sup>2)\<bar>"
      proof (simp add: sum_diff)
        have "(l2norm S (?\<Theta> {Suc m..n}))\<^sup>2
            = (\<Sum>i\<in>I \<inter> {Suc m..n}. l2product S (\<lambda>x. \<Sum>j\<in>I \<inter> {Suc m..n}. orthonormal_coeff S w f j * w j x)
                                               (\<lambda>x. orthonormal_coeff S w f i * w i x))"
          by (simp add: l2norm_pow_2 l2product_rsum si w)
        also have "\<dots> = (\<Sum>i\<in>I \<inter> {Suc m..n}. \<Sum>j\<in>I \<inter> {Suc m..n}.
                            orthonormal_coeff S w f j * orthonormal_coeff S w f i * l2product S (w j) (w i))"
          by (simp add: l2product_lsum l2product_lmult l2product_rmult si w flip: mult.assoc)
        also have "\<dots> \<le> \<bar>\<Sum>i\<in>I \<inter> {Suc m..n}. (orthonormal_coeff S w f i)\<^sup>2\<bar>"
          by (simp add: orthonormal_system_eq [OF os] power2_eq_square if_distrib [of "(*)_"] cong: if_cong)
        finally show "(l2norm S (?\<Theta> {Suc m..n}))\<^sup>2 \<le> \<bar>\<Sum>i\<in>I \<inter> {Suc m..n}. (orthonormal_coeff S w f i)\<^sup>2\<bar>" .
      qed
      also have "\<dots> < e\<^sup>2"
        using M [OF \<open>n\<ge>M\<close> \<open>m\<ge>M\<close>]
        by (simp add: dist_real_def sum_confine_eq_Int Int_commute)
      finally have "(l2norm S (\<lambda>x. ?\<Theta> {..m} x - ?\<Theta> {..n} x))^2 < e^2"
        using l2norm_diff [OF si si] by simp
      with \<open>e > 0\<close> show ?case
        by (simp add: power2_less_imp_less)
    next
      case (sym a b)
      then show ?case
        by (subst l2norm_diff) (auto simp: si)
    qed
    then show ?thesis
      by blast
  qed
  with that show thesis
    by (blast intro: si [of "{.._}"] l2_complete [of "\<lambda>n. ?\<Theta> {..n}"])
qed

lemma Fourier_series_l2_summable_strong:
  assumes os: "orthonormal_system S w" and w: "\<And>i. (w i) square_integrable S"
    and f: "f square_integrable S"
  obtains g where "g square_integrable S"
          "\<And>i. i \<in> I \<Longrightarrow> orthonormal_coeff S w (\<lambda>x. f x - g x) i = 0"
          "(\<lambda>n. l2norm S (\<lambda>x. (\<Sum>i\<in>I \<inter> {..n}. orthonormal_coeff S w f i * w i x) - g x))
           \<longlonglongrightarrow> 0"
proof -
  have S: "S \<in> sets lebesgue"
    using f square_integrable_def by blast
  obtain g where g: "g square_integrable S"
            and teng: "(\<lambda>n. l2norm S (\<lambda>x. (\<Sum>i\<in>I \<inter> {..n}. orthonormal_coeff S w f i * w i x) - g x))
                       \<longlonglongrightarrow> 0"
    using Fourier_series_l2_summable [OF assms] .
  show thesis
  proof
    show "orthonormal_coeff S w (\<lambda>x. f x - g x) i = 0"
      if "i \<in> I" for i
    proof (rule tendsto_unique)
      let ?\<Theta> = "\<lambda>A x. (\<Sum>i\<in>I \<inter> A. orthonormal_coeff S w f i * w i x)"
      let ?f = "\<lambda>n. l2product S (w i) (\<lambda>x. (f x - ?\<Theta> {..n} x) + (?\<Theta> {..n} x - g x))"
      show "?f \<longlonglongrightarrow> orthonormal_coeff S w (\<lambda>x. f x - g x) i"
        by (simp add: orthonormal_coeff_def)
      have 1: "(\<lambda>n. l2product S (w i) (\<lambda>x. f x - ?\<Theta> {..n} x)) \<longlonglongrightarrow> 0"
        proof (rule tendsto_eventually)
          have "l2product S (w i) (\<lambda>x. f x - ?\<Theta> {..j} x) = 0"
            if "j \<ge> i" for j
            using that \<open>i \<in> I\<close>
            apply (simp add: l2product_rdiff l2product_rsum l2product_rmult orthonormal_coeff_def w f S)
            apply (simp add: orthonormal_system_eq [OF os] if_distrib [of "(*)_"] cong: if_cong)
            done
          then show "\<forall>\<^sub>F n in sequentially. l2product S (w i) (\<lambda>x. f x - ?\<Theta> {..n} x) = 0"
            using eventually_at_top_linorder by blast
        qed
        have 2: "(\<lambda>n. l2product S (w i) (\<lambda>x. ?\<Theta> {..n} x - g x)) \<longlonglongrightarrow> 0"
        proof (intro Lim_null_comparison [OF _ teng] eventuallyI)
          show "norm (l2product S (w i) (\<lambda>x. ?\<Theta> {..n} x - g x)) \<le> l2norm S (\<lambda>x. ?\<Theta> {..n} x - g x)" for n
            using Schwartz_inequality_abs [of "w i" S "(\<lambda>x. ?\<Theta> {..n} x - g x)"]
            by (simp add: S g f w orthonormal_system_l2norm [OF os])
        qed
        show "?f \<longlonglongrightarrow> 0"
          using that tendsto_add [OF 1 2]
          by (subst l2product_radd) (simp_all add: l2product_radd w f g S)
      qed auto
  qed (auto simp: g teng)
qed


subsection\<open>Actual trigonometric orthogonality relations\<close>

lemma integrable_sin_cx:
  "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. sin(x * c))"
  by (intro continuous_imp_integrable_real continuous_intros)

lemma integrable_cos_cx:
  "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. cos(x * c))"
  by (intro continuous_imp_integrable_real continuous_intros)

lemma integral_cos_Z' [simp]:
  assumes "n \<in> \<int>"
  shows "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(n * x)) = (if n = 0 then 2 * pi else 0)"
  by (metis assms integral_cos_Z mult_commute_abs)

lemma integral_sin_and_cos:
  fixes m n::int
  shows
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(m * x) * cos(n * x)) = (if \<bar>m\<bar> = \<bar>n\<bar> then if n = 0 then 2 * pi else pi else 0)"
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(m * x) * sin(n * x)) = 0"
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin(m * x) * cos(n * x)) = 0"
  "\<lbrakk>m \<ge> 0; n \<ge> 0\<rbrakk> \<Longrightarrow> integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin (m * x) * sin (n * x)) = (if m = n \<and> n \<noteq> 0 then pi else 0)"
  "\<bar>integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin (m * x) * sin (n * x))\<bar> = (if \<bar>m\<bar> = \<bar>n\<bar> \<and> n \<noteq> 0 then pi else 0)"
  by (simp_all add: abs_if sin_times_sin cos_times_sin sin_times_cos cos_times_cos
                    integrable_sin_cx integrable_cos_cx mult_ac
               flip: distrib_left distrib_right left_diff_distrib right_diff_distrib)

lemma integral_sin_and_cos_Z [simp]:
  fixes m n::real
  assumes "m \<in> \<int>" "n \<in> \<int>"
  shows
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(m * x) * cos(n * x)) = (if \<bar>m\<bar> = \<bar>n\<bar> then if n = 0 then 2 * pi else pi else 0)"
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(m * x) * sin(n * x)) = 0"
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin(m * x) * cos(n * x)) = 0"
  "\<bar>integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin (m * x) * sin (n * x))\<bar> = (if \<bar>m\<bar> = \<bar>n\<bar> \<and> n \<noteq> 0 then pi else 0)"
  using assms unfolding Ints_def
     apply safe
  unfolding integral_sin_and_cos
     apply auto
  done

lemma integral_sin_and_cos_N [simp]:
  fixes m n::real
  assumes "m \<in> \<nat>" "n \<in> \<nat>"
  shows "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin (m * x) * sin (n * x)) = (if m = n \<and> n \<noteq> 0 then pi else 0)"
  using assms unfolding Nats_altdef1 by (auto simp: integral_sin_and_cos)


lemma integrable_sin_and_cos:
  fixes m n::int
  shows "integrable (lebesgue_on {a..b}) (\<lambda>x. cos(x * m) * cos(x * n))"
        "integrable (lebesgue_on {a..b}) (\<lambda>x. cos(x * m) * sin(x * n))"
        "integrable (lebesgue_on {a..b}) (\<lambda>x. sin(x * m) * cos(x * n))"
        "integrable (lebesgue_on {a..b}) (\<lambda>x. sin(x * m) * sin(x * n))"
  by (intro continuous_imp_integrable_real continuous_intros)+

lemma sqrt_pi_ge1: "sqrt pi \<ge> 1"
  using pi_gt3 by auto

definition trigonometric_set :: "nat \<Rightarrow> real \<Rightarrow> real"
  where "trigonometric_set n \<equiv>
    if n = 0 then \<lambda>x. 1 / sqrt(2 * pi)
    else if odd n then \<lambda>x. sin(real(Suc (n div 2)) * x) / sqrt(pi)
    else (\<lambda>x. cos((n div 2) * x) / sqrt pi)"

lemma trigonometric_set:
  "trigonometric_set 0 x = 1 / sqrt(2 * pi)"
  "trigonometric_set (Suc (2 * n)) x = sin(real(Suc n) * x) / sqrt(pi)"
  "trigonometric_set (2 * n + 2) x = cos(real(Suc n) * x) / sqrt(pi)"
  "trigonometric_set (Suc (Suc (2 * n))) x = cos(real(Suc n) * x) / sqrt(pi)"
  by (simp_all add: trigonometric_set_def algebra_simps add_divide_distrib)

lemma trigonometric_set_even:
   "trigonometric_set(2*k) = (if k = 0 then (\<lambda>x. 1 / sqrt(2 * pi)) else (\<lambda>x. cos(k * x) / sqrt pi))"
  by (induction k) (auto simp: trigonometric_set_def add_divide_distrib split: if_split_asm)

lemma orthonormal_system_trigonometric_set:
    "orthonormal_system {-pi..pi} trigonometric_set"
proof -
  have "l2product {-pi..pi} (trigonometric_set m) (trigonometric_set n) = (if m = n then 1 else 0)" for m n
  proof (induction m rule: odd_even_cases)
    case 0
    show ?case
      by (induction n rule: odd_even_cases) (auto simp: trigonometric_set l2product_def measure_restrict_space)
  next
    case (odd m)
    show ?case
      by (induction n rule: odd_even_cases) (auto simp: trigonometric_set l2product_def double_not_eq_Suc_double)
  next
    case (even m)
    show ?case
      by (induction n rule: odd_even_cases) (auto simp: trigonometric_set l2product_def Suc_double_not_eq_double)
  qed
  then show ?thesis
    unfolding orthonormal_system_def by auto
qed


lemma square_integrable_trigonometric_set:
   "(trigonometric_set i) square_integrable {-pi..pi}"
proof -
  have "continuous_on {-pi..pi} (\<lambda>x. sin ((1 + real n) * x) / sqrt pi)" for n
    by (intro continuous_intros) auto
  moreover
  have "continuous_on {-pi..pi} (\<lambda>x. cos (real i * x / 2) / sqrt pi) "
    by (intro continuous_intros) auto
  ultimately show ?thesis
    by (simp add: trigonometric_set_def)
qed

subsection\<open>Weierstrass for trigonometric polynomials\<close>

lemma Weierstrass_trig_1:
  fixes g :: "real \<Rightarrow> real"
  assumes contf: "continuous_on UNIV g" and periodic: "\<And>x. g(x + 2 * pi) = g x" and 1: "norm z = 1"
  shows "continuous (at z within (sphere 0 1)) (g \<circ> Im \<circ> Ln)"
proof (cases "Re z < 0")
  let ?f = "complex_of_real \<circ> g \<circ> (\<lambda>x. x + pi) \<circ> Im \<circ> Ln \<circ> uminus"
  case True
  have "continuous (at z within (sphere 0 1)) (complex_of_real \<circ> g \<circ> Im \<circ> Ln)"
  proof (rule continuous_transform_within)
    have [simp]: "z \<notin> \<real>\<^sub>\<ge>\<^sub>0"
      using True complex_nonneg_Reals_iff by auto
    show "continuous (at z within (sphere 0 1)) ?f"
      by (intro continuous_within_Ln continuous_intros continuous_on_imp_continuous_within [OF contf]) auto
    show "?f x' =  (complex_of_real \<circ> g \<circ> Im \<circ> Ln) x'"
      if "x' \<in> (sphere 0 1)" and "dist x' z < 1" for x'
    proof -
      have "x' \<noteq> 0"
        using that by auto
      with that show ?thesis
        by (auto simp: Ln_minus add.commute periodic)
    qed
  qed (use 1 in auto)
  then have "continuous (at z within (sphere 0 1)) (Re \<circ> complex_of_real \<circ> g \<circ> Im \<circ> Ln)"
    unfolding o_def by (rule continuous_Re)
  then show ?thesis
    by (simp add: o_def)
next
  case False
  let ?f = "complex_of_real \<circ> g \<circ> Im \<circ> Ln \<circ> uminus"
  have "z \<noteq> 0"
    using 1 by auto
  with False have "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    by (auto simp: not_less nonpos_Reals_def)
  then have "continuous (at z within (sphere 0 1)) (complex_of_real \<circ> g \<circ> Im \<circ> Ln)"
    by (intro continuous_within_Ln continuous_intros continuous_on_imp_continuous_within [OF contf]) auto
  then have "continuous (at z within (sphere 0 1)) (Re \<circ> complex_of_real \<circ> g \<circ> Im \<circ> Ln)"
    unfolding o_def by (rule continuous_Re)
  then show ?thesis
    by (simp add: o_def)
qed

inductive_set cx_poly :: "(complex \<Rightarrow> real) set" where
    Re: "Re \<in> cx_poly"
  | Im: "Im \<in> cx_poly"
  | const: "(\<lambda>x. c) \<in> cx_poly"
  | add:   "\<lbrakk>f \<in> cx_poly; g \<in> cx_poly\<rbrakk> \<Longrightarrow> (\<lambda>x. f x + g x) \<in> cx_poly"
  | mult:  "\<lbrakk>f \<in> cx_poly; g \<in> cx_poly\<rbrakk> \<Longrightarrow> (\<lambda>x. f x * g x) \<in> cx_poly"

declare cx_poly.intros [intro]


lemma Weierstrass_trig_polynomial:
  assumes contf: "continuous_on {-pi..pi} f" and fpi: "f(-pi) = f pi" and "0 < e"
  obtains n::nat and a b where
    "\<And>x::real. x \<in> {-pi..pi} \<Longrightarrow> \<bar>f x - (\<Sum>k\<le>n. a k * sin (k * x) + b k * cos (k * x))\<bar> < e"
proof -
  interpret CR: function_ring_on "cx_poly" "sphere 0 1"
  proof
    show "continuous_on (sphere 0 1) f" if "f \<in> cx_poly" for f
      using that by induction (assumption | intro continuous_intros)+
    fix x y::complex
    assume "x \<in> sphere 0 1" and "y \<in> sphere 0 1" and "x \<noteq> y"
    then consider "Re x \<noteq> Re y" | "Im x \<noteq> Im y"
      using complex_eqI by blast
    then show "\<exists>f\<in>cx_poly. f x \<noteq> f y"
      by (metis cx_poly.Im cx_poly.Re)
  qed (auto simp: cx_poly.intros)
  have "continuous (at z within (sphere 0 1)) (f \<circ> Im \<circ> Ln)" if "norm z = 1" for z
  proof -
    obtain g where contg: "continuous_on UNIV g" and gf: "\<And>x. x \<in> {-pi..pi} \<Longrightarrow> g x = f x"
      and periodic: "\<And>x. g(x + 2*pi) = g x"
      using Tietze_periodic_interval [OF contf fpi] by auto
    let ?f = "(g \<circ> Im \<circ> Ln)"
    show ?thesis
    proof (rule continuous_transform_within)
      show "continuous (at z within (sphere 0 1)) ?f"
        using Weierstrass_trig_1 [OF contg periodic that] by (simp add: sphere_def)
      show "?f x' = (f \<circ> Im \<circ> Ln) x'"
        if "x' \<in> sphere 0 1" "dist x' z < 1" for x'
      proof -
        have "x' \<noteq> 0"
          using that by auto
        then have "Im (Ln x') \<in> {-pi..pi}"
          using Im_Ln_le_pi [of x'] mpi_less_Im_Ln [of x'] by simp
        then show ?thesis
          using gf by simp
      qed
    qed (use that in auto)
  qed
  then have "continuous_on (sphere 0 1) (f \<circ> Im \<circ> Ln)"
    using continuous_on_eq_continuous_within mem_sphere_0 by blast
  then obtain g where "g \<in> cx_poly" and g: "\<And>x. x \<in> sphere 0 1 \<Longrightarrow> \<bar>(f \<circ> Im \<circ> Ln) x - g x\<bar> < e"
    using CR.Stone_Weierstrass_basic [of "f \<circ> Im \<circ> Ln"] \<open>e > 0\<close> by meson
  define trigpoly where
    "trigpoly \<equiv> \<lambda>f. \<exists>n a b. f = (\<lambda>x. (\<Sum>k\<le>n. a k * sin(real k * x) +  b k * cos(real k * x)))"
  have tp_const: "trigpoly(\<lambda>x. c)" for c
    unfolding trigpoly_def
    by (rule_tac x=0 in exI) auto
  have tp_add: "trigpoly(\<lambda>x. f x + g x)" if "trigpoly f" "trigpoly g" for f g
  proof -
    obtain n1 a1 b1 where feq: "f = (\<lambda>x. \<Sum>k\<le>n1. a1 k * sin (real k * x) + b1 k * cos (real k * x))"
      using \<open>trigpoly f\<close> trigpoly_def by blast
    obtain n2 a2 b2 where geq: "g = (\<lambda>x. \<Sum>k\<le>n2. a2 k * sin (real k * x) + b2 k * cos (real k * x))"
      using \<open>trigpoly g\<close> trigpoly_def by blast
    let ?a = "\<lambda>n. (if n \<le> n1 then a1 n else 0) + (if n \<le> n2 then a2 n else 0)"
    let ?b = "\<lambda>n. (if n \<le> n1 then b1 n else 0) + (if n \<le> n2 then b2 n else 0)"
    have eq: "{k. k \<le> max a b \<and> k \<le> a} = {..a}" "{k. k \<le> max a b \<and> k \<le> b} = {..b}" for a b::nat
      by auto
    have "(\<lambda>x. f x + g x) = (\<lambda>x. \<Sum>k \<le> max n1 n2. ?a k * sin (real k * x) + ?b k * cos (real k * x))"
      by (simp add: feq geq algebra_simps eq sum.distrib if_distrib [of "\<lambda>u. _ * u"] cong: if_cong flip: sum.inter_filter)
    then show ?thesis
      unfolding trigpoly_def by meson
  qed
  have tp_sum: "trigpoly(\<lambda>x. \<Sum>i\<in>S. f i x)" if "finite S" "\<And>i. i \<in> S \<Longrightarrow> trigpoly(f i)" for f and S :: "nat set"
    using that
    by induction (auto simp: tp_const tp_add)
  have tp_cmul: "trigpoly(\<lambda>x. c * f x)" if "trigpoly f" for f c
  proof -
    obtain n a b where feq: "f = (\<lambda>x. \<Sum>k\<le>n. a k * sin (real k * x) + b k * cos (real k * x))"
      using \<open>trigpoly f\<close> trigpoly_def by blast
    have "(\<lambda>x. c * f x) = (\<lambda>x. \<Sum>k \<le> n. (c * a k) * sin (real k * x) + (c * b k) * cos (real k * x))"
      by (simp add: feq algebra_simps sum_distrib_left)
    then show ?thesis
      unfolding trigpoly_def by meson
  qed
  have tp_cdiv: "trigpoly(\<lambda>x. f x / c)" if "trigpoly f" for f c
    using tp_cmul [OF \<open>trigpoly f\<close>, of "inverse c"]
    by (simp add: divide_inverse_commute)
  have tp_diff: "trigpoly(\<lambda>x. f x - g x)" if "trigpoly f" "trigpoly g" for f g
    using tp_add [OF \<open>trigpoly f\<close> tp_cmul [OF \<open>trigpoly g\<close>, of "-1"]] by auto
  have tp_sin: "trigpoly(\<lambda>x. sin (n * x))" if "n \<in> \<nat>" for n
    unfolding trigpoly_def
  proof
    obtain k where "n = real k"
      using Nats_cases \<open>n \<in> \<nat>\<close> by blast
    then show "\<exists>a b. (\<lambda>x. sin (n * x)) = (\<lambda>x. \<Sum>i \<le> nat\<lfloor>n\<rfloor>. a i * sin (real i * x) + b i * cos (real i * x))"
      apply (rule_tac x="\<lambda>i. if i = k then 1 else 0" in exI)
      apply (rule_tac x="\<lambda>i. 0" in exI)
      apply (simp add: if_distrib [of "\<lambda>u. u * _"] cong: if_cong)
      done
  qed
  have tp_cos: "trigpoly(\<lambda>x. cos (n * x))" if "n \<in> \<nat>" for n
    unfolding trigpoly_def
  proof
    obtain k where "n = real k"
      using Nats_cases \<open>n \<in> \<nat>\<close> by blast
    then show "\<exists>a b. (\<lambda>x. cos (n * x)) = (\<lambda>x. \<Sum>i \<le> nat\<lfloor>n\<rfloor>. a i * sin (real i * x) + b i * cos (real i * x))"
      apply (rule_tac x="\<lambda>i. 0" in exI)
      apply (rule_tac x="\<lambda>i. if i = k then 1 else 0" in exI)
      apply (simp add: if_distrib [of "\<lambda>u. u * _"] cong: if_cong)
      done
  qed
  have tp_sincos: "trigpoly(\<lambda>x. sin(i * x) * sin(j * x)) \<and> trigpoly(\<lambda>x. sin(i * x) * cos(j * x)) \<and>
                   trigpoly(\<lambda>x. cos(i * x) * sin(j * x)) \<and> trigpoly(\<lambda>x. cos(i * x) * cos(j * x))" (is "?P i j")
    for i j::nat
  proof (rule linorder_wlog [of _ j i])
    show "?P j i" if "i \<le> j" for j i
      using that
      by (simp add: sin_times_sin cos_times_cos sin_times_cos cos_times_sin diff_divide_distrib 
                    tp_add tp_diff tp_cdiv tp_cos tp_sin flip: left_diff_distrib distrib_right)
  qed (simp add: mult_ac)
  have tp_mult: "trigpoly(\<lambda>x. f x * g x)" if "trigpoly f" "trigpoly g" for f g
  proof -
    obtain n1 a1 b1 where feq: "f = (\<lambda>x. \<Sum>k\<le>n1. a1 k * sin (real k * x) + b1 k * cos (real k * x))"
      using \<open>trigpoly f\<close> trigpoly_def by blast
    obtain n2 a2 b2 where geq: "g = (\<lambda>x. \<Sum>k\<le>n2. a2 k * sin (real k * x) + b2 k * cos (real k * x))"
      using \<open>trigpoly g\<close> trigpoly_def by blast
    then show ?thesis
      unfolding feq geq
      by (simp add: algebra_simps sum_product tp_sum tp_add tp_cmul tp_sincos del: mult.commute)
  qed
  have *: "trigpoly(\<lambda>x.  f(exp(\<i> * of_real x)))" if "f \<in> cx_poly" for f
    using that
  proof induction
    case Re
    then show ?case
      using tp_cos [of 1] by (auto simp: Re_exp)
  next
    case Im
    then show ?case
      using tp_sin [of 1] by (auto simp: Im_exp)
  qed (auto simp: tp_const tp_add tp_mult)
  obtain n a b where eq: "(g (iexp x)) = (\<Sum>k\<le>n. a k * sin (real k * x) + b k * cos (real k * x))" for x
    using * [OF \<open>g \<in> cx_poly\<close>] trigpoly_def by meson
  show thesis
    proof
    show "\<bar>f \<theta> - (\<Sum>k\<le>n. a k * sin (real k * \<theta>) + b k * cos (real k * \<theta>))\<bar> < e"
      if "\<theta> \<in> {-pi..pi}" for \<theta>
    proof -
      have "f \<theta> - g (iexp \<theta>) = (f \<circ> Im \<circ> Ln) (iexp \<theta>) - g (iexp \<theta>)"
      proof (cases "\<theta> = -pi")
      case True
        then show ?thesis
          by (simp add: exp_minus fpi)
    next
      case False
      then show ?thesis
        using that by auto
    qed
    then show ?thesis
      using g [of "exp(\<i> * of_real \<theta>)"] by (simp flip: eq)
    qed
  qed
qed


subsection\<open>A bit of extra hacking round so that the ends of a function are OK\<close>

lemma integral_tweak_ends:
  fixes a b :: real
  assumes "a < b" "e > 0"
  obtains f where "continuous_on {a..b} f" "f a = d" "f b = 0" "l2norm {a..b} f < e"
proof -
  have cont: "continuous_on {a..b}
          (\<lambda>x. if x \<le> a+1 / real(Suc n)
               then ((Suc n) * d) * ((a+1 / (Suc n)) - x) else 0)" for n
  proof (cases "a+1/(Suc n) \<le> b")
    case True
    have *: "1 / (1 + real n) > 0"
      by auto
    have abeq: "{a..b} = {a..a+1/(Suc n)} \<union> {a+1/(Suc n)..b}"
      using \<open>a < b\<close> True
      apply auto
      using "*" by linarith
    show ?thesis
      unfolding abeq
    proof (rule continuous_on_cases)
      show "continuous_on {a..a+1 / real (Suc n)} (\<lambda>x. real (Suc n) * d * (a+1 / real (Suc n) - x))"
        by (intro continuous_intros)
    qed auto
  next
    case False
    show ?thesis
    proof (rule continuous_on_eq [where f = "\<lambda>x. ((Suc n) * d) * ((a+1/(Suc n)) - x)"])
      show " continuous_on {a..b} (\<lambda>x. (Suc n) * d * (a+1 / real (Suc n) - x))"
        by (intro continuous_intros)
    qed (use False in auto)
  qed
  let ?f = "\<lambda>k x. (if x \<le> a+1 / (Suc k) then (Suc k) * d * (a+1 / (Suc k) - x) else 0)\<^sup>2"
  let ?g = "\<lambda>x. if x = a then d\<^sup>2 else 0"
  have bmg: "?g \<in> borel_measurable (lebesgue_on {a..b})"
    apply (rule measurable_restrict_space1)
    using borel_measurable_if_I [of _ "{a}", OF borel_measurable_const] by auto
  have bmf: "?f k \<in> borel_measurable (lebesgue_on {a..b})" for k
  proof -
    have bm: "(\<lambda>x. (Suc k) * d * (a+1 / real (Suc k) - x))
              \<in> borel_measurable (lebesgue_on {..a+1 / (Suc k)})"
      by (intro measurable) (auto simp: measurable_completion measurable_restrict_space1)
    show ?thesis
      apply (intro borel_measurable_power measurable_restrict_space1)
      using borel_measurable_if_I [of _ "{.. a+1 / (Suc k)}", OF bm]  apply auto
      done
  qed
  have int_d2: "integrable (lebesgue_on {a..b}) (\<lambda>x. d\<^sup>2)"
    by (intro continuous_imp_integrable_real continuous_intros)
  have "(\<lambda>k. ?f k x) \<longlonglongrightarrow> ?g x"
    if x: "x \<in> {a..b}" for x
  proof (cases "x = a")
    case False
    then have "x > a"
      using x by auto
    with x obtain N where "N > 0" and N: "1 / real N < x-a"
      using real_arch_invD [of "x-a"]
      by (force simp: inverse_eq_divide)
    then have "x > a+1 / (1 + real k)"
      if "k \<ge> N" for k
    proof -
      have "a+1 / (1 + real k) < a+1 / real N"
        using that \<open>0 < N\<close> by (simp add: field_simps)
      also have "\<dots> < x"
        using N by linarith
      finally show ?thesis .
    qed
    then show ?thesis
      apply (intro tendsto_eventually eventually_sequentiallyI [where c=N])
      by (fastforce simp: False)
  qed auto
  then have tends: "AE x in (lebesgue_on {a..b}). (\<lambda>k. ?f k x) \<longlonglongrightarrow> ?g x"
    by force
  have le_d2: "\<And>k. AE x in (lebesgue_on {a..b}). norm (?f k x) \<le> d\<^sup>2"
  proof
    show "norm ((if x \<le> a+1 / real (Suc k) then real (Suc k) * d * (a+1 / real (Suc k) - x) else 0)\<^sup>2) \<le> d\<^sup>2"
      if "x \<in> space (lebesgue_on {a..b})" for k x
      using that
      apply (simp add: abs_mult divide_simps flip: abs_le_square_iff)
      apply (auto simp: abs_if zero_less_mult_iff mult_left_le)
      done
  qed
  have integ: "integrable (lebesgue_on {a..b}) ?g"
    using integrable_dominated_convergence [OF bmg bmf int_d2 tends le_d2] by auto
  have int: "(\<lambda>k. integral\<^sup>L (lebesgue_on {a..b}) (?f k)) \<longlonglongrightarrow> integral\<^sup>L (lebesgue_on {a..b}) ?g"
    using integral_dominated_convergence [OF bmg bmf int_d2 tends le_d2] by auto
  then obtain N where N: "\<And>k. k \<ge> N \<Longrightarrow> \<bar>integral\<^sup>L (lebesgue_on {a..b}) (?f k) - integral\<^sup>L (lebesgue_on {a..b}) ?g\<bar> < e\<^sup>2"
    apply (simp add: lim_sequentially dist_real_def)
    apply (drule_tac x="e^2" in spec)
    using \<open>e > 0\<close>
    by auto
  obtain M where "M > 0" and M: "1 / real M < b-a"
    using real_arch_invD [of "b-a"]
    by (metis \<open>a < b\<close> diff_gt_0_iff_gt inverse_eq_divide neq0_conv)
  have *: "\<bar>integral\<^sup>L (lebesgue_on {a..b}) (?f (max M N)) - integral\<^sup>L (lebesgue_on {a..b}) ?g\<bar> < e\<^sup>2"
    using N by force
  let ?\<phi> = "\<lambda>x. if x \<le> a+1/(Suc (max M N)) then ((Suc (max M N)) * d) * ((a+1/(Suc (max M N))) - x) else 0"
  show ?thesis
  proof
    show "continuous_on {a..b} ?\<phi>"
      by (rule cont)
    have "1 / (1 + real (max M N)) \<le> 1 / (real M)"
      by (simp add: \<open>0 < M\<close> frac_le)
    then have "\<not> (b \<le> a+1 / (1 + real (max M N)))"
      using M \<open>a < b\<close> \<open>M > 0\<close> max.cobounded1 [of M N]
      by linarith
    then show "?\<phi> b = 0"
      by simp
    have null_a: "{a} \<in> null_sets (lebesgue_on {a..b})"
      using \<open>a < b\<close> by (simp add: null_sets_restrict_space)
    have "LINT x|lebesgue_on {a..b}. ?g x = 0"
      by (force intro: integral_eq_zero_AE AE_I' [OF null_a])
    then have "l2norm {a..b} ?\<phi> < sqrt (e^2)"
      unfolding l2norm_def l2product_def power2_eq_square [symmetric]
      apply (intro real_sqrt_less_mono)
      using "*" by linarith
    then show "l2norm {a..b} ?\<phi> < e"
      using \<open>e > 0\<close> by auto
  qed auto
qed


lemma square_integrable_approximate_continuous_ends:
  assumes f: "f square_integrable {a..b}" and "a < b" "0 < e"
  obtains g where "continuous_on {a..b} g" "g b = g a" "g square_integrable {a..b}" "l2norm {a..b} (\<lambda>x. f x - g x) < e"
proof -
  obtain g where contg: "continuous_on UNIV g" and "g square_integrable {a..b}"
    and lg: "l2norm {a..b} (\<lambda>x. f x - g x) < e/2"
    using f \<open>e > 0\<close> square_integrable_approximate_continuous
    by (metis (full_types) box_real(2) half_gt_zero_iff lmeasurable_cbox)
  obtain h where conth: "continuous_on {a..b} h" and "h a = g b - g a" "h b = 0"
    and lh: "l2norm {a..b} h < e/2"
    using integral_tweak_ends \<open>e > 0\<close>
    by (metis \<open>a < b\<close> zero_less_divide_iff zero_less_numeral)
  have "h square_integrable {a..b}"
    using \<open>continuous_on {a..b} h\<close> continuous_imp_square_integrable by blast
  show thesis
  proof
    show "continuous_on {a..b} (\<lambda>x. g x + h x)"
      by (blast intro: continuous_on_subset [OF contg] conth continuous_intros)
    then show "(\<lambda>x. g x + h x) square_integrable {a..b}"
      using continuous_imp_square_integrable by blast
    show "g b + h b = g a + h a"
      by (simp add: \<open>h a = g b - g a\<close> \<open>h b = 0\<close>)
    have "l2norm {a..b} (\<lambda>x. (f x - g x) + - h x) < e"
    proof (rule le_less_trans [OF l2norm_triangle [of "\<lambda>x. f x - g x" "{a..b}" "\<lambda>x. - (h x)"]])
      show "(\<lambda>x. f x - g x) square_integrable {a..b}"
        using \<open>g square_integrable {a..b}\<close> f square_integrable_diff by blast
      show "(\<lambda>x. - h x) square_integrable {a..b}"
        by (simp add: \<open>h square_integrable {a..b}\<close>)
      show "l2norm {a..b} (\<lambda>x. f x - g x) + l2norm {a..b} (\<lambda>x. - h x) < e"
        using \<open>h square_integrable {a..b}\<close> l2norm_neg lg lh by auto
    qed
    then show "l2norm {a..b} (\<lambda>x. f x - (g x + h x)) < e"
      by (simp add: field_simps)
  qed
qed


subsection\<open>Hence the main approximation result\<close>

lemma Weierstrass_l2_trig_polynomial:
  assumes f: "f square_integrable {-pi..pi}" and "0 < e"
  obtains n a b where
   "l2norm {-pi..pi} (\<lambda>x. f x - (\<Sum>k\<le>n. a k * sin(real k * x) + b k * cos(real k * x))) < e"
proof -
  let ?\<phi> = "\<lambda>n a b x. \<Sum>k\<le>n. a k * sin(real k * x) + b k * cos(real k * x)"
  obtain g where contg: "continuous_on {-pi..pi} g" and geq: "g(-pi) = g pi"
           and g: "g square_integrable {-pi..pi}" and norm_fg: "l2norm {-pi..pi} (\<lambda>x. f x - g x) < e/2"
    using \<open>e > 0\<close> by (auto intro: square_integrable_approximate_continuous_ends [OF f, of "e/2"])
  then obtain n a b where g_phi_less: "\<And>x. x \<in> {-pi..pi} \<Longrightarrow> \<bar>g x - (?\<phi> n a b x)\<bar> < e/6"
    using \<open>e > 0\<close> Weierstrass_trig_polynomial [OF contg geq, of "e/6"]
    by (meson zero_less_divide_iff zero_less_numeral)
  show thesis
  proof
    have si: "(?\<phi> n u v) square_integrable {-pi..pi}" for n::nat and u v
    proof (intro square_integrable_sum continuous_imp_square_integrable)
      show "continuous_on {-pi..pi} (\<lambda>x. u k * sin (real k * x) + v k * cos (real k * x))"
        if "k \<in> {..n}" for k
        using that by (intro continuous_intros)
    qed auto
    have "l2norm {-pi..pi} (\<lambda>x. f x - (?\<phi> n a b x)) =  l2norm {-pi..pi} (\<lambda>x. (f x - g x) + (g x - (?\<phi> n a b x)))"
      by simp
    also have "\<dots> \<le> l2norm {-pi..pi} (\<lambda>x. f x - g x) + l2norm {-pi..pi} (\<lambda>x. g x - (?\<phi> n a b x))"
    proof (rule l2norm_triangle)
      show "(\<lambda>x. f x - g x) square_integrable {-pi..pi}"
        using f g square_integrable_diff by blast
      show "(\<lambda>x. g x - (?\<phi> n a b x)) square_integrable {-pi..pi}"
        using g si square_integrable_diff by blast
    qed
    also have "\<dots> < e"
    proof -
      have g_phi: "(\<lambda>x. g x - (?\<phi> n a b x)) square_integrable {-pi..pi}"
        using g si square_integrable_diff by blast
      have "l2norm {-pi..pi} (\<lambda>x. g x - (?\<phi> n a b x)) \<le> e/2"
        unfolding l2norm_def l2product_def power2_eq_square [symmetric]
      proof (rule real_le_lsqrt)
        show "0 \<le> LINT x|lebesgue_on {-pi..pi}. (g x - (?\<phi> n a b x))\<^sup>2"
          by (rule integral_nonneg_AE) auto
        have "LINT x|lebesgue_on {-pi..pi}. (g x - (?\<phi> n a b x))\<^sup>2
            \<le> LINT x|lebesgue_on {-pi..pi}. (e / 6) ^ 2"
        proof (rule integral_mono)
          show "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. (g x - (?\<phi> n a b x))\<^sup>2)"
            using g_phi square_integrable_def by auto
          show "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. (e / 6)\<^sup>2)"
            by (intro continuous_intros continuous_imp_integrable_real)
          show "(g x - (?\<phi> n a b x))\<^sup>2 \<le> (e / 6)\<^sup>2" if "x \<in> space (lebesgue_on {-pi..pi})" for x
            using \<open>e > 0\<close> g_phi_less that
            apply (simp add: abs_le_square_iff [symmetric])
            using less_eq_real_def by blast
        qed
        also have "\<dots> \<le> (e / 2)\<^sup>2"
          using \<open>e > 0\<close> pi_less_4 by (auto simp: power2_eq_square measure_restrict_space)
        finally show "LINT x|lebesgue_on {-pi..pi}. (g x - (?\<phi> n a b x))\<^sup>2 \<le> (e / 2)\<^sup>2" .
      qed (use \<open>e > 0\<close> in auto)
      with norm_fg show ?thesis
        by auto
    qed
    finally show "l2norm {-pi..pi} (\<lambda>x. f x - (?\<phi> n a b x)) < e" .
  qed
qed


proposition Weierstrass_l2_trigonometric_set:
  assumes f: "f square_integrable {-pi..pi}" and "0 < e"
  obtains n a where "l2norm {-pi..pi} (\<lambda>x. f x - (\<Sum>k\<le>n. a k * trigonometric_set k x)) < e"
proof -
  obtain n a b where lee:
    "l2norm {-pi..pi} (\<lambda>x. f x - (\<Sum>k\<le>n. a k * sin(real k * x) + b k * cos(real k * x))) < e"
    using Weierstrass_l2_trig_polynomial [OF assms] .
  let ?a = "\<lambda>k. if k = 0 then sqrt(2 * pi) * b 0
                else if even k then sqrt pi * b(k div 2)
                else if k \<le> 2 * n then sqrt pi * a((Suc k) div 2)
                else 0"
  show thesis
  proof
    have [simp]: "Suc (i * 2) \<le> n * 2 \<longleftrightarrow> i<n" "{..n} \<inter> {..<n} = {..<n}" for i n
      by auto
    have "(\<Sum>k\<le>n. b k * cos (real k * x)) = (\<Sum>i\<le>n. if i = 0 then b 0 else b i * cos (real i * x))" for x
      by (rule sum.cong) auto
    moreover have "(\<Sum>k\<le>n. a k * sin (real k * x)) = (\<Sum>i\<le>n. (if Suc (2 * i) \<le> 2 * n then sqrt pi * a (Suc i) * sin ((1 + real i) * x) else 0) / sqrt pi)"
                   (is "?lhs = ?rhs") for x
    proof (cases "n=0")
      case False
      then obtain n' where n': "n = Suc n'"
        using not0_implies_Suc by blast
      have "?lhs = (\<Sum>k = Suc 0..n. a k * sin (real k * x))"
        by (simp add: atMost_atLeast0 sum_shift_lb_Suc0_0)
      also have "\<dots> = (\<Sum>i<n. a (Suc i) * sin (x + x * real i))"
      proof (subst sum.reindex_bij_betw [symmetric])
        show "bij_betw Suc {..n'} {Suc 0..n}"
          by (simp add: atMost_atLeast0 n')
        show "(\<Sum>j\<le>n'. a (Suc j) * sin (real (Suc j) * x)) = (\<Sum>i<n. a (Suc i) * sin (x + x * real i))"
        unfolding n' lessThan_Suc_atMost by (simp add: algebra_simps)
      qed
      also have "\<dots> = ?rhs"
        by (simp add: field_simps if_distrib [of "\<lambda>x. x/_"] sum.inter_restrict [where B = "{..<n}", simplified, symmetric] cong: if_cong)
      finally
      show ?thesis .
    qed auto
    ultimately
    have "(\<Sum>k\<le>n. a k * sin(real k * x) + b k * cos(real k * x)) = (\<Sum>k \<le> Suc(2*n). ?a k * trigonometric_set k x)" for x
      unfolding sum.in_pairs_0 trigonometric_set_def
      by (simp add: sum.distrib if_distrib [of "\<lambda>x. x*_"] cong: if_cong)
    with lee show "l2norm {-pi..pi} (\<lambda>x. f x - (\<Sum>k \<le> Suc(2*n). ?a k * trigonometric_set k x)) < e"
      by auto
  qed
qed

subsection\<open>Convergence wrt the L2 norm of trigonometric Fourier series\<close>

definition Fourier_coefficient
  where "Fourier_coefficient \<equiv> orthonormal_coeff {-pi..pi} trigonometric_set"

lemma Fourier_series_l2:
  assumes "f square_integrable {-pi..pi}"
  shows "(\<lambda>n. l2norm {-pi..pi} (\<lambda>x. f x - (\<Sum>i\<le>n. Fourier_coefficient f i * trigonometric_set i x)))
         \<longlonglongrightarrow> 0"
proof (clarsimp simp add: lim_sequentially dist_real_def Fourier_coefficient_def)
  let ?h = "\<lambda>n x. (\<Sum>i\<le>n. orthonormal_coeff {-pi..pi} trigonometric_set f i * trigonometric_set i x)"
  show "\<exists>N. \<forall>n\<ge>N. \<bar>l2norm {-pi..pi} (\<lambda>x. f x - ?h n x)\<bar> < e"
    if "0 < e" for e
  proof -
    obtain N a where lte: "l2norm {-pi..pi} (\<lambda>x. f x - (\<Sum>k\<le>N. a k * trigonometric_set k x)) < e"
      using Weierstrass_l2_trigonometric_set by (meson \<open>0 < e\<close> assms)
    show ?thesis
    proof (intro exI allI impI)
      show "\<bar>l2norm {-pi..pi} (\<lambda>x. f x - ?h m x)\<bar> < e"
        if "N \<le> m" for m
      proof -
        have "\<bar>l2norm {-pi..pi} (\<lambda>x. f x - ?h m x)\<bar> = l2norm {-pi..pi} (\<lambda>x. f x - ?h m x)"
        proof (rule abs_of_nonneg)
          show "0 \<le> l2norm {-pi..pi} (\<lambda>x. f x -  ?h m x)"
            apply (intro l2norm_pos_le square_integrable_diff square_integrable_sum square_integrable_lmult
                square_integrable_trigonometric_set assms, auto)
            done
        qed
        also have "\<dots> \<le> l2norm {-pi..pi} (\<lambda>x. f x - (\<Sum>k\<le>N. a k * trigonometric_set k x))"
        proof -
          have "(\<Sum>i\<le>m. (if i \<le> N then a i else 0) * trigonometric_set i x) = (\<Sum>i\<le>N. a i * trigonometric_set i x)" for x
            using sum.inter_restrict [where A = "{..m}" and B = "{..N}", symmetric] that
            by (force simp: if_distrib [of "\<lambda>x. x * _"] min_absorb2 cong: if_cong)
          moreover
          have "l2norm {-pi..pi} (\<lambda>x. f x - ?h m x)
                \<le> l2norm {-pi..pi} (\<lambda>x. f x - (\<Sum>i\<le>m. (if i \<le> N then a i else 0) * trigonometric_set i x))"
            using orthonormal_optimal_partial_sum
              [OF orthonormal_system_trigonometric_set square_integrable_trigonometric_set assms]
            by simp
          ultimately show ?thesis
            by simp
        qed
        also have "\<dots> < e"
          by (rule lte)
        finally show ?thesis .
      qed
    qed
  qed
qed



subsection\<open>Fourier coefficients go to 0 (weak form of Riemann-Lebesgue)\<close>

lemma trigonometric_set_mul_absolutely_integrable:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>x. trigonometric_set n x * f x) absolutely_integrable_on {-pi..pi}"
proof (rule absolutely_integrable_bounded_measurable_product_real)
  show "trigonometric_set n \<in> borel_measurable (lebesgue_on {-pi..pi})"
    using square_integrable_def square_integrable_trigonometric_set by blast
  show "bounded (trigonometric_set n ` {-pi..pi})"
    unfolding bounded_iff using pi_gt3 sqrt_pi_ge1
    by (rule_tac x=1 in exI)
      (auto simp: trigonometric_set_def dist_real_def
        intro: order_trans [OF abs_sin_le_one] order_trans [OF abs_cos_le_one])
qed (auto simp: assms)


lemma trigonometric_set_mul_integrable:
   "f absolutely_integrable_on {-pi..pi} \<Longrightarrow> integrable (lebesgue_on {-pi..pi}) (\<lambda>x. trigonometric_set n x * f x)"
  using trigonometric_set_mul_absolutely_integrable
  by (simp add: integrable_restrict_space set_integrable_def)

lemma trigonometric_set_integrable [simp]: "integrable (lebesgue_on {-pi..pi}) (trigonometric_set n)"
  using trigonometric_set_mul_integrable [where f = id]
  by simp (metis absolutely_integrable_imp_integrable fmeasurableD interval_cbox lmeasurable_cbox square_integrable_imp_absolutely_integrable square_integrable_trigonometric_set)

lemma absolutely_integrable_sin_product:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>x. sin(k * x) * f x) absolutely_integrable_on {-pi..pi}"
proof (rule absolutely_integrable_bounded_measurable_product_real)
  show "(\<lambda>x. sin (k * x)) \<in> borel_measurable (lebesgue_on {-pi..pi})"
    by (metis borel_measurable_integrable integrable_sin_cx mult_commute_abs)
  show "bounded ((\<lambda>x. sin (k * x)) ` {-pi..pi})"
    by (metis (mono_tags, lifting) abs_sin_le_one bounded_iff imageE real_norm_def)
qed (auto simp: assms)

lemma absolutely_integrable_cos_product:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>x. cos(k * x) * f x) absolutely_integrable_on {-pi..pi}"
proof (rule absolutely_integrable_bounded_measurable_product_real)
  show "(\<lambda>x. cos (k * x)) \<in> borel_measurable (lebesgue_on {-pi..pi})"
    by (metis borel_measurable_integrable integrable_cos_cx mult_commute_abs)
  show "bounded ((\<lambda>x. cos (k * x)) ` {-pi..pi})"
    by (metis (mono_tags, lifting) abs_cos_le_one bounded_iff imageE real_norm_def)
qed (auto simp: assms)

lemma
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows Fourier_products_integrable_cos: "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. cos(k * x) * f x)"
  and   Fourier_products_integrable_sin: "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. sin(k * x) * f x)"
  using absolutely_integrable_cos_product absolutely_integrable_sin_product assms
  by (auto simp: integrable_restrict_space set_integrable_def)


lemma Riemann_lebesgue_square_integrable:
  assumes "orthonormal_system S w" "\<And>i. w i square_integrable S" "f square_integrable S"
  shows "orthonormal_coeff S w f \<longlonglongrightarrow> 0"
  using Fourier_series_square_summable [OF assms, of UNIV] summable_LIMSEQ_zero by force

proposition Riemann_lebesgue:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "Fourier_coefficient f \<longlonglongrightarrow> 0"
  unfolding lim_sequentially
proof (intro allI impI)
  fix e::real
  assume "e > 0"
  then obtain g where "continuous_on UNIV g" and gabs: "g absolutely_integrable_on {-pi..pi}"
                and fg_e2: "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. \<bar>f x - g x\<bar>) < e/2"
    using absolutely_integrable_approximate_continuous [OF assms, of "e/2"]
    by (metis (full_types) box_real(2) half_gt_zero_iff lmeasurable_cbox)
  have "g square_integrable {-pi..pi}"
    using \<open>continuous_on UNIV g\<close> continuous_imp_square_integrable continuous_on_subset by blast
  then have "orthonormal_coeff {-pi..pi} trigonometric_set g \<longlonglongrightarrow> 0"
    using Riemann_lebesgue_square_integrable orthonormal_system_trigonometric_set square_integrable_trigonometric_set by blast
  with \<open>e > 0\<close> obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> \<bar>orthonormal_coeff {-pi..pi} trigonometric_set g n\<bar> < e/2"
    unfolding lim_sequentially by (metis half_gt_zero_iff norm_conv_dist real_norm_def)
  have "\<bar>Fourier_coefficient f n\<bar> < e"
    if "n \<ge> N" for n
  proof -
    have "\<bar>LINT x|lebesgue_on {-pi..pi}. trigonometric_set n x * g x\<bar> < e/2"
      using N [OF \<open>n \<ge> N\<close>] by (auto simp: orthonormal_coeff_def l2product_def)

    have "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. trigonometric_set n x * g x)"
      using gabs trigonometric_set_mul_integrable by blast
    moreover have "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. trigonometric_set n x * f x)"
      using assms trigonometric_set_mul_integrable by blast
    ultimately have "\<bar>(LINT x|lebesgue_on {-pi..pi}. trigonometric_set n x * g x) -
                        (LINT x|lebesgue_on {-pi..pi}. trigonometric_set n x * f x)\<bar>
                     = \<bar>(LINT x|lebesgue_on {-pi..pi}. trigonometric_set n x * (g x - f x))\<bar>"
      by (simp add:  algebra_simps flip: Bochner_Integration.integral_diff)
    also have "\<dots> \<le> LINT x|lebesgue_on {-pi..pi}. \<bar>f x - g x\<bar>"
    proof (rule integral_abs_bound_integral)
      show "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. trigonometric_set n x * (g x - f x))"
        by (simp add: gabs assms trigonometric_set_mul_integrable)
      have "(\<lambda>x. f x - g x) absolutely_integrable_on {-pi..pi}"
        using gabs assms by blast
      then show "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. \<bar>f x - g x\<bar>)"
        by (simp add: absolutely_integrable_imp_integrable)
      fix x
      assume "x \<in> space (lebesgue_on {-pi..pi})"
      then have "-pi \<le> x" "x \<le> pi"
        by auto
      have "\<bar>trigonometric_set n x\<bar> \<le> 1"
        using pi_ge_two
        apply (simp add: trigonometric_set_def)
        using sqrt_pi_ge1 abs_sin_le_one order_trans abs_cos_le_one by metis
      then show "\<bar>trigonometric_set n x * (g x - f x)\<bar> \<le> \<bar>f x - g x\<bar>"
        using abs_ge_zero mult_right_mono by (fastforce simp add: abs_mult abs_minus_commute)
    qed
    finally have "\<bar>(LINT x|lebesgue_on {-pi..pi}. trigonometric_set n x * g x) -
           (LINT x|lebesgue_on {-pi..pi}. trigonometric_set n x * f x)\<bar>
          \<le> LINT x|lebesgue_on {-pi..pi}. \<bar>f x - g x\<bar>" .
    then show ?thesis
      using N [OF \<open>n \<ge> N\<close>] fg_e2
      unfolding Fourier_coefficient_def orthonormal_coeff_def l2product_def
      by linarith
  qed
  then show "\<exists>no. \<forall>n\<ge>no. dist (Fourier_coefficient f n) 0 < e"
    by auto
qed


lemma Riemann_lebesgue_sin:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>n. integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin(real n * x) * f x)) \<longlonglongrightarrow> 0"
  unfolding lim_sequentially
proof (intro allI impI)
  fix e::real
  assume "e > 0"
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> \<bar>Fourier_coefficient f n\<bar> < e/4"
    using Riemann_lebesgue [OF assms]
    unfolding lim_sequentially
    by (metis norm_conv_dist real_norm_def zero_less_divide_iff zero_less_numeral)
  have "\<bar>LINT x|lebesgue_on {-pi..pi}. sin (real n * x) * f x\<bar> < e" if "n > N" for n
    using that
  proof (induction n)
    case (Suc n)
    have "\<bar>Fourier_coefficient f(Suc (2 * n))\<bar> < e/4"
      using N Suc.prems by auto
    then have "\<bar>LINT x|lebesgue_on {-pi..pi}. sin ((1 + real n) * x) * f x\<bar> < sqrt pi * e / 4"
      by (simp add: Fourier_coefficient_def orthonormal_coeff_def
          trigonometric_set_def l2product_def field_simps)
    also have "\<dots> \<le> e"
      using \<open>0 < e\<close> pi_less_4 real_sqrt_less_mono by (fastforce simp add: field_simps)
    finally show ?case
      by simp
  qed auto
  then show "\<exists>no. \<forall>n\<ge>no. dist (LINT x|lebesgue_on {-pi..pi}. sin (real n * x) * f x) 0 < e"
    by (metis (full_types) le_neq_implies_less less_add_same_cancel2 less_trans norm_conv_dist real_norm_def zero_less_one)
qed

lemma Riemann_lebesgue_cos:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>n. integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(real n * x) * f x)) \<longlonglongrightarrow> 0"
  unfolding lim_sequentially
proof (intro allI impI)
  fix e::real
  assume "e > 0"
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> \<bar>Fourier_coefficient f n\<bar> < e/4"
    using Riemann_lebesgue [OF assms]
    unfolding lim_sequentially
    by (metis norm_conv_dist real_norm_def zero_less_divide_iff zero_less_numeral)
  have "\<bar>LINT x|lebesgue_on {-pi..pi}. cos (real n * x) * f x\<bar> < e" if "n > N" for n
    using that
  proof (induction n)
    case (Suc n)
    have eq: "(x * 2 + x * (real n * 2)) / 2 = x + x * (real n)" for x
      by simp
    have "\<bar>Fourier_coefficient f(2*n + 2)\<bar> < e/4"
      using N Suc.prems by auto
    then have "\<bar>LINT x|lebesgue_on {-pi..pi}. f x * cos (x + x * (real n))\<bar> < sqrt pi * e / 4"
      by (simp add: Fourier_coefficient_def orthonormal_coeff_def
          trigonometric_set_def l2product_def field_simps eq)
    also have "\<dots> \<le> e"
      using \<open>0 < e\<close> pi_less_4 real_sqrt_less_mono by (fastforce simp add: field_simps)
    finally show ?case
      by (simp add: field_simps)
  qed auto
  then show "\<exists>no. \<forall>n\<ge>no. dist (LINT x|lebesgue_on {-pi..pi}. cos (real n * x) * f x) 0 < e"
    by (metis (full_types) le_neq_implies_less less_add_same_cancel2 less_trans norm_conv_dist real_norm_def zero_less_one)
qed


lemma Riemann_lebesgue_sin_half:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>n. LINT x|lebesgue_on {-pi..pi}. sin ((real n + 1/2) * x) * f x) \<longlonglongrightarrow> 0"
proof (simp add: algebra_simps sin_add)
  let ?INT = "integral\<^sup>L (lebesgue_on {-pi..pi})"
  let ?f = "(\<lambda>n. ?INT (\<lambda>x. sin(n * x) * cos(1/2 * x) * f x) +
                 ?INT (\<lambda>x. cos(n * x) * sin(1/2 * x) * f x))"
  show "(\<lambda>n. ?INT (\<lambda>x. f x * (cos (x * real n) * sin (x/2)) + f x * (sin (x * real n) * cos (x/2)))) \<longlonglongrightarrow> 0"
  proof (rule Lim_transform_eventually)
    have sin: "(\<lambda>x. sin (1/2 * x) * f x) absolutely_integrable_on {-pi..pi}"
      by (intro absolutely_integrable_sin_product assms)
    have cos: "(\<lambda>x. cos (1/2 * x) * f x) absolutely_integrable_on {-pi..pi}"
      by (intro absolutely_integrable_cos_product assms)
    show "\<forall>\<^sub>F n in sequentially. ?f n = ?INT (\<lambda>x. f x * (cos (x * real n) * sin (x/2)) + f x * (sin (x * real n) * cos (x/2)))"
      unfolding mult.assoc
      apply (rule eventuallyI)
      apply (subst Bochner_Integration.integral_add [symmetric])
        apply (safe intro!: cos absolutely_integrable_sin_product sin absolutely_integrable_cos_product absolutely_integrable_imp_integrable)
        apply (auto simp: algebra_simps)
      done
    have "?f \<longlonglongrightarrow> 0 + 0"
      unfolding mult.assoc
      by (intro tendsto_add Riemann_lebesgue_sin Riemann_lebesgue_cos sin cos)
    then show "?f \<longlonglongrightarrow> (0::real)" by simp
  qed
qed


lemma Fourier_sum_limit_pair:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>n. \<Sum>k\<le>2 * n. Fourier_coefficient f k * trigonometric_set k t) \<longlonglongrightarrow> l
     \<longleftrightarrow> (\<lambda>n. \<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t) \<longlonglongrightarrow> l"
        (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  show ?rhs
    unfolding lim_sequentially dist_real_def
  proof (intro allI impI)
    fix e::real
    assume "e > 0"
    then obtain N1 where N1: "\<And>n. n \<ge> N1 \<Longrightarrow> \<bar>Fourier_coefficient f n\<bar> < e/2"
      using Riemann_lebesgue [OF assms] unfolding lim_sequentially
      by (metis norm_conv_dist real_norm_def zero_less_divide_iff zero_less_numeral)
    obtain N2 where N2: "\<And>n. n \<ge> N2 \<Longrightarrow> \<bar>(\<Sum>k\<le>2 * n. Fourier_coefficient f k * trigonometric_set k t) - l\<bar> < e/2"
      using L unfolding lim_sequentially dist_real_def
      by (meson \<open>0 < e\<close> half_gt_zero_iff)
    show "\<exists>no. \<forall>n\<ge>no. \<bar>(\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t) - l\<bar> < e"
    proof (intro exI allI impI)
      fix n
      assume n: "N1 + 2*N2 + 1 \<le> n"
      then have "n \<ge> N1" "n \<ge> N2" "n div 2 \<ge> N2"
        by linarith+
      consider "n = 2 * (n div 2)" | "n = Suc(2 * (n div 2))"
        by linarith
      then show "\<bar>(\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t) - l\<bar> < e"
      proof cases
        case 1
        show ?thesis
          apply (subst 1)
          using N2 [OF \<open>n div 2 \<ge> N2\<close>] by linarith
      next
        case 2
        have "\<bar>(\<Sum>k\<le>2 * (n div 2). Fourier_coefficient f k * trigonometric_set k t) - l\<bar> < e/2"
          using N2 [OF \<open>n div 2 \<ge> N2\<close>] by linarith
        moreover have "\<bar>Fourier_coefficient f(Suc (2 * (n div 2))) * trigonometric_set (Suc (2 * (n div 2))) t\<bar> < (e/2) * 1"
        proof -
          have "\<bar>trigonometric_set (Suc (2 * (n div 2))) t\<bar> \<le> 1"
            apply (simp add: trigonometric_set)
            using abs_sin_le_one sqrt_pi_ge1 by (blast intro: order_trans)
          moreover have "\<bar>Fourier_coefficient f(Suc (2 * (n div 2)))\<bar> < e/2"
            using N1 \<open>N1 \<le> n\<close> by auto
          ultimately show ?thesis
            unfolding abs_mult
            by (meson abs_ge_zero le_less_trans mult_left_mono real_mult_less_iff1 zero_less_one)
        qed
        ultimately show ?thesis
          apply (subst 2)
          unfolding sum.atMost_Suc by linarith
      qed
    qed
  qed
next
  assume ?rhs then show ?lhs
    unfolding lim_sequentially
    by (auto simp: elim!: imp_forward ex_forward)
qed


subsection\<open>Express Fourier sum in terms of the special expansion at the origin\<close>

lemma Fourier_sum_0:
  "(\<Sum>k \<le> n. Fourier_coefficient f k * trigonometric_set k 0) =
     (\<Sum>k \<le> n div 2. Fourier_coefficient f(2*k) * trigonometric_set (2*k) 0)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>k = 2 * 0.. Suc (2 * (n div 2)). Fourier_coefficient f k * trigonometric_set k 0)"
  proof (rule sum.mono_neutral_left)
    show "\<forall>i\<in>{2 * 0..Suc (2 * (n div 2))} - {..n}. Fourier_coefficient f i * trigonometric_set i 0 = 0"
    proof clarsimp
      fix i
      assume "i \<le> Suc (2 * (n div 2))" "\<not> i \<le> n"
			then have "i = Suc n" "even n"
			  by presburger+
			moreover
			assume "trigonometric_set i 0 \<noteq> 0"
			ultimately
			show "Fourier_coefficient f i = 0"
				by (simp add: trigonometric_set_def)
		qed
	qed auto
  also have "\<dots> = ?rhs"
 	  unfolding sum.in_pairs by (simp add: trigonometric_set atMost_atLeast0)
  finally show ?thesis .
qed


lemma Fourier_sum_0_explicit:
  "(\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k 0)
    = (Fourier_coefficient f 0 / sqrt 2 + (\<Sum>k = 1..n div 2. Fourier_coefficient f(2*k))) / sqrt pi"
  (is "?lhs = ?rhs")
proof -
  have "(\<Sum>k=0..n. Fourier_coefficient f k * trigonometric_set k 0)
        = Fourier_coefficient f 0 * trigonometric_set 0 0 + (\<Sum>k = 1..n. Fourier_coefficient f k * trigonometric_set k 0)"
    by (simp add: Fourier_sum_0 sum.atLeast_Suc_atMost)
  also have "\<dots> = ?rhs"
  proof -
    have "Fourier_coefficient f 0 * trigonometric_set 0 0 = Fourier_coefficient f 0 / (sqrt 2 * sqrt pi)"
      by (simp add: real_sqrt_mult trigonometric_set(1))
    moreover have "(\<Sum>k = Suc 0..n. Fourier_coefficient f k * trigonometric_set k 0) = (\<Sum>k = Suc 0..n div 2. Fourier_coefficient f(2*k)) / sqrt pi"
    proof (induction n)
      case (Suc n)
      show ?case
        by (simp add: Suc) (auto simp: trigonometric_set_def field_simps)
    qed auto
    ultimately show ?thesis
      by (simp add: add_divide_distrib)
  qed
  finally show ?thesis
    by (simp add: atMost_atLeast0)
qed

lemma Fourier_sum_0_integrals:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k 0) =
          (integral\<^sup>L (lebesgue_on {-pi..pi}) f / 2 +
           (\<Sum>k = Suc 0..n div 2. integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(k * x) * f x))) / pi"
proof -
  have "integral\<^sup>L (lebesgue_on {-pi..pi}) f / (sqrt (2 * pi) * sqrt 2 * sqrt pi) = integral\<^sup>L (lebesgue_on {-pi..pi}) f / (2 * pi)"
    by (simp add: algebra_simps real_sqrt_mult)
  moreover have "(\<Sum>k = Suc 0..n div 2. LINT x|lebesgue_on {-pi..pi}. trigonometric_set (2*k) x * f x) / sqrt pi
               = (\<Sum>k = Suc 0..n div 2. LINT x|lebesgue_on {-pi..pi}. cos (k * x) * f x) / pi"
    by (simp add: trigonometric_set_def sum_divide_distrib)
  ultimately show ?thesis
    unfolding Fourier_sum_0_explicit
    by (simp add: Fourier_coefficient_def orthonormal_coeff_def l2product_def trigonometric_set add_divide_distrib)
qed


lemma Fourier_sum_0_integral:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k 0) =
       integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. (1/2 + (\<Sum>k = Suc 0..n div 2. cos(k * x))) * f x) / pi"
proof -
  note * = Fourier_products_integrable_cos [OF assms]
  have "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. \<Sum>n = Suc 0..n div 2. f x * cos (x * real n))"
    using * by (force simp: mult_ac)
  moreover have "integral\<^sup>L (lebesgue_on {-pi..pi}) f / 2 + (\<Sum>k = Suc 0..n div 2. LINT x|lebesgue_on {-pi..pi}. f x * cos (x * real k))
               = (LINT x|lebesgue_on {-pi..pi}. f x / 2) + (LINT x|lebesgue_on {-pi..pi}. (\<Sum>n = Suc 0..n div 2. f x * cos (x * real n)))"
  proof (subst Bochner_Integration.integral_sum)
    show "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. f x * cos (x * real i))"
      if "i \<in> {Suc 0..n div 2}" for i
      using that * [of i] by (auto simp: Bochner_Integration.integral_sum mult_ac)
  qed auto
  ultimately show ?thesis
    using Fourier_products_integrable_cos [OF assms] absolutely_integrable_imp_integrable [OF assms]
    by (simp add: Fourier_sum_0_integrals sum_distrib_left assms algebra_simps)
qed


subsection\<open>How Fourier coefficients behave under addition etc\<close>

lemma Fourier_coefficient_add:
  assumes "f absolutely_integrable_on {-pi..pi}" "g absolutely_integrable_on {-pi..pi}"
  shows "Fourier_coefficient (\<lambda>x. f x + g x) i =
                Fourier_coefficient f i + Fourier_coefficient g i"
  using assms trigonometric_set_mul_integrable
  by (simp add: Fourier_coefficient_def orthonormal_coeff_def l2product_def distrib_left)

lemma Fourier_coefficient_minus:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "Fourier_coefficient (\<lambda>x. - f x) i = - Fourier_coefficient f i"
  using assms trigonometric_set_mul_integrable
  by (simp add: Fourier_coefficient_def orthonormal_coeff_def l2product_def)

lemma Fourier_coefficient_diff:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and g: "g absolutely_integrable_on {-pi..pi}"
  shows "Fourier_coefficient (\<lambda>x. f x - g x) i = Fourier_coefficient f i - Fourier_coefficient g i"
proof -
  have mg: "(\<lambda>x. - g x) absolutely_integrable_on {-pi..pi}"
    using g by (simp add: absolutely_integrable_measurable_real)
  show ?thesis
    using Fourier_coefficient_add [OF f mg] Fourier_coefficient_minus [OF g] by simp
qed

lemma Fourier_coefficient_const:
   "Fourier_coefficient (\<lambda>x. c) i = (if i = 0 then c * sqrt(2 * pi) else 0)"
  by (auto simp: Fourier_coefficient_def orthonormal_coeff_def l2product_def trigonometric_set_def divide_simps measure_restrict_space)

lemma Fourier_offset_term:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f absolutely_integrable_on {-pi..pi}" and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows  "Fourier_coefficient (\<lambda>x. f(x+t)) (2 * n + 2) * trigonometric_set (2 * n + 2) 0
        = Fourier_coefficient f(2 * n+1) * trigonometric_set (2 * n+1) t
        + Fourier_coefficient f(2 * n + 2) * trigonometric_set (2 * n + 2) t"
proof -
  have eq: "(2 + 2 * real n) * x / 2 = (1 + real n) * x" for x
    by (simp add: divide_simps)
  have 1: "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. f x * (cos (x + x * n) * cos (t + t * n)))"
    using Fourier_products_integrable_cos [of f "Suc n"] f
    by (simp add: algebra_simps) (simp add: mult.assoc [symmetric])
  have 2: "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. f x * (sin (x + x * n) * sin (t + t * n)))"
    using Fourier_products_integrable_sin [of f "Suc n"] f
    by (simp add: algebra_simps) (simp add: mult.assoc [symmetric])
  have "has_bochner_integral (lebesgue_on {-pi..pi}) (\<lambda>x. cos (real (Suc n) * (x + t - t)) * f(x + t))
                 (LINT x|lebesgue_on {-pi..pi}. cos (real (Suc n) * (x - t)) * f x)"
  proof (rule has_integral_periodic_offset)
    have "(\<lambda>x. cos (real (Suc n) * (x - t)) * f x) absolutely_integrable_on {-pi..pi}"
    proof (rule absolutely_integrable_bounded_measurable_product_real)
      show "(\<lambda>x. cos (real (Suc n) * (x - t))) \<in> borel_measurable (lebesgue_on {-pi..pi})"
        by (intro continuous_imp_measurable_on_sets_lebesgue continuous_intros) auto
      show "bounded ((\<lambda>x. cos (real (Suc n) * (x - t))) ` {-pi..pi})"
        by (rule boundedI [where B=1]) auto
    qed (use f in auto)
    then show "has_bochner_integral (lebesgue_on {-pi..pi}) (\<lambda>x. cos ((Suc n) * (x - t)) * f x) (LINT x|lebesgue_on {-pi..pi}. cos (real (Suc n) * (x - t)) * f x)"
      by (simp add: has_bochner_integral_integrable integrable_restrict_space set_integrable_def)
  next
    fix x
    show "cos (real (Suc n) * (x + (pi - - pi) - t)) * f(x + (pi - - pi)) = cos (real (Suc n) * (x - t)) * f x"
      using periodic cos.plus_of_nat [of "(Suc n) * (x - t)" "Suc n"] by (simp add: algebra_simps)
  qed
  then have "has_bochner_integral (lebesgue_on {-pi..pi}) (\<lambda>x. cos (real (Suc n) * x) * f(x + t))
                 (LINT x|lebesgue_on {-pi..pi}. cos (real (Suc n) * (x - t)) * f x)"
    by simp
  then have "LINT x|lebesgue_on {-pi..pi}. cos ((Suc n) * x) * f(x+t)
           = LINT x|lebesgue_on {-pi..pi}. cos ((Suc n) * (x - t)) * f x"
    using has_bochner_integral_integral_eq by blast
  also have "\<dots> = LINT x|lebesgue_on {-pi..pi}. cos ((Suc n) * x - ((Suc n) * t)) * f x"
    by (simp add: algebra_simps)
  also have "\<dots> = cos ((Suc n) * t) * (LINT x|lebesgue_on {-pi..pi}. cos ((Suc n) * x) * f x)
                 + sin ((Suc n) * t) * (LINT x|lebesgue_on {-pi..pi}. sin ((Suc n) * x) * f x)"
    by (simp add: cos_diff algebra_simps 1 2 flip: integral_mult_left_zero integral_mult_right_zero)
  finally have "LINT x|lebesgue_on {-pi..pi}. cos ((Suc n) * x) * f(x+t)
        = cos ((Suc n) * t) * (LINT x|lebesgue_on {-pi..pi}. cos ((Suc n) * x) * f x)
        + sin ((Suc n) * t) * (LINT x|lebesgue_on {-pi..pi}. sin ((Suc n) * x) * f x)" .
  then show ?thesis
    unfolding Fourier_coefficient_def orthonormal_coeff_def trigonometric_set_def
    by (simp add: eq) (simp add: divide_simps algebra_simps l2product_def)
qed


lemma Fourier_sum_offset:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f absolutely_integrable_on {-pi..pi}" and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows  "(\<Sum>k\<le>2*n. Fourier_coefficient f k * trigonometric_set k t) =
          (\<Sum>k\<le>2*n. Fourier_coefficient (\<lambda>x. f(x+t)) k * trigonometric_set k 0)" (is "?lhs = ?rhs")
proof -
  have "?lhs = Fourier_coefficient f 0 * trigonometric_set 0 t + (\<Sum>k = Suc 0..2*n. Fourier_coefficient f k * trigonometric_set k t)"
    by (simp add: atMost_atLeast0 sum.atLeast_Suc_atMost)
  moreover have "(\<Sum>k = Suc 0..2*n. Fourier_coefficient f k * trigonometric_set k t) =
                 (\<Sum>k = Suc 0..2*n. Fourier_coefficient (\<lambda>x. f(x+t)) k * trigonometric_set k 0)"
  proof (cases n)
    case (Suc n')
    have "(\<Sum>k = Suc 0..2 * n. Fourier_coefficient f k * trigonometric_set k t)
        = (\<Sum>k = Suc 0.. Suc (Suc (2 * n')). Fourier_coefficient f k * trigonometric_set k t)"
      by (simp add: Suc)
    also have "\<dots> = (\<Sum>k \<le> Suc (2 * n'). Fourier_coefficient f(Suc k) * trigonometric_set (Suc k) t)"
      unfolding atMost_atLeast0 using sum.shift_bounds_cl_Suc_ivl by blast
    also have "\<dots> = (\<Sum>k \<le> Suc (2 * n'). Fourier_coefficient (\<lambda>x. f(x+t)) (Suc k) * trigonometric_set (Suc k) 0)"
      unfolding sum.in_pairs_0
    proof (rule sum.cong [OF refl])
      show "Fourier_coefficient f(Suc (2 * k)) * trigonometric_set (Suc (2 * k)) t + Fourier_coefficient f(Suc (Suc (2 * k))) * trigonometric_set (Suc (Suc (2 * k))) t = Fourier_coefficient (\<lambda>x. f(x + t)) (Suc (2 * k)) * trigonometric_set (Suc (2 * k)) 0 + Fourier_coefficient (\<lambda>x. f(x + t)) (Suc (Suc (2 * k))) * trigonometric_set (Suc (Suc (2 * k))) 0"
        if "k \<in> {..n'}" for k
        using that Fourier_offset_term [OF assms, of t ] by (auto simp: trigonometric_set_def)
    qed
    also have "\<dots> = (\<Sum>k = Suc 0..Suc (Suc (2 * n')). Fourier_coefficient (\<lambda>x. f(x+t)) k * trigonometric_set k 0)"
      by (simp only: atMost_atLeast0 sum.shift_bounds_cl_Suc_ivl)
    also have "\<dots> = (\<Sum>k = Suc 0..2*n. Fourier_coefficient (\<lambda>x. f(x+t)) k * trigonometric_set k 0)"
      by (simp add: Suc)
    finally show ?thesis .
  qed auto
  moreover have "?rhs
           = Fourier_coefficient (\<lambda>x. f(x+t)) 0 * trigonometric_set 0 0 + (\<Sum>k = Suc 0..2*n. Fourier_coefficient (\<lambda>x. f(x+t)) k * trigonometric_set k 0)"
    by (simp add: atMost_atLeast0 sum.atLeast_Suc_atMost)
  moreover have "Fourier_coefficient f 0 * trigonometric_set 0 t
               = Fourier_coefficient (\<lambda>x. f(x+t)) 0 * trigonometric_set 0 0"
    by (simp add: Fourier_coefficient_def orthonormal_coeff_def trigonometric_set_def l2product_def integral_periodic_offset periodic)
  ultimately show ?thesis
    by simp
qed


lemma Fourier_sum_offset_unpaired:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f absolutely_integrable_on {-pi..pi}" and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows  "(\<Sum>k\<le>2*n. Fourier_coefficient f k * trigonometric_set k t) =
          (\<Sum>k\<le>n. Fourier_coefficient (\<lambda>x. f(x+t)) (2*k) * trigonometric_set (2*k) 0)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>k\<le>n. Fourier_coefficient (\<lambda>x. f(x+t)) (2*k) *  trigonometric_set (2*k) 0 +
                   Fourier_coefficient (\<lambda>x. f(x+t)) (Suc (2*k)) * trigonometric_set (Suc (2*k)) 0)"
    apply (simp add: assms Fourier_sum_offset)
    apply (subst sum.in_pairs_0 [symmetric])
    by (simp add: trigonometric_set)
  also have "\<dots> = ?rhs"
    by (auto simp: trigonometric_set)
  finally show ?thesis .
qed

subsection\<open>Express partial sums using Dirichlet kernel\<close>

definition Dirichlet_kernel
  where "Dirichlet_kernel \<equiv>
           \<lambda>n x. if x = 0 then real n + 1/2
                          else sin((real n + 1/2) * x) / (2 * sin(x/2))"

lemma Dirichlet_kernel_0 [simp]:
   "\<bar>x\<bar> < 2 * pi \<Longrightarrow> Dirichlet_kernel 0 x = 1/2"
  by (auto simp: Dirichlet_kernel_def sin_zero_iff)

lemma Dirichlet_kernel_minus [simp]: "Dirichlet_kernel n (-x) = Dirichlet_kernel n x"
  by (auto simp: Dirichlet_kernel_def)


lemma Dirichlet_kernel_continuous_strong:
   "continuous_on {-(2 * pi)<..<2 * pi} (Dirichlet_kernel n)"
proof -
  have "isCont (Dirichlet_kernel n) z" if "-(2 * pi) < z" "z < 2 * pi" for z
  proof (cases "z=0")
    case True
    have *: "(\<lambda>x. sin ((n + 1/2) * x) / (2 * sin (x/2))) \<midarrow>0 \<rightarrow> real n + 1/2"
      by real_asymp
    show ?thesis
      unfolding Dirichlet_kernel_def continuous_at True
      apply (rule Lim_transform_eventually [where f = "\<lambda>x. sin((n + 1/2) * x) / (2 * sin(x/2))"])
       apply (auto simp: * eventually_at_filter)
      done
  next
    case False
    have "continuous (at z) (\<lambda>x. sin((real n + 1/2) * x) / (2 * sin(x/2)))"
      using that False by (intro continuous_intros) (auto simp: sin_zero_iff)
    moreover have "\<forall>\<^sub>F x in nhds z. x \<noteq> 0"
      using False t1_space_nhds by blast
    ultimately show ?thesis
      using False
      by (force simp: Dirichlet_kernel_def continuous_at eventually_at_filter elim: Lim_transform_eventually)
  qed
  then show ?thesis
    by (simp add: continuous_on_eq_continuous_at)
qed

lemma Dirichlet_kernel_continuous: "continuous_on {-pi..pi} (Dirichlet_kernel n)"
  apply (rule continuous_on_subset [OF Dirichlet_kernel_continuous_strong], clarsimp)
  using pi_gt_zero by linarith


lemma absolutely_integrable_mult_Dirichlet_kernel:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>x. Dirichlet_kernel n x * f x) absolutely_integrable_on {-pi..pi}"
proof (rule absolutely_integrable_bounded_measurable_product_real)
  show "Dirichlet_kernel n \<in> borel_measurable (lebesgue_on {-pi..pi})"
    by (simp add: Dirichlet_kernel_continuous continuous_imp_measurable_on_sets_lebesgue)
  have "compact (Dirichlet_kernel n ` {-pi..pi})"
    by (auto simp: compact_continuous_image [OF Dirichlet_kernel_continuous])
  then show "bounded (Dirichlet_kernel n ` {-pi..pi})"
    using compact_imp_bounded by blast
qed (use assms in auto)


lemma cosine_sum_lemma:
   "(1/2 + (\<Sum>k = Suc 0..n. cos(real k * x))) * sin(x/2) =  sin((real n + 1/2) * x) / 2"
proof -
  consider "n=0" | "n \<ge> 1" by linarith
  then show ?thesis
  proof cases
    case 2
    then have "(\<Sum>k = Suc 0..n. (sin (real k * x + x/2) * 2 - sin (real k * x - x/2) * 2) / 2)
        = sin (real n * x + x/2) - sin (x/2)"
    proof (induction n)
      case (Suc n)
      show ?case
      proof (cases "n=0")
        case False
        with Suc show ?thesis
          by (simp add: divide_simps algebra_simps)
      qed auto
    qed auto
    then show ?thesis
      by (simp add: distrib_right sum_distrib_right cos_times_sin)
  qed auto
qed


lemma Dirichlet_kernel_cosine_sum:
  assumes "\<bar>x\<bar> < 2 * pi"
  shows "Dirichlet_kernel n x = 1/2 + (\<Sum>k = Suc 0..n. cos(real k * x))"
proof -
  have "sin ((real n + 1/2) * x) / (2 * sin (x/2)) = 1/2 + (\<Sum>k = Suc 0..n. cos (real k * x))"
    if "x \<noteq> 0"
  proof -
    have "sin(x/2) \<noteq> 0"
      using assms that by (auto simp: sin_zero_iff)
    then show ?thesis
     using cosine_sum_lemma [of x n] by (simp add: divide_simps)
  qed
  then show ?thesis
    by (auto simp: Dirichlet_kernel_def)
qed

lemma integrable_Dirichlet_kernel: "integrable (lebesgue_on {-pi..pi}) (Dirichlet_kernel n)"
  using Dirichlet_kernel_continuous continuous_imp_integrable_real by blast

lemma integral_Dirichlet_kernel [simp]:
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (Dirichlet_kernel n) = pi"
proof -
  have "integral\<^sup>L (lebesgue_on {-pi..pi}) (Dirichlet_kernel n) = LINT x|lebesgue_on {-pi..pi}. 1/2 + (\<Sum>k = Suc 0..n. cos (k * x))"
    using pi_ge_two
    by (force intro: Bochner_Integration.integral_cong [OF refl Dirichlet_kernel_cosine_sum])
  also have "\<dots> = (LINT x|lebesgue_on {-pi..pi}. 1/2) + (LINT x|lebesgue_on {-pi..pi}. (\<Sum>k = Suc 0..n. cos (k * x)))"
  proof (rule Bochner_Integration.integral_add)
    show "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. \<Sum>k = Suc 0..n. cos (real k * x))"
      by (rule Bochner_Integration.integrable_sum) (metis integrable_cos_cx mult_commute_abs)
  qed auto
  also have "\<dots> = pi"
  proof -
    have "\<And>i. \<lbrakk>Suc 0 \<le> i; i \<le> n\<rbrakk>
         \<Longrightarrow> integrable (lebesgue_on {-pi..pi}) (\<lambda>x. cos (real i * x))"
      by (metis integrable_cos_cx mult_commute_abs)
    then have "LINT x|lebesgue_on {-pi..pi}. (\<Sum>k = Suc 0..n. cos (real k * x)) = 0"
      by (simp add: Bochner_Integration.integral_sum)
    then show ?thesis
      by (auto simp: measure_restrict_space)
  qed
  finally show ?thesis .
qed

lemma integral_Dirichlet_kernel_half [simp]:
  "integral\<^sup>L (lebesgue_on {0..pi}) (Dirichlet_kernel n) = pi/2"
proof -
  have "integral\<^sup>L (lebesgue_on {- pi..0}) (Dirichlet_kernel n) +
        integral\<^sup>L (lebesgue_on {0..pi}) (Dirichlet_kernel n) = pi"
    using integral_combine [OF integrable_Dirichlet_kernel] integral_Dirichlet_kernel by simp
  moreover have "integral\<^sup>L (lebesgue_on {- pi..0}) (Dirichlet_kernel n) = integral\<^sup>L (lebesgue_on {0..pi}) (Dirichlet_kernel n)"
    using integral_reflect_real [of pi 0 "Dirichlet_kernel n"] by simp
  ultimately show ?thesis
    by simp
qed


lemma Fourier_sum_offset_Dirichlet_kernel:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows
   "(\<Sum>k\<le>2*n. Fourier_coefficient f k * trigonometric_set k t) =
            integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. Dirichlet_kernel n x * f(x+t)) / pi"
  (is "?lhs = ?rhs")
proof -
  have ft: "(\<lambda>x. f(x+t)) absolutely_integrable_on {-pi..pi}"
    using absolutely_integrable_periodic_offset [OF f, of t] periodic by simp
  have "?lhs = (\<Sum>k=0..n. Fourier_coefficient (\<lambda>x. f(x+t)) (2*k) * trigonometric_set (2*k) 0)"
    using Fourier_sum_offset_unpaired assms atMost_atLeast0 by auto
  also have "\<dots> = Fourier_coefficient (\<lambda>x. f(x+t)) 0 / sqrt (2 * pi)
                 + (\<Sum>k = Suc 0..n. Fourier_coefficient (\<lambda>x. f(x+t)) (2*k) / sqrt pi)"
    by (simp add: sum.atLeast_Suc_atMost trigonometric_set_def)
  also have "\<dots> = (LINT x|lebesgue_on {-pi..pi}. f(x+t)) / (2 * pi) +
                   (\<Sum>k = Suc 0..n. (LINT x|lebesgue_on {-pi..pi}. cos (real k * x) * f(x+t)) / pi)"
    by (simp add: Fourier_coefficient_def orthonormal_coeff_def trigonometric_set_def l2product_def)
  also have "\<dots> = LINT x|lebesgue_on {-pi..pi}.
                     f(x+t) / (2 * pi) + (\<Sum>k = Suc 0..n. (cos (real k * x) * f(x+t)) / pi)"
    using Fourier_products_integrable_cos [OF ft] absolutely_integrable_imp_integrable [OF ft] by simp
  also have "\<dots> = (LINT x|lebesgue_on {-pi..pi}.
                     f(x+t) / 2 + (\<Sum>k = Suc 0..n. cos (real k * x) * f(x+t))) / pi"
    by (simp add: divide_simps sum_distrib_right mult.assoc)
  also have "\<dots> = ?rhs"
  proof -
    have "LINT x|lebesgue_on {-pi..pi}. f(x + t) / 2 + (\<Sum>k = Suc 0..n. cos (real k * x) * f(x + t))
        = LINT x|lebesgue_on {-pi..pi}. Dirichlet_kernel n x * f(x + t)"
    proof -
      have eq: "f(x+t) / 2 + (\<Sum>k = Suc 0..n. cos (real k * x) * f(x + t))
              = Dirichlet_kernel n x * f(x + t)" if "- pi \<le> x" "x \<le> pi" for x
      proof (cases "x = 0")
        case False
        then have "sin (x/2) \<noteq> 0"
          using that by (auto simp: sin_zero_iff)
        then have "f(x + t) * (1/2 + (\<Sum>k = Suc 0..n. cos(real k * x))) = f(x + t) * sin((real n + 1/2) * x) / 2 / sin(x/2)"
          using cosine_sum_lemma [of x n] by (simp add: divide_simps)
        then show ?thesis
          by (simp add: Dirichlet_kernel_def False field_simps sum_distrib_left)
      qed (simp add: Dirichlet_kernel_def algebra_simps)
      show ?thesis
        by (rule Bochner_Integration.integral_cong [OF refl]) (simp add: eq)
    qed
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed


lemma Fourier_sum_limit_Dirichlet_kernel:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "((\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> l)
     \<longleftrightarrow> (\<lambda>n. LINT x|lebesgue_on {-pi..pi}. Dirichlet_kernel n x * f(x + t)) \<longlonglongrightarrow> pi * l"
    (is "?lhs = ?rhs")
proof -
  have "?lhs \<longleftrightarrow> (\<lambda>n. (LINT x|lebesgue_on {-pi..pi}. Dirichlet_kernel n x * f(x + t)) / pi) \<longlonglongrightarrow> l"
    by (simp add: Fourier_sum_limit_pair [OF f, symmetric] Fourier_sum_offset_Dirichlet_kernel assms)
  also have "\<dots> \<longleftrightarrow> (\<lambda>k. (LINT x|lebesgue_on {-pi..pi}. Dirichlet_kernel k x * f(x + t)) * inverse pi)
                    \<longlonglongrightarrow> pi * l * inverse pi"
    by (auto simp: divide_simps)
  also have "\<dots> \<longleftrightarrow> ?rhs"
    using tendsto_mult_right_iff [of "inverse pi", symmetric] by auto
  finally show ?thesis .
qed

subsection\<open>A directly deduced sufficient condition for convergence at a point\<close>

lemma simple_Fourier_convergence_periodic:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and ft: "(\<lambda>x. (f(x+t) - f t) / sin(x/2)) absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> f t"
proof -
  let ?\<Phi> = "\<lambda>n. \<Sum>k\<le>n. Fourier_coefficient (\<lambda>x. f x - f t) k * trigonometric_set k t"
  let ?\<Psi> = "\<lambda>n. LINT x|lebesgue_on {-pi..pi}. Dirichlet_kernel n x * (f(x + t) - f t)"
  have fft: "(\<lambda>x. f x - f t) absolutely_integrable_on {-pi..pi}"
    by (simp add: f absolutely_integrable_measurable_real)
  have fxt: "(\<lambda>x. f(x + t)) absolutely_integrable_on {-pi..pi}"
    using absolutely_integrable_periodic_offset assms by auto
  have *: "?\<Phi> \<longlonglongrightarrow> 0 \<longleftrightarrow> ?\<Psi> \<longlonglongrightarrow> 0"
    by (simp add: Fourier_sum_limit_Dirichlet_kernel fft periodic)
  moreover have "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t) - f t) \<longlonglongrightarrow> 0"
    if "?\<Phi> \<longlonglongrightarrow> 0"
  proof (rule Lim_transform_eventually [OF that eventually_sequentiallyI])
    show "(\<Sum>k\<le>n. Fourier_coefficient (\<lambda>x. f x - f t) k * trigonometric_set k t)
        = (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t) - f t"
      if "Suc 0 \<le> n" for n
    proof -
      have "(\<Sum>k = Suc 0..n. Fourier_coefficient (\<lambda>x. f x - f t) k * trigonometric_set k t)
          = (\<Sum>k = Suc 0..n. Fourier_coefficient f k * trigonometric_set k t)"
      proof (rule sum.cong [OF refl])
        fix k
        assume k: "k \<in> {Suc 0..n}"
        then have [simp]: "integral\<^sup>L (lebesgue_on {-pi..pi}) (trigonometric_set k) = 0"
          by (auto simp: trigonometric_set_def)
        show "Fourier_coefficient (\<lambda>x. f x - f t) k * trigonometric_set k t = Fourier_coefficient f k * trigonometric_set k t"
          using k unfolding Fourier_coefficient_def orthonormal_coeff_def l2product_def
          by (simp add: right_diff_distrib f absolutely_integrable_measurable_real trigonometric_set_mul_integrable)
      qed
      moreover have "Fourier_coefficient (\<lambda>x. f x - f t) 0 * trigonometric_set 0 t =
                     Fourier_coefficient f 0 * trigonometric_set 0 t - f t"
        using f unfolding Fourier_coefficient_def orthonormal_coeff_def l2product_def
        by (auto simp: divide_simps trigonometric_set absolutely_integrable_imp_integrable measure_restrict_space)
      ultimately show ?thesis
        by (simp add: sum.atLeast_Suc_atMost atMost_atLeast0)
    qed
  qed
  moreover
  have "?\<Psi> \<longlonglongrightarrow> 0"
  proof -
    have eq: "\<And>n. ?\<Psi> n = integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin((n + 1/2) * x) * ((f(x+t) - f t) / sin(x/2) / 2))"
      unfolding Dirichlet_kernel_def
      by (rule Bochner_Integration.integral_cong [OF refl]) (auto simp: divide_simps sin_zero_iff)
    show ?thesis
      unfolding eq
      by (intro ft set_integrable_divide Riemann_lebesgue_sin_half)
  qed
  ultimately show ?thesis
    by (simp add: LIM_zero_cancel)
qed


subsection\<open>A more natural sufficient Hoelder condition at a point\<close>

lemma bounded_inverse_sin_half:
  assumes "d > 0"
  obtains B where "B>0" "\<And>x. x \<in> ({-pi..pi} - {-d<..<d}) \<Longrightarrow> \<bar>inverse (sin (x/2))\<bar> \<le> B"
proof -
  have "bounded ((\<lambda>x. inverse (sin (x/2))) ` ({-pi..pi} - {- d<..<d}))"
  proof (intro compact_imp_bounded compact_continuous_image)
    have "\<lbrakk>x \<in> {-pi..pi}; x \<noteq> 0\<rbrakk> \<Longrightarrow> sin (x/2) \<noteq> 0" for x
      using \<open>0 < d\<close> by (auto simp: sin_zero_iff)
    then show "continuous_on ({-pi..pi} - {-d<..<d}) (\<lambda>x. inverse (sin (x/2)))"
      using \<open>0 < d\<close> by (intro continuous_intros) auto
    show "compact ({-pi..pi} - {-d<..<d})"
      by (simp add: compact_diff)
  qed
  then show thesis
    using that by (auto simp: bounded_pos)
qed

proposition Hoelder_Fourier_convergence_periodic:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and "d > 0" "a > 0"
    and ft: "\<And>x. \<bar>x-t\<bar> < d \<Longrightarrow> \<bar>f x - f t\<bar> \<le> M * \<bar>x-t\<bar> powr a"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> f t"
proof (rule simple_Fourier_convergence_periodic [OF f])
  have half: "((\<lambda>x. sin(x/2)) has_real_derivative 1/2) (at 0)"
    by (rule derivative_eq_intros refl | force)+
  then obtain e0::real where "e0 > 0" and e0: "\<And>x. \<lbrakk>x \<noteq> 0; \<bar>x\<bar> < e0\<rbrakk> \<Longrightarrow> \<bar>sin (x/2) / x - 1/2\<bar> < 1/4"
    apply (simp add: DERIV_def Lim_at dist_real_def)
    apply (drule_tac x="1/4" in spec, auto)
    done
  obtain e where "e > 0" and e: "\<And>x. \<bar>x\<bar> < e \<Longrightarrow> \<bar>(f(x+t) - f t) / sin (x/2)\<bar> \<le> 4 * (\<bar>M\<bar> * \<bar>x\<bar> powr (a-1))"
  proof
    show "min d e0 > 0"
      using \<open>d > 0\<close> \<open>e0 > 0\<close> by auto
  next
    fix x
    assume x: "\<bar>x\<bar> < min d e0"
    show "\<bar>(f(x + t) - f t) / sin (x/2)\<bar> \<le> 4 * (\<bar>M\<bar> * \<bar>x\<bar> powr (a - 1))"
    proof (cases "sin(x/2) = 0 \<or> x=0")
      case False
      have eq: "\<bar>(f(x + t) - f t) / sin (x/2)\<bar> = \<bar>inverse (sin (x/2) / x)\<bar> * (\<bar>f(x + t) - f t\<bar> / \<bar>x\<bar>)"
        by simp
      show ?thesis
        unfolding eq
      proof (rule mult_mono)
        have "\<bar>sin (x/2) / x - 1/2\<bar> < 1/4"
          using e0 [of x] x False by force
        then have "1/4 \<le> \<bar>sin (x/2) / x\<bar>"
          by (simp add: abs_if field_simps split: if_split_asm)
        then show "\<bar>inverse (sin (x/2) / x)\<bar> \<le> 4"
          using False by (simp add: field_simps)
        have "\<bar>f(x + t) - f t\<bar> / \<bar>x\<bar> \<le> M * \<bar>x + t - t\<bar> powr (a - 1)"
          using ft [of "x+t"] x by (auto simp: divide_simps algebra_simps Transcendental.powr_mult_base)
        also have "\<dots> \<le> \<bar>M\<bar> * \<bar>x\<bar> powr (a - 1)"
          by (simp add: mult_mono)
        finally show "\<bar>f(x + t) - f t\<bar> / \<bar>x\<bar> \<le> \<bar>M\<bar> * \<bar>x\<bar> powr (a - 1)" .
      qed auto
    qed auto
  qed
  obtain B where "B>0" and B: "\<And>x. x \<in> ({-pi..pi} - {- e<..<e}) \<Longrightarrow> \<bar>inverse (sin (x/2))\<bar> \<le> B"
    using bounded_inverse_sin_half [OF \<open>e > 0\<close>] by metis
  let ?g = "\<lambda>x. max (B * \<bar>f(x + t) - f t\<bar>) ((4 * \<bar>M\<bar>) * \<bar>x\<bar> powr (a - 1))"
  show "(\<lambda>x. (f(x + t) - f t) / sin (x/2)) absolutely_integrable_on {-pi..pi}"
  proof (rule measurable_bounded_by_integrable_imp_absolutely_integrable)
    have fxt: "(\<lambda>x. f(x + t)) absolutely_integrable_on {-pi..pi}"
      using absolutely_integrable_periodic_offset assms by auto
    show "(\<lambda>x. (f(x + t) - f t) / sin (x/2)) \<in> borel_measurable (lebesgue_on {-pi..pi})"
    proof (intro measurable)
      show "(\<lambda>x. f(x + t)) \<in> borel_measurable (lebesgue_on {-pi..pi})"
        using absolutely_integrable_on_def fxt integrable_imp_measurable by blast
      show "(\<lambda>x. sin (x/2)) \<in> borel_measurable (lebesgue_on {-pi..pi})"
        by (intro continuous_imp_measurable_on_sets_lebesgue continuous_intros) auto
    qed auto
    have "(\<lambda>x. f(x + t) - f t) absolutely_integrable_on {-pi..pi}"
      by (intro set_integral_diff fxt) (simp add: set_integrable_def)
    moreover
    have "(\<lambda>x. \<bar>x\<bar> powr (a - 1)) absolutely_integrable_on {-pi..pi}"
    proof -
      have "((\<lambda>x. x powr (a - 1)) has_integral
       inverse a * pi powr a - inverse a * 0 powr a)
       {0..pi}"
      proof (rule fundamental_theorem_of_calculus_interior)
        show "continuous_on {0..pi} (\<lambda>x. inverse a * x powr a)"
          using \<open>a > 0\<close>
          by (intro continuous_on_powr' continuous_intros) auto
        show "((\<lambda>b. inverse a * b powr a) has_vector_derivative x powr (a - 1)) (at x)"
          if "x \<in> {0<..<pi}" for x
          using that \<open>a > 0\<close>
          apply (simp flip: has_field_derivative_iff_has_vector_derivative)
          apply (rule derivative_eq_intros | simp)+
          done
      qed auto
      then have int: "(\<lambda>x. x powr (a - 1)) integrable_on {0..pi}"
        by blast
      show ?thesis
      proof (rule nonnegative_absolutely_integrable_1)
        show "(\<lambda>x. \<bar>x\<bar> powr (a - 1)) integrable_on {-pi..pi}"
        proof (rule Henstock_Kurzweil_Integration.integrable_combine)
          show "(\<lambda>x. \<bar>x\<bar> powr (a - 1)) integrable_on {0..pi}"
            using int integrable_eq by fastforce
          then show "(\<lambda>x. \<bar>x\<bar> powr (a - 1)) integrable_on {- pi..0}"
            using Henstock_Kurzweil_Integration.integrable_reflect_real by fastforce
        qed auto
      qed auto
    qed
    ultimately show "?g integrable_on {-pi..pi}"
      apply (intro set_lebesgue_integral_eq_integral absolutely_integrable_max_1 absolutely_integrable_bounded_measurable_product_real set_integrable_abs measurable)
              apply (auto simp: image_constant_conv)
      done
    show "norm ((f(x + t) - f t) / sin (x/2)) \<le> ?g x" if "x \<in> {-pi..pi}" for x
    proof (cases "\<bar>x\<bar> < e")
      case True
      then show ?thesis
        using e [OF True] by (simp add: max_def)
    next
      case False
      then have "\<bar>inverse (sin (x/2))\<bar> \<le> B"
        using B that by force
      then have "\<bar>inverse (sin (x/2))\<bar> * \<bar>f(x + t) - f t\<bar> \<le> B * \<bar>f(x + t) - f t\<bar>"
        by (simp add: mult_right_mono)
      then have "\<bar>f(x + t) - f t\<bar> / \<bar>sin (x/2)\<bar> \<le> B * \<bar>f(x + t) - f t\<bar>"
        by (simp add: divide_simps split: if_split_asm)
      then show ?thesis
        by auto
    qed
  qed auto
qed (auto simp: periodic)


text\<open>In particular, a Lipschitz condition at the point\<close>
corollary Lipschitz_Fourier_convergence_periodic:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and "d > 0"
    and ft: "\<And>x. \<bar>x-t\<bar> < d \<Longrightarrow> \<bar>f x - f t\<bar> \<le> M * \<bar>x-t\<bar>"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> f t"
  using Hoelder_Fourier_convergence_periodic [OF f \<open>d > 0\<close>, of 1] assms
  by (fastforce simp add:)

text\<open>In particular, if left and right derivatives both exist\<close>
proposition bi_differentiable_Fourier_convergence_periodic:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and f_lt: "f differentiable at_left t"
    and f_gt: "f differentiable at_right t"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> f t"
proof -
  obtain D_lt where D_lt: "\<And>e. e > 0 \<Longrightarrow> \<exists>d>0. \<forall>x<t. 0 < dist x t \<and> dist x t < d \<longrightarrow> dist ((f x - f t) / (x - t)) D_lt < e"
    using f_lt unfolding has_field_derivative_iff real_differentiable_def Lim_within
    by (meson lessThan_iff)
  then obtain d_lt where "d_lt > 0"
    and d_lt: "\<And>x. \<lbrakk>x < t; 0 < \<bar>x - t\<bar>; \<bar>x - t\<bar> < d_lt\<rbrakk> \<Longrightarrow> \<bar>(f x - f t) / (x - t) - D_lt\<bar> < 1"
    unfolding dist_real_def by (metis dist_commute dist_real_def zero_less_one)
  obtain D_gt where D_gt: "\<And>e. e > 0 \<Longrightarrow> \<exists>d>0. \<forall>x>t. 0 < dist x t \<and> dist x t < d \<longrightarrow> dist ((f x - f t) / (x - t)) D_gt < e"
    using f_gt unfolding has_field_derivative_iff real_differentiable_def Lim_within
    by (meson greaterThan_iff)
  then obtain d_gt where "d_gt > 0"
    and d_gt: "\<And>x. \<lbrakk>x > t; 0 < \<bar>x - t\<bar>; \<bar>x - t\<bar> < d_gt\<rbrakk> \<Longrightarrow> \<bar>(f x - f t) / (x - t) - D_gt\<bar> < 1"
    unfolding dist_real_def by (metis dist_commute dist_real_def zero_less_one)
  show ?thesis
  proof (rule Lipschitz_Fourier_convergence_periodic [OF f])
    fix x
    assume "\<bar>x - t\<bar> < min d_lt d_gt"
    then have *: "\<bar>x - t\<bar> < d_lt" "\<bar>x - t\<bar> < d_gt"
      by auto
    consider "x<t" | "x=t" | "x>t"
      by linarith
    then show "\<bar>f x - f t\<bar> \<le> (\<bar>D_lt\<bar> + \<bar>D_gt\<bar> + 1)  * \<bar>x - t\<bar>"
    proof cases
      case 1
      then have "\<bar>(f x - f t) / (x - t) - D_lt\<bar> < 1"
        using d_lt [OF 1] * by auto
      then have "\<bar>(f x - f t) / (x - t)\<bar> - \<bar>D_lt\<bar> < 1"
        by linarith
      then have "\<bar>f x - f t\<bar> \<le> (\<bar>D_lt\<bar> + 1) * \<bar>x - t\<bar>"
        by (simp add: comm_semiring_class.distrib divide_simps split: if_split_asm)
      also have "\<dots> \<le> (\<bar>D_lt\<bar> + \<bar>D_gt\<bar> + 1) * \<bar>x - t\<bar>"
        by (simp add: mult_right_mono)
      finally show ?thesis .
    next
      case 3
      then have "\<bar>(f x - f t) / (x - t) - D_gt\<bar> < 1"
        using d_gt [OF 3] * by auto
      then have "\<bar>(f x - f t) / (x - t)\<bar> - \<bar>D_gt\<bar> < 1"
        by linarith
      then have "\<bar>f x - f t\<bar> \<le> (\<bar>D_gt\<bar> + 1) * \<bar>x - t\<bar>"
        by (simp add: comm_semiring_class.distrib divide_simps split: if_split_asm)
      also have "\<dots> \<le> (\<bar>D_lt\<bar> + \<bar>D_gt\<bar> + 1) * \<bar>x - t\<bar>"
        by (simp add: mult_right_mono)
      finally show ?thesis .
    qed auto
  qed (auto simp: \<open>0 < d_gt\<close> \<open>0 < d_lt\<close> periodic)
qed


text\<open>And in particular at points where the function is differentiable\<close>
lemma differentiable_Fourier_convergence_periodic:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and fdif: "f differentiable (at t)"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> f t"
  by (rule bi_differentiable_Fourier_convergence_periodic) (auto simp: differentiable_at_withinI assms)

text\<open>Use reflection to halve the region of integration\<close>
lemma absolutely_integrable_mult_Dirichlet_kernel_reflected:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>x. Dirichlet_kernel n x * f(t+x)) absolutely_integrable_on {-pi..pi}"
        "(\<lambda>x. Dirichlet_kernel n x * f(t-x)) absolutely_integrable_on {-pi..pi}"
        "(\<lambda>x. Dirichlet_kernel n x * c) absolutely_integrable_on {-pi..pi}"
proof -
  show "(\<lambda>x. Dirichlet_kernel n x * f(t+x)) absolutely_integrable_on {-pi..pi}"
    apply (rule absolutely_integrable_mult_Dirichlet_kernel)
    using absolutely_integrable_periodic_offset [OF f, of t] periodic
    apply simp
    done
  then show "(\<lambda>x. Dirichlet_kernel n x * f(t-x)) absolutely_integrable_on {-pi..pi}"
    by (subst absolutely_integrable_reflect_real [symmetric]) simp
  show "(\<lambda>x. Dirichlet_kernel n x * c) absolutely_integrable_on {-pi..pi}"
    by (simp add: absolutely_integrable_measurable_real borel_measurable_integrable integrable_Dirichlet_kernel)
qed


lemma absolutely_integrable_mult_Dirichlet_kernel_reflected_part:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "d \<le> pi"
  shows "(\<lambda>x. Dirichlet_kernel n x * f(t+x)) absolutely_integrable_on {0..d}"
        "(\<lambda>x. Dirichlet_kernel n x * f(t-x)) absolutely_integrable_on {0..d}"
        "(\<lambda>x. Dirichlet_kernel n x * c) absolutely_integrable_on {0..d}"
  using absolutely_integrable_mult_Dirichlet_kernel_reflected [OF f periodic, of n] \<open>d \<le> pi\<close>
  by (force intro: absolutely_integrable_on_subinterval)+

lemma absolutely_integrable_mult_Dirichlet_kernel_reflected_part2:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "d \<le> pi"
  shows "(\<lambda>x. Dirichlet_kernel n x * (f(t+x) + f(t-x))) absolutely_integrable_on {0..d}"
        "(\<lambda>x. Dirichlet_kernel n x * ((f(t+x) + f(t-x)) - c)) absolutely_integrable_on {0..d}"
  using absolutely_integrable_mult_Dirichlet_kernel_reflected_part assms
  by (simp_all add: distrib_left right_diff_distrib)

lemma integral_reflect_and_add:
  fixes f :: "real \<Rightarrow> 'b::euclidean_space"
  assumes "integrable (lebesgue_on {-a..a}) f"
  shows "integral\<^sup>L (lebesgue_on {-a..a}) f = integral\<^sup>L (lebesgue_on {0..a})  (\<lambda>x. f x + f(-x))"
proof (cases "a \<ge> 0")
  case True
  have f: "integrable (lebesgue_on {0..a}) f" "integrable (lebesgue_on {-a..0}) f"
    using integrable_subinterval assms by fastforce+
  then have fm: "integrable (lebesgue_on {0..a}) (\<lambda>x. f(-x))"
    using integrable_reflect_real by fastforce
  have "integral\<^sup>L (lebesgue_on {-a..a}) f = integral\<^sup>L (lebesgue_on {-a..0}) f + integral\<^sup>L (lebesgue_on {0..a}) f"
    by (simp add: True assms integral_combine)
  also have "\<dots> = integral\<^sup>L (lebesgue_on {0..a}) (\<lambda>x. f(-x)) + integral\<^sup>L (lebesgue_on {0..a}) f"
    by (metis (no_types) add.inverse_inverse add.inverse_neutral integral_reflect_real)
  also have "\<dots> = integral\<^sup>L (lebesgue_on {0..a}) (\<lambda>x. f x + f(-x))"
    by (simp add: fm f)
  finally show ?thesis .
qed (use assms in auto)

lemma Fourier_sum_offset_Dirichlet_kernel_half:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<Sum>k\<le>2*n. Fourier_coefficient f k * trigonometric_set k t) - l
       = (LINT x|lebesgue_on {0..pi}. Dirichlet_kernel n x * (f(t+x) + f(t-x) - 2*l)) / pi"
proof -
  have fxt: "(\<lambda>x. f(x + t)) absolutely_integrable_on {-pi..pi}"
    using absolutely_integrable_periodic_offset assms by auto
  have int: "integrable (lebesgue_on {0..pi}) (Dirichlet_kernel n)"
    using not_integrable_integral_eq by fastforce
  have "LINT x|lebesgue_on {-pi..pi}. Dirichlet_kernel n x * f(x + t)
      = LINT x|lebesgue_on {0..pi}. Dirichlet_kernel n x * f(x + t) + Dirichlet_kernel n (- x) * f(- x + t)"
    by (simp add: integral_reflect_and_add absolutely_integrable_imp_integrable absolutely_integrable_mult_Dirichlet_kernel fxt)
  also have "\<dots> = (LINT x|lebesgue_on {0..pi}. Dirichlet_kernel n x * (f(t+x) + f(t-x) - 2*l)) + pi * l"
    using absolutely_integrable_mult_Dirichlet_kernel_reflected_part [OF f periodic order_refl, of n t]
    apply (simp add: algebra_simps absolutely_integrable_imp_integrable int)
    done
  finally show ?thesis
    by (simp add: Fourier_sum_offset_Dirichlet_kernel assms divide_simps)
qed

lemma Fourier_sum_limit_Dirichlet_kernel_half:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> l
     \<longleftrightarrow> (\<lambda>n. (LINT x|lebesgue_on {0..pi}. Dirichlet_kernel n x * (f(t+x) + f(t-x) - 2*l))) \<longlonglongrightarrow> 0"
  apply (simp flip: Fourier_sum_limit_pair [OF f])
  apply (simp add: Lim_null [where l=l] Fourier_sum_offset_Dirichlet_kernel_half assms)
  done


subsection\<open>Localization principle: convergence only depends on values "nearby"\<close>

proposition Riemann_localization_integral:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and g: "g absolutely_integrable_on {-pi..pi}"
    and "d > 0" and d: "\<And>x. \<bar>x\<bar> < d \<Longrightarrow> f x = g x"
  shows "(\<lambda>n. integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. Dirichlet_kernel n x * f x)
            - integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. Dirichlet_kernel n x * g x))
         \<longlonglongrightarrow> 0"  (is "?a \<longlonglongrightarrow> 0")
proof -
  let ?f = "\<lambda>x. (if \<bar>x\<bar> < d then 0 else f x - g x) / sin(x/2) / 2"
  have eq: "?a n = integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin((n+1/2) * x) * ?f x)" for n
  proof -
    have "?a n = integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. Dirichlet_kernel n x * (if \<bar>x\<bar> < d then 0 else f x - g x))"
      apply (simp add: absolutely_integrable_imp_integrable absolutely_integrable_mult_Dirichlet_kernel f g flip: Bochner_Integration.integral_diff)
      apply (auto simp: d algebra_simps intro: Bochner_Integration.integral_cong)
      done
    also have "\<dots> = integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin((n+1/2) * x) * ?f x)"
      using \<open>d > 0\<close> by (auto simp: Dirichlet_kernel_def intro: Bochner_Integration.integral_cong)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding eq
  proof (rule Riemann_lebesgue_sin_half)
    obtain B where "B>0" and B: "\<And>x. x \<in> ({-pi..pi} - {-d<..<d}) \<Longrightarrow> \<bar>inverse (sin (x/2))\<bar> \<le> B"
      using bounded_inverse_sin_half [OF \<open>d > 0\<close>] by metis
    have "(\<lambda>x. (if \<bar>x\<bar> < d then 0 else f x - g x) / sin (x/2)) absolutely_integrable_on {-pi..pi}"
    proof (rule measurable_bounded_by_integrable_imp_absolutely_integrable)
      show "(\<lambda>x. (if \<bar>x\<bar> < d then 0 else f x - g x) / sin (x/2)) \<in> borel_measurable (lebesgue_on {-pi..pi})"
      proof (intro measurable)
        show "f \<in> borel_measurable (lebesgue_on {-pi..pi})" "g \<in> borel_measurable (lebesgue_on {-pi..pi})"
          using absolutely_integrable_on_def f g integrable_imp_measurable by blast+
        show "(\<lambda>x. x) \<in> borel_measurable (lebesgue_on {-pi..pi})"
             "(\<lambda>x. sin (x/2)) \<in> borel_measurable (lebesgue_on {-pi..pi})"
          by (intro continuous_intros continuous_imp_measurable_on_sets_lebesgue | force)+
      qed auto
      have "(\<lambda>x. B * \<bar>f x - g x\<bar>) absolutely_integrable_on {-pi..pi}"
        using \<open>B > 0\<close> by (simp add: f g set_integrable_abs)
      then show "(\<lambda>x. B * \<bar>f x - g x\<bar>) integrable_on {-pi..pi}"
        using absolutely_integrable_on_def by blast
    next
      fix x
      assume x: "x \<in> {-pi..pi}"
      then have [simp]: "sin (x/2) = 0 \<longleftrightarrow> x=0"
        using \<open>0 < d\<close> by (force simp: sin_zero_iff)
      show "norm ((if \<bar>x\<bar> < d then 0 else f x - g x) / sin (x/2)) \<le> B * \<bar>f x - g x\<bar>"
      proof (cases "\<bar>x\<bar> < d")
        case False
        then have "1 \<le> B * \<bar>sin (x/2)\<bar>"
          using \<open>B > 0\<close> B [of x] x \<open>d > 0\<close>
          by (auto simp: abs_less_iff divide_simps split: if_split_asm)
        then have "1 * \<bar>f x - g x\<bar> \<le> B * \<bar>sin (x/2)\<bar> * \<bar>f x - g x\<bar>"
          by (metis (full_types) abs_ge_zero mult.commute mult_left_mono)
        then show ?thesis
          using False by (auto simp: divide_simps algebra_simps)
      qed (simp add: d)
    qed auto
    then show "(\<lambda>x. (if \<bar>x\<bar> < d then 0 else f x - g x) / sin (x/2) / 2) absolutely_integrable_on {-pi..pi}"
      using set_integrable_divide by blast
  qed
qed

lemma Riemann_localization_integral_range:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and "0 < d" "d \<le> pi"
  shows "(\<lambda>n. integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. Dirichlet_kernel n x * f x)
            - integral\<^sup>L (lebesgue_on {-d..d}) (\<lambda>x. Dirichlet_kernel n x * f x))
             \<longlonglongrightarrow> 0"
proof -
  have *: "(\<lambda>n. (LINT x|lebesgue_on {-pi..pi}. Dirichlet_kernel n x * f x)
              - (LINT x|lebesgue_on {-pi..pi}. Dirichlet_kernel n x * (if x \<in> {-d..d} then f x else 0)))
           \<longlonglongrightarrow> 0"
  proof (rule Riemann_localization_integral [OF f _ \<open>0 < d\<close>])
    have "f absolutely_integrable_on {-d..d}"
      using f absolutely_integrable_on_subinterval \<open>d \<le> pi\<close> by fastforce
    moreover have "(\<lambda>x. if - pi \<le> x \<and> x \<le> pi then if x \<in> {-d..d} then f x else 0  else 0)
                 = (\<lambda>x. if x \<in> {-d..d} then f x else 0)"
      using \<open>d \<le> pi\<close> by force
    ultimately
    show "(\<lambda>x. if x \<in> {-d..d} then f x else 0) absolutely_integrable_on {-pi..pi}"
      apply (subst absolutely_integrable_restrict_UNIV [symmetric])
      apply (simp flip: absolutely_integrable_restrict_UNIV [of "{-d..d}" f])
      done
  qed auto
  then show ?thesis
    using integral_restrict [of "{-d..d}" "{-pi..pi}" "\<lambda>x. Dirichlet_kernel _ x * f x"] assms
    by (simp add: if_distrib cong: if_cong)
qed

lemma Riemann_localization:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and g: "g absolutely_integrable_on {-pi..pi}"
    and perf: "\<And>x. f(x + 2*pi) = f x"
    and perg: "\<And>x. g(x + 2*pi) = g x"
    and "d > 0" and d: "\<And>x. \<bar>x-t\<bar> < d \<Longrightarrow> f x = g x"
  shows "(\<lambda>n. \<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t) \<longlonglongrightarrow> c
     \<longleftrightarrow> (\<lambda>n. \<Sum>k\<le>n. Fourier_coefficient g k * trigonometric_set k t) \<longlonglongrightarrow> c"
proof -
  have "(\<lambda>n. LINT x|lebesgue_on {-pi..pi}. Dirichlet_kernel n x * f(x + t)) \<longlonglongrightarrow> pi * c
    \<longleftrightarrow> (\<lambda>n. LINT x|lebesgue_on {-pi..pi}. Dirichlet_kernel n x * g (x + t)) \<longlonglongrightarrow> pi * c"
  proof (intro Lim_transform_eq Riemann_localization_integral)
    show "(\<lambda>x. f(x + t)) absolutely_integrable_on {-pi..pi}" "(\<lambda>x. g (x + t)) absolutely_integrable_on {-pi..pi}"
      using assms by (auto intro: absolutely_integrable_periodic_offset)
  qed (use assms in auto)
  then show ?thesis
    by (simp add: Fourier_sum_limit_Dirichlet_kernel assms)
qed

subsection\<open>Localize the earlier integral\<close>

lemma Riemann_localization_integral_range_half:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and "0 < d" "d \<le> pi"
  shows "(\<lambda>n. (LINT x|lebesgue_on {0..pi}. Dirichlet_kernel n x * (f x + f(-x)))
            - (LINT x|lebesgue_on {0..d}. Dirichlet_kernel n x * (f x + f(-x)))) \<longlonglongrightarrow> 0"
proof -
  have *: "(\<lambda>x. Dirichlet_kernel n x * f x) absolutely_integrable_on {-d..d}" for n
    by (metis (full_types) absolutely_integrable_mult_Dirichlet_kernel absolutely_integrable_on_subinterval
              \<open>d \<le> pi\<close> atLeastatMost_subset_iff f neg_le_iff_le)
  show ?thesis
    using absolutely_integrable_mult_Dirichlet_kernel [OF f]
    using Riemann_localization_integral_range [OF assms]
    apply (simp add: "*" absolutely_integrable_imp_integrable integral_reflect_and_add)
    apply (simp add: algebra_simps)
    done
qed


lemma Fourier_sum_limit_Dirichlet_kernel_part:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
    and d: "0 < d" "d \<le> pi"
  shows "(\<lambda>n. \<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t) \<longlonglongrightarrow> l
     \<longleftrightarrow> (\<lambda>n. (LINT x|lebesgue_on {0..d}. Dirichlet_kernel n x * ((f(t+x) + f(t-x)) - 2*l))) \<longlonglongrightarrow> 0"
proof -
  have "(\<lambda>x. f(t+x)) absolutely_integrable_on {-pi..pi}"
    using absolutely_integrable_periodic_offset [OF f, of t] periodic by simp
  then have int: "(\<lambda>x. f(t+x) - l) absolutely_integrable_on {-pi..pi}"
    by auto
  have "(\<lambda>n. LINT x|lebesgue_on {0..pi}. Dirichlet_kernel n x * (f(t+x) + f(t-x) - 2*l)) \<longlonglongrightarrow> 0
    \<longleftrightarrow> (\<lambda>n. LINT x|lebesgue_on {0..d}. Dirichlet_kernel n x * (f(t+x) + f(t-x) - 2*l)) \<longlonglongrightarrow> 0"
    by (rule Lim_transform_eq) (use Riemann_localization_integral_range_half [OF int d] in auto)
  then show ?thesis
    by (simp add: Fourier_sum_limit_Dirichlet_kernel_half assms)
qed

subsection\<open>Make a harmless simplifying tweak to the Dirichlet kernel\<close>

lemma inte_Dirichlet_kernel_mul_expand:
  assumes f: "f \<in> borel_measurable (lebesgue_on S)" and S: "S \<in> sets lebesgue"
  shows "(LINT x|lebesgue_on S. Dirichlet_kernel n x * f x
        = LINT x|lebesgue_on S. sin((n+1/2) * x) * f x / (2 * sin(x/2)))
       \<and> (integrable (lebesgue_on S) (\<lambda>x. Dirichlet_kernel n x * f x)
      \<longleftrightarrow> integrable (lebesgue_on S) (\<lambda>x. sin((n+1/2) * x) * f x / (2 * sin(x/2))))"
proof (cases "0 \<in> S")
  case True
  have *: "{x. x = 0 \<and> x \<in> S} \<in> sets (lebesgue_on S)"
    using True  by (simp add: S sets_restrict_space_iff cong: conj_cong)
  have bm1: "(\<lambda>x. Dirichlet_kernel n x * f x) \<in> borel_measurable (lebesgue_on S)"
    unfolding Dirichlet_kernel_def
    by (force intro: * assms measurable continuous_imp_measurable_on_sets_lebesgue continuous_intros)
  have bm2: "(\<lambda>x. sin ((n + 1/2) * x) * f x / (2 * sin (x/2))) \<in> borel_measurable (lebesgue_on S)"
    by (intro assms measurable continuous_imp_measurable_on_sets_lebesgue continuous_intros) auto
  have 0: "{0} \<in> null_sets (lebesgue_on S)"
    using True by (simp add: S null_sets_restrict_space)
  show ?thesis
    apply (intro conjI integral_cong_AE integrable_cong_AE bm1 bm2 AE_I' [OF 0])
    unfolding Dirichlet_kernel_def  by auto
next
  case False
  then show ?thesis
    unfolding Dirichlet_kernel_def by (auto intro!: Bochner_Integration.integral_cong Bochner_Integration.integrable_cong)
qed

lemma
  assumes f: "f \<in> borel_measurable (lebesgue_on S)" and S: "S \<in> sets lebesgue"
  shows integral_Dirichlet_kernel_mul_expand:
        "(LINT x|lebesgue_on S. Dirichlet_kernel n x * f x)
       = (LINT x|lebesgue_on S. sin((n+1/2) * x) * f x / (2 * sin(x/2)))" (is "?th1")
  and integrable_Dirichlet_kernel_mul_expand:
       "integrable (lebesgue_on S) (\<lambda>x. Dirichlet_kernel n x * f x)
    \<longleftrightarrow> integrable (lebesgue_on S) (\<lambda>x. sin((n+1/2) * x) * f x / (2 * sin(x/2)))" (is "?th2")
  using inte_Dirichlet_kernel_mul_expand [OF assms] by auto


proposition Fourier_sum_limit_sine_part:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
    and d: "0 < d" "d \<le> pi"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> l
     \<longleftrightarrow> (\<lambda>n. LINT x|lebesgue_on {0..d}. sin((n + 1/2) * x) * ((f(t+x) + f(t-x) - 2*l) / x)) \<longlonglongrightarrow> 0"
    (is "?lhs \<longleftrightarrow> ?\<Psi> \<longlonglongrightarrow> 0")
proof -
  have ftx: "(\<lambda>x. f(t+x)) absolutely_integrable_on {-pi..pi}"
    using absolutely_integrable_periodic_offset assms by auto
  then have ftmx: "(\<lambda>x. f(t-x)) absolutely_integrable_on {-pi..pi}"
    by (simp flip: absolutely_integrable_reflect_real [where f= "(\<lambda>x. f(t+x))"])
  have fbm: "(\<lambda>x. f(t+x) + f(t-x) - 2*l) absolutely_integrable_on {-pi..pi}"
    by (force intro: ftmx ftx)
  let ?\<Phi> = "\<lambda>n. LINT x|lebesgue_on {0..d}. Dirichlet_kernel n x * ((f(t+x) + f(t-x)) - 2*l)"
  have "?lhs \<longleftrightarrow> ?\<Phi> \<longlonglongrightarrow> 0"
    by (intro Fourier_sum_limit_Dirichlet_kernel_part assms)
  moreover have "?\<Phi> \<longlonglongrightarrow> 0 \<longleftrightarrow> ?\<Psi> \<longlonglongrightarrow> 0"
  proof (rule Lim_transform_eq [OF Lim_transform_eventually])
    let ?f = "\<lambda>n. LINT x|lebesgue_on {0..d}. sin((real n + 1/2) * x) * (1 / (2 * sin(x/2)) - 1/x) * (f(t+x) + f(t-x) - 2*l)"
    have "?f n = (LINT x|lebesgue_on {-pi..pi}.
            sin ((n + 1/2) * x) * ((if x \<in> {0..d} then 1 / (2 * sin (x/2)) - 1/x else 0) * (f(t+x) + f(t-x) - 2*l)))" for n
      using d by (simp add: integral_restrict if_distrib [of "\<lambda>u. _ * (u * _)"] mult.assoc flip: atLeastAtMost_iff cong: if_cong)
    moreover have "\<dots> \<longlonglongrightarrow> 0"
    proof (intro Riemann_lebesgue_sin_half absolutely_integrable_bounded_measurable_product_real)
      have "(\<lambda>x. 1 / (2 * sin(x/2)) - 1/x) \<in> borel_measurable (lebesgue_on {0..d})"
        by (intro measurable continuous_imp_measurable_on_sets_lebesgue continuous_intros) auto
      then show "(\<lambda>x. if x \<in> {0..d} then 1 / (2 * sin(x/2)) - 1/x else 0) \<in> borel_measurable (lebesgue_on {-pi..pi})"
        using d by (simp add: borel_measurable_if_lebesgue_on flip: atLeastAtMost_iff)

      let ?g = "\<lambda>x::real. 1 / (2 * sin(x/2)) - 1/x"
      have limg: "(?g \<longlongrightarrow> ?g a) (at a within {0..d})"   \<comment>\<open>thanks to Manuel Eberl\<close>
        if a: "0 \<le> a" "a \<le> d" for a
      proof -
        have "(?g \<longlongrightarrow> 0) (at_right 0)" and "(?g \<longlongrightarrow> ?g d) (at_left d)"
          using d sin_gt_zero[of "d/2"] by (real_asymp simp: field_simps)+
        moreover have "(?g \<longlongrightarrow> ?g a) (at a)" if "a > 0"
          using a that d sin_gt_zero[of "a/2"] that by (real_asymp simp: field_simps)
        ultimately show ?thesis using that d
          by (cases "a = 0 \<or> a = d") (auto simp: at_within_Icc_at at_within_Icc_at_right at_within_Icc_at_left)
      qed
      have "((\<lambda>x. if x \<in> {0..d} then 1 / (2 * sin(x/2)) - 1/x else 0) ` {-pi..pi}) = ((\<lambda>x. 1 / (2 * sin(x/2)) - 1/x) ` {0..d})"
        using d  by (auto intro: image_eqI [where x=0])
      moreover have "bounded \<dots>"
        by (intro compact_imp_bounded compact_continuous_image) (auto simp: continuous_on limg)
      ultimately show "bounded ((\<lambda>x. if x \<in> {0..d} then 1 / (2 * sin(x/2)) - 1/x else 0) ` {-pi..pi})"
        by simp
    qed (auto simp: fbm)
    ultimately show "?f \<longlonglongrightarrow> (0::real)"
      by simp
    show "\<forall>\<^sub>F n in sequentially. ?f n = ?\<Phi> n - ?\<Psi> n"
    proof (rule eventually_sequentiallyI [where c = "Suc 0"])
      fix n
      assume "n \<ge> Suc 0"
      have "integrable (lebesgue_on {0..d}) (\<lambda>x. sin ((real n + 1/2) * x) * (f(t+x) + f(t-x) - 2*l) / (2 * sin(x/2)))"
        using d
        apply (subst integrable_Dirichlet_kernel_mul_expand [symmetric])
          apply (intro assms absolutely_integrable_imp_borel_measurable absolutely_integrable_on_subinterval [OF fbm]
                       absolutely_integrable_imp_integrable absolutely_integrable_mult_Dirichlet_kernel_reflected_part2 | force)+
        done
      moreover have "integrable (lebesgue_on {0..d}) (\<lambda>x. sin ((real n + 1/2) * x) * (f(t+x) + f(t-x) - 2*l) / x)"
      proof (rule integrable_cong_AE_imp)
        let ?g = "\<lambda>x. Dirichlet_kernel n x * (2 * sin(x/2) / x * (f(t+x) + f(t-x) - 2*l))"
        have *: "\<bar>2 * sin (x/2) / x\<bar> \<le> 1" for x::real
          using abs_sin_x_le_abs_x [of "x/2"]
          by (simp add: divide_simps mult.commute abs_mult)
        have "bounded ((\<lambda>x. 1 + (x/2)\<^sup>2) ` {-pi..pi})"
          by (intro compact_imp_bounded compact_continuous_image continuous_intros) auto
        then have bo: "bounded ((\<lambda>x. 2 * sin (x/2) / x) ` {-pi..pi})"
          using * unfolding bounded_real by blast
        show "integrable (lebesgue_on {0..d}) ?g"
          using d
          apply (intro absolutely_integrable_imp_integrable
              absolutely_integrable_on_subinterval [OF absolutely_integrable_mult_Dirichlet_kernel]
              absolutely_integrable_bounded_measurable_product_real bo fbm
              measurable continuous_imp_measurable_on_sets_lebesgue continuous_intros, auto)
          done
        show "(\<lambda>x. sin ((n + 1/2) * x) * (f(t+x) + f(t-x) - 2*l) / x) \<in> borel_measurable (lebesgue_on {0..d})"
          using d
          apply (intro measurable absolutely_integrable_imp_borel_measurable
                       absolutely_integrable_on_subinterval [OF ftx] absolutely_integrable_on_subinterval [OF ftmx]
                       absolutely_integrable_continuous_real continuous_intros, auto)
          done
        have "Dirichlet_kernel n x * (2 * sin(x/2)) / x = sin ((real n + 1/2) * x) / x"
          if "0 < x" "x \<le> d" for x
          using that d by (simp add: Dirichlet_kernel_def divide_simps sin_zero_pi_iff)
        then show "AE x in lebesgue_on {0..d}. ?g x = sin ((real n + 1/2) * x) * (f(t+x) + f(t-x) - 2*l) / x"
          using d by (force intro: AE_I' [where N="{0}"])
      qed
      ultimately have "?f n = (LINT x|lebesgue_on {0..d}. sin ((n + 1/2) * x) * (f(t+x) + f(t-x) - 2*l) / (2 * sin(x/2)))
                 - (LINT x|lebesgue_on {0..d}. sin ((n + 1/2) * x) * (f(t+x) + f(t-x) - 2*l) / x)"
        by (simp add: right_diff_distrib [of _ _ "1/_"] left_diff_distrib)
      also have "\<dots> = ?\<Phi> n - ?\<Psi> n"
        using d
        by (simp add: measurable_restrict_mono [OF absolutely_integrable_imp_borel_measurable [OF fbm]]
                      integral_Dirichlet_kernel_mul_expand)
      finally show "?f n = ?\<Phi> n - ?\<Psi> n" .
    qed
  qed
  ultimately show ?thesis
    by simp
qed


subsection\<open>Dini's test for the convergence of a Fourier series\<close>

proposition Fourier_Dini_test:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
    and int0d: "integrable (lebesgue_on {0..d}) (\<lambda>x. \<bar>f(t+x) + f(t-x) - 2*l\<bar> / x)"
    and "0 < d"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> l"
proof -
  define \<phi> where "\<phi> \<equiv> \<lambda>n x. sin((n + 1/2) * x) * ((f(t+x) + f(t-x) - 2*l) / x)"
  have "(\<lambda>n. LINT x|lebesgue_on {0..pi}. \<phi> n x) \<longlonglongrightarrow> 0"
    unfolding lim_sequentially dist_real_def
  proof (intro allI impI)
    fix e :: real
    assume "e > 0"
    define \<theta> where "\<theta> \<equiv> \<lambda>x. LINT x|lebesgue_on {0..x}. \<bar>f(t+x) + f(t-x) - 2*l\<bar> / x"
    have [simp]: "\<theta> 0 = 0"
      by (simp add: \<theta>_def integral_eq_zero_null_sets)
    have cont: "continuous_on {0..d} \<theta>"
      unfolding \<theta>_def using indefinite_integral_continuous_real int0d by blast
    with \<open>d > 0\<close>
    have "\<forall>e>0. \<exists>da>0. \<forall>x'\<in>{0..d}. \<bar>x' - 0\<bar> < da \<longrightarrow> \<bar>\<theta> x' - \<theta> 0\<bar> < e"
      by (force simp: continuous_on_real_range dest: bspec [where x=0])
    with \<open>e > 0\<close>
    obtain k where "k > 0" and k: "\<And>x'. \<lbrakk>0 \<le> x'; x' < k; x' \<le> d\<rbrakk> \<Longrightarrow> \<bar>\<theta> x'\<bar> < e/2"
      by (drule_tac x="e/2" in spec) auto
    define \<delta> where "\<delta> \<equiv> min d (min (k/2) pi)"
    have e2: "\<bar>\<theta> \<delta>\<bar> < e/2" and "\<delta> > 0" "\<delta> \<le> pi"
      unfolding \<delta>_def using k \<open>k > 0\<close> \<open>d > 0\<close> by auto
    have ftx: "(\<lambda>x. f(t+x)) absolutely_integrable_on {-pi..pi}"
      using absolutely_integrable_periodic_offset assms by auto
    then have ftmx: "(\<lambda>x. f(t-x)) absolutely_integrable_on {-pi..pi}"
      by (simp flip: absolutely_integrable_reflect_real [where f= "(\<lambda>x. f(t+x))"])
    have 1: "\<phi> n absolutely_integrable_on {0..\<delta>}" for n::nat
      unfolding \<phi>_def
    proof (rule absolutely_integrable_bounded_measurable_product_real)
      show "(\<lambda>x. sin ((real n + 1/2) * x)) \<in> borel_measurable (lebesgue_on {0..\<delta>})"
        by (intro continuous_imp_measurable_on_sets_lebesgue continuous_intros) auto
      show "bounded ((\<lambda>x. sin ((real n + 1/2) * x)) ` {0..\<delta>})"
        by (simp add: bounded_iff) (use abs_sin_le_one in blast)
      have "(\<lambda>x. (f(t+x) + f(t-x) - 2*l) / x) \<in> borel_measurable (lebesgue_on {0..\<delta>})"
        using \<open>d > 0\<close> unfolding \<delta>_def
        by (intro measurable absolutely_integrable_imp_borel_measurable
            absolutely_integrable_on_subinterval [OF ftx] absolutely_integrable_on_subinterval [OF ftmx]
            absolutely_integrable_continuous_real continuous_intros, auto)
      moreover have "integrable (lebesgue_on {0..\<delta>}) (norm \<circ> (\<lambda>x. (f(t+x) + f(t-x) - 2*l) / x))"
      proof (rule integrable_subinterval [of 0 d])
        show "integrable (lebesgue_on {0..d}) (norm \<circ> (\<lambda>x. (f(t+x) + f(t-x) - 2*l) / x))"
          using int0d by (subst integrable_cong) (auto simp: o_def)
        show "{0..\<delta>} \<subseteq> {0..d}"
          using \<open>d > 0\<close> by (auto simp: \<delta>_def)
      qed
      ultimately show "(\<lambda>x. (f(t+x) + f(t-x) - 2*l) / x) absolutely_integrable_on {0..\<delta>}"
        by (auto simp: absolutely_integrable_measurable)
    qed auto
    have 2: "\<phi> n absolutely_integrable_on {\<delta>..pi}" for n::nat
      unfolding \<phi>_def
    proof (rule absolutely_integrable_bounded_measurable_product_real)
      show "(\<lambda>x. sin ((n + 1/2) * x)) \<in> borel_measurable (lebesgue_on {\<delta>..pi})"
        by (intro continuous_imp_measurable_on_sets_lebesgue continuous_intros) auto
      show "bounded ((\<lambda>x. sin ((n + 1/2) * x)) ` {\<delta>..pi})"
        by (simp add: bounded_iff) (use abs_sin_le_one in blast)
    have "(\<lambda>x. inverse x * (f(t+x) + f(t-x) - 2*l)) absolutely_integrable_on {\<delta>..pi}"
    proof (rule absolutely_integrable_bounded_measurable_product_real)
      have "(\<lambda>x. 1/x) \<in> borel_measurable (lebesgue_on {\<delta>..pi})"
        by (auto simp: measurable_completion measurable_restrict_space1)
      then show "inverse \<in> borel_measurable (lebesgue_on {\<delta>..pi})"
        by (metis (no_types, lifting) inverse_eq_divide measurable_lebesgue_cong)
      have "\<forall>x\<in>{\<delta>..pi}. inverse \<bar>x\<bar> \<le> inverse \<delta>"
        using \<open>0 < \<delta>\<close> by auto
      then show "bounded (inverse ` {\<delta>..pi})"
        by (auto simp: bounded_iff)
      show "(\<lambda>x. f(t+x) + f(t-x) - 2*l) absolutely_integrable_on {\<delta>..pi}"
      proof (rule absolutely_integrable_on_subinterval)
        show "(\<lambda>x. (f(t+x) + f(t-x) - 2*l)) absolutely_integrable_on {-pi..pi}"
          by (fast intro: ftx ftmx absolutely_integrable_on_const)
        show "{\<delta>..pi} \<subseteq> {-pi..pi}"
          using \<open>0 < \<delta>\<close> by auto
      qed
    qed auto
    then show "(\<lambda>x. (f(t+x) + f(t-x) - 2*l) / x) absolutely_integrable_on {\<delta>..pi}"
      by (metis (no_types, lifting) divide_inverse mult.commute set_integrable_cong)
  qed auto
  have "(\<lambda>x. f(t+x) - l) absolutely_integrable_on {-pi..pi}"
    using ftx by auto
  moreover have "bounded ((\<lambda>x. 0) ` {x. \<bar>x\<bar> < \<delta>})"
    using bounded_def by blast
  moreover have "bounded (inverse ` {x. \<not> \<bar>x\<bar> < \<delta>})"
    using \<open>\<delta> > 0\<close> by (auto simp: divide_simps intro: boundedI [where B = "1/\<delta>"])
  ultimately have "(\<lambda>x. (if \<bar>x\<bar> < \<delta> then 0 else inverse x) * (if x \<in> {-pi..pi} then f(t+x) - l else 0)) absolutely_integrable_on UNIV"
    apply (intro absolutely_integrable_bounded_measurable_product_real measurable set_integral_diff)
          apply (auto simp: lebesgue_on_UNIV_eq measurable_completion simp flip: absolutely_integrable_restrict_UNIV [where S = "{-pi..pi}"])
    done
  moreover have "(if x \<in> {-pi..pi} then if \<bar>x\<bar> < \<delta> then 0 else (f(t+x) - l) / x else 0)
               = (if \<bar>x\<bar> < \<delta> then 0 else inverse x) * (if x \<in> {-pi..pi} then f(t+x) - l else 0)"  for x
    by (auto simp: divide_simps)
  ultimately have *: "(\<lambda>x. if \<bar>x\<bar> < \<delta> then 0 else (f(t+x) - l) / x) absolutely_integrable_on {-pi..pi}"
    by (simp add: flip: absolutely_integrable_restrict_UNIV [where S = "{-pi..pi}"])
  have "(\<lambda>n. LINT x|lebesgue_on {0..pi}. sin ((n + 1/2) * x) * (if \<bar>x\<bar> < \<delta> then 0 else (f(t+x) - l) / x)
                                       + sin ((n + 1/2) * -x) * (if \<bar>x\<bar> < \<delta> then 0 else (f(t-x) - l) / -x))
        \<longlonglongrightarrow> 0"
    using Riemann_lebesgue_sin_half [OF *] *
    by (simp add: integral_reflect_and_add absolutely_integrable_imp_integrable absolutely_integrable_sin_product cong: if_cong)
  moreover have "sin ((n + 1/2) * x) * (if \<bar>x\<bar> < \<delta> then 0 else (f(t+x) - l) / x)
               + sin ((n + 1/2) * -x) * (if \<bar>x\<bar> < \<delta> then 0 else (f(t-x) - l) / -x)
           = (if \<not> \<bar>x\<bar> < \<delta> then \<phi> n x else 0)" for x n
    by simp (auto simp: divide_simps algebra_simps \<phi>_def)
  ultimately have "(\<lambda>n. LINT x|lebesgue_on {0..pi}. (if \<not> \<bar>x\<bar> < \<delta> then \<phi> n x else 0)) \<longlonglongrightarrow> 0"
    by simp
  moreover have "(if 0 \<le> x \<and> x \<le> pi then if \<not> \<bar>x\<bar> < \<delta> then \<phi> n x else 0 else 0)
               = (if \<delta> \<le> x \<and> x \<le> pi then \<phi> n x else 0)" for x n
    using \<open>\<delta> > 0\<close> by auto
  ultimately have \<dagger>: "(\<lambda>n. LINT x|lebesgue_on {\<delta>..pi}. \<phi> n x) \<longlonglongrightarrow> 0"
    by (simp flip: Lebesgue_Measure.integral_restrict_UNIV)
  then obtain N::nat where N: "\<And>n. n\<ge>N \<Longrightarrow> \<bar>LINT x|lebesgue_on {\<delta>..pi}. \<phi> n x\<bar> < e/2"
    unfolding lim_sequentially dist_real_def
    by (metis (full_types) \<open>0 < e\<close> diff_zero half_gt_zero_iff)
  have "\<bar>integral\<^sup>L (lebesgue_on {0..pi}) (\<phi> n)\<bar> < e" if "n \<ge> N" for n::nat
  proof -
    have int: "integrable (lebesgue_on {0..pi}) (\<phi> (real n))"
      by (intro integrable_combine [of concl: 0 pi] absolutely_integrable_imp_integrable) (use  \<open>\<delta> > 0\<close>  \<open>\<delta> \<le> pi\<close> 1 2 in auto)
    then have "integral\<^sup>L (lebesgue_on {0..pi}) (\<phi> n) = integral\<^sup>L (lebesgue_on {0..\<delta>}) (\<phi> n) + integral\<^sup>L (lebesgue_on {\<delta>..pi}) (\<phi> n)"
      by (rule integral_combine) (use \<open>0 < \<delta>\<close> \<open>\<delta> \<le> pi\<close> in auto)
    moreover have "\<bar>integral\<^sup>L (lebesgue_on {0..\<delta>}) (\<phi> n)\<bar> \<le> LINT x|lebesgue_on {0..\<delta>}. \<bar>f(t + x) + f(t - x) - 2 * l\<bar> / x"
    proof (rule integral_abs_bound_integral)
      show "integrable (lebesgue_on {0..\<delta>}) (\<phi> (real n))"
        by (meson integrable_subinterval \<open>\<delta> \<le> pi\<close> int atLeastatMost_subset_iff order_refl)
      have "{0..\<delta>} \<subseteq> {0..d}"
        by (auto simp: \<delta>_def)
      then show "integrable (lebesgue_on {0..\<delta>}) (\<lambda>x. \<bar>f(t + x) + f(t - x) - 2 * l\<bar> / x)"
        by (rule integrable_subinterval [OF int0d])
      show "\<bar>\<phi> (real n) x\<bar> \<le> \<bar>f(t + x) + f(t - x) - 2 * l\<bar> / x"
        if "x \<in> space (lebesgue_on {0..\<delta>})" for x
        using that
        apply (auto simp: \<phi>_def divide_simps abs_mult)
        by (simp add: mult.commute mult_left_le)
    qed
    ultimately have "\<bar>integral\<^sup>L (lebesgue_on {0..pi}) (\<phi> n)\<bar> < e/2 + e/2"
      using N [OF that] e2 unfolding \<theta>_def by linarith
    then show ?thesis
      by simp
  qed
  then show "\<exists>N. \<forall>n\<ge>N. \<bar>integral\<^sup>L (lebesgue_on {0..pi}) (\<phi> (real n)) - 0\<bar> < e"
    by force
qed
  then show ?thesis
    unfolding \<phi>_def using Fourier_sum_limit_sine_part assms pi_gt_zero by blast
qed


subsection\<open>Cesaro summability of Fourier series using Fejér kernel\<close>

definition Fejer_kernel :: "nat \<Rightarrow> real \<Rightarrow> real"
  where
  "Fejer_kernel \<equiv> \<lambda>n x. if n = 0 then 0 else (\<Sum>r<n. Dirichlet_kernel r x) / n"

lemma Fejer_kernel:
     "Fejer_kernel n x =
        (if n = 0 then 0
         else if x = 0 then n/2
         else sin(n / 2 * x) ^ 2 / (2 * n * sin(x/2) ^ 2))"
proof (cases "x=0 \<or> sin(x/2) = 0")
  case True
  have "(\<Sum>r<n. (1 + real r * 2)) = real n * real n"
    by (induction n) (auto simp: algebra_simps)
  with True show ?thesis
    by (auto simp: Fejer_kernel_def Dirichlet_kernel_def field_simps simp flip: sum_divide_distrib)
next
  case False
  have "sin (x/2) * (\<Sum>r<n. sin ((real r * 2 + 1) * x / 2)) =
        sin (real n * x / 2) * sin (real n * x / 2)"
  proof (induction n)
  next
    case (Suc n)
    then show ?case
      apply (simp add: field_simps sin_times_sin)
      apply (simp add: add_divide_distrib)
      done
  qed auto
  then show ?thesis
    using False
    unfolding Fejer_kernel_def Dirichlet_kernel_def
    by (simp add: divide_simps power2_eq_square mult.commute flip: sum_divide_distrib)
qed

lemma Fejer_kernel_0 [simp]: "Fejer_kernel 0 x = 0"  "Fejer_kernel n 0 = n/2"
  by (auto simp: Fejer_kernel)

lemma Fejer_kernel_continuous_strong:
  "continuous_on {-(2 * pi)<..<2 * pi} (Fejer_kernel n)"
proof (cases "n=0")
  case False
  then show ?thesis
  by (simp add: Fejer_kernel_def continuous_intros Dirichlet_kernel_continuous_strong)
qed (simp add: Fejer_kernel_def)

lemma Fejer_kernel_continuous:
  "continuous_on {-pi..pi} (Fejer_kernel n)"
  apply (rule continuous_on_subset [OF Fejer_kernel_continuous_strong])
  apply (simp add: subset_iff)
  using pi_gt_zero apply linarith
  done


lemma absolutely_integrable_mult_Fejer_kernel:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>x. Fejer_kernel n x * f x) absolutely_integrable_on {-pi..pi}"
proof (rule absolutely_integrable_bounded_measurable_product_real)
  show "Fejer_kernel n \<in> borel_measurable (lebesgue_on {-pi..pi})"
    by (simp add: Fejer_kernel_continuous continuous_imp_measurable_on_sets_lebesgue)
  show "bounded (Fejer_kernel n ` {-pi..pi})"
    using Fejer_kernel_continuous compact_continuous_image compact_imp_bounded by blast
qed (use assms in auto)


lemma absolutely_integrable_mult_Fejer_kernel_reflected1:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>x. Fejer_kernel n x * f(t + x)) absolutely_integrable_on {-pi..pi}"
  using assms
  by (force intro: absolutely_integrable_mult_Fejer_kernel absolutely_integrable_periodic_offset)

lemma absolutely_integrable_mult_Fejer_kernel_reflected2:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>x. Fejer_kernel n x * f(t - x)) absolutely_integrable_on {-pi..pi}"
proof -
  have "(\<lambda>x. f(t - x)) absolutely_integrable_on {-pi..pi}"
    using assms
    apply (subst absolutely_integrable_reflect_real [symmetric])
    apply (simp add: absolutely_integrable_periodic_offset)
    done
  then show ?thesis
    by (rule absolutely_integrable_mult_Fejer_kernel)
qed

lemma absolutely_integrable_mult_Fejer_kernel_reflected3:
  shows "(\<lambda>x. Fejer_kernel n x * c) absolutely_integrable_on {-pi..pi}"
  using absolutely_integrable_on_const absolutely_integrable_mult_Fejer_kernel by blast


lemma absolutely_integrable_mult_Fejer_kernel_reflected_part1:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "d \<le> pi"
  shows "(\<lambda>x. Fejer_kernel n x * f(t + x)) absolutely_integrable_on {0..d}"
  by (rule absolutely_integrable_on_subinterval [OF absolutely_integrable_mult_Fejer_kernel_reflected1]) (auto simp: assms)

lemma absolutely_integrable_mult_Fejer_kernel_reflected_part2:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "d \<le> pi"
  shows "(\<lambda>x. Fejer_kernel n x * f(t - x)) absolutely_integrable_on {0..d}"
  by (rule absolutely_integrable_on_subinterval [OF absolutely_integrable_mult_Fejer_kernel_reflected2]) (auto simp: assms)

lemma absolutely_integrable_mult_Fejer_kernel_reflected_part3:
  assumes "d \<le> pi"
  shows "(\<lambda>x. Fejer_kernel n x * c) absolutely_integrable_on {0..d}"
  by (rule absolutely_integrable_on_subinterval [OF absolutely_integrable_mult_Fejer_kernel_reflected2]) (auto simp: assms)

lemma absolutely_integrable_mult_Fejer_kernel_reflected_part4:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "d \<le> pi"
  shows "(\<lambda>x. Fejer_kernel n x * (f(t + x) + f(t - x))) absolutely_integrable_on {0..d}"
  unfolding distrib_left
  by (intro set_integral_add absolutely_integrable_mult_Fejer_kernel_reflected_part1 absolutely_integrable_mult_Fejer_kernel_reflected_part2 assms)

lemma absolutely_integrable_mult_Fejer_kernel_reflected_part5:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "d \<le> pi"
  shows "(\<lambda>x. Fejer_kernel n x * ((f(t + x) + f(t - x)) - c)) absolutely_integrable_on {0..d}"
  unfolding distrib_left right_diff_distrib
  by (intro set_integral_add set_integral_diff absolutely_integrable_on_const
      absolutely_integrable_mult_Fejer_kernel_reflected_part1 absolutely_integrable_mult_Fejer_kernel_reflected_part2 assms, auto)


lemma Fourier_sum_offset_Fejer_kernel_half:
  fixes n::nat
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "n > 0"
  shows "(\<Sum>r<n. \<Sum>k\<le>2*r. Fourier_coefficient f k * trigonometric_set k t) / n - l
       = (LINT x|lebesgue_on {0..pi}. Fejer_kernel n x * (f(t + x) + f(t - x) - 2 * l)) / pi"
proof -
  have "(\<Sum>r<n. \<Sum>k\<le>2 * r. Fourier_coefficient f k * trigonometric_set k t) - real n * l
       = (\<Sum>r<n. (\<Sum>k\<le>2 * r. Fourier_coefficient f k * trigonometric_set k t) - l)"
    by (simp add: sum_subtractf)
  also have "\<dots> = (\<Sum>r<n.
                      (LINT x|lebesgue_on {0..pi}. Dirichlet_kernel r x * (f(t + x) + f(t - x) - 2 * l)) / pi)"
    by (simp add: Fourier_sum_offset_Dirichlet_kernel_half assms)
  also have "\<dots> = real n * ((LINT x|lebesgue_on {0..pi}. Fejer_kernel n x * (f(t + x) + f(t - x) - 2 * l)) / pi)"
  proof -
    have "integrable (lebesgue_on {0..pi}) (\<lambda>x. Dirichlet_kernel i x * (f(t + x) + f(t - x) - 2 * l))" for i
      using absolutely_integrable_mult_Dirichlet_kernel_reflected_part2(2) f periodic
      by (force simp: intro!: absolutely_integrable_imp_integrable)
    then show ?thesis
      using \<open>n > 0\<close>
      apply (simp add: Fejer_kernel_def flip: sum_divide_distrib)
      apply (simp add: sum_distrib_right flip: Bochner_Integration.integral_sum [symmetric])
      done
  qed
  finally have "(\<Sum>r<n. \<Sum>k\<le>2 * r. Fourier_coefficient f k * trigonometric_set k t) - real n * l = real n * ((LINT x|lebesgue_on {0..pi}. Fejer_kernel n x * (f(t + x) + f(t - x) - 2 * l)) / pi)" .
  with \<open>n > 0\<close> show ?thesis
    by (auto simp: mult.commute divide_simps)
qed


lemma Fourier_sum_limit_Fejer_kernel_half:
  fixes n::nat
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. ((\<Sum>r<n. \<Sum>k\<le>2*r. Fourier_coefficient f k * trigonometric_set k t)) / n) \<longlonglongrightarrow> l
         \<longleftrightarrow>
         ((\<lambda>n. integral\<^sup>L (lebesgue_on {0..pi}) (\<lambda>x. Fejer_kernel n x * ((f(t + x) + f(t - x)) - 2*l)))  \<longlonglongrightarrow> 0)"
        (is "?lhs = ?rhs")
proof -
  have "?lhs \<longleftrightarrow>
        (\<lambda>n. ((\<Sum>r<n. \<Sum>k\<le>2*r.  Fourier_coefficient f k * trigonometric_set k t)) / n - l) \<longlonglongrightarrow> 0"
    by (simp add: LIM_zero_iff)
  also have "\<dots> \<longleftrightarrow>
        (\<lambda>n. ((((\<Sum>r<n. \<Sum>k\<le>2*r.  Fourier_coefficient f k * trigonometric_set k t)) / n) - l) * pi) \<longlonglongrightarrow> 0"
    using tendsto_mult_right_iff [OF pi_neq_zero] by simp
  also have "\<dots> \<longleftrightarrow> ?rhs"
    apply (intro Lim_transform_eq [OF Lim_transform_eventually [of "\<lambda>n. 0"]] eventually_sequentiallyI [of 1])
    apply (simp_all add: Fourier_sum_offset_Fejer_kernel_half assms)
    done
  finally show ?thesis .
qed


lemma has_integral_Fejer_kernel:
  "has_bochner_integral (lebesgue_on {-pi..pi}) (Fejer_kernel n) (if n = 0 then 0 else pi)"
proof -
  have "has_bochner_integral (lebesgue_on {-pi..pi}) (\<lambda>x. (\<Sum>r<n. Dirichlet_kernel r x) / real n) ((\<Sum>r<n. pi) / n)"
    by (simp add: has_bochner_integral_iff integrable_Dirichlet_kernel has_bochner_integral_divide has_bochner_integral_sum)
  then show ?thesis
    by (auto simp: Fejer_kernel_def)
qed

lemma has_integral_Fejer_kernel_half:
  "has_bochner_integral (lebesgue_on {0..pi}) (Fejer_kernel n) (if n = 0 then 0 else pi/2)"
proof -
  have "has_bochner_integral (lebesgue_on {0..pi}) (\<lambda>x. (\<Sum>r<n. Dirichlet_kernel r x) / real n) ((\<Sum>r<n. pi/2) / n)"
    apply (intro has_bochner_integral_sum has_bochner_integral_divide)
    using not_integrable_integral_eq by (force simp: has_bochner_integral_iff)
  then show ?thesis
    by (auto simp: Fejer_kernel_def)
qed

lemma Fejer_kernel_pos_le [simp]: "Fejer_kernel n x \<ge> 0"
  by (simp add: Fejer_kernel)


theorem Fourier_Fejer_Cesaro_summable:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
    and fl: "(f \<longlongrightarrow> l) (at t within atMost t)"
    and fr: "(f \<longlongrightarrow> r) (at t within atLeast t)"
  shows "(\<lambda>n. (\<Sum>m<n. \<Sum>k\<le>2*m. Fourier_coefficient f k * trigonometric_set k t) / n) \<longlonglongrightarrow> (l+r) / 2"
proof -
  define h where "h \<equiv> \<lambda>u. (f(t+u) + f(t-u)) - (l+r)"
  have "(\<lambda>n. LINT u|lebesgue_on {0..pi}. Fejer_kernel n u * h u) \<longlonglongrightarrow> 0"
  proof -
    have h0: "(h \<longlongrightarrow> 0) (at 0 within atLeast 0)"
    proof -
      have l0: "((\<lambda>u. f(t-u) - l) \<longlongrightarrow> 0) (at 0 within {0..})"
        using fl
        unfolding Lim_within
        apply (elim all_forward imp_forward ex_forward conj_forward asm_rl, clarify)
        apply (drule_tac x="t-x" in bspec)
         apply (auto simp: dist_norm)
        done
      have r0: "((\<lambda>u. f(t + u) - r) \<longlongrightarrow> 0) (at 0 within {0..})"
        using fr
        unfolding Lim_within
        apply (elim all_forward imp_forward ex_forward conj_forward asm_rl, clarify)
        apply (drule_tac x="t+x" in bspec)
         apply (auto simp: dist_norm)
        done
      show ?thesis
        using tendsto_add [OF l0 r0] by (simp add: h_def algebra_simps)
    qed
    show ?thesis
      unfolding lim_sequentially dist_real_def diff_0_right
    proof clarify
      fix e::real
      assume "e > 0"
      then obtain x' where "0 < x'" "\<And>x. \<lbrakk>0 < x; x < x'\<rbrakk> \<Longrightarrow> \<bar>h x\<bar> < e / (2 * pi)"
        using h0 unfolding Lim_within dist_real_def
        by (auto simp: dest: spec [where x="e/2/pi"])
      then obtain \<xi> where "0 < \<xi>" "\<xi> < pi" and \<xi>: "\<And>x. 0 < x \<and> x \<le> \<xi> \<Longrightarrow> \<bar>h x\<bar> < e/2/pi"
        apply (intro that [where \<xi>="min x' pi/2"], auto)
        using m2pi_less_pi by linarith
      have ftx: "(\<lambda>x. f(t+x)) absolutely_integrable_on {-pi..pi}"
        using absolutely_integrable_periodic_offset assms by auto
      then have ftmx: "(\<lambda>x. f(t-x)) absolutely_integrable_on {-pi..pi}"
        by (simp flip: absolutely_integrable_reflect_real [where f= "(\<lambda>x. f(t+x))"])
      have h_aint: "h absolutely_integrable_on {-pi..pi}"
        unfolding h_def
        by (intro absolutely_integrable_on_const set_integral_diff set_integral_add, auto simp: ftx ftmx)
      have "(\<lambda>n. LINT x|lebesgue_on {\<xi>..pi}. Fejer_kernel n x * h x) \<longlonglongrightarrow> 0"
      proof (rule Lim_null_comparison)
        define \<phi> where "\<phi> \<equiv> \<lambda>n. (LINT x|lebesgue_on {\<xi>..pi}. \<bar>h x\<bar> / (2 * sin(x/2) ^ 2)) / n"
        show "\<forall>\<^sub>F n in sequentially. norm (LINT x|lebesgue_on {\<xi>..pi}. Fejer_kernel n x * h x) \<le> \<phi> n"
        proof (rule eventually_sequentiallyI)
          fix n::nat assume "n \<ge> 1"
          have hint: "(\<lambda>x. h x / (2 * sin(x/2) ^ 2)) absolutely_integrable_on {\<xi>..pi}"
            unfolding divide_inverse mult.commute [of "h _"]
          proof (rule absolutely_integrable_bounded_measurable_product_real)
            have cont: "continuous_on {\<xi>..pi} (\<lambda>x. inverse (2 * (sin (x * inverse 2))\<^sup>2))"
              using \<open>0 < \<xi>\<close> by (intro continuous_intros) (auto simp: sin_zero_pi_iff)
            show "(\<lambda>x. inverse (2 * (sin (x * inverse 2))\<^sup>2)) \<in> borel_measurable (lebesgue_on {\<xi>..pi})"
              using \<open>0 < \<xi>\<close>
              by (intro cont continuous_imp_measurable_on_sets_lebesgue) auto
            show "bounded ((\<lambda>x. inverse (2 * (sin (x * inverse 2))\<^sup>2)) ` {\<xi>..pi})"
              using cont by (simp add: compact_continuous_image compact_imp_bounded)
            show "h absolutely_integrable_on {\<xi>..pi}"
              using \<open>0 < \<xi>\<close> \<open>\<xi> < pi\<close> by (auto intro: absolutely_integrable_on_subinterval [OF h_aint])
          qed auto
          then have *: "integrable (lebesgue_on {\<xi>..pi}) (\<lambda>x. \<bar>h x\<bar> / (2 * (sin (x/2))\<^sup>2))"
            by (simp add: absolutely_integrable_measurable o_def)
          define \<psi> where
              "\<psi> \<equiv> \<lambda>x. (if n = 0 then 0 else if x = 0 then n/2
                         else (sin (real n / 2 * x))\<^sup>2 / (2 * real n * (sin (x/2))\<^sup>2)) * h x"
          have "\<bar>LINT x|lebesgue_on {\<xi>..pi}. \<psi> x\<bar>
              \<le> (LINT x|lebesgue_on {\<xi>..pi}. \<bar>h x\<bar> / (2 * (sin (x/2))\<^sup>2) / n)"
          proof (rule integral_abs_bound_integral)
            show **: "integrable (lebesgue_on {\<xi>..pi}) (\<lambda>x. \<bar>h x\<bar> / (2 * (sin (x/2))\<^sup>2) / n)"
              using Bochner_Integration.integrable_mult_left [OF *, of "1/n"]
              by (simp add: field_simps)
            show \<dagger>: "\<bar>\<psi> x\<bar> \<le> \<bar>h x\<bar> / (2 * (sin (x/2))\<^sup>2) / real n"
              if "x \<in> space (lebesgue_on {\<xi>..pi})" for x
              using that \<open>0 < \<xi>\<close>
              apply (simp add: \<psi>_def divide_simps mult_less_0_iff abs_mult)
              apply (auto simp: square_le_1 mult_left_le_one_le)
              done
            show "integrable (lebesgue_on {\<xi>..pi}) \<psi>"
            proof (rule measurable_bounded_by_integrable_imp_lebesgue_integrable [OF _ **])
              let ?g = "\<lambda>x. \<bar>h x\<bar> / (2 * sin(x/2) ^ 2) / n"
              have ***: "integrable (lebesgue_on {\<xi>..pi}) (\<lambda>x. (sin (n/2 * x))\<^sup>2 * (inverse (2 * (sin (x/2))\<^sup>2) * h x))"
              proof (rule absolutely_integrable_imp_integrable [OF absolutely_integrable_bounded_measurable_product_real])
                show "(\<lambda>x. (sin (real n / 2 * x))\<^sup>2) \<in> borel_measurable (lebesgue_on {\<xi>..pi})"
                  by (intro continuous_imp_measurable_on_sets_lebesgue continuous_intros) auto
                show "bounded ((\<lambda>x. (sin (real n / 2 * x))\<^sup>2) ` {\<xi>..pi})"
                  by (force simp: square_le_1 intro: boundedI [where B=1])
                show "(\<lambda>x. inverse (2 * (sin (x/2))\<^sup>2) * h x) absolutely_integrable_on {\<xi>..pi}"
                  using hint by (simp add: divide_simps)
              qed auto
              show "\<psi> \<in> borel_measurable (lebesgue_on {\<xi>..pi})"
                apply (rule borel_measurable_integrable)
                apply (rule integrable_cong [where f = "\<lambda>x. sin(n / 2 * x) ^ 2 / (2 * n * sin(x/2) ^ 2) * h x", OF refl, THEN iffD1])
                using \<open>0 < \<xi>\<close> **
                 apply (force simp: \<psi>_def divide_simps algebra_simps mult_less_0_iff abs_mult)
                using Bochner_Integration.integrable_mult_left [OF ***, of "1/n"]
                by (simp add: field_simps)
              show "norm (\<psi> x) \<le> ?g x" if "x \<in> {\<xi>..pi}" for x
                using that \<dagger> by (simp add: \<psi>_def)
            qed auto
          qed
          then show "norm (LINT x|lebesgue_on {\<xi>..pi}. Fejer_kernel n x * h x) \<le> \<phi> n"
            by (simp add: Fejer_kernel \<phi>_def \<psi>_def flip: Bochner_Integration.integral_divide [OF *])
        qed
        show "\<phi> \<longlonglongrightarrow> 0"
          unfolding \<phi>_def divide_inverse
          by (simp add: tendsto_mult_right_zero lim_inverse_n)
      qed
      then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> \<bar>LINT x|lebesgue_on {\<xi>..pi}. Fejer_kernel n x * h x\<bar> < e/2"
        unfolding lim_sequentially by (metis half_gt_zero_iff norm_conv_dist real_norm_def \<open>e > 0\<close>)
      show "\<exists>N. \<forall>n\<ge>N. \<bar>(LINT u|lebesgue_on {0..pi}. Fejer_kernel n u * h u)\<bar> < e"
      proof (intro exI allI impI)
        fix n :: nat
        assume n: "n \<ge> max 1 N"
        with N have 1: "\<bar>LINT x|lebesgue_on {\<xi>..pi}. Fejer_kernel n x * h x\<bar> < e/2"
          by simp
        have "integral\<^sup>L (lebesgue_on {0..\<xi>}) (Fejer_kernel n) \<le> integral\<^sup>L (lebesgue_on {0..pi}) (Fejer_kernel n)"
         using \<open>\<xi> < pi\<close> has_bochner_integral_iff has_integral_Fejer_kernel_half
         by (force intro!: integral_mono_lebesgue_on_AE)
        also have "\<dots> \<le> pi"
          using has_integral_Fejer_kernel_half by (simp add: has_bochner_integral_iff)
        finally have int_le_pi: "integral\<^sup>L (lebesgue_on {0..\<xi>}) (Fejer_kernel n) \<le> pi" .
        have 2: "\<bar>LINT x|lebesgue_on {0..\<xi>}. Fejer_kernel n x * h x\<bar> \<le> (LINT x|lebesgue_on {0..\<xi>}. Fejer_kernel n x * e/2/pi)"
        proof -
          have eq: "integral\<^sup>L (lebesgue_on {0..\<xi>}) (\<lambda>x. Fejer_kernel n x * h x)
                  = integral\<^sup>L (lebesgue_on {0..\<xi>}) (\<lambda>x. Fejer_kernel n x * (if x = 0 then 0 else h x))"
          proof (rule integral_cong_AE)
            have \<dagger>: "{u. u \<noteq> 0 \<longrightarrow> P u} \<inter> {0..\<xi>} = {0} \<union> Collect P \<inter> {0..\<xi>}"
              "{u. u \<noteq> 0 \<and> P u} \<inter> {0..\<xi>} = (Collect P \<inter> {0..\<xi>}) - {0}" for P
              using \<open>0 < \<xi>\<close> by auto
            have *: "- {0} \<inter> A \<inter> {0..\<xi>} = A \<inter> {0..\<xi>} - {0}" for A
              by auto
            show "(\<lambda>x. Fejer_kernel n x * h x) \<in> borel_measurable (lebesgue_on {0..\<xi>})"
              using \<open>\<xi> < pi\<close>
              by (intro absolutely_integrable_imp_borel_measurable h_aint
                  absolutely_integrable_on_subinterval [OF absolutely_integrable_mult_Fejer_kernel], auto)
            then show "(\<lambda>x. Fejer_kernel n x * (if x = 0 then 0 else h x)) \<in> borel_measurable (lebesgue_on {0..\<xi>})"
              apply (simp add: in_borel_measurable Ball_def vimage_def Collect_conj_eq Collect_imp_eq * flip: Collect_neg_eq)
              apply (elim all_forward imp_forward asm_rl)
              using \<open>0 < \<xi>\<close>
              apply (auto simp: \<dagger> sets.insert_in_sets sets_restrict_space_iff cong: conj_cong)
              done
            have 0: "{0} \<in> null_sets (lebesgue_on {0..\<xi>})"
              using \<open>0 < \<xi>\<close> by (simp add: null_sets_restrict_space)
            then show "AE x in lebesgue_on {0..\<xi>}. Fejer_kernel n x * h x = Fejer_kernel n x * (if x = 0 then 0 else h x)"
              by (auto intro: AE_I' [OF 0])
          qed
          show ?thesis
            unfolding eq
          proof (rule integral_abs_bound_integral)
            have "(\<lambda>x. if x = 0 then 0 else h x) absolutely_integrable_on {- pi..pi}"
            proof (rule absolutely_integrable_spike [OF h_aint])
              show "negligible {0}"
                by auto
            qed auto
            with \<open>0 < \<xi>\<close> \<open>\<xi> < pi\<close> show "integrable (lebesgue_on {0..\<xi>}) (\<lambda>x. Fejer_kernel n x * (if x = 0 then 0 else h x))"
              by (intro absolutely_integrable_imp_integrable h_aint absolutely_integrable_on_subinterval [OF absolutely_integrable_mult_Fejer_kernel]) auto
            show "integrable (lebesgue_on {0..\<xi>}) (\<lambda>x. Fejer_kernel n x * e / 2 / pi)"
              by (simp add: absolutely_integrable_imp_integrable \<open>\<xi> < pi\<close> absolutely_integrable_mult_Fejer_kernel_reflected_part3 less_eq_real_def)
            show "\<bar>Fejer_kernel n x * (if x = 0 then 0 else h x)\<bar> \<le> Fejer_kernel n x * e / 2 / pi"
              if "x \<in> space (lebesgue_on {0..\<xi>})" for x
              using that \<xi> [of x] \<open>e > 0\<close>
              by (auto simp: abs_mult eq simp flip: times_divide_eq_right intro: mult_left_mono)
          qed
        qed
        have 3: "\<dots> \<le> e/2"
          using int_le_pi \<open>0 < e\<close>
          by (simp add: divide_simps mult.commute [of e])

        have "integrable (lebesgue_on {0..pi}) (\<lambda>x. Fejer_kernel n x * h x)"
          unfolding h_def
          by (simp add: absolutely_integrable_imp_integrable absolutely_integrable_mult_Fejer_kernel_reflected_part5 assms)
        then have "LINT x|lebesgue_on {0..pi}. Fejer_kernel n x * h x
                 = (LINT x|lebesgue_on {0..\<xi>}. Fejer_kernel n x * h x) + (LINT x|lebesgue_on {\<xi>..pi}. Fejer_kernel n x * h x)"
          by (rule integral_combine) (use  \<open>0 < \<xi>\<close> \<open>\<xi> < pi\<close> in auto)
        then show "\<bar>LINT u|lebesgue_on {0..pi}. Fejer_kernel n u * h u\<bar> < e"
          using 1 2 3 by linarith
      qed
    qed
  qed
  then show ?thesis
    unfolding h_def by (simp add: Fourier_sum_limit_Fejer_kernel_half assms add_divide_distrib)
qed

corollary Fourier_Fejer_Cesaro_summable_simple:
  assumes f: "continuous_on UNIV f"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>m<n. \<Sum>k\<le>2*m. Fourier_coefficient f k * trigonometric_set k x) / n) \<longlonglongrightarrow> f x"
proof -
  have "(\<lambda>n. (\<Sum>m<n. \<Sum>k\<le>2*m. Fourier_coefficient f k * trigonometric_set k x) / n) \<longlonglongrightarrow> (f x + f x) / 2"
  proof (rule Fourier_Fejer_Cesaro_summable)
    show "f absolutely_integrable_on {- pi..pi}"
      using absolutely_integrable_continuous_real continuous_on_subset f by blast
    show "(f \<longlongrightarrow> f x) (at x within {..x})"  "(f \<longlongrightarrow> f x) (at x within {x..})"
      using Lim_at_imp_Lim_at_within continuous_on_def f by blast+
  qed (auto simp: periodic Lim_at_imp_Lim_at_within continuous_on_def f)
  then show ?thesis
    by simp
qed

end


