theory Gronwall
imports Vector_Derivative_On
begin

subsection \<open>Gronwall\<close>

lemma derivative_quotient_bound:
  assumes g_deriv_on: "(g has_vderiv_on g') {a .. b}"
  assumes frac_le: "\<And>t. t \<in> {a .. b} \<Longrightarrow> g' t / g t \<le> K"
  assumes g'_cont: "continuous_on {a .. b} g'"
  assumes g_pos: "\<And>t. t \<in> {a .. b} \<Longrightarrow> g t > 0"
  assumes t_in: "t \<in> {a .. b}"
  shows "g t \<le> g a * exp (K * (t - a))"
proof -
  have g_deriv: "\<And>t. t \<in> {a .. b} \<Longrightarrow> (g has_real_derivative g' t) (at t within {a .. b})"
    using g_deriv_on
    by (auto simp: has_vderiv_on_def has_field_derivative_iff_has_vector_derivative[symmetric])
  from assms have g_nonzero: "\<And>t. t \<in> {a .. b} \<Longrightarrow> g t \<noteq> 0"
    by fastforce
  have frac_integrable: "\<And>t. t \<in> {a .. b} \<Longrightarrow> (\<lambda>t. g' t / g t) integrable_on {a..t}"
    by (force simp: g_nonzero intro: assms has_field_derivative_subset[OF g_deriv]
      continuous_on_subset[OF g'_cont] continuous_intros integrable_continuous_real
      continuous_on_subset[OF vderiv_on_continuous_on[OF g_deriv_on]])
  have "\<And>t. t \<in> {a..b} \<Longrightarrow> ((\<lambda>t. g' t / g t) has_integral ln (g t) - ln (g a)) {a .. t}"
    by (rule fundamental_theorem_of_calculus)
      (auto intro!: derivative_eq_intros assms has_field_derivative_subset[OF g_deriv]
        simp: has_field_derivative_iff_has_vector_derivative[symmetric])
  hence *: "\<And>t. t \<in> {a .. b} \<Longrightarrow> ln (g t) - ln (g a) = integral {a .. t} (\<lambda>t. g' t / g t)"
    using integrable_integral[OF frac_integrable]
    by (rule has_integral_unique[where f = "\<lambda>t. g' t / g t"])
  from * t_in have "ln (g t) - ln (g a) = integral {a .. t} (\<lambda>t. g' t / g t)" .
  also have "\<dots> \<le> integral {a .. t} (\<lambda>_. K)"
    using \<open>t \<in> {a .. b}\<close>
    by (intro integral_le) (auto intro!: frac_integrable frac_le integral_le)
  also have "\<dots> = K * (t - a)" using \<open>t \<in> {a .. b}\<close>
    by simp
  finally have "ln (g t) \<le> K * (t - a) + ln (g a)" (is "?lhs \<le> ?rhs")
    by simp
  hence "exp ?lhs \<le> exp ?rhs"
    by simp
  thus ?thesis
    using \<open>t \<in> {a .. b}\<close> g_pos
    by (simp add: ac_simps exp_add del: exp_le_cancel_iff)
qed

lemma derivative_quotient_bound_left:
  assumes g_deriv_on: "(g has_vderiv_on g') {a .. b}"
  assumes frac_ge: "\<And>t. t \<in> {a .. b} \<Longrightarrow> K \<le> g' t / g t"
  assumes g'_cont: "continuous_on {a .. b} g'"
  assumes g_pos: "\<And>t. t \<in> {a .. b} \<Longrightarrow> g t > 0"
  assumes t_in: "t \<in> {a..b}"
  shows "g t \<le> g b * exp (K * (t - b))"
proof -
  have g_deriv: "\<And>t. t \<in> {a .. b} \<Longrightarrow> (g has_real_derivative g' t) (at t within {a .. b})"
    using g_deriv_on
    by (auto simp: has_vderiv_on_def has_field_derivative_iff_has_vector_derivative[symmetric])
  from assms have g_nonzero: "\<And>t. t \<in> {a..b} \<Longrightarrow> g t \<noteq> 0"
    by fastforce
  have frac_integrable: "\<And>t. t \<in> {a .. b} \<Longrightarrow> (\<lambda>t. g' t / g t) integrable_on {t..b}"
    by (force simp: g_nonzero intro: assms has_field_derivative_subset[OF g_deriv]
      continuous_on_subset[OF g'_cont] continuous_intros integrable_continuous_real
      continuous_on_subset[OF vderiv_on_continuous_on[OF g_deriv_on]])
  have "\<And>t. t \<in> {a..b} \<Longrightarrow> ((\<lambda>t. g' t / g t) has_integral ln (g b) - ln (g t)) {t..b}"
    by (rule fundamental_theorem_of_calculus)
      (auto intro!: derivative_eq_intros assms has_field_derivative_subset[OF g_deriv]
        simp: has_field_derivative_iff_has_vector_derivative[symmetric])
  hence *: "\<And>t. t \<in> {a..b} \<Longrightarrow> ln (g b) - ln (g t) = integral {t..b} (\<lambda>t. g' t / g t)"
    using integrable_integral[OF frac_integrable]
    by (rule has_integral_unique[where f = "\<lambda>t. g' t / g t"])
  have "K * (b - t) = integral {t..b} (\<lambda>_. K)"
    using \<open>t \<in> {a..b}\<close>
    by simp
  also have "... \<le> integral {t..b} (\<lambda>t. g' t / g t)"
    using \<open>t \<in> {a..b}\<close>
    by (intro integral_le) (auto intro!: frac_integrable frac_ge integral_le)
  also have "... = ln (g b) - ln (g t)"
    using * t_in by simp
  finally have "K * (b - t) + ln (g t) \<le> ln (g b)" (is "?lhs \<le> ?rhs")
    by simp
  hence "exp ?lhs \<le> exp ?rhs"
    by simp
  hence "g t * exp (K * (b - t)) \<le> g b"
    using \<open>t \<in> {a..b}\<close> g_pos
    by (simp add: ac_simps exp_add del: exp_le_cancel_iff)
  hence "g t / exp (K * (t - b)) \<le> g b"
    by (simp add: algebra_simps exp_diff)
  thus ?thesis
    by (simp add: field_simps)
qed

lemma gronwall_general:
  fixes g K C a b and t::real
  defines "G \<equiv> \<lambda>t. C + K * integral {a..t} (\<lambda>s. g s)"
  assumes g_le_G: "\<And>t. t \<in> {a..b} \<Longrightarrow> g t \<le> G t"
  assumes g_cont: "continuous_on {a..b} g"
  assumes g_nonneg: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 \<le> g t"
  assumes pos: "0 < C" "K > 0"
  assumes "t \<in> {a..b}"
  shows "g t \<le> C * exp (K * (t - a))"
proof -
  have G_pos: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 < G t"
    by (auto simp: G_def intro!: add_pos_nonneg mult_nonneg_nonneg Henstock_Kurzweil_Integration.integral_nonneg
      integrable_continuous_real assms intro: less_imp_le continuous_on_subset)
  have "g t \<le> G t" using assms by auto
  also
  {
    have "(G has_vderiv_on (\<lambda>t. K * g t)) {a..b}"
      by (auto intro!: derivative_eq_intros integral_has_vector_derivative g_cont
        simp add: G_def has_vderiv_on_def)
    moreover
    {
      fix t assume "t \<in> {a..b}"
      hence "K * g t / G t \<le> K * G t / G t"
        using pos g_le_G G_pos
        by (intro divide_right_mono mult_left_mono) (auto intro!: less_imp_le)
      also have "\<dots> = K"
        using G_pos[of t] \<open>t \<in> {a .. b}\<close> by simp
      finally have "K * g t / G t \<le> K" .
    }
    ultimately have "G t \<le> G a * exp (K * (t - a))"
      apply (rule derivative_quotient_bound)
      using \<open>t \<in> {a..b}\<close>
      by (auto intro!: continuous_intros g_cont G_pos simp: field_simps pos)
  }
  also have "G a = C"
    by (simp add: G_def)
  finally show ?thesis
    by simp
qed

lemma gronwall_general_left:
  fixes g K C a b and t::real
  defines "G \<equiv> \<lambda>t. C + K * integral {t..b} (\<lambda>s. g s)"
  assumes g_le_G: "\<And>t. t \<in> {a..b} \<Longrightarrow> g t \<le> G t"
  assumes g_cont: "continuous_on {a..b} g"
  assumes g_nonneg: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 \<le> g t"
  assumes pos: "0 < C" "K > 0"
  assumes "t \<in> {a..b}"
  shows "g t \<le> C * exp (-K * (t - b))"
proof -
  have G_pos: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 < G t"
    by (auto simp: G_def intro!: add_pos_nonneg mult_nonneg_nonneg Henstock_Kurzweil_Integration.integral_nonneg
      integrable_continuous_real assms intro: less_imp_le continuous_on_subset)
  have "g t \<le> G t" using assms by auto
  also
  {
    have "(G has_vderiv_on (\<lambda>t. -K * g t)) {a..b}"
      by (auto intro!: derivative_eq_intros g_cont integral_has_vector_derivative'
          simp add: G_def has_vderiv_on_def)
    moreover
    {
      fix t assume "t \<in> {a..b}"
      hence "K * g t / G t \<le> K * G t / G t"
        using pos g_le_G G_pos
        by (intro divide_right_mono mult_left_mono) (auto intro!: less_imp_le)
      also have "\<dots> = K"
        using G_pos[of t] \<open>t \<in> {a .. b}\<close> by simp
      finally have "K * g t / G t \<le> K" .
      hence "-K \<le> -K * g t / G t"
        by simp
    }
    ultimately
    have "G t \<le> G b * exp (-K * (t - b))"
      apply (rule derivative_quotient_bound_left)
      using \<open>t \<in> {a..b}\<close>
      by (auto intro!: continuous_intros g_cont G_pos simp: field_simps pos)
  }
  also have "G b = C"
    by (simp add: G_def)
  finally show ?thesis
    by simp
qed

lemma gronwall_general_segment:
  fixes a b::real
  assumes "\<And>t. t \<in> closed_segment a b \<Longrightarrow> g t \<le> C + K * integral (closed_segment a t) g"
    and "continuous_on (closed_segment a b) g"
    and "\<And>t. t \<in> closed_segment a b \<Longrightarrow> 0 \<le> g t"
    and "0 < C"
    and "0 < K"
    and "t \<in> closed_segment a b"
  shows "g t \<le> C * exp (K * abs (t - a))"
proof cases
  assume "a \<le> b"
  then have *: "abs (t - a) = t -a" using assms by (auto simp: closed_segment_eq_real_ivl)
  show ?thesis
    unfolding *
    using assms
    by (intro gronwall_general[where b=b]) (auto intro!: simp: closed_segment_eq_real_ivl \<open>a \<le> b\<close>)
next
  assume "\<not>a \<le> b"
  then have *: "K * abs (t - a) = - K * (t - a)" using assms by (auto simp: closed_segment_eq_real_ivl algebra_simps)
  {
    fix s :: real
    assume a1: "b \<le> s"
    assume a2: "s \<le> a"
    assume a3: "\<And>t. b \<le> t \<and> t \<le> a \<Longrightarrow> g t \<le> C + K * integral (if a \<le> t then {a..t} else {t..a}) g"
    have "s = a \<or> s < a"
      using a2 by (meson less_eq_real_def)
    then have "g s \<le> C + K * integral {s..a} g"
      using a3 a1 by fastforce
  } then show ?thesis
    unfolding *
    using assms  \<open>\<not>a \<le> b\<close>
    by (intro gronwall_general_left)
      (auto intro!: simp: closed_segment_eq_real_ivl)
qed

lemma gronwall_more_general_segment:
  fixes a b c::real
  assumes "\<And>t. t \<in> closed_segment a b \<Longrightarrow> g t \<le> C + K * integral (closed_segment c t) g"
    and cont: "continuous_on (closed_segment a b) g"
    and "\<And>t. t \<in> closed_segment a b \<Longrightarrow> 0 \<le> g t"
    and "0 < C"
    and "0 < K"
    and t: "t \<in> closed_segment a b"
    and c: "c \<in> closed_segment a b"
  shows "g t \<le> C * exp (K * abs (t - c))"
proof -
  from t c have "t \<in> closed_segment c a \<or> t \<in> closed_segment c b"
    by (auto simp: closed_segment_eq_real_ivl split_ifs)
  then show ?thesis
  proof
    assume "t \<in> closed_segment c a"
    moreover
    have subs: "closed_segment c a \<subseteq> closed_segment a b" using t c
      by (auto simp: closed_segment_eq_real_ivl split_ifs)
    ultimately show ?thesis
      by (intro gronwall_general_segment[where b=a])
        (auto intro!: assms intro: continuous_on_subset)
  next
    assume "t \<in> closed_segment c b"
    moreover
    have subs: "closed_segment c b \<subseteq> closed_segment a b" using t c
      by (auto simp: closed_segment_eq_real_ivl)
    ultimately show ?thesis
      by (intro gronwall_general_segment[where b=b])
        (auto intro!: assms intro: continuous_on_subset)
  qed
qed

lemma gronwall:
  fixes g K C and t::real
  defines "G \<equiv> \<lambda>t. C + K * integral {0..t} (\<lambda>s. g s)"
  assumes g_le_G: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> a \<Longrightarrow> g t \<le> G t"
  assumes g_cont: "continuous_on {0..a} g"
  assumes g_nonneg: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> a \<Longrightarrow> 0 \<le> g t"
  assumes pos: "0 < C" "0 < K"
  assumes "0 \<le> t" "t \<le> a"
  shows "g t \<le> C * exp (K * t)"
  apply(rule gronwall_general[where a=0, simplified, OF assms(2-6)[unfolded G_def]])
  using assms(7,8)
  by simp_all

lemma gronwall_left:
  fixes g K C and t::real
  defines "G \<equiv> \<lambda>t. C + K * integral {t..0} (\<lambda>s. g s)"
  assumes g_le_G: "\<And>t. a \<le> t \<Longrightarrow> t \<le> 0 \<Longrightarrow> g t \<le> G t"
  assumes g_cont: "continuous_on {a..0} g"
  assumes g_nonneg: "\<And>t. a \<le> t \<Longrightarrow> t \<le> 0 \<Longrightarrow> 0 \<le> g t"
  assumes pos: "0 < C" "0 < K"
  assumes "a \<le> t" "t \<le> 0"
  shows "g t \<le> C * exp (-K * t)"
  apply(simp, rule gronwall_general_left[where b=0, simplified, OF assms(2-6)[unfolded G_def]])
  using assms(7,8)
  by simp_all

end