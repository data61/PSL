theory Integrals
  imports "HOL-Analysis.Analysis" General_Utils
begin

lemma gauge_integral_Fubini_universe_x:
  fixes f :: "('a::euclidean_space * 'b::euclidean_space) \<Rightarrow> 'c::euclidean_space"
  assumes fun_lesbegue_integrable: "integrable lborel f" and
    x_axis_integral_measurable: "(\<lambda>x. integral UNIV (\<lambda>y. f(x, y))) \<in> borel_measurable lborel"
  shows "integral UNIV f = integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. f(x,y)))"
    "(\<lambda>x. integral UNIV (\<lambda>y. f(x,y))) integrable_on UNIV"
proof -
  have f_is_measurable: "f \<in> borel_measurable lborel"
    using fun_lesbegue_integrable and borel_measurable_integrable
    by auto
  have fun_lborel_prod_integrable:
    "integrable (lborel \<Otimes>\<^sub>M lborel) f"
    using fun_lesbegue_integrable
    by (simp add: lborel_prod)
  then have region_integral_is_one_twoD_integral:
    "LBINT x. LBINT y. f (x, y) = integral\<^sup>L (lborel \<Otimes>\<^sub>M lborel) f"
    using lborel_pair.integral_fst'
    by auto
  then have AE_one_D_integrals_eq: "AE x in lborel. LBINT y. f (x, y) = integral UNIV (\<lambda>y. f(x,y))"
  proof -
    have "AE x in lborel. integrable lborel (\<lambda>y. f(x,y))"
      using lborel_pair.AE_integrable_fst' and fun_lborel_prod_integrable
      by blast
    then show ?thesis
      using integral_lborel  and always_eventually
        and AE_mp
      by fastforce
  qed
  have one_D_integral_measurable:
    "(\<lambda>x. LBINT y. f (x, y)) \<in> borel_measurable lborel"
    using f_is_measurable and lborel.borel_measurable_lebesgue_integral
    by auto
  then have second_lesbegue_integral_eq:
    "LBINT x. LBINT y. f (x, y) = LBINT x. (integral UNIV (\<lambda>y. f(x,y)))"
    using x_axis_integral_measurable and integral_cong_AE and AE_one_D_integrals_eq
    by blast
  have "integrable lborel (\<lambda>x. LBINT y. f (x, y))"
    using fun_lborel_prod_integrable and lborel_pair.integrable_fst'
    by auto
  then have oneD_gauge_integral_lesbegue_integrable:
    "integrable lborel (\<lambda>x. integral UNIV (\<lambda>y. f(x,y)))"
    using x_axis_integral_measurable and AE_one_D_integrals_eq and integrable_cong_AE_imp
    by blast
  then show one_D_gauge_integral_integrable:
    "(\<lambda>x. integral UNIV (\<lambda>y. f(x,y))) integrable_on UNIV"
    using integrable_on_lborel
    by auto
  have "LBINT x. (integral UNIV (\<lambda>y. f(x,y))) = integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. f(x, y)))"
    using integral_lborel oneD_gauge_integral_lesbegue_integrable
    by fastforce
  then have twoD_lesbeuge_eq_twoD_gauge:
    "LBINT x. LBINT y. f (x, y) = integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. f(x, y)))"
    using second_lesbegue_integral_eq
    by auto
  then show "integral UNIV f = integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. f(x,y)))"
    using fun_lesbegue_integrable and integral_lborel and region_integral_is_one_twoD_integral
    by (metis lborel_prod)
qed

lemma gauge_integral_Fubini_universe_y:
  fixes f :: "('a::euclidean_space * 'b::euclidean_space) \<Rightarrow> 'c::euclidean_space"
  assumes fun_lesbegue_integrable: "integrable lborel f" and
    y_axis_integral_measurable: "(\<lambda>x. integral UNIV (\<lambda>y. f(y, x))) \<in> borel_measurable lborel"
  shows "integral UNIV f = integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. f(y, x)))"
    "(\<lambda>x. integral UNIV (\<lambda>y. f(y, x))) integrable_on UNIV"
proof -
  have f_is_measurable: "f \<in> borel_measurable lborel"
    using fun_lesbegue_integrable and borel_measurable_integrable
    by auto
  have fun_lborel_prod_integrable:
    "integrable (lborel \<Otimes>\<^sub>M lborel) f"
    using fun_lesbegue_integrable
    by (simp add: lborel_prod)
  then have region_integral_is_one_twoD_integral:
    "LBINT x. LBINT y. f (y, x) = integral\<^sup>L (lborel \<Otimes>\<^sub>M lborel) f"
    using lborel_pair.integral_fst'
      f_is_measurable lborel_pair.integrable_product_swap lborel_pair.integral_fst lborel_pair.integral_product_swap lborel_prod
    by force
  then have AE_one_D_integrals_eq: "AE x in lborel. LBINT y. f (y, x) = integral UNIV (\<lambda>y. f(y,x))"
  proof -
    have "AE x in lborel. integrable lborel (\<lambda>y. f(y,x))"
      using lborel_pair.AE_integrable_fst' and fun_lborel_prod_integrable
        lborel_pair.AE_integrable_fst lborel_pair.integrable_product_swap
      by blast
    then show ?thesis
      using integral_lborel  and always_eventually
        and AE_mp
      by fastforce
  qed
  have one_D_integral_measurable:
    "(\<lambda>x. LBINT y. f (y, x)) \<in> borel_measurable lborel"
    using f_is_measurable and lborel.borel_measurable_lebesgue_integral
    by auto
  then have second_lesbegue_integral_eq:
    "LBINT x. LBINT y. f (y, x) = LBINT x. (integral UNIV (\<lambda>y. f(y, x)))"
    using y_axis_integral_measurable and integral_cong_AE and AE_one_D_integrals_eq
    by blast
  have "integrable lborel (\<lambda>x. LBINT y. f (y, x))"
    using fun_lborel_prod_integrable and lborel_pair.integrable_fst'
    by (simp add: lborel_pair.integrable_fst lborel_pair.integrable_product_swap)
  then have oneD_gauge_integral_lesbegue_integrable:
    "integrable lborel (\<lambda>x. integral UNIV (\<lambda>y. f(y, x)))"
    using y_axis_integral_measurable and AE_one_D_integrals_eq and integrable_cong_AE_imp
    by blast
  then show one_D_gauge_integral_integrable:
    "(\<lambda>x. integral UNIV (\<lambda>y. f(y, x))) integrable_on UNIV"
    using integrable_on_lborel
    by auto
  have "LBINT x. (integral UNIV (\<lambda>y. f(y, x))) = integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. f(y, x)))"
    using integral_lborel oneD_gauge_integral_lesbegue_integrable
    by fastforce
  then have twoD_lesbeuge_eq_twoD_gauge:
    "LBINT x. LBINT y. f (y, x) = integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. f(y, x)))"
    using second_lesbegue_integral_eq
    by auto
  then show "integral UNIV f = integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. f(y, x)))"
    using fun_lesbegue_integrable and integral_lborel and region_integral_is_one_twoD_integral
    by (metis lborel_prod)
qed

lemma gauge_integral_Fubini_curve_bounded_region_x:
  fixes f g :: "('a::euclidean_space * 'b::euclidean_space) \<Rightarrow> 'c::euclidean_space" and
    g1 g2:: "'a \<Rightarrow> 'b" and
    s:: "('a * 'b) set"
  assumes fun_lesbegue_integrable: "integrable lborel f" and
    x_axis_gauge_integrable: "\<And>x. (\<lambda>y. f(x, y)) integrable_on UNIV" and
    (*IS THIS redundant? NO IT IS NOT*)
    x_axis_integral_measurable: "(\<lambda>x. integral UNIV (\<lambda>y. f(x, y))) \<in> borel_measurable lborel" and
    f_is_g_indicator: "f = (\<lambda>x. if x \<in> s then g x else 0)" and
    s_is_bounded_by_g1_and_g2: "s = {(x,y). (\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i) \<and>
                                      (\<forall>i\<in>Basis. (g1 x) \<bullet> i \<le> y \<bullet> i \<and> y \<bullet> i \<le> (g2 x) \<bullet> i)}"
  shows "integral s g = integral (cbox a b) (\<lambda>x. integral (cbox (g1 x) (g2 x)) (\<lambda>y. g(x,y)))"
proof -
  have two_D_integral_to_one_D: "integral UNIV f = integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. f(x,y)))"
    using gauge_integral_Fubini_universe_x and fun_lesbegue_integrable and x_axis_integral_measurable
    by auto
  have one_d_integral_integrable: "(\<lambda>x. integral UNIV (\<lambda>y. f(x,y))) integrable_on UNIV"
    using gauge_integral_Fubini_universe_x(2) and assms
    by blast
  have case_x_in_range:
    "\<forall> x \<in> cbox a b. integral (cbox (g1 x) (g2 x)) (\<lambda>y. g(x,y)) = integral UNIV (\<lambda>y. f(x,y))"
  proof
    fix x:: 'a
    assume within_range: "x \<in> (cbox a b)"
    let ?f_one_D_spec = "(\<lambda>y. if y \<in> (cbox (g1 x) (g2 x)) then g(x,y) else 0)"
    have f_one_D_region: "(\<lambda>y. f(x,y)) = (\<lambda>y. if y \<in> cbox (g1 x) (g2 x) then g(x,y) else 0)"
    proof
      fix y::'b
      show "f (x, y) = (if y \<in> (cbox (g1 x) (g2 x)) then g (x, y) else 0)"
        apply (simp add: f_is_g_indicator s_is_bounded_by_g1_and_g2)
        using within_range
        apply (simp add: cbox_def)
        by smt
    qed
    have zero_out_of_bound: "\<forall> y.  y \<notin> cbox (g1 x) (g2 x) \<longrightarrow> f (x,y) = 0"
      using f_is_g_indicator and s_is_bounded_by_g1_and_g2
      by (auto simp add: cbox_def)
    have "(\<lambda>y. f(x,y)) integrable_on cbox (g1 x)  (g2 x)"
    proof -
      have "?f_one_D_spec integrable_on UNIV"
        using f_one_D_region and x_axis_gauge_integrable
        by metis
      then have "?f_one_D_spec integrable_on cbox(g1 x) (g2 x)"
        using integrable_on_subcbox
        by blast
      then show ?thesis using f_one_D_region  by auto
    qed
    then have f_integrale_x: "((\<lambda>y. f(x,y)) has_integral (integral (cbox (g1 x) (g2 x)) (\<lambda>y. f(x,y)))) (cbox (g1 x) (g2 x))"
      using integrable_integral and within_range and x_axis_gauge_integrable
      by auto
    have "integral (cbox (g1 x)  (g2 x)) (\<lambda>y. f (x, y)) = integral UNIV (\<lambda>y. f (x, y))"
      using has_integral_on_superset[OF f_integrale_x _ Set.subset_UNIV] zero_out_of_bound
      by (simp add: integral_unique)
    then have "((\<lambda>y. f(x, y)) has_integral integral UNIV (\<lambda>y. f (x, y))) (cbox (g1 x) (g2 x))"
      using f_integrale_x
      by simp
    then have "((\<lambda>y. g(x, y)) has_integral integral UNIV (\<lambda>y. f (x, y))) (cbox (g1 x)(g2 x))"
      using  Henstock_Kurzweil_Integration.has_integral_restrict [OF subset_refl ] and
        f_one_D_region
      by (smt has_integral_eq)
    then show "integral (cbox (g1 x) (g2 x)) (\<lambda>y. g (x, y)) = integral UNIV (\<lambda>y. f (x, y))"
      by auto
  qed
  have case_x_not_in_range:
    "\<forall> x. x \<notin> cbox a  b \<longrightarrow> integral UNIV (\<lambda>y. f(x,y)) = 0"
  proof
    fix x::'a
    have "x \<notin> (cbox a b) \<longrightarrow> (\<forall>y. f(x,y) = 0)"
      apply  (simp add: s_is_bounded_by_g1_and_g2 f_is_g_indicator cbox_def)
      by auto
    then show "x \<notin> cbox a b \<longrightarrow> integral UNIV (\<lambda>y. f (x, y)) = 0"
      by (simp)
  qed
  have RHS: "integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. f(x,y))) = integral (cbox a b) (\<lambda>x. integral (cbox (g1 x) (g2 x)) (\<lambda>y. g(x,y)))"
  proof -
    let ?first_integral = "(\<lambda>x. integral (cbox (g1 x) (g2 x)) (\<lambda>y. g(x,y)))"
    let ?x_integral_cases = "(\<lambda>x. if x \<in> cbox a b then  ?first_integral x else 0)"
    have x_integral_cases_integral: "(\<lambda>x. integral UNIV (\<lambda>y. f(x,y))) = ?x_integral_cases"
      using case_x_in_range and case_x_not_in_range
      by auto
    have "((\<lambda>x. integral UNIV (\<lambda>y. f(x,y))) has_integral (integral UNIV f)) UNIV"
      using two_D_integral_to_one_D
        one_d_integral_integrable
      by auto
    then have "(?x_integral_cases has_integral (integral UNIV f)) UNIV"
      using x_integral_cases_integral by auto
    then have "(?first_integral has_integral (integral UNIV f)) (cbox a b)"
      using  has_integral_restrict_UNIV[of "cbox a b" "?first_integral" "integral UNIV f"]
      by auto
    then show ?thesis
      using two_D_integral_to_one_D
      by (simp add: integral_unique)
  qed
  have f_integrable:"f integrable_on UNIV"
    using fun_lesbegue_integrable and integrable_on_lborel
    by auto
  then have LHS: "integral UNIV f = integral s g"
    apply (simp add: f_is_g_indicator)
    using integrable_restrict_UNIV
      integral_restrict_UNIV
    by auto
  then show ?thesis
    using RHS and two_D_integral_to_one_D
    by auto
qed

lemma gauge_integral_Fubini_curve_bounded_region_y:
  fixes f g :: "('a::euclidean_space * 'b::euclidean_space) \<Rightarrow> 'c::euclidean_space" and
    g1 g2:: "'b \<Rightarrow> 'a" and
    s:: "('a * 'b) set"
  assumes fun_lesbegue_integrable: "integrable lborel f" and
    y_axis_gauge_integrable: "\<And>x. (\<lambda>y. f(y, x)) integrable_on UNIV" and
    (*IS THIS redundant? NO IT IS NOT*)
    y_axis_integral_measurable: "(\<lambda>x. integral UNIV (\<lambda>y. f(y, x))) \<in> borel_measurable lborel" and
    f_is_g_indicator: "f = (\<lambda>x. if x \<in> s then g x else 0)" and
    s_is_bounded_by_g1_and_g2: "s = {(y, x). (\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i) \<and>
                                                   (\<forall>i\<in>Basis. (g1 x) \<bullet> i \<le> y \<bullet> i \<and> y \<bullet> i \<le> (g2 x) \<bullet> i)}"
  shows "integral s g = integral (cbox a b) (\<lambda>x. integral (cbox (g1 x) (g2 x)) (\<lambda>y. g(y, x)))"
proof -
  have two_D_integral_to_one_D: "integral UNIV f = integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. f(y, x)))"
    using gauge_integral_Fubini_universe_y and fun_lesbegue_integrable and y_axis_integral_measurable
    by auto
  have one_d_integral_integrable: "(\<lambda>x. integral UNIV (\<lambda>y. f(y, x))) integrable_on UNIV"
    using gauge_integral_Fubini_universe_y(2) and assms
    by blast
  have case_y_in_range:
    "\<forall> x \<in> cbox a b. integral (cbox (g1 x) (g2 x)) (\<lambda>y. g(y, x)) = integral UNIV (\<lambda>y. f(y, x))"
  proof
    fix x:: 'b
    assume within_range: "x \<in> (cbox a b)"
    let ?f_one_D_spec = "(\<lambda>y. if y \<in> (cbox (g1 x) (g2 x)) then g(y, x) else 0)"
    have f_one_D_region: "(\<lambda>y. f(y, x)) = (\<lambda>y. if y \<in> cbox (g1 x) (g2 x) then g(y, x) else 0)"
    proof
      fix y::'a
      show "f (y, x) = (if y \<in> (cbox (g1 x) (g2 x)) then g (y, x) else 0)"
        apply (simp add: f_is_g_indicator s_is_bounded_by_g1_and_g2)
        using within_range
        apply (simp add: cbox_def)
        by smt
    qed
    have zero_out_of_bound: "\<forall> y.  y \<notin> cbox (g1 x) (g2 x) \<longrightarrow> f (y, x) = 0"
      using f_is_g_indicator and s_is_bounded_by_g1_and_g2
      by (auto simp add: cbox_def)
    have "(\<lambda>y. f(y, x)) integrable_on cbox (g1 x)  (g2 x)"
    proof -
      have "?f_one_D_spec integrable_on UNIV"
        using f_one_D_region and y_axis_gauge_integrable
        by metis
      then have "?f_one_D_spec integrable_on cbox(g1 x) (g2 x)"
        using integrable_on_subcbox
        by blast
      then show ?thesis using f_one_D_region  by auto
    qed
    then have f_integrale_y: "((\<lambda>y. f(y, x)) has_integral (integral (cbox (g1 x) (g2 x)) (\<lambda>y. f(y,x)))) (cbox (g1 x) (g2 x))"
      using integrable_integral and within_range and y_axis_gauge_integrable
      by auto
    have "integral (cbox (g1 x)  (g2 x)) (\<lambda>y. f (y, x)) = integral UNIV (\<lambda>y. f (y, x))"
      using has_integral_on_superset[OF f_integrale_y _ Set.subset_UNIV] zero_out_of_bound
      by (simp add: integral_unique)
    then have "((\<lambda>y. f(y, x)) has_integral integral UNIV (\<lambda>y. f (y, x))) (cbox (g1 x) (g2 x))"
      using f_integrale_y
      by simp
    then have "((\<lambda>y. g(y, x)) has_integral integral UNIV (\<lambda>y. f (y, x))) (cbox (g1 x)(g2 x))"
      using  Henstock_Kurzweil_Integration.has_integral_restrict [OF subset_refl ] and
        f_one_D_region
      by (smt has_integral_eq)
    then show "integral (cbox (g1 x) (g2 x)) (\<lambda>y. g (y, x)) = integral UNIV (\<lambda>y. f (y, x))"
      by auto
  qed
  have case_y_not_in_range:
    "\<forall> x. x \<notin> cbox a  b \<longrightarrow> integral UNIV (\<lambda>y. f(y, x)) = 0"
  proof
    fix x::'b
    have "x \<notin> (cbox a b) \<longrightarrow> (\<forall>y. f(y, x) = 0)"
      apply  (simp add: s_is_bounded_by_g1_and_g2 f_is_g_indicator cbox_def)
      by auto
    then show "x \<notin> cbox a b \<longrightarrow> integral UNIV (\<lambda>y. f (y, x)) = 0"
      by (simp)
  qed
  have RHS: "integral UNIV (\<lambda>x. integral UNIV (\<lambda>y. f(y, x))) = integral (cbox a b) (\<lambda>x. integral (cbox (g1 x) (g2 x)) (\<lambda>y. g(y, x)))"
  proof -
    let ?first_integral = "(\<lambda>x. integral (cbox (g1 x) (g2 x)) (\<lambda>y. g(y, x)))"
    let ?x_integral_cases = "(\<lambda>x. if x \<in> cbox a b then  ?first_integral x else 0)"
    have y_integral_cases_integral: "(\<lambda>x. integral UNIV (\<lambda>y. f(y, x))) = ?x_integral_cases"
      using case_y_in_range and case_y_not_in_range
      by auto
    have "((\<lambda>x. integral UNIV (\<lambda>y. f(y, x))) has_integral (integral UNIV f)) UNIV"
      using two_D_integral_to_one_D
        one_d_integral_integrable
      by auto
    then have "(?x_integral_cases has_integral (integral UNIV f)) UNIV"
      using y_integral_cases_integral by auto
    then have "(?first_integral has_integral (integral UNIV f)) (cbox a b)"
      using has_integral_restrict_UNIV[of "cbox a b" "?first_integral" "integral UNIV f"]
      by auto
    then show ?thesis
      using two_D_integral_to_one_D
      by (simp add: integral_unique)
  qed
  have f_integrable:"f integrable_on UNIV"
    using fun_lesbegue_integrable and integrable_on_lborel
    by auto
  then have LHS: "integral UNIV f = integral s g"
    apply (simp add: f_is_g_indicator)
    using integrable_restrict_UNIV
      integral_restrict_UNIV
    by auto
  then show ?thesis
    using RHS and two_D_integral_to_one_D
    by auto
qed

lemma gauge_integral_by_substitution:
  fixes f::"(real \<Rightarrow> real)" and
    g::"(real \<Rightarrow> real)" and
    g'::"real \<Rightarrow> real" and
    a::"real" and
    b::"real"
  assumes a_le_b: "a \<le> b" and
    ga_le_gb: "g a \<le> g b" and
    g'_derivative: "\<forall>x \<in> {a..b}. (g has_vector_derivative (g' x)) (at x within {a..b})" and
    g'_continuous: "continuous_on {a..b} g'" and
    f_continuous: "continuous_on (g ` {a..b}) f"
  shows "integral {g a..g b} (f) = integral {a..b} (\<lambda>x. f(g x) * (g' x))"
proof -
  have "\<forall>x \<in> {a..b}. (g has_real_derivative (g' x)) (at x within {a..b})"
    using has_field_derivative_iff_has_vector_derivative[of "g"] and g'_derivative
    by auto
  then have 2: "interval_lebesgue_integral lborel (ereal (a)) (ereal (b)) (\<lambda>x. g' x *\<^sub>R f (g x))
                    = interval_lebesgue_integral lborel (ereal (g a)) (ereal (g b)) f"
    using interval_integral_substitution_finite[of "a" "b" "g" "g'" "f"] and g'_continuous and a_le_b and f_continuous
    by auto
  have g_continuous: "continuous_on {a .. b}  g"
    using Derivative.differentiable_imp_continuous_on
    apply (simp add: differentiable_on_def differentiable_def)
    by (metis continuous_on_vector_derivative g'_derivative)
  have "set_integrable lborel {a .. b} (\<lambda>x. g' x *\<^sub>R f (g x))"
  proof -
    have "continuous_on {a .. b} (\<lambda>x. g' x *\<^sub>R f (g x))"
    proof -
      have "continuous_on {a .. b} (\<lambda>x. f (g x))"
      proof -
        show ?thesis
          using Topological_Spaces.continuous_on_compose f_continuous g_continuous
          by auto
      qed
      then show ?thesis
        using Limits.continuous_on_mult g'_continuous
        by auto
    qed
    then show ?thesis
      using borel_integrable_atLeastAtMost' by blast
  qed
  then have 0: "interval_lebesgue_integral lborel (ereal (a)) (ereal (b)) (\<lambda>x. g' x *\<^sub>R f (g x))
                      = integral {a .. b} (\<lambda>x. g' x *\<^sub>R f (g x))"
    using a_le_b and interval_integral_eq_integral
    by (metis (no_types))
  have "set_integrable lborel {g a .. g b} f"
  proof -
    have "continuous_on {g a .. g b} f"
    proof -
      have "{g a .. g b} \<subseteq> g ` {a .. b}"
        using g_continuous
        by (metis a_le_b atLeastAtMost_iff atLeastatMost_subset_iff continuous_image_closed_interval imageI order_refl)
      then show "continuous_on {g a .. g b} f"
        using f_continuous continuous_on_subset
        by blast
    qed
    then show ?thesis
      using borel_integrable_atLeastAtMost'
      by blast
  qed
  then have 1: "interval_lebesgue_integral lborel (ereal (g a)) (ereal (g b)) f
                      = integral {g a .. g b} f"
    using ga_le_gb and interval_integral_eq_integral
    by (metis (no_types))
  then show ?thesis
    using 0 and 1 and 2
    by (metis (no_types, lifting)  Henstock_Kurzweil_Integration.integral_cong mult.commute real_scaleR_def)
qed

lemma frontier_ic:
  assumes "a < (b::real)"
  shows "frontier {a<..b}  = {a,b}"
  apply(simp add: frontier_def)
  using assms
  by auto

lemma frontier_ci:
  assumes "a < (b::real)"
  shows "frontier {a<..<b}  = {a,b}"
  apply(simp add: frontier_def)
  using assms
  by auto

lemma ic_not_closed:
  assumes "a < (b::real)"
  shows "\<not> closed {a<..b}"
  using assms frontier_subset_eq frontier_ic greaterThanAtMost_iff by blast

lemma closure_ic_union_ci:
  assumes "a < (b::real)" "b < c"
  shows "closure ({a..<b} \<union> {b<..c})  = {a .. c}"
  using frontier_ic[OF assms(1)] frontier_ci[OF assms(2)] closure_Un assms
  apply(simp add: frontier_def)
  by auto

lemma interior_ic_ci_union:
  assumes "a < (b::real)" "b < c"
  shows "b \<notin> (interior ({a..<b} \<union> {b<..c}))"
proof-
  have "b \<notin> ({a..<b} \<union> {b<..c})" by auto
  then show ?thesis
    using interior_subset by blast
qed

lemma frontier_ic_union_ci:
  assumes "a < (b::real)" "b < c"
  shows "b \<in> frontier ({a..<b} \<union> {b<..c})"
  using closure_ic_union_ci assms interior_ic_ci_union
  by(simp add: frontier_def)

lemma ic_union_ci_not_closed:
  assumes "a < (b::real)" "b < c"
  shows "\<not> closed ({a..<b} \<union> {b<..c})"
proof-
  have "b \<notin> ({a..<b} \<union> {b<..c})" by auto
  then show ?thesis
    using assms frontier_subset_eq frontier_ic_union_ci[OF assms]
    by (auto simp only: subset_iff)
qed

lemma integrable_continuous_:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "continuous_on (cbox a b) f"
  shows "f integrable_on cbox a b"
  by (simp add: assms integrable_continuous)

lemma removing_singletons_from_div:
  assumes   "\<forall>t\<in>S. \<exists>c d::real. c < d \<and> {c..d} = t"
    "{x} \<union> \<Union>S = {a..b}" "a < x" "x < b"
    "finite S"
  shows "\<exists>t\<in>S. x \<in> t"
proof(rule ccontr)
  assume "\<not>(\<exists>t\<in>S. x \<in> t)"
  then have "\<forall>t\<in>S. x \<notin> t" by auto
  then have "x \<notin> \<Union>S" by auto
  then have i: "\<Union>S = {a..b} - {x}" using assms (2) by auto
  have "x \<in> {a..b}" using assms by auto
  then have "{a .. b} - {x} = {a..<x} \<union> {x<..b}" by auto
  then have 0: "\<Union>S = {a..<x} \<union> {x<..b}" using i by auto
  have 1:"closed (\<Union>S)"
    apply(rule closed_Union)
  proof-
    show "finite S"
      using assms by auto
    show "\<forall>T\<in>S. closed T" using assms  by auto
  qed
  show False using 0 1 ic_union_ci_not_closed assms by auto
qed

lemma remove_singleton_from_division_of:(*By Manuel Eberl*)
  assumes "A division_of {a::real..b}" "a < b"
  assumes "x \<in> {a..b}"
  shows   "\<exists>c d. c < d \<and> {c..d} \<in> A \<and> x \<in> {c..d}"
proof -
  from assms have "x islimpt {a..b}"
    by (intro connected_imp_perfect) auto
  also have "{a..b} = {x. {x..x} \<in> A} \<union> ({a..b} - {x. {x..x} \<in> A})"
    using assms by auto
  also have "x islimpt \<dots> \<longleftrightarrow> x islimpt {a..b} - {x. {x..x} \<in> A}"
  proof (intro islimpt_Un_finite)
    have "{x. {x..x} \<in> A} \<subseteq> Inf ` A"
    proof safe
      fix x assume "{x..x} \<in> A"
      thus "x \<in> Inf ` A"
        by (auto intro!: bexI[of _ "{x}"] simp: image_iff)
    qed
    moreover from assms have "finite A" by (auto simp: division_of_def)
    hence "finite (Inf ` A)" by auto
    ultimately show "finite {x. {x..x} \<in> A}" by (rule finite_subset)
  qed
  also have "{a..b} = \<Union>A"
    using assms by (auto simp: division_of_def)
  finally have "x islimpt \<Union>(A - range (\<lambda>x. {x..x}))"
    by (rule islimpt_subset) auto
  moreover have "closed (\<Union>(A - range (\<lambda>x. {x..x})))"
    using assms by (intro closed_Union) auto
  ultimately have "x \<in> (\<Union>(A - range (\<lambda>x. {x..x})))"
    by (auto simp: closed_limpt)
  then obtain X where "x \<in> X" "X \<in> A" "X \<notin> range (\<lambda>x. {x..x})"
    by blast
  moreover from division_ofD(2)[OF assms(1) this(2)] division_ofD(3)[OF assms(1) this(2)]
    division_ofD(4)[OF assms(1) this(2)]
  obtain c d where "X = cbox c d" "X \<subseteq> {a..b}" "X \<noteq> {}" by blast
  ultimately have "c \<le> d" by auto
  have "c \<noteq> d"
  proof
    assume "c = d"
    with \<open>X = cbox c d\<close> have "X = {c..c}" by auto
    hence "X \<in> range (\<lambda>x. {x..x})" by blast
    with \<open>X \<notin> range (\<lambda>x. {x..x})\<close> show False by contradiction
  qed
  with \<open>c \<le> d\<close> have "c < d" by simp
  with \<open>X = cbox c d\<close> and \<open>x \<in> X\<close> and \<open>X \<in> A\<close> show ?thesis
    by auto
qed

lemma remove_singleton_from_tagged_division_of:
  assumes "A tagged_division_of {a::real..b}" "a < b"
  assumes "x \<in> {a..b}"
  shows   "\<exists>k c d. c < d \<and> (k, {c..d}) \<in> A \<and> x \<in> {c..d}"
  using remove_singleton_from_division_of[OF division_of_tagged_division[OF assms(1)] assms(2)]
    (*sledgehammer*)
  using assms(3) by fastforce

lemma tagged_div_wo_singlestons:
  assumes "p tagged_division_of {a::real..b}" "a < b"
  shows "(p - {xk. \<exists>x y. xk = (x,{y})}) tagged_division_of cbox a b"
  using remove_singleton_from_tagged_division_of[OF assms] assms
  apply(auto simp add: tagged_division_of_def tagged_partial_division_of_def)
     apply blast
    apply blast
   apply blast
  by fastforce

lemma tagged_div_wo_empty:
  assumes "p tagged_division_of {a::real..b}" "a < b"
  shows "(p - {xk. \<exists>x. xk = (x,{})}) tagged_division_of cbox a b"
  using remove_singleton_from_tagged_division_of[OF assms] assms
  apply(auto simp add: tagged_division_of_def tagged_partial_division_of_def)
     apply blast
    apply blast
   apply blast
  by fastforce

lemma fine_diff:
  assumes "\<gamma> fine p"
  shows "\<gamma> fine (p - s)"
  apply (auto simp add: fine_def)
  using assms by auto

lemma tagged_div_tage_notin_set:
  assumes "finite (s::real set)"
    "p tagged_division_of {a..b}"
    "\<gamma> fine p" "(\<forall>(x, K)\<in>p. \<exists>c d::real. c < d \<and> K = {c..d})" "gauge \<gamma>"
  shows "\<exists>p' \<gamma>'. p' tagged_division_of {a..b} \<and>
                  \<gamma>' fine p' \<and> (\<forall>(x, K)\<in>p'. x \<notin> s) \<and> gauge \<gamma>'"
proof-
  have "(\<forall>(x::real, K)\<in>p. \<exists>x'. x' \<notin> s \<and> x'\<in> interior K)"
  proof-
    {fix x::real
      fix K
      assume ass: "(x::real,K) \<in> p"
      have "(\<forall>(x, K)\<in>p. infinite (interior K))"
        using assms(4) infinite_Ioo interior_atLeastAtMost_real
        by (smt split_beta)
      then have i: "infinite (interior K)" using ass by auto
      have "\<exists>x'. x' \<notin> s \<and> x'\<in> interior K"
        using infinite_imp_nonempty[OF Diff_infinite_finite[OF assms(1) i]] by auto}
    then show ?thesis by auto
  qed
  then obtain f where f: "(\<forall>(x::real, K)\<in>p. (f (x,K)) \<notin> s \<and> (f (x,K)) \<in> interior K)"
    using choice_iff[where ?Q = "\<lambda>(x,K) x'. (x::real, K)\<in>p \<longrightarrow> x' \<notin> s \<and> x' \<in> interior K"]
    apply (auto simp add: case_prod_beta)
    by metis
  have f': "(\<forall>(x::real, K)\<in>p. (f (x,K)) \<notin> s \<and> (f (x,K)) \<in> K)"
    using f interior_subset
    by (auto simp add: case_prod_beta subset_iff)
  let ?p' = "{m. (\<exists>xK. m = ((f xK), snd xK) \<and> xK \<in> p)}"
  have 0: "(\<forall>(x, K)\<in>?p'. x \<notin> s)"
    using f
    by (auto simp add: case_prod_beta)
  have i: "finite {(f (a, b), b) |a b. (a, b) \<in> p}"
  proof-
    have a: "{(f (a, b), b) |a b. (a, b) \<in> p} = (%(a,b). (f(a,b),b)) ` p"  by auto
    have b: "finite p" using assms(2) by auto
    show ?thesis using a b by auto
  qed
  have 1: "?p' tagged_division_of {a..b}"
    using assms(2) f'
    apply(auto simp add: tagged_division_of_def tagged_partial_division_of_def case_prod_beta)
       apply(metis i)
      apply blast
     apply blast
    by fastforce
      (*f is injective becuase interiors of different K's are disjoint and f is in interior*)
  have f_inj: "inj_on f p"
    apply(simp add: inj_on_def)
  proof-
    {fix x y
      assume "x \<in> p" "y \<in> p"
        "f x = f y"
      then have "x = y"
        using f
          tagged_division_ofD(5)[OF assms(2)]
          (*sledgehammer*)
        by (smt case_prodE disjoint_insert(2) mk_disjoint_insert)}note * = this
    show "\<forall>x\<in>p. \<forall>y\<in>p. f x = f y \<longrightarrow> x = y"  using * by auto
  qed
  let ?\<gamma>' = "\<lambda>x. if (\<exists>xK \<in> p. f xK  = x) then (\<gamma> o fst o  the_inv_into p f) x else \<gamma> x"
  have 2: "?\<gamma>' fine ?p'" using assms(3)
    apply(auto simp add: fine_def case_prod_beta the_inv_into_f_f[OF f_inj])
    by force
  have 3: "gauge ?\<gamma>'"
    using assms(5) assms(3) f'
    apply(auto simp add: fine_def gauge_def case_prod_beta the_inv_into_f_f[OF f_inj])
    by force
  have "?p' tagged_division_of {a..b} \<and> ?\<gamma>' fine ?p' \<and> (\<forall>(x, K)\<in>?p'. x \<notin> s) \<and> gauge ?\<gamma>'"
    using 0 1 2 3 by auto
  then show ?thesis by smt
qed

lemma has_integral_bound_spike_finite:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B" and "finite S"
    and f: "(f has_integral i) (cbox a b)"
    and leB: "\<And>x. x \<in> cbox a b - S \<Longrightarrow> norm (f x) \<le> B"
  shows "norm i \<le> B * content (cbox a b)"
proof -
  define g where "g \<equiv> (\<lambda>x. if x \<in> S then 0 else f x)"
  then have "\<And>x. x \<in> cbox a b - S \<Longrightarrow> norm (g x) \<le> B"
    using leB by simp
  moreover have "(g has_integral i) (cbox a b)"
    using has_integral_spike_finite [OF \<open>finite S\<close> _ f]
    by (simp add: g_def)
  ultimately show ?thesis
    by (simp add: \<open>0 \<le> B\<close> g_def has_integral_bound)
qed

lemma has_integral_bound_:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "a < b"
    and "0 \<le> B"
    and f: "(f has_integral i) (cbox a b)"
    and "finite s"
    and "\<forall>x\<in>(cbox a b)-s. norm (f x) \<le> B"
  shows "norm i \<le> B * content (cbox a b)"
  using has_integral_bound_spike_finite assms by blast

corollary has_integral_bound_real':
  fixes f :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B"
    and f: "(f has_integral i) (cbox a b)"
    and "finite s"
    and "\<forall>x\<in>(cbox a b)-s. norm (f x) \<le> B"
  shows "norm i \<le> B * content {a..b}"
    (*sledgehammer*)
  by (metis assms(1) assms(3) assms(4) box_real(2) f has_integral_bound_spike_finite)

lemma integral_has_vector_derivative_continuous_at':
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite s"
    and f: "f integrable_on {a..b}"
    and x: "x \<in> {a..b} - s"
    and fx: "continuous (at x within ({a..b} - s)) f"
  shows "((\<lambda>u. integral {a..u} f) has_vector_derivative f x) (at x within ({a..b} - s))"
proof -
  let ?I = "\<lambda>a b. integral {a..b} f"
  { fix e::real
    assume "e > 0"
    obtain d where "d>0" and d: "\<And>x'. \<lbrakk>x' \<in> {a..b} - s; \<bar>x' - x\<bar> < d\<rbrakk> \<Longrightarrow> norm(f x' - f x) \<le> e"
      using \<open>e>0\<close> fx by (auto simp: continuous_within_eps_delta dist_norm less_imp_le)
    have "norm (integral {a..y} f - integral {a..x} f - (y-x) *\<^sub>R f x) \<le> e * \<bar>y - x\<bar>"
      if y: "y \<in> {a..b} - s" and yx: "\<bar>y - x\<bar> < d" for y
    proof (cases "y < x")
      case False
      have "f integrable_on {a..y}"
        using f y by (simp add: integrable_subinterval_real)
      then have Idiff: "?I a y - ?I a x = ?I x y"
        using False x by (simp add: algebra_simps integral_combine)
      have fux_int: "((\<lambda>u. f u - f x) has_integral integral {x..y} f - (y-x) *\<^sub>R f x) {x..y}"
        apply (rule has_integral_diff)
        using x y apply (auto intro: integrable_integral [OF integrable_subinterval_real [OF f]])
        using has_integral_const_real [of "f x" x y] False
        apply (simp add: )
        done
      show ?thesis
        using False
        apply (simp add: abs_eq_content del: content_real_if measure_lborel_Icc)
        apply (rule has_integral_bound_real'[where f="(\<lambda>u. f u - f x)"])
        using yx False d x y \<open>e>0\<close> apply (auto simp add: Idiff fux_int)
      proof-
        let ?M48= "mset_set s"
        show "\<And>z. y - x < d \<Longrightarrow> (\<And>x'. a \<le> x' \<and> x' \<le> b \<and> x' \<notin> s \<Longrightarrow> \<bar>x' - x\<bar> < d \<Longrightarrow> norm (f x' - f x) \<le> e) \<Longrightarrow> 0 < e \<Longrightarrow> z \<notin># ?M48 \<Longrightarrow> a \<le> x \<Longrightarrow> x \<notin> s \<Longrightarrow> y \<le> b \<Longrightarrow> y \<notin> s \<Longrightarrow> x \<le> z \<Longrightarrow> z \<le> y \<Longrightarrow> norm (f z - f x) \<le> e"
          using assms by auto
      qed
    next
      case True
      have "f integrable_on {a..x}"
        using f x by (simp add: integrable_subinterval_real)
      then have Idiff: "?I a x - ?I a y = ?I y x"
        using True x y by (simp add: algebra_simps integral_combine)
      have fux_int: "((\<lambda>u. f u - f x) has_integral integral {y..x} f - (x - y) *\<^sub>R f x) {y..x}"
        apply (rule has_integral_diff)
        using x y apply (auto intro: integrable_integral [OF integrable_subinterval_real [OF f]])
        using has_integral_const_real [of "f x" y x] True
        apply (simp add: )
        done
      have "norm (integral {a..x} f - integral {a..y} f - (x - y) *\<^sub>R f x) \<le> e * \<bar>y - x\<bar>"
        using True
        apply (simp add: abs_eq_content del: content_real_if measure_lborel_Icc)
        apply (rule has_integral_bound_real'[where f="(\<lambda>u. f u - f x)"])
        using yx True d x y \<open>e>0\<close> apply (auto simp add: Idiff fux_int)
      proof-
        let ?M44= "mset_set s"
        show " \<And>xa. x - y < d \<Longrightarrow> y < x \<Longrightarrow> (\<And>x'. a \<le> x' \<and> x' \<le> b \<and> x' \<notin> s \<Longrightarrow> \<bar>x' - x\<bar> < d \<Longrightarrow> norm (f x' - f x) \<le> e) \<Longrightarrow> 0 < e \<Longrightarrow> xa \<notin># ?M44 \<Longrightarrow> x \<le> b \<Longrightarrow> x \<notin> s \<Longrightarrow> a \<le> y \<Longrightarrow> y \<notin> s \<Longrightarrow> y \<le> xa \<Longrightarrow> xa \<le> x \<Longrightarrow> norm (f xa - f x) \<le> e"
          using assms by auto
      qed
      then show ?thesis
        by (simp add: algebra_simps norm_minus_commute)
    qed
    then have "\<exists>d>0. \<forall>y\<in>{a..b} - s. \<bar>y - x\<bar> < d \<longrightarrow> norm (integral {a..y} f - integral {a..x} f - (y-x) *\<^sub>R f x) \<le> e * \<bar>y - x\<bar>"
      using \<open>d>0\<close> by blast
  }
  then show ?thesis
    by (simp add: has_vector_derivative_def has_derivative_within_alt bounded_linear_scaleR_left)
qed

lemma integral_has_vector_derivative':
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite s"
    "f integrable_on {a..b}"
    "x \<in> {a..b} - s"
    "continuous (at x within {a..b} - s) f"
  shows "((\<lambda>u. integral {a .. u} f) has_vector_derivative f(x)) (at x within {a .. b} - s)"
  apply (rule integral_has_vector_derivative_continuous_at')
  using assms
     apply (auto simp: continuous_on_eq_continuous_within)
  done

lemma fundamental_theorem_of_calculus_interior_stronger:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite S"
    and "a \<le> b" "\<And>x. x \<in> {a <..< b} - S \<Longrightarrow> (f has_vector_derivative f'(x)) (at x)"
    and "continuous_on {a .. b} f"
  shows "(f' has_integral (f b - f a)) {a .. b}"
  using assms
proof (induction arbitrary: a b)
  case empty
  then show ?case
    using fundamental_theorem_of_calculus_interior by force
next
  case (insert x S)
  show ?case
  proof (cases "x \<in> {a<..<b}")
    case False then show ?thesis
      using insert by blast
  next
    case True then have "a < x" "x < b"
      by auto
    have "(f' has_integral f x - f a) {a..x}"
      apply (rule insert)
      using \<open>a < x\<close> \<open>x < b\<close> insert.prems continuous_on_subset by force+
    moreover have "(f' has_integral f b - f x) {x..b}"
      apply (rule insert)
      using \<open>x < b\<close> \<open>a < x\<close> insert.prems continuous_on_subset by force+
    ultimately show ?thesis
      by (meson finite_insert fundamental_theorem_of_calculus_interior_strong insert.hyps(1) insert.prems(1) insert.prems(2) insert.prems(3))
  qed
qed

lemma at_within_closed_interval_finite:
  fixes x::real
  assumes "a < x" "x < b" "x \<notin> S" "finite S"
  shows "(at x within {a..b} - S) = at x"
proof -
  have "interior ({a..b} - S) = {a<..<b} - S"
    using \<open>finite S\<close>
    by (simp add: interior_diff finite_imp_closed)
  then show ?thesis
    using at_within_interior assms by fastforce
qed

lemma at_within_cbox_finite:
  assumes "x \<in> box a b" "x \<notin> S" "finite S"
  shows "(at x within cbox a b - S) = at x"
proof -
  have "interior (cbox a b - S) = box a b - S"
    using \<open>finite S\<close> by (simp add: interior_diff finite_imp_closed)
  then show ?thesis
    using at_within_interior assms by fastforce
qed

lemma fundamental_theorem_of_calculus_interior_stronger':
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite S"
    and "a \<le> b" "\<And>x. x \<in> {a <..< b} - S \<Longrightarrow> (f has_vector_derivative f'(x)) (at x within {a..b} - S)"
    and "continuous_on {a .. b} f"
  shows "(f' has_integral (f b - f a)) {a .. b}"
  using assms fundamental_theorem_of_calculus_interior_strong at_within_cbox_finite
    (*sledgehammer*)
  by (metis DiffD1 DiffD2 interior_atLeastAtMost_real interior_cbox interval_cbox)

lemma has_integral_substitution_general_:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes s: "finite s" and le: "a \<le> b"
    and subset: "g ` {a..b} \<subseteq> {c..d}"
    and f: "f integrable_on {c..d}" "continuous_on ({c..d} - (g ` s)) f"
    (*and f [continuous_intros]: "continuous_on {c..d} f"*)
    and g : "continuous_on {a..b} g" "inj_on g ({a..b} \<union> s)"
    and deriv [derivative_intros]:
    "\<And>x. x \<in> {a..b} - s \<Longrightarrow> (g has_field_derivative g' x) (at x within {a..b})"
  shows "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (integral {g a..g b} f - integral {g b..g a} f)) {a..b}"
proof -
  let ?F = "\<lambda>x. integral {c..g x} f"
  have cont_int: "continuous_on {a..b} ?F"
    by (rule continuous_on_compose2[OF _ g(1) subset] indefinite_integral_continuous_1
        f)+
  have deriv: "\<And>x. x \<in> {a..b} - s \<Longrightarrow> (((\<lambda>x. integral {c..x} f) \<circ> g) has_vector_derivative g' x *\<^sub>R f (g x))
                 (at x within ({a..b} - s))"
    apply (rule has_vector_derivative_eq_rhs)
     apply (rule vector_diff_chain_within)
      apply (subst has_field_derivative_iff_has_vector_derivative [symmetric])
  proof-
    fix x::real
    assume ass: "x \<in> {a..b} - s"
    let ?f'3 = "g' x"
    have i:"{a..b} - s \<subseteq> {a..b}" by auto
    have ii: " (g has_vector_derivative g' x) (at x within {a..b})" using deriv[OF ass]
      by (simp only: has_field_derivative_iff_has_vector_derivative)
    show "(g has_real_derivative ?f'3) (at x within {a..b} - s)"
      using has_vector_derivative_within_subset[OF ii i]
      by (simp only: has_field_derivative_iff_has_vector_derivative)
  next
    let ?g'3 = "f o g"
    show "\<And>x. x \<in> {a..b} - s \<Longrightarrow> ((\<lambda>x. integral {c..x} f) has_vector_derivative ?g'3 x) (at (g x) within g ` ({a..b} - s))"
    proof-
      fix x::real
      assume ass: "x \<in> {a..b} - s"
      have "finite (g ` s)" using s by auto
      then have i: "((\<lambda>x. integral {c..x} f) has_vector_derivative f(g x)) (at (g x) within ({c..d} - g ` s))"
        apply (rule integral_has_vector_derivative')
      proof-
        show " f integrable_on {c..d}" using f by auto
        show "g x \<in> {c..d} - g ` s" using ass subset
            (*sledgehammer*)
          by (smt Diff_iff Un_upper1 Un_upper2 g(2) imageE image_subset_iff inj_onD subsetCE)
        show "continuous (at (g x) within {c..d} - g ` s) f"
          (*sledgehammer*)
          using \<open>g x \<in> {c..d} - g ` s\<close> continuous_on_eq_continuous_within f(2) by blast
      qed
      have ii: "g ` ({a..b} - s) \<subseteq> ({c..d} - g ` s)"
        using subset g(2)
          (*sledgehammer*)
        by (smt Diff_subset Un_Diff Un_commute Un_upper2 inj_on_image_set_diff subset_trans sup.order_iff)
      then show "((\<lambda>x. integral {c..x} f) has_vector_derivative ?g'3 x) (at (g x) within g ` ({a..b} - s))"
        (*sledgehammer*)
        by (smt Diff_subset has_vector_derivative_weaken Un_upper1 Un_upper2 \<open>finite (g ` s)\<close> ass comp_def continuous_on_eq_continuous_within f(1) f(2) g(2) image_diff_subset image_subset_iff inj_on_image_set_diff integral_has_vector_derivative_continuous_at' subset_trans)
    qed
    show "\<And>x. x \<in> {a..b} - s \<Longrightarrow> g' x *\<^sub>R ?g'3 x = g' x *\<^sub>R f (g x)" by auto
  qed
  have deriv: "(?F has_vector_derivative g' x *\<^sub>R f (g x))
                  (at x within {a..b} - s)" if "x \<in> {a<..<b} - (s)" for x
    using deriv[of x] that by (simp add: at_within_Icc_at o_def)
  have "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (?F b - ?F a)) {a..b}"
    using cont_int
    using fundamental_theorem_of_calculus_interior_stronger'[OF s le deriv]
    by blast
  also
  from subset have "g x \<in> {c..d}" if "x \<in> {a..b}" for x using that by blast
  from this[of a] this[of b] le have cd: "c \<le> g a" "g b \<le> d" "c \<le> g b" "g a \<le> d" by auto
  have "integral {c..g b} f - integral {c..g a} f = integral {g a..g b} f - integral {g b..g a} f"
  proof cases
    assume "g a \<le> g b"
    note le = le this
    from cd have "integral {c..g a} f + integral {g a..g b} f = integral {c..g b} f"
      using integral_combine f(1) le
      by (smt atLeastatMost_subset_iff integrable_subinterval_real)
    with le show ?thesis
      by (cases "g a = g b") (simp_all add: algebra_simps)
  next
    assume less: "\<not>g a \<le> g b"
    then have "g a \<ge> g b" by simp
    note le = le this
    from cd have "integral {c..g b} f + integral {g b..g a} f = integral {c..g a} f"
      using integral_combine f(1) le
      by (smt atLeastatMost_subset_iff integrable_subinterval_real)
    with less show ?thesis
      by (simp_all add: algebra_simps)
  qed
  finally show ?thesis .
qed

lemma has_integral_substitution_general__:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes s: "finite s" and le: "a \<le> b" and s_subset: "s \<subseteq> {a..b}"
    and subset: "g ` {a..b} \<subseteq> {c..d}"
    and f: "f integrable_on {c..d}" "continuous_on ({c..d} - (g ` s)) f"
    (*and f [continuous_intros]: "continuous_on {c..d} f"*)
    and g : "continuous_on {a..b} g" "inj_on g {a..b}"
    and deriv [derivative_intros]:
    "\<And>x. x \<in> {a..b} - s \<Longrightarrow> (g has_field_derivative g' x) (at x within {a..b})"
  shows "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (integral {g a..g b} f - integral {g b..g a} f)) {a..b}"
  using s_subset has_integral_substitution_general_[OF s le subset f g(1) _ deriv]
  by (simp add: g(2) sup_absorb1)

lemma has_integral_substitution_general_':
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes s: "finite s" and le: "a \<le> b" and s': "finite s'"
    and subset: "g ` {a..b} \<subseteq> {c..d}"
    and f: "f integrable_on {c..d}" "continuous_on ({c..d} - s') f"
    and g : "continuous_on {a..b} g" "\<forall>x\<in>s'. finite (g -` {x})" "surj_on s' g" "inj_on g ({a..b} \<union> ((s \<union> g -` s')))"
    and deriv [derivative_intros]:
    "\<And>x. x \<in> {a..b} - s \<Longrightarrow> (g has_field_derivative g' x) (at x within {a..b})"
  shows "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (integral {g a..g b} f - integral {g b..g a} f)) {a..b}"
proof-
  have a: "g -` s' = \<Union>{t. \<exists>x. t = g -` {x} \<and> x \<in> s'}"
    using s s' by blast
  have "finite (\<Union>{t. \<exists>x. t = g -` {x} \<and> x \<in> s'})" using s'
    by (metis (no_types, lifting) \<open>g -` s' = \<Union>{g -` {x} |x. x \<in> s'}\<close> finite_UN_I g(2) vimage_eq_UN)
  then have 0: "finite (s \<union> (g -` s'))"
    using a s
    by simp
  have 1: "continuous_on ({c..d} - g ` (s \<union> g -` s')) f"
    using f(2) surj_on_image_vimage_eq
    by (metis Diff_mono Un_upper2 continuous_on_subset equalityE g(3) image_Un)
  have 2: " (\<And>x. x \<in> {a..b} - (s \<union> g -` s') \<Longrightarrow> (g has_real_derivative g' x) (at x within {a..b}))"
    using deriv by auto
  show ?thesis using has_integral_substitution_general_[OF 0 assms(2) subset f(1) 1 g(1) g(4) 2]
    by auto
qed

end
