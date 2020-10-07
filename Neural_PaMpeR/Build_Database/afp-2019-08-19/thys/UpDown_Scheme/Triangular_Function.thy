section \<open> Hat Functions \<close>

theory Triangular_Function
imports "HOL-Analysis.Analysis" Grid
begin

lemma continuous_on_max[continuous_intros]:
  fixes f :: "_ \<Rightarrow> 'a::linorder_topology"
  shows "continuous_on S f \<Longrightarrow> continuous_on S g \<Longrightarrow> continuous_on S (\<lambda>x. max (f x) (g x))"
  by (auto simp: continuous_on_def intro: tendsto_max)

definition \<phi> :: "(nat \<times> int) \<Rightarrow> real \<Rightarrow> real" where
  "\<phi> \<equiv> (\<lambda>(l,i) x. max 0 (1 - \<bar> x * 2^(l + 1) - real_of_int i \<bar>))"

definition \<Phi> :: "(nat \<times> int) list \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where
  "\<Phi> p x = (\<Prod>d<length p. \<phi> (p ! d) (x d))"

definition l2_\<phi> where
  "l2_\<phi> p1 p2 = (\<integral>x. \<phi> p1 x * \<phi> p2 x \<partial>lborel)"

definition l2 where
  "l2 a b = (\<integral>x. \<Phi> a x * \<Phi> b x \<partial>(\<Pi>\<^sub>M d\<in>{..<length a}. lborel))"

lemma measurable_\<phi>[measurable]: "\<phi> p \<in> borel_measurable borel"
  by (cases p) (simp add: \<phi>_def)

lemma \<phi>_nonneg: "0 \<le> \<phi> p x"
  by (simp add: \<phi>_def split: prod.split)

lemma \<phi>_zero_iff:
  "\<phi> (l,i) x = 0 \<longleftrightarrow> x \<notin> {real_of_int (i - 1) / 2^(l + 1) <..< real_of_int (i + 1) / 2^(l + 1)}"
  by (auto simp: \<phi>_def field_simps split: split_max)

lemma \<phi>_zero: "x \<notin> {real_of_int (i - 1) / 2^(l + 1) <..< real_of_int (i + 1) / 2^(l + 1)} \<Longrightarrow> \<phi> (l,i) x = 0"
  unfolding \<phi>_zero_iff by simp

lemma \<phi>_eq_0: assumes x: "x < 0 \<or> 1 < x" and i: "0 < i" "i < 2^Suc l" shows "\<phi> (l, i) x = 0"
  using x
proof
  assume "x < 0"
  also have "0 \<le> real_of_int (i - 1) / 2^(l + 1)"
    using i by (auto simp: field_simps)
  finally show ?thesis
    by (auto intro!: \<phi>_zero simp: field_simps)
next
  have "real_of_int (i + 1) / 2^(l + 1) \<le> 1"
    using i by (subst divide_le_eq_1_pos) (auto simp del: of_int_add power_Suc)
  also assume "1 < x"
  finally show ?thesis
    by (auto intro!: \<phi>_zero simp: field_simps)
qed

lemma ix_lt: "p \<in> sparsegrid dm lm \<Longrightarrow> d < dm \<Longrightarrow> ix p d < 2^(lv p d + 1)"
  unfolding sparsegrid_def lgrid_def
  using grid_estimate[of d "start dm" p "{0 ..< dm}"] by auto

lemma ix_gt: "p \<in> sparsegrid dm lm \<Longrightarrow> d < dm \<Longrightarrow> 0 < ix p d"
  unfolding sparsegrid_def lgrid_def
  using grid_estimate[of d "start dm" p "{0 ..< dm}"] by auto

lemma \<Phi>_eq_0: assumes x: "\<exists>d<length p. x d < 0 \<or> 1 < x d" and p: "p \<in> sparsegrid dm lm" shows "\<Phi> p x = 0"
  unfolding \<Phi>_def
proof (rule prod_zero)
  from x guess d ..
  with p[THEN ix_lt, of d] p[THEN ix_gt, of d] p
  show "\<exists>a\<in>{..<length p}. \<phi> (p ! a) (x a) = 0"
    apply (cases "p!d")
    apply (intro bexI[of _ d])
    apply (auto intro!: \<phi>_eq_0 simp: sparsegrid_length ix_def lv_def)
    done
qed simp

lemma \<phi>_left_support':
  "x \<in> {real_of_int (i - 1) / 2^(l + 1) .. real_of_int i / 2^(l + 1)} \<Longrightarrow> \<phi> (l,i) x = 1 + x * 2^(l + 1) - real_of_int i"
  by (auto simp: \<phi>_def field_simps split: split_max)

lemma \<phi>_left_support: "x \<in> {-1 .. 0::real} \<Longrightarrow> \<phi> (l,i) ((x + real_of_int i) / 2^(l + 1)) = 1 + x"
  by (auto simp: \<phi>_def field_simps split: split_max)

lemma \<phi>_right_support':
  "x \<in> {real_of_int i / 2^(l + 1) .. real_of_int (i + 1) / 2^(l + 1)} \<Longrightarrow> \<phi> (l,i) x = 1 - x * 2^(l + 1) + real_of_int i"
  by (auto simp: \<phi>_def field_simps split: split_max)

lemma \<phi>_right_support: 
  "x \<in> {0 .. 1::real} \<Longrightarrow> \<phi> (l,i) ((x + real i) / 2^(l + 1)) = 1 - x"
  by (auto simp: \<phi>_def field_simps split: split_max)

lemma integrable_\<phi>: "integrable lborel (\<phi> p)"
proof (induct p)
  case (Pair l i)
  have "integrable lborel (\<lambda>x. indicator {real_of_int (i - 1) / 2^(l + 1) .. real_of_int (i + 1) / 2^(l + 1)} x *\<^sub>R \<phi> (l, i) x)"
    unfolding \<phi>_def by (intro borel_integrable_compact) (auto intro!: continuous_intros)
  then show ?case
    by (rule integrable_cong[THEN iffD1, rotated -1]) (auto simp: \<phi>_zero_iff)
qed

lemma integrable_\<phi>2: "integrable lborel (\<lambda>x. \<phi> p x * \<phi> q x)"
proof (cases p q rule: prod.exhaust[case_product prod.exhaust])
  case (Pair_Pair l i l' i')
  have "integrable lborel
      (\<lambda>x. indicator {real_of_int (i - 1) / 2^(l + 1) .. real_of_int (i + 1) / 2^(l + 1)} x *\<^sub>R (\<phi> (l, i) x * \<phi> (l', i') x))"
    unfolding \<phi>_def by (intro borel_integrable_compact) (auto intro!: continuous_intros)
  then show ?thesis unfolding Pair_Pair
    by (rule integrable_cong[THEN iffD1, rotated -1]) (auto simp: \<phi>_zero_iff)
qed

lemma l2_\<phi>I_DERIV:
  assumes n: "\<And> x. x \<in> { (real_of_int i' - 1) / 2^(l' + 1) .. real_of_int i' / 2^(l' + 1) } \<Longrightarrow>
    DERIV \<Phi>_n x :> (\<phi> (l', i') x * \<phi> (l, i) x)" (is "\<And> x. x \<in> {?a..?b} \<Longrightarrow> DERIV _ _ :> ?P x")
    and p: "\<And> x. x \<in> { real_of_int i' / 2^(l' + 1) .. (real_of_int i' + 1) / 2^(l' + 1) } \<Longrightarrow>
    DERIV \<Phi>_p x :> (\<phi> (l', i') x * \<phi> (l, i) x)" (is "\<And> x. x \<in> {?b..?c} \<Longrightarrow> _")
  shows "l2_\<phi> (l', i') (l, i) = (\<Phi>_n ?b - \<Phi>_n ?a) + (\<Phi>_p ?c - \<Phi>_p ?b)"
proof -
  have "has_bochner_integral lborel
      (\<lambda>x. ?P x * indicator {?a..?b} x + ?P x * indicator {?b..?c} x)
      ((\<Phi>_n ?b - \<Phi>_n ?a) + (\<Phi>_p ?c - \<Phi>_p ?b))"
    by (intro has_bochner_integral_add has_bochner_integral_FTC_Icc_nonneg n p)
       (auto simp: \<phi>_nonneg field_simps)
  then have "has_bochner_integral lborel?P ((\<Phi>_n ?b - \<Phi>_n ?a) + (\<Phi>_p ?c - \<Phi>_p ?b))"
    by (rule has_bochner_integral_discrete_difference[where X="{?b}", THEN iffD1, rotated -1])
       (auto simp: power_add intro!: \<phi>_zero integral_cong split: split_indicator)
  then show ?thesis by (simp add: has_bochner_integral_iff l2_\<phi>_def)
qed

lemma l2_eq: "length a = length b \<Longrightarrow> l2 a b = (\<Prod>d<length a. l2_\<phi> (a!d) (b!d))"
  unfolding l2_def l2_\<phi>_def \<Phi>_def 
  apply (simp add: prod.distrib[symmetric])
proof (rule product_sigma_finite.product_integral_prod)
  show "product_sigma_finite (\<lambda>d. lborel)" ..
qed (auto intro: integrable_\<phi>2)

lemma l2_when_disjoint:
  assumes "l \<le> l'"
  defines "d == l' - l"
  assumes "(i + 1) * 2^d < i' \<or> i' < (i - 1) * 2^d" (is "?right \<or> ?left")
  shows "l2_\<phi> (l', i') (l, i) = 0"
proof -
  let ?sup = "\<lambda>l i. {real_of_int (i - 1) / 2^(l + 1) <..< real_of_int (i + 1) / 2^(l + 1)}"

  have l': "l' = l + d"
    using assms by simp
  have *: "\<And>i l. 2 ^ l = real_of_int (2 ^ l::int)"
    by simp
  have [arith]: "0 < (2^d::int)"
    by simp

  from \<open>?right \<or> ?left\<close> \<open>l \<le> l'\<close> have empty_support: "?sup l i \<inter> ?sup l' i' = {}"
    by (auto simp add: min_def max_def divide_simps l' power_add * of_int_mult[symmetric]
                simp del: of_int_diff of_int_add of_int_mult of_int_power)
       (simp_all add: field_simps)
  then have "\<And>x. \<phi> (l', i') x * \<phi> (l, i) x = 0"
    unfolding \<phi>_zero_iff mult_eq_0_iff by blast
  then show ?thesis
    by (simp add: l2_\<phi>_def del: mult_eq_0_iff vector_space_over_itself.scale_eq_0_iff)
qed

lemma l2_commutative: "l2_\<phi> p q = l2_\<phi> q p"
  by (simp add: l2_\<phi>_def mult.commute)

lemma l2_when_same: "l2_\<phi> (l, i) (l, i) = 1/3 / 2^l"
proof (subst l2_\<phi>I_DERIV)
  let ?l = "(2 :: real)^(l + 1)"
  let ?in = "real_of_int i - 1"
  let ?ip = "real_of_int i + 1"
  let ?\<phi> = "\<phi> (l,i)"
  let ?\<phi>2 = "\<lambda>x. ?\<phi> x * ?\<phi> x"

  { fix x assume "x \<in> {?in / ?l .. real_of_int i / ?l}"
    hence \<phi>_eq: "?\<phi> x = ?l * x  - ?in" using \<phi>_left_support' by auto
    show "DERIV (\<lambda>x. x^3 / 3 * ?l^2 + x * ?in^2 - x^2/2 * 2 * ?l * ?in) x :> ?\<phi>2 x"
      by (auto intro!: derivative_eq_intros simp add: power2_eq_square field_simps \<phi>_eq) }

  { fix x assume "x \<in> {real_of_int i / ?l .. ?ip / ?l}"
    hence \<phi>_eq: "?\<phi> x = ?ip - ?l * x" using \<phi>_right_support' by auto
    show "DERIV (\<lambda>x. x^3 / 3 * ?l^2 + x * ?ip^2 - x^2/2 * 2 * ?l * ?ip) x :> ?\<phi>2 x"
      by (auto intro!: derivative_eq_intros simp add: power2_eq_square field_simps \<phi>_eq) }
qed (simp_all add: field_simps power_eq_if[of _ 2] power_eq_if[of _ 3])

lemma l2_when_left_child:
  assumes "l < l'"
  and i'_bot: "i' > (i - 1) * 2^(l' - l)"
  and i'_top: "i' < i * 2^(l' - l)"
  shows "l2_\<phi> (l', i') (l, i) = (1 + real_of_int i' / 2^(l' - l) - real_of_int i) / 2^(l' + 1)"
proof (subst l2_\<phi>I_DERIV)
  let ?l' = "(2 :: real)^(l' + 1)"
  let ?in' = "real_of_int i' - 1"
  let ?ip' = "real_of_int i' + 1"
  let ?l = "(2 :: real)^(l + 1)"
  let ?i = "real_of_int i - 1"
  let ?\<phi>' = "\<phi> (l',i')"
  let ?\<phi> = "\<phi> (l, i)"
  let "?\<phi>2 x" = "?\<phi>' x * ?\<phi> x"
  define \<Phi>_n where "\<Phi>_n x = x^3 / 3 * ?l' * ?l + x * ?i * ?in' - x^2 / 2 * (?in' * ?l + ?i * ?l')" for x
  define \<Phi>_p where "\<Phi>_p x = x^2 / 2 * (?ip' * ?l + ?i * ?l') - x^3 / 3 * ?l' * ?l - x * ?i * ?ip'" for x

  have level_diff: "2^(l' - l) = 2^l' / (2^l :: real)" using power_diff[of "2::real" l l'] \<open>l < l'\<close> by auto

  { fix x assume x: "x \<in> {?in' / ?l' .. ?ip' / ?l'}"
    have "?i * 2^(l' - l) \<le> ?in'"
      using i'_bot int_less_real_le by auto
    hence "?i / ?l \<le> ?in' / ?l'"
      using level_diff by (auto simp: field_simps)
    hence "?i / ?l \<le> x" using x by auto
    moreover
    have "?ip' \<le> real_of_int i * 2^(l' - l)"
      using i'_top int_less_real_le by auto
    hence ip'_le_i: "?ip' / ?l' \<le> real_of_int i / ?l"
      using level_diff by (auto simp: field_simps)
    hence "x \<le> real_of_int i / ?l" using x by auto
    ultimately have "?\<phi> x = ?l * x  - ?i" using \<phi>_left_support' by auto
  } note \<phi>_eq = this

  { fix x assume x: "x \<in> {?in' / ?l' .. real_of_int i' / ?l'}"
    hence \<phi>'_eq: "?\<phi>' x = ?l' * x  - ?in'" using \<phi>_left_support' by auto
    from x have x': "x \<in> {?in' / ?l' .. ?ip' / ?l'}" by (auto simp add: field_simps)
    show "DERIV \<Phi>_n x :> ?\<phi>2 x" unfolding \<phi>_eq[OF x'] \<phi>'_eq \<Phi>_n_def
      by (auto intro!: derivative_eq_intros simp add: power2_eq_square algebra_simps) }

  { fix x assume x: "x \<in> {real_of_int i' / ?l' .. ?ip' / ?l'}"
    hence \<phi>'_eq: "?\<phi>' x = ?ip' - ?l' * x" using \<phi>_right_support' by auto
    from x have x': "x \<in> {?in' / ?l' .. ?ip' / ?l'}" by (simp add: field_simps)
    show "DERIV \<Phi>_p x :> ?\<phi>2 x" unfolding \<phi>_eq[OF x'] \<phi>'_eq \<Phi>_p_def
      by (auto intro!: derivative_eq_intros simp add: power2_eq_square algebra_simps) }
qed (simp_all add: field_simps power_eq_if[of _ 2] power_eq_if[of _ 3] power_diff[of "2::real", OF _ \<open>l < l'\<close>[THEN less_imp_le]] )

lemma l2_when_right_child:
  assumes "l < l'"
  and i'_bot: "i' > i * 2^(l' - l)"
  and i'_top: "i' < (i + 1) * 2^(l' - l)"
  shows "l2_\<phi> (l', i') (l, i) = (1 - real_of_int i' / 2^(l' - l) + real_of_int i) / 2^(l' + 1)"
proof (subst l2_\<phi>I_DERIV)
  let ?l' = "(2 :: real)^(l' + 1)"
  let ?in' = "real_of_int i' - 1"
  let ?ip' = "real_of_int i' + 1"
  let ?l = "(2 :: real)^(l + 1)"
  let ?i = "real_of_int i + 1"
  let ?\<phi>' = "\<phi> (l',i')"
  let ?\<phi> = "\<phi> (l, i)"
  let ?\<phi>2 = "\<lambda>x. ?\<phi>' x * ?\<phi> x"
  define \<Phi>_n where "\<Phi>_n x = x^2 / 2 * (?in' * ?l + ?i * ?l') - x^3 / 3 * ?l' * ?l - x * ?i * ?in'" for x
  define \<Phi>_p where "\<Phi>_p x = x^3 / 3 * ?l' * ?l + x * ?i * ?ip' - x^2 / 2 * (?ip' * ?l + ?i * ?l')" for x

  have level_diff: "2^(l' - l) = 2^l' / (2^l :: real)" using power_diff[of "2::real" l l'] \<open>l < l'\<close> by auto

  { fix x assume x: "x \<in> {?in' / ?l' .. ?ip' / ?l'}"
    have "real_of_int i * 2^(l' - l) \<le> ?in'"
      using i'_bot int_less_real_le by auto
    hence "real_of_int i / ?l \<le> ?in' / ?l'"
      using level_diff by (auto simp: field_simps)
    hence "real_of_int i / ?l \<le> x" using x by auto
    moreover
    have "?ip' \<le> ?i * 2^(l' - l)"
      using i'_top int_less_real_le by auto
    hence ip'_le_i: "?ip' / ?l' \<le> ?i / ?l"
      using level_diff by (auto simp: field_simps)
    hence "x \<le> ?i / ?l" using x by auto
    ultimately have "?\<phi> x = ?i - ?l * x" using \<phi>_right_support' by auto
  } note \<phi>_eq = this

  { fix x assume x: "x \<in> {?in' / ?l' .. real_of_int i' / ?l'}"
    hence \<phi>'_eq: "?\<phi>' x = ?l' * x  - ?in'" using \<phi>_left_support' by auto

    from x have x': "x \<in> {?in' / ?l' .. ?ip' / ?l'}" by (simp add: field_simps)
    show "DERIV \<Phi>_n x :> ?\<phi>2 x" unfolding \<Phi>_n_def \<phi>_eq[OF x'] \<phi>'_eq
      by (auto intro!: derivative_eq_intros simp add: simp add: power2_eq_square algebra_simps) }

  { fix x assume x: "x \<in> {real_of_int i' / ?l' .. ?ip' / ?l'}"
    hence \<phi>'_eq: "?\<phi>' x = ?ip' - ?l' * x" using \<phi>_right_support' by auto
    from x have x': "x \<in> {?in' / ?l' .. ?ip' / ?l'}" by (auto simp: field_simps)
    show "DERIV \<Phi>_p x :> ?\<phi>2 x" unfolding \<phi>_eq[OF x'] \<phi>'_eq \<Phi>_p_def
      by (auto intro!: derivative_eq_intros simp add: power2_eq_square algebra_simps) }
qed (simp_all add: field_simps power_eq_if[of _ 2] power_eq_if[of _ 3] power_diff[of "2::real", OF _ \<open>l < l'\<close>[THEN less_imp_le]] )

lemma level_shift: "lc > l \<Longrightarrow> (x :: real) / 2 ^ (lc - Suc l) = x * 2 / 2 ^ (lc - l)"
  by (auto simp add: power_diff)

lemma l2_child: assumes "d < length b"
  and p_grid: "p \<in> grid (child b dir d) ds" (is "p \<in> grid ?child ds")
  shows "l2_\<phi> (p ! d) (b ! d) = (1 - real_of_int (sgn dir) * (real_of_int (ix p d) / 2^(lv p d - lv b d) - real_of_int (ix b d))) /
                                 2^(lv p d + 1)"
proof -
  have "lv ?child d \<le> lv p d" using \<open>d < length b\<close> and p_grid
    using grid_single_level by auto
  hence "lv b d < lv p d" using \<open>d < length b\<close> and p_grid
    using child_lv by auto

  let ?i_c = "ix ?child d" and ?l_c = "lv ?child d"
  let ?i_p = "ix p d" and ?l_p = "lv p d"
  let ?i_b = "ix b d" and ?l_b = "lv b d"

  have "(2::int) * 2^(?l_p - ?l_c) = 2^Suc (?l_p - ?l_c)" by auto
  also have "\<dots> = 2^(Suc ?l_p - ?l_c)"
  proof -
    have "Suc (?l_p - ?l_c) = Suc ?l_p - ?l_c"
      using \<open>lv ?child d \<le> lv p d\<close> by auto
    thus ?thesis by auto
  qed
  also have "\<dots> = 2^(?l_p - ?l_b)"
    using \<open>d < length b\<close> and \<open>lv b d < lv p d\<close>
    by (auto simp add: child_def lv_def)
  finally have level: "2^(?l_p - ?l_b) = (2::int) * 2^(?l_p - ?l_c)" ..

  from \<open>d < length b\<close> and p_grid
  have range_left: "?i_p > (?i_c - 1) * 2^(?l_p - ?l_c)" and
       range_right: "?i_p < (?i_c + 1) * 2^(?l_p - ?l_c)"
    using grid_estimate by auto

  show ?thesis
  proof (cases dir)
    case left
    with child_ix_left[OF \<open>d < length b\<close>]
    have "(?i_b - 1) * 2^(?l_p - ?l_b) = (?i_c - 1) * 2^(?l_p - ?l_c)" and
      "?i_b * 2^(?l_p - ?l_b) = (?i_c + 1) * 2^(?l_p - ?l_c)" using level by auto
    hence "?i_p > (?i_b - 1) * 2^(?l_p - ?l_b)" and
      "?i_p < ?i_b * 2^(?l_p - ?l_b)"
      using range_left and range_right by auto
    with \<open>?l_b < ?l_p\<close>
    have "l2_\<phi> (?l_p, ?i_p) (?l_b, ?i_b) =
          (1 + real_of_int ?i_p / 2^(?l_p - ?l_b) - real_of_int ?i_b) / 2^(?l_p + 1)"
      by (rule l2_when_left_child)
    thus ?thesis using left by (auto simp add: ix_def lv_def)
  next
    case right
    hence "?i_c = 2 * ?i_b + 1" using child_ix_right and \<open>d < length b\<close> by auto
    hence "?i_b * 2^(?l_p - ?l_b) = (?i_c - 1) * 2^(?l_p - ?l_c)" and
      "(?i_b + 1) * 2^(?l_p - ?l_b) = (?i_c + 1) * 2^(?l_p - ?l_c)" using level by auto
    hence "?i_p > ?i_b * 2^(?l_p - ?l_b)" and
      "?i_p < (?i_b + 1) * 2^(?l_p - ?l_b)"
      using range_left and range_right by auto
    with \<open>?l_b < ?l_p\<close>
    have "l2_\<phi> (?l_p, ?i_p) (?l_b, ?i_b) =
          (1 - real_of_int ?i_p / 2^(?l_p - ?l_b) + real_of_int ?i_b) / 2^(?l_p + 1)"
      by (rule l2_when_right_child)
    thus ?thesis using right by (auto simp add: ix_def lv_def)
  qed
qed

lemma l2_same: "l2_\<phi> (p!d) (p!d) = 1/3 / 2^(lv p d)"
proof -
  have "l2_\<phi> (p!d) (p!d) = l2_\<phi> (lv p d, ix p d) (lv p d, ix p d)"
    by (auto simp add: lv_def ix_def)
  thus ?thesis using l2_when_same by auto
qed

lemma l2_disjoint: assumes "d < length b" and "p \<in> grid b {d}" and "p' \<in> grid b {d}"
  and "p' \<notin> grid p {d}" and "lv p' d \<ge> lv p d"
  shows "l2_\<phi> (p' ! d) (p ! d) = 0"
proof -
  have range: "ix p' d > (ix p d + 1) * 2^(lv p' d - lv p d) \<or> ix p' d < (ix p d - 1) * 2^(lv p' d - lv p d)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "ix p' d \<le> (ix p d + 1) * 2^(lv p' d - lv p d)" and "ix p' d \<ge> (ix p d - 1) * 2^(lv p' d - lv p d)" by auto
    with \<open>p' \<in> grid b {d}\<close> and \<open>p \<in> grid b {d}\<close> and \<open>lv p' d \<ge> lv p d\<close> and \<open>d < length b\<close>
    have "p' \<in> grid p {d}" using grid_part[where p=p and b=b and d=d and p'=p'] by auto
    with \<open>p' \<notin> grid p {d}\<close> show False by auto
  qed

  have "l2_\<phi> (p' ! d) (p ! d) = l2_\<phi> (lv p' d, ix p' d) (lv p d, ix p d)" by (auto simp add: ix_def lv_def)
  also have "\<dots> = 0" using range and \<open>lv p' d \<ge> lv p d\<close> and l2_when_disjoint by auto
  finally show ?thesis .
qed

lemma l2_down2:
  fixes pc pd p
  assumes "d < length pd"
  assumes pc_in_grid: "pc \<in> grid (child pd dir d) {d}"
  assumes pd_is_child: "pd = child p dir d" (is "pd = ?pd")
  shows "l2_\<phi> (pc ! d) (pd ! d) / 2 = l2_\<phi> (pc ! d) (p ! d)"
proof -
  have "d < length p" using pd_is_child \<open>d < length pd\<close> by auto

  moreover
  have "pc \<in> grid ?pd {d}" using pd_is_child and grid_child and pc_in_grid by auto
  hence "lv p d < lv pc d" using grid_child_level and \<open>d < length pd\<close> and pd_is_child by auto

  moreover
  have "real_of_int (sgn dir) * real_of_int (sgn dir) = 1" by (cases dir, auto)

  ultimately show ?thesis
    unfolding l2_child[OF \<open>d < length pd\<close> pc_in_grid]
              l2_child[OF \<open>d < length p\<close> \<open>pc \<in> grid ?pd {d}\<close>]
    using child_lv and child_ix and pd_is_child and level_shift
    by (auto simp add: algebra_simps diff_divide_distrib add_divide_distrib)
qed

lemma l2_zigzag:
  assumes "d < length p" and p_child: "p = child p_p dir d"
  and p'_grid: "p' \<in> grid (child p (inv dir) d) {d}"
  and ps_intro: "child p (inv dir) d = child ps dir d" (is "?c_p = ?c_ps")
  shows "l2_\<phi> (p' ! d) (p_p ! d) = l2_\<phi> (p' ! d) (ps ! d) + l2_\<phi> (p' ! d) (p ! d) / 2"
proof -
  have "length p = length ?c_p" by auto
  also have "\<dots> = length ?c_ps" using ps_intro by auto
  finally have "length p = length ps" using ps_intro by auto
  hence "d < length p_p" using p_child and \<open>d < length p\<close> by auto

  moreover
  from ps_intro have "ps = p[d := (lv p d, ix p d - sgn dir)]" by (rule child_neighbour)
  hence "lv ps d = lv p d" and "real_of_int (ix ps d) = real_of_int (ix p d) - real_of_int (sgn dir)"
    using lv_def and ix_def and \<open>length p = length ps\<close> and \<open>d < length p\<close> by auto

  moreover
  have "d < length ps" and *: "p' \<in> grid (child ps dir d) {d}"
    using p'_grid ps_intro \<open>length p = length ps\<close> \<open>d < length p\<close> by auto

  have "p' \<in> grid p {d}" using p'_grid and grid_child by auto
  hence p_p_grid: "p' \<in> grid (child p_p dir d) {d}" using p_child by auto
  hence "lv p' d > lv p_p d" using grid_child_level and \<open>d < length p_p\<close> by auto

  moreover
  have "real_of_int (sgn dir) * real_of_int (sgn dir) = 1" by (cases dir, auto)

  ultimately show ?thesis
    unfolding l2_child[OF \<open>d < length p\<close> p'_grid] l2_child[OF \<open>d < length ps\<close> *]
              l2_child[OF \<open>d < length p_p\<close> p_p_grid]
    using child_lv and child_ix and p_child level_shift
    by (auto simp add: add_divide_distrib algebra_simps diff_divide_distrib)
qed

end
