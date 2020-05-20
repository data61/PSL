section\<open>Square integrable functions over the reals\<close>

theory Square_Integrable
  imports Lspace 
begin

subsection\<open>Basic definitions\<close>

definition square_integrable:: "(real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> bool" (infixr "square'_integrable" 46)
  where "f square_integrable S \<equiv> S \<in> sets lebesgue \<and> f \<in> borel_measurable (lebesgue_on S) \<and> integrable (lebesgue_on S) (\<lambda>x. f x ^ 2)"

lemma square_integrable_imp_measurable:
   "f square_integrable S \<Longrightarrow> f \<in> borel_measurable (lebesgue_on S)"
  by (simp add: square_integrable_def)

lemma square_integrable_imp_lebesgue:
   "f square_integrable S \<Longrightarrow> S \<in> sets lebesgue"
  by (simp add: square_integrable_def)

lemma square_integrable_imp_lspace:
  assumes "f square_integrable S" shows "f \<in> lspace (lebesgue_on S) 2"
proof -
  have "(\<lambda>x. (f x)\<^sup>2) absolutely_integrable_on S"
    by (metis assms integrable_on_lebesgue_on nonnegative_absolutely_integrable_1 square_integrable_def zero_le_power2)
  moreover have "S \<in> sets lebesgue"
    using assms square_integrable_def by blast
  ultimately show ?thesis
    by (simp add: assms Lp_space_numeral integrable_restrict_space set_integrable_def square_integrable_imp_measurable)
qed

lemma square_integrable_iff_lspace:
  assumes "S \<in> sets lebesgue"
  shows "f square_integrable S \<longleftrightarrow> f \<in> lspace (lebesgue_on S) 2" (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then show ?rhs
    using square_integrable_imp_lspace by blast
next
  assume ?rhs then show ?lhs
  using assms by (auto simp: Lp_space_numeral square_integrable_def integrable_on_lebesgue_on)
qed

lemma square_integrable_0 [simp]:
   "S \<in> sets lebesgue \<Longrightarrow> (\<lambda>x. 0) square_integrable S"
  by (simp add: square_integrable_def power2_eq_square integrable_0)

lemma square_integrable_neg_eq [simp]:
   "(\<lambda>x. -(f x)) square_integrable S \<longleftrightarrow> f square_integrable S"
  by (auto simp: square_integrable_def)

lemma square_integrable_lmult [simp]:
  assumes "f square_integrable S"
  shows "(\<lambda>x. c * f x) square_integrable S"
proof (simp add: square_integrable_def, intro conjI)
  have f: "f \<in> borel_measurable (lebesgue_on S)" "integrable (lebesgue_on S) (\<lambda>x. f x ^ 2)"
    using assms by (simp_all add: square_integrable_def)
  then show "(\<lambda>x. c * f x) \<in> borel_measurable (lebesgue_on S)"
    using borel_measurable_scaleR [of "\<lambda>x. c" "lebesgue_on S" f]  by simp
  have "integrable (lebesgue_on S) (\<lambda>x. c\<^sup>2 * (f x)\<^sup>2)"
  by (cases "c=0") (auto simp: f integrable_0)
  then show "integrable (lebesgue_on S) (\<lambda>x. (c * f x)\<^sup>2)"
    by (simp add: power2_eq_square mult_ac)
  show "S \<in> sets lebesgue"
    using assms square_integrable_def by blast
qed

lemma square_integrable_rmult [simp]:
   "f square_integrable S \<Longrightarrow> (\<lambda>x. f x * c) square_integrable S"
  using square_integrable_lmult [of f S c] by (simp add: mult.commute)

lemma square_integrable_imp_absolutely_integrable_product:
  assumes f: "f square_integrable S" and g: "g square_integrable S"
  shows "(\<lambda>x. f x * g x) absolutely_integrable_on S"
proof -
  have fS: "integrable (lebesgue_on S) (\<lambda>r. (f r)\<^sup>2)" "integrable (lebesgue_on S) (\<lambda>r. (g r)\<^sup>2)"
    using assms square_integrable_def by blast+
  have "integrable (lebesgue_on S) (\<lambda>x. \<bar>f x * g x\<bar>)"
  proof (intro integrable_abs Holder_inequality [of 2 2])
    show "f \<in> borel_measurable (lebesgue_on S)" "g \<in> borel_measurable (lebesgue_on S)"
      using f g square_integrable_def by blast+
    show "integrable (lebesgue_on S) (\<lambda>x. \<bar>f x\<bar> powr 2)" "integrable (lebesgue_on S) (\<lambda>x. \<bar>g x\<bar> powr 2)"
      using nonnegative_absolutely_integrable_1 [of "(\<lambda>x. (f x)\<^sup>2)"] nonnegative_absolutely_integrable_1 [of "(\<lambda>x. (g x)\<^sup>2)"]
      by (simp_all add: fS integrable_restrict_space set_integrable_def)
  qed auto
  then show ?thesis
    using assms
    by (simp add: absolutely_integrable_measurable_real borel_measurable_times square_integrable_def)
qed

lemma square_integrable_imp_integrable_product:
  assumes "f square_integrable S" "g square_integrable S"
  shows  "integrable (lebesgue_on S) (\<lambda>x. f x * g x)"
  using absolutely_integrable_measurable assms integrable_abs_iff
  by (metis (full_types) absolutely_integrable_measurable_real square_integrable_def square_integrable_imp_absolutely_integrable_product)

lemma square_integrable_add [simp]:
  assumes f: "f square_integrable S" and g: "g square_integrable S"
  shows "(\<lambda>x. f x + g x) square_integrable S"
  unfolding square_integrable_def
proof (intro conjI)
  show "S \<in> sets lebesgue"
    using assms square_integrable_def by blast
  show "(\<lambda>x. f x + g x) \<in> borel_measurable (lebesgue_on S)"
    by (simp add: f g borel_measurable_add square_integrable_imp_measurable)
  show "integrable (lebesgue_on S) (\<lambda>x. (f x + g x)\<^sup>2)"
    unfolding power2_eq_square distrib_right distrib_left
  proof (intro Bochner_Integration.integrable_add)
    show "integrable (lebesgue_on S) (\<lambda>x. f x * f x)" "integrable (lebesgue_on S) (\<lambda>x. g x * g x)"
      using f g square_integrable_imp_integrable_product by blast+
    show "integrable (lebesgue_on S) (\<lambda>x. f x * g x)" "integrable (lebesgue_on S) (\<lambda>x. g x * f x)"
      using f g square_integrable_imp_integrable_product by blast+
  qed
qed

lemma square_integrable_diff [simp]:
   "\<lbrakk>f square_integrable S; g square_integrable S\<rbrakk> \<Longrightarrow> (\<lambda>x. f x - g x) square_integrable S"
  using square_integrable_neg_eq square_integrable_add [of f S "\<lambda>x. - (g x)"] by auto

lemma square_integrable_abs [simp]:
   "f square_integrable S \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) square_integrable S"
  by (simp add: square_integrable_def borel_measurable_abs)

lemma square_integrable_sum [simp]:
  assumes I: "finite I" "\<And>i. i \<in> I \<Longrightarrow> f i square_integrable S" and S: "S \<in> sets lebesgue"
  shows "(\<lambda>x. \<Sum>i\<in>I. f i x) square_integrable S"
  using I by induction (simp_all add: S)

lemma continuous_imp_square_integrable [simp]:
   "continuous_on {a..b} f \<Longrightarrow> f square_integrable {a..b}"
  using continuous_imp_integrable [of a b "(\<lambda>x. (f x)\<^sup>2)"]
  by (simp add: square_integrable_def continuous_on_power continuous_imp_measurable_on_sets_lebesgue)

lemma square_integrable_imp_absolutely_integrable:
  assumes f: "f square_integrable S" and S: "S \<in> lmeasurable"
  shows "f absolutely_integrable_on S"
proof -
  have "f \<in> lspace (lebesgue_on S) 2"
    using f S square_integrable_iff_lspace by blast
  then have "f \<in> lspace (lebesgue_on S) 1"
    by (rule lspace_mono) (use S in auto)
  then show ?thesis
    using S by (simp flip: lspace_1)
qed

lemma square_integrable_imp_integrable:
  assumes f: "f square_integrable S" and S: "S \<in> lmeasurable"
  shows "integrable (lebesgue_on S) f"
  by (meson S absolutely_integrable_measurable_real f fmeasurableD integrable_abs_iff square_integrable_imp_absolutely_integrable)

subsection\<open> The norm and inner product in L2\<close>

definition l2product :: "'a::euclidean_space set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real"
  where "l2product S f g \<equiv> (\<integral>x. f x * g x \<partial>(lebesgue_on S))"

definition l2norm :: "['a::euclidean_space set, 'a \<Rightarrow> real] \<Rightarrow> real"
  where "l2norm S f \<equiv> sqrt (l2product S f f)"

definition lnorm :: "['a measure, real, 'a \<Rightarrow> real] \<Rightarrow> real"
  where "lnorm M p f \<equiv> (\<integral>x. \<bar>f x\<bar> powr p \<partial>M) powr (1/p)"

corollary Holder_inequality_lnorm:
  assumes "p > (0::real)" "q > 0" "1/p+1/q = 1"
      and "f \<in> borel_measurable M" "g \<in> borel_measurable M"
          "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)"
          "integrable M (\<lambda>x. \<bar>g x\<bar> powr q)"
  shows "(\<integral>x. \<bar>f x * g x\<bar> \<partial>M) \<le> lnorm M p f * lnorm M q g"
        "\<bar>\<integral>x. f x * g x \<partial>M \<bar> \<le> lnorm M p f * lnorm M q g"
  by (simp_all add: Holder_inequality assms lnorm_def)

lemma l2norm_lnorm: "l2norm S f = lnorm (lebesgue_on S) 2 f"
proof -
  have "(LINT x|lebesgue_on S. (f x)\<^sup>2) \<ge> 0"
    by simp
  then show ?thesis
    by (auto simp: lnorm_def l2norm_def l2product_def power2_eq_square powr_half_sqrt)
qed

lemma lnorm_nonneg: "lnorm M p f \<ge> 0"
  by (simp add: lnorm_def)

lemma lnorm_minus_commute: "lnorm M p (g - f) = lnorm M p (f - g)"
  by (simp add: lnorm_def abs_minus_commute)


text\<open> Extending a continuous function in a periodic way\<close>

proposition continuous_on_compose_frac:
  fixes f:: "real \<Rightarrow> real"
  assumes contf: "continuous_on {0..1} f" and f10: "f 1 = f 0"
  shows "continuous_on UNIV (f \<circ> frac)"
proof -
  have *: "isCont (f \<circ> frac) x"
    if caf: "\<And>x. \<lbrakk>0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> continuous (at x within {0..1}) f" for x
  proof (cases "x \<in> \<int>")
    case True
    then have [simp]: "frac x = 0"
      by simp
    show ?thesis
    proof (clarsimp simp add: continuous_at_eps_delta dist_real_def)
      have f0: "continuous (at 0 within {0..1}) f" and f1: "continuous (at 1 within {0..1}) f"
        by (auto intro: caf)
      show "\<exists>d>0. \<forall>x'. \<bar>x'-x\<bar> < d \<longrightarrow> \<bar>f(frac x') - f 0\<bar> < e"
        if "0 < e" for e
      proof -
        obtain d0 where "d0 > 0" and d0: "\<And>x'. \<lbrakk>x'\<in>{0..1}; \<bar>x'\<bar> < d0\<rbrakk> \<Longrightarrow> \<bar>f x' - f 0\<bar> < e"
          using \<open>e > 0\<close> caf [of 0] dist_not_less_zero
          by (auto simp: continuous_within_eps_delta dist_real_def)
        obtain d1 where "d1 > 0" and d1: "\<And>x'. \<lbrakk>x'\<in>{0..1}; \<bar>x' - 1\<bar> < d1\<rbrakk> \<Longrightarrow> \<bar>f x' - f 0\<bar> < e"
          using \<open>e > 0\<close> caf [of 1] dist_not_less_zero f10
          by (auto simp: continuous_within_eps_delta dist_real_def)
        show ?thesis
        proof (intro exI conjI allI impI)
          show "0 < min 1 (min d0 d1)"
            by (auto simp: \<open>d0 > 0\<close> \<open>d1 > 0\<close>)
          show "\<bar>f(frac x') - f 0\<bar> < e"
            if "\<bar>x'-x\<bar> < min 1 (min d0 d1)" for x'
          proof (cases "x \<le> x'")
            case True
            with \<open>x \<in> \<int>\<close> that have "frac x' = x' - x"
              by (simp add: frac_unique_iff)
            then show ?thesis
              using True d0 that by auto
          next
            case False
            then have [simp]: "frac x' = 1 - (x - x')"
              using that \<open>x \<in> \<int>\<close> by (simp add: not_le frac_unique_iff)
            show ?thesis
              using False d1 that by auto
          qed
        qed
      qed
    qed
  next
    case False
    show ?thesis
    proof (rule continuous_at_compose)
      show "isCont frac x"
        by (simp add: False continuous_frac)
      have "frac x \<in> {0<..<1}"
        by (simp add: False frac_lt_1)
      then show "isCont f(frac x)"
        by (metis at_within_Icc_at greaterThanLessThan_iff le_cases not_le that)
    qed
  qed
  then show ?thesis
    using contf by (simp add: o_def continuous_on_eq_continuous_within)
qed


proposition Tietze_periodic_interval:
  fixes f:: "real \<Rightarrow> real"
  assumes contf: "continuous_on {a..b} f" and fab: "f a = f b"
  obtains g where "continuous_on UNIV g" "\<And>x. x \<in> {a..b} \<Longrightarrow> g x = f x"
                  "\<And>x. g(x + (b-a)) = g x"
proof (cases "a < b")
  case True
  let ?g = "f \<circ> (\<lambda>y. a + (b-a) * y) \<circ> frac \<circ>
                (\<lambda>x. (x - a) / (b-a))"
  show ?thesis
  proof
    have "a + (b - a) * y \<le> b" if "a < b" "0 \<le> y" "y \<le> 1" for y
      using that affine_ineq by (force simp: field_simps)
    then have *: "continuous_on (range (\<lambda>x. (x - a) / (b - a))) (f \<circ> (\<lambda>y. a + (b - a) * y) \<circ> frac)"
      apply (intro continuous_on_subset [OF continuous_on_compose_frac] continuous_on_subset [OF contf]
          continuous_intros)
      using \<open>a < b\<close>
      by (auto simp: fab)
    show "continuous_on UNIV ?g"
      by (intro * continuous_on_compose continuous_intros) (use True in auto)
    show "?g x = f x" if "x \<in> {a..b}" for x :: real
    proof (cases "x=b")
      case True
      then show ?thesis
        by (auto simp: frac_def intro: fab)
    next
      case False
      with \<open>a < b\<close> that have "frac ((x - a) / (b - a)) = (x - a) / (b - a)"
        by (subst frac_eq) (auto simp: divide_simps)
      with \<open>a < b\<close> show ?thesis
        by auto
    qed
    have "a + (b-a) * frac ((x + b - 2 * a) / (b-a)) = a + (b-a) * frac ((x - a) / (b-a))" for x
      using True frac_1_eq [of "(x - a) / (b-a)"] by (auto simp: divide_simps)
    then show "?g (x + (b-a)) = (?g x::real)" for x
      by force
  qed
next
  case False
  show ?thesis
  proof
    show "f a = f x" if "x \<in> {a..b}" for x
      using that False order_trans by fastforce
  qed auto
qed


subsection\<open>Lspace stuff\<close>

lemma eNorm_triangle_eps:
  assumes "eNorm N (x' - x) < a" "defect N = 1"
  obtains e where "e > 0" "\<And>y. eNorm N (y - x') < e \<Longrightarrow> eNorm N (y - x) < a"
proof -
  let ?d = "a - Norm N (x' - x)"
  have nt: "eNorm N (x' - x) < \<top>"
    using assms top.not_eq_extremum by fastforce
  with assms have d: "?d > 0"
    by (simp add: Norm_def diff_gr0_ennreal)
  have [simp]: "ennreal (1 - Norm N (x' - x)) = 1 - eNorm N (x' - x)"
    using that nt  unfolding Norm_def  by (metis enn2real_nonneg ennreal_1 ennreal_enn2real ennreal_minus)
  show ?thesis
  proof
    show "(0::ennreal) < ?d"
      using d ennreal_less_zero_iff by blast
    show "eNorm N (y - x) < a"
      if "eNorm N (y - x') < ?d" for y
      using that assms eNorm_triangular_ineq [of N "y - x'" "x' - x"] le_less_trans less_diff_eq_ennreal
      by (simp add: Norm_def nt)
  qed
qed

lemma topspace_topology\<^sub>N [simp]:
  assumes "defect N = 1" shows "topspace (topology\<^sub>N N) = UNIV"
proof -
  have "x \<in> topspace (topology\<^sub>N N)" for x
  proof -
    have "\<exists>e>0. \<forall>y. eNorm N (y - x') < e \<longrightarrow> eNorm N (y - x) < 1"
      if "eNorm N (x' - x) < 1" for x'
      using eNorm_triangle_eps
      by (metis assms that)
    then show ?thesis
      unfolding topspace_def
      by (rule_tac X="{y. eNorm N (y - x) < 1}" in UnionI) (auto intro: openin_topology\<^sub>N_I)
  qed
  then show ?thesis
    by auto
qed

lemma tendsto_ine\<^sub>N_iff_limitin:
  assumes "defect N = 1"
  shows "tendsto_ine\<^sub>N N u x = limitin (topology\<^sub>N N) u x sequentially"
proof -
  have "\<forall>\<^sub>F x in sequentially. u x \<in> U"
    if 0: "(\<lambda>n. eNorm N (u n - x)) \<longlonglongrightarrow> 0" and U: "openin (topology\<^sub>N N) U" "x \<in> U" for U
  proof -
    obtain e where "e > 0" and e: "\<And>y. eNorm N (y-x) < e \<Longrightarrow> y \<in> U"
      using openin_topology\<^sub>N_D U by metis
    then show ?thesis
      using eventually_mono order_tendstoD(2)[OF 0] by force
  qed
  moreover have "(\<lambda>n. eNorm N (u n - x)) \<longlonglongrightarrow> 0"
    if x: "x \<in> topspace (topology\<^sub>N N)"
      and *: "\<And>U. \<lbrakk>openin (topology\<^sub>N N) U; x \<in> U\<rbrakk> \<Longrightarrow> (\<forall>\<^sub>F x in sequentially. u x \<in> U)"
  proof (rule order_tendstoI)
    show "\<forall>\<^sub>F n in sequentially. eNorm N (u n - x) < a" if "a > 0" for a
      apply (rule * [OF openin_topology\<^sub>N_I, of "{v. eNorm N (v - x) < a}", simplified])
      using assms eNorm_triangle_eps that apply blast+
      done
  qed simp
  ultimately show ?thesis
    by (auto simp: tendsto_ine\<^sub>N_def limitin_def assms)
qed

corollary tendsto_ine\<^sub>N_iff_limitin_ge1:
  fixes p :: ennreal
  assumes "p \<ge> 1"
  shows "tendsto_ine\<^sub>N (\<LL> p M) u x = limitin (topology\<^sub>N (\<LL> p M)) u x sequentially"
proof (rule tendsto_ine\<^sub>N_iff_limitin)
  show "defect (\<LL> p M) = 1"
    by (metis (full_types) L_infinity(2) L_zero(2) Lp(2) Lp_cases assms ennreal_ge_1)
qed

corollary tendsto_in\<^sub>N_iff_limitin:
  assumes "defect N = 1" "x \<in> space\<^sub>N N" "\<And>n. u n \<in> space\<^sub>N N"
  shows "tendsto_in\<^sub>N N u x = limitin (topology\<^sub>N N) u x sequentially"
  using assms tendsto_ine\<^sub>N_iff_limitin tendsto_ine_in by blast

corollary tendsto_in\<^sub>N_iff_limitin_ge1:
  fixes p :: ennreal
  assumes "p \<ge> 1" "x \<in> lspace M p" "\<And>n. u n \<in> lspace M p"
  shows "tendsto_in\<^sub>N (\<LL> p M) u x = limitin (topology\<^sub>N (\<LL> p M)) u x sequentially"
proof (rule tendsto_in\<^sub>N_iff_limitin)
  show "defect (\<LL> p M) = 1"
    by (metis (full_types) L_infinity(2) L_zero(2) Lp(2) Lp_cases \<open>p \<ge> 1\<close> ennreal_ge_1)
qed (auto simp: assms)


lemma l2product_sym: "l2product S f g = l2product S g f"
  by (simp add: l2product_def mult.commute)

lemma l2product_pos_le:
   "f square_integrable S \<Longrightarrow> 0 \<le> l2product S f f"
  by (simp add: square_integrable_def l2product_def flip: power2_eq_square)

lemma l2norm_pow_2:
   "f square_integrable S \<Longrightarrow> (l2norm S f) ^ 2 = l2product S f f"
  by (simp add: l2norm_def l2product_pos_le)

lemma l2norm_pos_le:
   "f square_integrable S \<Longrightarrow> 0 \<le> l2norm S f"
  by (simp add: l2norm_def l2product_pos_le)

lemma l2norm_le: "(l2norm S f \<le> l2norm S g \<longleftrightarrow> l2product S f f \<le> l2product S g g)"
  by (simp add: l2norm_def)

lemma l2norm_eq:
   "(l2norm S f = l2norm S g \<longleftrightarrow> l2product S f f = l2product S g g)"
  by (simp add: l2norm_def)

lemma Schwartz_inequality_strong:
  assumes "f square_integrable S" "g square_integrable S"
  shows "l2product S (\<lambda>x. \<bar>f x\<bar>) (\<lambda>x. \<bar>g x\<bar>) \<le> l2norm S f * l2norm S g"
  using Holder_inequality_lnorm [of 2 2 f "lebesgue_on S" g] assms
  by (simp add: square_integrable_def l2product_def abs_mult flip: l2norm_lnorm)

lemma Schwartz_inequality_abs:
  assumes "f square_integrable S" "g square_integrable S"
  shows "\<bar>l2product S f g\<bar> \<le> l2norm S f * l2norm S g"
proof -
  have "\<bar>l2product S f g\<bar> \<le> l2product S (\<lambda>x. \<bar>f x\<bar>) (\<lambda>x. \<bar>g x\<bar>)"
    unfolding l2product_def
  proof (rule integral_abs_bound_integral)
    show "integrable (lebesgue_on S) (\<lambda>x. f x * g x)" "integrable (lebesgue_on S) (\<lambda>x. \<bar>f x\<bar> * \<bar>g x\<bar>)"
      by (simp_all add: assms square_integrable_imp_integrable_product)
  qed (simp add: abs_mult)
  also have "\<dots> \<le> l2norm S f * l2norm S g"
    by (simp add: Schwartz_inequality_strong assms)
  finally show ?thesis .
qed

lemma Schwartz_inequality:
  assumes "f square_integrable S" "g square_integrable S"
  shows "l2product S f g \<le> l2norm S f * l2norm S g"
  using Schwartz_inequality_abs assms by fastforce


lemma lnorm_triangle:
  assumes f: "f \<in> lspace M p" and g: "g \<in> lspace M p" and "p \<ge> 1"
  shows "lnorm M p (\<lambda>x. f x + g x) \<le> lnorm M p f + lnorm M p g"
proof -
  have "p > 0"
    using assms by linarith
  then have "integrable M (\<lambda>x. \<bar>f x\<bar> powr p)" "integrable M (\<lambda>x. \<bar>g x\<bar> powr p)"
    by (simp_all add: Lp_D(2) assms)
  moreover have "f \<in> borel_measurable M" "g \<in> borel_measurable M"
    using Lp_measurable f g by blast+
  ultimately show ?thesis
    unfolding lnorm_def using Minkowski_inequality(2) \<open>p \<ge> 1\<close> by blast
qed

lemma lnorm_triangle_fun:
  assumes f: "f \<in> lspace M p" and g: "g \<in> lspace M p" and "p \<ge> 1"
  shows "lnorm M p (f + g) \<le> lnorm M p f + lnorm M p g"
  using lnorm_triangle [OF assms] by (simp add: plus_fun_def)

lemma l2norm_triangle:
  assumes "f square_integrable S" "g square_integrable S"
  shows "l2norm S (\<lambda>x. f x + g x) \<le> l2norm S f + l2norm S g"
proof -
  have "f \<in> lspace (lebesgue_on S) 2" "g \<in> lspace (lebesgue_on S) 2"
    using assms by (simp_all add: square_integrable_imp_lspace)
  then show ?thesis
    using lnorm_triangle [of f 2 "lebesgue_on S"]
    by (simp add: l2norm_lnorm)
qed


lemma l2product_ladd:
   "\<lbrakk>f square_integrable S; g square_integrable S; h square_integrable S\<rbrakk>
    \<Longrightarrow> l2product S (\<lambda>x. f x + g x) h = l2product S f h + l2product S g h"
  by (simp add: l2product_def algebra_simps square_integrable_imp_integrable_product)

lemma l2product_radd:
   "\<lbrakk>f square_integrable S; g square_integrable S; h square_integrable S\<rbrakk>
    \<Longrightarrow> l2product S f(\<lambda>x. g x + h x) = l2product S f g + l2product S f h"
  by (simp add: l2product_def algebra_simps square_integrable_imp_integrable_product)

lemma l2product_ldiff:
   "\<lbrakk>f square_integrable S; g square_integrable S; h square_integrable S\<rbrakk>
    \<Longrightarrow> l2product S (\<lambda>x. f x - g x) h = l2product S f h - l2product S g h"
  by (simp add: l2product_def algebra_simps square_integrable_imp_integrable_product)

lemma l2product_rdiff:
   "\<lbrakk>f square_integrable S; g square_integrable S; h square_integrable S\<rbrakk>
    \<Longrightarrow> l2product S f(\<lambda>x. g x - h x) = l2product S f g - l2product S f h"
  by (simp add: l2product_def algebra_simps square_integrable_imp_integrable_product)

lemma l2product_lmult:
   "\<lbrakk>f square_integrable S; g square_integrable S\<rbrakk>
    \<Longrightarrow> l2product S (\<lambda>x. c * f x) g = c * l2product S f g"
  by (simp add: l2product_def algebra_simps)

lemma l2product_rmult:
   "\<lbrakk>f square_integrable S; g square_integrable S\<rbrakk>
    \<Longrightarrow> l2product S f(\<lambda>x. c * g x) = c * l2product S f g"
  by (simp add: l2product_def algebra_simps)

lemma l2product_lzero [simp]: "l2product S (\<lambda>x. 0) f = 0"
  by (simp add: l2product_def)

lemma l2product_rzero [simp]: "l2product S f(\<lambda>x. 0) = 0"
  by (simp add: l2product_def)

lemma l2product_lsum:
  assumes I: "finite I" "\<And>i. i \<in> I \<Longrightarrow> (f i) square_integrable S" and S: "g square_integrable S"
  shows "l2product S (\<lambda>x. \<Sum>i\<in>I. f i x) g = (\<Sum>i\<in>I. l2product S (f i) g)"
  using I
proof induction
  case (insert i I)
  with S show ?case
    by (simp add: l2product_ladd square_integrable_imp_lebesgue)
qed auto

lemma l2product_rsum:
  assumes I: "finite I" "\<And>i. i \<in> I \<Longrightarrow> (f i) square_integrable S" and S: "g square_integrable S"
  shows "l2product S g (\<lambda>x. \<Sum>i\<in>I. f i x) = (\<Sum>i\<in>I. l2product S g (f i))"
  using l2product_lsum [OF assms] by (simp add: l2product_sym)

lemma l2norm_lmult:
   "f square_integrable S \<Longrightarrow> l2norm S (\<lambda>x. c * f x) = \<bar>c\<bar> * l2norm S f"
  by (simp add: l2norm_def l2product_rmult l2product_sym real_sqrt_mult)

lemma l2norm_rmult:
   "f square_integrable S \<Longrightarrow> l2norm S (\<lambda>x. f x * c) = l2norm S f * \<bar>c\<bar>"
  using l2norm_lmult by (simp add: mult.commute)

lemma l2norm_neg:
   "f square_integrable S \<Longrightarrow> l2norm S (\<lambda>x. - f x) = l2norm S f"
  using l2norm_lmult [of f S "-1"] by simp

lemma l2norm_diff:
  assumes "f square_integrable S" "g square_integrable S"
  shows "l2norm S (\<lambda>x. f x - g x) = l2norm S (\<lambda>x. g x - f x)"
proof -
  have "(\<lambda>x. f x - g x) square_integrable S"
    using assms square_integrable_diff by blast
  then show ?thesis
    using l2norm_neg [of "\<lambda>x. f x - g x" S] by (simp add: algebra_simps)
qed


subsection\<open>Completeness (Riesz-Fischer)\<close>

lemma eNorm_eq_lnorm: "\<lbrakk>f \<in> lspace M p; p > 0\<rbrakk> \<Longrightarrow> eNorm (\<LL> (ennreal p) M) f = ennreal (lnorm M p f)"
  by (simp add: Lp_D(4) lnorm_def)

lemma Norm_eq_lnorm: "\<lbrakk>f \<in> lspace M p; p > 0\<rbrakk> \<Longrightarrow> Norm (\<LL> (ennreal p) M) f = lnorm M p f"
  by (simp add: Lp_D(3) lnorm_def)


lemma eNorm_ge1_triangular_ineq:
  assumes "p \<ge> (1::real)"
  shows "eNorm (\<LL> p M) (x + y) \<le> eNorm (\<LL> p M) x + eNorm (\<LL> p M) y"
  using eNorm_triangular_ineq [of "(\<LL> p M)"] assms
  by (simp add: Lp(2))

text\<open>A mere repackaging of the theorem @{thm Lp_complete}, but nearly as much work again.\<close>
proposition l2_complete:
  assumes f: "\<And>i::nat. f i square_integrable S"
    and cauchy: "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. l2norm S (\<lambda>x. f m x - f n x) < e"
  obtains g where "g square_integrable S" "((\<lambda>n. l2norm S (\<lambda>x. f n x - g x)) \<longlonglongrightarrow> 0)"
proof -
  have finite: "eNorm (\<LL> 2 (lebesgue_on S)) (f n - f m) < \<top>" for m n
    by (metis f infinity_ennreal_def spaceN_diff spaceN_iff square_integrable_imp_lspace)
  have *: "cauchy_ine\<^sub>N (\<LL> 2 (lebesgue_on S)) f"
  proof (clarsimp simp: cauchy_ine\<^sub>N_def)
    show "\<exists>M. \<forall>n\<ge>M. \<forall>m\<ge>M. eNorm (\<LL> 2 (lebesgue_on S)) (f n - f m) < e"
      if "e > 0" for e
    proof (cases e)
      case (real r)
      then have "r > 0"
        using that by auto
      with cauchy obtain N::nat where N: "\<And>m n. \<lbrakk>m \<ge> N; n \<ge> N\<rbrakk> \<Longrightarrow> l2norm S (\<lambda>x. f n x - f m x) < r"
        by blast
      show ?thesis
      proof (intro exI allI impI)
        show "eNorm (\<LL> 2 (lebesgue_on S)) (f n - f m) < e"
          if "N \<le> m" "N \<le> n" for m n
        proof -
          have fnm: "(f n - f m) \<in> borel_measurable (lebesgue_on S)"
            using f unfolding square_integrable_def by (blast intro: borel_measurable_diff')
          have "l2norm S (\<lambda>x. f n x - f m x) = lnorm (lebesgue_on S) 2 (\<lambda>x. f n x - f m x)"
            by (metis l2norm_lnorm)
          also have "\<dots> = Norm (\<LL> 2 (lebesgue_on S)) (f n - f m)"
            using Lp_Norm [OF _ fnm, of 2] by (simp add: lnorm_def)
          finally show ?thesis
            using N [OF that] real finite
            by (simp add: Norm_def)
        qed
      qed
    qed (simp add: finite)
  qed
  then obtain g where g: "tendsto_ine\<^sub>N (\<LL> 2 (lebesgue_on S)) f g"
    using Lp_complete complete\<^sub>N_def by blast
  show ?thesis
  proof
    have fng_to_0: "(\<lambda>n. eNorm (\<LL> 2 (lebesgue_on S)) (\<lambda>x. f n x - g x)) \<longlonglongrightarrow> 0"
      using g Lp_D(4) [of 2 _ "lebesgue_on S"]
      by (simp add: tendsto_ine\<^sub>N_def minus_fun_def)
    then obtain M where "\<And>n . n \<ge> M \<Longrightarrow> eNorm (\<LL> 2 (lebesgue_on S)) (\<lambda>x. f n x - g x) < \<top>"
      apply (simp add: lim_explicit)
      by (metis (full_types) open_lessThan diff_self eNorm_zero lessThan_iff local.finite)
    then have "eNorm (\<LL> 2 (lebesgue_on S)) (\<lambda>x. g x - f M x) < \<top>"
      using eNorm_uminus [of _ "\<lambda>x. g x - f _ x"] by (simp add: uminus_fun_def)
    moreover have "eNorm (\<LL> 2 (lebesgue_on S)) (\<lambda>x. f M x) < \<top>"
      using f square_integrable_imp_lspace by (simp add: spaceN_iff)
    ultimately have "eNorm (\<LL> 2 (lebesgue_on S)) g < \<top>"
      using eNorm_ge1_triangular_ineq [of 2 "lebesgue_on S" "g - f M" "f M", simplified] not_le top.not_eq_extremum
      by (fastforce simp add: minus_fun_def)
    then have g_space: "g \<in> space\<^sub>N (\<LL> 2 (lebesgue_on S))"
      by (simp add: spaceN_iff)
    show "g square_integrable S"
      unfolding square_integrable_def
    proof (intro conjI)
      show "g \<in> borel_measurable (lebesgue_on S)"
        using Lp_measurable g_space by blast
      show "S \<in> sets lebesgue"
        using f square_integrable_def by blast
      then show "integrable (lebesgue_on S) (\<lambda>x. (g x)\<^sup>2)"
        using g_space square_integrable_def square_integrable_iff_lspace by blast
    qed
    then have "f n - g \<in> lspace (lebesgue_on S) 2" for n
      using f spaceN_diff square_integrable_imp_lspace by blast
    with fng_to_0 have "(\<lambda>n. ennreal (lnorm (lebesgue_on S) 2 (\<lambda>x. f n x - g x))) \<longlonglongrightarrow> 0"
      by (simp add: minus_fun_def flip: eNorm_eq_lnorm)
    then have "(\<lambda>n. lnorm (lebesgue_on S) 2 (\<lambda>x. f n x - g x)) \<longlonglongrightarrow> 0"
      by (simp add: ennreal_tendsto_0_iff lnorm_def)
    then show "(\<lambda>n. l2norm S (\<lambda>x. f n x - g x)) \<longlonglongrightarrow> 0"
      using g by (simp add:  l2norm_lnorm lnorm_def)
  qed
qed

subsection\<open>Approximation of functions in Lp by bounded and continuous ones\<close>

lemma lspace_bounded_measurable:
  fixes p::real
  assumes f: "f \<in> borel_measurable (lebesgue_on S)" and g: "g \<in> lspace (lebesgue_on S) p" and "p > 0"
    and le: " AE x in lebesgue_on S. norm (\<bar>f x\<bar> powr p) \<le> norm (\<bar>g x\<bar> powr p)"
  shows "f \<in> lspace (lebesgue_on S) p"
  using assms by (auto simp: lspace_ennreal_iff intro: Bochner_Integration.integrable_bound)

lemma lspace_approximate_bounded:
  assumes f: "f \<in> lspace (lebesgue_on S) p" and S: "S \<in> lmeasurable" and "p > 0" "e > 0"
  obtains g where "g \<in> lspace (lebesgue_on S) p" "bounded (g ` S)"
    "lnorm (lebesgue_on S) p (f - g) < e"
proof -
  have f_bm: "f \<in> borel_measurable (lebesgue_on S)"
    using Lp_measurable f by blast
  let ?f = "\<lambda>n::nat. \<lambda>x. max (- n) (min n (f x))"
  have "tendsto_in\<^sub>N (\<LL> p (lebesgue_on S)) ?f f"
  proof (rule Lp_domination_limit)
    show "\<And>n::nat. ?f n \<in> borel_measurable (lebesgue_on S)"
      by (intro f_bm borel_measurable_max borel_measurable_min borel_measurable_const)
    show "abs \<circ> f \<in> lspace (lebesgue_on S) p"
      using Lp_Banach_lattice [OF f] by (simp add: o_def)
    have *: "\<forall>\<^sub>F n in sequentially. dist (?f n x) (f x) < e"
      if x: "x \<in> space (lebesgue_on S)" and "e > 0" for x e
    proof
      show "dist (?f n x) (f x) < e"
        if "nat \<lceil>\<bar>f x\<bar>\<rceil> \<le> n" for n :: nat
        using that \<open>0 < e\<close> by (simp add: dist_real_def max_def min_def abs_if split: if_split_asm)
    qed
    then show "AE x in lebesgue_on S. (\<lambda>n::nat. max (- n) (min n (f x))) \<longlonglongrightarrow> f x"
      by (blast intro: tendstoI)
  qed (auto simp: f_bm)
  moreover
  have lspace: "?f n \<in> lspace (lebesgue_on S) p" for n::nat
    by (intro f lspace_const lspace_min lspace_max \<open>p > 0\<close> S)
  ultimately have "(\<lambda>n. lnorm (lebesgue_on S) p (?f n - f)) \<longlonglongrightarrow> 0"
    by (simp add: tendsto_in\<^sub>N_def Norm_eq_lnorm \<open>p > 0\<close> f)
  with \<open>e > 0\<close> obtain N where N: "\<bar>lnorm (lebesgue_on S) p (?f N - f)\<bar> < e"
    by (auto simp: LIMSEQ_iff)
  show ?thesis
  proof
    have "\<forall>x\<in>S. \<bar>max (- real N) (min (real N) (f x))\<bar> \<le> N"
      by auto
    then show "bounded (?f N ` S::real set)"
      by (force simp: bounded_iff)
    show "lnorm (lebesgue_on S) p (f - ?f N) < e"
      using N by (simp add: lnorm_minus_commute)
  qed (auto simp: lspace)
qed

lemma borel_measurable_imp_continuous_limit:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes h: "h \<in> borel_measurable (lebesgue_on S)" and S: "S \<in> sets lebesgue"
  obtains g where "\<And>n. continuous_on UNIV (g n)" "AE x in lebesgue_on S. (\<lambda>n::nat. g n x) \<longlonglongrightarrow> h x"
proof -
  have "h measurable_on S"
    using S h measurable_on_iff_borel_measurable by blast
  then obtain N g where N: "N \<in> null_sets lebesgue" and g: "\<And>n. continuous_on UNIV (g n)"
    and tends: "\<And>x. x \<notin> N \<Longrightarrow> (\<lambda>n. g n x) \<longlonglongrightarrow> (if x \<in> S then h x else 0)"
    by (auto simp: measurable_on_def negligible_iff_null_sets)
  moreover have "AE x in lebesgue_on S. (\<lambda>n::nat. g n x) \<longlonglongrightarrow> h x"
  proof (rule AE_I')
    show "N \<inter> S \<in> null_sets (lebesgue_on S)"
      by (simp add: S N null_set_Int2 null_sets_restrict_space)
    show "{x \<in> space (lebesgue_on S). \<not> (\<lambda>n. g n x) \<longlonglongrightarrow> h x} \<subseteq> N \<inter> S"
      using tends by force
  qed
  ultimately show thesis
    using that by blast
qed


proposition lspace_approximate_continuous:
  assumes f: "f \<in> lspace (lebesgue_on S) p" and S: "S \<in> lmeasurable" and "1 \<le> p" "e > 0"
  obtains g where "continuous_on UNIV g" "g \<in> lspace (lebesgue_on S) p" "lnorm (lebesgue_on S) p (f - g) < e"
proof -
  have "p > 0"
    using assms by simp
  obtain h where h: "h \<in> lspace (lebesgue_on S) p" and "bounded (h ` S)"
    and lesse2: "lnorm (lebesgue_on S) p (f - h) < e/2"
    by (rule lspace_approximate_bounded [of f p S "e/2"]) (use assms in auto)
  then obtain B where "B > 0" and B: "\<And>x. x \<in> S \<Longrightarrow> \<bar>h x\<bar> \<le> B"
    by (auto simp: bounded_pos)
  have bmh: "h \<in> borel_measurable (lebesgue_on S)"
    using h lspace_ennreal_iff [of p] \<open>p \<ge> 1\<close> by auto
  obtain g where contg: "\<And>n. continuous_on UNIV (g n)"
    and gle: "\<And>n x. x \<in> S \<Longrightarrow> \<bar>g n x\<bar> \<le> B"
    and tends: "AE x in lebesgue_on S. (\<lambda>n::nat. g n x) \<longlonglongrightarrow> h x"
  proof -
    obtain \<gamma> where cont: "\<And>n. continuous_on UNIV (\<gamma> n)"
      and tends: "AE x in lebesgue_on S. (\<lambda>n::nat. \<gamma> n x) \<longlonglongrightarrow> h x"
      using borel_measurable_imp_continuous_limit S bmh by blast
    let ?g = "\<lambda>n::nat. \<lambda>x. max (- B) (min B (\<gamma> n x))"
    show thesis
    proof
      show "continuous_on UNIV (?g n)" for n
        by (intro continuous_intros cont)
      show "\<bar>?g n x\<bar> \<le> B" if "x \<in> S"  for n x
        using that \<open>B > 0\<close> by (auto simp: max_def min_def)
      have "(\<lambda>n. max (- B) (min B (\<gamma> n x))) \<longlonglongrightarrow> h x"
        if "(\<lambda>n. \<gamma> n x) \<longlonglongrightarrow> h x" "x \<in> S" for x
        using that \<open>B > 0\<close> B [OF \<open>x \<in> S\<close>]
        unfolding LIMSEQ_def by (fastforce simp: min_def max_def dist_real_def)
      then show "AE x in lebesgue_on S. (\<lambda>n. ?g n x) \<longlonglongrightarrow> h x"
        using tends by auto
    qed
  qed
  have lspace_B: "(\<lambda>x. B) \<in> lspace (lebesgue_on S) p"
    by (simp add: S \<open>0 < p\<close> lspace_const)
  have lspace_g: "g n \<in> lspace (lebesgue_on S) p" for n
  proof (rule lspace_bounded_measurable)
    show "g n \<in> borel_measurable (lebesgue_on S)"
      by (simp add: borel_measurable_continuous_onI contg measurable_completion measurable_restrict_space1)
    show "AE x in lebesgue_on S. norm (\<bar>g n x\<bar> powr p) \<le> norm (\<bar>B\<bar> powr p)"
      using \<open>B > 0\<close> gle S \<open>0 < p\<close> powr_mono2 by auto
  qed (use \<open>p > 0\<close> lspace_B in auto)
  have "tendsto_in\<^sub>N (\<LL> p (lebesgue_on S)) g h"
  proof (rule Lp_domination_limit [OF bmh _ lspace_B tends])
    show "\<And>n::nat. g n \<in> borel_measurable (lebesgue_on S)"
      using Lp_measurable lspace_g by blast
    show "\<And>n. AE x in lebesgue_on S. \<bar>g n x\<bar> \<le> B"
      using S gle by auto
  qed
  then have 0: "(\<lambda>n. Norm (\<LL> p (lebesgue_on S)) (g n - h)) \<longlonglongrightarrow> 0"
    by (simp add: tendsto_in\<^sub>N_def)
  have "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. lnorm (lebesgue_on S) p (g n - h) < e"
    using LIMSEQ_D [OF 0] \<open>e > 0\<close>
    by (force simp: Norm_eq_lnorm \<open>0 < p\<close> h lspace_g)
  then obtain N where N: "lnorm (lebesgue_on S) p (g N - h) < e/2"
    unfolding minus_fun_def by (meson \<open>e>0\<close> half_gt_zero order_refl)
  show ?thesis
  proof
    show "continuous_on UNIV (g N)"
      by (simp add: contg)
    show "g N \<in> lspace (lebesgue_on S) (ennreal p)"
      by (simp add: lspace_g)
    have "lnorm (lebesgue_on S) p (f - h + - (g N - h)) \<le> lnorm (lebesgue_on S) p (f - h) + lnorm (lebesgue_on S) p (- (g N - h))"
      by (rule lnorm_triangle_fun) (auto simp: lspace_g h assms)
    also have "\<dots>  < e/2 + e/2"
      using lesse2 N by (simp add: lnorm_minus_commute)
    finally show "lnorm (lebesgue_on S) p (f - g N) < e"
      by simp
  qed
qed

proposition square_integrable_approximate_continuous:
  assumes f: "f square_integrable S" and S: "S \<in> lmeasurable" and "e > 0"
  obtains g where "continuous_on UNIV g" "g square_integrable S" "l2norm S (\<lambda>x. f x - g x) < e"
proof -
  have f2: "f \<in> lspace (lebesgue_on S) 2"
    by (simp add: f square_integrable_imp_lspace)
  then obtain g where contg: "continuous_on UNIV g"
             and g2: "g \<in> lspace (lebesgue_on S) 2"
             and less_e: "lnorm (lebesgue_on S) 2 (\<lambda>x. f x - g x) < e"
    using lspace_approximate_continuous [of f 2 S e] S \<open>0 < e\<close> by (auto simp: minus_fun_def)
  show thesis
  proof
    show "g square_integrable S"
      using g2 by (simp add: S fmeasurableD square_integrable_iff_lspace)
    show "l2norm S (\<lambda>x. f x - g x) < e"
      using less_e by (simp add: l2norm_lnorm)
  qed (simp add: contg)
qed

lemma absolutely_integrable_approximate_continuous:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f absolutely_integrable_on S" and S: "S \<in> lmeasurable" and "0 < e"
  obtains g where "continuous_on UNIV g" "g absolutely_integrable_on S" "integral\<^sup>L (lebesgue_on S) (\<lambda>x. \<bar>f x - g x\<bar>) < e"
proof -
  obtain g where "continuous_on UNIV g" "g \<in> lspace (lebesgue_on S) 1"
              and lnorm: "lnorm (lebesgue_on S) 1 (f - g) < e"
  proof (rule lspace_approximate_continuous)
    show "f \<in> lspace (lebesgue_on S) (ennreal 1)"
      by (simp add: S f fmeasurableD lspace_1)
  qed (auto simp: assms)
  show thesis
  proof
    show "continuous_on UNIV g"
      by fact
    show "g absolutely_integrable_on S"
      using S \<open>g \<in> lspace (lebesgue_on S) 1\<close> lspace_1 by blast
    have *: "(\<lambda>x. f x - g x) absolutely_integrable_on S"
      by (simp add: \<open>g absolutely_integrable_on S\<close> f)
    moreover have "integrable (lebesgue_on S) (\<lambda>x. \<bar>f x - g x\<bar>)"
      by (simp add: L1_D(2) S * fmeasurableD lspace_1)
    ultimately show "integral\<^sup>L (lebesgue_on S)  (\<lambda>x. \<bar>f x - g x\<bar>) < e"
      using lnorm S unfolding lnorm_def absolutely_integrable_on_def
      by simp
  qed
qed

end
