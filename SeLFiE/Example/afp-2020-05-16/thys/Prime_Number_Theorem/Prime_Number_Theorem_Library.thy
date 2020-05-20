section \<open>Auxiliary material\<close>
theory Prime_Number_Theorem_Library
imports
  Zeta_Function.Zeta_Function
  "HOL-Real_Asymp.Real_Asymp"
begin

(* TODO: Move *)
lemma asymp_equivD_strong:
  assumes "f \<sim>[F] g" "eventually (\<lambda>x. f x \<noteq> 0 \<or> g x \<noteq> 0) F"
  shows   "((\<lambda>x. f x / g x) \<longlongrightarrow> 1) F"
proof -
  from assms(1) have "((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x) \<longlongrightarrow> 1) F"
    by (rule asymp_equivD)
  also have "?this \<longleftrightarrow> ?thesis"
    by (intro filterlim_cong eventually_mono[OF assms(2)]) auto
  finally show ?thesis .
qed

lemma frontier_real_Ici [simp]:
  fixes a :: real
  shows "frontier {a..} = {a}"
  unfolding frontier_def by (auto simp: interior_real_atLeast)

lemma sum_upto_ln_conv_sum_upto_mangoldt:
  "sum_upto (\<lambda>n. ln (real n)) x = sum_upto (\<lambda>n. mangoldt n * nat \<lfloor>x / real n\<rfloor>) x"
proof -
  have "sum_upto (\<lambda>n. ln (real n)) x =
          sum_upto (\<lambda>n. \<Sum>d | d dvd n. mangoldt d) x"
    by (intro sum_upto_cong) (simp_all add: mangoldt_sum)
  also have "\<dots> = sum_upto (\<lambda>k. sum_upto (\<lambda>d. mangoldt k) (x / real k)) x"
    by (rule sum_upto_sum_divisors)
  also have "\<dots> = sum_upto (\<lambda>n. mangoldt n * nat \<lfloor>x / real n\<rfloor>) x"
    unfolding sum_upto_altdef by (simp add: mult_ac)
  finally show ?thesis .
qed

lemma ln_fact_conv_sum_upto_mangoldt:
  "ln (fact n) = sum_upto (\<lambda>k. mangoldt k * (n div k)) n"
proof -
  have [simp]: "{0<..Suc n} = insert (Suc n) {0<..n}" for n by auto
  have "ln (fact n) = sum_upto (\<lambda>n. ln (real n)) n"
    by (induction n) (auto simp: sum_upto_altdef nat_add_distrib ln_mult)
  also have "\<dots> = sum_upto (\<lambda>k. mangoldt k * (n div k)) n"
    unfolding sum_upto_ln_conv_sum_upto_mangoldt
    by (intro sum_upto_cong) (auto simp: floor_divide_of_nat_eq)
  finally show ?thesis .
qed

lemma powr_sum: "x \<noteq> 0 \<Longrightarrow> finite A \<Longrightarrow> x powr sum f A = (\<Prod>y\<in>A. x powr f y)"
  by (simp add: powr_def exp_sum sum_distrib_right)

lemma fds_abs_converges_comparison_test:
  fixes s :: "'a :: dirichlet_series"
  assumes "eventually (\<lambda>n. norm (fds_nth f n) \<le> fds_nth g n) at_top" and "fds_converges g (s \<bullet> 1)"
  shows   "fds_abs_converges f s"
  unfolding fds_abs_converges_def
proof (rule summable_comparison_test_ev)
  from assms(2) show "summable (\<lambda>n. fds_nth g n / n powr (s \<bullet> 1))"
    by (auto simp: fds_converges_def)
  from assms(1) eventually_gt_at_top[of 0]
    show "eventually (\<lambda>n. norm (norm (fds_nth f n / nat_power n s)) \<le>
                            fds_nth g n / real n powr (s \<bullet> 1)) at_top"
    by eventually_elim (auto simp: norm_divide norm_nat_power intro!: divide_right_mono)
qed

lemma fds_converges_scaleR [intro]:
  assumes "fds_converges f s"
  shows   "fds_converges (c *\<^sub>R f) s"
proof -
  from assms have "summable (\<lambda>n. c *\<^sub>R (fds_nth f n / nat_power n s))"
    by (intro summable_scaleR_right) (auto simp: fds_converges_def)
  also have "(\<lambda>n. c *\<^sub>R (fds_nth f n / nat_power n s)) = (\<lambda>n. (c *\<^sub>R fds_nth f n / nat_power n s))"
    by (simp add: scaleR_conv_of_real)
  finally show ?thesis by (simp add: fds_converges_def)
qed

lemma fds_abs_converges_scaleR [intro]:
  assumes "fds_abs_converges f s"
  shows   "fds_abs_converges (c *\<^sub>R f) s"
proof -
  from assms have "summable (\<lambda>n. abs c * norm (fds_nth f n / nat_power n s))"
    by (intro summable_mult) (auto simp: fds_abs_converges_def)
  also have "(\<lambda>n. abs c * norm (fds_nth f n / nat_power n s)) =
               (\<lambda>n. norm ((c *\<^sub>R fds_nth f n) / nat_power n s))" by (simp add: norm_divide)
  finally show ?thesis by (simp add: fds_abs_converges_def)
qed

lemma conv_abscissa_scaleR: "conv_abscissa (scaleR c f) \<le> conv_abscissa f"
  by (rule conv_abscissa_mono) auto

lemma abs_conv_abscissa_scaleR: "abs_conv_abscissa (scaleR c f) \<le> abs_conv_abscissa f"
  by (rule abs_conv_abscissa_mono) auto

lemma fds_converges_mult_const_left [intro]:
  "fds_converges f s \<Longrightarrow> fds_converges (fds_const c * f) s"
  by (auto simp: fds_converges_def dest: summable_mult[of _ c])

lemma fds_abs_converges_mult_const_left [intro]:
  "fds_abs_converges f s \<Longrightarrow> fds_abs_converges (fds_const c * f) s"
  by (auto simp: fds_abs_converges_def norm_mult norm_divide dest: summable_mult[of _ "norm c"])

lemma conv_abscissa_mult_const_left:
  "conv_abscissa (fds_const c * f) \<le> conv_abscissa f"
  by (intro conv_abscissa_mono) auto

lemma abs_conv_abscissa_mult_const_left:
  "abs_conv_abscissa (fds_const c * f) \<le> abs_conv_abscissa f"
  by (intro abs_conv_abscissa_mono) auto

lemma fds_converges_mult_const_right [intro]:
  "fds_converges f s \<Longrightarrow> fds_converges (f * fds_const c) s"
  by (auto simp: fds_converges_def dest: summable_mult2[of _ c])

lemma fds_abs_converges_mult_const_right [intro]:
  "fds_abs_converges f s \<Longrightarrow> fds_abs_converges (f * fds_const c) s"
  by (auto simp: fds_abs_converges_def norm_mult norm_divide dest: summable_mult2[of _ "norm c"])

lemma conv_abscissa_mult_const_right:
  "conv_abscissa (f * fds_const c) \<le> conv_abscissa f"
  by (intro conv_abscissa_mono) auto

lemma abs_conv_abscissa_mult_const_right:
  "abs_conv_abscissa (f * fds_const c) \<le> abs_conv_abscissa f"
  by (intro abs_conv_abscissa_mono) auto


lemma bounded_coeffs_imp_fds_abs_converges:
  fixes s :: "'a :: dirichlet_series" and f :: "'a fds"
  assumes "Bseq (fds_nth f)" "s \<bullet> 1 > 1"
  shows   "fds_abs_converges f s"
proof -
  from assms obtain C where C: "\<And>n. norm (fds_nth f n) \<le> C"
    by (auto simp: Bseq_def)
  show ?thesis
  proof (rule fds_abs_converges_comparison_test)
    from \<open>s \<bullet> 1 > 1\<close> show "fds_converges (C *\<^sub>R fds_zeta) (s \<bullet> 1)"
      by (intro fds_abs_converges_imp_converges) auto
    from C show "eventually (\<lambda>n. norm (fds_nth f n) \<le> fds_nth (C *\<^sub>R fds_zeta) n) at_top"
      by (intro always_eventually) (auto simp: fds_nth_zeta)
  qed
qed

lemma bounded_coeffs_imp_fds_abs_converges':
  fixes s :: "'a :: dirichlet_series" and f :: "'a fds"
  assumes "Bseq (\<lambda>n. fds_nth f n * nat_power n s0)" "s \<bullet> 1 > 1 - s0 \<bullet> 1"
  shows   "fds_abs_converges f s"
proof -
  have "fds_nth (fds_shift s0 f) = (\<lambda>n. fds_nth f n * nat_power n s0)"
    by (auto simp: fun_eq_iff)
  with assms have "Bseq (fds_nth (fds_shift s0 f))" by simp
  with assms(2) have "fds_abs_converges (fds_shift s0 f) (s + s0)"
    by (intro bounded_coeffs_imp_fds_abs_converges) (auto simp: algebra_simps)
  thus ?thesis by simp
qed

lemma bounded_coeffs_imp_abs_conv_abscissa_le:
  fixes s :: "'a :: dirichlet_series" and f :: "'a fds" and c :: ereal
  assumes "Bseq (\<lambda>n. fds_nth f n * nat_power n s)" "1 - s \<bullet> 1 \<le> c"
  shows   "abs_conv_abscissa f \<le> c"
proof (rule abs_conv_abscissa_leI_weak)
  fix x assume "c < ereal x"
  have "ereal (1 - s \<bullet> 1) \<le> c" by fact
  also have "\<dots> < ereal x" by fact
  finally have "1 - s \<bullet> 1 < ereal x" by simp
  thus "fds_abs_converges f (of_real x)"
    by (intro bounded_coeffs_imp_fds_abs_converges'[OF assms(1)]) auto
qed

lemma bounded_coeffs_imp_abs_conv_abscissa_le_1:
  fixes s :: "'a :: dirichlet_series" and f :: "'a fds"
  assumes "Bseq (\<lambda>n. fds_nth f n)"
  shows   "abs_conv_abscissa f \<le> 1"
proof -
  have [simp]: "fds_nth f n * nat_power n 0 = fds_nth f n" for n
    by (cases "n = 0") auto
  show ?thesis
    by (rule bounded_coeffs_imp_abs_conv_abscissa_le[where s = 0]) (insert assms, auto simp:)
qed

(* TODO: replace library version *)
(* EXAMPLE: This might make a good example to illustrate real_asymp *)
lemma
  fixes a b c :: real
  assumes ab: "a + b > 0" and c: "c < -1"
  shows set_integrable_powr_at_top: "(\<lambda>x. (b + x) powr c) absolutely_integrable_on {a<..}"
  and   set_lebesgue_integral_powr_at_top:
          "(\<integral>x\<in>{a<..}. ((b + x) powr c) \<partial>lborel) = -((b + a) powr (c + 1) / (c + 1))"
  and   powr_has_integral_at_top:
          "((\<lambda>x. (b + x) powr c) has_integral -((b + a) powr (c + 1) / (c + 1))) {a<..}"
proof -
  let ?f = "\<lambda>x. (b + x) powr c" and ?F = "\<lambda>x. (b + x) powr (c + 1) / (c + 1)"
  have limits: "((?F \<circ> real_of_ereal) \<longlongrightarrow> ?F a) (at_right (ereal a))"
               "((?F \<circ> real_of_ereal) \<longlongrightarrow> 0) (at_left \<infinity>)"
    using c ab unfolding ereal_tendsto_simps1 by (real_asymp simp: field_simps)+
  have 1: "set_integrable lborel (einterval a \<infinity>) ?f" using ab c limits
    by (intro interval_integral_FTC_nonneg) (auto intro!: derivative_eq_intros)
  thus 2: "?f absolutely_integrable_on {a<..}"
    by (auto simp: set_integrable_def integrable_completion)
  have "LBINT x=ereal a..\<infinity>. (b + x) powr c = 0 - ?F a" using ab c limits
    by (intro interval_integral_FTC_nonneg) (auto intro!: derivative_eq_intros)
  thus 3: "(\<integral>x\<in>{a<..}. ((b + x) powr c) \<partial>lborel) = -((b + a) powr (c + 1) / (c + 1))"
    by (simp add: interval_integral_to_infinity_eq)
  show "(?f has_integral -((b + a) powr (c + 1) / (c + 1))) {a<..}"
    using set_borel_integral_eq_integral[OF 1] 3 by (simp add: has_integral_iff)
qed

lemma fds_converges_altdef2:
  "fds_converges f s \<longleftrightarrow> convergent (\<lambda>N. eval_fds (fds_truncate N f) s)"
  unfolding fds_converges_def summable_iff_convergent' eval_fds_truncate
  by (auto simp: not_le intro!: convergent_cong always_eventually sum.mono_neutral_right)

lemma tendsto_eval_fds_truncate:
  assumes "fds_converges f s"
  shows   "(\<lambda>N. eval_fds (fds_truncate N f) s) \<longlonglongrightarrow> eval_fds f s"
proof -
  have "(\<lambda>N. eval_fds (fds_truncate N f) s) \<longlonglongrightarrow> eval_fds f s \<longleftrightarrow>
          (\<lambda>N. \<Sum>i\<le>N. fds_nth f i / nat_power i s) \<longlonglongrightarrow> eval_fds f s"
    unfolding eval_fds_truncate
    by (intro filterlim_cong always_eventually allI sum.mono_neutral_left) (auto simp: not_le)
  also have \<dots> using assms
    by (simp add: fds_converges_iff sums_def' atLeast0AtMost)
  finally show ?thesis .
qed

lemma linepath_translate_left: "linepath (c + a) (c + a) = (\<lambda>x. c + a) \<circ> linepath a b"
  by (auto simp: fun_eq_iff linepath_def algebra_simps)

lemma linepath_translate_right: "linepath (a + c) (b + c) = (\<lambda>x. x + c) \<circ> linepath a b"
  by (auto simp: fun_eq_iff linepath_def algebra_simps)

lemma integrable_on_affinity:
  assumes "m \<noteq> 0" "f integrable_on (cbox a b)"
  shows   "(\<lambda>x. f (m *\<^sub>R x + c)) integrable_on ((\<lambda>x. (1 / m) *\<^sub>R x - ((1 / m) *\<^sub>R c)) ` cbox a b)"
proof -
  from assms obtain I where "(f has_integral I) (cbox a b)"
    by (auto simp: integrable_on_def)
  from has_integral_affinity[OF this assms(1), of c] show ?thesis
    by (auto simp: integrable_on_def)
qed

lemma has_integral_cmul_iff:
  assumes "c \<noteq> 0"
  shows   "((\<lambda>x. c *\<^sub>R f x) has_integral (c *\<^sub>R I)) A \<longleftrightarrow> (f has_integral I) A"
  using assms has_integral_cmul[of f I A c]
        has_integral_cmul[of "\<lambda>x. c *\<^sub>R f x" "c *\<^sub>R I" A "inverse c"] by (auto simp: field_simps)

lemma has_integral_affinity':
  fixes a :: "'a::euclidean_space"
  assumes "(f has_integral i) (cbox a b)" and "m > 0"
  shows "((\<lambda>x. f(m *\<^sub>R x + c)) has_integral (i /\<^sub>R m ^ DIM('a)))
           (cbox ((a - c) /\<^sub>R m) ((b - c) /\<^sub>R m))"
proof (cases "cbox a b = {}")
  case True
  hence "(cbox ((a - c) /\<^sub>R m) ((b - c) /\<^sub>R m)) = {}"
    using \<open>m > 0\<close> unfolding box_eq_empty by (auto simp: algebra_simps)
  with True and assms show ?thesis by simp
next
  case False
  have "((\<lambda>x. f (m *\<^sub>R x + c)) has_integral (1 / \<bar>m\<bar> ^ DIM('a)) *\<^sub>R i)
          ((\<lambda>x. (1 / m) *\<^sub>R x + - ((1 / m) *\<^sub>R c)) ` cbox a b)"
    using assms by (intro has_integral_affinity) auto
  also have "((\<lambda>x. (1 / m) *\<^sub>R x + - ((1 / m) *\<^sub>R c)) ` cbox a b) =
               ((\<lambda>x.  - ((1 / m) *\<^sub>R c) + x) ` (\<lambda>x. (1 / m) *\<^sub>R x) ` cbox a b)"
    by (simp add: image_image algebra_simps)
  also have "(\<lambda>x. (1 / m) *\<^sub>R x) ` cbox a b = cbox ((1 / m) *\<^sub>R a) ((1 / m) *\<^sub>R b)" using \<open>m > 0\<close> False
    by (subst image_smult_cbox) simp_all
  also have "(\<lambda>x. - ((1 / m) *\<^sub>R c) + x) ` \<dots> = cbox ((a - c) /\<^sub>R m) ((b - c) /\<^sub>R m)"
    by (subst cbox_translation [symmetric]) (simp add: field_simps vector_add_divide_simps)
  finally show ?thesis using \<open>m > 0\<close> by (simp add: field_simps)
qed

lemma has_integral_affinity_iff:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: real_normed_vector"
  assumes "m > 0"
  shows   "((\<lambda>x. f (m *\<^sub>R x + c)) has_integral (I /\<^sub>R m ^ DIM('a)))
               (cbox ((a - c) /\<^sub>R m) ((b - c) /\<^sub>R m)) \<longleftrightarrow>
           (f has_integral I) (cbox a b)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  from has_integral_affinity'[OF this, of "1 / m" "-c /\<^sub>R m"] and \<open>m > 0\<close>
    show ?rhs by (simp add: vector_add_divide_simps) (simp add: field_simps)
next
  assume ?rhs
  from has_integral_affinity'[OF this, of m c] and \<open>m > 0\<close>
  show ?lhs by simp
qed

lemma has_contour_integral_linepath_Reals_iff:
  fixes a b :: complex and f :: "complex \<Rightarrow> complex"
  assumes "a \<in> Reals" "b \<in> Reals" "Re a < Re b"
  shows   "(f has_contour_integral I) (linepath a b) \<longleftrightarrow>
             ((\<lambda>x. f (of_real x)) has_integral I) {Re a..Re b}"
proof -
  from assms have [simp]: "of_real (Re a) = a" "of_real (Re b) = b"
    by (simp_all add: complex_eq_iff)
  from assms have "a \<noteq> b" by auto
  have "((\<lambda>x. f (of_real x)) has_integral I) (cbox (Re a) (Re b)) \<longleftrightarrow>
          ((\<lambda>x. f (a + b * of_real x - a * of_real x)) has_integral I /\<^sub>R (Re b - Re a)) {0..1}"
    by (subst has_integral_affinity_iff [of "Re b - Re a" _ "Re a", symmetric])
       (insert assms, simp_all add: field_simps scaleR_conv_of_real)
  also have "(\<lambda>x. f (a + b * of_real x - a * of_real x)) =
               (\<lambda>x. (f (a + b * of_real x - a * of_real x) * (b - a)) /\<^sub>R (Re b - Re a))"
    using \<open>a \<noteq> b\<close> by (auto simp: field_simps fun_eq_iff scaleR_conv_of_real)
  also have "(\<dots> has_integral I /\<^sub>R (Re b - Re a)) {0..1} \<longleftrightarrow>
               ((\<lambda>x. f (linepath a b x) * (b - a)) has_integral I) {0..1}" using assms
    by (subst has_integral_cmul_iff) (auto simp: linepath_def scaleR_conv_of_real algebra_simps)
  also have "\<dots> \<longleftrightarrow> (f has_contour_integral I) (linepath a b)" unfolding has_contour_integral_def
    by (intro has_integral_cong) (simp add: vector_derivative_linepath_within)
  finally show ?thesis by simp
qed

lemma contour_integrable_linepath_Reals_iff:
  fixes a b :: complex and f :: "complex \<Rightarrow> complex"
  assumes "a \<in> Reals" "b \<in> Reals" "Re a < Re b"
  shows   "(f contour_integrable_on linepath a b) \<longleftrightarrow>
             (\<lambda>x. f (of_real x)) integrable_on {Re a..Re b}"
  using has_contour_integral_linepath_Reals_iff[OF assms, of f]
  by (auto simp: contour_integrable_on_def integrable_on_def)

lemma contour_integral_linepath_Reals_eq:
  fixes a b :: complex and f :: "complex \<Rightarrow> complex"
  assumes "a \<in> Reals" "b \<in> Reals" "Re a < Re b"
  shows   "contour_integral (linepath a b) f = integral {Re a..Re b} (\<lambda>x. f (of_real x))"
proof (cases "f contour_integrable_on linepath a b")
  case True
  thus ?thesis using has_contour_integral_linepath_Reals_iff[OF assms, of f]
    using has_contour_integral_integral has_contour_integral_unique by blast
next
  case False
  thus ?thesis using contour_integrable_linepath_Reals_iff[OF assms, of f]
    by (simp add: not_integrable_contour_integral not_integrable_integral)
qed

lemma has_contour_integral_linepath_same_Im_iff:
  fixes a b :: complex and f :: "complex \<Rightarrow> complex"
  assumes "Im a = Im b" "Re a < Re b"
  shows   "(f has_contour_integral I) (linepath a b) \<longleftrightarrow>
             ((\<lambda>x. f (of_real x + Im a * \<i>)) has_integral I) {Re a..Re b}"
proof -
  have deriv: "vector_derivative ((\<lambda>x. x - Im a * \<i>) \<circ> linepath a b) (at y) = b - a" for y
    using linepath_translate_right[of a "-Im a * \<i>" b, symmetric] by simp
  have "(f has_contour_integral I) (linepath a b) \<longleftrightarrow>
          ((\<lambda>x. f (x + Im a * \<i>)) has_contour_integral I) (linepath (a - Im a * \<i>) (b - Im a * \<i>))"
    using linepath_translate_right[of a "-Im a * \<i>" b] deriv by (simp add: has_contour_integral)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. f (x + Im a * \<i>)) has_integral I) {Re a..Re b}" using assms
    by (subst has_contour_integral_linepath_Reals_iff) (auto simp: complex_is_Real_iff)
  finally show ?thesis .
qed

lemma contour_integrable_linepath_same_Im_iff:
  fixes a b :: complex and f :: "complex \<Rightarrow> complex"
  assumes "Im a = Im b" "Re a < Re b"
  shows   "(f contour_integrable_on linepath a b) \<longleftrightarrow>
             (\<lambda>x. f (of_real x + Im a * \<i>)) integrable_on {Re a..Re b}"
  using has_contour_integral_linepath_same_Im_iff[OF assms, of f]
  by (auto simp: contour_integrable_on_def integrable_on_def)

lemma contour_integral_linepath_same_Im:
  fixes a b :: complex and f :: "complex \<Rightarrow> complex"
  assumes "Im a = Im b" "Re a < Re b"
  shows   "contour_integral (linepath a b) f = integral {Re a..Re b} (\<lambda>x. f (x + Im a * \<i>))"
proof (cases "f contour_integrable_on linepath a b")
  case True
  thus ?thesis using has_contour_integral_linepath_same_Im_iff[OF assms, of f]
    using has_contour_integral_integral has_contour_integral_unique by blast
next
  case False
  thus ?thesis using contour_integrable_linepath_same_Im_iff[OF assms, of f]
    by (simp add: not_integrable_contour_integral not_integrable_integral)
qed


lemmas [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1

lemma continuous_on_compact_bound:
  assumes "compact A" "continuous_on A f"
  obtains B where "B \<ge> 0" "\<And>x. x \<in> A \<Longrightarrow> norm (f x) \<le> B"
proof -
  from assms(2,1) have "compact (f ` A)" by (rule compact_continuous_image)
  then obtain B where "\<forall>x\<in>A. norm (f x) \<le> B"
    by (auto dest!: compact_imp_bounded simp: bounded_iff)
  hence "max B 0 \<ge> 0" and "\<forall>x\<in>A. norm (f x) \<le> max B 0" by auto
  thus ?thesis using that by blast
qed

interpretation cis: periodic_fun_simple cis "2 * pi"
  by standard (simp_all add: complex_eq_iff)

lemma open_contains_cbox:
  fixes x :: "'a :: euclidean_space"
  assumes "open A" "x \<in> A"
  obtains a b where "cbox a b \<subseteq> A" "x \<in> box a b" "\<forall>i\<in>Basis. a \<bullet> i < b \<bullet> i"
proof -
  from assms obtain R where R: "R > 0" "ball x R \<subseteq> A"
    by (auto simp: open_contains_ball)
  define r :: real where "r = R / (2 * sqrt DIM('a))"
  from \<open>R > 0\<close> have [simp]: "r > 0" by (auto simp: r_def)
  define d :: 'a where "d = r *\<^sub>R Topology_Euclidean_Space.One"
  have "cbox (x - d) (x + d) \<subseteq> A"
  proof safe
    fix y assume y: "y \<in> cbox (x - d) (x + d)"
    have "dist x y = sqrt (\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2)"
      by (subst euclidean_dist_l2) (auto simp: L2_set_def)
    also from y have "sqrt (\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2) \<le> sqrt (\<Sum>i\<in>(Basis::'a set). r\<^sup>2)"
      by (intro real_sqrt_le_mono sum_mono power_mono)
         (auto simp: dist_norm d_def cbox_def algebra_simps)
    also have "\<dots> = sqrt (DIM('a) * r\<^sup>2)" by simp
    also have "DIM('a) * r\<^sup>2 = (R / 2) ^ 2"
      by (simp add: r_def power_divide)
    also have "sqrt \<dots> = R / 2"
      using \<open>R > 0\<close> by simp
    also from \<open>R > 0\<close> have "\<dots> < R" by simp
    finally have "y \<in> ball x R" by simp
    with R show "y \<in> A" by blast
  qed
  thus ?thesis
    using that[of "x - d" "x + d"] by (auto simp: algebra_simps d_def box_def)
qed

lemma open_contains_box:
  fixes x :: "'a :: euclidean_space"
  assumes "open A" "x \<in> A"
  obtains a b where "box a b \<subseteq> A" "x \<in> box a b" "\<forall>i\<in>Basis. a \<bullet> i < b \<bullet> i"
proof -
  from open_contains_cbox[OF assms] guess a b .
  with that[of a b] box_subset_cbox[of a b] show ?thesis by auto
qed

lemma analytic_onE_box:
  assumes "f analytic_on A" "s \<in> A"
  obtains a b where "Re a < Re b" "Im a < Im b" "s \<in> box a b" "f analytic_on box a b"
proof -
  from assms obtain r where r: "r > 0" "f holomorphic_on ball s r"
    by (auto simp: analytic_on_def)
  with open_contains_box[of "ball s r" s] obtain a b
    where "box a b \<subseteq> ball s r" "s \<in> box a b" "\<forall>i\<in>Basis. a \<bullet> i < b \<bullet> i" by auto
  moreover from r have "f analytic_on ball s r" by (simp add: analytic_on_open)
  ultimately show ?thesis using that[of a b] analytic_on_subset[of _ "ball s r" "box a b"]
    by (auto simp: Basis_complex_def)
qed

lemma inner_image_box:
  assumes "(i :: 'a :: euclidean_space) \<in> Basis"
  assumes "\<forall>i\<in>Basis. a \<bullet> i < b \<bullet> i"
  shows   "(\<lambda>x. x \<bullet> i) ` box a b = {a \<bullet> i<..<b \<bullet> i}"
proof safe
  fix x assume x: "x \<in> {a \<bullet> i<..<b \<bullet> i}"
  let ?y = "(\<Sum>j\<in>Basis. (if i = j then x else (a + b) \<bullet> j / 2) *\<^sub>R j)"
  from x assms have "?y \<bullet> i \<in> (\<lambda>x. x \<bullet> i) ` box a b"
    by (intro imageI) (auto simp: box_def algebra_simps)
  also have "?y \<bullet> i = (\<Sum>j\<in>Basis. (if i = j then x else (a + b) \<bullet> j / 2) * (j \<bullet> i))"
    by (simp add: inner_sum_left)
  also have "\<dots> = (\<Sum>j\<in>Basis. if i = j then x else 0)"
    by (intro sum.cong) (auto simp: inner_not_same_Basis assms)
  also have "\<dots> = x" using assms by simp
  finally show "x \<in> (\<lambda>x. x \<bullet> i) ` box a b"  .
qed (insert assms, auto simp: box_def)

lemma Re_image_box:
  assumes "Re a < Re b" "Im a < Im b"
  shows   "Re ` box a b = {Re a<..<Re b}"
  using inner_image_box[of "1::complex" a b] assms by (auto simp: Basis_complex_def)

lemma Im_image_box:
  assumes "Re a < Re b" "Im a < Im b"
  shows   "Im ` box a b = {Im a<..<Im b}"
  using inner_image_box[of "\<i>::complex" a b] assms by (auto simp: Basis_complex_def)

lemma inner_image_cbox:
  assumes "(i :: 'a :: euclidean_space) \<in> Basis"
  assumes "\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i"
  shows   "(\<lambda>x. x \<bullet> i) ` cbox a b = {a \<bullet> i..b \<bullet> i}"
proof safe
  fix x assume x: "x \<in> {a \<bullet> i..b \<bullet> i}"
  let ?y = "(\<Sum>j\<in>Basis. (if i = j then x else a \<bullet> j) *\<^sub>R j)"
  from x assms have "?y \<bullet> i \<in> (\<lambda>x. x \<bullet> i) ` cbox a b"
    by (intro imageI) (auto simp: cbox_def)
  also have "?y \<bullet> i = (\<Sum>j\<in>Basis. (if i = j then x else a \<bullet> j) * (j \<bullet> i))"
    by (simp add: inner_sum_left)
  also have "\<dots> = (\<Sum>j\<in>Basis. if i = j then x else 0)"
    by (intro sum.cong) (auto simp: inner_not_same_Basis assms)
  also have "\<dots> = x" using assms by simp
  finally show "x \<in> (\<lambda>x. x \<bullet> i) ` cbox a b"  .
qed (insert assms, auto simp: cbox_def)

lemma Re_image_cbox:
  assumes "Re a \<le> Re b" "Im a \<le> Im b"
  shows   "Re ` cbox a b = {Re a..Re b}"
  using inner_image_cbox[of "1::complex" a b] assms by (auto simp: Basis_complex_def)

lemma Im_image_cbox:
  assumes "Re a \<le> Re b" "Im a \<le> Im b"
  shows   "Im ` cbox a b = {Im a..Im b}"
  using inner_image_cbox[of "\<i>::complex" a b] assms by (auto simp: Basis_complex_def)

lemma analytic_onE_cball:
  assumes "f analytic_on A" "s \<in> A" "ub > (0::real)"
  obtains R where "R > 0" "R < ub" "f analytic_on cball s R"
proof -
  from assms obtain r where "r > 0" "f holomorphic_on ball s r"
    by (auto simp: analytic_on_def)
  hence "f analytic_on ball s r" by (simp add: analytic_on_open)
  hence "f analytic_on cball s (min (ub / 2) (r / 2))"
    by (rule analytic_on_subset, subst cball_subset_ball_iff) (use \<open>r > 0\<close> in auto)
  moreover have "min (ub / 2) (r / 2) > 0" and "min (ub / 2) (r / 2) < ub"
    using \<open>r > 0\<close> and \<open>ub > 0\<close> by (auto simp: min_def)
  ultimately show ?thesis using that[of "min (ub / 2) (r / 2)"]
    by blast
qed


corollary analytic_pre_zeta' [analytic_intros]:
  assumes "f analytic_on A" "a > 0"
  shows   "(\<lambda>x. pre_zeta a (f x)) analytic_on A"
  using analytic_on_compose_gen[OF assms(1) analytic_pre_zeta[of a UNIV]] assms(2)
  by (auto simp: o_def)

corollary analytic_hurwitz_zeta' [analytic_intros]:
  assumes "f analytic_on A" "(\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 1)" "a > 0"
  shows   "(\<lambda>x. hurwitz_zeta a (f x)) analytic_on A"
  using analytic_on_compose_gen[OF assms(1) analytic_hurwitz_zeta[of a "-{1}"]] assms(2,3)
  by (auto simp: o_def)

corollary analytic_zeta' [analytic_intros]:
  assumes "f analytic_on A" "(\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 1)"
  shows   "(\<lambda>x. zeta (f x)) analytic_on A"
  using analytic_on_compose_gen[OF assms(1) analytic_zeta[of "-{1}"]] assms(2)
  by (auto simp: o_def)


lemma logderiv_zeta_analytic: "(\<lambda>s. deriv zeta s / zeta s) analytic_on {s. Re s \<ge> 1} - {1}"
  using zeta_Re_ge_1_nonzero by (auto intro!: analytic_intros)

lemma cis_pi_half [simp]: "cis (pi / 2) = \<i>"
  by (simp add: complex_eq_iff)

lemma mult_real_sqrt: "x \<ge> 0 \<Longrightarrow> x * sqrt y = sqrt (x ^ 2 * y)"
  by (simp add: real_sqrt_mult)

lemma arcsin_pos: "x \<in> {0<..1} \<Longrightarrow> arcsin x > 0"
  using arcsin_less_arcsin[of 0 x] by simp

lemmas analytic_imp_holomorphic' = holomorphic_on_subset[OF analytic_imp_holomorphic]

lemma residue_simple':
  assumes "open s" "0 \<in> s" "f holomorphic_on s"
  shows   "residue (\<lambda>w. f w / w) 0 = f 0"
  using residue_simple[of s 0 f] assms by simp


lemma fds_converges_cong:
  assumes "eventually (\<lambda>n. fds_nth f n = fds_nth g n) at_top" "s = s'"
  shows   "fds_converges f s \<longleftrightarrow> fds_converges g s'"
  unfolding fds_converges_def
  by (intro summable_cong eventually_mono[OF assms(1)]) (simp_all add: assms)

lemma fds_abs_converges_cong:
  assumes "eventually (\<lambda>n. fds_nth f n = fds_nth g n) at_top" "s = s'"
  shows   "fds_abs_converges f s \<longleftrightarrow> fds_abs_converges g s'"
  unfolding fds_abs_converges_def
  by (intro summable_cong eventually_mono[OF assms(1)]) (simp_all add: assms)

lemma conv_abscissa_cong:
  assumes "eventually (\<lambda>n. fds_nth f n = fds_nth g n) at_top"
  shows   "conv_abscissa f = conv_abscissa g"
proof -
  have "fds_converges f = fds_converges g"
    by (intro ext fds_converges_cong assms refl)
  thus ?thesis by (simp add: conv_abscissa_def)
qed

lemma abs_conv_abscissa_cong:
  assumes "eventually (\<lambda>n. fds_nth f n = fds_nth g n) at_top"
  shows   "abs_conv_abscissa f = abs_conv_abscissa g"
proof -
  have "fds_abs_converges f = fds_abs_converges g"
    by (intro ext fds_abs_converges_cong assms refl)
  thus ?thesis by (simp add: abs_conv_abscissa_def)
qed


definition fds_remainder where
  "fds_remainder m = fds_subseries (\<lambda>n. n > m)"

lemma fds_nth_remainder: "fds_nth (fds_remainder m f) = (\<lambda>n. if n > m then fds_nth f n else 0)"
  by (simp add: fds_remainder_def fds_subseries_def fds_nth_fds')

lemma fds_converges_remainder_iff [simp]:
  "fds_converges (fds_remainder m f) s \<longleftrightarrow> fds_converges f s"
  by (intro fds_converges_cong eventually_mono[OF eventually_gt_at_top[of m]])
     (auto simp: fds_nth_remainder)

lemma fds_abs_converges_remainder_iff [simp]:
  "fds_abs_converges (fds_remainder m f) s \<longleftrightarrow> fds_abs_converges f s"
  by (intro fds_abs_converges_cong eventually_mono[OF eventually_gt_at_top[of m]])
     (auto simp: fds_nth_remainder)

lemma fds_converges_remainder [intro]:
        "fds_converges f s \<Longrightarrow> fds_converges (fds_remainder m f) s"
  and fds_abs_converges_remainder [intro]:
        "fds_abs_converges f s \<Longrightarrow> fds_abs_converges (fds_remainder m f) s"
  by simp_all

lemma conv_abscissa_remainder [simp]:
  "conv_abscissa (fds_remainder m f) = conv_abscissa f"
  by (intro conv_abscissa_cong eventually_mono[OF eventually_gt_at_top[of m]])
     (auto simp: fds_nth_remainder)

lemma abs_conv_abscissa_remainder [simp]:
  "abs_conv_abscissa (fds_remainder m f) = abs_conv_abscissa f"
  by (intro abs_conv_abscissa_cong eventually_mono[OF eventually_gt_at_top[of m]])
     (auto simp: fds_nth_remainder)

lemma eval_fds_remainder:
   "eval_fds (fds_remainder m f) s = (\<Sum>n. fds_nth f (n + Suc m) / nat_power (n + Suc m) s)"
    (is "_ = suminf (\<lambda>n. ?f (n + Suc m))")
proof (cases "fds_converges f s")
  case False
  hence "\<not>fds_converges (fds_remainder m f) s" by simp
  hence "(\<lambda>x. (\<lambda>n. fds_nth (fds_remainder m f) n / nat_power n s) sums x) = (\<lambda>_. False)"
    by (auto simp: fds_converges_def summable_def)
  hence "eval_fds (fds_remainder m f) s = (THE _. False)"
    by (simp add: eval_fds_def suminf_def)
  moreover from False have "\<not>summable (\<lambda>n. ?f (n + Suc m))" unfolding fds_converges_def
    by (subst summable_iff_shift) auto
  hence "(\<lambda>x. (\<lambda>n. ?f (n + Suc m)) sums x) = (\<lambda>_. False)"
    by (auto simp: summable_def)
  hence "suminf (\<lambda>n. ?f (n + Suc m)) = (THE _. False)"
    by (simp add: suminf_def)
  ultimately show ?thesis by simp
next
  case True
  hence *: "fds_converges (fds_remainder m f) s" by simp
  have "eval_fds (fds_remainder m f) s = (\<Sum>n. fds_nth (fds_remainder m f) n / nat_power n s)"
    unfolding eval_fds_def ..
  also have "\<dots> = (\<Sum>n. fds_nth (fds_remainder m f) (n + Suc m) / nat_power (n + Suc m) s)"
    using * unfolding fds_converges_def
    by (subst suminf_minus_initial_segment) (auto simp: fds_nth_remainder)
  also have "(\<lambda>n. fds_nth (fds_remainder m f) (n + Suc m)) = (\<lambda>n. fds_nth f (n + Suc m))"
    by (intro ext) (auto simp: fds_nth_remainder)
  finally show ?thesis .
qed

lemma fds_truncate_plus_remainder: "fds_truncate m f + fds_remainder m f = f"
  by (intro fds_eqI) (auto simp: fds_truncate_def fds_remainder_def fds_subseries_def)


lemma holomorphic_fds_eval' [holomorphic_intros]:
  assumes "g holomorphic_on A" "\<And>x. x \<in> A \<Longrightarrow> Re (g x) > conv_abscissa f"
  shows   "(\<lambda>x. eval_fds f (g x)) holomorphic_on A"
  using holomorphic_on_compose_gen[OF assms(1) holomorphic_fds_eval[OF order.refl, of f]] assms(2)
  by (auto simp: o_def)

lemma analytic_fds_eval' [analytic_intros]:
  assumes "g analytic_on A" "\<And>x. x \<in> A \<Longrightarrow> Re (g x) > conv_abscissa f"
  shows   "(\<lambda>x. eval_fds f (g x)) analytic_on A"
  using analytic_on_compose_gen[OF assms(1) analytic_fds_eval[OF order.refl, of f]] assms(2)
  by (auto simp: o_def)

lemma homotopic_loopsI:
  fixes h :: "real \<times> real \<Rightarrow> _"
  assumes "continuous_on ({0..1} \<times> {0..1}) h"
          "h ` ({0..1} \<times> {0..1}) \<subseteq> s"
          "\<And>x. x \<in> {0..1} \<Longrightarrow> h (0, x) = p x"
          "\<And>x. x \<in> {0..1} \<Longrightarrow> h (1, x) = q x"
          "\<And>x. x \<in> {0..1} \<Longrightarrow> pathfinish (h \<circ> Pair x) = pathstart (h \<circ> Pair x)"
  shows   "homotopic_loops s p q"
  using assms unfolding homotopic_loops by (intro exI[of _ h]) auto

lemma continuous_on_linepath [continuous_intros]:
  assumes "continuous_on A a" "continuous_on A b" "continuous_on A f"
  shows   "continuous_on A (\<lambda>x. linepath (a x) (b x) (f x))"
  using assms by (auto simp: linepath_def intro!: continuous_intros assms)

lemma continuous_on_part_circlepath [continuous_intros]:
  assumes "continuous_on A c" "continuous_on A r" "continuous_on A a" "continuous_on A b"
          "continuous_on A f"
  shows   "continuous_on A (\<lambda>x. part_circlepath (c x) (r x) (a x) (b x) (f x))"
  using assms by (auto simp: part_circlepath_def intro!: continuous_intros assms)

lemma homotopic_loops_part_circlepath:
  assumes "sphere c r \<subseteq> A" and "r \<ge> 0" and
          "b1 = a1 + 2 * of_int k * pi" and "b2 = a2 + 2 * of_int k * pi"
  shows   "homotopic_loops A (part_circlepath c r a1 b1) (part_circlepath c r a2 b2)"
proof -
  define h where "h = (\<lambda>(x,y). part_circlepath c r (linepath a1 a2 x) (linepath b1 b2 x) y)"
  show ?thesis
  proof (rule homotopic_loopsI)
    show "continuous_on ({0..1} \<times> {0..1}) h"
      by (auto simp: h_def case_prod_unfold intro!: continuous_intros)
  next
    from assms have "h ` ({0..1} \<times> {0..1}) \<subseteq> sphere c r"
      by (auto simp: h_def part_circlepath_def dist_norm norm_mult)
    also have "\<dots> \<subseteq> A" by fact
    finally show "h ` ({0..1} \<times> {0..1}) \<subseteq> A" .
  next
    fix x :: real assume x: "x \<in> {0..1}"
    show "h (0, x) = part_circlepath c r a1 b1 x" and "h (1, x) = part_circlepath c r a2 b2 x"
      by (simp_all add: h_def linepath_def)
    have "cis (pi * (real_of_int k * 2)) = 1"
      using cis.plus_of_int[of 0 k] by (simp add: algebra_simps)
    thus "pathfinish (h \<circ> Pair x) = pathstart (h \<circ> Pair x)"
      by (simp add: h_def o_def exp_eq_polar linepath_def algebra_simps
                    cis_mult [symmetric] cis_divide [symmetric] assms)
  qed
qed

lemma homotopic_pathsI:
  fixes h :: "real \<times> real \<Rightarrow> _"
  assumes "continuous_on ({0..1} \<times> {0..1}) h"
  assumes "h ` ({0..1} \<times> {0..1}) \<subseteq> s"
  assumes "\<And>x. x \<in> {0..1} \<Longrightarrow> h (0, x) = p x"
  assumes "\<And>x. x \<in> {0..1} \<Longrightarrow> h (1, x) = q x"
  assumes "\<And>x. x \<in> {0..1} \<Longrightarrow> pathstart (h \<circ> Pair x) = pathstart p"
  assumes "\<And>x. x \<in> {0..1} \<Longrightarrow> pathfinish (h \<circ> Pair x) = pathfinish p"
  shows   "homotopic_paths s p q"
  using assms unfolding homotopic_paths by (intro exI[of _ h]) auto

lemma part_circlepath_conv_subpath:
  "part_circlepath c r a b = subpath (a / (2*pi)) (b / (2*pi)) (circlepath c r)"
  by (simp add: part_circlepath_def circlepath_def subpath_def linepath_def algebra_simps exp_eq_polar)

lemma homotopic_paths_part_circlepath:
  assumes "a \<le> b" "b \<le> c"
  assumes "path_image (part_circlepath C r a c) \<subseteq> A" "r \<ge> 0"
  shows   "homotopic_paths A (part_circlepath C r a c)
             (part_circlepath C r a b +++ part_circlepath C r b c)"
  (is "homotopic_paths _ ?g (?h1 +++ ?h2)")
proof (cases "a = c")
  case False
  with assms have "a < c" by simp
  define slope where "slope = (b - a) / (c - a)"
  from assms and \<open>a < c\<close> have slope: "slope \<in> {0..1}"
    by (auto simp: field_simps slope_def)
  define f :: "real \<Rightarrow> real" where
    "f = linepath 0 slope +++ linepath slope 1"

  show ?thesis
  proof (rule homotopic_paths_reparametrize)
    fix t :: real assume t: "t \<in> {0..1}"
    show "(?h1 +++ ?h2) t = ?g (f t)"
    proof (cases "t \<le> 1 / 2")
      case True
      hence "?g (f t) = C + r * cis ((1 - f t) * a + f t * c)"
        by (simp add: joinpaths_def part_circlepath_def exp_eq_polar linepath_def)
      also from True \<open>a < c\<close> have "(1 - f t) * a + f t * c = (1 - 2 * t) * a + 2 * t * b"
        unfolding f_def slope_def linepath_def joinpaths_def
        by (simp add: divide_simps del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
           (simp add: algebra_simps)?
      also from True have "C + r * cis \<dots> = (?h1 +++ ?h2) t"
        by (simp add: joinpaths_def part_circlepath_def exp_eq_polar linepath_def)
      finally show ?thesis ..
    next
      case False
      hence "?g (f t) = C + r * cis ((1 - f t) * a + f t * c)"
        by (simp add: joinpaths_def part_circlepath_def exp_eq_polar linepath_def)
      also from False \<open>a < c\<close> have "(1 - f t) * a + f t * c = (2 - 2 * t) * b + (2 * t - 1) * c"
        unfolding f_def slope_def linepath_def joinpaths_def
        by (simp add: divide_simps del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
           (simp add: algebra_simps)?
      also from False have "C + r * cis \<dots> = (?h1 +++ ?h2) t"
        by (simp add: joinpaths_def part_circlepath_def exp_eq_polar linepath_def)
      finally show ?thesis ..
    qed
  next
    from slope have "path_image f \<subseteq> {0..1}"
      by (auto simp: f_def path_image_join closed_segment_eq_real_ivl)
    thus "f ` {0..1} \<subseteq> {0..1}" by (simp add: path_image_def)
  next
    have "path f" unfolding f_def by auto
    thus "continuous_on {0..1} f" by (simp add: path_def)
  qed (insert assms, auto simp: f_def joinpaths_def linepath_def)
next
  case [simp]: True
  with assms have [simp]: "b = c" by auto
  have "part_circlepath C r c c +++ part_circlepath C r c c = part_circlepath C r c c"
    by (simp add: fun_eq_iff joinpaths_def part_circlepath_def)
  thus ?thesis using assms by simp
qed

lemma has_contour_integral_mirror_iff:
  assumes "valid_path g"
  shows   "(f has_contour_integral I) (-g) \<longleftrightarrow> ((\<lambda>x. -f (- x)) has_contour_integral I) g"
proof -
  from assms have "g piecewise_differentiable_on {0..1}"
    by (auto simp: valid_path_def piecewise_C1_imp_differentiable)
  then obtain S where S: "finite S" "\<And>x. x \<in> {0..1} - S \<Longrightarrow> g differentiable at x within {0..1}"
     unfolding piecewise_differentiable_on_def by blast
  have S': "g differentiable at x" if "x \<in> {0..1} - ({0, 1} \<union> S)" for x
  proof -
    from that have "x \<in> interior {0..1}" by auto
    with S(2)[of x] that show ?thesis by (auto simp: at_within_interior[of _ "{0..1}"])
  qed

  have "(f has_contour_integral I) (-g) \<longleftrightarrow>
          ((\<lambda>x. f (- g x) * vector_derivative (-g) (at x)) has_integral I) {0..1}"
    by (simp add: has_contour_integral)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. -f (- g x) * vector_derivative g (at x)) has_integral I) {0..1}"
    by (intro has_integral_spike_finite_eq[of "S \<union> {0, 1}"])
       (insert \<open>finite S\<close> S', auto simp: o_def fun_Compl_def)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. -f (-x)) has_contour_integral I) g"
    by (simp add: has_contour_integral)
  finally show ?thesis .
qed

lemma contour_integral_on_mirror_iff:
  assumes "valid_path g"
  shows   "f contour_integrable_on (-g) \<longleftrightarrow> (\<lambda>x. -f (- x)) contour_integrable_on g"
  by (auto simp: contour_integrable_on_def has_contour_integral_mirror_iff assms)

lemma contour_integral_mirror:
  assumes "valid_path g"
  shows   "contour_integral (-g) f = contour_integral g (\<lambda>x. -f (- x))"
proof (cases "f contour_integrable_on (-g)")
  case True
  then obtain I where I: "(f has_contour_integral I) (-g)"
    by (auto simp: contour_integrable_on_def)
  also note has_contour_integral_mirror_iff[OF assms]
  finally have "((\<lambda>x. - f (- x)) has_contour_integral I) g" .
  with I show ?thesis using contour_integral_unique by blast
next
  case False
  hence "\<not>(\<lambda>x. -f (-x)) contour_integrable_on g"
    by (auto simp: contour_integral_on_mirror_iff assms)
  from False and this show ?thesis
    by (simp add: not_integrable_contour_integral)
qed

lemma contour_integrable_neg_iff:
  "(\<lambda>x. -f x) contour_integrable_on g \<longleftrightarrow> f contour_integrable_on g"
  using contour_integrable_neg[of f g] contour_integrable_neg[of "\<lambda>x. -f x" g] by auto

lemma contour_integral_neg:
  shows "contour_integral g (\<lambda>x. -f x) = -contour_integral g f"
proof (cases "f contour_integrable_on g")
  case True
  thus ?thesis by (simp add: contour_integral_neg)
next
  case False
  hence "\<not>(\<lambda>x. -f x) contour_integrable_on g" by (simp add: contour_integrable_neg_iff)
  with False show ?thesis
    by (simp add: not_integrable_contour_integral)
qed


lemma minus_cis: "-cis x = cis (x + pi)"
  by (simp add: complex_eq_iff)

lemma path_image_part_circlepath_subset:
  assumes "a \<le> a'" "a' \<le> b'" "b' \<le> b"
  shows   "path_image (part_circlepath c r a' b') \<subseteq> path_image (part_circlepath c r a b)"
  using assms by (subst (1 2) path_image_part_circlepath) auto

lemma part_circlepath_mirror:
  assumes "a' = a + pi + 2 * pi * of_int k" "b' = b + pi + 2 * pi * of_int k" "c' = -c"
  shows   "-part_circlepath c r a b = part_circlepath c' r a' b'"
proof
  fix x :: real
  have "part_circlepath c' r a' b' x = c' + r * cis (linepath a b x + pi + k * (2 * pi))"
    by (simp add: part_circlepath_def exp_eq_polar assms linepath_translate_right mult_ac)
  also have "cis (linepath a b x + pi + k * (2 * pi)) = cis (linepath a b x + pi)"
    by (rule cis.plus_of_int)
  also have "\<dots> = -cis (linepath a b x)"
    by (simp add: minus_cis)
  also have "c' + r * \<dots> = -part_circlepath c r a b x"
    by (simp add: part_circlepath_def assms exp_eq_polar)
  finally show "(- part_circlepath c r a b) x = part_circlepath c' r a' b' x"
    by simp
qed

lemma path_mirror [intro]: "path (g :: _ \<Rightarrow> 'b::topological_group_add) \<Longrightarrow> path (-g)"
  by (auto simp: path_def intro!: continuous_intros)

lemma path_mirror_iff [simp]: "path (-g :: _ \<Rightarrow> 'b::topological_group_add) \<longleftrightarrow> path g"
  using path_mirror[of g] path_mirror[of "-g"] by (auto simp: fun_Compl_def)

lemma valid_path_mirror [intro]: "valid_path g \<Longrightarrow> valid_path (-g)"
  by (auto simp: valid_path_def fun_Compl_def piecewise_C1_differentiable_neg)

lemma valid_path_mirror_iff [simp]: "valid_path (-g) \<longleftrightarrow> valid_path g"
  using valid_path_mirror[of g] valid_path_mirror[of "-g"] by (auto simp: fun_Compl_def)

lemma pathstart_mirror [simp]: "pathstart (-g) = -pathstart g"
  and pathfinish_mirror [simp]: "pathfinish (-g) = -pathfinish g"
  by (simp_all add: pathstart_def pathfinish_def)

lemma path_image_mirror: "path_image (-g) = uminus ` path_image g"
  by (auto simp: path_image_def)

lemma contour_integral_bound_part_circlepath:
  assumes "f contour_integrable_on part_circlepath c r a b"
  assumes "B \<ge> 0" "r \<ge> 0" "\<And>x. x \<in> path_image (part_circlepath c r a b) \<Longrightarrow> norm (f x) \<le> B"
  shows   "norm (contour_integral (part_circlepath c r a b) f) \<le> B * r * \<bar>b - a\<bar>"
proof -
  let ?I = "integral {0..1} (\<lambda>x. f (part_circlepath c r a b x) * \<i> * of_real (r * (b - a)) *
              exp (\<i> * linepath a b x))"
  have "norm ?I \<le> integral {0..1} (\<lambda>x::real. B * 1 * (r * \<bar>b - a\<bar>) * 1)"
  proof (rule integral_norm_bound_integral, goal_cases)
    case 1
    with assms(1) show ?case
      by (simp add: contour_integrable_on vector_derivative_part_circlepath mult_ac)
  next
    case (3 x)
    with assms(2-) show ?case unfolding norm_mult norm_of_real abs_mult
      by (intro mult_mono) (auto simp: path_image_def)
  qed auto
  also have "?I = contour_integral (part_circlepath c r a b) f"
    by (simp add: contour_integral_integral vector_derivative_part_circlepath mult_ac)
  finally show ?thesis by simp
qed

lemma contour_integral_spike_finite_simple_path:
  assumes "finite A" "simple_path g" "g = g'" "\<And>x. x \<in> path_image g - A \<Longrightarrow> f x = f' x"
  shows   "contour_integral g f = contour_integral g' f'"
  unfolding contour_integral_integral
proof (rule integral_spike)
  have "finite (g -` A \<inter> {0<..<1})" using \<open>simple_path g\<close> \<open>finite A\<close>
    by (intro finite_vimage_IntI simple_path_inj_on) auto
  hence "finite ({0, 1} \<union> g -` A \<inter> {0<..<1})" by auto
  thus "negligible ({0, 1} \<union> g -` A \<inter> {0<..<1})" by (rule negligible_finite)
next
  fix x assume "x \<in> {0..1} - ({0, 1} \<union> g -` A \<inter> {0<..<1})"
  hence "g x \<in> path_image g - A" by (auto simp: path_image_def)
  from assms(4)[OF this] and assms(3)
    show "f' (g' x) * vector_derivative g' (at x) = f (g x) * vector_derivative g (at x)" by simp
  qed

proposition contour_integral_bound_part_circlepath_strong:
  assumes fi: "f contour_integrable_on part_circlepath z r s t"
      and "finite k" and le: "0 \<le> B" "0 < r" "s \<le> t"
      and B: "\<And>x. x \<in> path_image(part_circlepath z r s t) - k \<Longrightarrow> norm(f x) \<le> B"
    shows "cmod (contour_integral (part_circlepath z r s t) f) \<le> B * r * (t - s)"
proof -
  from fi have "(f has_contour_integral contour_integral (part_circlepath z r s t) f)
                  (part_circlepath z r s t)"
    by (rule has_contour_integral_integral)
  from has_contour_integral_bound_part_circlepath_strong[OF this assms(2-)] show ?thesis by auto
qed

lemma cos_le_zero:
  assumes "x \<in> {pi/2..3*pi/2}"
  shows   "cos x \<le> 0"
proof -
  have "cos x = -cos (x - pi)" by (simp add: cos_diff)
  moreover from assms have "cos (x - pi) \<ge> 0"
    by (intro cos_ge_zero) auto
  ultimately show ?thesis by simp
qed

lemma cos_le_zero': "x \<in> {-3*pi/2..-pi/2} \<Longrightarrow> cos x \<le> 0"
  using cos_le_zero[of "-x"] by simp

lemma cis_minus_pi_half [simp]: "cis (- (pi / 2)) = -\<i>"
  by (simp add: complex_eq_iff)

lemma winding_number_join_pos_combined':
     "\<lbrakk>valid_path \<gamma>1 \<and> z \<notin> path_image \<gamma>1 \<and> 0 < Re (winding_number \<gamma>1 z);
       valid_path \<gamma>2 \<and> z \<notin> path_image \<gamma>2 \<and> 0 < Re (winding_number \<gamma>2 z);
       pathfinish \<gamma>1 = pathstart \<gamma>2\<rbrakk>
      \<Longrightarrow> valid_path(\<gamma>1 +++ \<gamma>2) \<and> z \<notin> path_image(\<gamma>1 +++ \<gamma>2) \<and> 0 < Re(winding_number(\<gamma>1 +++ \<gamma>2) z)"
  by (simp add: valid_path_join path_image_join winding_number_join valid_path_imp_path)

lemma Union_atLeastAtMost_real_of_nat:
  assumes "a < b"
  shows   "(\<Union>n\<in>{a..<b}. {real n..real (n + 1)}) = {real a..real b}"
proof (intro equalityI subsetI)
  fix x assume x: "x \<in> {real a..real b}"
  thus "x \<in> (\<Union>n\<in>{a..<b}. {real n..real (n + 1)})"
  proof (cases "x = real b")
    case True
    with assms show ?thesis by (auto intro!: bexI[of _ "b - 1"])
  next
    case False
    with x have x: "x \<ge> real a" "x < real b" by simp_all
    hence "x \<ge> real (nat \<lfloor>x\<rfloor>)" "x \<le> real (Suc (nat \<lfloor>x\<rfloor>))" by linarith+
    moreover from x have "nat \<lfloor>x\<rfloor> \<ge> a" "nat \<lfloor>x\<rfloor> < b" by linarith+
    ultimately have "\<exists>n\<in>{a..<b}. x \<in> {real n..real (n + 1)}"
      by (intro bexI[of _ "nat \<lfloor>x\<rfloor>"]) simp_all
    thus ?thesis by blast
  qed
qed auto

lemma nat_sum_has_integral_floor:
  fixes f :: "nat \<Rightarrow> 'a :: banach"
  assumes mn: "m < n"
  shows "((\<lambda>x. f (nat \<lfloor>x\<rfloor>)) has_integral sum f {m..<n}) {real m..real n}"
proof -
  define D where "D = (\<lambda>i. {real i..real (Suc i)}) ` {m..<n}"
  have D: "D division_of {m..n}"
    using Union_atLeastAtMost_real_of_nat[OF mn] by (simp add: division_of_def D_def)
  have "((\<lambda>x. f (nat \<lfloor>x\<rfloor>)) has_integral (\<Sum>X\<in>D. f (nat \<lfloor>Inf X\<rfloor>))) {real m..real n}"
  proof (rule has_integral_combine_division)
    fix X assume X: "X \<in> D"
    have "nat \<lfloor>x\<rfloor> = nat \<lfloor>Inf X\<rfloor>" if "x \<in> X - {Sup X}" for x
      using that X by (auto simp: D_def nat_eq_iff floor_eq_iff)
    hence "((\<lambda>x. f (nat \<lfloor>x\<rfloor>)) has_integral f (nat \<lfloor>Inf X\<rfloor>)) X \<longleftrightarrow>
           ((\<lambda>x. f (nat \<lfloor>Inf X\<rfloor>)) has_integral f (nat \<lfloor>Inf X\<rfloor>)) X" using X
      by (intro has_integral_spike_eq[of "{Sup X}"]) auto
    also from X have "\<dots>" using has_integral_const_real[of "f (nat \<lfloor>Inf X\<rfloor>)" "Inf X" "Sup X"]
      by (auto simp: D_def)
    finally show "((\<lambda>x. f (nat \<lfloor>x\<rfloor>)) has_integral f (nat \<lfloor>Inf X\<rfloor>)) X" .
  qed fact+
  also have "(\<Sum>X\<in>D. f (nat \<lfloor>Inf X\<rfloor>)) = (\<Sum>k\<in>{m..<n}. f k)"
    unfolding D_def by (subst sum.reindex) (auto simp: inj_on_def nat_add_distrib)
  finally show ?thesis .
qed

lemma nat_sum_has_integral_ceiling:
  fixes f :: "nat \<Rightarrow> 'a :: banach"
  assumes mn: "m < n"
  shows "((\<lambda>x. f (nat \<lceil>x\<rceil>)) has_integral sum f {m<..n}) {real m..real n}"
proof -
  define D where "D = (\<lambda>i. {real i..real (Suc i)}) ` {m..<n}"
  have D: "D division_of {m..n}"
    using Union_atLeastAtMost_real_of_nat[OF mn] by (simp add: division_of_def D_def)
  have "((\<lambda>x. f (nat \<lceil>x\<rceil>)) has_integral (\<Sum>X\<in>D. f (nat \<lfloor>Sup X\<rfloor>))) {real m..real n}"
  proof (rule has_integral_combine_division)
    fix X assume X: "X \<in> D"
    have "nat \<lceil>x\<rceil> = nat \<lfloor>Sup X\<rfloor>" if "x \<in> X - {Inf X}" for x
      using that X by (auto simp: D_def nat_eq_iff ceiling_eq_iff)
    hence "((\<lambda>x. f (nat \<lceil>x\<rceil>)) has_integral f (nat \<lfloor>Sup X\<rfloor>)) X \<longleftrightarrow>
           ((\<lambda>x. f (nat \<lfloor>Sup X\<rfloor>)) has_integral f (nat \<lfloor>Sup X\<rfloor>)) X" using X
      by (intro has_integral_spike_eq[of "{Inf X}"]) auto
    also from X have "\<dots>" using has_integral_const_real[of "f (nat \<lfloor>Sup X\<rfloor>)" "Inf X" "Sup X"]
      by (auto simp: D_def)
    finally show "((\<lambda>x. f (nat \<lceil>x\<rceil>)) has_integral f (nat \<lfloor>Sup X\<rfloor>)) X" .
  qed fact+
  also have "(\<Sum>X\<in>D. f (nat \<lfloor>Sup X\<rfloor>)) = (\<Sum>k\<in>{m..<n}. f (Suc k))"
    unfolding D_def by (subst sum.reindex) (auto simp: inj_on_def nat_add_distrib)
  also have "\<dots> = (\<Sum>k\<in>{m<..n}. f k)"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>x. x - 1" Suc]) auto
  finally show ?thesis .
qed

lemma zeta_partial_sum_le:
  fixes x :: real and m :: nat
  assumes x: "x \<in> {0<..1}"
  shows "(\<Sum>k=1..m. real k powr (x - 1)) \<le> real m powr x / x"
proof -
  consider "m = 0" | "m = 1" | "m > 1" by force
  thus ?thesis
  proof cases
    assume m: "m > 1"
    hence "{1..m} = insert 1 {1<..m}" by auto
    also have "(\<Sum>k\<in>\<dots>. real k powr (x - 1)) = 1 + (\<Sum>k\<in>{1<..m}. real k powr (x - 1))"
      by simp
    also have "(\<Sum>k\<in>{1<..m}. real k powr (x - 1)) \<le> real m powr x / x - 1 / x"
    proof (rule has_integral_le)
      show "((\<lambda>t. (nat \<lceil>t\<rceil>) powr (x - 1)) has_integral (\<Sum>n\<in>{1<..m}. n powr (x - 1))) {real 1..m}"
        using m by (intro nat_sum_has_integral_ceiling) auto
    next
      have "((\<lambda>t. t powr (x - 1)) has_integral (real m powr x / x - real 1 powr x / x))
              {real 1..real m}"
        by (intro fundamental_theorem_of_calculus)
           (insert x m, auto simp flip: has_field_derivative_iff_has_vector_derivative
                             intro!: derivative_eq_intros)
      thus "((\<lambda>t. t powr (x - 1)) has_integral (real m powr x / x - 1 / x)) {real 1..real m}"
        by simp
    qed (insert x, auto intro!: powr_mono2')
    also have "1 + (real m powr x / x - 1 / x) \<le> real m powr x / x"
      using x by (simp add: field_simps)
    finally show ?thesis by simp
  qed (use assms in auto)
qed

lemma zeta_partial_sum_le':
  fixes x :: real and m :: nat
  assumes x: "x > 0" and m: "m > 0"
  shows   "(\<Sum>n=1..m. real n powr (x - 1)) \<le> m powr x * (1 / x + 1 / m)"
proof (cases "x > 1")
  case False
  with assms have "(\<Sum>n=1..m. real n powr (x - 1)) \<le> m powr x / x"
    by (intro zeta_partial_sum_le) auto
  also have "\<dots> \<le> m powr x * (1 / x + 1 / m)"
    using assms by (simp add: field_simps)
  finally show ?thesis .
next
  case True
  have "(\<Sum>n\<in>{1..m}. n powr (x - 1)) = (\<Sum>n\<in>insert m {0..<m}. n powr (x - 1))"
    by (intro sum.mono_neutral_left) auto
  also have "\<dots> = m powr (x - 1) + (\<Sum>n\<in>{0..<m}. n powr (x - 1))" by simp
  also have "(\<Sum>n\<in>{0..<m}. n powr (x - 1)) \<le> real m powr x / x"
  proof (rule has_integral_le)
    show "((\<lambda>t. (nat \<lfloor>t\<rfloor>) powr (x - 1)) has_integral (\<Sum>n\<in>{0..<m}. n powr (x - 1))) {real 0..m}"
      using m by (intro nat_sum_has_integral_floor) auto
  next
    show "((\<lambda>t. t powr (x - 1)) has_integral (real m powr x / x)) {real 0..real m}"
      using has_integral_powr_from_0[of "x - 1"] x by auto
  next
    fix t assume "t \<in> {real 0..real m}"
    with \<open>x > 1\<close> show "real (nat \<lfloor>t\<rfloor>) powr (x - 1) \<le> t powr (x - 1)"
      by (cases "t = 0") (auto intro: powr_mono2)
  qed
  also have "m powr (x - 1) + m powr x / x = m powr x * (1 / x + 1 / m)"
    using m x by (simp add: powr_diff field_simps)
  finally show ?thesis by simp
qed

lemma natfun_bigo_1E:
  assumes "(f :: nat \<Rightarrow> _) \<in> O(\<lambda>_. 1)"
  obtains C where "C \<ge> lb" "\<And>n. norm (f n) \<le> C"
proof -
  from assms obtain C N where "\<forall>n\<ge>N. norm (f n) \<le> C"
    by (auto elim!: landau_o.bigE simp: eventually_at_top_linorder)
  hence *: "norm (f n) \<le> Max ({C, lb} \<union> (norm ` f ` {..<N}))" for n
    by (cases "n \<ge> N") (subst Max_ge_iff; force simp: image_iff)+
  moreover have "Max ({C, lb} \<union> (norm ` f ` {..<N})) \<ge> lb"
    by (intro Max.coboundedI) auto
  ultimately show ?thesis using that by blast
qed

lemma natfun_bigo_iff_Bseq: "f \<in> O(\<lambda>_. 1) \<longleftrightarrow> Bseq f"
proof
  assume "Bseq f"
  then obtain C where "C > 0" "\<And>n. norm (f n) \<le> C" by (auto simp: Bseq_def)
  thus "f \<in> O(\<lambda>_. 1)" by (intro bigoI[of _ C]) auto
next
  assume "f \<in> O(\<lambda>_. 1)"
  from natfun_bigo_1E[OF this, where lb = 1] obtain C where "C \<ge> 1" "\<And>n. norm (f n) \<le> C"
    by auto
  thus "Bseq f" by (auto simp: Bseq_def intro!: exI[of _ C])
qed

lemma enn_decreasing_sum_le_set_nn_integral:
  fixes f :: "real \<Rightarrow> ennreal"
  assumes decreasing: "\<And>x y. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> f y \<le> f x"
  shows "(\<Sum>n. f (real (Suc n))) \<le> set_nn_integral lborel {0..} f"
proof -
  have "(\<Sum>n. (f (Suc n))) =
          (\<Sum>n. \<integral>\<^sup>+x\<in>{real n<..real (Suc n)}. (f (Suc n)) \<partial>lborel)"
    by (subst nn_integral_cmult_indicator) auto
  also have "nat \<lceil>x\<rceil> = Suc n" if "x \<in> {real n<..real (Suc n)}" for x n
    using that by (auto simp: nat_eq_iff ceiling_eq_iff)
  hence "(\<Sum>n. \<integral>\<^sup>+x\<in>{real n<..real (Suc n)}. (f (Suc n)) \<partial>lborel) =
          (\<Sum>n. \<integral>\<^sup>+x\<in>{real n<..real (Suc n)}. (f (real (nat \<lceil>x\<rceil>))) \<partial>lborel)"
    by (intro suminf_cong nn_integral_cong) (auto simp: indicator_def)
  also have "\<dots> = (\<integral>\<^sup>+x\<in>(\<Union>i. {real i<..real (Suc i)}). (f (nat \<lceil>x::real\<rceil>)) \<partial>lborel)"
    by (subst nn_integral_disjoint_family)
       (auto simp: disjoint_family_on_def)
  also have "\<dots> \<le> (\<integral>\<^sup>+x\<in>{0..}. (f x) \<partial>lborel)"
    by (intro nn_integral_mono) (auto simp: indicator_def intro!: decreasing)
  finally show ?thesis .
qed

(* TODO replace version in library *)
lemma nn_integral_has_integral_lebesgue:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes nonneg: "\<And>x. x \<in> \<Omega> \<Longrightarrow> 0 \<le> f x" and I: "(f has_integral I) \<Omega>"
  shows "integral\<^sup>N lborel (\<lambda>x. indicator \<Omega> x * f x) = I"
proof -
  from I have "(\<lambda>x. indicator \<Omega> x *\<^sub>R f x) \<in> lebesgue \<rightarrow>\<^sub>M borel"
    by (rule has_integral_implies_lebesgue_measurable)
  then obtain f' :: "'a \<Rightarrow> real"
    where [measurable]: "f' \<in> borel \<rightarrow>\<^sub>M borel" and eq: "AE x in lborel. indicator \<Omega> x * f x = f' x"
    by (auto dest: completion_ex_borel_measurable_real)

  from I have "((\<lambda>x. abs (indicator \<Omega> x * f x)) has_integral I) UNIV"
    using nonneg by (simp add: indicator_def if_distrib[of "\<lambda>x. x * f y" for y] cong: if_cong)
  also have "((\<lambda>x. abs (indicator \<Omega> x * f x)) has_integral I) UNIV \<longleftrightarrow> ((\<lambda>x. abs (f' x)) has_integral I) UNIV"
    using eq by (intro has_integral_AE) auto
  finally have "integral\<^sup>N lborel (\<lambda>x. abs (f' x)) = I"
    by (rule nn_integral_has_integral_lborel[rotated 2]) auto
  also have "integral\<^sup>N lborel (\<lambda>x. abs (f' x)) = integral\<^sup>N lborel (\<lambda>x. abs (indicator \<Omega> x * f x))"
    using eq by (intro nn_integral_cong_AE) auto
  also have "(\<lambda>x. abs (indicator \<Omega> x * f x)) = (\<lambda>x. indicator \<Omega> x * f x)"
    using nonneg by (auto simp: indicator_def fun_eq_iff)
  finally show ?thesis .
qed

lemma decreasing_sum_le_integral:
  fixes f :: "real \<Rightarrow> real"
  assumes nonneg: "\<And>x. x \<ge> 0 \<Longrightarrow> f x \<ge> 0"
  assumes decreasing: "\<And>x y. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> f y \<le> f x"
  assumes integral: "(f has_integral I) {0..}"
  shows   "summable (\<lambda>i. f (real (Suc i)))" and "suminf (\<lambda>i. f (real (Suc i))) \<le> I"
proof -
  have [simp]: "I \<ge> 0"
    by (intro has_integral_nonneg[OF integral] nonneg) auto
  have "(\<Sum>n. ennreal (f (Suc n))) =
          (\<Sum>n. \<integral>\<^sup>+x\<in>{real n<..real (Suc n)}. ennreal (f (Suc n)) \<partial>lborel)"
    by (subst nn_integral_cmult_indicator) auto
  also have "nat \<lceil>x\<rceil> = Suc n" if "x \<in> {real n<..real (Suc n)}" for x n
    using that by (auto simp: nat_eq_iff ceiling_eq_iff)
  hence "(\<Sum>n. \<integral>\<^sup>+x\<in>{real n<..real (Suc n)}. ennreal (f (Suc n)) \<partial>lborel) =
          (\<Sum>n. \<integral>\<^sup>+x\<in>{real n<..real (Suc n)}. ennreal (f (real (nat \<lceil>x\<rceil>))) \<partial>lborel)"
    by (intro suminf_cong nn_integral_cong) (auto simp: indicator_def)
  also have "\<dots> = (\<integral>\<^sup>+x\<in>(\<Union>i. {real i<..real (Suc i)}). ennreal (f (nat \<lceil>x::real\<rceil>)) \<partial>lborel)"
    by (subst nn_integral_disjoint_family)
       (auto simp: disjoint_family_on_def intro!: measurable_completion)
  also have "\<dots> \<le> (\<integral>\<^sup>+x\<in>{0..}. ennreal (f x) \<partial>lborel)"
    by (intro nn_integral_mono) (auto simp: indicator_def nonneg intro!: decreasing)
  also have "\<dots> = (\<integral>\<^sup>+ x. ennreal (indicat_real {0..} x * f x) \<partial>lborel)"
    by (intro nn_integral_cong) (auto simp: indicator_def)
  also have "\<dots> = ennreal I"
    using nn_integral_has_integral_lebesgue[OF nonneg integral] by (auto simp: nonneg)
  finally have *: "(\<Sum>n. ennreal (f (Suc n))) \<le> ennreal I" .
  from * show summable: "summable (\<lambda>i. f (real (Suc i)))"
    by (intro summable_suminf_not_top) (auto simp: top_unique intro: nonneg)
  note *
  also from summable have "(\<Sum>n. ennreal (f (Suc n))) = ennreal (\<Sum>n. f (Suc n))"
    by (subst suminf_ennreal2) (auto simp: o_def nonneg)
  finally show "(\<Sum>n. f (real (Suc n))) \<le> I" by (subst (asm) ennreal_le_iff) auto
qed

lemma decreasing_sum_le_integral':
  fixes f :: "real \<Rightarrow> real"
  assumes "\<And>x. x \<ge> 0 \<Longrightarrow> f x \<ge> 0"
  assumes "\<And>x y. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> f y \<le> f x"
  assumes "(f has_integral I) {0..}"
  shows   "summable (\<lambda>i. f (real i))" and "suminf (\<lambda>i. f (real i)) \<le> f 0 + I"
proof -
  have "summable ((\<lambda>i. f (real (Suc i))))"
    using decreasing_sum_le_integral[OF assms] by (simp add: o_def)
  thus *: "summable (\<lambda>i. f (real i))" by (subst (asm) summable_Suc_iff)
  have "(\<Sum>n. f (real (Suc n))) \<le> I" by (intro decreasing_sum_le_integral assms)
  thus "suminf (\<lambda>i. f (real i)) \<le> f 0 + I"
    using * by (subst (asm) suminf_split_head) auto
qed

lemma norm_suminf_le:
  assumes "\<And>n. norm (f n :: 'a :: banach) \<le> g n" "summable g"
  shows   "norm (suminf f) \<le> suminf g"
proof -
  have *: "summable (\<lambda>n. norm (f n))" using assms
    by (intro summable_norm summable_comparison_test[OF _ assms(2)] exI[of _ 0]) auto
  hence "norm (suminf f) \<le> (\<Sum>n. norm (f n))" by (intro summable_norm) auto
  also have "\<dots> \<le> suminf g" by (intro suminf_le * assms allI)
  finally show ?thesis .
qed

lemma of_nat_powr_neq_1_complex [simp]:
  assumes "n > 1" "Re s \<noteq> 0"
  shows   "of_nat n powr s \<noteq> (1::complex)"
proof -
  have "norm (of_nat n powr s) = real n powr Re s"
    by (simp add: norm_powr_real_powr)
  also have "\<dots> \<noteq> 1"
    using assms by (auto simp: powr_def)
  finally show ?thesis by auto
qed

lemma abs_summable_on_uminus_iff:
  "(\<lambda>x. -f x) abs_summable_on A \<longleftrightarrow> f abs_summable_on A"
  using abs_summable_on_uminus[of f A] abs_summable_on_uminus[of "\<lambda>x. -f x" A] by auto

lemma abs_summable_on_cmult_right_iff:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_field, second_countable_topology}"
  assumes "c \<noteq> 0"
  shows   "(\<lambda>x. c * f x) abs_summable_on A \<longleftrightarrow> f abs_summable_on A"
  using assms abs_summable_on_cmult_right[of c f A]
        abs_summable_on_cmult_right[of "inverse c" "\<lambda>x. c * f x" A] by (auto simp: field_simps)

lemma abs_summable_on_cmult_left_iff:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_field, second_countable_topology}"
  assumes "c \<noteq> 0"
  shows   "(\<lambda>x. f x * c) abs_summable_on A \<longleftrightarrow> f abs_summable_on A"
  using assms abs_summable_on_cmult_left[of c f A]
        abs_summable_on_cmult_left[of "inverse c" "\<lambda>x. f x * c" A] by (auto simp: field_simps)

lemma fds_logderiv_completely_multiplicative:
  fixes f :: "'a :: {real_normed_field} fds"
  assumes "completely_multiplicative_function (fds_nth f)" "fds_nth f 1 \<noteq> 0"
  shows   "fds_deriv f / f = - fds (\<lambda>n. fds_nth f n * mangoldt n)"
proof -
  have "fds_deriv f / f = - fds (\<lambda>n. fds_nth f n * mangoldt n) * f / f"
    using completely_multiplicative_fds_deriv[of "fds_nth f"] assms by simp
  also have "\<dots> = - fds (\<lambda>n. fds_nth f n * mangoldt n)"
    using assms by (simp add: divide_fds_def fds_right_inverse)
  finally show ?thesis .
qed

lemma fds_nth_logderiv_completely_multiplicative:
  fixes f :: "'a :: {real_normed_field} fds"
  assumes "completely_multiplicative_function (fds_nth f)" "fds_nth f 1 \<noteq> 0"
  shows   "fds_nth (fds_deriv f / f) n = -fds_nth f n * mangoldt n"
  using assms by (subst fds_logderiv_completely_multiplicative) (simp_all add: fds_nth_fds')

lemma eval_fds_logderiv_completely_multiplicative:
  fixes s :: "'a :: dirichlet_series" and l :: 'a and f :: "'a fds"
  defines "h \<equiv> fds_deriv f / f"
  assumes "completely_multiplicative_function (fds_nth f)" and [simp]: "fds_nth f 1 \<noteq> 0"
  assumes "s \<bullet> 1 > abs_conv_abscissa f"
  shows  "(\<lambda>p. of_real (ln (real p)) * (1 / (1 - fds_nth f p / nat_power p s) - 1))
            abs_summable_on {p. prime p}" (is ?th1)
    and  "eval_fds h s = -(\<Sum>\<^sub>ap | prime p. of_real (ln (real p)) *
                            (1 / (1 - fds_nth f p / nat_power p s) - 1))" (is ?th2)
proof -
  let ?P = "{p::nat. prime p}"
  interpret f: completely_multiplicative_function "fds_nth f" by fact
  have "fds_abs_converges h s"
    using abs_conv_abscissa_completely_multiplicative_log_deriv[OF assms(2)] assms
    by (intro fds_abs_converges) auto
  hence *: "(\<lambda>n. fds_nth h n / nat_power n s) abs_summable_on UNIV"
    by (auto simp: h_def fds_abs_converges_altdef')

  note *
  also have "(\<lambda>n. fds_nth h n / nat_power n s) abs_summable_on UNIV \<longleftrightarrow>
          (\<lambda>x. -fds_nth f x * mangoldt x / nat_power x s) abs_summable_on Collect primepow"
    unfolding h_def using fds_nth_logderiv_completely_multiplicative[OF assms(2)]
    by (intro abs_summable_on_cong_neutral) (auto simp: fds_nth_fds mangoldt_def)
  finally have sum1: "(\<lambda>x. -fds_nth f x * mangoldt x / nat_power x s)
                      abs_summable_on Collect primepow"
    by (rule abs_summable_on_subset) auto
  also have "?this \<longleftrightarrow> (\<lambda>(p,k). -fds_nth f (p ^ Suc k) * mangoldt (p ^ Suc k) /
                                nat_power (p ^ Suc k) s) abs_summable_on (?P \<times> UNIV)"
    using bij_betw_primepows unfolding case_prod_unfold
    by (intro abs_summable_on_reindex_bij_betw [symmetric])
  also have "\<dots> \<longleftrightarrow> (\<lambda>(p,k). -((fds_nth f p / nat_power p s) ^ Suc k * of_real (ln (real p))))
                abs_summable_on (?P \<times> UNIV)"
    unfolding case_prod_unfold
    by (intro abs_summable_on_cong, subst mangoldt_primepow)
       (auto simp: f.mult f.power nat_power_mult_distrib nat_power_power_left power_divide
             dest: prime_gt_1_nat)
  finally have sum2: \<dots> .

  have sum4: "summable (\<lambda>n. (norm (fds_nth f p / nat_power p s)) ^ Suc n)" if p: "prime p" for p
  proof -
    have "summable (\<lambda>n. \<bar>ln (real p)\<bar> * (norm (fds_nth f p / nat_power p s)) ^ Suc n)"
      using p abs_summable_on_Sigma_project2[OF sum2, of p] unfolding abs_summable_on_nat_iff'
      by (simp add: norm_power norm_mult norm_divide mult_ac del: power_Suc)
    thus ?thesis by (rule summable_mult_D) (insert p, auto dest: prime_gt_1_nat)
  qed
  have sums: "(\<lambda>n. (fds_nth f p / nat_power p s) ^ Suc n) sums
                (1 / (1 - fds_nth f p / nat_power p s) - 1)" if p: "prime p" for p :: nat
  proof -
    from sum4[OF p] have "norm (fds_nth f p / nat_power p s) < 1"
      unfolding summable_Suc_iff by (simp add: summable_geometric_iff)
    from geometric_sums[OF this] show ?thesis by (subst sums_Suc_iff) auto
  qed

  have eq: "(\<Sum>\<^sub>ak. - ((fds_nth f p / nat_power p s) ^ Suc k * of_real (ln (real p)))) =
               -(of_real (ln (real p)) * (1 / (1 - fds_nth f p / nat_power p s) - 1))"
    if p: "prime p" for p
  proof -
    have "(\<Sum>\<^sub>ak. - ((fds_nth f p / nat_power p s) ^ Suc k * of_real (ln (real p)))) =
             (\<Sum>\<^sub>ak. (fds_nth f p / nat_power p s) ^ Suc k) * of_real (-ln (real p))"
      using sum4[of p] p
      by (subst infsetsum_cmult_left [symmetric])
         (auto simp: abs_summable_on_nat_iff' norm_power simp del: power_Suc)
    also have "(\<Sum>\<^sub>ak. (fds_nth f p / nat_power p s) ^ Suc k) =
                 (1 / (1 - fds_nth f p / nat_power p s) - 1)" using sum4[OF p] sums[OF p]
      by (subst infsetsum_nat')
         (auto simp: sums_iff abs_summable_on_nat_iff' norm_power simp del: power_Suc)
    finally show ?thesis by (simp add: mult_ac)
  qed

  have sum3: "(\<lambda>x. \<Sum>\<^sub>ay. - ((fds_nth f x / nat_power x s) ^ Suc y * of_real (ln (real x))))
                 abs_summable_on {p. prime p}"
    using sum2 by (rule abs_summable_on_Sigma_project1') auto
  also have "?this \<longleftrightarrow> (\<lambda>p. -(of_real (ln (real p)) *
                (1 / (1 - fds_nth f p / nat_power p s) - 1))) abs_summable_on {p. prime p}"
    by (intro abs_summable_on_cong eq) auto
  also have "\<dots> \<longleftrightarrow> ?th1" by (subst abs_summable_on_uminus_iff) auto
  finally show ?th1 .

  have "eval_fds h s = (\<Sum>\<^sub>an. fds_nth h n / nat_power n s)"
    using * unfolding eval_fds_def by (subst infsetsum_nat') auto
  also have "\<dots> = (\<Sum>\<^sub>an \<in> {n. primepow n}. -fds_nth f n * mangoldt n / nat_power n s)"
    unfolding h_def using fds_nth_logderiv_completely_multiplicative[OF assms(2)]
    by (intro infsetsum_cong_neutral) (auto simp: fds_nth_fds mangoldt_def)
  also have "\<dots> = (\<Sum>\<^sub>a(p,k)\<in>(?P \<times> UNIV). -fds_nth f (p ^ Suc k) * mangoldt (p ^ Suc k) /
                                            nat_power (p ^ Suc k) s)"
     using bij_betw_primepows unfolding case_prod_unfold
     by (intro infsetsum_reindex_bij_betw [symmetric])
  also have "\<dots> = (\<Sum>\<^sub>a(p,k)\<in>(?P \<times> UNIV).
                     -((fds_nth f p / nat_power p s) ^ Suc k) * of_real (ln (real p)))"
    by (intro infsetsum_cong)
       (auto simp: f.mult f.power mangoldt_def aprimedivisor_prime_power ln_realpow prime_gt_0_nat
          nat_power_power_left divide_simps simp del: power_Suc)
  also have "\<dots> = (\<Sum>\<^sub>ap | prime p. \<Sum>\<^sub>ak.
                    - ((fds_nth f p / nat_power p s) ^ Suc k) * of_real (ln (real p)))"
    using sum2 by (subst infsetsum_Times) (auto simp: case_prod_unfold)
  also have "\<dots> = (\<Sum>\<^sub>ap | prime p. -(of_real (ln (real p)) *
                    (1 / (1 - fds_nth f p / nat_power p s) - 1)))"
    using eq by (intro infsetsum_cong) auto
  finally show ?th2 by (subst (asm) infsetsum_uminus)
qed

lemma eval_fds_logderiv_zeta:
  assumes "Re s > 1"
  shows  "(\<lambda>p. of_real (ln (real p)) / (p powr s - 1))
            abs_summable_on {p. prime p}" (is ?th1)
    and  "deriv zeta s / zeta s =
            -(\<Sum>\<^sub>ap | prime p. of_real (ln (real p)) / (p powr s - 1))" (is ?th2)
proof -
  have *: "completely_multiplicative_function (fds_nth fds_zeta :: _ \<Rightarrow> complex)"
    by standard auto
  note abscissa = le_less_trans[OF abs_conv_abscissa_completely_multiplicative_log_deriv[OF *]]
  have "(\<lambda>p. ln (real p) * (1 / (1 - fds_nth fds_zeta p / p powr s) - 1))
           abs_summable_on {p. prime p}"
    using eval_fds_logderiv_completely_multiplicative[OF *, of s] assms by auto
  also have "?this \<longleftrightarrow> (\<lambda>p. ln (real p) / (p powr s - 1)) abs_summable_on {p. prime p}" using assms
    by (intro abs_summable_on_cong) (auto simp: fds_nth_zeta divide_simps dest: prime_gt_1_nat)
  finally show ?th1 .

  from assms have ev: "eventually (\<lambda>z. z \<in> {z. Re z > 1}) (nhds s)"
    by (intro eventually_nhds_in_open open_halfspace_Re_gt) auto
  have "deriv zeta s = deriv (eval_fds fds_zeta) s"
    by (intro deriv_cong_ev[OF eventually_mono[OF ev]]) (auto simp: eval_fds_zeta)
  also have "deriv (eval_fds fds_zeta) s / zeta s = eval_fds (fds_deriv fds_zeta / fds_zeta) s"
    using assms zeta_Re_gt_1_nonzero[of s]
    by (subst eval_fds_log_deriv) (auto simp: eval_fds_zeta eval_fds_deriv intro!: abscissa)
  also have "eval_fds (fds_deriv fds_zeta / fds_zeta) s =
               -(\<Sum>\<^sub>ap | prime p. ln (real p) * (1 / (1 - fds_nth fds_zeta p / p powr s) - 1))"
    (is "_ = -?S") using eval_fds_logderiv_completely_multiplicative[OF *, of s] assms by auto
  also have "?S = (\<Sum>\<^sub>ap | prime p. ln (real p) / (p powr s - 1))" using assms
    by (intro infsetsum_cong) (auto simp: fds_nth_zeta divide_simps dest: prime_gt_1_nat)
  finally show ?th2 .
qed

lemma sums_logderiv_zeta:
  assumes "Re s > 1"
  shows   "(\<lambda>p. if prime p then of_real (ln (real p)) / (of_nat p powr s - 1) else 0) sums
             -(deriv zeta s / zeta s)" (is "?f sums _")
proof -
  note * = eval_fds_logderiv_zeta[OF assms]
  from sums_infsetsum_nat[OF *(1)] and *(2) show ?thesis by simp
qed

lemma abs_conv_abscissa_diff_le:
  "abs_conv_abscissa (f - g :: 'a :: dirichlet_series fds) \<le>
     max (abs_conv_abscissa f) (abs_conv_abscissa g)"
  using abs_conv_abscissa_add_le[of f "-g"] by auto

lemma abs_conv_abscissa_diff_leI:
  "abs_conv_abscissa (f :: 'a :: dirichlet_series fds) \<le> d \<Longrightarrow> abs_conv_abscissa g \<le> d \<Longrightarrow>
     abs_conv_abscissa (f - g) \<le> d"
  using abs_conv_abscissa_diff_le[of f g] by (auto simp: le_max_iff_disj)

lemma range_add_nat: "range (\<lambda>n. n + c) = {(c::nat)..}"
proof safe
  fix x assume "x \<ge> c"
  hence "x = x - c + c" by simp
  thus "x \<in> range (\<lambda>n. n + c)" by blast
qed auto

lemma abs_summable_hurwitz_zeta:
  assumes "Re s > 1" "a + real b > 0"
  shows   "(\<lambda>n. 1 / (of_nat n + a) powr s) abs_summable_on {b..}"
proof -
  from assms have "summable (\<lambda>n. cmod (1 / (of_nat (n + b) + a) powr s))"
    using summable_hurwitz_zeta_real[of "Re s" "a + b"]
    by (auto simp: norm_divide powr_minus field_simps norm_powr_real_powr)
  hence "(\<lambda>n. 1 / (of_nat (n + b) + a) powr s) abs_summable_on UNIV"
    by (auto simp: abs_summable_on_nat_iff' add_ac)
  also have "?this \<longleftrightarrow> (\<lambda>n. 1 / (of_nat n + a) powr s) abs_summable_on range (\<lambda>n. n + b)"
    by (rule abs_summable_on_reindex_iff) auto
  also have "range (\<lambda>n. n + b) = {b..}" by (rule range_add_nat)
  finally show ?thesis .
qed

lemma hurwitz_zeta_nat_conv_infsetsum:
  assumes "a > 0" and "Re s > 1"
  shows   "hurwitz_zeta (real a) s = (\<Sum>\<^sub>an. of_nat (n + a) powr -s)"
          "hurwitz_zeta (real a) s = (\<Sum>\<^sub>an\<in>{a..}. of_nat n powr -s)"
proof -
  have "hurwitz_zeta (real a) s = (\<Sum>n. of_nat (n + a) powr -s)"
    using assms by (subst hurwitz_zeta_conv_suminf) auto
  also have "\<dots> = (\<Sum>\<^sub>an. of_nat (n + a) powr -s)"
    using abs_summable_hurwitz_zeta[of s a 0] assms
    by (intro infsetsum_nat' [symmetric]) (auto simp: powr_minus field_simps)
  finally show "hurwitz_zeta (real a) s = (\<Sum>\<^sub>an. of_nat (n + a) powr -s)" .
  also have "\<dots> = (\<Sum>\<^sub>an\<in>range (\<lambda>n. n + a). of_nat n powr -s)"
    by (rule infsetsum_reindex [symmetric]) auto
  also have "range (\<lambda>n. n + a) = {a..}" by (rule range_add_nat)
  finally show "hurwitz_zeta (real a) s = (\<Sum>\<^sub>an\<in>{a..}. of_nat n powr -s)" .
qed

lemma continuous_on_pre_zeta [continuous_intros]:
  assumes "continuous_on A f" "a > 0"
  shows   "continuous_on A (\<lambda>x. pre_zeta a (f x))"
proof -
  from assms have "continuous_on UNIV (pre_zeta a)"
    by (intro holomorphic_on_imp_continuous_on[OF holomorphic_pre_zeta]) auto
  from continuous_on_compose2[OF this assms(1)] show ?thesis by simp
qed

lemma continuous_pre_zeta [continuous_intros]:
  assumes "continuous (at x within A) f" "a > 0"
  shows   "continuous (at x within A) (\<lambda>x. pre_zeta a (f x))"
proof -
  have "continuous (at z) (pre_zeta a)" for z
    by (rule continuous_on_interior[of UNIV]) (insert assms, auto intro!: continuous_intros)
  from continuous_within_compose3[OF this assms(1)] show ?thesis .
qed


lemma pre_zeta_bound:
  assumes "0 < Re s" and a: "a > 0"
  shows   "norm (pre_zeta a s) \<le> (1 + norm s / Re s) / 2 * a powr -Re s"
proof -
  let ?f = "\<lambda>x. - (s * (x + a) powr (-1-s))"
  let ?g' = "\<lambda>x. norm s * (x + a) powr (-1-Re s)"
  let ?g = "\<lambda>x. -norm s / Re s * (x + a) powr (-Re s)"
  define R where "R = EM_remainder 1 ?f 0"
  have [simp]: "-Re s - 1 = -1 - Re s" by (simp add: algebra_simps)

  have "\<bar>frac x - 1 / 2\<bar> \<le> 1 / 2" for x :: real unfolding frac_def
    by linarith
  hence "\<bar>pbernpoly (Suc 0) x\<bar> \<le> 1 / 2" for x
    by (simp add: pbernpoly_def bernpoly_def)
  moreover have "((\<lambda>b. cmod s * (b + a) powr - Re s / Re s) \<longlongrightarrow> 0) at_top"
    using \<open>Re s > 0\<close> \<open>a > 0\<close> by real_asymp
  ultimately have *: "\<forall>x. x \<ge> real 0 \<longrightarrow> norm (EM_remainder 1 ?f (int x)) \<le>
                           (1 / 2) / fact 1 * (-?g (real x))"
    using \<open>a > 0\<close> \<open>Re s > 0\<close>
    by (intro norm_EM_remainder_le_strong_nat'[where g' = ?g' and Y = "{}"])
       (auto intro!: continuous_intros derivative_eq_intros
             simp: field_simps norm_mult norm_powr_real_powr add_eq_0_iff)
  have R: "norm R \<le> norm s / (2 * Re s) * a powr -Re s"
    unfolding R_def using spec[OF *, of 0] by simp

  from assms have "pre_zeta a s = a powr -s / 2 + R"
    by (simp add: pre_zeta_def pre_zeta_aux_def R_def)
  also have "norm \<dots> \<le> a powr -Re s / 2 + norm s / (2 * Re s) * a powr -Re s" using a
    by (intro order.trans[OF norm_triangle_ineq] add_mono R) (auto simp: norm_powr_real_powr)
  also have "\<dots> = (1 + norm s / Re s) / 2 * a powr -Re s"
    by (simp add: field_simps)
  finally show ?thesis .
qed

lemma pre_zeta_bound':
  assumes "0 < Re s" and a: "a > 0"
  shows   "norm (pre_zeta a s) \<le> norm s / (Re s * a powr Re s)"
proof -
  from assms have "norm (pre_zeta a s) \<le> (1 + norm s / Re s) / 2 * a powr -Re s"
    by (intro pre_zeta_bound) auto
  also have "\<dots> = (Re s + norm s) / 2 / (Re s * a powr Re s)"
    using assms by (auto simp: field_simps powr_minus)
  also have "Re s + norm s \<le> norm s + norm s" by (intro add_right_mono complex_Re_le_cmod)
  also have "(norm s + norm s) / 2 = norm s" by simp
  finally show "norm (pre_zeta a s) \<le> norm s / (Re s * a powr Re s)"
    using assms by (simp add: divide_right_mono)
qed

lemma summable_comparison_test_bigo:
  fixes f :: "nat \<Rightarrow> real"
  assumes "summable (\<lambda>n. norm (g n))" "f \<in> O(g)"
  shows   "summable f"
proof -
  from \<open>f \<in> O(g)\<close> obtain C where C: "eventually (\<lambda>x. norm (f x) \<le> C * norm (g x)) at_top"
    by (auto elim: landau_o.bigE)
  thus ?thesis
    by (rule summable_comparison_test_ev) (insert assms, auto intro: summable_mult)
qed

lemma deriv_zeta_eq:
  assumes s: "s \<noteq> 1"
  shows   "deriv zeta s = deriv (pre_zeta 1) s - 1 / (s - 1)\<^sup>2"
proof -
  from s have ev: "eventually (\<lambda>z. z \<noteq> 1) (nhds s)" by (intro t1_space_nhds)
  have [derivative_intros]: "(pre_zeta 1 has_field_derivative deriv (pre_zeta 1) s) (at s)"
    by (intro holomorphic_derivI[of _ UNIV] holomorphic_intros) auto
  have "((\<lambda>s. pre_zeta 1 s + 1 / (s - 1)) has_field_derivative
          (deriv (pre_zeta 1) s - 1 / (s - 1)\<^sup>2)) (at s)"
    using s by (auto intro!: derivative_eq_intros simp: power2_eq_square)
  also have "?this \<longleftrightarrow> (zeta has_field_derivative (deriv (pre_zeta 1) s - 1 / (s - 1)\<^sup>2)) (at s)"
    by (intro has_field_derivative_cong_ev eventually_mono[OF ev])
       (auto simp: zeta_def hurwitz_zeta_def)
  finally show ?thesis by (rule DERIV_imp_deriv)
qed

lemma zeta_remove_zero:
  assumes "Re s \<ge> 1"
  shows   "(s - 1) * pre_zeta 1 s + 1 \<noteq> 0"
proof (cases "s = 1")
  case False
  hence "(s - 1) * pre_zeta 1 s + 1 = (s - 1) * zeta s"
    by (simp add: zeta_def hurwitz_zeta_def divide_simps)
  also from False assms have "\<dots> \<noteq> 0" using zeta_Re_ge_1_nonzero[of s] by auto
  finally show ?thesis .
qed auto

lemma eval_fds_deriv_zeta:
  assumes "Re s > 1"
  shows   "eval_fds (fds_deriv fds_zeta) s = deriv zeta s"
proof -
  have ev: "eventually (\<lambda>z. z \<in> {z. Re z > 1}) (nhds s)"
    using assms by (intro eventually_nhds_in_open open_halfspace_Re_gt) auto
  from assms have "eval_fds (fds_deriv fds_zeta) s = deriv (eval_fds fds_zeta) s"
    by (subst eval_fds_deriv) auto
  also have "\<dots> = deriv zeta s"
    by (intro deriv_cong_ev eventually_mono[OF ev]) (auto simp: eval_fds_zeta)
  finally show ?thesis .
qed

lemma length_sorted_list_of_set [simp]:
  "finite A \<Longrightarrow> length (sorted_list_of_set A) = card A"
  by (metis length_remdups_card_conv length_sort set_sorted_list_of_set
            sorted_list_of_set_sort_remdups)

lemma le_nat_iff': "x \<le> nat y \<longleftrightarrow> x = 0 \<and> y \<le> 0 \<or> int x \<le> y"
  by auto

lemma sum_upto_plus1:
  assumes "x \<ge> 0"
  shows   "sum_upto f (x + 1) = sum_upto f x + f (Suc (nat \<lfloor>x\<rfloor>))"
proof -
  have "sum_upto f (x + 1) = sum f {0<..Suc (nat \<lfloor>x\<rfloor>)}"
    using assms by (simp add: sum_upto_altdef nat_add_distrib)
  also have "{0<..Suc (nat \<lfloor>x\<rfloor>)} = insert (Suc (nat \<lfloor>x\<rfloor>)) {0<..nat \<lfloor>x\<rfloor>}"
    by auto
  also have "sum f \<dots> = sum_upto f x + f (Suc (nat \<lfloor>x\<rfloor>))"
    by (subst sum.insert) (auto simp: sum_upto_altdef add_ac)
  finally show ?thesis .
qed

lemma sum_upto_minus1:
  assumes "x \<ge> 1"
  shows   "sum_upto f (x - 1) = (sum_upto f x - f (nat \<lfloor>x\<rfloor>) :: 'a :: ab_group_add)"
  using sum_upto_plus1[of "x - 1" f] assms by (simp add: algebra_simps nat_diff_distrib)

lemma integral_smallo:
  fixes f g g' :: "real \<Rightarrow> real"
  assumes "f \<in> o(g')" and "filterlim g at_top at_top"
  assumes "\<And>a' x. a \<le> a' \<Longrightarrow> a' \<le> x \<Longrightarrow> f integrable_on {a'..x}"
  assumes deriv: "\<And>x. x \<ge> a \<Longrightarrow> (g has_field_derivative g' x) (at x)"
  assumes cont: "continuous_on {a..} g'"
  assumes nonneg: "\<And>x. x \<ge> a \<Longrightarrow> g' x \<ge> 0"
  shows   "(\<lambda>x. integral {a..x} f) \<in> o(g)"
proof (rule landau_o.smallI)
  fix c :: real assume c: "c > 0"
  note [continuous_intros] = continuous_on_subset[OF cont]
  define c' where "c' = c / 2"
  from c have c': "c' > 0" by (simp add: c'_def)
  from landau_o.smallD[OF assms(1) this]
    obtain b where b: "\<And>x. x \<ge> b \<Longrightarrow> norm (f x) \<le> c' * norm (g' x)"
    unfolding eventually_at_top_linorder by blast
  define b' where "b' = max a b"
  define D where "D = norm (integral {a..b'} f)"

  have "filterlim (\<lambda>x. c' * g x) at_top at_top"
    using c' by (intro filterlim_tendsto_pos_mult_at_top[OF tendsto_const] assms)
  hence "eventually (\<lambda>x. c' * g x \<ge> D - c' * g b') at_top"
    by (auto simp: filterlim_at_top)
  thus "eventually (\<lambda>x. norm (integral {a..x} f) \<le> c * norm (g x)) at_top"
    using eventually_ge_at_top[of b']
  proof eventually_elim
    case (elim x)
    have b': "a \<le> b'" "b \<le> b'" by (auto simp: b'_def)
    from elim b' have integrable: "(\<lambda>x. \<bar>g' x\<bar>) integrable_on {b'..x}"
      by (intro integrable_continuous_real continuous_intros) auto
    have "integral {a..x} f = integral {a..b'} f + integral {b'..x} f"
      using elim b' by (intro Henstock_Kurzweil_Integration.integral_combine [symmetric] assms) auto
    also have "norm \<dots> \<le> D + norm (integral {b'..x} f)"
      unfolding D_def by (rule norm_triangle_ineq)
    also have "norm (integral {b'..x} f) \<le> integral {b'..x} (\<lambda>x. c' * norm (g' x))"
      using b' elim assms c' integrable by (intro integral_norm_bound_integral b assms) auto
    also have "\<dots> = c' * integral {b'..x} (\<lambda>x. \<bar>g' x\<bar>)" by simp
    also have "integral {b'..x} (\<lambda>x. \<bar>g' x\<bar>) = integral {b'..x} g'"
      using assms b' by (intro integral_cong) auto
    also have "(g' has_integral (g x - g b')) {b'..x}" using b' elim
      by (intro fundamental_theorem_of_calculus)
         (auto simp flip: has_field_derivative_iff_has_vector_derivative
               intro!: has_field_derivative_at_within[OF deriv])
    hence "integral {b'..x} g' = g x - g b'"
      by (simp add: has_integral_iff)
    also have "D + c' * (g x - g b') \<le> c * g x"
      using elim by (simp add: field_simps c'_def)
    also have "\<dots> \<le> c * norm (g x)"
      using c by (intro mult_left_mono) auto
    finally show ?case by simp
  qed
qed

lemma integral_bigo:
  fixes f g g' :: "real \<Rightarrow> real"
  assumes "f \<in> O(g')" and "filterlim g at_top at_top"
  assumes "\<And>a' x. a \<le> a' \<Longrightarrow> a' \<le> x \<Longrightarrow> f integrable_on {a'..x}"
  assumes deriv: "\<And>x. x \<ge> a \<Longrightarrow> (g has_field_derivative g' x) (at x within {a..})"
  assumes cont: "continuous_on {a..} g'"
  assumes nonneg: "\<And>x. x \<ge> a \<Longrightarrow> g' x \<ge> 0"
  shows   "(\<lambda>x. integral {a..x} f) \<in> O(g)"
proof -
  note [continuous_intros] = continuous_on_subset[OF cont]
  from landau_o.bigE[OF assms(1)]
    obtain c b where c: "c > 0" and b: "\<And>x. x \<ge> b \<Longrightarrow> norm (f x) \<le> c * norm (g' x)"
      unfolding eventually_at_top_linorder by metis
  define c' where "c' = c / 2"
  define b' where "b' = max a b"
  define D where "D = norm (integral {a..b'} f)"

  have "filterlim (\<lambda>x. c * g x) at_top at_top"
    using c by (intro filterlim_tendsto_pos_mult_at_top[OF tendsto_const] assms)
  hence "eventually (\<lambda>x. c * g x \<ge> D - c * g b') at_top"
    by (auto simp: filterlim_at_top)
  hence "eventually (\<lambda>x. norm (integral {a..x} f) \<le> 2 * c * norm (g x)) at_top"
    using eventually_ge_at_top[of b']
  proof eventually_elim
    case (elim x)
    have b': "a \<le> b'" "b \<le> b'" by (auto simp: b'_def)
    from elim b' have integrable: "(\<lambda>x. \<bar>g' x\<bar>) integrable_on {b'..x}"
      by (intro integrable_continuous_real continuous_intros) auto
    have "integral {a..x} f = integral {a..b'} f + integral {b'..x} f"
      using elim b' by (intro Henstock_Kurzweil_Integration.integral_combine [symmetric] assms) auto
    also have "norm \<dots> \<le> D + norm (integral {b'..x} f)"
      unfolding D_def by (rule norm_triangle_ineq)
    also have "norm (integral {b'..x} f) \<le> integral {b'..x} (\<lambda>x. c * norm (g' x))"
      using b' elim assms c integrable by (intro integral_norm_bound_integral b assms) auto
    also have "\<dots> = c * integral {b'..x} (\<lambda>x. \<bar>g' x\<bar>)" by simp
    also have "integral {b'..x} (\<lambda>x. \<bar>g' x\<bar>) = integral {b'..x} g'"
      using assms b' by (intro integral_cong) auto
    also have "(g' has_integral (g x - g b')) {b'..x}" using b' elim
      by (intro fundamental_theorem_of_calculus)
         (auto simp flip: has_field_derivative_iff_has_vector_derivative
               intro!: DERIV_subset[OF deriv])
    hence "integral {b'..x} g' = g x - g b'"
      by (simp add: has_integral_iff)
    also have "D + c * (g x - g b') \<le> 2 * c * g x"
      using elim by (simp add: field_simps c'_def)
    also have "\<dots> \<le> 2 * c * norm (g x)"
      using c by (intro mult_left_mono) auto
    finally show ?case by simp
  qed
  thus ?thesis by (rule bigoI)
qed

lemma primepows_le_subset:
  assumes x: "x > 0" and l: "l > 0"
  shows   "{(p, i). prime p \<and> l \<le> i \<and> real (p ^ i) \<le> x} \<subseteq> {..nat \<lfloor>root l x\<rfloor>} \<times> {..nat \<lfloor>log 2 x\<rfloor>}"
proof safe
  fix p i :: nat assume pi: "prime p" "i \<ge> l" "real (p ^ i) \<le> x"
  have "real p ^ l \<le> real p ^ i" using pi x l
    by (intro power_increasing) (auto dest: prime_gt_0_nat)
  also have "\<dots> \<le> x" using pi by simp
  finally have "root l (real p ^ l) \<le> root l x"
    using x pi l by (subst real_root_le_iff) auto
  also have "root l (real p ^ l) = real p"
    using pi l by (subst real_root_pos2) auto
  finally show "p \<le> nat \<lfloor>root l x\<rfloor>" using pi l x by (simp add: le_nat_iff' le_floor_iff)

  from pi have "2 ^ i \<le> real p ^ i" using l
    by (intro power_mono) (auto dest: prime_gt_1_nat)
  also have "\<dots> \<le> x" using pi by simp
  finally show "i \<le> nat \<lfloor>log 2 x\<rfloor>" using pi x
    by (auto simp: le_nat_iff' le_floor_iff le_log_iff powr_realpow)
qed

lemma mangoldt_non_primepow: "\<not>primepow n \<Longrightarrow> mangoldt n = 0"
  by (auto simp: mangoldt_def)

lemma le_imp_bigo_real:
  assumes "c \<ge> 0" "eventually (\<lambda>x. f x \<le> c * (g x :: real)) F" "eventually (\<lambda>x. 0 \<le> f x) F"
  shows   "f \<in> O[F](g)"
proof -
  have "eventually (\<lambda>x. norm (f x) \<le> c * norm (g x)) F"
    using assms(2,3)
  proof eventually_elim
    case (elim x)
    have "norm (f x) \<le> c * g x" using elim by simp
    also have "\<dots> \<le> c * norm (g x)" by (intro mult_left_mono assms) auto
    finally show ?case .
  qed
  thus ?thesis by (intro bigoI[of _ c]) auto
qed

(* TODO: unneeded. But why does real_asymp not work? *)
lemma ln_minus_ln_floor_bigo: "(\<lambda>x. ln x - ln (real (nat \<lfloor>x\<rfloor>))) \<in> O(\<lambda>_. 1)"
proof (intro le_imp_bigo_real[of 1] eventually_mono[OF eventually_ge_at_top[of 1]])
  fix x :: real assume x: "x \<ge> 1"
  from x have *: "x - real (nat \<lfloor>x\<rfloor>) \<le> 1" by linarith
  from x have "ln x - ln (real (nat \<lfloor>x\<rfloor>)) \<le> (x - real (nat \<lfloor>x\<rfloor>)) / real (nat \<lfloor>x\<rfloor>)"
    by (intro ln_diff_le) auto
  also have "\<dots> \<le> 1 / 1" using x * by (intro frac_le) auto
  finally show "ln x - ln (real (nat \<lfloor>x\<rfloor>)) \<le> 1 * 1" by simp
qed auto

lemma cos_geD:
  assumes "cos x \<ge> cos a" "0 \<le> a" "a \<le> pi" "-pi \<le> x" "x \<le> pi"
  shows   "x \<in> {-a..a}"
proof (cases "x \<ge> 0")
  case True
  with assms show ?thesis
    by (subst (asm) cos_mono_le_eq) auto
next
  case False
  with assms show ?thesis using cos_mono_le_eq[of a "-x"]
    by auto
qed

(* TODO: Could be generalised *)
lemma path_image_part_circlepath_same_Re:
  assumes "0 \<le> b" "b \<le> pi" "a = -b" "r \<ge> 0"
  shows   "path_image (part_circlepath c r a b) = sphere c r \<inter> {s. Re s \<ge> Re c + r * cos a}"
proof safe
  fix z assume "z \<in> path_image (part_circlepath c r a b)"
  with assms obtain t where t: "t \<in> {a..b}" "z = c + of_real r * cis t"
    by (auto simp: path_image_part_circlepath exp_eq_polar)
  from t and assms show "z \<in> sphere c r"
    by (auto simp: dist_norm norm_mult)
  from t and assms show "Re z \<ge> Re c + r * cos a"
    using cos_monotone_0_pi_le[of t b] cos_monotone_minus_pi_0'[of a t]
    by (cases "t \<ge> 0") (auto intro!: mult_left_mono)
next
  fix z assume z: "z \<in> sphere c r" "Re z \<ge> Re c + r * cos a"
  show "z \<in> path_image (part_circlepath c r a b)"
  proof (cases "r = 0")
    case False
    with assms have r: "r > 0" by simp
    with z have z_eq: "z = c + r * cis (Arg (z - c))"
      using Arg_eq[of "z - c"] by (auto simp: dist_norm exp_eq_polar norm_minus_commute)
  moreover from z(2) r assms have "cos b \<le> cos (Arg (z - c))"
    by (subst (asm) z_eq) auto
  with assms have "Arg (z - c) \<in> {-b..b}"
    using Arg_le_pi[of "z - c"] mpi_less_Arg[of "z - c"] by (intro cos_geD) auto
  ultimately show "z \<in> path_image (part_circlepath c r a b)"
    using assms by (subst path_image_part_circlepath) (auto simp: exp_eq_polar)
  qed (insert assms z, auto simp: path_image_part_circlepath)
qed

lemma part_circlepath_rotate_left:
  "part_circlepath c r (x + a) (x + b) = (\<lambda>z. c + cis x * (z - c)) \<circ> part_circlepath c r a b"
  by (simp add: part_circlepath_def exp_eq_polar fun_eq_iff
                linepath_translate_left linepath_translate_right cis_mult add_ac)

lemma part_circlepath_rotate_right:
  "part_circlepath c r (a + x) (b + x) = (\<lambda>z. c + cis x * (z - c)) \<circ> part_circlepath c r a b"
  by (simp add: part_circlepath_def exp_eq_polar fun_eq_iff
                linepath_translate_left linepath_translate_right cis_mult add_ac)

lemma path_image_semicircle_Re_ge:
  assumes "r \<ge> 0"
  shows   "path_image (part_circlepath c r (-pi/2) (pi/2)) =
             sphere c r \<inter> {s. Re s \<ge> Re c}"
  by (subst path_image_part_circlepath_same_Re) (simp_all add: assms)

lemma sphere_rotate: "(\<lambda>z. c + cis x * (z - c)) ` sphere c r = sphere c r"
proof safe
  fix z assume z: "z \<in> sphere c r"
  hence "z = c + cis x * (c + cis (-x) * (z - c) - c)"
        "c + cis (-x) * (z - c) \<in> sphere c r"
    by (auto simp: dist_norm norm_mult norm_minus_commute
                   cis_conv_exp exp_minus field_simps norm_divide)
  with z show "z \<in> (\<lambda>z. c + cis x * (z - c)) ` sphere c r" by blast
qed (auto simp: dist_norm norm_minus_commute norm_mult)


lemma path_image_semicircle_Re_le:
  assumes "r \<ge> 0"
  shows   "path_image (part_circlepath c r (pi/2) (3/2*pi)) =
             sphere c r \<inter> {s. Re s \<le> Re c}"
proof -
  let ?f = "(\<lambda>z. c + cis pi * (z - c))"
  have *: "part_circlepath c r (pi/2) (3/2*pi) = part_circlepath c r (pi + (-pi/2)) (pi + pi/2)"
    by simp
  have "path_image (part_circlepath c r (pi/2) (3/2*pi)) =
          ?f ` sphere c r \<inter> ?f ` {s. Re c \<le> Re s}"
    unfolding * part_circlepath_rotate_left path_image_compose path_image_semicircle_Re_ge[OF assms]
    by auto
  also have "?f ` sphere c r = sphere c r"
    by (rule sphere_rotate)
  also have "?f ` {s. Re c \<le> Re s} = {s. Re c \<ge> Re s}"
    by (auto simp: image_iff intro!: exI[of _ "2 * c - x" for x])
  finally show ?thesis .
qed

lemma path_image_semicircle_Im_ge:
  assumes "r \<ge> 0"
  shows   "path_image (part_circlepath c r 0 pi) =
             sphere c r \<inter> {s. Im s \<ge> Im c}"
proof -
  let ?f = "(\<lambda>z. c + cis (pi/2) * (z - c))"
  have *: "part_circlepath c r 0 pi = part_circlepath c r (pi / 2 + (-pi/2)) (pi / 2 + pi/2)"
    by simp
  have "path_image (part_circlepath c r 0 pi) =
          ?f ` sphere c r \<inter> ?f ` {s. Re c \<le> Re s}"
    unfolding * part_circlepath_rotate_left path_image_compose path_image_semicircle_Re_ge[OF assms]
    by auto
  also have "?f ` sphere c r = sphere c r"
    by (rule sphere_rotate)
  also have "?f ` {s. Re c \<le> Re s} = {s. Im c \<le> Im s}"
    by (auto simp: image_iff intro!: exI[of _ "c - \<i> * (x - c)" for x])
  finally show ?thesis .
qed

lemma path_image_semicircle_Im_le:
  assumes "r \<ge> 0"
  shows   "path_image (part_circlepath c r pi (2 * pi)) =
             sphere c r \<inter> {s. Im s \<le> Im c}"
proof -
  let ?f = "(\<lambda>z. c + cis (3*pi/2) * (z - c))"
  have *: "part_circlepath c r pi (2*pi) = part_circlepath c r (3*pi/2 + (-pi/2)) (3*pi/2 + pi/2)"
    by simp
  have "path_image (part_circlepath c r pi (2 * pi)) =
          ?f ` sphere c r \<inter> ?f ` {s. Re c \<le> Re s}"
    unfolding * part_circlepath_rotate_left path_image_compose path_image_semicircle_Re_ge[OF assms]
    by auto
  also have "?f ` sphere c r = sphere c r"
    by (rule sphere_rotate)
  also have "cis (3 * pi / 2) = -\<i>"
    using cis_mult[of pi "pi / 2"] by simp
  hence "?f ` {s. Re c \<le> Re s} = {s. Im c \<ge> Im s}"
    by (auto simp: image_iff intro!: exI[of _ "c + \<i> * (x - c)" for x])
  finally show ?thesis .
qed

lemma powr_numeral [simp]: "x \<ge> 0 \<Longrightarrow> (x::real) powr numeral y = x ^ numeral y"
  using powr_numeral[of x y] by (cases "x = 0") auto

lemma eval_fds_logderiv_zeta_real:
  assumes "x > (1 :: real)"
  shows  "(\<lambda>p. ln (real p) / (p powr x - 1)) abs_summable_on {p. prime p}" (is ?th1)
    and  "deriv zeta (of_real x) / zeta (of_real x) =
            -of_real (\<Sum>\<^sub>ap | prime p. ln (real p) / (p powr x - 1))" (is ?th2)
proof -
  have "(\<lambda>p. Re (of_real (ln (real p)) / (of_nat p powr of_real x - 1)))
          abs_summable_on {p. prime p}" using assms
    by (intro abs_summable_Re eval_fds_logderiv_zeta) auto
  also have "?this \<longleftrightarrow> ?th1"
    by (intro abs_summable_on_cong) (auto simp: powr_Reals_eq)
  finally show ?th1 .
  show ?th2 using assms
    by (subst eval_fds_logderiv_zeta) (auto simp: infsetsum_of_real [symmetric] powr_Reals_eq)
qed

lemma
  fixes a b c d :: real
  assumes ab: "d * a + b \<ge> 1" and c: "c < -1" and d: "d > 0"
  defines "C \<equiv> - ((ln (d * a + b) - 1 / (c + 1)) * (d * a + b) powr (c + 1) / (d * (c + 1)))"
  shows set_integrable_ln_powr_at_top:
          "(\<lambda>x. (ln (d * x + b) * ((d * x + b) powr c))) absolutely_integrable_on {a<..}" (is ?th1)
  and   set_lebesgue_integral_ln_powr_at_top:
          "(\<integral>x\<in>{a<..}. (ln (d * x + b) * ((d * x + b) powr c)) \<partial>lborel) = C" (is ?th2)
  and   ln_powr_has_integral_at_top:
          "((\<lambda>x. ln (d * x + b) * (d * x + b) powr c) has_integral C) {a<..}" (is ?th3)
proof -
  define f where "f = (\<lambda>x. ln (d * x + b) * (d * x + b) powr c)"
  define F where "F = (\<lambda>x. (ln (d * x + b) - 1 / (c + 1)) * (d * x + b) powr (c + 1) / (d * (c + 1)))"

  have *: "(F has_field_derivative f x) (at x)" "isCont f x" "f x \<ge> 0" if "x > a" for x
  proof -
    have "1 \<le> d * a + b" by fact
    also have "\<dots> < d * x + b" using that assms
      by (intro add_strict_right_mono mult_strict_left_mono)
    finally have gt_1: "d * x + b > 1" .
    show "(F has_field_derivative f x) (at x)" "isCont f x" using ab c d gt_1
    by (auto simp: F_def f_def divide_simps intro!: derivative_eq_intros continuous_intros)
       (auto simp: algebra_simps powr_add)?
    show "f x \<ge> 0" using gt_1 by (auto simp: f_def)
  qed

  have limits: "((F \<circ> real_of_ereal) \<longlongrightarrow> F a) (at_right (ereal a))"
               "((F \<circ> real_of_ereal) \<longlongrightarrow> 0) (at_left \<infinity>)"
    using c ab d unfolding ereal_tendsto_simps1 F_def  by (real_asymp; simp add: field_simps)+
  have 1: "set_integrable lborel (einterval a \<infinity>) f" using ab c limits
    by (intro interval_integral_FTC_nonneg) (auto intro!: * AE_I2)
  thus 2: "f absolutely_integrable_on {a<..}"
    by (auto simp: set_integrable_def integrable_completion)
  have "(LBINT x=ereal a..\<infinity>. f x) = 0 - F a" using ab c limits
    by (intro interval_integral_FTC_nonneg) (auto intro!: *)
  thus 3: ?th2
    by (simp add: interval_integral_to_infinity_eq F_def f_def C_def)
  show ?th3
    using set_borel_integral_eq_integral[OF 1] 3 by (simp add: has_integral_iff f_def C_def)
qed

lemma ln_fact_conv_sum_upto: "ln (fact n) = sum_upto ln n"
  by (induction n) (auto simp: sum_upto_plus1 add.commute[of 1] ln_mult)

lemma sum_upto_ln_conv_ln_fact: "sum_upto ln x = ln (fact (nat \<lfloor>x\<rfloor>))"
  by (simp add: ln_fact_conv_sum_upto sum_upto_altdef)

lemma real_of_nat_div: "real (a div b) = real_of_int \<lfloor>real a / real b\<rfloor>"
  by (subst floor_divide_of_nat_eq) auto

lemma integral_subset_negligible:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  assumes "S \<subseteq> T" "negligible (T - S)"
  shows   "integral S f = integral T f"
proof -
  have "integral T f = integral T (\<lambda>x. if x \<in> S then f x else 0)"
    by (rule integral_spike[of "T - S"]) (use assms in auto)
  also have "\<dots> = integral (S \<inter> T) f"
    by (subst integral_restrict_Int) auto
  also have "S \<inter> T = S" using assms by auto
  finally show ?thesis ..
qed

lemma integrable_on_cong [cong]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x = g x" "A = B"
  shows   "f integrable_on A \<longleftrightarrow> g integrable_on B"
  using has_integral_cong[of A f g, OF assms(1)] assms(2)
  by (auto simp: integrable_on_def)

lemma measurable_sum_upto [measurable]:
  fixes f :: "'a \<Rightarrow> nat \<Rightarrow> real"
  assumes [measurable]: "\<And>y. (\<lambda>t. f t y) \<in> M \<rightarrow>\<^sub>M borel"
  assumes [measurable]: "x \<in> M \<rightarrow>\<^sub>M borel"
  shows "(\<lambda>t. sum_upto (f t) (x t)) \<in> M \<rightarrow>\<^sub>M borel"
proof -
  have meas: "(\<lambda>t. set_lebesgue_integral lborel {y. y \<ge> 0 \<and> y - real (nat \<lfloor>x t\<rfloor>) \<le> 0} (\<lambda>y. f t (nat \<lceil>y\<rceil>)))
          \<in> M \<rightarrow>\<^sub>M borel" (is "?f \<in> _") unfolding set_lebesgue_integral_def
    by measurable
  also have "?f = (\<lambda>t. sum_upto (f t) (x t))"
  proof
    fix t :: 'a
    show "?f t = sum_upto (f t) (x t)"
    proof (cases "x t < 1")
      case True
      hence "{y. y \<ge> 0 \<and> y - real (nat \<lfloor>x t\<rfloor>) \<le> 0} = {0}" by auto
      thus ?thesis using True
        by (simp add: set_integral_at_point sum_upto_altdef)
    next
      case False
      define n where "n = nat \<lfloor>x t\<rfloor>"
      from False have "n > 0" by (auto simp: n_def)

      have *: "((\<lambda>x. f t (nat \<lceil>x\<rceil>)) has_integral sum (f t) {0<..n}) {real 0..real n}"
        using \<open>n > 0\<close> by (intro nat_sum_has_integral_ceiling) auto

      have **: "(\<lambda>x. f t (nat \<lceil>x\<rceil>)) absolutely_integrable_on {real 0..real n}"
      proof (rule absolutely_integrable_absolutely_integrable_ubound)
        show "(\<lambda>_. MAX n\<in>{0..n}. \<bar>f t n\<bar>) absolutely_integrable_on {real 0..real n}"
          using \<open>n > 0\<close> by (subst absolutely_integrable_on_iff_nonneg)
                           (auto simp: Max_ge_iff intro!: exI[of _ "f t 0"])
        show "(\<lambda>x. f t (nat \<lceil>x\<rceil>)) integrable_on {real 0..real n}"
          using * by (simp add: has_integral_iff)
      next
        fix y :: real assume y: "y \<in> {real 0..real n}"
        have "f t (nat \<lceil>y\<rceil>) \<le> \<bar>f t (nat \<lceil>y\<rceil>)\<bar>"
          by simp
        also have "\<dots> \<le> (MAX n\<in>{0..n}. \<bar>f t n\<bar>)"
          using y by (intro Max.coboundedI) auto
        finally show "f t (nat \<lceil>y\<rceil>) \<le> (MAX n\<in>{0..n}. \<bar>f t n\<bar>)" .
      qed
      have "sum (f t) {0<..n} = (\<integral>x\<in>{real 0..real n}. f t (nat \<lceil>x\<rceil>) \<partial>lebesgue)"
        using has_integral_set_lebesgue[OF **] * by (simp add: has_integral_iff)
      also have "\<dots> = (\<integral>x\<in>{real 0..real n}. f t (nat \<lceil>x\<rceil>) \<partial>lborel)"
        unfolding set_lebesgue_integral_def by (subst integral_completion) auto
      also have "{real 0..real n} = {y. 0 \<le> y \<and> y - real (nat \<lfloor>x t\<rfloor>) \<le> 0}"
        by (auto simp: n_def)
      also have "sum (f t) {0<..n} = sum_upto (f t) (x t)"
        by (simp add: sum_upto_altdef n_def)
      finally show ?thesis ..
    qed
  qed
  finally show ?thesis .
qed

end
