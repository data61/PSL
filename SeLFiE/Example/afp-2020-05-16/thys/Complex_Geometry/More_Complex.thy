(* -------------------------------------------------------------------------- *)
subsection \<open>Library Additions for Complex Numbers\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Some additional lemmas about complex numbers.\<close>

theory More_Complex
  imports Complex_Main More_Transcendental Canonical_Angle
begin

text \<open>Conjugation and @{term cis}\<close>

declare cis_cnj[simp] 

lemma rcis_cnj: 
  shows "cnj a = rcis (cmod a) (- arg a)"
  by (subst rcis_cmod_arg[of a, symmetric]) (simp add: rcis_def)

lemmas complex_cnj = complex_cnj_diff complex_cnj_mult complex_cnj_add complex_cnj_divide complex_cnj_minus

text \<open>Some properties for @{term complex_of_real}. Also, since it is often used in our
formalization we abbreviate it to @{term cor}.\<close>

abbreviation cor :: "real \<Rightarrow> complex" where
  "cor \<equiv> complex_of_real"

lemma cor_neg_one [simp]:
  shows "cor (-1) = -1"
  by simp

lemma neg_cor_neg_one [simp]:
  shows "- cor (-1) = 1"
  by simp

lemma cmod_cis [simp]:
  assumes "a \<noteq> 0"
  shows "cor (cmod a) * cis (arg a) = a"
  using assms
  by (metis rcis_cmod_arg rcis_def)

lemma cis_cmod [simp]:
  assumes "a \<noteq> 0"
  shows "cis (arg a) * cor (cmod a) = a"
  using assms cmod_cis[of a]
  by (simp add: field_simps)

lemma cor_add:
  shows "cor (a + b) = cor a + cor b"
  by (rule of_real_add)

lemma cor_mult:
  shows "cor (a * b) = cor a * cor b"
  by (rule of_real_mult)

lemma cor_squared:
  shows "(cor x)\<^sup>2 = cor (x\<^sup>2)"
  by (simp add: power2_eq_square)

lemma cor_sqrt_mult_cor_sqrt [simp]:
  shows "cor (sqrt A) * cor (sqrt A) = cor \<bar>A\<bar>"
  by (metis cor_mult real_sqrt_abs2 real_sqrt_mult)

lemma cor_eq_0: "cor x + \<i> * cor y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
 by (metis Complex_eq Im_complex_of_real Im_i_times Re_complex_of_real add_cancel_left_left of_real_eq_0_iff plus_complex.sel(2) zero_complex.code)

lemma one_plus_square_neq_zero [simp]:
  shows "1 + (cor x)\<^sup>2 \<noteq> 0"
  by (metis (hide_lams, no_types) of_real_1 of_real_add of_real_eq_0_iff of_real_power power_one sum_power2_eq_zero_iff zero_neq_one)

text \<open>Additional lemmas about @{term Complex} constructor. Following newer versions of Isabelle,
these should be deprecated.\<close>

lemma complex_real_two [simp]:
  shows "Complex 2 0 = 2"
  by (simp add: Complex_eq)

lemma complex_double [simp]:
  shows "(Complex a b) * 2 = Complex (2*a) (2*b)"
  by (simp add: Complex_eq)

lemma complex_half [simp]: 
  shows "(Complex a b) / 2 = Complex (a/2) (b/2)"
  by (subst complex_eq_iff) auto

lemma Complex_scale1:
  shows "Complex (a * b) (a * c) = cor a * Complex b c"
  unfolding complex_of_real_def
  unfolding Complex_eq
  by (auto simp add: field_simps)

lemma Complex_scale2: 
  shows "Complex (a * c) (b * c) = Complex a b * cor c"
  unfolding complex_of_real_def
  unfolding Complex_eq
  by (auto simp add: field_simps)

lemma Complex_scale3: 
  shows "Complex (a / b) (a / c) = cor a * Complex (1 / b) (1 / c)"
  unfolding complex_of_real_def
  unfolding Complex_eq
  by (auto simp add: field_simps)

lemma Complex_scale4:
  shows "c \<noteq> 0 \<Longrightarrow> Complex (a / c) (b / c) = Complex a b / cor c"
  unfolding complex_of_real_def
  unfolding Complex_eq
  by (auto simp add: field_simps power2_eq_square)

lemma Complex_Re_express_cnj:
  shows "Complex (Re z) 0 = (z + cnj z) / 2"
  by (cases z) (simp add: Complex_eq)

lemma Complex_Im_express_cnj:
  shows "Complex 0 (Im z) = (z - cnj z)/2"
  by (cases z) (simp add: Complex_eq)

text \<open>Additional properties of @{term cmod}.\<close>

lemma complex_mult_cnj_cmod:
  shows "z * cnj z = cor ((cmod z)\<^sup>2)"
  using complex_norm_square
  by auto

lemma cmod_square: 
  shows "(cmod z)\<^sup>2 = Re (z * cnj z)"
  using complex_mult_cnj_cmod[of z]
  by (simp add: power2_eq_square)

lemma cor_cmod_power_4 [simp]:
  shows "cor (cmod z) ^ 4 = (z * cnj z)\<^sup>2"
  by (metis complex_norm_square cor_squared numeral_times_numeral power2_eq_square semiring_norm(11) semiring_norm(13) semiring_normalization_rules(36))

lemma cnjE:
  assumes "x \<noteq> 0"
  shows "cnj x = cor ((cmod x)\<^sup>2) / x"
  using complex_mult_cnj_cmod[of x] assms
  by (auto simp add: field_simps)

lemma cmod_mult [simp]:
  shows "cmod (a * b) = cmod a * cmod b"
  by (rule norm_mult)

lemma cmod_divide [simp]:
  shows "cmod (a / b) = cmod a / cmod b"
  by (rule norm_divide)

lemma cmod_cor_divide [simp]:
  shows "cmod (z / cor k) = cmod z / \<bar>k\<bar>"
  by auto

lemma cmod_mult_minus_left_distrib [simp]:
  shows "cmod (z*z1 - z*z2) = cmod z * cmod(z1 - z2)"
  by (metis bounded_bilinear.diff_right bounded_bilinear_mult cmod_mult)

lemma cmod_eqI:
  assumes "z1 * cnj z1 = z2 * cnj z2"
  shows "cmod z1 = cmod z2"
  using assms
  by (subst complex_mod_sqrt_Re_mult_cnj)+ auto

lemma cmod_eqE:
  assumes "cmod z1 = cmod z2"
  shows "z1 * cnj z1 = z2 * cnj z2"
proof-
  from assms have "cor ((cmod z1)\<^sup>2) = cor ((cmod z2)\<^sup>2)"
    by auto
  thus ?thesis
    using complex_mult_cnj_cmod
    by auto
qed

lemma cmod_eq_one [simp]:
  shows "cmod a = 1 \<longleftrightarrow> a*cnj a = 1"
  by (metis cmod_eqE cmod_eqI complex_cnj_one monoid_mult_class.mult.left_neutral norm_one)

text \<open>We introduce @{term is_real} (the imaginary part of complex number is zero) and @{term is_imag}
(real part of complex number is zero) operators and prove some of their properties.\<close>

abbreviation is_real where
  "is_real z \<equiv> Im z = 0"

abbreviation is_imag where
  "is_imag z \<equiv> Re z = 0"

lemma real_imag_0:
  assumes "is_real a" "is_imag a" 
  shows "a = 0"
  using assms
  by (simp add: complex.expand)

lemma complex_eq_if_Re_eq:
  assumes "is_real z1" and "is_real z2"
  shows "z1 = z2 \<longleftrightarrow> Re z1 = Re z2"
  using assms
  by (cases z1, cases z2) auto

lemma mult_reals [simp]:
  assumes "is_real a" and "is_real b"
  shows "is_real (a * b)"
  using assms
  by auto

lemma div_reals [simp]:
  assumes "is_real a" and "is_real b"
  shows "is_real (a / b)"
  using assms
  by (simp add: complex_is_Real_iff)

lemma complex_of_real_Re [simp]:
  assumes "is_real k"
  shows "cor (Re k) = k"
  using assms
  by (cases k) (auto simp add: complex_of_real_def)

lemma cor_cmod_real:
  assumes "is_real a"
  shows "cor (cmod a) = a \<or> cor (cmod a) = -a"
  using assms
  unfolding cmod_def
  by (cases "Re a > 0") auto

lemma eq_cnj_iff_real:
  shows "cnj z = z \<longleftrightarrow> is_real z"
  by (cases z) (simp add: Complex_eq)

lemma eq_minus_cnj_iff_imag:
  shows "cnj z = -z \<longleftrightarrow> is_imag z"
  by (cases z) (simp add: Complex_eq)

lemma Re_divide_real:
  assumes "is_real b" and "b \<noteq> 0"
  shows "Re (a / b) = (Re a) / (Re b)"
  using assms
  by (simp add: complex_is_Real_iff)

lemma Re_mult_real:
  assumes "is_real a"
  shows "Re (a * b) = (Re a) * (Re b)"
  using assms
  by simp

lemma Im_mult_real:
  assumes "is_real a"
  shows "Im (a * b) = (Re a) * (Im b)"
  using assms
  by simp

lemma Im_divide_real:
  assumes "is_real b" and "b \<noteq> 0"
  shows "Im (a / b) = (Im a) / (Re b)"
  using assms
  by (simp add: complex_is_Real_iff)

lemma Re_half [simp]:
  shows "Re (x / 2) = Re x / 2"
  by (rule Re_divide_numeral)

lemma Re_double [simp]:
  shows "Re (2 * x) = 2 * Re x"
  using Re_mult_real[of "2" x]
  by simp

lemma Im_half [simp]:
  shows "Im (z / 2) = Im z / 2"
  by (subst Im_divide_real, auto)

lemma Im_double [simp]:
  shows "Im (2 * z) = 2 * Im z"
  using Im_mult_real[of "2" z]
  by simp

lemma Re_sgn:
  assumes "is_real R"
  shows "Re (sgn R) = sgn (Re R)"
  using assms
  by (metis Re_sgn complex_of_real_Re norm_of_real real_sgn_eq)

lemma is_real_div:
  assumes "b \<noteq> 0"
  shows "is_real (a / b) \<longleftrightarrow> a*cnj b = b*cnj a"
  using assms
  by (metis complex_cnj_divide complex_cnj_zero_iff eq_cnj_iff_real frac_eq_eq mult.commute)

lemma is_real_mult_real:
  assumes "is_real a" and "a \<noteq> 0"
  shows "is_real b \<longleftrightarrow> is_real (a * b)"
  using assms
  by (cases a, auto simp add: Complex_eq)

lemma Im_express_cnj:
  shows "Im z = (z - cnj z) / (2 * \<i>)"
  by (simp add: complex_diff_cnj field_simps)

lemma Re_express_cnj: 
  shows "Re z = (z + cnj z) / 2"
  by (simp add: complex_add_cnj)

text \<open>Rotation of complex number for 90 degrees in the positive direction.\<close>

abbreviation rot90 where
  "rot90 z \<equiv> Complex (-Im z) (Re z)"

lemma rot90_ii: 
  shows "rot90 z = z * \<i>"
  by (metis Complex_mult_i complex_surj)

text \<open>With @{term cnj_mix} we introduce scalar product between complex vectors. This operation shows
to be useful to succinctly express some conditions.\<close>

abbreviation cnj_mix where
  "cnj_mix z1 z2 \<equiv> cnj z1 * z2 + z1 * cnj z2"

abbreviation scalprod where
  "scalprod z1 z2 \<equiv> cnj_mix z1 z2 / 2"

lemma cnj_mix_minus:
  shows "cnj z1*z2 - z1*cnj z2 = \<i> * cnj_mix (rot90 z1) z2"
  by (cases z1, cases z2) (simp add: Complex_eq field_simps)

lemma cnj_mix_minus':
  shows "cnj z1*z2 - z1*cnj z2 = rot90 (cnj_mix (rot90 z1) z2)"
  by (cases z1, cases z2) (simp add: Complex_eq field_simps)

lemma cnj_mix_real [simp]:
  shows "is_real (cnj_mix z1 z2)"
  by (cases z1, cases z2) simp

lemma scalprod_real [simp]:
  shows "is_real (scalprod z1 z2)"
  using cnj_mix_real
  by simp

text \<open>Additional properties of @{term cis} function.\<close>

lemma cis_minus_pi2 [simp]:
  shows "cis (-pi/2) = -\<i>"
  by (simp add: cis_inverse[symmetric])

lemma cis_pi2_minus_x [simp]:
  shows "cis (pi/2 - x) = \<i> * cis(-x)"
  using cis_divide[of "pi/2" x, symmetric]
  using cis_divide[of 0 x, symmetric]
  by simp

lemma cis_pm_pi [simp]: 
  shows "cis (x - pi) = - cis x" and  "cis (x + pi) = - cis x"
  by (simp add: cis.ctr complex_minus)+


lemma cis_times_cis_opposite [simp]: 
  shows "cis \<phi> * cis (- \<phi>) = 1"
  by (simp add: cis_mult)

text \<open>@{term cis} repeats only after $2k\pi$\<close>
lemma cis_eq:
  assumes "cis a = cis b"
  shows "\<exists> k::int. a - b = 2 * k * pi"
  using assms sin_cos_eq[of a b]
  using cis.sel[of a] cis.sel[of b]
  by (cases "cis a", cases "cis b") auto

text \<open>@{term cis} is injective on $(-\pi, \pi]$.\<close>
lemma cis_inj:
  assumes "-pi < \<alpha>" and "\<alpha> \<le> pi" and "-pi < \<alpha>'" and "\<alpha>' \<le> pi"
  assumes "cis \<alpha> = cis \<alpha>'"
  shows "\<alpha> = \<alpha>'"
  using assms
  by (metis arg_unique sgn_cis)

text \<open>@{term cis} of an angle combined with @{term cis} of the opposite angle\<close>

lemma cis_diff_cis_opposite [simp]: 
  shows "cis \<phi> - cis (- \<phi>) = 2 * \<i> * sin \<phi>"
  using Im_express_cnj[of "cis \<phi>"]
  by simp

lemma cis_opposite_diff_cis [simp]:
  shows "cis (-\<phi>) - cis (\<phi>) = - 2 * \<i> * sin \<phi>"
  using cis_diff_cis_opposite[of "-\<phi>"]
  by simp

lemma cis_add_cis_opposite [simp]: 
  shows "cis \<phi> + cis (-\<phi>) = 2 * cos \<phi>"
proof-
  have "2 * cos \<phi> = (cis \<phi> + cnj (cis \<phi>))"
    using Re_express_cnj[of "cis \<phi>"]
    by (simp add: field_simps)
  thus ?thesis
    by simp
qed

text \<open>@{term cis} equal to 1 or -1\<close>
lemma cis_one [simp]:
  assumes "sin \<phi> = 0" and "cos \<phi> = 1"
  shows "cis \<phi> = 1"
  using assms
  by (auto simp add: cis.ctr one_complex.code)

lemma cis_minus_one [simp]:
  assumes "sin \<phi> = 0" and "cos \<phi> = -1"
  shows "cis \<phi> = -1"
  using assms
  by (auto simp add: cis.ctr Complex_eq_neg_1)

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Additional properties of complex number argument\<close>
(* -------------------------------------------------------------------------- *)

text \<open>@{term arg} of real numbers\<close>

lemma is_real_arg1:
  assumes "arg z = 0 \<or> arg z = pi"
  shows "is_real z"
  using assms
  using rcis_cmod_arg[of z] Im_rcis[of "cmod z" "arg z"]
  by auto

lemma is_real_arg2:
  assumes "is_real z"
  shows "arg z = 0 \<or> arg z = pi"
proof (cases "z = 0")
  case True
  thus ?thesis
    by (auto simp add: arg_zero)
next
  case False
  hence "sin (arg z) = 0"
    using assms rcis_cmod_arg[of z] Im_rcis[of "cmod z" "arg z"]
    by auto
  thus ?thesis
    using arg_bounded[of z]
    using sin_0_iff_canon
    by simp
qed

lemma arg_complex_of_real_positive [simp]:
  assumes "k > 0"
  shows "arg (cor k) = 0"
proof-
  have "cos (arg (Complex k 0)) > 0"
    using assms
    using rcis_cmod_arg[of "Complex k 0"] Re_rcis[of "cmod (Complex k 0)" "arg (Complex k 0)"]
    by (smt complex.sel(1) mult_nonneg_nonpos norm_ge_zero)
  thus ?thesis
    using assms is_real_arg2[of "cor k"]
    unfolding complex_of_real_def
    by auto
qed

lemma arg_complex_of_real_negative [simp]:
  assumes "k < 0"
  shows "arg (cor k) = pi"
proof-
  have "cos (arg (Complex k 0)) < 0"
    using \<open>k < 0\<close> rcis_cmod_arg[of "Complex k 0"] Re_rcis[of "cmod (Complex k 0)" "arg (Complex k 0)"]
    by (smt complex.sel(1) mult_nonneg_nonneg norm_ge_zero)
  thus ?thesis
    using assms is_real_arg2[of "cor k"]
    unfolding complex_of_real_def
    by auto
qed

lemma arg_0_iff:
  shows "z \<noteq> 0 \<and> arg z = 0 \<longleftrightarrow> is_real z \<and> Re z > 0"
  by (smt arg_complex_of_real_negative arg_complex_of_real_positive arg_zero complex_of_real_Re is_real_arg1 pi_gt_zero zero_complex.simps)

lemma arg_pi_iff:
  shows "arg z = pi \<longleftrightarrow> is_real z \<and> Re z < 0"
  by (smt arg_complex_of_real_negative arg_complex_of_real_positive arg_zero complex_of_real_Re is_real_arg1 pi_gt_zero zero_complex.simps)


text \<open>@{term arg} of imaginary numbers\<close>

lemma is_imag_arg1:
  assumes "arg z = pi/2 \<or> arg z = -pi/2"
  shows "is_imag z"
  using assms
  using rcis_cmod_arg[of z] Re_rcis[of "cmod z" "arg z"]
  by (metis cos_minus cos_pi_half minus_divide_left mult_eq_0_iff)

lemma is_imag_arg2:
  assumes "is_imag z" and "z \<noteq> 0"
  shows "arg z = pi/2 \<or> arg z = -pi/2"
proof-
  have "cos (arg z) = 0"
    using assms
    by (metis Re_rcis no_zero_divisors norm_eq_zero rcis_cmod_arg)
  thus ?thesis
    using arg_bounded[of z]
    using cos_0_iff_canon[of "arg z"]
    by simp
qed

lemma arg_complex_of_real_times_i_positive [simp]:
  assumes "k > 0"
  shows "arg (cor k * \<i>) = pi / 2"
proof-
  have "sin (arg (Complex 0 k)) > 0"
    using \<open>k > 0\<close> rcis_cmod_arg[of "Complex 0 k"] Im_rcis[of "cmod (Complex 0 k)" "arg (Complex 0 k)"]
    by (smt complex.sel(2) mult_nonneg_nonpos norm_ge_zero)
  thus ?thesis
    using assms is_imag_arg2[of "cor k * \<i>"]
    using arg_zero complex_of_real_i
    by force
qed

lemma arg_complex_of_real_times_i_negative [simp]:
  assumes "k < 0"
  shows "arg (cor k * \<i>) = - pi / 2"
proof-
  have "sin (arg (Complex 0 k)) < 0"
    using \<open>k < 0\<close> rcis_cmod_arg[of "Complex 0 k"] Im_rcis[of "cmod (Complex 0 k)" "arg (Complex 0 k)"]
    by (smt complex.sel(2) mult_nonneg_nonneg norm_ge_zero)
  thus ?thesis
    using assms is_imag_arg2[of "cor k * \<i>"]
    using arg_zero complex_of_real_i[of k]
    by (smt complex.sel(1) sin_pi_half sin_zero)
qed

lemma arg_pi2_iff:
  shows "z \<noteq> 0 \<and> arg z = pi / 2 \<longleftrightarrow> is_imag z \<and> Im z > 0"
  by (smt Im_rcis Re_i_times Re_rcis arcsin_minus_1 cos_pi_half divide_minus_left mult.commute mult_cancel_right1 rcis_cmod_arg is_imag_arg2 sin_arcsin sin_pi_half zero_less_mult_pos zero_less_norm_iff)

lemma arg_minus_pi2_iff:
  shows "z \<noteq> 0 \<and> arg z = - pi / 2 \<longleftrightarrow> is_imag z \<and> Im z < 0"
  by (smt arg_pi2_iff complex.expand divide_cancel_right pi_neq_zero is_imag_arg1 is_imag_arg2 zero_complex.simps(1) zero_complex.simps(2))

lemma arg_ii [simp]:
  shows "arg \<i> = pi/2"
proof-
  have "\<i> = cis (arg \<i>)"
    using rcis_cmod_arg[of \<i>]
    by (simp add: rcis_def)
  hence "cos (arg \<i>) = 0" "sin (arg \<i>) = 1"
    by (metis cis.simps(1) imaginary_unit.simps(1), metis cis.simps(2) imaginary_unit.simps(2))
  thus ?thesis
    using cos_0_iff_canon[of "arg \<i>"] arg_bounded[of \<i>]
    by auto
qed

lemma arg_minus_ii [simp]: 
  shows "arg (-\<i>) = -pi/2"
proof-
  have "-\<i> = cis (arg (- \<i>))"
    using rcis_cmod_arg[of "-\<i>"]
    by (simp add: rcis_def)
  hence "cos (arg (-\<i>)) = 0" "sin (arg (-\<i>)) = -1"
    using cis.simps[of "arg (-\<i>)"]
    by auto
  thus ?thesis
    using cos_0_iff_canon[of "arg (-\<i>)"] arg_bounded[of "-\<i>"]
    by fastforce
qed

text \<open>Argument is a canonical angle\<close>

lemma canon_ang_arg:
  shows "\<downharpoonright>arg z\<downharpoonleft> = arg z"
  using canon_ang_id[of "arg z"] arg_bounded
  by simp

lemma arg_cis:
  shows "arg (cis \<phi>) = \<downharpoonright>\<phi>\<downharpoonleft>"
proof (rule canon_ang_eqI[symmetric])
  show "- pi < arg (cis \<phi>) \<and> arg (cis \<phi>) \<le> pi"
    using arg_bounded
    by simp
next
  show "\<exists> k::int. arg (cis \<phi>) - \<phi> = 2*k*pi"
  proof-
    have "cis (arg (cis \<phi>)) = cis \<phi>"
      using cis_arg[of "cis \<phi>"]
      by auto
    thus ?thesis
      using cis_eq
      by auto
  qed
qed

text \<open>Cosine and sine of @{term arg}\<close>

lemma cos_arg:
  assumes "z \<noteq> 0"
  shows "cos (arg z) = Re z / cmod z"
  by (metis Complex.Re_sgn cis.simps(1) assms cis_arg)

lemma sin_arg:
  assumes "z \<noteq> 0"
  shows "sin (arg z) = Im z / cmod z"
  by (metis Complex.Im_sgn cis.simps(2) assms cis_arg)

text \<open>Argument of product\<close>

lemma cis_arg_mult:
  assumes "z1 * z2 \<noteq> 0"
  shows "cis (arg (z1 * z2)) = cis (arg z1 + arg z2)"
proof-
  have "z1 * z2 = cor (cmod z1) * cor (cmod z2) * cis (arg z1) * cis (arg z2)"
    using rcis_cmod_arg[of z1, symmetric]  rcis_cmod_arg[of z2, symmetric]
    unfolding rcis_def
    by algebra
  hence "z1 * z2 = cor (cmod (z1 * z2)) * cis (arg z1 + arg z2)"
    using cis_mult[of "arg z1" "arg z2"]
    by auto
  hence "cor (cmod (z1 * z2)) * cis (arg z1 + arg z2) =  cor (cmod (z1 * z2)) * cis (arg (z1 * z2))"
    using assms
    using rcis_cmod_arg[of "z1*z2"]
    unfolding rcis_def
    by auto
  thus ?thesis
    using mult_cancel_left[of "cor (cmod (z1 * z2))" "cis (arg z1 + arg z2)" "cis (arg (z1 * z2))"]
    using assms
    by auto
qed

lemma arg_mult_2kpi:
  assumes "z1 * z2 \<noteq> 0"
  shows "\<exists> k::int. arg (z1 * z2) = arg z1 + arg z2 + 2*k*pi"
proof-
  have "cis (arg (z1*z2)) = cis (arg z1 + arg z2)"
    by (rule cis_arg_mult[OF assms])
  thus ?thesis
    using cis_eq[of "arg (z1*z2)" "arg z1 + arg z2"]
    by (auto simp add: field_simps)
qed

lemma arg_mult:
  assumes "z1 * z2 \<noteq> 0"
  shows "arg(z1 * z2) = \<downharpoonright>arg z1 + arg z2\<downharpoonleft>"
proof-
  obtain k::int where "arg(z1 * z2) = arg z1 + arg z2 + 2*k*pi"
    using arg_mult_2kpi[of z1 z2]
    using assms
    by auto
  hence "\<downharpoonright>arg(z1 * z2)\<downharpoonleft> = \<downharpoonright>arg z1 + arg z2\<downharpoonleft>"
    using canon_ang_eq
    by(simp add:field_simps)
  thus ?thesis
    using canon_ang_arg[of "z1*z2"]
    by auto
qed

lemma arg_mult_real_positive [simp]:
  assumes "k > 0"
  shows "arg (cor k * z) = arg z"
proof (cases "z = 0")
  case True
  thus ?thesis
    by (auto simp add: arg_zero)
next
  case False
  thus ?thesis
    using assms
    using arg_mult[of "cor k" z]
    by (auto simp add: canon_ang_arg)
qed

lemma arg_mult_real_negative [simp]:
  assumes "k < 0"
  shows "arg (cor k * z) = arg (-z)"
proof (cases "z = 0")
  case True
  thus ?thesis
    by (auto simp add: arg_zero)
next
  case False
  thus ?thesis
    using assms
    using arg_mult[of "cor k" z]
    using arg_mult[of "-1" z]
    using arg_complex_of_real_negative[of k] arg_complex_of_real_negative[of "-1"]
    by auto
qed

lemma arg_div_real_positive [simp]:
  assumes "k > 0"
  shows "arg (z / cor k) = arg z"
proof(cases "z = 0")
  case True
  thus ?thesis
    by auto
next
  case False
  thus ?thesis
    using assms
    using arg_mult_real_positive[of "1/k" z]
    by auto
qed

lemma arg_div_real_negative [simp]:
  assumes "k < 0"
  shows "arg (z / cor k) = arg (-z)"
proof(cases "z = 0")
  case True
  thus ?thesis
    by auto
next
  case False
  thus ?thesis
    using assms
    using arg_mult_real_negative[of "1/k" z]
    by auto
qed

lemma arg_mult_eq:
  assumes "z * z1 \<noteq> 0" and "z * z2 \<noteq> 0"
  assumes "arg (z * z1) = arg (z * z2)"
  shows "arg z1 = arg z2"
proof-
  from assms have "\<downharpoonright>arg z + arg z1\<downharpoonleft> = \<downharpoonright>arg z + arg z2\<downharpoonleft>"
    by (simp add: arg_mult)
  then obtain x::int where *: "arg z1 - arg z2 = 2 * x * pi"
    using canon_ang_eqE[of "arg z + arg z1" "arg z + arg z2"]
    by auto
  moreover
  have "arg z1 - arg z2 < 2*pi" "arg z1 - arg z2 > -2*pi"
    using arg_bounded[of z1] arg_bounded[of z2]
    by auto
  ultimately
  have "-1 < x" "x < 1"
    using divide_strict_right_mono[of "-pi" "pi * x" pi]
    by auto
  hence "x = 0"
    by auto
  thus ?thesis
    using *
    by simp
qed

text \<open>Argument of conjugate\<close>

lemma arg_cnj_pi:
  assumes "arg z = pi"
  shows "arg (cnj z) = pi"
proof-
  have "cos (arg (cnj z)) = cos (arg z)"
    using rcis_cmod_arg[of z, symmetric] Re_rcis[of "cmod z" "arg z"]
    using rcis_cmod_arg[of "cnj z", symmetric] Re_rcis[of "cmod (cnj z)" "arg (cnj z)"]
    by auto
  hence "arg (cnj z) = arg z \<or> arg(cnj z) = -arg z"
    using arg_bounded[of z] arg_bounded[of "cnj z"]
    by (metis arccos_cos arccos_cos2 less_eq_real_def linorder_le_cases minus_minus)
  thus ?thesis
    using assms
    using arg_bounded[of "cnj z"]
    by auto
qed

lemma arg_cnj_not_pi:
  assumes "arg z \<noteq> pi"
  shows "arg (cnj z) = -arg z"
proof(cases "arg z = 0")
  case True
  thus ?thesis
    using eq_cnj_iff_real[of z] is_real_arg1[of z] by force
next
  case False
  have "cos (arg (cnj z)) = cos (arg z)"
    using rcis_cmod_arg[of z] Re_rcis[of "cmod z" "arg z"]
    using rcis_cmod_arg[of "cnj z"] Re_rcis[of "cmod (cnj z)" "arg (cnj z)"]
    by auto
  hence "arg (cnj z) = arg z \<or> arg(cnj z) = -arg z"
    using arg_bounded[of z] arg_bounded[of "cnj z"]
    by (metis arccos_cos arccos_cos2 less_eq_real_def linorder_le_cases minus_minus)
  moreover
  have "sin (arg (cnj z)) = -sin (arg z)"
    using rcis_cmod_arg[of z] Im_rcis[of "cmod z" "arg z"]
    using rcis_cmod_arg[of "cnj z"] Im_rcis[of "cmod (cnj z)" "arg (cnj z)"]
    using calculation eq_cnj_iff_real is_real_arg2
    by force
  hence "arg (cnj z) \<noteq> arg z"
    using sin_0_iff_canon[of "arg (cnj z)"] arg_bounded False assms
    by auto
  ultimately
  show ?thesis
    by auto
qed

text \<open>Argument of reciprocal\<close>

lemma arg_inv_not_pi:
  assumes "z \<noteq> 0" and "arg z \<noteq> pi"
  shows "arg (1 / z) = - arg z"
proof-
  have "1/z = cnj z / cor ((cmod z)\<^sup>2 )"
    using \<open>z \<noteq> 0\<close> complex_mult_cnj_cmod[of z]
    by (auto simp add:field_simps)
  thus ?thesis
    using arg_div_real_positive[of "(cmod z)\<^sup>2" "cnj z"] \<open>z \<noteq> 0\<close>
    using arg_cnj_not_pi[of z] \<open>arg z \<noteq> pi\<close>
    by auto
qed

lemma arg_inv_pi:
  assumes "z \<noteq> 0" and "arg z = pi"
  shows "arg (1 / z) = pi"
proof-
  have "1/z = cnj z / cor ((cmod z)\<^sup>2 )"
    using \<open>z \<noteq> 0\<close> complex_mult_cnj_cmod[of z]
    by (auto simp add:field_simps)
  thus ?thesis
    using arg_div_real_positive[of "(cmod z)\<^sup>2" "cnj z"] \<open>z \<noteq> 0\<close>
    using arg_cnj_pi[of z] \<open>arg z = pi\<close>
    by auto
qed

lemma arg_inv_2kpi:
  assumes "z \<noteq> 0"
  shows "\<exists> k::int. arg (1 / z) = - arg z + 2*k*pi"
  using arg_inv_pi[OF assms]
  using arg_inv_not_pi[OF assms]
  by (cases "arg z = pi") (rule_tac x="1" in exI, simp, rule_tac x="0" in exI, simp)

lemma arg_inv:
  assumes "z \<noteq> 0"
  shows "arg (1 / z) = \<downharpoonright>- arg z\<downharpoonleft>"
proof-
  obtain k::int where "arg(1 / z) = - arg z + 2*k*pi"
    using arg_inv_2kpi[of z]
    using assms
    by auto
  hence "\<downharpoonright>arg(1 / z)\<downharpoonleft> = \<downharpoonright>- arg z\<downharpoonleft>"
    using canon_ang_eq
    by(simp add:field_simps)
  thus ?thesis
    using canon_ang_arg[of "1 / z"]
    by auto
qed

text \<open>Argument of quotient\<close>

lemma arg_div_2kpi:
  assumes "z1 \<noteq> 0" and "z2 \<noteq> 0"
  shows "\<exists> k::int. arg (z1 / z2) = arg z1 - arg z2 + 2*k*pi"
proof-
  obtain x1 where "arg (z1 * (1 / z2)) = arg z1 + arg (1 / z2) + 2 * real_of_int x1 * pi"
    using assms arg_mult_2kpi[of z1 "1/z2"]
    by auto
  moreover
  obtain x2 where "arg (1 / z2) = - arg z2 + 2 * real_of_int x2 * pi"
    using assms arg_inv_2kpi[of z2]
    by auto
  ultimately
  show ?thesis
    by (rule_tac x="x1 + x2" in exI, simp add: field_simps)
qed

lemma arg_div:
  assumes "z1 \<noteq> 0" and "z2 \<noteq> 0"
  shows "arg(z1 / z2) = \<downharpoonright>arg z1 - arg z2\<downharpoonleft>"
proof-
  obtain k::int where "arg(z1 / z2) = arg z1 - arg z2 + 2*k*pi"
    using arg_div_2kpi[of z1 z2]
    using assms
    by auto
  hence "canon_ang(arg(z1 / z2)) = canon_ang(arg z1 - arg z2)"
    using canon_ang_eq
    by(simp add:field_simps)
  thus ?thesis
    using canon_ang_arg[of "z1/z2"]
    by auto
qed

text \<open>Argument of opposite\<close>

lemma arg_uminus:
  assumes "z \<noteq> 0"
  shows "arg (-z) = \<downharpoonright>arg z + pi\<downharpoonleft>"
  using assms
  using arg_mult[of "-1" z]
  using arg_complex_of_real_negative[of "-1"]
  by (auto simp add: field_simps)

lemma arg_uminus_opposite_sign:
  assumes "z \<noteq> 0"
  shows "arg z > 0 \<longleftrightarrow> \<not> arg (-z) > 0"
proof (cases "arg z = 0")
  case True
  thus ?thesis
    using assms
    by (simp add: arg_uminus)
next
  case False
  show ?thesis
  proof (cases "arg z > 0")
    case True
    thus ?thesis
      using assms
      using arg_bounded[of z]
      using canon_ang_plus_pi1[of "arg z"]
      by (simp add: arg_uminus)
  next
    case False
    thus ?thesis
      using \<open>arg z \<noteq> 0\<close>
      using assms
      using arg_bounded[of z]
      using canon_ang_plus_pi2[of "arg z"]
      by (simp add: arg_uminus)
  qed
qed

text \<open>Sign of argument is the same as the sign of the Imaginary part\<close>

lemma arg_Im_sgn:
  assumes "\<not> is_real z"
  shows "sgn (arg z) = sgn (Im z)"
proof-
  have "z \<noteq> 0"
    using assms
    by auto
  then obtain r \<phi> where polar: "z = cor r * cis \<phi>" "\<phi> = arg z" "r > 0"
    by (smt cmod_cis mult_eq_0_iff norm_ge_zero of_real_0)
  hence "Im z = r * sin \<phi>"
    by (metis Im_mult_real Re_complex_of_real cis.simps(2) Im_complex_of_real)
  hence  "Im z > 0 \<longleftrightarrow> sin \<phi> > 0" "Im z < 0 \<longleftrightarrow> sin \<phi> < 0"
    using \<open>r > 0\<close>
    using mult_pos_pos mult_nonneg_nonneg zero_less_mult_pos mult_less_cancel_left
    by smt+
  moreover
  have "\<phi> \<noteq> pi" "\<phi> \<noteq> 0"
    using \<open>\<not> is_real z\<close> polar cis_pi
    by force+
  hence "sin \<phi> > 0 \<longleftrightarrow> \<phi> > 0" "\<phi> < 0 \<longleftrightarrow> sin \<phi> < 0"
    using \<open>\<phi> = arg z\<close> \<open>\<phi> \<noteq> 0\<close> \<open>\<phi> \<noteq> pi\<close>
    using arg_bounded[of z]
    by (smt sin_gt_zero sin_le_zero sin_pi_minus sin_0_iff_canon sin_ge_zero)+
  ultimately
  show ?thesis
    using \<open>\<phi> = arg z\<close>
    by auto
qed


subsubsection \<open>Complex square root\<close>

definition
  "ccsqrt z = rcis (sqrt (cmod z)) (arg z / 2)"

lemma square_ccsqrt [simp]:
  shows "(ccsqrt x)\<^sup>2 = x"
  unfolding ccsqrt_def
  by (subst DeMoivre2) (simp add: rcis_cmod_arg)

lemma ex_complex_sqrt:
  shows "\<exists> s::complex. s*s = z"
  unfolding power2_eq_square[symmetric]
  by (rule_tac x="csqrt z" in exI) simp

lemma ccsqrt:
  assumes "s * s = z"
  shows "s = ccsqrt z \<or> s = -ccsqrt z"
proof (cases "s = 0")
  case True
  thus ?thesis
    using assms
    unfolding ccsqrt_def
    by simp
next
  case False
  then obtain k::int where "cmod s * cmod s = cmod z" "2 * arg s - arg z = 2*k*pi"
    using assms
    using rcis_cmod_arg[of z] rcis_cmod_arg[of s]
    using arg_mult[of s s]
    using canon_ang(3)[of "2*arg s"]
    by (auto simp add: norm_mult arg_mult)
  have *: "sqrt (cmod z) = cmod s"
    using \<open>cmod s * cmod s = cmod z\<close>
    by (smt norm_not_less_zero real_sqrt_abs2)

  have **: "arg z / 2 = arg s - k*pi"
    using \<open>2 * arg s - arg z = 2*k*pi\<close>
    by simp

  have "cis (arg s - k*pi) = cis (arg s) \<or> cis (arg s - k*pi) = -cis (arg s)"
  proof (cases "even k")
    case True
    hence "cis (arg s - k*pi) = cis (arg s)"
      by (simp add: cis_def complex.corec cos_diff sin_diff)
    thus ?thesis
      by simp
  next
    case False
    hence "cis (arg s - k*pi) = -cis (arg s)"
      by (simp add: cis_def complex.corec Complex_eq cos_diff sin_diff)
    thus ?thesis
      by simp
  qed
  thus ?thesis
  proof
    assume ***: "cis (arg s - k * pi) = cis (arg s)"
    hence "s = ccsqrt z"
      using rcis_cmod_arg[of s]
      unfolding ccsqrt_def rcis_def
      by (subst *, subst **, subst ***, simp)
    thus ?thesis
      by simp
  next
    assume ***: "cis (arg s - k * pi) = -cis (arg s)"
    hence "s = - ccsqrt z"
      using rcis_cmod_arg[of s]
      unfolding ccsqrt_def rcis_def
      by (subst *, subst **, subst ***, simp)
    thus ?thesis
      by simp
  qed
qed

lemma null_ccsqrt [simp]:
  shows "ccsqrt x = 0 \<longleftrightarrow> x = 0"
  unfolding ccsqrt_def
  by auto

lemma ccsqrt_mult:
  shows "ccsqrt (a * b) = ccsqrt a * ccsqrt b \<or>
         ccsqrt (a * b) = - ccsqrt a * ccsqrt b"
proof (cases "a = 0 \<or> b = 0")
  case True
  thus ?thesis
    by auto
next
  case False
  obtain k::int where "arg a + arg b - \<downharpoonright>arg a + arg b\<downharpoonleft> = 2 * real_of_int k * pi"
    using canon_ang(3)[of "arg a + arg b"]
    by auto
  hence *: "\<downharpoonright>arg a + arg b\<downharpoonleft> = arg a + arg b - 2 * (real_of_int k) * pi"
    by (auto simp add: field_simps)

  have "cis (\<downharpoonright>arg a + arg b\<downharpoonleft> / 2) = cis (arg a / 2 + arg b / 2) \<or> cis (\<downharpoonright>arg a + arg b\<downharpoonleft> / 2) = - cis (arg a / 2 + arg b / 2)"
    using cos_even_kpi[of k] cos_odd_kpi[of k]
    by ((subst *)+, (subst diff_divide_distrib)+, (subst add_divide_distrib)+)
       (cases "even k", auto simp add: cis_def complex.corec Complex_eq cos_diff sin_diff)
  thus ?thesis
    using False
    unfolding ccsqrt_def
    by (simp add: rcis_mult real_sqrt_mult arg_mult)
       (auto simp add: rcis_def)
qed

lemma csqrt_real:
  assumes "is_real x"
  shows "(Re x \<ge> 0 \<and> ccsqrt x = cor (sqrt (Re x))) \<or>
         (Re x < 0 \<and> ccsqrt x = \<i> * cor (sqrt (- (Re x))))"
proof (cases "x = 0")
  case True
  thus ?thesis
    by auto
next
  case False
  show ?thesis
  proof (cases "Re x > 0")
    case True
    hence "arg x = 0"
      using \<open>is_real x\<close>
      by (metis arg_complex_of_real_positive complex_of_real_Re)
    thus ?thesis
      using \<open>Re x > 0\<close> \<open>is_real x\<close>
      unfolding ccsqrt_def
      by (simp add: cmod_eq_Re)
  next
    case False
    hence "Re x < 0"
      using \<open>x \<noteq> 0\<close> \<open>is_real x\<close>
      using complex_eq_if_Re_eq by auto
    hence "arg x = pi"
      using \<open>is_real x\<close>
      by (metis arg_complex_of_real_negative complex_of_real_Re)
    thus ?thesis
      using \<open>Re x < 0\<close> \<open>is_real x\<close>
      unfolding ccsqrt_def rcis_def
      by (simp add: cis_def complex.corec Complex_eq cmod_eq_Re)
  qed
qed


text \<open>Rotation of complex vector to x-axis.\<close>

lemma is_real_rot_to_x_axis:
  assumes "z \<noteq> 0"
  shows "is_real (cis (-arg z) * z)"
proof (cases "arg z = pi")
  case True
  thus ?thesis
    using is_real_arg1[of z]
    by auto
next
  case False
  hence "\<downharpoonright>- arg z\<downharpoonleft> = - arg z"
    using canon_ang_eqI[of "- arg z" "-arg z"]
    using arg_bounded[of z]
    by (auto simp add: field_simps)
  hence "arg (cis (- (arg z)) * z) = 0"
    using arg_mult[of "cis (- (arg z))" z] \<open>z \<noteq> 0\<close>
    using arg_cis[of "- arg z"]
    by simp
  thus ?thesis
    using is_real_arg1[of "cis (- arg z) * z"]
    by auto
qed

lemma positive_rot_to_x_axis:
  assumes "z \<noteq> 0"
  shows "Re (cis (-arg z) * z) > 0"
  using assms
  by (smt Re_complex_of_real cis_rcis_eq mult_cancel_right1 rcis_cmod_arg rcis_mult rcis_zero_arg zero_less_norm_iff)

text \<open>Inequalities involving @{term cmod}.\<close>

lemma cmod_1_plus_mult_le:
  shows "cmod (1 + z*w) \<le> sqrt((1 + (cmod z)\<^sup>2) * (1 + (cmod w)\<^sup>2))"
proof-
  have "Re ((1+z*w)*(1+cnj z*cnj w)) \<le> Re (1+z*cnj z)* Re (1+w*cnj w)"
  proof-
    have "Re ((w - cnj z)*cnj(w - cnj z)) \<ge> 0"
      by (subst complex_mult_cnj_cmod) (simp add: power2_eq_square)
    hence "Re (z*w + cnj z * cnj w) \<le> Re (w*cnj w) + Re(z*cnj z)"
      by (simp add: field_simps)
    thus ?thesis
      by (simp add: field_simps)
  qed
  hence "(cmod (1 + z * w))\<^sup>2 \<le> (1 + (cmod z)\<^sup>2) * (1 + (cmod w)\<^sup>2)"
    by (subst cmod_square)+ simp
  thus ?thesis
    by (metis abs_norm_cancel real_sqrt_abs real_sqrt_le_iff)
qed

lemma cmod_diff_ge: 
  shows "cmod (b - c) \<ge> sqrt (1 + (cmod b)\<^sup>2) - sqrt (1 + (cmod c)\<^sup>2)"
proof-
  have "(cmod (b - c))\<^sup>2 + (1/2*Im(b*cnj c - c*cnj b))\<^sup>2 \<ge> 0"
    by simp
  hence "(cmod (b - c))\<^sup>2 \<ge> - (1/2*Im(b*cnj c - c*cnj b))\<^sup>2"
    by simp
  hence "(cmod (b - c))\<^sup>2 \<ge> (1/2*Re(b*cnj c + c*cnj b))\<^sup>2 - Re(b*cnj b*c*cnj c) "
    by (auto simp add: power2_eq_square field_simps)
  hence "Re ((b - c)*(cnj b - cnj c)) \<ge> (1/2*Re(b*cnj c + c*cnj b))\<^sup>2 - Re(b*cnj b*c*cnj c)"
    by (subst (asm) cmod_square) simp
  moreover
  have "(1 + (cmod b)\<^sup>2) * (1 + (cmod c)\<^sup>2) = 1 + Re(b*cnj b) + Re(c*cnj c) + Re(b*cnj b*c*cnj c)"
    by (subst cmod_square)+ (simp add: field_simps power2_eq_square)
  moreover
  have "(1 + Re (scalprod b c))\<^sup>2 = 1 + 2*Re(scalprod b c) + ((Re (scalprod b c))\<^sup>2)"
    by (subst power2_sum) simp
  hence "(1 + Re (scalprod b c))\<^sup>2 = 1 + Re(b*cnj c + c*cnj b) + (1/2 * Re (b*cnj c + c*cnj b))\<^sup>2"
    by simp
  ultimately
  have "(1 + (cmod b)\<^sup>2) * (1 + (cmod c)\<^sup>2) \<ge> (1 + Re (scalprod b c))\<^sup>2"
    by (simp add: field_simps)
  moreover
  have "sqrt((1 + (cmod b)\<^sup>2) * (1 + (cmod c)\<^sup>2)) \<ge> 0"
    by (metis one_power2 real_sqrt_sum_squares_mult_ge_zero)
  ultimately
  have "sqrt((1 + (cmod b)\<^sup>2) * (1 + (cmod c)\<^sup>2)) \<ge> 1 + Re (scalprod b c)"
    by (metis power2_le_imp_le real_sqrt_ge_0_iff real_sqrt_pow2_iff)
  hence "Re ((b - c) * (cnj b - cnj c)) \<ge> 1 + Re (c*cnj c) + 1 + Re (b*cnj b) - 2*sqrt((1 + (cmod b)\<^sup>2) * (1 + (cmod c)\<^sup>2))"
    by (simp add: field_simps)
  hence *: "(cmod (b - c))\<^sup>2 \<ge> (sqrt (1 + (cmod b)\<^sup>2) - sqrt (1 + (cmod c)\<^sup>2))\<^sup>2"
    apply (subst cmod_square)+
    apply (subst (asm) cmod_square)+
    apply (subst power2_diff)
    apply (subst real_sqrt_pow2, simp)
    apply (subst real_sqrt_pow2, simp)
    apply (simp add: real_sqrt_mult)
    done
  thus ?thesis
  proof (cases "sqrt (1 + (cmod b)\<^sup>2) - sqrt (1 + (cmod c)\<^sup>2) > 0")
    case True
    thus ?thesis
      using power2_le_imp_le[OF *]
      by simp
  next
    case False
    hence "0 \<ge> sqrt (1 + (cmod b)\<^sup>2) - sqrt (1 + (cmod c)\<^sup>2)"
      by (metis less_eq_real_def linorder_neqE_linordered_idom)
    moreover
    have "cmod (b - c) \<ge> 0"
      by simp
    ultimately
    show ?thesis
      by (metis add_increasing monoid_add_class.add.right_neutral)
  qed
qed

lemma cmod_diff_le:
  shows "cmod (b - c) \<le> sqrt (1 + (cmod b)\<^sup>2) + sqrt (1 + (cmod c)\<^sup>2)"
proof-
  have "(cmod (b + c))\<^sup>2 + (1/2*Im(b*cnj c - c*cnj b))\<^sup>2 \<ge> 0"
    by simp
  hence "(cmod (b + c))\<^sup>2 \<ge> - (1/2*Im(b*cnj c - c*cnj b))\<^sup>2"
    by simp
  hence "(cmod (b + c))\<^sup>2 \<ge> (1/2*Re(b*cnj c + c*cnj b))\<^sup>2 - Re(b*cnj b*c*cnj c) "
    by (auto simp add: power2_eq_square field_simps)
  hence "Re ((b + c)*(cnj b + cnj c)) \<ge> (1/2*Re(b*cnj c + c*cnj b))\<^sup>2 - Re(b*cnj b*c*cnj c)"
    by (subst (asm) cmod_square) simp
  moreover
  have "(1 + (cmod b)\<^sup>2) * (1 + (cmod c)\<^sup>2) = 1 + Re(b*cnj b) + Re(c*cnj c) + Re(b*cnj b*c*cnj c)"
    by (subst cmod_square)+ (simp add: field_simps power2_eq_square)
  moreover
  have ++: "2*Re(scalprod b c) = Re(b*cnj c + c*cnj b)"
    by simp
  have "(1 - Re (scalprod b c))\<^sup>2 = 1 - 2*Re(scalprod b c) + ((Re (scalprod b c))\<^sup>2)"
    by (subst power2_diff) simp
  hence "(1 - Re (scalprod b c))\<^sup>2 = 1 - Re(b*cnj c + c*cnj b) + (1/2 * Re (b*cnj c + c*cnj b))\<^sup>2"
    by (subst ++[symmetric]) simp
  ultimately
  have "(1 + (cmod b)\<^sup>2) * (1 + (cmod c)\<^sup>2) \<ge> (1 - Re (scalprod b c))\<^sup>2"
    by (simp add: field_simps)
  moreover
  have "sqrt((1 + (cmod b)\<^sup>2) * (1 + (cmod c)\<^sup>2)) \<ge> 0"
    by (metis one_power2 real_sqrt_sum_squares_mult_ge_zero)
  ultimately
  have "sqrt((1 + (cmod b)\<^sup>2) * (1 + (cmod c)\<^sup>2)) \<ge> 1 - Re (scalprod b c)"
    by (metis power2_le_imp_le real_sqrt_ge_0_iff real_sqrt_pow2_iff)
  hence "Re ((b - c) * (cnj b - cnj c)) \<le> 1 + Re (c*cnj c) + 1 + Re (b*cnj b) + 2*sqrt((1 + (cmod b)\<^sup>2) * (1 + (cmod c)\<^sup>2))"
    by (simp add: field_simps)
  hence *: "(cmod (b - c))\<^sup>2 \<le> (sqrt (1 + (cmod b)\<^sup>2) + sqrt (1 + (cmod c)\<^sup>2))\<^sup>2"
    apply (subst cmod_square)+
    apply (subst (asm) cmod_square)+
    apply (subst power2_sum)
    apply (subst real_sqrt_pow2, simp)
    apply (subst real_sqrt_pow2, simp)
    apply (simp add: real_sqrt_mult)
    done
  thus ?thesis
    using power2_le_imp_le[OF *]
    by simp
qed


text \<open>Definition of Euclidean distance between two complex numbers.\<close>

definition cdist where
  [simp]: "cdist z1 z2 \<equiv> cmod (z2 - z1)"

text \<open>Misc. properties of complex numbers.\<close>

lemma ex_complex_to_complex [simp]:
  fixes z1 z2 :: complex
  assumes "z1 \<noteq> 0" and "z2 \<noteq> 0"
  shows "\<exists>k. k \<noteq> 0 \<and> z2 = k * z1"
  using assms
  by (rule_tac x="z2/z1" in exI) simp

lemma ex_complex_to_one [simp]:
  fixes z::complex
  assumes "z \<noteq> 0"
  shows "\<exists>k. k \<noteq> 0 \<and> k * z = 1"
  using assms
  by (rule_tac x="1/z" in exI) simp

lemma ex_complex_to_complex2 [simp]:
  fixes z::complex
  shows "\<exists>k. k \<noteq> 0 \<and> k * z = z"
  by (rule_tac x="1" in exI) simp

lemma complex_sqrt_1:
  fixes z::complex
  assumes "z \<noteq> 0"
  shows "z = 1 / z \<longleftrightarrow> z = 1 \<or> z = -1"
  using assms
  using nonzero_eq_divide_eq square_eq_iff
  by fastforce

end
