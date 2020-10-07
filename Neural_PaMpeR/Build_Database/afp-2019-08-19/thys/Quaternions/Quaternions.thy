section\<open>Theory of Quaternions\<close>
text\<open>This theory is inspired by the HOL Light development of quaternions, but follows its own route. 
Quaternions are developed coinductively, as in the existing formalisation of the complex numbers. 
Quaternions are quickly shown to belong to the type classes of real normed division algebras 
and real inner product spaces. And therefore they inherit a great body of facts involving algebraic 
laws, limits, continuity, etc., which must be proved explicitly in the HOL Light version. 
The development concludes with the geometric interpretation of the product of imaginary quaternions.\<close>
theory "Quaternions"
  imports "HOL-Analysis.Analysis"
begin

subsection\<open>Basic definitions\<close>

text\<open>As with the complex numbers, coinduction is convenient\<close>

codatatype quat = Quat (Re: real) (Im1: real) (Im2: real) (Im3: real)

lemma quat_eqI [intro?]: "\<lbrakk>Re x = Re y; Im1 x = Im1 y; Im2 x = Im2 y; Im3 x = Im3 y\<rbrakk> \<Longrightarrow> x = y"
  by (rule quat.expand) simp

lemma quat_eq_iff: "x = y \<longleftrightarrow> Re x = Re y \<and> Im1 x = Im1 y \<and> Im2 x = Im2 y \<and> Im3 x = Im3 y"
  by (auto intro: quat.expand)

context
begin
no_notation Complex.imaginary_unit ("\<i>")

primcorec quat_ii :: quat  ("\<i>")
  where "Re \<i> = 0" | "Im1 \<i> = 1" | "Im2 \<i> = 0" | "Im3 \<i> = 0"

primcorec quat_jj :: quat  ("\<j>")
  where "Re \<j> = 0" | "Im1 \<j> = 0" | "Im2 \<j> = 1" | "Im3 \<j> = 0"

primcorec quat_kk :: quat  ("\<k>")
  where "Re \<k> = 0" | "Im1 \<k> = 0" | "Im2 \<k> = 0" | "Im3 \<k> = 1"

end

bundle quaternion_syntax begin
notation quat_ii ("\<i>")
no_notation Complex.imaginary_unit ("\<i>")
end

bundle no_quaternion_syntax begin
no_notation quat_ii ("\<i>")
notation Complex.imaginary_unit ("\<i>")
end

unbundle quaternion_syntax

subsection \<open>Addition and Subtraction: An Abelian Group\<close>

instantiation quat :: ab_group_add
begin

primcorec zero_quat
  where "Re 0 = 0" |"Im1 0 = 0" | "Im2 0 = 0" | "Im3 0 = 0"

primcorec plus_quat
  where
    "Re (x + y) = Re x + Re y"
  | "Im1 (x + y) = Im1 x + Im1 y"
  | "Im2 (x + y) = Im2 x + Im2 y"
  | "Im3 (x + y) = Im3 x + Im3 y"

primcorec uminus_quat
  where
    "Re (- x) = - Re x"
  | "Im1 (- x) = - Im1 x"
  | "Im2 (- x) = - Im2 x"
  | "Im3 (- x) = - Im3 x"

primcorec minus_quat
  where
    "Re (x - y) = Re x - Re y"
  | "Im1 (x - y) = Im1 x - Im1 y"
  | "Im2 (x - y) = Im2 x - Im2 y"
  | "Im3 (x - y) = Im3 x - Im3 y"

instance
  by standard (simp_all add: quat_eq_iff)

end


subsection \<open>A Vector Space\<close>

instantiation quat :: real_vector

begin

primcorec scaleR_quat
  where
    "Re (scaleR r x) = r * Re x"
  | "Im1 (scaleR r x) = r * Im1 x"
  | "Im2 (scaleR r x) = r * Im2 x"
  | "Im3 (scaleR r x) = r * Im3 x"

instance
  by standard (auto simp: quat_eq_iff distrib_left distrib_right  scaleR_add_right)

end

instantiation quat :: real_algebra_1

begin

primcorec one_quat
  where "Re 1 = 1" | "Im1 1 = 0" | "Im2 1 = 0" | "Im3 1 = 0"

primcorec times_quat
  where
    "Re (x * y) = Re x * Re y - Im1 x * Im1 y - Im2 x * Im2 y - Im3 x * Im3 y"
  | "Im1 (x * y) = Re x * Im1 y + Im1 x *  Re y + Im2 x * Im3 y - Im3 x * Im2 y"
  | "Im2 (x * y) = Re x * Im2 y - Im1 x * Im3 y + Im2 x *  Re y + Im3 x * Im1 y"
  | "Im3 (x * y) = Re x * Im3 y + Im1 x * Im2 y - Im2 x * Im1 y + Im3 x *  Re y"

instance
  by standard (auto simp: quat_eq_iff distrib_left distrib_right Rings.right_diff_distrib Rings.left_diff_distrib)

end


subsection \<open>Multiplication and Division: A Real Division Algebra\<close>

instantiation quat :: real_div_algebra
begin

primcorec inverse_quat
  where
    "Re (inverse x) = Re x / ((Re x)\<^sup>2 + (Im1 x)\<^sup>2 + (Im2 x)\<^sup>2 + (Im3 x)\<^sup>2)"
  | "Im1 (inverse x) = - (Im1 x) / ((Re x)\<^sup>2 + (Im1 x)\<^sup>2 + (Im2 x)\<^sup>2 + (Im3 x)\<^sup>2)"
  | "Im2 (inverse x) = - (Im2 x) / ((Re x)\<^sup>2 + (Im1 x)\<^sup>2 + (Im2 x)\<^sup>2 + (Im3 x)\<^sup>2)"
  | "Im3 (inverse x) = - (Im3 x) / ((Re x)\<^sup>2 + (Im1 x)\<^sup>2 + (Im2 x)\<^sup>2 + (Im3 x)\<^sup>2)"

definition "x div y = x * inverse y" for x y :: quat

instance
proof
  show "\<And>x::quat. x \<noteq> 0 \<Longrightarrow> inverse x * x = 1"
    by (auto simp: quat_eq_iff add_nonneg_eq_0_iff
        power2_eq_square add_divide_distrib [symmetric] diff_divide_distrib [symmetric])
  show "\<And>x::quat. x \<noteq> 0 \<Longrightarrow> x * inverse x = 1"
    by (auto simp: quat_eq_iff add_nonneg_eq_0_iff power2_eq_square add_divide_distrib [symmetric])
  show "\<And>x y::quat. x div y = x * inverse y"
    by (simp add: divide_quat_def)
  show "inverse 0 = (0::quat)"
    by (auto simp: quat_eq_iff)
qed

end


subsection \<open>Multiplication and Division: A Real Normed Division Algebra\<close>

fun quat_proj
  where
    "quat_proj x 0 = Re x"
  | "quat_proj x (Suc 0) = Im1 x"
  | "quat_proj x (Suc (Suc 0)) = Im2 x"
  | "quat_proj x (Suc (Suc (Suc 0))) = Im3 x"

lemma quat_proj_add:
  assumes "i \<le> 3"
  shows "quat_proj (x+y) i = quat_proj x i + quat_proj y i"
proof -
  consider "i = 0" | "i = 1" | "i = 2" | "i = 3"
    using assms by linarith
  then show ?thesis
    by cases (auto simp: numeral_2_eq_2 numeral_3_eq_3)
qed

instantiation quat :: real_normed_div_algebra
begin

definition "norm z = sqrt ((Re z)\<^sup>2 + (Im1 z)\<^sup>2 + (Im2 z)\<^sup>2 + (Im3 z)\<^sup>2)"

definition "sgn x = x /\<^sub>R norm x" for x :: quat

definition "dist x y = norm (x - y)" for x y :: quat

definition [code del]:
  "(uniformity :: (quat \<times> quat) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition [code del]:
  "open (U :: quat set) \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

lemma norm_eq_L2: "norm z = L2_set (quat_proj z) {..3}"
  by (simp add: norm_quat_def L2_set_def numeral_3_eq_3)

instance
proof
  fix r :: real and x y :: quat and S :: "quat set"
  show "(norm x = 0) \<longleftrightarrow> (x = 0)"
    by (simp add: norm_quat_def quat_eq_iff add_nonneg_eq_0_iff)
  have eq: "L2_set (quat_proj (x + y)) {..3} = L2_set (\<lambda>i. quat_proj x i + quat_proj y i) {..3}"
    by (rule L2_set_cong) (auto simp: quat_proj_add)
  show "norm (x + y) \<le> norm x + norm y"
    by (simp add: norm_eq_L2 eq L2_set_triangle_ineq)
  show "norm (scaleR r x) = \<bar>r\<bar> * norm x"
    by (simp add: norm_quat_def quat_eq_iff power_mult_distrib distrib_left [symmetric] real_sqrt_mult)
  show "norm (x * y) = norm x * norm y"
    by (simp add: norm_quat_def quat_eq_iff real_sqrt_mult [symmetric]
        power2_eq_square algebra_simps)
qed (rule sgn_quat_def dist_quat_def open_quat_def uniformity_quat_def)+

end


instantiation quat :: real_inner
begin

definition inner_quat_def:
  "inner x y = Re x * Re y + Im1 x * Im1 y + Im2 x * Im2 y + Im3 x * Im3 y"

instance
proof
  fix x y z :: quat and r :: real
  show "inner x y = inner y x"
    unfolding inner_quat_def by (simp add: mult.commute)
  show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_quat_def by (simp add: distrib_right)
  show "inner (scaleR r x) y = r * inner x y"
    unfolding inner_quat_def by (simp add: distrib_left)
  show "0 \<le> inner x x"
    unfolding inner_quat_def by simp
  show "inner x x = 0 \<longleftrightarrow> x = 0"
    unfolding inner_quat_def by (simp add: add_nonneg_eq_0_iff quat_eq_iff)
  show "norm x = sqrt (inner x x)"
    unfolding inner_quat_def norm_quat_def
    by (simp add: power2_eq_square)
qed

end

lemma quat_inner_1 [simp]: "inner 1 x = Re x"
  unfolding inner_quat_def by simp

lemma quat_inner_1_right [simp]: "inner x 1 = Re x"
  unfolding inner_quat_def by simp

lemma quat_inner_i_left [simp]: "inner \<i> x = Im1 x"
  unfolding inner_quat_def by simp

lemma quat_inner_i_right [simp]: "inner x \<i> = Im1 x"
  unfolding inner_quat_def by simp

lemma quat_inner_j_left [simp]: "inner \<j> x = Im2 x"
  unfolding inner_quat_def by simp

lemma quat_inner_j_right [simp]: "inner x \<j> = Im2 x"
  unfolding inner_quat_def by simp

lemma quat_inner_k_left [simp]: "inner \<k> x = Im3 x"
  unfolding inner_quat_def by simp

lemma quat_inner_k_right [simp]: "inner x \<k> = Im3 x"
  unfolding inner_quat_def by simp

abbreviation quat_of_real :: "real \<Rightarrow> quat"
  where "quat_of_real \<equiv> of_real"

lemma Re_quat_of_real [simp]: "Re(quat_of_real a) = a"
  by (simp add: of_real_def)

lemma Im1_quat_of_real [simp]: "Im1(quat_of_real a) = 0"
  by (simp add: of_real_def)

lemma Im2_quat_of_real [simp]: "Im2(quat_of_real a) = 0"
  by (simp add: of_real_def)

lemma Im3_quat_of_real [simp]: "Im3(quat_of_real a) = 0"
  by (simp add: of_real_def)

lemma quat_eq_0_iff: "q = 0 \<longleftrightarrow> (Re q)\<^sup>2 + (Im1 q)\<^sup>2 + (Im2 q)\<^sup>2 + (Im3 q)\<^sup>2 = 0"
proof
  assume "(quat.Re q)\<^sup>2 + (Im1 q)\<^sup>2 + (Im2 q)\<^sup>2 + (Im3 q)\<^sup>2 = 0"
  then have "\<forall>qa. qa - q = qa"
    by (simp add: add_nonneg_eq_0_iff minus_quat.ctr)
  then show "q = 0"
    by simp
qed auto

lemma quat_of_real_times_commute: "quat_of_real r * q = q * of_real r"
  by (simp add: of_real_def)

lemma quat_of_real_times_left_commute: "quat_of_real r * (p * q) = p * (of_real r * q)"
  by (simp add: of_real_def)

lemma quat_norm_units [simp]: "norm quat_ii = 1" "norm (\<j>::quat) = 1" "norm (\<k>::quat) = 1"
  by (auto simp: norm_quat_def)

lemma ii_nz [simp]: "quat_ii \<noteq> 0"
  using quat_ii.simps(2) by fastforce

lemma jj_nz [simp]: "\<j> \<noteq> 0"
  using quat_jj.sel(3) by fastforce

lemma kk_nz [simp]: "\<k> \<noteq> 0"
  using quat_kk.sel(4) by force

text\<open>An "expansion" theorem into the traditional notation\<close>

lemma quat_unfold:
   "q = of_real(Re q) + \<i> * of_real(Im1 q) + \<j> * of_real(Im2 q) + \<k> * of_real(Im3 q)"
  by (simp add: quat_eq_iff)

lemma quat_trad: "Quat x y z w = of_real x + \<i> * of_real y + \<j> * of_real z + \<k> * of_real w"
  by (simp add: quat_eq_iff)

lemma of_real_eq_Quat: "of_real a = Quat a 0 0 0"
  by (simp add: quat_trad)

lemma ii_squared [simp]: "quat_ii\<^sup>2 = -1"
  by (simp add: power2_eq_square quat.expand)

lemma jj_squared [simp]: "\<j>^2 = -1"
  by (simp add: power2_eq_square quat.expand)

lemma kk_squared [simp]: "\<k>^2 = -1"
  by (simp add: power2_eq_square quat.expand)

lemma inverse_ii [simp]: "inverse quat_ii = -quat_ii"
  by (simp add: power2_eq_square quat.expand)

lemma inverse_jj [simp]: "inverse \<j> = -\<j>"
  by (simp add: power2_eq_square quat.expand)

lemma inverse_kk [simp]: "inverse \<k> = -\<k>"
  by (simp add: power2_eq_square quat.expand)

lemma inverse_mult: "inverse (p * q) = inverse q * inverse p" for p::quat
  by (metis inverse_zero mult_not_zero nonzero_inverse_mult_distrib)

lemma quat_of_real_inverse_collapse [simp]:
  assumes "c \<noteq> 0"
  shows "quat_of_real c * quat_of_real (inverse c) = 1" "quat_of_real (inverse c) * quat_of_real c = 1"
  using assms by auto

subsection\<open>Conjugate of a quaternion\<close>

primcorec cnj :: "quat \<Rightarrow> quat"
  where
    "Re (cnj z) = Re z"
  | "Im1 (cnj z) = - Im1 z"
  | "Im2 (cnj z) = - Im2 z"
  | "Im3 (cnj z) = - Im3 z"


lemma cnj_cancel_iff [simp]: "cnj x = cnj y \<longleftrightarrow> x = y"
proof
  show "cnj x = cnj y \<Longrightarrow> x = y"
    by (simp add: quat_eq_iff)
qed auto

lemma cnj_cnj [simp]:
   "cnj(cnj q) = q"
  by (simp add: quat_eq_iff)

lemma cnj_of_real [simp]: "cnj(quat_of_real x) = quat_of_real x"
  by (simp add: quat_eqI)

lemma cnj_zero [simp]: "cnj 0 = 0"
  by (simp add: quat_eq_iff)

lemma cnj_zero_iff [iff]: "cnj z = 0 \<longleftrightarrow> z = 0"
  by (simp add: quat_eq_iff)

lemma cnj_one [simp]: "cnj 1 = 1"
  by (simp add: quat_eq_iff)

lemma cnj_one_iff [simp]: "cnj z = 1 \<longleftrightarrow> z = 1"
  by (simp add: quat_eq_iff)

lemma quat_norm_cnj [simp]: "norm(cnj q) = norm q"
  by (simp add: norm_quat_def)

lemma cnj_add [simp]: "cnj (x + y) = cnj x + cnj y"
  by (simp add: quat_eq_iff)

lemma cnj_sum [simp]: "cnj (sum f S) = (\<Sum>x\<in>S. cnj (f x))"
  by (induct S rule: infinite_finite_induct) auto

lemma cnj_diff [simp]: "cnj (x - y) = cnj x - cnj y"
  by (simp add: quat_eq_iff)

lemma cnj_minus [simp]: "cnj (- x) = - cnj x"
  by (simp add: quat_eq_iff)

lemma cnj_mult [simp]: "cnj (x * y) = cnj y * cnj x"
  by (simp add: quat_eq_iff)

lemma cnj_inverse [simp]: "cnj (inverse x) = inverse (cnj x)"
  by (simp add: quat_eq_iff)

lemma cnj_divide [simp]: "cnj (x / y) = inverse (cnj y) * cnj x"
  by (simp add: divide_quat_def)

lemma cnj_power [simp]: "cnj (x^n) = cnj x ^ n"
  by (induct n) (auto simp: power_commutes)

lemma cnj_of_nat [simp]: "cnj (of_nat n) = of_nat n"
  by (metis cnj_of_real of_real_of_nat_eq)

lemma cnj_of_int [simp]: "cnj (of_int z) = of_int z"
  by (metis cnj_of_real of_real_of_int_eq)

lemma cnj_numeral [simp]: "cnj (numeral w) = numeral w"
  by (metis of_nat_numeral cnj_of_nat)

lemma cnj_neg_numeral [simp]: "cnj (- numeral w) = - numeral w"
  by simp

lemma cnj_scaleR [simp]: "cnj (scaleR r x) = scaleR r (cnj x)"
  by (simp add: quat_eq_iff)

lemma cnj_units [simp]: "cnj quat_ii = -\<i>" "cnj \<j> = -\<j>" "cnj \<k> = -\<k>"
  by (simp_all add: quat_eq_iff)

lemma cnj_eq_of_real: "cnj q = quat_of_real x \<longleftrightarrow> q = quat_of_real x"
proof
  show "cnj q = quat_of_real x \<Longrightarrow> q = quat_of_real x"
    by (metis cnj_of_real cnj_cnj)
qed auto

lemma quat_add_cnj: "q + cnj q = quat_of_real(2 * Re q)" "cnj q + q = quat_of_real(2 * Re q)"
  by simp_all (simp_all add: mult.commute mult_2 plus_quat.code)

lemma quat_divide_numeral:
  fixes x::quat shows "x / numeral w = x /\<^sub>R numeral w"
  unfolding divide_quat_def
  by (metis mult.right_neutral mult_scaleR_right of_real_def of_real_inverse of_real_numeral)

lemma Re_divide_numeral [simp]: "Re (x / numeral w) = Re x / numeral w"
  by (metis divide_inverse_commute quat_divide_numeral scaleR_quat.simps(1))

lemma Im1_divide_numeral [simp]: "Im1 (x / numeral w) = Im1 x / numeral w"
  unfolding quat_divide_numeral by simp

lemma Im2_divide_numeral [simp]: "Im2 (x / numeral w) = Im2 x / numeral w"
  unfolding quat_divide_numeral by simp

lemma Im3_divide_numeral [simp]: "Im3 (x / numeral w) = Im3 x / numeral w"
  unfolding quat_divide_numeral by simp


lemma of_real_quat_re_cnj: "quat_of_real(Re q) = inverse(quat_of_real 2) * (q + cnj q)"
  by (simp add: quat_eq_iff)

lemma quat_mult_cnj_commute: "cnj q * q = q * cnj q"
  by (simp add: quat_eq_iff)

lemma quat_norm_pow_2: "quat_of_real(norm q) ^ 2 = q * cnj q"
  by (simp add: quat_eq_iff norm_quat_def flip: of_real_power) (auto simp: power2_eq_square)

lemma quat_norm_pow_2_alt: "quat_of_real(norm q) ^ 2 = cnj q * q"
  by (simp add: quat_mult_cnj_commute quat_norm_pow_2)

lemma quat_inverse_cnj: "inverse q = inverse (quat_of_real((norm q)\<^sup>2)) * cnj q"
  by (simp add: quat_eq_iff norm_quat_def numeral_Bit0 flip: of_real_power)

lemma quat_inverse_eq_cnj: "norm q = 1 \<Longrightarrow> inverse q = cnj q"
  by (metis inverse_1 mult_cancel_left norm_eq_zero norm_one cnj_one quat_norm_pow_2 right_inverse)

subsection\<open>Linearity and continuity of the components\<close>

lemma bounded_linear_Re: "bounded_linear Re"
  and bounded_linear_Im1: "bounded_linear Im1"
  and bounded_linear_Im2: "bounded_linear Im2"
  and bounded_linear_Im3: "bounded_linear Im3"
  by (simp_all add: bounded_linear_intro [where K=1] norm_quat_def real_le_rsqrt add.assoc)

lemmas Cauchy_Re = bounded_linear.Cauchy [OF bounded_linear_Re]
lemmas Cauchy_Im1 = bounded_linear.Cauchy [OF bounded_linear_Im1]
lemmas Cauchy_Im2 = bounded_linear.Cauchy [OF bounded_linear_Im2]
lemmas Cauchy_Im3 = bounded_linear.Cauchy [OF bounded_linear_Im3]
lemmas tendsto_Re [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Re]
lemmas tendsto_Im1 [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Im1]
lemmas tendsto_Im2 [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Im2]
lemmas tendsto_Im3 [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Im3]
lemmas isCont_Re [simp] = bounded_linear.isCont [OF bounded_linear_Re]
lemmas isCont_Im1 [simp] = bounded_linear.isCont [OF bounded_linear_Im1]
lemmas isCont_Im2 [simp] = bounded_linear.isCont [OF bounded_linear_Im2]
lemmas isCont_Im3 [simp] = bounded_linear.isCont [OF bounded_linear_Im3]
lemmas continuous_Re [simp] = bounded_linear.continuous [OF bounded_linear_Re]
lemmas continuous_Im1 [simp] = bounded_linear.continuous [OF bounded_linear_Im1]
lemmas continuous_Im2 [simp] = bounded_linear.continuous [OF bounded_linear_Im2]
lemmas continuous_Im3 [simp] = bounded_linear.continuous [OF bounded_linear_Im3]
lemmas continuous_on_Re [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Re]
lemmas continuous_on_Im1 [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Im1]
lemmas continuous_on_Im2 [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Im2]
lemmas continuous_on_Im3 [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Im3]
lemmas has_derivative_Re [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Re]
lemmas has_derivative_Im1 [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Im1]
lemmas has_derivative_Im2 [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Im2]
lemmas has_derivative_Im3 [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Im3]
lemmas sums_Re = bounded_linear.sums [OF bounded_linear_Re]
lemmas sums_Im1 = bounded_linear.sums [OF bounded_linear_Im1]
lemmas sums_Im2 = bounded_linear.sums [OF bounded_linear_Im2]
lemmas sums_Im3 = bounded_linear.sums [OF bounded_linear_Im3]


subsection\<open>Quaternionic-specific theorems about sums\<close>

lemma Re_sum [simp]: "Re(sum f S) = sum (\<lambda>x.  Re(f x)) S" for f :: "'a \<Rightarrow> quat"
  by (induct S rule: infinite_finite_induct) auto

lemma Im1_sum [simp]: "Im1(sum f S) = sum (\<lambda>x. Im1(f x)) S"
  by (induct S rule: infinite_finite_induct) auto

lemma Im2_sum [simp]: "Im2(sum f S) = sum (\<lambda>x. Im2(f x)) S"
  by (induct S rule: infinite_finite_induct) auto

lemma Im3_sum [simp]: "Im3(sum f S) = sum (\<lambda>x. Im3(f x)) S"
  by (induct S rule: infinite_finite_induct) auto

lemma in_Reals_iff_Re: "q \<in> Reals \<longleftrightarrow> quat_of_real(Re q) = q"
  by (metis Re_quat_of_real Reals_cases Reals_of_real)

lemma in_Reals_iff_cnj: "q \<in> Reals \<longleftrightarrow> cnj q = q"
  by (simp add: in_Reals_iff_Re quat_eq_iff)

lemma real_norm: "q \<in> Reals \<Longrightarrow> norm q = abs(Re q)"
  by (metis in_Reals_iff_Re norm_of_real)


lemma norm_power2: "(norm q)\<^sup>2 = Re(cnj q * q)"
  by (metis Re_quat_of_real of_real_power quat_mult_cnj_commute quat_norm_pow_2)

lemma quat_norm_imaginary: "Re x = 0 \<Longrightarrow> x\<^sup>2 = - (quat_of_real (norm x))\<^sup>2"
  unfolding quat_norm_pow_2
  by (cases x) (auto simp: power2_eq_square cnj.ctr times_quat.ctr uminus_quat.ctr)


subsection\<open>Bound results for real and imaginary components of limits\<close>

lemma Re_tendsto_upperbound:
   "\<lbrakk>(f \<longlongrightarrow> l) net; \<forall>\<^sub>F x in net. quat.Re (f x) \<le> b; net \<noteq> bot\<rbrakk> \<Longrightarrow> Re l \<le> b"
  by (blast intro: tendsto_upperbound [OF tendsto_Re])

lemma Im1_tendsto_upperbound:
   "\<lbrakk>(f \<longlongrightarrow> l) net; \<forall>\<^sub>F x in net. Im1 (f x) \<le> b; net \<noteq> bot\<rbrakk> \<Longrightarrow> Im1 l \<le> b"
  by (blast intro: tendsto_upperbound [OF tendsto_Im1])

lemma Im2_tendsto_upperbound:
   "\<lbrakk>(f \<longlongrightarrow> l) net; \<forall>\<^sub>F x in net. Im2 (f x) \<le> b; net \<noteq> bot\<rbrakk> \<Longrightarrow> Im2 l \<le> b"
  by (blast intro: tendsto_upperbound [OF tendsto_Im2])

lemma Im3_tendsto_upperbound:
   "\<lbrakk>(f \<longlongrightarrow> l) net; \<forall>\<^sub>F x in net. Im3 (f x) \<le> b; net \<noteq> bot\<rbrakk> \<Longrightarrow> Im3 l \<le> b"
  by (blast intro: tendsto_upperbound [OF tendsto_Im3])

lemma Re_tendsto_lowerbound:
   "\<lbrakk>(f \<longlongrightarrow> l) net; \<forall>\<^sub>F x in net. b \<le> quat.Re (f x); net \<noteq> bot\<rbrakk> \<Longrightarrow> b \<le> Re l"
  by (blast intro: tendsto_lowerbound [OF tendsto_Re])

lemma Im1_tendsto_lowerbound:
   "\<lbrakk>(f \<longlongrightarrow> l) net; \<forall>\<^sub>F x in net. b \<le> Im1 (f x); net \<noteq> bot\<rbrakk> \<Longrightarrow> b \<le> Im1 l"
  by (blast intro: tendsto_lowerbound [OF tendsto_Im1])

lemma Im2_tendsto_lowerbound:
   "\<lbrakk>(f \<longlongrightarrow> l) net; \<forall>\<^sub>F x in net. b \<le> Im2 (f x); net \<noteq> bot\<rbrakk> \<Longrightarrow> b \<le> Im2 l"
  by (blast intro: tendsto_lowerbound [OF tendsto_Im2])

lemma Im3_tendsto_lowerbound:
   "\<lbrakk>(f \<longlongrightarrow> l) net; \<forall>\<^sub>F x in net. b \<le> Im3 (f x); net \<noteq> bot\<rbrakk> \<Longrightarrow> b \<le> Im3 l"
  by (blast intro: tendsto_lowerbound [OF tendsto_Im3])

lemma of_real_continuous_iff: "continuous net (\<lambda>x. quat_of_real(f x)) \<longleftrightarrow> continuous net f"
  by (simp add: continuous_def tendsto_iff)

lemma of_real_continuous_on_iff:
   "continuous_on S (\<lambda>x. quat_of_real(f x)) \<longleftrightarrow> continuous_on S f"
  using continuous_on_Re continuous_on_of_real by fastforce

subsection\<open>Quaternions for describing 3D isometries\<close>

subsubsection\<open>The \<open>HIm\<close> operator\<close>

definition HIm :: "quat \<Rightarrow> real^3" where
  "HIm q \<equiv> vector[Im1 q, Im2 q, Im3 q]"

lemma HIm_Quat: "HIm (Quat w x y z) = vector[x,y,z]"
  by (simp add: HIm_def)

lemma him_eq: "HIm p = HIm q \<longleftrightarrow> Im1 p = Im1 q \<and> Im2 p = Im2 q \<and> Im3 p = Im3 q"
  by (metis HIm_def vector_3)

lemma him_of_real [simp]: "HIm(of_real a) = 0"
  by (simp add: of_real_eq_Quat HIm_Quat vec_eq_iff vector_def)

lemma him_0 [simp]: "HIm 0 = 0"
  by (metis him_of_real of_real_0)

lemma him_1 [simp]: "HIm 1 = 0"
  by (metis him_of_real of_real_1)

lemma him_cnj: "HIm(cnj q) = - HIm q"
  by (simp add: HIm_def vec_eq_iff vector_def)

lemma him_mult_left [simp]: "HIm(of_real a * q) = a *\<^sub>R HIm q"
  by (simp add: HIm_def vec_eq_iff vector_def)

lemma him_mult_right [simp]: "HIm(q * of_real a) = a *\<^sub>R HIm q"
  by (simp add: HIm_def vec_eq_iff vector_def)

lemma him_add [simp]: "HIm(p + q) = HIm p + HIm q"
  by (simp add: HIm_def vec_eq_iff vector_def)

lemma him_minus [simp]: "HIm(-q) = - HIm q"
  by (simp add: HIm_def vec_eq_iff vector_def)

lemma him_diff [simp]: "HIm(p - q) = HIm p - HIm q"
  by (simp add: HIm_def vec_eq_iff vector_def)

lemma him_sum [simp]: "HIm (sum f S) = (\<Sum>x\<in>S. HIm (f x))"
  by (induct S rule: infinite_finite_induct) auto

lemma linear_him: "linear HIm"
  by (metis him_add him_mult_right linearI mult.right_neutral mult_scaleR_right of_real_def)

subsubsection\<open>The \<open>Hv\<close> operator\<close>

definition Hv :: "real^3 \<Rightarrow> quat" where
  "Hv v \<equiv> Quat 0 (v$1) (v$2) (v$3)"

lemma Re_Hv [simp]: "Re(Hv v) = 0"
  by (simp add: Hv_def)

lemma Im1_Hv [simp]: "Im1(Hv v) = v$1"
  by (simp add: Hv_def)

lemma Im2_Hv [simp]: "Im2(Hv v) = v$2"
  by (simp add: Hv_def)

lemma Im3_Hv [simp]: "Im3(Hv v) = v$3"
  by (simp add: Hv_def)

lemma hv_vec: "Hv(vec r) = Quat 0 r r r"
  by (simp add: Hv_def)

lemma hv_eq_zero [simp]: "Hv v = 0 \<longleftrightarrow> v = 0"
  by (simp add: quat_eq_iff vec_eq_iff) (metis exhaust_3)

lemma hv_zero [simp]: "Hv 0 = 0"
  by simp

lemma hv_vector [simp]: "Hv(vector[x,y,z]) = Quat 0 x y z"
  by (simp add: Hv_def)

lemma hv_basis: "Hv(axis 1 1) = \<i>" "Hv(axis 2 1) = \<j>" "Hv(axis 3 1) = \<k>"
  by (auto simp: Hv_def axis_def quat_ii.code quat_jj.code quat_kk.code)

lemma hv_add [simp]: "Hv(x + y) = Hv x + Hv y"
  by (simp add: Hv_def quat_eq_iff)

lemma hv_minus [simp]: "Hv(-x) = -Hv x"
  by (simp add: Hv_def quat_eq_iff)

lemma hv_diff [simp]: "Hv(x - y) = Hv x - Hv y"
  by (simp add: Hv_def quat_eq_iff)

lemma hv_cmult [simp]: "Hv(a *\<^sub>R x) = of_real a * Hv x"
  by (simp add: Hv_def quat_eq_iff)

lemma hv_sum [simp]: "Hv (sum f S) = (\<Sum>x\<in>S. Hv (f x))"
  by (induct S rule: infinite_finite_induct) auto

lemma hv_inj: "Hv x = Hv y \<longleftrightarrow> x = y"
  by (simp add: Hv_def quat_eq_iff vec_eq_iff) (metis (full_types) exhaust_3)

lemma linear_hv: "linear Hv"
  by unfold_locales (auto simp: of_real_def)

lemma him_hv [simp]: "HIm(Hv x) = x"
  using HIm_def hv_inj quat_eq_iff by fastforce

lemma cnj_hv [simp]: "cnj(Hv v) = -Hv v"
  using Hv_def cnj.code hv_minus by auto

lemma hv_him: "Hv(HIm q) = Quat 0 (Im1 q) (Im2 q) (Im3 q)"
  by (simp add: HIm_def)

lemma hv_him_eq: "Hv(HIm q) = q \<longleftrightarrow> Re q = 0"
  by (simp add: hv_him quat_eq_iff)

lemma dot_hv [simp]: "Hv u \<bullet> Hv v = u \<bullet> v"
  by (simp add: Hv_def inner_quat_def inner_vec_def sum_3)

lemma norm_hv [simp]: "norm (Hv v) = norm v"
  by (simp add: norm_eq)

subsection\<open>Geometric interpretation of the product of imaginary quaternions\<close>

context includes cross3_syntax
begin

lemma mult_hv_eq_cross_dot: "Hv x * Hv y = Hv(x \<times> y) - of_real (x \<bullet> y)"
  by (simp add: quat_eq_iff cross3_simps)

text\<open>Representing orthogonal transformations as conjugation or congruence with a quaternion\<close>

lemma orthogonal_transformation_quat_congruence:
  assumes "norm q = 1"
  shows "orthogonal_transformation (\<lambda>x. HIm(cnj q * Hv x * q))"
proof -
  have nq: "(quat.Re q)\<^sup>2 + (Im1 q)\<^sup>2 + (Im2 q)\<^sup>2 + (Im3 q)\<^sup>2 = 1"
    using assms norm_quat_def by auto
  have "Vector_Spaces.linear (*\<^sub>R) (*\<^sub>R) (\<lambda>x. HIm (cnj q * Hv x * q))"
  proof
    show "\<And>r b. HIm (cnj q * Hv (r *\<^sub>R b) * q) = r *\<^sub>R HIm (cnj q * Hv b * q)"
      by (metis him_mult_left hv_cmult mult_scaleR_left mult_scaleR_right scaleR_conv_of_real)
  qed (simp add: distrib_left distrib_right)
  moreover have "HIm (cnj q * Hv v * q) \<bullet> HIm (cnj q * Hv w * q) = ((quat.Re q)\<^sup>2 + (Im1 q)\<^sup>2 + (Im2 q)\<^sup>2 + (Im3 q)\<^sup>2)\<^sup>2 * (v \<bullet> w)" for v w
    by (simp add: HIm_def inner_vec_def sum_3 power2_eq_square algebra_simps) (*SLOW, like 15s*)
  ultimately show ?thesis
    by (simp add: orthogonal_transformation_def linear_def nq)
qed

lemma orthogonal_transformation_quat_conjugation:
  assumes "q \<noteq> 0"
  shows "orthogonal_transformation (\<lambda>x. HIm(inverse q * Hv x * q))"
proof -
  obtain c p where eq: "q = of_real c * p" and 1: "norm p = 1"
  proof
    show "q = quat_of_real (norm q) * (inverse (of_real (norm q)) * q)"
      by (metis assms mult.assoc mult.left_neutral norm_eq_zero of_real_eq_0_iff right_inverse)
    show "norm (inverse (quat_of_real (norm q)) * q) = 1"
      using assms by (simp add: norm_mult norm_inverse)
  qed
  have "c \<noteq> 0"
    using assms eq by auto
  then have "HIm (cnj p * Hv x * p) = HIm (inverse (quat_of_real c * p) * Hv x * (quat_of_real c * p))" for x
    apply (simp add: inverse_mult mult.assoc flip: quat_inverse_eq_cnj [OF 1] of_real_inverse)
    using quat_of_real_times_commute quat_of_real_times_left_commute quat_of_real_inverse_collapse
    by (simp add: of_real_def)
  then show ?thesis
    using orthogonal_transformation_quat_congruence [OF 1]
    by (simp add: eq)
qed

unbundle no_quaternion_syntax

end

end
