(*
  File:    Angles.thy
  Author:  Manuel Eberl <eberlm@in.tum.de>

  Definition of angles between vectors and between three points.
*)

section \<open>Definition of angles\<close>
theory Angles
imports
  "HOL-Analysis.Analysis"
begin

lemma collinear_translate_iff: "collinear (((+) a) ` A) \<longleftrightarrow> collinear A"
  by (auto simp: collinear_def)


definition vangle where
  "vangle u v = (if u = 0 \<or> v = 0 then pi / 2 else arccos (u \<bullet> v / (norm u * norm v)))"

definition angle where
  "angle a b c = vangle (a - b) (c - b)"

lemma angle_altdef: "angle a b c = arccos ((a - b) \<bullet> (c - b) / (dist a b * dist c b))"
  by (simp add: angle_def vangle_def dist_norm)

lemma vangle_0_left [simp]: "vangle 0 v = pi / 2"
  and vangle_0_right [simp]: "vangle u 0 = pi / 2"
  by (simp_all add: vangle_def)

lemma vangle_refl [simp]: "u \<noteq> 0 \<Longrightarrow> vangle u u = 0"
  by (simp add: vangle_def dot_square_norm power2_eq_square)

lemma angle_refl [simp]: "angle a a b = pi / 2" "angle a b b = pi / 2"
  by (simp_all add: angle_def)

lemma angle_refl_mid [simp]: "a \<noteq> b \<Longrightarrow> angle a b a = 0"
  by (simp add: angle_def)


lemma cos_vangle: "cos (vangle u v) = u \<bullet> v / (norm u * norm v)"
  unfolding vangle_def using Cauchy_Schwarz_ineq2[of u v] by (auto simp: field_simps)

lemma cos_angle: "cos (angle a b c) = (a - b) \<bullet> (c - b) / (dist a b * dist c b)"
  by (simp add: angle_def cos_vangle dist_norm)

lemma inner_conv_angle: "(a - b) \<bullet> (c - b) = dist a b * dist c b * cos (angle a b c)"
  by (simp add: cos_angle)

lemma vangle_commute: "vangle u v = vangle v u"
  by (simp add: vangle_def inner_commute mult.commute)

lemma angle_commute: "angle a b c = angle c b a"
  by (simp add: angle_def vangle_commute)

lemma vangle_nonneg: "vangle u v \<ge> 0" and vangle_le_pi: "vangle u v \<le> pi"
  using Cauchy_Schwarz_ineq2[of u v]
  by (auto simp: vangle_def field_simps intro!: arccos_lbound arccos_ubound)

lemmas vangle_bounds = vangle_nonneg vangle_le_pi

lemma angle_nonneg: "angle a b c \<ge> 0" and angle_le_pi: "angle a b c \<le> pi"
  using vangle_bounds unfolding angle_def by blast+

lemmas angle_bounds = angle_nonneg angle_le_pi

lemma sin_vangle_nonneg: "sin (vangle u v) \<ge> 0"
  using vangle_bounds by (rule sin_ge_zero)

lemma sin_angle_nonneg: "sin (angle a b c) \<ge> 0"
  using angle_bounds by (rule sin_ge_zero)


lemma vangle_eq_0D:
  assumes "vangle u v = 0"
  shows   "norm u *\<^sub>R v = norm v *\<^sub>R u"
proof -
  from assms have "u \<bullet> v = norm u * norm v"
    using arccos_eq_iff[of "(u \<bullet> v) / (norm u * norm v)" 1] Cauchy_Schwarz_ineq2[of u v]
    by (fastforce simp: vangle_def split: if_split_asm)
  thus ?thesis by (subst (asm) norm_cauchy_schwarz_eq) simp_all
qed

lemma vangle_eq_piD:
  assumes "vangle u v = pi"
  shows   "norm u *\<^sub>R v + norm v *\<^sub>R u = 0"
proof -
  from assms have "(-u) \<bullet> v = norm (-u) * norm v"
    using arccos_eq_iff[of "(u \<bullet> v) / (norm u * norm v)" "-1"] Cauchy_Schwarz_ineq2[of u v]
    by (simp add: field_simps vangle_def split: if_split_asm)
  thus ?thesis by (subst (asm) norm_cauchy_schwarz_eq) simp_all
qed

lemma dist_triangle_eq:
  fixes a b c :: "'a :: real_inner"
  shows "(dist a c = dist a b + dist b c) \<longleftrightarrow> dist a b *\<^sub>R (c - b) + dist b c *\<^sub>R (a - b) = 0"
  using norm_triangle_eq[of "b - a" "c - b"]
  by (simp add: dist_norm norm_minus_commute algebra_simps)

lemma angle_eq_pi_imp_dist_additive:
  assumes "angle a b c = pi"
  shows   "dist a c = dist a b + dist b c"
  using vangle_eq_piD[OF assms[unfolded angle_def]]
  by (subst dist_triangle_eq) (simp add: dist_norm norm_minus_commute)


lemma orthogonal_iff_vangle: "orthogonal u v \<longleftrightarrow> vangle u v = pi / 2"
  using arccos_eq_iff[of "u \<bullet> v / (norm u * norm v)" 0] Cauchy_Schwarz_ineq2[of u v]
  by (auto simp: vangle_def orthogonal_def)

lemma cos_minus1_imp_pi:
  assumes "cos x = -1" "x \<ge> 0" "x < 3 * pi"
  shows   "x = pi"
proof -
  have "cos (x - pi) = 1" by (simp add: assms)
  then obtain n :: int where n: "of_int n = (x / pi - 1) / 2"
    by (subst (asm) cos_one_2pi_int) (auto simp: field_simps)
  also from assms have "\<dots> \<in> {-1<..<1}" by (auto simp: field_simps)
  finally have "n = 0" by simp
  with n show ?thesis by simp
qed


lemma vangle_eqI:
  assumes "u \<noteq> 0" "v \<noteq> 0" "w \<noteq> 0" "x \<noteq> 0"
  assumes "(u \<bullet> v) * norm w * norm x = (w \<bullet> x) * norm u * norm v"
  shows   "vangle u v = vangle w x"
  using assms Cauchy_Schwarz_ineq2[of u v] Cauchy_Schwarz_ineq2[of w x]
  unfolding vangle_def by (auto simp: arccos_eq_iff field_simps)

lemma angle_eqI:
  assumes "a \<noteq> b" "a \<noteq> c" "d \<noteq> e" "d \<noteq> f"
  assumes "((b-a) \<bullet> (c-a)) * dist d e * dist d f = ((e-d) \<bullet> (f-d)) * dist a b * dist a c"
  shows   "angle b a c = angle e d f"
  using assms unfolding angle_def
  by (intro vangle_eqI) (simp_all add: dist_norm norm_minus_commute)

lemma cos_vangle_eqD: "cos (vangle u v) = cos (vangle w x) \<Longrightarrow> vangle u v = vangle w x"
  by (rule cos_inj_pi) (simp_all add: vangle_bounds)

lemma cos_angle_eqD: "cos (angle a b c) = cos (angle d e f) \<Longrightarrow> angle a b c = angle d e f"
  unfolding angle_def by (rule cos_vangle_eqD)

lemma sin_vangle_zero_iff: "sin (vangle u v) = 0 \<longleftrightarrow> vangle u v \<in> {0, pi}"
proof
  assume "sin (vangle u v) = 0"
  then obtain n :: int where n: "of_int n = vangle u v / pi"
    by (subst (asm) sin_zero_iff_int2) auto
  also have "\<dots> \<in> {0..1}" using vangle_bounds by (auto simp: field_simps)
  finally have "n \<in> {0,1}" by auto
  thus "vangle u v \<in> {0,pi}" using n by (auto simp: field_simps)
qed auto

lemma sin_angle_zero_iff: "sin (angle a b c) = 0 \<longleftrightarrow> angle a b c \<in> {0, pi}"
  unfolding angle_def by (simp only: sin_vangle_zero_iff)

lemma vangle_collinear: "vangle u v \<in> {0, pi} \<Longrightarrow> collinear {0, u, v}"
apply (subst norm_cauchy_schwarz_equal [symmetric])
apply (subst norm_cauchy_schwarz_abs_eq)
apply (auto dest!: vangle_eq_0D vangle_eq_piD simp: eq_neg_iff_add_eq_0)
done

lemma angle_collinear: "angle a b c \<in> {0, pi} \<Longrightarrow> collinear {a, b, c}"
apply (unfold angle_def, drule vangle_collinear)
apply (subst collinear_translate_iff[symmetric, of _ "-b"])
apply (auto simp: insert_commute)
done

lemma not_collinear_vangle: "\<not>collinear {0,u,v} \<Longrightarrow> vangle u v \<in> {0<..<pi}"
  using vangle_bounds[of u v] vangle_collinear[of u v]
  by (cases "vangle u v = 0 \<or> vangle u v = pi") auto

lemma not_collinear_angle: "\<not>collinear {a,b,c} \<Longrightarrow> angle a b c \<in> {0<..<pi}"
  using angle_bounds[of a b c] angle_collinear[of a b c]
  by (cases "angle a b c = 0 \<or> angle a b c = pi") auto

subsection\<open>Contributions from Lukas Bulwahn\<close>

lemma vangle_scales:
  assumes "0 < c"
  shows "vangle (c *\<^sub>R v\<^sub>1) v\<^sub>2 = vangle v\<^sub>1 v\<^sub>2"
using assms unfolding vangle_def by auto

lemma vangle_inverse:
  "vangle (- v\<^sub>1) v\<^sub>2 = pi - vangle v\<^sub>1 v\<^sub>2"
proof -
  have "\<bar>v\<^sub>1 \<bullet> v\<^sub>2 / (norm v\<^sub>1 * norm v\<^sub>2)\<bar> \<le> 1"
  proof cases
    assume "v\<^sub>1 \<noteq> 0 \<and> v\<^sub>2 \<noteq> 0"
    from this show ?thesis by (simp add: Cauchy_Schwarz_ineq2)
  next
    assume "\<not> (v\<^sub>1 \<noteq> 0 \<and> v\<^sub>2 \<noteq> 0)"
    from this show ?thesis by auto
  qed
  from this show ?thesis
    unfolding vangle_def
    by (simp add: arccos_minus_abs)
qed

lemma orthogonal_iff_angle:
  shows "orthogonal (A - B) (C - B) \<longleftrightarrow> angle A B C = pi / 2"
unfolding angle_def by (auto simp only: orthogonal_iff_vangle)

lemma angle_inverse:
  assumes "between (A, C) B"
  assumes "A \<noteq> B" "B \<noteq> C"
  shows "angle A B D = pi - angle C B D"
proof -
  from \<open>between (A, C) B\<close> obtain u where u: "u \<ge> 0" "u \<le> 1"
    and X: "B = u *\<^sub>R A + (1 - u) *\<^sub>R C"
    by (metis add.commute betweenE between_commute)
  from \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> X have "u \<noteq> 0" "u \<noteq> 1" by auto
  have "0 < ((1 - u) / u)"
    using \<open>u \<noteq> 0\<close> \<open>u \<noteq> 1\<close> \<open>u \<ge> 0\<close> \<open>u \<le> 1\<close> by simp
  from X have "A - B = - (1 - u) *\<^sub>R (C - A)"
    by (simp add: real_vector.scale_right_diff_distrib real_vector.scale_left_diff_distrib)
  moreover from X have "C - B = u *\<^sub>R (C - A)"
    by (simp add: scaleR_diff_left real_vector.scale_right_diff_distrib)
  ultimately have "A - B = - (((1 - u) / u) *\<^sub>R (C - B))"
    using \<open>u \<noteq> 0\<close> by simp (metis minus_diff_eq real_vector.scale_minus_left)
  from this have "vangle (A - B) (D - B) = pi - vangle (C - B) (D - B)"
    using \<open>0 < (1 - u) / u\<close> by (simp add: vangle_inverse vangle_scales)
  from this show ?thesis
    unfolding angle_def by simp
qed

lemma strictly_between_implies_angle_eq_pi:
  assumes "between (A, C) B"
  assumes "A \<noteq> B" "B \<noteq> C"
  shows "angle A B C = pi"
proof -
  from \<open>between (A, C) B\<close> obtain u where u: "u \<ge> 0" "u \<le> 1"
    and X: "B = u *\<^sub>R A + (1 - u) *\<^sub>R C"
    by (metis add.commute betweenE between_commute)
  from \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> X have "u \<noteq> 0" "u \<noteq> 1" by auto
  from \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> \<open>between (A, C) B\<close> have "A \<noteq> C" by auto
  from X have "A - B = - (1 - u) *\<^sub>R (C - A)"
    by (simp add: real_vector.scale_right_diff_distrib real_vector.scale_left_diff_distrib)
  moreover from this have "dist A B = norm ((1 - u) *\<^sub>R (C - A))"
    using \<open>u \<ge> 0\<close> \<open>u \<le> 1\<close> by (simp add: dist_norm)
  moreover from X have "C - B = u *\<^sub>R (C - A)"
    by (simp add: scaleR_diff_left real_vector.scale_right_diff_distrib)
  moreover from this have "dist C B = norm (u *\<^sub>R (C - A))"
    by (simp add: dist_norm)
  ultimately have "(A - B) \<bullet> (C - B) / (dist A B * dist C B) = u * (u - 1) / (\<bar>1 - u\<bar> * \<bar>u\<bar>)"
    using \<open>A \<noteq> C\<close> by (simp add: dot_square_norm power2_eq_square)
  also have "\<dots> = - 1"
    using \<open>u \<noteq> 0\<close> \<open>u \<noteq> 1\<close> \<open>u \<ge> 0\<close> \<open>u \<le> 1\<close> by (simp add: divide_eq_minus_1_iff)
  finally show ?thesis
    unfolding angle_altdef by simp
qed

end
