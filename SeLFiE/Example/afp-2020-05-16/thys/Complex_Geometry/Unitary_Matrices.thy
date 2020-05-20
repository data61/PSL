(* -------------------------------------------------------------------------- *)
subsection \<open>Generalized Unitary Matrices\<close>
(* -------------------------------------------------------------------------- *)

theory Unitary_Matrices
imports Matrices More_Complex
begin

text \<open>In this section (generalized) $2\times 2$ unitary matrices are introduced.\<close>

text \<open>Unitary matrices\<close>
definition unitary where
  "unitary M \<longleftrightarrow> mat_adj M *\<^sub>m\<^sub>m M = eye"

text \<open>Generalized unitary matrices\<close>
definition unitary_gen where
  "unitary_gen M \<longleftrightarrow>
   (\<exists> k::complex. k \<noteq> 0 \<and> mat_adj M *\<^sub>m\<^sub>m M = k *\<^sub>s\<^sub>m eye)"

text \<open>Scalar can be always be a positive real\<close>
lemma unitary_gen_real:
  assumes "unitary_gen M"
  shows "(\<exists> k::real. k > 0 \<and> mat_adj M *\<^sub>m\<^sub>m M = cor k *\<^sub>s\<^sub>m eye)"
proof-
  obtain k where *: "mat_adj M *\<^sub>m\<^sub>m M = k *\<^sub>s\<^sub>m eye" "k \<noteq> 0"
    using assms
    by (auto simp add: unitary_gen_def)
  obtain a b c d where "M = (a, b, c, d)"
    by (cases M) auto
  hence "k = cor ((cmod a)\<^sup>2) + cor ((cmod c)\<^sup>2)"
    using *
    by (subst  complex_mult_cnj_cmod[symmetric])+ (auto simp add: mat_adj_def mat_cnj_def)
  hence "is_real k \<and> Re k > 0"
    using \<open>k \<noteq> 0\<close>
    by (smt add_cancel_left_left arg_0_iff arg_complex_of_real_positive not_sum_power2_lt_zero of_real_0 plus_complex.simps(1) plus_complex.simps(2))
  thus ?thesis
    using *
    by (rule_tac x="Re k" in exI) simp
qed

text \<open>Generalized unitary matrices can be factored into a product of a unitary matrix and a real
positive scalar multiple of the identity matrix\<close>
lemma unitary_gen_unitary:
  shows "unitary_gen M \<longleftrightarrow>
         (\<exists> k M'. k > 0 \<and> unitary M' \<and> M = (cor k *\<^sub>s\<^sub>m eye) *\<^sub>m\<^sub>m M')" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain k where *: "k>0" "mat_adj M *\<^sub>m\<^sub>m M = cor k *\<^sub>s\<^sub>m eye"
    using unitary_gen_real[of M]
    by auto

  let ?k' = "cor (sqrt k)"
  have "?k' * cnj ?k' = cor k"
    using \<open>k > 0\<close>
    by simp
  moreover
  have "Re ?k' > 0" "is_real ?k'" "?k' \<noteq> 0"
    using \<open>k > 0\<close>
    by auto
  ultimately
  show ?rhs
    using * mat_eye_l
    unfolding unitary_gen_def unitary_def
    by (rule_tac x="Re ?k'" in exI) (rule_tac x="(1/?k')*\<^sub>s\<^sub>mM" in exI, simp add: mult_sm_mm[symmetric])
next
  assume ?rhs
  then obtain k M' where "k > 0" "unitary M'" "M = (cor k *\<^sub>s\<^sub>m eye) *\<^sub>m\<^sub>m M'"
    by blast
  hence "M = cor k *\<^sub>s\<^sub>m M'"
    using mult_sm_mm[of "cor k" eye M'] mat_eye_l
    by simp
  thus ?lhs
    using \<open>unitary M'\<close> \<open>k > 0\<close>
    by (simp add: unitary_gen_def unitary_def)
qed

text \<open>When they represent Möbius transformations, eneralized unitary matrices fix the imaginary unit circle. Therefore, they
fix a Hermitean form with (2, 0) signature (two positive and no negative diagonal elements).\<close>
lemma unitary_gen_iff':
  shows "unitary_gen M \<longleftrightarrow> 
         (\<exists> k::complex. k \<noteq> 0 \<and> congruence M (1, 0, 0, 1) = k *\<^sub>s\<^sub>m (1, 0, 0, 1))"
  unfolding unitary_gen_def
  using mat_eye_r
  by (auto simp add: mult.assoc)

text \<open>Unitary matrices are special cases of general unitary matrices\<close>
lemma unitary_unitary_gen [simp]:
  assumes "unitary M" 
  shows "unitary_gen M"
  using assms
  unfolding unitary_gen_def unitary_def
  by auto

text \<open>Generalized unitary matrices are regular\<close>
lemma unitary_gen_regular:
  assumes "unitary_gen M"
  shows "mat_det M \<noteq> 0"
proof-
  from assms obtain k where
    "k \<noteq> 0" "mat_adj M *\<^sub>m\<^sub>m M = k *\<^sub>s\<^sub>m eye"
    unfolding unitary_gen_def
    by auto
  hence "mat_det (mat_adj M *\<^sub>m\<^sub>m M) \<noteq> 0"
    by simp
  thus ?thesis
    by (simp add: mat_det_adj)
qed

lemmas unitary_regular = unitary_gen_regular[OF unitary_unitary_gen]

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Group properties\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Generalized $2\times 2$ unitary matrices form a group under
multiplication (usually denoted by $GU(2, \mathbb{C})$). The group is closed
under non-zero complex scalar multiplication. Since these matrices are
always regular, they form a subgroup of general linear group (usually
denoted by $GL(2, \mathbb{C})$) of all regular matrices.\<close>

lemma unitary_gen_scale [simp]:
  assumes "unitary_gen M" and "k \<noteq> 0"
  shows "unitary_gen (k *\<^sub>s\<^sub>m M)"
  using assms
  unfolding unitary_gen_def
  by auto

lemma unitary_comp:
  assumes "unitary M1" and "unitary M2"
  shows "unitary (M1 *\<^sub>m\<^sub>m M2)"
  using assms
  unfolding unitary_def
  by (metis mat_adj_mult_mm mat_eye_l mult_mm_assoc)

lemma unitary_gen_comp:
  assumes "unitary_gen M1" and "unitary_gen M2"
  shows "unitary_gen (M1 *\<^sub>m\<^sub>m M2)"
proof-
  obtain k1 k2 where *: "k1 * k2 \<noteq> 0" "mat_adj M1 *\<^sub>m\<^sub>m M1 = k1 *\<^sub>s\<^sub>m eye" "mat_adj M2 *\<^sub>m\<^sub>m M2 = k2 *\<^sub>s\<^sub>m eye"
    using assms
    unfolding unitary_gen_def
    by auto
  have "mat_adj M2 *\<^sub>m\<^sub>m mat_adj M1 *\<^sub>m\<^sub>m (M1 *\<^sub>m\<^sub>m M2) = mat_adj M2 *\<^sub>m\<^sub>m (mat_adj M1 *\<^sub>m\<^sub>m M1) *\<^sub>m\<^sub>m M2"
    by (auto simp add: mult_mm_assoc)
  also have "... = mat_adj M2 *\<^sub>m\<^sub>m ((k1 *\<^sub>s\<^sub>m eye) *\<^sub>m\<^sub>m M2)"
    using *
    by (auto simp add: mult_mm_assoc)
  also have "... = mat_adj M2 *\<^sub>m\<^sub>m (k1 *\<^sub>s\<^sub>m M2)"
    using mult_sm_eye_mm[of k1 M2]
    by (simp del: eye_def)
  also have "... = k1 *\<^sub>s\<^sub>m (k2 *\<^sub>s\<^sub>m eye)"
    using *
    by auto
  finally
  show ?thesis
    using *
    unfolding unitary_gen_def
    by (rule_tac x="k1*k2" in exI, simp del: eye_def)
qed

lemma unitary_adj_eq_inv:
  shows "unitary M \<longleftrightarrow> mat_det M \<noteq> 0 \<and> mat_adj M = mat_inv M"
  using  unitary_regular[of M] mult_mm_inv_r[of M "mat_adj M" eye]  mat_eye_l[of "mat_inv M"] mat_inv_l[of M]
  unfolding unitary_def
  by - (rule, simp_all)

lemma unitary_inv:
  assumes "unitary M"
  shows "unitary (mat_inv M)"
  using assms
  unfolding unitary_adj_eq_inv
  using mat_adj_inv[of M] mat_det_inv[of M]
  by simp

lemma unitary_gen_inv:
  assumes "unitary_gen M"
  shows "unitary_gen (mat_inv M)"
proof-
    obtain k M' where "0 < k" "unitary M'" "M = cor k *\<^sub>s\<^sub>m eye *\<^sub>m\<^sub>m M'"
      using unitary_gen_unitary[of M] assms
      by blast
    hence "mat_inv M = cor (1/k) *\<^sub>s\<^sub>m mat_inv M'"
      by (metis mat_inv_mult_sm mult_sm_eye_mm norm_not_less_zero of_real_1 of_real_divide of_real_eq_0_iff sgn_1_neg sgn_greater sgn_if sgn_pos sgn_sgn)
    thus ?thesis
      using \<open>k > 0\<close> \<open>unitary M'\<close>
      by (subst unitary_gen_unitary[of "mat_inv M"]) (rule_tac x="1/k" in exI, rule_tac x="mat_inv M'" in exI, metis divide_pos_pos mult_sm_eye_mm unitary_inv zero_less_one)
  qed

(* -------------------------------------------------------------------------- *)
subsubsection \<open>The characterization in terms of matrix elements\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Special matrices are those having the determinant equal to 1. We first give their characterization.\<close>
lemma unitary_special:
  assumes "unitary M" and "mat_det M = 1"
  shows "\<exists> a b. M = (a, b, -cnj b, cnj a)"
proof-
  have "mat_adj M = mat_inv M"
    using assms mult_mm_inv_r[of M "mat_adj M" "eye"] mat_eye_r mat_eye_l
    by (simp add: unitary_def)
  thus ?thesis
    using \<open>mat_det M = 1\<close>
    by (cases M) (auto simp add: mat_adj_def mat_cnj_def)
qed

lemma unitary_gen_special:
  assumes "unitary_gen M" and "mat_det M = 1"
  shows "\<exists> a b. M = (a, b, -cnj b, cnj a)"
proof-
  from assms
  obtain k where *: "k \<noteq> 0" "mat_adj M *\<^sub>m\<^sub>m M = k *\<^sub>s\<^sub>m eye"
    unfolding unitary_gen_def
    by auto
  hence "mat_det (mat_adj M *\<^sub>m\<^sub>m M) = k*k"
    by simp
  hence "k*k = 1"
    using assms(2)
    by (simp add: mat_det_adj)
  hence "k = 1 \<or> k = -1"
    using square_eq_1_iff[of k]
    by simp
  moreover
  have "mat_adj M = k *\<^sub>s\<^sub>m mat_inv M"
    using *
    using assms mult_mm_inv_r[of M "mat_adj M" "k *\<^sub>s\<^sub>m eye"] mat_eye_r mat_eye_l
    by simp (metis mult_sm_eye_mm *(2))
  moreover
  obtain a b c d where "M = (a, b, c, d)"
    by (cases M) auto
  ultimately
  have "M = (a, b, -cnj b, cnj a) \<or> M = (a, b, cnj b, -cnj a)"
    using assms(2)
    by (auto simp add: mat_adj_def mat_cnj_def)
  moreover
  have "Re (- (cor (cmod a))\<^sup>2 - (cor (cmod b))\<^sup>2) < 1"
    by (smt cmod_square complex_norm_square minus_complex.simps(1) of_real_power realpow_square_minus_le uminus_complex.simps(1))
  hence "- (cor (cmod a))\<^sup>2 - (cor (cmod b))\<^sup>2 \<noteq> 1"
    by force
  hence "M \<noteq> (a, b, cnj b, -cnj a)"
    using \<open>mat_det M = 1\<close> complex_mult_cnj_cmod[of a] complex_mult_cnj_cmod[of b]
    by auto
  ultimately
  show ?thesis
    by auto
qed

text \<open>A characterization of all generalized unitary matrices\<close>
lemma unitary_gen_iff:
  shows "unitary_gen M \<longleftrightarrow> 
         (\<exists> a b k. k \<noteq> 0 \<and> mat_det (a, b, -cnj b, cnj a) \<noteq> 0 \<and>
                           M = k *\<^sub>s\<^sub>m (a, b, -cnj b, cnj a))" (is "?lhs = ?rhs")
proof
  assume ?lhs
  obtain d where *: "d*d = mat_det M"
    using ex_complex_sqrt
    by auto
  hence "d \<noteq> 0"
    using unitary_gen_regular[OF \<open>unitary_gen M\<close>]
    by auto
  from \<open>unitary_gen M\<close>
  obtain k where "k \<noteq> 0" "mat_adj M *\<^sub>m\<^sub>m M = k *\<^sub>s\<^sub>m eye"
    unfolding unitary_gen_def
    by auto
  hence "mat_adj ((1/d)*\<^sub>s\<^sub>mM) *\<^sub>m\<^sub>m ((1/d)*\<^sub>s\<^sub>mM) = (k / (d*cnj d)) *\<^sub>s\<^sub>m eye"
    by simp
  obtain a b where "(a, b, - cnj b, cnj a) = (1 / d) *\<^sub>s\<^sub>m M"
    using unitary_gen_special[of "(1 / d) *\<^sub>s\<^sub>m M"]  \<open>unitary_gen M\<close> *  unitary_gen_regular[of M] \<open>d \<noteq> 0\<close>
    by force
  moreover
  hence "mat_det (a, b, - cnj b, cnj a) \<noteq> 0"
    using unitary_gen_regular[OF \<open>unitary_gen M\<close>] \<open>d \<noteq> 0\<close>
    by auto
  ultimately
  show ?rhs
    apply (rule_tac x="a" in exI, rule_tac x="b" in exI, rule_tac x="d" in exI)
    using mult_sm_inv_l[of "1/d" M]
    by (auto simp add: field_simps)
next
  assume ?rhs
  then obtain a b k where "k \<noteq> 0 \<and> mat_det (a, b, - cnj b, cnj a) \<noteq> 0 \<and> M = k *\<^sub>s\<^sub>m (a, b, - cnj b, cnj a)"
    by auto
  thus ?lhs
    unfolding unitary_gen_def
    apply (auto simp add: mat_adj_def mat_cnj_def)
    using mult_eq_0_iff[of "cnj k * k" "cnj a * a + cnj b * b"]
    by (auto simp add: field_simps)
qed

text \<open>A characterization of unitary matrices\<close>

lemma unitary_iff:
  shows "unitary M \<longleftrightarrow>
         (\<exists> a b k. (cmod a)\<^sup>2 + (cmod b)\<^sup>2 \<noteq> 0 \<and> 
                           (cmod k)\<^sup>2 = 1 / ((cmod a)\<^sup>2 + (cmod b)\<^sup>2) \<and>
                           M = k *\<^sub>s\<^sub>m (a, b, -cnj b, cnj a))" (is "?lhs = ?rhs")
proof
  assume ?lhs
  obtain k a b where *: "M = k *\<^sub>s\<^sub>m (a, b, -cnj b, cnj a)" "k \<noteq> 0" "mat_det (a, b, -cnj b, cnj a) \<noteq> 0"
    using unitary_gen_iff  unitary_unitary_gen[OF \<open>unitary M\<close>]
    by auto

  have md: "mat_det (a, b, -cnj b, cnj a) = cor ((cmod a)\<^sup>2 + (cmod b)\<^sup>2)"
    by (auto simp add: complex_mult_cnj_cmod)

  have "k * cnj k * mat_det (a, b, -cnj b, cnj a) = 1"
    using \<open>unitary M\<close> *
    unfolding unitary_def
    by (auto simp add: mat_adj_def mat_cnj_def field_simps)
  hence "(cmod k)\<^sup>2 * ((cmod a)\<^sup>2 + (cmod b)\<^sup>2) = 1"
    by (subst (asm) complex_mult_cnj_cmod, subst (asm) md, subst (asm) cor_mult[symmetric]) (metis of_real_1 of_real_eq_iff)
  thus ?rhs
    using * mat_eye_l
    apply (rule_tac x="a" in exI, rule_tac x="b" in exI, rule_tac x="k" in exI)
    apply (auto simp add: complex_mult_cnj_cmod)
    by (metis \<open>(cmod k)\<^sup>2 * ((cmod a)\<^sup>2 + (cmod b)\<^sup>2) = 1\<close> mult_eq_0_iff nonzero_eq_divide_eq zero_neq_one)
next
  assume ?rhs
  then obtain a b k where  *: "(cmod a)\<^sup>2 + (cmod b)\<^sup>2 \<noteq> 0" "(cmod k)\<^sup>2 = 1 / ((cmod a)\<^sup>2 + (cmod b)\<^sup>2)" "M = k *\<^sub>s\<^sub>m (a, b, -cnj b, cnj a)"
    by auto
  have "(k * cnj k) * (a * cnj a) + (k * cnj k) * (b * cnj b) = 1"
    apply (subst complex_mult_cnj_cmod)+
    using *(1-2)
    by (metis (no_types, lifting) distrib_left nonzero_eq_divide_eq of_real_1 of_real_add of_real_divide of_real_eq_0_iff)
  thus ?lhs
    using *
    unfolding unitary_def
    by (simp add: mat_adj_def mat_cnj_def field_simps)
qed

end
