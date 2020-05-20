(* ----------------------------------------------------------------- *)
subsection \<open>Generalized unitary matrices with signature $(1, 1)$\<close>
(* ----------------------------------------------------------------- *)

theory Unitary11_Matrices
imports Matrices More_Complex
begin

text \<open> When acting as Möbius transformations in the extended
complex plane, generalized complex $2\times 2$ unitary matrices fix
the imaginary unit circle (a Hermitean form with (2, 0) signature). We
now describe matrices that fix the ordinary unit circle (a Hermitean
form with (1, 1) signature, i.e., one positive and one negative
element on the diagonal). These are extremely important for further
formalization, since they will represent disc automorphisims and
isometries of the Poincar\'e disc. The development of this theory
follows the development of the theory of generalized unitary matrices.
\<close>

text \<open>Unitary11 matrices\<close>
definition unitary11 where
  "unitary11 M \<longleftrightarrow> congruence M (1, 0, 0, -1) = (1, 0, 0, -1)"

text \<open>Generalized unitary11 matrices\<close>
definition unitary11_gen where
  "unitary11_gen M \<longleftrightarrow> (\<exists> k. k \<noteq> 0 \<and> congruence M (1, 0, 0, -1) = k *\<^sub>s\<^sub>m (1, 0, 0, -1))"

text \<open>Scalar can always be a non-zero real number\<close>
lemma unitary11_gen_real:
  shows "unitary11_gen M \<longleftrightarrow> (\<exists> k. k \<noteq> 0 \<and> congruence M (1, 0, 0, -1) = cor k *\<^sub>s\<^sub>m (1, 0, 0, -1))"
  unfolding unitary11_gen_def
proof (auto simp del: congruence_def)
  fix k
  assume "k \<noteq> 0" "congruence M (1, 0, 0, -1) = (k, 0, 0, - k)"
  hence "mat_det (congruence M (1, 0, 0, -1)) = -k*k"
    by simp
  moreover
  have "is_real (mat_det (congruence M (1, 0, 0, -1)))" "Re (mat_det (congruence M (1, 0, 0, -1))) \<le> 0"
    by (auto simp add: mat_det_adj)
  ultimately
  have "is_real (k*k)" "Re (-k*k) \<le> 0"
    by auto
  hence "is_real (k*k) \<and> Re (k * k) > 0"
    using \<open>k \<noteq> 0\<close>
    by (smt complex_eq_if_Re_eq mult_eq_0_iff mult_minus_left uminus_complex.simps(1) zero_complex.simps(1) zero_complex.simps(2))
  hence "is_real k"
    by auto
  thus "\<exists>ka. ka \<noteq> 0 \<and> k = cor ka"
    using \<open>k \<noteq> 0\<close>
    by (rule_tac x="Re k" in exI) (cases k, auto simp add: Complex_eq)
qed

text \<open>Unitary11 matrices are special cases of generalized unitary 11 matrices\<close>
lemma unitary11_unitary11_gen [simp]:
  assumes "unitary11 M"
  shows "unitary11_gen M"
  using assms
  unfolding unitary11_gen_def unitary11_def
  by (rule_tac x="1" in exI, auto)

text \<open>All generalized unitary11 matrices are regular\<close>
lemma unitary11_gen_regular:
  assumes "unitary11_gen M"
  shows "mat_det M \<noteq> 0"
proof-
  from assms obtain k where
    "k \<noteq> 0" "mat_adj M *\<^sub>m\<^sub>m (1, 0, 0, -1) *\<^sub>m\<^sub>m M = cor k *\<^sub>s\<^sub>m (1, 0, 0, -1)"
    unfolding unitary11_gen_real
    by auto
  hence "mat_det (mat_adj M *\<^sub>m\<^sub>m (1, 0, 0, -1) *\<^sub>m\<^sub>m M) \<noteq> 0"
    by simp
  thus ?thesis
    by (simp add: mat_det_adj)
qed

lemmas unitary11_regular = unitary11_gen_regular[OF unitary11_unitary11_gen]

(* ----------------------------------------------------------------- *)
subsubsection \<open>The characterization in terms of matrix elements\<close>
(* ----------------------------------------------------------------- *)

text \<open>Special matrices are those having the determinant equal to 1. We first give their characterization.\<close>
lemma unitary11_special:
  assumes "unitary11 M" and "mat_det M = 1"
  shows "\<exists> a b. M = (a, b, cnj b, cnj a)"
proof-
  have "mat_adj M *\<^sub>m\<^sub>m (1, 0, 0, -1) = (1, 0, 0, -1) *\<^sub>m\<^sub>m mat_inv M"
    using assms mult_mm_inv_r
    by (simp add: unitary11_def)
  thus ?thesis
    using assms(2)
    by (cases M) (simp add: mat_adj_def mat_cnj_def)
qed

lemma unitary11_gen_special:
  assumes "unitary11_gen M" and "mat_det M = 1"
  shows "\<exists> a b. M = (a, b, cnj b, cnj a) \<or> M = (a, b, -cnj b, -cnj a)"
proof-
  from assms
  obtain k where *: "k \<noteq> 0" "mat_adj M *\<^sub>m\<^sub>m (1, 0, 0, -1) *\<^sub>m\<^sub>m M = cor k *\<^sub>s\<^sub>m (1, 0, 0, -1)"
    unfolding unitary11_gen_real
    by auto
  hence "mat_det (mat_adj M *\<^sub>m\<^sub>m (1, 0, 0, -1) *\<^sub>m\<^sub>m M) = -  cor k* cor k"
    by simp
  hence "mat_det (mat_adj M *\<^sub>m\<^sub>m M) = cor k* cor k"
    by simp
  hence "cor k* cor k = 1"
    using assms(2)
    by (simp add: mat_det_adj)
  hence "cor k = 1 \<or> cor k = -1"
    using square_eq_1_iff[of "cor k"]
    by simp
  moreover
  have "mat_adj M *\<^sub>m\<^sub>m (1, 0, 0, -1) = (cor k *\<^sub>s\<^sub>m (1, 0, 0, -1)) *\<^sub>m\<^sub>m mat_inv M "
    using *
    using assms mult_mm_inv_r mat_eye_r mat_eye_l
    by auto
  moreover
  obtain a b c d where "M = (a, b, c, d)"
    by (cases M) auto
  ultimately
  have "M = (a, b, cnj b, cnj a) \<or> M = (a, b, -cnj b, -cnj a)"
    using assms(2)
    by (auto simp add: mat_adj_def mat_cnj_def)
  thus ?thesis
    by auto
qed

text \<open>A characterization of all generalized unitary11 matrices\<close>
lemma unitary11_gen_iff':
  shows "unitary11_gen M \<longleftrightarrow>
         (\<exists> a b k. k \<noteq> 0 \<and> mat_det (a, b, cnj b, cnj a) \<noteq> 0 \<and>
                           (M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a) \<or> 
                            M = k *\<^sub>s\<^sub>m (-1, 0, 0, 1) *\<^sub>m\<^sub>m (a, b, cnj b, cnj a)))" (is "?lhs = ?rhs")
proof
  assume ?lhs
  obtain d where *: "d*d = mat_det M"
    using ex_complex_sqrt
    by auto
  hence "d \<noteq> 0"
    using unitary11_gen_regular[OF \<open>unitary11_gen M\<close>]
    by auto
  from \<open>unitary11_gen M\<close>
  obtain k where "k \<noteq> 0" "mat_adj M *\<^sub>m\<^sub>m (1, 0, 0, -1) *\<^sub>m\<^sub>m M = cor k *\<^sub>s\<^sub>m (1, 0, 0, -1)"
    unfolding unitary11_gen_real
    by auto
  hence "mat_adj ((1/d)*\<^sub>s\<^sub>mM)*\<^sub>m\<^sub>m (1, 0, 0, -1) *\<^sub>m\<^sub>m ((1/d)*\<^sub>s\<^sub>mM) = (cor k / (d*cnj d)) *\<^sub>s\<^sub>m (1, 0, 0, -1)"
    by simp
  moreover
  have "is_real (cor k / (d * cnj d))"
    by (metis complex_In_mult_cnj_zero div_reals Im_complex_of_real)
  hence "cor (Re (cor k / (d * cnj d))) = cor k / (d * cnj d)"
    by simp
  ultimately
  have "unitary11_gen ((1/d)*\<^sub>s\<^sub>mM)"
    unfolding unitary11_gen_real
    using \<open>d \<noteq> 0\<close> \<open>k \<noteq> 0\<close>
    using \<open>cor (Re (cor k / (d * cnj d))) = cor k / (d * cnj d)\<close>
    by (rule_tac x="Re (cor k / (d * cnj d))" in exI, auto, simp add: *)
  moreover
  have "mat_det ((1 / d) *\<^sub>s\<^sub>m M) = 1"
    using * unitary11_gen_regular[of M] \<open>unitary11_gen M\<close>
    by auto
  ultimately
  obtain a b where "(a, b, cnj b, cnj a) = (1 / d) *\<^sub>s\<^sub>m M \<or> (a, b, -cnj b, -cnj a) = (1 / d) *\<^sub>s\<^sub>m M"
    using unitary11_gen_special[of "(1 / d) *\<^sub>s\<^sub>m M"]
    by force
  thus ?rhs
  proof
    assume "(a, b, cnj b, cnj a) = (1 / d) *\<^sub>s\<^sub>m M"
    moreover
    hence "mat_det (a, b, cnj b, cnj a) \<noteq> 0"
      using unitary11_gen_regular[OF \<open>unitary11_gen M\<close>] \<open>d \<noteq> 0\<close>
      by auto
    ultimately
    show ?rhs
      using \<open>d \<noteq> 0\<close>
      by (rule_tac x="a" in exI, rule_tac x="b" in exI, rule_tac x="d" in exI, simp)
  next
    assume *: "(a, b, -cnj b, -cnj a) = (1 / d) *\<^sub>s\<^sub>m M"
    hence " (1 / d) *\<^sub>s\<^sub>m M = (a, b, -cnj b, -cnj a)"
      by simp
    hence "M = (a * d, b * d, - (d * cnj b), - (d * cnj a))"
      using \<open>d \<noteq> 0\<close>
      using mult_sm_inv_l[of "1/d" M "(a, b, -cnj b, -cnj a)", symmetric]
      by (simp add: field_simps)
    moreover
    have "mat_det (a, b, -cnj b, -cnj a) \<noteq> 0"
      using * unitary11_gen_regular[OF \<open>unitary11_gen M\<close>] \<open>d \<noteq> 0\<close>
      by auto
    ultimately
    show ?thesis
      using \<open>d \<noteq> 0\<close>
      by (rule_tac x="a" in exI, rule_tac x="b" in exI, rule_tac x="-d" in exI) (simp add: field_simps)
  qed
next
  assume ?rhs
  then obtain a b k where "k \<noteq> 0" "mat_det (a, b, cnj b, cnj a) \<noteq> 0"
    "M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a) \<or> M = k *\<^sub>s\<^sub>m (-1, 0, 0, 1) *\<^sub>m\<^sub>m (a, b, cnj b, cnj a)"
    by auto
  moreover
  let ?x = "cnj k * cnj a * (k * a) + - (cnj k * b * (k * cnj b))"
  have "?x = (k*cnj k)*(a*cnj a - b*cnj b)"
    by (auto simp add: field_simps)
  hence "is_real ?x"
    by simp
  hence "cor (Re ?x) = ?x"
    by (rule complex_of_real_Re)
  moreover
  have "?x \<noteq> 0"
    using mult_eq_0_iff[of "cnj k * k" "(cnj a * a + - cnj b * b)"]
    using \<open>mat_det (a, b, cnj b, cnj a) \<noteq> 0\<close> \<open>k \<noteq> 0\<close>
    by (auto simp add: field_simps)
  hence "Re ?x \<noteq> 0"
    using \<open>is_real ?x\<close>
    by (metis calculation(4) of_real_0)
  ultimately
  show ?lhs
    unfolding unitary11_gen_real
    by (rule_tac x="Re ?x" in exI) (auto simp add: mat_adj_def mat_cnj_def)
qed

text \<open>Another characterization of all generalized unitary11 matrices. They are products of 
rotation and Blaschke factor matrices.\<close>
lemma unitary11_gen_cis_blaschke:
  assumes "k \<noteq> 0" and "M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)" and 
          "a \<noteq> 0" and "mat_det (a, b, cnj b, cnj a) \<noteq> 0"
  shows "\<exists> k' \<phi> a'. k' \<noteq> 0 \<and> a' * cnj a' \<noteq> 1 \<and> 
                                 M = k' *\<^sub>s\<^sub>m (cis \<phi>, 0, 0, 1) *\<^sub>m\<^sub>m (1, -a', -cnj a', 1)"
proof-
  have "a = cnj a * cis (2 * arg a)"
    using rcis_cmod_arg[of a] rcis_cnj[of a]
    using cis_rcis_eq rcis_mult
    by simp
  thus ?thesis
    using assms
    by (rule_tac x="k*cnj a" in exI, rule_tac x="2*arg a" in exI, rule_tac x="- b / a" in exI) (auto simp add: field_simps)
qed

lemma unitary11_gen_cis_blaschke':
  assumes "k \<noteq> 0" and "M = k *\<^sub>s\<^sub>m (-1, 0, 0, 1) *\<^sub>m\<^sub>m (a, b, cnj b, cnj a)" and
          "a \<noteq> 0" and "mat_det (a, b, cnj b, cnj a) \<noteq> 0"
  shows "\<exists> k' \<phi> a'. k' \<noteq> 0 \<and> a' * cnj a' \<noteq> 1 \<and>
                                 M = k' *\<^sub>s\<^sub>m (cis \<phi>, 0, 0, 1) *\<^sub>m\<^sub>m (1, -a', -cnj a', 1)"
proof-
  obtain k' \<phi> a' where *: "k' \<noteq> 0" "k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a) = k' *\<^sub>s\<^sub>m (cis \<phi>, 0, 0, 1) *\<^sub>m\<^sub>m (1, -a', -cnj a', 1)" "a' * cnj a' \<noteq> 1"
    using unitary11_gen_cis_blaschke[OF \<open>k \<noteq> 0\<close> _ \<open>a \<noteq> 0\<close>] \<open>mat_det (a, b, cnj b, cnj a) \<noteq> 0\<close>
    by blast
  have "(cis \<phi>, 0, 0, 1) *\<^sub>m\<^sub>m (-1, 0, 0, 1) = (cis (\<phi> + pi), 0, 0, 1)"
   by (simp add: cis_def complex.corec Complex_eq)
  thus ?thesis
    using * \<open>M = k *\<^sub>s\<^sub>m (-1, 0, 0, 1) *\<^sub>m\<^sub>m (a, b, cnj b, cnj a)\<close>
    by (rule_tac x="k'" in exI, rule_tac x="\<phi> + pi" in exI, rule_tac x="a'" in exI, simp)
qed

lemma unitary11_gen_cis_blaschke_rev:
  assumes "k' \<noteq> 0" and "M = k' *\<^sub>s\<^sub>m (cis \<phi>, 0, 0, 1) *\<^sub>m\<^sub>m (1, -a', -cnj a', 1)" and
          "a' * cnj a' \<noteq> 1"
  shows "\<exists> k a b. k \<noteq> 0 \<and> mat_det (a, b, cnj b, cnj a) \<noteq> 0  \<and>
                          M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)"
  using assms
  apply (rule_tac x="k'*cis(\<phi>/2)" in exI, rule_tac x="cis(\<phi>/2)" in exI, rule_tac x="-a'*cis(\<phi>/2)" in exI)
  apply (simp add: cis_mult mult.commute mult.left_commute)
  done

lemma unitary11_gen_cis_inversion:
  assumes "k \<noteq> 0" and "M = k *\<^sub>s\<^sub>m (0, b, cnj b, 0)" and "b \<noteq> 0"
  shows "\<exists> k' \<phi>. k' \<noteq> 0 \<and>
                              M = k' *\<^sub>s\<^sub>m (cis \<phi>, 0, 0, 1) *\<^sub>m\<^sub>m (0, 1, 1, 0)"
using assms
using rcis_cmod_arg[of b, symmetric] rcis_cnj[of b] cis_rcis_eq
by simp (rule_tac x="2*arg b" in exI, simp add: rcis_mult)

lemma unitary11_gen_cis_inversion':
  assumes "k \<noteq> 0" and "M = k *\<^sub>s\<^sub>m (-1, 0, 0, 1) *\<^sub>m\<^sub>m (0, b, cnj b, 0)" and "b \<noteq> 0"
  shows "\<exists> k' \<phi>. k' \<noteq> 0 \<and>
                   M = k' *\<^sub>s\<^sub>m (cis \<phi>, 0, 0, 1) *\<^sub>m\<^sub>m (0, 1, 1, 0)"
proof-
  obtain k' \<phi> where *: "k' \<noteq> 0" "k *\<^sub>s\<^sub>m (0, b, cnj b, 0) = k' *\<^sub>s\<^sub>m (cis \<phi>, 0, 0, 1) *\<^sub>m\<^sub>m (0, 1, 1, 0)"
    using unitary11_gen_cis_inversion[OF \<open>k \<noteq> 0\<close> _ \<open>b \<noteq> 0\<close>]
    by metis
  have "(cis \<phi>, 0, 0, 1) *\<^sub>m\<^sub>m (-1, 0, 0, 1) = (cis (\<phi> + pi), 0, 0, 1)"
    by (simp add: cis_def complex.corec Complex_eq)
  thus ?thesis
    using * \<open>M = k *\<^sub>s\<^sub>m (-1, 0, 0, 1) *\<^sub>m\<^sub>m (0, b, cnj b, 0)\<close>
    by (rule_tac x="k'" in exI, rule_tac x="\<phi> + pi" in exI, simp)
qed

lemma unitary11_gen_cis_inversion_rev:
  assumes "k' \<noteq> 0" and "M = k' *\<^sub>s\<^sub>m (cis \<phi>, 0, 0, 1) *\<^sub>m\<^sub>m (0, 1, 1, 0)"
  shows "\<exists> k a b. k \<noteq> 0 \<and> mat_det (a, b, cnj b, cnj a) \<noteq> 0 \<and>
                          M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)"
  using assms
  by (rule_tac x="k'*cis(\<phi>/2)" in exI, rule_tac x=0 in exI, rule_tac x="cis(\<phi>/2)" in exI) (simp add: cis_mult)

text \<open>Another characterization of generalized unitary11 matrices\<close>
lemma unitary11_gen_iff:
  shows "unitary11_gen M \<longleftrightarrow> 
         (\<exists> k a b. k \<noteq> 0 \<and> mat_det (a, b, cnj b, cnj a) \<noteq> 0 \<and>
                           M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a))" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain a b k where *: "k \<noteq> 0" "mat_det (a, b, cnj b, cnj a) \<noteq> 0" "M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a) \<or> M = k *\<^sub>s\<^sub>m (-1, 0, 0, 1) *\<^sub>m\<^sub>m (a, b, cnj b, cnj a)"
    using unitary11_gen_iff'
    by auto
  show ?rhs
  proof (cases "M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)")
    case True
    thus ?thesis
      using *
      by auto
  next
    case False
    hence **: "M = k *\<^sub>s\<^sub>m (-1, 0, 0, 1) *\<^sub>m\<^sub>m (a, b, cnj b, cnj a)"
      using *
      by simp
    show ?thesis
    proof (cases "a = 0")
      case True
      hence "b \<noteq> 0"
        using *
        by auto
      show ?thesis
        using unitary11_gen_cis_inversion_rev[of _ M]
        using ** \<open>a = 0\<close>
        using unitary11_gen_cis_inversion'[OF \<open>k \<noteq> 0\<close> _ \<open>b \<noteq> 0\<close>, of M]
        by auto
    next
      case False
      show ?thesis
        using unitary11_gen_cis_blaschke_rev[of _ M]
        using **
        using unitary11_gen_cis_blaschke'[OF \<open>k \<noteq> 0\<close> _ \<open>a \<noteq> 0\<close>, of M b] \<open>mat_det (a, b, cnj b, cnj a) \<noteq> 0\<close>
        by blast
    qed
  qed
next
  assume ?rhs
  thus ?lhs
    using unitary11_gen_iff'
    by auto
qed

lemma unitary11_iff:
  shows "unitary11 M \<longleftrightarrow>
         (\<exists> a b k. (cmod a)\<^sup>2 > (cmod b)\<^sup>2 \<and>
                           (cmod k)\<^sup>2 = 1 / ((cmod a)\<^sup>2 - (cmod b)\<^sup>2) \<and>
                           M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a))" (is "?lhs = ?rhs")
proof
  assume ?lhs
  obtain k a b where *:
    "M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)""mat_det (a, b, cnj b, cnj a) \<noteq> 0" "k \<noteq> 0"
    using unitary11_gen_iff unitary11_unitary11_gen[OF \<open>unitary11 M\<close>]
    by auto

  have md: "mat_det (a, b, cnj b, cnj a) = cor ((cmod a)\<^sup>2 - (cmod b)\<^sup>2)"
    by (auto simp add: complex_mult_cnj_cmod)
  hence **: "(cmod a)\<^sup>2 \<noteq> (cmod b)\<^sup>2"
    using \<open>mat_det (a, b, cnj b, cnj a) \<noteq> 0\<close>
    by auto

  have "k * cnj k * mat_det (a, b, cnj b, cnj a) = 1"
    using \<open>M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)\<close>
    using \<open>unitary11 M\<close>
    unfolding unitary11_def
    by (auto simp add: mat_adj_def mat_cnj_def) (simp add: field_simps)
  hence ***: "(cmod k)\<^sup>2 * ((cmod a)\<^sup>2 - (cmod b)\<^sup>2) = 1"
    by (subst (asm) complex_mult_cnj_cmod, subst (asm) md, subst (asm) cor_mult[symmetric]) (metis of_real_1 of_real_eq_iff)
  hence "((cmod a)\<^sup>2 - (cmod b)\<^sup>2) = 1 / (cmod k)\<^sup>2"
    by (cases "k=0") (auto simp add: field_simps)
  hence "cmod a ^ 2 = cmod b ^ 2 + 1 / cmod k ^ 2"
    by simp
  thus ?rhs
    using \<open>M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)\<close> ** mat_eye_l
    by (rule_tac x="a" in exI, rule_tac x="b" in exI, rule_tac x="k" in exI)
       (auto simp add: complex_mult_cnj_cmod intro!: )
next
  assume ?rhs
  then obtain a b k where "(cmod b)\<^sup>2 < (cmod a)\<^sup>2 \<and> (cmod k)\<^sup>2 = 1 / ((cmod a)\<^sup>2 - (cmod b)\<^sup>2) \<and> M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)"
    by auto
  moreover
  have "cnj k * cnj a * (k * a) + - (cnj k * b * (k * cnj b)) = (cor ((cmod k)\<^sup>2 * ((cmod a)\<^sup>2 - (cmod b)\<^sup>2)))"
  proof-
    have "cnj k * cnj a * (k * a) = cor ((cmod k)\<^sup>2 * (cmod a)\<^sup>2)"
      using complex_mult_cnj_cmod[of a] complex_mult_cnj_cmod[of k]
      by (auto simp add: field_simps)
    moreover
    have "cnj k * b * (k * cnj b) = cor ((cmod k)\<^sup>2 * (cmod b)\<^sup>2)"
      using complex_mult_cnj_cmod[of b, symmetric] complex_mult_cnj_cmod[of k]
      by (auto simp add: field_simps)
    ultimately
    show ?thesis
      by (auto simp add: field_simps)
  qed
  ultimately
  show ?lhs
    unfolding unitary11_def
    by (auto simp add: mat_adj_def mat_cnj_def field_simps)
qed

(* ----------------------------------------------------------------- *)
subsubsection \<open>Group properties\<close>
(* ----------------------------------------------------------------- *)

text \<open>Generalized unitary11 matrices form a group under
multiplication (it is sometimes denoted by $GU_{1, 1}(2,
\mathbb{C})$). The group is also closed under non-zero complex scalar
multiplication. Since these matrices are always regular, they form a
subgroup of general linear group (usually denoted by $GL(2,
\mathbb{C})$) of all regular matrices.\<close>

lemma unitary11_gen_mult_sm:
  assumes "k \<noteq> 0" and "unitary11_gen M"
  shows "unitary11_gen (k *\<^sub>s\<^sub>m M)"
proof-
  have "k * cnj k = cor (Re (k * cnj k))"
    by (subst complex_of_real_Re) auto
  thus ?thesis
    using assms
    unfolding unitary11_gen_real
    by auto (rule_tac x="Re (k*cnj k) * ka" in exI, auto)
qed

lemma unitary11_gen_div_sm:
  assumes "k \<noteq> 0" and "unitary11_gen (k *\<^sub>s\<^sub>m M)"
  shows "unitary11_gen M"
  using assms unitary11_gen_mult_sm[of "1/k" "k *\<^sub>s\<^sub>m M"]
  by simp


lemma unitary11_inv:
  assumes "k \<noteq> 0" and "M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)" and "mat_det (a, b, cnj b, cnj a) \<noteq> 0"
  shows "\<exists> k' a' b'. k' \<noteq> 0 \<and> mat_inv M = k' *\<^sub>s\<^sub>m (a', b', cnj b', cnj a') \<and> mat_det (a', b', cnj b', cnj a') \<noteq> 0"
  using assms
  by (subst assms, subst mat_inv_mult_sm[OF assms(1)])
     (rule_tac x="1/(k * mat_det (a, b, cnj b, cnj a))" in exI, rule_tac x="cnj a" in exI, rule_tac x="-b" in exI, simp add: field_simps)

lemma unitary11_comp:
  assumes "k1 \<noteq> 0" and "M1 = k1 *\<^sub>s\<^sub>m (a1, b1, cnj b1, cnj a1)" and "mat_det (a1, b1, cnj b1, cnj a1) \<noteq> 0"
          "k2 \<noteq> 0" "M2 = k2 *\<^sub>s\<^sub>m (a2, b2, cnj b2, cnj a2)" "mat_det (a2, b2, cnj b2, cnj a2) \<noteq> 0"
  shows "\<exists> k a b. k \<noteq> 0 \<and> M1 *\<^sub>m\<^sub>m M2 = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a) \<and> mat_det (a, b, cnj b, cnj a) \<noteq> 0"
  using assms
  apply (rule_tac x="k1*k2" in exI)
  apply (rule_tac x="a1*a2 + b1*cnj b2" in exI)
  apply (rule_tac x="a1*b2 + b1*cnj a2" in exI)
proof (auto simp add: algebra_simps)
  assume *: "a1 * (a2 * (cnj a1 * cnj a2)) + b1 * (b2 * (cnj b1 * cnj b2)) =
            a1 * (b2 * (cnj a1 * cnj b2)) + a2 * (b1 * (cnj a2 * cnj b1))" and
         **: "a1*cnj a1 \<noteq> b1 * cnj b1" "a2*cnj a2 \<noteq> b2*cnj b2"
  hence "(a1*cnj a1)*(a2*cnj a2 - b2*cnj b2) = (b1*cnj b1)*(a2*cnj a2 - b2*cnj b2)"
    by (simp add: field_simps)
  hence "a1*cnj a1 = b1*cnj b1"
    using **(2)
    by simp
  thus False
    using **(1)
    by simp
qed

lemma unitary11_gen_mat_inv:
  assumes "unitary11_gen M" and "mat_det M \<noteq> 0"
  shows "unitary11_gen (mat_inv M)"
proof-
  obtain k a b where "k \<noteq> 0 \<and> mat_det (a, b, cnj b, cnj a) \<noteq> 0 \<and> M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)"
    using assms unitary11_gen_iff[of M]
    by auto
  then obtain k' a' b' where "k' \<noteq> 0 \<and> mat_inv M = k' *\<^sub>s\<^sub>m (a', b', cnj b', cnj a') \<and> mat_det (a', b', cnj b', cnj a') \<noteq> 0"
    using unitary11_inv [of k M a b]
    by auto
  thus ?thesis
    using unitary11_gen_iff[of "mat_inv M"]
    by auto
qed

lemma unitary11_gen_comp:
  assumes "unitary11_gen M1" and "mat_det M1 \<noteq> 0" and "unitary11_gen M2"  and "mat_det M2 \<noteq> 0"
  shows "unitary11_gen (M1 *\<^sub>m\<^sub>m M2)"
proof-
  from assms obtain k1 k2 a1 a2 b1 b2 where
    "k1 \<noteq> 0 \<and> mat_det (a1, b1, cnj b1, cnj a1) \<noteq> 0 \<and> M1 = k1 *\<^sub>s\<^sub>m (a1, b1, cnj b1, cnj a1)"
    "k2 \<noteq> 0 \<and> mat_det (a2, b2, cnj b2, cnj a2) \<noteq> 0 \<and> M2 = k2 *\<^sub>s\<^sub>m (a2, b2, cnj b2, cnj a2)"
    using unitary11_gen_iff[of M1]  unitary11_gen_iff[of M2]
    by blast
  then obtain k a b where "k \<noteq> 0 \<and> M1 *\<^sub>m\<^sub>m M2 = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a) \<and> mat_det (a, b, cnj b, cnj a) \<noteq> 0"
    using unitary11_comp[of k1 M1 a1 b1 k2 M2 a2 b2]
    by blast
  thus ?thesis
    using unitary11_gen_iff[of "M1 *\<^sub>m\<^sub>m M2"]
    by blast
qed

text \<open>Classification into orientation-preserving and orientation-reversing matrices\<close>
lemma unitary11_sgn_det_orientation:
  assumes "k \<noteq> 0" and "mat_det (a, b, cnj b, cnj a) \<noteq> 0" and "M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)"
  shows "\<exists> k'. sgn k' = sgn (Re (mat_det (a, b, cnj b, cnj a))) \<and> congruence M (1, 0, 0, -1) = cor k' *\<^sub>s\<^sub>m (1, 0, 0, -1)"
proof-
  let ?x = "cnj k * cnj a * (k * a) - (cnj k * b * (k * cnj b))"
  have *: "?x = k * cnj k * (a * cnj a - b * cnj b)"
    by (auto simp add: field_simps)
  hence "is_real ?x"
    by auto
  hence "cor (Re ?x) = ?x"
    by (rule complex_of_real_Re)
  moreover
  have "sgn (Re ?x) = sgn (Re (a * cnj a - b * cnj b))"
  proof-
    have *: "Re ?x = (cmod k)\<^sup>2 * Re (a * cnj a - b * cnj b)"
      by (subst *, subst complex_mult_cnj_cmod, subst Re_mult_real) (metis Im_complex_of_real, metis Re_complex_of_real)
    show ?thesis
      using \<open>k \<noteq> 0\<close>
      by (subst *) (simp add: sgn_mult)
  qed
  ultimately
  show ?thesis
    using assms(3)
    by (rule_tac x="Re ?x" in exI) (auto simp add: mat_adj_def mat_cnj_def)
qed

lemma unitary11_sgn_det:
  assumes "k \<noteq> 0" and "mat_det (a, b, cnj b, cnj a) \<noteq> 0" and "M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)" and "M = (A, B, C, D)"
  shows "sgn (Re (mat_det (a, b, cnj b, cnj a))) = (if b = 0 then 1 else sgn (Re ((A*D)/(B*C)) - 1))"
proof (cases "b = 0")
  case True
  thus ?thesis
    using assms
    by (simp only: mat_det.simps, subst complex_mult_cnj_cmod, subst minus_complex.sel, subst Re_complex_of_real, simp)
next
  case False
  from assms have *: "A =  k * a" "B =  k * b" "C =  k * cnj b" "D =  k * cnj a"
    by auto
  hence *: "(A*D)/(B*C) = (a*cnj a)/(b*cnj b)"
    using \<open>k \<noteq> 0\<close>
    by simp
  show ?thesis
    using \<open>b \<noteq> 0\<close>
    apply (subst *, subst Re_divide_real, simp, simp)
    apply (simp only: mat_det.simps)
    apply (subst complex_mult_cnj_cmod)+
    apply ((subst Re_complex_of_real)+, subst minus_complex.sel, (subst Re_complex_of_real)+, simp add: field_simps sgn_if)
    done
qed

lemma unitary11_orientation:
  assumes "unitary11_gen M" and "M = (A, B, C, D)"
  shows "\<exists> k'. sgn k' = sgn (if B = 0 then 1 else sgn (Re ((A*D)/(B*C)) - 1)) \<and> congruence M (1, 0, 0, -1) = cor k' *\<^sub>s\<^sub>m (1, 0, 0, -1)"
proof-
  from \<open>unitary11_gen M\<close>
  obtain k a b where *: "k \<noteq> 0" "mat_det (a, b, cnj b, cnj a) \<noteq> 0" "M = k*\<^sub>s\<^sub>m (a, b, cnj b, cnj a)"
    using unitary11_gen_iff[of M]
    by auto
  moreover
  have "b = 0 \<longleftrightarrow> B = 0"
    using \<open>M = (A, B, C, D)\<close> *
    by auto
  ultimately
  show ?thesis
    using unitary11_sgn_det_orientation[OF *] unitary11_sgn_det[OF * \<open>M = (A, B, C, D)\<close>]
    by auto
qed

lemma unitary11_sgn_det_orientation':
  assumes "congruence M (1, 0, 0, -1) = cor k' *\<^sub>s\<^sub>m (1, 0, 0, -1)" and "k' \<noteq> 0"
  shows "\<exists> a b k. k \<noteq> 0 \<and> M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a) \<and> sgn k' = sgn (Re (mat_det (a, b, cnj b, cnj a)))"
proof-
  obtain a b k where
    "k \<noteq> 0" "mat_det (a, b, cnj b, cnj a) \<noteq> 0" "M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)"
    using assms
    using unitary11_gen_iff[of M]
    unfolding unitary11_gen_def
    by auto
  moreover
  have "sgn k' = sgn (Re (mat_det (a, b, cnj b, cnj a)))"
  proof-
    let ?x = "cnj k * cnj a * (k * a) - (cnj k * b * (k * cnj b))"
    have *: "?x = k * cnj k * (a * cnj a - b * cnj b)"
      by (auto simp add: field_simps)
    hence "is_real ?x"
      by auto
    hence "cor (Re ?x) = ?x"
      by (rule complex_of_real_Re)

    have **: "sgn (Re ?x) = sgn (Re (a * cnj a - b * cnj b))"
    proof-
      have *: "Re ?x = (cmod k)\<^sup>2 * Re (a * cnj a - b * cnj b)"
        by (subst *, subst complex_mult_cnj_cmod, subst Re_mult_real) (metis Im_complex_of_real, metis Re_complex_of_real)
      show ?thesis
        using \<open>k \<noteq> 0\<close>
        by (subst *) (simp add: sgn_mult)
    qed
    moreover
    have "?x = cor k'"
      using \<open>M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)\<close> assms
      by (simp add: mat_adj_def mat_cnj_def)
    hence "sgn (Re ?x) = sgn k'"
      using \<open>cor (Re ?x) = ?x\<close>
      unfolding complex_of_real_def
      by simp
    ultimately
    show ?thesis
      by simp
  qed
  ultimately
  show ?thesis
    by (rule_tac x="a" in exI, rule_tac x="b" in exI, rule_tac x="k" in exI)  simp
qed

end
