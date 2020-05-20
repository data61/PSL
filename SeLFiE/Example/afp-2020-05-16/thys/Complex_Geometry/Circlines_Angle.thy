theory Circlines_Angle
  imports Oriented_Circlines Elementary_Complex_Geometry
begin


(* ----------------------------------------------------------------- *)
subsection \<open>Angle between circlines\<close>
(* ----------------------------------------------------------------- *)

text \<open>Angle between circlines can be defined in purely algebraic terms (following Schwerdtfeger
\cite{schwerdtfeger}) and using this definitions many properties can be easily proved.\<close>

fun mat_det_12 :: "complex_mat \<Rightarrow> complex_mat \<Rightarrow> complex" where
  "mat_det_12 (A1, B1, C1, D1) (A2, B2, C2, D2) = A1*D2 + A2*D1 - B1*C2 - B2*C1"

lemma mat_det_12_mm_l [simp]:
  shows "mat_det_12 (M *\<^sub>m\<^sub>m A) (M *\<^sub>m\<^sub>m B) = mat_det M * mat_det_12 A B"
  by (cases M, cases A, cases B) (simp add: field_simps)

lemma mat_det_12_mm_r [simp]:
  shows "mat_det_12 (A *\<^sub>m\<^sub>m M) (B *\<^sub>m\<^sub>m M) = mat_det M * mat_det_12 A B"
  by (cases M, cases A, cases B) (simp add: field_simps)

lemma mat_det_12_sm_l [simp]:
  shows "mat_det_12 (k *\<^sub>s\<^sub>m A) B = k * mat_det_12 A B"
  by (cases A, cases B) (simp add: field_simps)

lemma mat_det_12_sm_r [simp]:
  shows "mat_det_12 A (k *\<^sub>s\<^sub>m B) = k * mat_det_12 A B"
  by (cases A, cases B) (simp add: field_simps)

lemma mat_det_12_congruence [simp]:
  shows "mat_det_12 (congruence M A) (congruence M B) = (cor ((cmod (mat_det M))\<^sup>2)) * mat_det_12 A B"
  unfolding congruence_def
  by ((subst mult_mm_assoc[symmetric])+, subst mat_det_12_mm_l, subst mat_det_12_mm_r, subst mat_det_adj) (auto simp add: field_simps complex_mult_cnj_cmod)


definition cos_angle_cmat :: "complex_mat \<Rightarrow> complex_mat \<Rightarrow> real" where
  [simp]: "cos_angle_cmat H1 H2 = - Re (mat_det_12 H1 H2) / (2 * (sqrt (Re (mat_det H1 * mat_det H2))))"

lift_definition cos_angle_clmat :: "circline_mat \<Rightarrow> circline_mat \<Rightarrow> real" is cos_angle_cmat
  done

lemma cos_angle_den_scale [simp]:
  assumes "k1 > 0" and "k2 > 0"
  shows "sqrt (Re ((k1\<^sup>2 * mat_det H1) * (k2\<^sup>2 * mat_det H2))) =
         k1 * k2 * sqrt (Re (mat_det H1 * mat_det H2))"
proof-
  let ?lhs = "(k1\<^sup>2 * mat_det H1) * (k2\<^sup>2 * mat_det H2)"
  let ?rhs = "mat_det H1 * mat_det H2"
  have 1: "?lhs = (k1\<^sup>2*k2\<^sup>2) * ?rhs"
    by simp
  hence "Re ?lhs = (k1\<^sup>2*k2\<^sup>2) * Re ?rhs"
    by (simp add: field_simps)
  thus ?thesis
    using assms
    by (simp add: real_sqrt_mult)
qed

lift_definition cos_angle :: "ocircline \<Rightarrow> ocircline \<Rightarrow> real" is cos_angle_clmat
proof transfer
  fix H1 H2 H1' H2'
  assume "ocircline_eq_cmat H1 H1'" "ocircline_eq_cmat H2 H2'"
  then obtain k1 k2 :: real where
  *:  "k1 > 0" "H1' = cor k1 *\<^sub>s\<^sub>m H1"
      "k2 > 0" "H2' = cor k2 *\<^sub>s\<^sub>m H2"
    by auto
  thus "cos_angle_cmat H1 H2 = cos_angle_cmat H1' H2'"
    unfolding cos_angle_cmat_def
    apply (subst *)+
    apply (subst mat_det_12_sm_l, subst mat_det_12_sm_r)
    apply (subst mat_det_mult_sm)+
    apply (subst power2_eq_square[symmetric])+
    apply (subst cos_angle_den_scale, simp, simp)
    apply simp
    done
qed

text \<open>Möbius transformations are conformal, meaning that they preserve oriented angle between
oriented circlines.\<close>

lemma cos_angle_opposite1 [simp]: 
  shows "cos_angle (opposite_ocircline H) H' = - cos_angle H H'"
  by (transfer, transfer, simp)

lemma cos_angle_opposite2 [simp]: 
  shows "cos_angle H (opposite_ocircline H') = - cos_angle H H'"
  by (transfer, transfer, simp)

(* ----------------------------------------------------------------- *)
subsubsection \<open>Connection with the elementary angle definition between circles\<close>
(* ----------------------------------------------------------------- *)

text\<open>We want to connect algebraic definition of an angle with a traditional one and 
to prove equivalency between these two definitions. For the traditional definition of 
an angle we follow the approach suggested by Needham \cite{needham}.\<close>

lemma Re_sgn:
  assumes "is_real A" and "A \<noteq> 0"
  shows "Re (sgn A) = sgn_bool (Re A > 0)"
using assms
using More_Complex.Re_sgn complex_eq_if_Re_eq
by auto

lemma Re_mult_real3:
  assumes "is_real z1" and "is_real z2" and "is_real z3"
  shows "Re (z1 * z2 * z3) = Re z1 * Re z2 * Re z3"
  using assms
  by (metis Re_mult_real mult_reals)

lemma sgn_sqrt [simp]: 
  shows "sgn (sqrt x) = sgn x"
  by (simp add: sgn_root sqrt_def)

lemma real_circle_sgn_r:
  assumes "is_circle H" and "(a, r) = euclidean_circle H"
  shows "sgn r = - circline_type H"
  using assms
proof (transfer, transfer)
  fix H :: complex_mat and a r
  assume hh: "hermitean H \<and> H \<noteq> mat_zero"
  obtain A B C D where HH: "H = (A, B, C, D)"
    by (cases H) auto
  hence "is_real A" "is_real D"
    using hermitean_elems hh
    by auto
  assume "\<not> circline_A0_cmat H" "(a, r) = euclidean_circle_cmat H"
  hence "A \<noteq> 0"
    using \<open>\<not> circline_A0_cmat H\<close> HH
    by simp
  hence "Re A * Re A > 0"
    using \<open>is_real A\<close>
    using complex_eq_if_Re_eq not_real_square_gt_zero
    by fastforce
  thus "sgn r = - circline_type_cmat H"
    using HH \<open>(a, r) = euclidean_circle_cmat H\<close> \<open>is_real A\<close> \<open>is_real D\<close> \<open>A \<noteq> 0\<close>
    by (simp add: Re_divide_real sgn_minus[symmetric])
qed

text \<open>The definition of an angle using algebraic terms is not intuitive, and we want to connect it to
the more common definition given earlier that defines an
angle between circlines as the angle between tangent vectors in the point of the intersection of the
circlines.\<close>

lemma cos_angle_eq_cos_ang_circ:
  assumes
  "is_circle (of_ocircline H1)" and "is_circle (of_ocircline H2)" and
  "circline_type (of_ocircline H1) < 0" and "circline_type (of_ocircline H2) < 0"
  "(a1, r1) = euclidean_circle (of_ocircline H1)" and "(a2, r2) = euclidean_circle (of_ocircline H2)" and
  "of_complex E \<in> ocircline_set H1 \<inter> ocircline_set H2"
  shows "cos_angle H1 H2 = cos (ang_circ E a1 a2 (pos_oriented H1) (pos_oriented H2))"
proof-
  let ?p1 = "pos_oriented H1" and ?p2 = "pos_oriented H2"
  have "E \<in> circle a1 r1" "E \<in> circle a2 r2"
    using classic_circle[of "of_ocircline H1" a1 r1]  classic_circle[of "of_ocircline H2" a2 r2]
    using assms of_complex_inj
    by auto
  hence *: "cdist E a1 = r1" "cdist E a2 = r2"
    unfolding circle_def
    by (simp_all add: norm_minus_commute)
  have "r1 > 0" "r2 > 0"
    using assms(1-6) real_circle_sgn_r[of "of_ocircline H1" a1 r1]  real_circle_sgn_r[of "of_ocircline H2" a2 r2]
    using sgn_greater 
    by fastforce+
  hence "E \<noteq> a1" "E \<noteq> a2"
    using \<open>cdist E a1 = r1\<close> \<open>cdist E a2 = r2\<close>
    by auto

  let ?k = "sgn_bool (?p1 = ?p2)"
  let ?xx = "?k * (r1\<^sup>2 + r2\<^sup>2 - (cdist a2 a1)\<^sup>2) / (2 * r1 * r2)"

  have "cos (ang_circ E a1 a2 ?p1 ?p2) = ?xx"
    using law_of_cosines[of a2 a1 E] * \<open>r1 > 0\<close> \<open>r2 > 0\<close> cos_ang_circ_simp[OF \<open>E \<noteq> a1\<close> \<open>E \<noteq> a2\<close>]
    by (subst (asm) ang_vec_opposite_opposite'[OF \<open>E \<noteq> a1\<close>[symmetric] \<open>E \<noteq> a2\<close>[symmetric], symmetric]) simp
  moreover
  have "cos_angle H1 H2 = ?xx"
    using \<open>r1 > 0\<close> \<open>r2 > 0\<close>
    using \<open>(a1, r1) = euclidean_circle (of_ocircline H1)\<close> \<open>(a2, r2) = euclidean_circle (of_ocircline H2)\<close>
    using \<open>is_circle (of_ocircline H1)\<close> \<open>is_circle (of_ocircline H2)\<close>
    using \<open>circline_type (of_ocircline H1) < 0\<close> \<open>circline_type (of_ocircline H2) < 0\<close>
  proof (transfer, transfer)
    fix a1 r1 H1 H2 a2 r2
    assume hh: "hermitean H1 \<and> H1 \<noteq> mat_zero" "hermitean H2 \<and> H2 \<noteq> mat_zero"
    obtain A1 B1 C1 D1 where HH1: "H1 = (A1, B1, C1, D1)"
      by (cases H1) auto
    obtain A2 B2 C2 D2 where HH2: "H2 = (A2, B2, C2, D2)"
      by (cases H2) auto
    have *: "is_real A1" "is_real A2" "is_real D1" "is_real D2" "cnj B1 = C1" "cnj B2 = C2"
      using hh hermitean_elems[of A1 B1 C1 D1] hermitean_elems[of A2 B2 C2 D2] HH1 HH2
      by auto
    have "cnj A1 = A1" "cnj A2 = A2"
      using \<open>is_real A1\<close> \<open>is_real A2\<close>
      by (case_tac[!] A1, case_tac[!] A2, auto simp add: Complex_eq)

    assume "\<not> circline_A0_cmat (id H1)" "\<not> circline_A0_cmat (id H2)"
    hence "A1 \<noteq> 0" "A2 \<noteq> 0"
      using HH1 HH2
      by auto
    hence "Re A1 \<noteq> 0" "Re A2 \<noteq> 0"
      using \<open>is_real A1\<close> \<open>is_real A2\<close>
      using complex.expand
      by auto

    assume "circline_type_cmat (id H1) < 0" "circline_type_cmat (id H2) < 0"
    assume "(a1, r1) = euclidean_circle_cmat (id H1)" "(a2, r2) = euclidean_circle_cmat (id H2)"
    assume "r1 > 0" "r2 > 0"

    let ?D12 = "mat_det_12 H1 H2" and ?D1 = "mat_det H1" and ?D2 = "mat_det H2"
    let ?x1 = "(cdist a2 a1)\<^sup>2 - r1\<^sup>2 - r2\<^sup>2" and ?x2 = "2*r1*r2"
    let ?x = "?x1 / ?x2"
    have *:  "Re (?D12) / (2 * (sqrt (Re (?D1 * ?D2)))) = Re (sgn A1) * Re (sgn A2) * ?x"
    proof-
      let ?M1 = "(A1, B1, C1, D1)" and ?M2 = "(A2, B2, C2, D2)"
      let ?d1 = "B1 * C1 - A1 * D1" and ?d2 = "B2 * C2 - A2 * D2"
      have "Re ?d1 > 0" "Re ?d2 > 0"
        using HH1 HH2 \<open>circline_type_cmat (id H1) < 0\<close>  \<open>circline_type_cmat (id H2) < 0\<close>
        by auto
      hence **: "Re (?d1 / (A1 * A1)) > 0" "Re (?d2 / (A2 * A2)) > 0"
        using \<open>is_real A1\<close> \<open>is_real A2\<close> \<open>A1 \<noteq> 0\<close> \<open>A2 \<noteq> 0\<close>
        by (subst Re_divide_real, simp_all add: complex_neq_0 power2_eq_square)+
      have ***: "is_real (?d1 / (A1 * A1)) \<and> is_real (?d2 / (A2 * A2))"
        using \<open>is_real A1\<close>  \<open>is_real A2\<close> \<open>A1 \<noteq> 0\<close> \<open>A2 \<noteq> 0\<close> \<open>cnj B1 = C1\<close>[symmetric] \<open>cnj B2 = C2\<close>[symmetric] \<open>is_real D1\<close> \<open>is_real D2\<close>
        by (subst div_reals, simp, simp, simp)+

      have "cor ?x = mat_det_12 ?M1 ?M2 / (2 * sgn A1 * sgn A2 * cor (sqrt (Re ?d1) * sqrt (Re ?d2)))"
      proof-
        have "A1*A2*cor ?x1 = mat_det_12 ?M1 ?M2"
        proof-
          have 1: "A1*A2*(cor ((cdist a2 a1)\<^sup>2)) = ((B2*A1 - A2*B1)*(C2*A1 - C1*A2)) / (A1*A2)"
            using \<open>(a1, r1) = euclidean_circle_cmat (id H1)\<close> \<open>(a2, r2) = euclidean_circle_cmat (id H2)\<close>
            unfolding cdist_def cmod_square
            using HH1 HH2 * \<open>A1 \<noteq> 0\<close> \<open>A2 \<noteq> 0\<close> \<open>cnj A1 = A1\<close> \<open>cnj A2 = A2\<close>
            unfolding Let_def
            apply (subst complex_of_real_Re)
            apply (simp add: field_simps)
            apply (simp add: complex_mult_cnj_cmod power2_eq_square)
            apply (simp add: field_simps)
            done
          have 2: "A1*A2*cor (-r1\<^sup>2) = A2*D1 - B1*C1*A2/A1"
            using \<open>(a1, r1) = euclidean_circle_cmat (id H1)\<close>
            using HH1 ** * *** \<open>A1 \<noteq> 0\<close>
            by (simp add: power2_eq_square field_simps)
          have 3: "A1*A2*cor (-r2\<^sup>2) = A1*D2 - B2*C2*A1/A2"
            using \<open>(a2, r2) = euclidean_circle_cmat (id H2)\<close>
            using HH2 ** * *** \<open>A2 \<noteq> 0\<close>
            by (simp add: power2_eq_square field_simps)
          have "A1*A2*cor((cdist a2 a1)\<^sup>2) + A1*A2*cor(-r1\<^sup>2) + A1*A2*cor(-r2\<^sup>2) = mat_det_12 ?M1 ?M2"
            using \<open>A1 \<noteq> 0\<close> \<open>A2 \<noteq> 0\<close>
            by (subst 1, subst 2, subst 3) (simp add: field_simps)
          thus ?thesis
            by (simp add: field_simps)
        qed

        moreover

        have "A1 * A2 * cor (?x2) = 2 * sgn A1 * sgn A2 * cor (sqrt (Re ?d1) * sqrt (Re ?d2))"
        proof-
          have 1: "sqrt (Re (?d1/ (A1 * A1))) = sqrt (Re ?d1) / \<bar>Re A1\<bar>"
            using \<open>A1 \<noteq> 0\<close> \<open>is_real A1\<close>
            by (subst Re_divide_real, simp, simp, subst real_sqrt_divide, simp)

          have 2: "sqrt (Re (?d2/ (A2 * A2))) = sqrt (Re ?d2) / \<bar>Re A2\<bar>"
            using \<open>A2 \<noteq> 0\<close> \<open>is_real A2\<close>
            by (subst Re_divide_real, simp, simp, subst real_sqrt_divide, simp)
          have "sgn A1 = A1 / cor \<bar>Re A1\<bar>"
            using \<open>is_real A1\<close>
            unfolding sgn_eq
            by (simp add: cmod_eq_Re)
          moreover
          have "sgn A2 = A2 / cor \<bar>Re A2\<bar>"
            using \<open>is_real A2\<close>
            unfolding sgn_eq
            by (simp add: cmod_eq_Re)
          ultimately
          show ?thesis
            using \<open>(a1, r1) = euclidean_circle_cmat (id H1)\<close> \<open>(a2, r2) = euclidean_circle_cmat (id H2)\<close>  HH1 HH2
            using *** \<open>is_real A1\<close> \<open>is_real A2\<close>
            by simp (subst 1, subst 2, simp)
        qed

        ultimately

        have "(A1 * A2 * cor ?x1) / (A1 * A2 * (cor ?x2)) =
               mat_det_12 ?M1 ?M2 / (2 * sgn A1 * sgn A2 * cor (sqrt (Re ?d1) * sqrt (Re ?d2)))"
          by simp
        thus ?thesis
          using \<open>A1 \<noteq> 0\<close> \<open>A2 \<noteq> 0\<close>
          by simp
      qed
      hence "cor ?x * sgn A1 * sgn A2 = mat_det_12 ?M1 ?M2 / (2 * cor (sqrt (Re ?d1) * sqrt (Re ?d2)))"
        using \<open>A1 \<noteq> 0\<close> \<open>A2 \<noteq> 0\<close>
        by (simp add: sgn_zero_iff)
      moreover
      have "Re (cor ?x * sgn A1 * sgn A2) = Re (sgn A1) * Re (sgn A2) * ?x"
      proof-
        have "is_real (cor ?x)" "is_real (sgn A1)" "is_real (sgn A2)"
          using \<open>is_real A1\<close> \<open>is_real A2\<close> Im_complex_of_real[of ?x]
          by auto
        thus ?thesis
          using Re_complex_of_real[of ?x]
          by (subst Re_mult_real3, auto simp add: field_simps)
      qed
      moreover
      have *: "sqrt (Re ?D1) * sqrt (Re ?D2) = sqrt (Re ?d1) * sqrt (Re ?d2)"
        using HH1 HH2
        by (subst real_sqrt_mult[symmetric])+ (simp add: field_simps)
      have "2 * (sqrt (Re (?D1 * ?D2))) \<noteq> 0"
        using \<open>Re ?d1 > 0\<close>  \<open>Re ?d2 > 0\<close> HH1 HH2 \<open>is_real A1\<close> \<open>is_real A2\<close>  \<open>is_real D1\<close> \<open>is_real D2\<close>
        using hh mat_det_hermitean_real[of "H1"]
        by (subst Re_mult_real, auto)
      hence **: "Re (?D12 / (2 * cor (sqrt (Re (?D1 * ?D2))))) = Re (?D12) / (2 * (sqrt (Re (?D1 * ?D2))))"
        using \<open>Re ?d1 > 0\<close>  \<open>Re ?d2 > 0\<close> HH1 HH2 \<open>is_real A1\<close> \<open>is_real A2\<close>  \<open>is_real D1\<close> \<open>is_real D2\<close>
        by (subst Re_divide_real) auto
      have "Re (mat_det_12 ?M1 ?M2 / (2 * cor (sqrt (Re ?d1) * sqrt (Re ?d2)))) = Re (?D12) / (2 * (sqrt (Re (?D1 * ?D2))))"
        using HH1 HH2 hh mat_det_hermitean_real[of "H1"]
        by (subst **[symmetric], subst Re_mult_real, simp, subst real_sqrt_mult, subst *, simp)
      ultimately
      show ?thesis
        by simp
    qed
    have **: "pos_oriented_cmat H1 \<longleftrightarrow> Re A1 > 0"  "pos_oriented_cmat H2 \<longleftrightarrow> Re A2 > 0"
      using \<open>Re A1 \<noteq> 0\<close> HH1  \<open>Re A2 \<noteq> 0\<close> HH2
      by auto
    show "cos_angle_cmat H1 H2 = sgn_bool (pos_oriented_cmat H1 = pos_oriented_cmat H2) * (r1\<^sup>2 + r2\<^sup>2 - (cdist a2 a1)\<^sup>2) /  (2 * r1 * r2)"
      unfolding Let_def
      using \<open>r1 > 0\<close> \<open>r2 > 0\<close>
      unfolding cos_angle_cmat_def
      apply (subst divide_minus_left)
      apply (subst *)
      apply (subst Re_sgn[OF \<open>is_real A1\<close> \<open>A1 \<noteq> 0\<close>], subst Re_sgn[OF \<open>is_real A2\<close> \<open>A2 \<noteq> 0\<close>])
      apply (subst **, subst **)
      apply (simp add: field_simps)
      done
  qed
  ultimately
  show ?thesis
    by simp
qed

(* ----------------------------------------------------------------- *)
subsection \<open>Perpendicularity\<close>
(* ----------------------------------------------------------------- *)

text \<open>Two circlines are perpendicular if the intersect at right angle i.e., the angle with the cosine
0.\<close>

definition perpendicular where
  "perpendicular H1 H2 \<longleftrightarrow> cos_angle (of_circline H1) (of_circline H2) = 0"

lemma perpendicular_sym:
  shows "perpendicular H1 H2 \<longleftrightarrow> perpendicular H2 H1"
  unfolding perpendicular_def
  by (transfer, transfer, auto simp add: field_simps)

(* ----------------------------------------------------------------- *)
subsection \<open>Möbius transforms preserve angles and perpendicularity\<close>
(* ----------------------------------------------------------------- *)

text \<open>Möbius transformations are \emph{conformal} i.e., they preserve angles between circlines.\<close>

lemma moebius_preserve_circline_angle [simp]:
  shows "cos_angle (moebius_ocircline M H1) (moebius_ocircline M H2) =
         cos_angle H1 H2 "
proof (transfer, transfer)
  fix H1 H2 M :: complex_mat
  assume hh: "mat_det M \<noteq> 0"
  show "cos_angle_cmat (moebius_circline_cmat_cmat M H1) (moebius_circline_cmat_cmat M H2) = cos_angle_cmat H1 H2"
    unfolding cos_angle_cmat_def moebius_circline_cmat_cmat_def
    unfolding Let_def mat_det_12_congruence mat_det_congruence
    using hh mat_det_inv[of M]
    apply (subst cor_squared[symmetric])+
    apply (subst cos_angle_den_scale, simp)
    apply (auto simp add: power2_eq_square real_sqrt_mult field_simps)
    done
qed

lemma perpendicular_moebius [simp]:
  assumes "perpendicular H1 H2"
  shows "perpendicular (moebius_circline M H1) (moebius_circline M H2)"
  using assms
  unfolding perpendicular_def
  using moebius_preserve_circline_angle[of M "of_circline H1" "of_circline H2"]
  using moebius_ocircline_circline[of M "of_circline H1"]
  using moebius_ocircline_circline[of M "of_circline H2"]
  by (auto simp del: moebius_preserve_circline_angle)

end
