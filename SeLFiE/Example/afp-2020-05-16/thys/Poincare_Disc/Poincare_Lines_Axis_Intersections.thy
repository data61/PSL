theory Poincare_Lines_Axis_Intersections
  imports Poincare_Between
begin

(* ------------------------------------------------------------------ *)
section\<open>Intersection of h-lines with the x-axis in the Poincar\'e model\<close>
(* ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------- *)
subsection\<open>Betweeness of x-axis intersection\<close>
(* ---------------------------------------------------------------- *)

text\<open>The intersection point of the h-line determined by points $u$ and $v$ and the x-axis is between
$u$ and $v$, then $u$ and $v$ are in the opposite half-planes (one must be in the upper, and the
other one in the lower half-plane).\<close>

lemma poincare_between_x_axis_intersection:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc" and "z \<in> unit_disc" and "u \<noteq> v"
  assumes "u \<notin> circline_set x_axis" and "v \<notin> circline_set x_axis"
  assumes "z \<in> circline_set (poincare_line u v) \<inter> circline_set x_axis"
  shows "poincare_between u z v \<longleftrightarrow> arg (to_complex u) * arg (to_complex v) < 0"
proof-
  have "\<forall> u v. u \<in> unit_disc \<and> v \<in> unit_disc \<and> u \<noteq> v \<and>
       u \<notin> circline_set x_axis \<and> v \<notin> circline_set x_axis \<and> 
       z \<in> circline_set (poincare_line u v) \<inter> circline_set x_axis \<longrightarrow> 
       (poincare_between u z v \<longleftrightarrow> arg (to_complex u) * arg (to_complex v) < 0)" (is "?P z")
  proof (rule wlog_real_zero)
    show "?P 0\<^sub>h"
    proof ((rule allI)+, rule impI, (erule conjE)+)
      fix u v
      assume *: "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
                "u \<notin> circline_set x_axis" "v \<notin> circline_set x_axis"
                "0\<^sub>h \<in> circline_set (poincare_line u v) \<inter> circline_set x_axis"
      obtain u' v' where uv: "u = of_complex u'" "v = of_complex v'"
        using * inf_or_of_complex[of u] inf_or_of_complex[of v]
        by auto

       
      hence "u \<noteq> 0\<^sub>h" "v \<noteq> 0\<^sub>h" "u' \<noteq> 0" "v' \<noteq> 0"
        using *
        by auto

      hence "arg u' \<noteq> 0" "arg v' \<noteq> 0"
        using * arg_0_iff[of u'] arg_0_iff[of v']
        unfolding circline_set_x_axis uv
        by auto

      have "poincare_collinear {0\<^sub>h, u, v}"
        using *
        unfolding poincare_collinear_def
        by (rule_tac x="poincare_line u v" in exI, simp)
      have "(\<exists>k<0. u' = cor k * v') \<longleftrightarrow> (arg u' * arg v' < 0)" (is "?lhs \<longleftrightarrow> ?rhs")
      proof
        assume "?lhs"
        then obtain k where "k < 0" "u' = cor k * v'"
          by auto
        thus ?rhs
          using arg_mult_real_negative[of k v'] arg_uminus_opposite_sign[of v']
          using \<open>u' \<noteq> 0\<close> \<open>v' \<noteq> 0\<close> \<open>arg u' \<noteq> 0\<close> \<open>arg v' \<noteq> 0\<close>
          by (auto simp add: mult_neg_pos mult_pos_neg)
      next
        assume ?rhs
        obtain ru rv \<phi> where polar: "u' = cor ru * cis \<phi>" "v' = cor rv * cis \<phi>"
          using \<open>poincare_collinear {0\<^sub>h, u, v}\<close> poincare_collinear_zero_polar_form[of u' v'] uv * \<open>u' \<noteq> 0\<close> \<open>v' \<noteq> 0\<close>
          by auto
        have "ru * rv < 0"
          using polar \<open>?rhs\<close> \<open>u' \<noteq> 0\<close> \<open>v' \<noteq> 0\<close>
          using arg_mult_real_negative[of "ru" "cis \<phi>"] arg_mult_real_positive[of "ru" "cis \<phi>"]
          using arg_mult_real_negative[of "rv" "cis \<phi>"] arg_mult_real_positive[of "rv" "cis \<phi>"]
          apply (cases "ru > 0")
          apply (cases "rv > 0", simp, simp add: mult_pos_neg)
          apply (cases "rv > 0", simp add: mult_neg_pos, simp)
          done
        thus "?lhs"
          using polar     
          by (rule_tac x="ru / rv" in exI, auto simp add: divide_less_0_iff mult_less_0_iff)
      qed
      thus "poincare_between u 0\<^sub>h v = (arg (to_complex u) * arg (to_complex v) < 0)"
        using poincare_between_u0v[of u v] * \<open>u \<noteq> 0\<^sub>h\<close> \<open>v \<noteq> 0\<^sub>h\<close> uv
        by simp
    qed
  next
    fix a z 
    assume 1: "is_real a" "cmod a < 1" "z \<in> unit_disc"
    assume 2: "?P (moebius_pt (blaschke a) z)"
    show "?P z"
    proof ((rule allI)+, rule impI, (erule conjE)+)
      fix u v
      let ?M = "moebius_pt (blaschke a)"
      let ?Mu = "?M u"
      let ?Mv = "?M v"
      assume *: "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v" "u \<notin> circline_set x_axis" "v \<notin> circline_set x_axis"
      hence "u \<noteq> \<infinity>\<^sub>h" "v \<noteq> \<infinity>\<^sub>h"
        by auto

      have **: "\<And> x y :: real. x * y < 0 \<longleftrightarrow> sgn (x * y) < 0"
        by simp

      assume "z \<in> circline_set (poincare_line u v) \<inter> circline_set x_axis"
      thus "poincare_between u z v = (arg (to_complex u) * arg (to_complex v) < 0)"
        using * 1 2[rule_format, of ?Mu ?Mv] \<open>cmod a < 1\<close> \<open>is_real a\<close> blaschke_unit_disc_fix[of a]
        using inversion_noteq_unit_disc[of "of_complex a" u] \<open>u \<noteq> \<infinity>\<^sub>h\<close>
        using inversion_noteq_unit_disc[of "of_complex a" v] \<open>v \<noteq> \<infinity>\<^sub>h\<close>
        apply auto
        apply (subst (asm) **, subst **, subst (asm) sgn_mult, subst sgn_mult, simp)
        apply (subst (asm) **, subst (asm) **, subst (asm) sgn_mult, subst (asm) sgn_mult, simp)
        done
    qed
  next
    show "z \<in> unit_disc" by fact
  next
    show "is_real (to_complex z)"
      using assms inf_or_of_complex[of z]
      by (auto simp add: circline_set_x_axis)
  qed
  thus ?thesis
    using assms
    by simp
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Check if an h-line intersects the x-axis\<close>
(* ------------------------------------------------------------------ *)

lemma x_axis_intersection_equation:
  assumes
   "H = mk_circline A B C D" and
   "(A, B, C, D) \<in> hermitean_nonzero"
 shows "of_complex z \<in> circline_set x_axis \<inter> circline_set H \<longleftrightarrow>
        A*z\<^sup>2 + 2*Re B*z + D = 0 \<and> is_real z" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  have "?lhs \<longleftrightarrow> A*z\<^sup>2 + (B + cnj B)*z + D = 0 \<and> z = cnj z"
    using assms
    using circline_equation_x_axis[of z]
    using circline_equation[of H A B C D z]
    using hermitean_elems
    by (auto simp add: power2_eq_square field_simps)
  thus ?thesis
    using eq_cnj_iff_real[of z]
    using hermitean_elems[of A B C D]
    by (simp add: complex_add_cnj complex_eq_if_Re_eq)
qed

text \<open>Check if an h-line intersects x-axis within the unit disc - this could be generalized to
checking if an arbitrary circline intersects the x-axis, but we do not need that.\<close>

definition intersects_x_axis_cmat :: "complex_mat \<Rightarrow> bool" where
  [simp]: "intersects_x_axis_cmat H = (let (A, B, C, D) = H in A = 0 \<or> (Re B)\<^sup>2 > (Re A)\<^sup>2)"

lift_definition intersects_x_axis_clmat :: "circline_mat \<Rightarrow> bool" is intersects_x_axis_cmat
  done

lift_definition intersects_x_axis :: "circline \<Rightarrow> bool" is intersects_x_axis_clmat
proof (transfer)
  fix H1 H2
  assume hh: "hermitean H1 \<and> H1 \<noteq> mat_zero" and "hermitean H2 \<and> H2 \<noteq> mat_zero"
  obtain A1 B1 C1 D1 A2 B2 C2 D2 where *: "H1 = (A1, B1, C1, D1)" "H2 = (A2, B2, C2, D2)"
    by (cases H1, cases H2, auto)
  assume "circline_eq_cmat H1 H2"
  then obtain k where k: "k \<noteq> 0 \<and> H2 = cor k *\<^sub>s\<^sub>m H1"
    by auto
  show "intersects_x_axis_cmat H1 = intersects_x_axis_cmat H2"
  proof-
    have "k \<noteq> 0 \<Longrightarrow> (Re A1)\<^sup>2 < (Re B1)\<^sup>2 \<longleftrightarrow> (k * Re A1)\<^sup>2 < (k * Re B1)\<^sup>2"
      by (smt mult_strict_left_mono power2_eq_square semiring_normalization_rules(13) zero_less_power2)
    thus ?thesis
      using * k
      by auto
  qed
qed

lemma intersects_x_axis_mk_circline:
  assumes "is_real A" and "A \<noteq> 0 \<or> B \<noteq> 0"
  shows "intersects_x_axis (mk_circline A B (cnj B) A) \<longleftrightarrow> A = 0 \<or> (Re B)\<^sup>2 > (Re A)\<^sup>2"
proof-
  let ?H = "(A, B, (cnj B),  A)"
  have "hermitean ?H"                
    using `is_real A` 
    unfolding hermitean_def mat_adj_def mat_cnj_def
    using eq_cnj_iff_real 
    by auto
  moreover
  have "?H \<noteq> mat_zero"
    using assms
    by auto
  ultimately
  show ?thesis
    by (transfer, transfer, auto simp add: Let_def)
qed

lemma intersects_x_axis_iff:
  assumes "is_poincare_line H"
  shows "(\<exists> x \<in> unit_disc. x \<in> circline_set H \<inter> circline_set x_axis) \<longleftrightarrow> intersects_x_axis H"
proof-
  obtain Ac B C Dc where  *: "H = mk_circline Ac B C Dc" "hermitean (Ac, B, C, Dc)" "(Ac, B, C, Dc) \<noteq> mat_zero"
    using ex_mk_circline[of H]
    by auto
  hence "(cmod B)\<^sup>2 > (cmod Ac)\<^sup>2" "Ac = Dc"
    using assms
    using is_poincare_line_mk_circline
    by auto

  hence "H = mk_circline (Re Ac) B (cnj B) (Re Ac)" "hermitean (cor (Re Ac),  B, (cnj B), cor (Re Ac))" "(cor (Re Ac),  B, (cnj B), cor (Re Ac)) \<noteq> mat_zero"
    using hermitean_elems[of Ac B C Dc] *
    by auto
  then obtain A where
    *: "H = mk_circline (cor A) B (cnj B) (cor A)" "(cor A,  B, (cnj B), cor A) \<in> hermitean_nonzero"
    by auto

  show ?thesis
  proof (cases "A = 0")
    case True
    thus ?thesis
      using *
      using x_axis_intersection_equation[OF *(1-2), of 0]
      using intersects_x_axis_mk_circline[of "cor A" B]
      by auto
  next
    case False
    show ?thesis
    proof
      assume "\<exists> x \<in> unit_disc. x \<in> circline_set H \<inter> circline_set x_axis"
      then obtain x where **: "of_complex x \<in> unit_disc" "of_complex x \<in> circline_set H \<inter> circline_set x_axis"
        by (metis inf_or_of_complex inf_notin_unit_disc)
      hence "is_real x"
        unfolding circline_set_x_axis
        using of_complex_inj
        by auto
      hence eq: "A * (Re x)\<^sup>2 + 2 * Re B * Re x + A = 0"
        using **
        using x_axis_intersection_equation[OF *(1-2), of "Re x"]
        by simp
      hence "(2 * Re B)\<^sup>2 - 4 * A * A \<ge> 0"
        using discriminant_iff[of A _ "2 * Re B" A]
        using discrim_def[of A "2 * Re B" A] False
        by auto
      hence "(Re B)\<^sup>2 \<ge> (Re A)\<^sup>2"
        by (simp add: power2_eq_square)
      moreover
      have "(Re B)\<^sup>2 \<noteq> (Re A)\<^sup>2"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence "Re B = Re A \<or> Re B = - Re A"
          using power2_eq_iff by blast
        hence "A * (Re x)\<^sup>2 +  A * 2* Re x + A = 0 \<or> A * (Re x)\<^sup>2 - A * 2 * Re x + A = 0"
          using eq
          by auto
        hence "A * ((Re x)\<^sup>2 +  2* Re x + 1) = 0 \<or> A * ((Re x)\<^sup>2 - 2 * Re x + 1) = 0"
          by (simp add: field_simps)
        hence "(Re x)\<^sup>2 + 2 * Re x + 1 = 0 \<or> (Re x)\<^sup>2 - 2 * Re x + 1 = 0"
          using \<open>A \<noteq> 0\<close>
          by simp
        hence "(Re x + 1)\<^sup>2 = 0 \<or> (Re x - 1)\<^sup>2 = 0"
          by (simp add: power2_sum power2_diff field_simps)
        hence "Re x = -1 \<or> Re x = 1"
          by auto
        thus False
          using \<open>is_real x\<close> \<open>of_complex x \<in> unit_disc\<close>
          by (auto simp add: cmod_eq_Re)
      qed
      ultimately
      show "intersects_x_axis H"
        using intersects_x_axis_mk_circline
        using *
        by auto
    next
      assume "intersects_x_axis H"
      hence "(Re B)\<^sup>2 > (Re A)\<^sup>2"
        using * False
        using intersects_x_axis_mk_circline
        by simp
      hence discr: "(2 * Re B)\<^sup>2 - 4 * A * A > 0"
        by (simp add: power2_eq_square)
      then obtain x1 x2 where
        eqs: "A * x1\<^sup>2 + 2 * Re B * x1 + A = 0" "A * x2\<^sup>2 + 2 * Re B * x2 + A = 0" "x1 \<noteq> x2"
        using discriminant_pos_ex[OF \<open>A \<noteq> 0\<close>, of "2 * Re B" A]
        using discrim_def[of A "2 * Re B" A]
        by auto
      hence "x1 * x2 = 1"
        using viette2[OF \<open>A \<noteq> 0\<close>, of "2 * Re B" A x1 x2] discr \<open>A \<noteq> 0\<close>
        by auto
      have "abs x1 \<noteq> 1" "abs x2 \<noteq> 1"
        using eqs discr \<open>x1 * x2 = 1\<close>
        by (auto simp add: abs_if power2_eq_square)
      hence "abs x1 < 1 \<or> abs x2 < 1"
        using \<open>x1 * x2 = 1\<close>
        by (smt mult_le_cancel_left1 mult_minus_right)
      thus "\<exists>x \<in> unit_disc. x \<in> circline_set H \<inter> circline_set x_axis"
        using x_axis_intersection_equation[OF *(1-2), of x1]
        using x_axis_intersection_equation[OF *(1-2), of x2]
        using eqs
        by auto
    qed
  qed
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Check if a Poincar\'e line intersects the y-axis\<close>
(* ------------------------------------------------------------------ *)

definition intersects_y_axis_cmat :: "complex_mat \<Rightarrow> bool" where
  [simp]: "intersects_y_axis_cmat H = (let (A, B, C, D) = H in A = 0 \<or> (Im B)\<^sup>2 > (Re A)\<^sup>2)"

lift_definition intersects_y_axis_clmat :: "circline_mat \<Rightarrow> bool" is intersects_y_axis_cmat
  done

lift_definition intersects_y_axis :: "circline \<Rightarrow> bool" is intersects_y_axis_clmat
proof (transfer)
  fix H1 H2
  assume hh: "hermitean H1 \<and> H1 \<noteq> mat_zero" and "hermitean H2 \<and> H2 \<noteq> mat_zero"
  obtain A1 B1 C1 D1 A2 B2 C2 D2 where *: "H1 = (A1, B1, C1, D1)" "H2 = (A2, B2, C2, D2)"
    by (cases H1, cases H2, auto)
  assume "circline_eq_cmat H1 H2"
  then obtain k where k: "k \<noteq> 0 \<and> H2 = cor k *\<^sub>s\<^sub>m H1"
    by auto
  show "intersects_y_axis_cmat H1 = intersects_y_axis_cmat H2"
  proof-
    have "k \<noteq> 0 \<Longrightarrow> (Re A1)\<^sup>2 < (Im B1)\<^sup>2 \<longleftrightarrow> (k * Re A1)\<^sup>2 < (k * Im B1)\<^sup>2"
      by (smt mult_strict_left_mono power2_eq_square semiring_normalization_rules(13) zero_less_power2)
    thus ?thesis
      using * k
      by auto
  qed
qed

lemma intersects_x_axis_intersects_y_axis [simp]:
  shows "intersects_x_axis (moebius_circline (moebius_rotation (pi/2)) H) \<longleftrightarrow> intersects_y_axis H"
  unfolding moebius_rotation_def moebius_similarity_def
  by simp (transfer, transfer, auto simp add: mat_adj_def mat_cnj_def)

lemma intersects_y_axis_iff:
  assumes "is_poincare_line H"
  shows "(\<exists> y \<in> unit_disc. y \<in> circline_set H \<inter> circline_set y_axis) \<longleftrightarrow> intersects_y_axis H" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  let ?R = "moebius_rotation (pi / 2)"
  let ?H' = "moebius_circline ?R H"
  have 1: "is_poincare_line ?H'"
    using assms
    using unit_circle_fix_preserve_is_poincare_line[OF _ assms, of ?R]
    by simp

  show ?thesis
  proof
    assume "?lhs"
    then obtain y where "y \<in> unit_disc" "y \<in> circline_set H \<inter> circline_set y_axis"
      by auto
    hence "moebius_pt ?R y \<in> unit_disc \<and> moebius_pt ?R y \<in> circline_set ?H' \<inter> circline_set x_axis"
      using rotation_pi_2_y_axis
      by (metis Int_iff circline_set_moebius_circline_E moebius_circline_comp_inv_left moebius_pt_comp_inv_left unit_disc_fix_discI unit_disc_fix_rotation)
    thus ?rhs
      using intersects_x_axis_iff[OF 1]
      using intersects_x_axis_intersects_y_axis[of H]
      by auto
  next
    assume "intersects_y_axis H"
    hence "intersects_x_axis ?H'"
      using intersects_x_axis_intersects_y_axis[of H]
      by simp
    then obtain x where *: "x \<in> unit_disc" "x \<in> circline_set ?H' \<inter> circline_set x_axis"
      using intersects_x_axis_iff[OF 1]
      by auto
    let ?y = "moebius_pt (-?R) x"
    have "?y \<in> unit_disc \<and> ?y \<in> circline_set H \<inter> circline_set y_axis"
      using * rotation_pi_2_y_axis[symmetric]
      by (metis Int_iff circline_set_moebius_circline_E moebius_pt_comp_inv_left moebius_rotation_uminus uminus_moebius_def unit_disc_fix_discI unit_disc_fix_rotation)
    thus ?lhs
      by auto
  qed
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Intersection point of a Poincar\'e line with the x-axis in the unit disc\<close>
(* ------------------------------------------------------------------ *)

definition calc_x_axis_intersection_cvec :: "complex \<Rightarrow> complex \<Rightarrow> complex_vec" where
 [simp]:  "calc_x_axis_intersection_cvec A B =
    (let discr = (Re B)\<^sup>2 - (Re A)\<^sup>2 in
         (-Re(B) + sgn (Re B) * sqrt(discr), A))"

(* intersection with the x-axis for poincare lines that are euclidean circles *)
definition calc_x_axis_intersection_cmat_cvec :: "complex_mat \<Rightarrow> complex_vec" where [simp]:
  "calc_x_axis_intersection_cmat_cvec H =
    (let (A, B, C, D) = H in 
       if A \<noteq> 0 then
          calc_x_axis_intersection_cvec A B
       else
          (0, 1)
    )"

lift_definition calc_x_axis_intersection_clmat_hcoords :: "circline_mat \<Rightarrow> complex_homo_coords" is calc_x_axis_intersection_cmat_cvec
  by (auto split: if_split_asm)

lift_definition calc_x_axis_intersection :: "circline \<Rightarrow> complex_homo" is calc_x_axis_intersection_clmat_hcoords
proof transfer
  fix H1 H2
  assume *: "hermitean H1 \<and> H1 \<noteq> mat_zero" "hermitean H2 \<and> H2 \<noteq> mat_zero"
  obtain A1 B1 C1 D1 A2 B2 C2 D2 where hh: "H1 = (A1, B1, C1, D1)" "H2 = (A2, B2, C2, D2)"
    by (cases H1, cases H2, auto)
  assume "circline_eq_cmat H1 H2"
  then obtain k where k: "k \<noteq> 0" "H2 = cor k *\<^sub>s\<^sub>m H1"
    by auto

  have "calc_x_axis_intersection_cvec A1 B1 \<approx>\<^sub>v calc_x_axis_intersection_cvec A2 B2"
    using hh k
    apply simp
    apply (rule_tac x="cor k" in exI)
    apply auto
    apply (simp add: sgn_mult power_mult_distrib)
    apply (subst right_diff_distrib[symmetric])
    apply (subst real_sqrt_mult)
    apply (subst cor_mult)
    by (simp add: real_sgn_eq right_diff_distrib)

  thus "calc_x_axis_intersection_cmat_cvec H1 \<approx>\<^sub>v
        calc_x_axis_intersection_cmat_cvec H2"
    using hh k
    by (auto simp del: calc_x_axis_intersection_cvec_def)
qed


lemma calc_x_axis_intersection_in_unit_disc:
  assumes "is_poincare_line H" "intersects_x_axis H"
  shows "calc_x_axis_intersection H \<in> unit_disc"
proof (cases "is_line H")
  case True
  thus ?thesis
    using assms
    unfolding unit_disc_def disc_def
    by simp (transfer, transfer, auto simp add: vec_cnj_def)
next
  case False
  thus ?thesis
    using assms
    unfolding unit_disc_def disc_def
  proof (simp, transfer, transfer)
    fix H
    assume hh: "hermitean H \<and> H \<noteq> mat_zero"
    then obtain A B D where *: "H = (A, B, cnj B, D)" "is_real A" "is_real D"
      using hermitean_elems
      by (cases H) blast
    assume "is_poincare_line_cmat H"
    hence *: "H = (A, B, cnj B, A)" "is_real A"
      using *
      by auto

    assume "\<not> circline_A0_cmat H"
    hence "A \<noteq> 0"
      using *
      by simp

    assume "intersects_x_axis_cmat H"
    hence "(Re B)\<^sup>2 > (Re A)\<^sup>2"
      using * \<open>A \<noteq> 0\<close>
      by (auto simp add: power2_eq_square complex.expand)

    hence "Re B \<noteq> 0"
      by auto

    have "Re A \<noteq> 0"
      using \<open>is_real A\<close> \<open>A \<noteq> 0\<close>
      by (auto simp add: complex.expand)

    have "sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2) < sqrt((Re B)\<^sup>2)"
      using \<open>Re A \<noteq> 0\<close>
      by (subst real_sqrt_less_iff) auto
    also have "... =  sgn (Re B) * (Re B)"
      by (smt mult_minus_right nonzero_eq_divide_eq real_sgn_eq real_sqrt_abs)
    finally
    have 1: "sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2) < sgn (Re B) * (Re B)"
      .

    have 2: "(Re B)\<^sup>2 - (Re A)\<^sup>2 < sgn (Re B) * (Re B) * sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2)"
      using \<open>(Re B)\<^sup>2 > (Re A)\<^sup>2\<close>
      using mult_strict_right_mono[OF 1, of "sqrt ((Re B)\<^sup>2 - (Re A)\<^sup>2)"]
      by simp

    have 3: "(Re B)\<^sup>2 - 2*sgn (Re B)*Re B*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2) + (Re B)\<^sup>2 - (Re A)\<^sup>2 < (Re A)\<^sup>2"
      using mult_strict_left_mono[OF 2, of 2]
      by (simp add: field_simps)

    have "(sgn (Re B))\<^sup>2 = 1"
      using \<open>Re B \<noteq> 0\<close>
      by (simp add: sgn_if)

    hence "(-Re B + sgn (Re B) * sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2))\<^sup>2 < (Re A)\<^sup>2"
      using \<open>(Re B)\<^sup>2 > (Re A)\<^sup>2\<close> 3
      by (simp add: power2_diff field_simps)

    thus "in_ocircline_cmat_cvec unit_circle_cmat (calc_x_axis_intersection_cmat_cvec H)"
      using * \<open>(Re B)\<^sup>2 > (Re A)\<^sup>2\<close>
      by (auto simp add: vec_cnj_def power2_eq_square split: if_split_asm)
  qed
qed


lemma calc_x_axis_intersection:
  assumes "is_poincare_line H" and "intersects_x_axis H"
  shows "calc_x_axis_intersection H \<in> circline_set H \<inter> circline_set x_axis"
proof (cases "is_line H")
  case True
  thus ?thesis
    using assms
    unfolding circline_set_def
    by simp (transfer, transfer, auto simp add: vec_cnj_def)
next
  case False
  thus ?thesis
    using assms
    unfolding circline_set_def
  proof (simp, transfer, transfer)
    fix H
    assume hh: "hermitean H \<and> H \<noteq> mat_zero"
    then obtain A B D where *: "H = (A, B, cnj B, D)" "is_real A" "is_real D"
      using hermitean_elems
      by (cases H) blast
    assume "is_poincare_line_cmat H"
    hence *: "H = (A, B, cnj B, A)" "is_real A"
      using *
      by auto
    assume "\<not> circline_A0_cmat H"
    hence "A \<noteq> 0"
      using *
      by auto

    assume "intersects_x_axis_cmat H"
    hence "(Re B)\<^sup>2 > (Re A)\<^sup>2"
      using * \<open>A \<noteq> 0\<close>
      by (auto simp add: power2_eq_square complex.expand)

    hence "Re B \<noteq> 0"
      by auto

    show "on_circline_cmat_cvec H (calc_x_axis_intersection_cmat_cvec H) \<and>
        on_circline_cmat_cvec x_axis_cmat (calc_x_axis_intersection_cmat_cvec H)" (is "?P1 \<and> ?P2")
    proof
      show "on_circline_cmat_cvec H (calc_x_axis_intersection_cmat_cvec H)"
      proof (cases "circline_A0_cmat H")
        case True
        thus ?thesis
          using * \<open>is_poincare_line_cmat H\<close> \<open>intersects_x_axis_cmat H\<close>
          by (simp add: vec_cnj_def)
      next
        case False
        let ?x = "calc_x_axis_intersection_cvec A B"
        let ?nom = "fst ?x" and ?den = "snd ?x"
        have x: "?x = (?nom, ?den)"
          by simp

        hence "on_circline_cmat_cvec H (calc_x_axis_intersection_cvec A B)"
        proof (subst *, subst x, subst on_circline_cmat_cvec_circline_equation)
          have "(sgn(Re B))\<^sup>2 = 1"
            using \<open>Re B \<noteq> 0\<close> sgn_pos zero_less_power2 by fastforce
          have "(sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2))\<^sup>2 = (Re B)\<^sup>2 - (Re A)\<^sup>2"
            using \<open>(Re B)\<^sup>2 > (Re A)\<^sup>2\<close>
            by simp

          have "(-(Re B) + sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2))\<^sup>2 = 
                (-(Re B))\<^sup>2 + (sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2))\<^sup>2 - 2*(Re B)*sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2)"
            by (simp add: power2_diff)
          also have "... = (Re B)*(Re B) + (sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2))\<^sup>2 - 2*(Re B)*sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2)"
            by (simp add: power2_eq_square)
          also have "... = (Re B)*(Re B) + (sgn(Re B))\<^sup>2*(sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2))\<^sup>2 - 2*(Re B)*sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2)"
            by (simp add: power_mult_distrib)
          also have "... = (Re B)*(Re B) + (Re B)\<^sup>2 - (Re A)\<^sup>2 - 2*(Re B)*sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2)"
            using \<open>(sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2))\<^sup>2 = (Re B)\<^sup>2 - (Re A)\<^sup>2\<close> \<open>(sgn(Re B))\<^sup>2 = 1\<close>
            by simp
          finally have "(-(Re B) + sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2))\<^sup>2 =
                        (Re B)*(Re B) + (Re B)\<^sup>2 - (Re A)\<^sup>2 - 2*(Re B)*sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2)"
            by simp           

          have "is_real ?nom" "is_real ?den"
            using \<open>is_real A\<close>
            by simp+
          hence "cnj (?nom) = ?nom" "cnj (?den) = ?den"
            by (simp add:eq_cnj_iff_real)+      
          hence "A*?nom*(cnj (?nom)) + B*?den*(cnj (?nom)) + (cnj B)*(cnj (?den))*?nom + A*?den*(cnj (?den))
                = A*?nom*?nom + B*?den*?nom + (cnj B)*?den*?nom + A*?den*?den"
            by auto
          also have "... = A*?nom*?nom + (B + (cnj B))*?den*?nom + A*?den*?den"
            by (simp add:field_simps)
          also have "... = A*?nom*?nom + 2*(Re B)*?den*?nom + A*?den*?den"
            by (simp add:complex_add_cnj)
          also have "... = A*?nom\<^sup>2 + 2*(Re B)*?den*?nom + A*?den*?den"
            by (simp add:power2_eq_square)
          also have "... = A*(-(Re B) + sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2))\<^sup>2
                           + 2*(Re B)*A*(-(Re B) + sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2)) + A*A*A"
            unfolding calc_x_axis_intersection_cvec_def
            by auto
          also have "... = A*((Re B)*(Re B) + (Re B)\<^sup>2 - (Re A)\<^sup>2 - 2*(Re B)*sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2)) 
                     + 2*(Re B)*A*(-(Re B) + sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2)) + A*A*A"
            using \<open>(-(Re B) + sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2))\<^sup>2 =
                        (Re B)*(Re B) + (Re B)\<^sup>2 - (Re A)\<^sup>2 - 2*(Re B)*sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2)\<close>
            by simp
          also have "... = A*((Re B)*(Re B) + (Re B)\<^sup>2 - A\<^sup>2 - 2*(Re B)*sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2)) 
                     + 2*(Re B)*A*(-(Re B) + sgn(Re B)*sqrt((Re B)\<^sup>2 - (Re A)\<^sup>2)) + A*A*A"
            using \<open>is_real A\<close>
            by simp
          also have "... = 0"
            apply (simp add:field_simps)
            by (simp add: power2_eq_square)
          finally have "A*?nom*(cnj (?nom)) + B*?den*(cnj (?nom)) + (cnj B)*(cnj (?den))*?nom + A*?den*(cnj (?den)) = 0"
            by simp       
          thus "circline_equation A B (cnj B) A ?nom ?den"
            by simp
        qed
        thus ?thesis
          using * \<open>is_poincare_line_cmat H\<close> \<open>intersects_x_axis_cmat H\<close>
          by (simp add: vec_cnj_def)
      qed
    next
      show  "on_circline_cmat_cvec x_axis_cmat (calc_x_axis_intersection_cmat_cvec H)"
        using * \<open>is_poincare_line_cmat H\<close> \<open>intersects_x_axis_cmat H\<close> \<open>is_real A\<close>
        using eq_cnj_iff_real[of A]
        by (simp add: vec_cnj_def)
    qed
  qed
qed

lemma unique_calc_x_axis_intersection:
  assumes "is_poincare_line H" and "H \<noteq> x_axis"
  assumes "x \<in> unit_disc" and "x \<in> circline_set H \<inter> circline_set x_axis"
  shows  "x = calc_x_axis_intersection H"
proof-
  have *: "intersects_x_axis H"
    using assms
    using intersects_x_axis_iff[OF assms(1)]
    by auto
  show "x = calc_x_axis_intersection H"
    using calc_x_axis_intersection[OF assms(1) *]
    using calc_x_axis_intersection_in_unit_disc[OF assms(1) *]
    using assms
    using unique_is_poincare_line[of x "calc_x_axis_intersection H" H x_axis]
    by auto
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Check if an h-line intersects the positive part of the x-axis\<close>
(* ------------------------------------------------------------------ *)

definition intersects_x_axis_positive_cmat :: "complex_mat \<Rightarrow> bool" where
  [simp]: "intersects_x_axis_positive_cmat H = (let (A, B, C, D) = H in Re A \<noteq> 0 \<and> Re B / Re A < -1)"

lift_definition intersects_x_axis_positive_clmat :: "circline_mat \<Rightarrow> bool" is intersects_x_axis_positive_cmat
  done

lift_definition intersects_x_axis_positive :: "circline \<Rightarrow> bool" is intersects_x_axis_positive_clmat
proof (transfer)
  fix H1 H2
  assume hh: "hermitean H1 \<and> H1 \<noteq> mat_zero" and "hermitean H2 \<and> H2 \<noteq> mat_zero"
  obtain A1 B1 C1 D1 A2 B2 C2 D2 where *: "H1 = (A1, B1, C1, D1)" "H2 = (A2, B2, C2, D2)"
    by (cases H1, cases H2, auto)
  assume "circline_eq_cmat H1 H2"
  then obtain k where "k \<noteq> 0 \<and> H2 = cor k *\<^sub>s\<^sub>m H1"
    by auto
  thus "intersects_x_axis_positive_cmat H1 = intersects_x_axis_positive_cmat H2"
    using *
    by simp
qed

lemma intersects_x_axis_positive_mk_circline:
  assumes "is_real A" and "A \<noteq> 0 \<or> B \<noteq> 0"
  shows "intersects_x_axis_positive (mk_circline A B (cnj B) A) \<longleftrightarrow> Re B / Re A < -1"
proof-
  let ?H = "(A, B, (cnj B),  A)"
  have "hermitean ?H" 
    using `is_real A` 
    unfolding hermitean_def mat_adj_def mat_cnj_def
    using eq_cnj_iff_real 
    by auto
  moreover
  have "?H \<noteq> mat_zero"
    using assms
    by auto
  ultimately
  show ?thesis
    by (transfer, transfer, auto simp add: Let_def)
qed


lemma intersects_x_axis_positive_intersects_x_axis [simp]:
  assumes "intersects_x_axis_positive H"
  shows "intersects_x_axis H"
proof-
  have "\<And> a aa. \<lbrakk> Re a \<noteq> 0; Re aa / Re a < - 1; \<not> (Re a)\<^sup>2 < (Re aa)\<^sup>2 \<rbrakk> \<Longrightarrow> aa = 0 \<and> a = 0"
    by (smt less_divide_eq_1_pos one_less_power pos2 power2_minus power_divide zero_less_power2)
  thus ?thesis
    using assms
    apply transfer
    apply transfer
    apply (auto simp add: hermitean_def mat_adj_def mat_cnj_def)
    done
qed

lemma add_less_abs_positive_iff:
  fixes a b :: real
  assumes "abs b < abs a"
  shows "a + b > 0 \<longleftrightarrow> a > 0"
  using assms
  by auto

lemma calc_x_axis_intersection_positive_abs':
  fixes A B :: real
  assumes "B\<^sup>2 > A\<^sup>2" and "A \<noteq> 0"
  shows "abs (sgn(B) * sqrt(B\<^sup>2 - A\<^sup>2) / A) < abs(-B/A)"
proof-
  from assms have "B \<noteq> 0"
    by auto

  have "B\<^sup>2 - A\<^sup>2 < B\<^sup>2"
    using \<open>A \<noteq> 0\<close>
    by auto
  hence "sqrt (B\<^sup>2 - A\<^sup>2) < abs B"
    using real_sqrt_less_iff[of "B\<^sup>2 - A\<^sup>2" "B\<^sup>2"]
    by simp
  thus ?thesis
    using assms \<open>B \<noteq> 0\<close>
    by (simp add: abs_mult divide_strict_right_mono)
qed

lemma calc_intersect_x_axis_positive_lemma:
  assumes "B\<^sup>2 > A\<^sup>2" and "A \<noteq> 0"
  shows "(-B + sgn B * sqrt(B\<^sup>2 - A\<^sup>2)) / A > 0 \<longleftrightarrow> -B/A > 1"
proof-
  have "(-B + sgn B * sqrt(B\<^sup>2 - A\<^sup>2)) / A = -B / A + (sgn B * sqrt(B\<^sup>2 - A\<^sup>2)) / A"
    using assms
    by (simp add: field_simps)
  moreover
  have "-B / A + (sgn B * sqrt(B\<^sup>2 - A\<^sup>2)) / A > 0 \<longleftrightarrow> - B / A > 0"
    using add_less_abs_positive_iff[OF calc_x_axis_intersection_positive_abs'[OF assms]]
    by simp
  moreover
  hence "(B/A)\<^sup>2 > 1"
    using assms
    by (simp add: power_divide)
  hence "B/A > 1 \<or> B/A < -1"
    by (smt one_power2 pos2 power2_minus power_0 power_strict_decreasing zero_power2)
  hence "-B / A > 0 \<longleftrightarrow> -B / A > 1"
    by auto
  ultimately
  show ?thesis
    using assms
    by auto
qed

lemma intersects_x_axis_positive_iff':
  assumes "is_poincare_line H"
  shows "intersects_x_axis_positive H \<longleftrightarrow> 
         calc_x_axis_intersection H \<in> unit_disc \<and> calc_x_axis_intersection H \<in> circline_set H \<inter> positive_x_axis" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  let ?x = "calc_x_axis_intersection H"
  assume ?lhs
  hence "?x \<in> circline_set x_axis" "?x \<in> circline_set H" "?x \<in> unit_disc"
    using calc_x_axis_intersection_in_unit_disc[OF assms] calc_x_axis_intersection[OF assms]
    by auto
  moreover
  have "Re (to_complex ?x) > 0"
    using \<open>?lhs\<close> assms
  proof (transfer, transfer)
    fix H
    assume hh: "hermitean H \<and> H \<noteq> mat_zero"
    obtain A B C D where *: "H = (A, B, C, D)"
      by (cases H, auto)
    assume "intersects_x_axis_positive_cmat H"
    hence **: "Re B / Re A < - 1" "Re A \<noteq> 0"
      using *
      by auto
    have "(Re B)\<^sup>2 > (Re A)\<^sup>2"
      using **
      by (smt divide_less_eq_1_neg divide_minus_left less_divide_eq_1_pos real_sqrt_abs real_sqrt_less_iff right_inverse_eq)
    have "is_real A" "A \<noteq> 0"
      using hh hermitean_elems * \<open>Re A \<noteq> 0\<close> complex.expand[of A 0]
      by auto
    have "(cmod B)\<^sup>2 > (cmod A)\<^sup>2"
      using \<open>(Re B)\<^sup>2 > (Re A)\<^sup>2\<close> \<open>is_real A\<close>
      by (smt cmod_power2 power2_less_0 zero_power2)
    have ***: "0 < (- Re B + sgn (Re B) * sqrt ((Re B)\<^sup>2 - (Re A)\<^sup>2)) / Re A"
      using calc_intersect_x_axis_positive_lemma[of "Re A" "Re B"] ** \<open>(Re B)\<^sup>2 > (Re A)\<^sup>2\<close>
      by auto

    assume "is_poincare_line_cmat H"
    hence "A = D"
      using * hh
      by simp

    have "Re ((cor (sgn (Re B)) * cor (sqrt ((Re B)\<^sup>2 - (Re A)\<^sup>2)) - cor (Re B)) / A) = (sgn (Re B) * sqrt ((Re B)\<^sup>2 - (Re A)\<^sup>2) - Re B) / Re D"
      using \<open>is_real A\<close> \<open>A = D\<close>
      by (metis (no_types, lifting) Re_complex_of_real complex_of_real_Re of_real_diff of_real_divide of_real_mult)
    thus "0 < Re (to_complex_cvec (calc_x_axis_intersection_cmat_cvec H))"
      using * hh ** *** \<open>(cmod B)\<^sup>2 > (cmod A)\<^sup>2\<close> \<open>(Re B)\<^sup>2 > (Re A)\<^sup>2\<close> \<open>A \<noteq> 0\<close> \<open>A = D\<close>
      by simp
  qed
  ultimately
  show ?rhs
    unfolding positive_x_axis_def
    by auto
next
  let ?x = "calc_x_axis_intersection H"
  assume ?rhs
  hence "Re (to_complex ?x) > 0"  "?x \<noteq> \<infinity>\<^sub>h" "?x \<in> circline_set x_axis" "?x \<in> unit_disc" "?x \<in> circline_set H"
    unfolding positive_x_axis_def
    by auto
  hence "intersects_x_axis H"
    using intersects_x_axis_iff[OF assms]
    by auto
  thus ?lhs
    using \<open>Re (to_complex ?x) > 0\<close> assms
  proof (transfer, transfer)
    fix H
    assume hh: "hermitean H \<and> H \<noteq> mat_zero"
    obtain A B C D where *: "H = (A, B, C, D)"
      by (cases H, auto)
    assume "0 < Re (to_complex_cvec (calc_x_axis_intersection_cmat_cvec H))" "intersects_x_axis_cmat H" "is_poincare_line_cmat H"
    hence **: "A \<noteq> 0" "0 < Re ((cor (sgn (Re B)) * cor (sqrt ((Re B)\<^sup>2 - (Re A)\<^sup>2)) - cor (Re B)) / A)"  "A = D" "is_real A" "(Re B)\<^sup>2 > (Re A)\<^sup>2"
      using * hh hermitean_elems
      by (auto split: if_split_asm)

    have "Re A \<noteq> 0"
      using complex.expand[of A 0] \<open>A \<noteq> 0\<close> \<open>is_real A\<close>
      by auto

    have "Re ((cor (sgn (Re B)) * cor (sqrt ((Re B)\<^sup>2 - (Re D)\<^sup>2)) - cor (Re B)) / D) = (sgn (Re B) * sqrt ((Re B)\<^sup>2 - (Re D)\<^sup>2) - Re B) / Re D"
      using \<open>is_real A\<close> \<open>A = D\<close>
      by (metis (no_types, lifting) Re_complex_of_real complex_of_real_Re of_real_diff of_real_divide of_real_mult)

    thus "intersects_x_axis_positive_cmat H"
      using * ** \<open>Re A \<noteq> 0\<close>
      using calc_intersect_x_axis_positive_lemma[of "Re A" "Re B"]
      by simp
  qed
qed

lemma intersects_x_axis_positive_iff:
  assumes "is_poincare_line H" and "H \<noteq> x_axis"
  shows "intersects_x_axis_positive H \<longleftrightarrow> 
         (\<exists> x. x \<in> unit_disc \<and> x \<in> circline_set H \<inter> positive_x_axis)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
    using intersects_x_axis_positive_iff'[OF assms(1)]
    by auto
next
  assume ?rhs
  then obtain x where "x \<in> unit_disc" "x \<in> circline_set H \<inter> positive_x_axis"
    by auto
  thus ?lhs
    using unique_calc_x_axis_intersection[OF assms, of x]
    using intersects_x_axis_positive_iff'[OF assms(1)]
    unfolding positive_x_axis_def
    by auto
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Check if an h-line intersects the positive part of the y-axis\<close>
(* ------------------------------------------------------------------ *)

definition intersects_y_axis_positive_cmat :: "complex_mat \<Rightarrow> bool" where
  [simp]: "intersects_y_axis_positive_cmat H = (let (A, B, C, D) = H in Re A \<noteq> 0 \<and> Im B / Re A < -1)"

lift_definition intersects_y_axis_positive_clmat :: "circline_mat \<Rightarrow> bool" is intersects_y_axis_positive_cmat
  done

lift_definition intersects_y_axis_positive :: "circline \<Rightarrow> bool" is intersects_y_axis_positive_clmat
proof (transfer)
  fix H1 H2
  assume hh: "hermitean H1 \<and> H1 \<noteq> mat_zero" and "hermitean H2 \<and> H2 \<noteq> mat_zero"
  obtain A1 B1 C1 D1 A2 B2 C2 D2 where *: "H1 = (A1, B1, C1, D1)" "H2 = (A2, B2, C2, D2)"
    by (cases H1, cases H2, auto)
  assume "circline_eq_cmat H1 H2"
  then obtain k where "k \<noteq> 0 \<and> H2 = cor k *\<^sub>s\<^sub>m H1"
    by auto
  thus "intersects_y_axis_positive_cmat H1 = intersects_y_axis_positive_cmat H2"
    using *
    by simp
qed

lemma intersects_x_axis_positive_intersects_y_axis_positive [simp]:
  shows "intersects_x_axis_positive (moebius_circline (moebius_rotation (-pi/2)) H) \<longleftrightarrow> intersects_y_axis_positive H"
  using hermitean_elems
  unfolding moebius_rotation_def moebius_similarity_def
  by simp (transfer, transfer, auto simp add: mat_adj_def mat_cnj_def)

lemma intersects_y_axis_positive_iff:
  assumes "is_poincare_line H" "H \<noteq> y_axis"
  shows "(\<exists> y \<in> unit_disc. y \<in> circline_set H \<inter> positive_y_axis) \<longleftrightarrow> intersects_y_axis_positive H" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  let ?R = "moebius_rotation (-pi / 2)"
  let ?H' = "moebius_circline ?R H"
  have 1: "is_poincare_line ?H'"
    using assms
    using unit_circle_fix_preserve_is_poincare_line[OF _ assms(1), of ?R]
    by simp

  have 2: "moebius_circline ?R H \<noteq> x_axis"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "H = moebius_circline (moebius_rotation (pi/2)) x_axis"
      using moebius_circline_comp_inv_left[of ?R H]
      by auto
    thus False
      using \<open>H \<noteq> y_axis\<close>
      by auto
  qed

  show ?thesis
  proof
    assume "?lhs"
    then obtain y where "y \<in> unit_disc" "y \<in> circline_set H \<inter> positive_y_axis"
      by auto
    hence "moebius_pt ?R y \<in> unit_disc" "moebius_pt ?R y \<in> circline_set ?H' \<inter> positive_x_axis"
      using rotation_minus_pi_2_positive_y_axis
      by auto
    thus ?rhs
      using intersects_x_axis_positive_iff[OF 1 2]
      using intersects_x_axis_positive_intersects_y_axis_positive[of H]
      by auto
  next
    assume "intersects_y_axis_positive H"
    hence "intersects_x_axis_positive ?H'"
      using intersects_x_axis_positive_intersects_y_axis_positive[of H]
      by simp
    then obtain x where *: "x \<in> unit_disc" "x \<in> circline_set ?H' \<inter> positive_x_axis"
      using intersects_x_axis_positive_iff[OF 1 2]
      by auto
    let ?y = "moebius_pt (-?R) x"
    have "?y \<in> unit_disc \<and> ?y \<in> circline_set H \<inter> positive_y_axis"
      using * rotation_minus_pi_2_positive_y_axis[symmetric]
      by (metis Int_iff circline_set_moebius_circline_E image_eqI moebius_pt_comp_inv_image_left moebius_rotation_uminus uminus_moebius_def unit_disc_fix_discI unit_disc_fix_rotation)
    thus ?lhs
      by auto
  qed
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Position of the intersection point in the unit disc\<close>
(* ------------------------------------------------------------------ *)

text\<open>Check if the intersection point of one h-line with the x-axis is located more outward the edge
of the disc than the intersection point of another h-line.\<close>

definition outward_cmat :: "complex_mat \<Rightarrow> complex_mat \<Rightarrow> bool" where
 [simp]: "outward_cmat H1 H2 = (let (A1, B1, C1, D1) = H1; (A2, B2, C2, D2) = H2
                                 in -Re B1/Re A1 \<le> -Re B2/Re A2)"
lift_definition outward_clmat :: "circline_mat \<Rightarrow> circline_mat \<Rightarrow> bool" is outward_cmat
  done
lift_definition outward :: "circline \<Rightarrow> circline \<Rightarrow> bool" is outward_clmat
  apply transfer
  apply simp
  apply (case_tac circline_mat1, case_tac circline_mat2, case_tac circline_mat3, case_tac circline_mat4)
  apply simp
  apply (erule_tac exE)+
  apply (erule_tac conjE)+
  apply simp
  done

lemma outward_mk_circline:
  assumes "is_real A1" and "is_real A2" and "A1 \<noteq> 0 \<or> B1 \<noteq> 0" and "A2 \<noteq> 0 \<or> B2 \<noteq> 0" 
  shows "outward (mk_circline A1 B1 (cnj B1) A1) (mk_circline A2 B2 (cnj B2) A2) \<longleftrightarrow> - Re B1 / Re A1 \<le> - Re B2 / Re A2"
proof-
  let ?H1 = "(A1, B1, (cnj B1),  A1)"
  let ?H2 = "(A2, B2, (cnj B2),  A2)"
  have "hermitean ?H1" "hermitean ?H2"
    using `is_real A1` `is_real A2`
    unfolding hermitean_def mat_adj_def mat_cnj_def
    using eq_cnj_iff_real 
    by auto
  moreover
  have "?H1 \<noteq> mat_zero" "?H2 \<noteq> mat_zero"
    using assms
    by auto
  ultimately
  show ?thesis
    by (transfer, transfer, auto simp add: Let_def)
qed

lemma calc_x_axis_intersection_fun_mono:
  fixes x1 x2 :: real
  assumes "x1 > 1" and "x2 > x1"
  shows "x1 - sqrt(x1\<^sup>2 - 1) > x2 - sqrt(x2\<^sup>2 - 1)"
  using assms
proof-
  have *: "sqrt(x1\<^sup>2 - 1) + sqrt(x2\<^sup>2 - 1) > 0"
    using assms
    by (smt one_less_power pos2 real_sqrt_gt_zero)

  have "sqrt(x1\<^sup>2 - 1) < x1"
    using real_sqrt_less_iff[of "x1\<^sup>2 - 1" "x1\<^sup>2"] \<open>x1 > 1\<close>
    by auto
  moreover
  have "sqrt(x2\<^sup>2 - 1) < x2"
    using real_sqrt_less_iff[of "x2\<^sup>2 - 1" "x2\<^sup>2"] \<open>x1 > 1\<close> \<open>x2 > x1\<close>
    by auto
  ultimately
  have "sqrt(x1\<^sup>2 - 1) + sqrt(x2\<^sup>2 - 1) < x1 + x2"
    by simp
  hence "(x1 + x2) / (sqrt(x1\<^sup>2 - 1) + sqrt(x2\<^sup>2 - 1)) > 1"
    using *
    using less_divide_eq_1_pos[of "sqrt(x1\<^sup>2 - 1) + sqrt(x2\<^sup>2 - 1)" "x1 + x2"]
    by simp
  hence "(x2\<^sup>2 - x1\<^sup>2) / (sqrt(x1\<^sup>2 - 1) + sqrt(x2\<^sup>2 - 1)) > x2 - x1"
    using \<open>x2 > x1\<close>
    using mult_less_cancel_left_pos[of "x2 - x1" 1 "(x2 + x1) / (sqrt(x1\<^sup>2 - 1) + sqrt(x2\<^sup>2 - 1))"]
    by (simp add: power2_eq_square field_simps)
  moreover
  have "(x2\<^sup>2 - x1\<^sup>2) = (sqrt(x1\<^sup>2 - 1) + sqrt(x2\<^sup>2 - 1)) * ((sqrt(x2\<^sup>2 - 1) - sqrt(x1\<^sup>2 - 1)))"
    using \<open>x1 > 1\<close> \<open>x2 > x1\<close>
    by (simp add: field_simps)
  ultimately
  have "sqrt(x2\<^sup>2 - 1) - sqrt(x1\<^sup>2 - 1) > x2 - x1"
    using *
    by simp
  thus ?thesis
    by simp
qed

lemma calc_x_axis_intersection_mono:
  fixes a1 b1 a2 b2 :: real
  assumes "-b1/a1 > 1" and "a1 \<noteq> 0" and "-b2/a2 \<ge> -b1/a1" and "a2 \<noteq> 0"
  shows "(-b1 + sgn b1 * sqrt(b1\<^sup>2 - a1\<^sup>2)) / a1 \<ge> (-b2 + sgn b2 * sqrt(b2\<^sup>2 - a2\<^sup>2)) / a2" (is "?lhs \<ge> ?rhs")
proof-
  have "?lhs = -b1/a1 - sqrt((-b1/a1)\<^sup>2 - 1)"
  proof (cases "b1 > 0")
    case True
    hence "a1 < 0"
      using assms
      by (smt divide_neg_pos)
    thus ?thesis
      using \<open>b1 > 0\<close> \<open>a1 < 0\<close>
      by (simp add: real_sqrt_divide field_simps)
  next
    case False
    hence "b1 < 0"
      using assms
      by (cases "b1 = 0") auto
    hence "a1 > 0"
      using assms
      by (smt divide_pos_neg)
    thus ?thesis
      using \<open>b1 < 0\<close> \<open>a1 > 0\<close>
      by (simp add: real_sqrt_divide field_simps)
  qed

  moreover

  have "?rhs = -b2/a2 - sqrt((-b2/a2)\<^sup>2 - 1)"
  proof (cases "b2 > 0")
    case True
    hence "a2 < 0"
      using assms
      by (smt divide_neg_pos)
    thus ?thesis
      using \<open>b2 > 0\<close> \<open>a2 < 0\<close>
      by (simp add: real_sqrt_divide field_simps)
  next
    case False
    hence "b2 < 0"
      using assms
      by (cases "b2 = 0") auto
    hence "a2 > 0"
      using assms
      by (smt divide_pos_neg)
    thus ?thesis
      using \<open>b2 < 0\<close> \<open>a2 > 0\<close>
      by (simp add: real_sqrt_divide field_simps)
  qed

  ultimately

  show ?thesis
    using calc_x_axis_intersection_fun_mono[of "-b1/a1" "-b2/a2"]
    using assms
    by (cases "-b1/a1=-b2/a2", auto)
qed

lemma outward:
  assumes "is_poincare_line H1" and "is_poincare_line H2"
  assumes "intersects_x_axis_positive H1" and "intersects_x_axis_positive H2"
  assumes "outward H1 H2"
  shows "Re (to_complex (calc_x_axis_intersection H1)) \<ge> Re (to_complex (calc_x_axis_intersection H2))"
proof-
  have "intersects_x_axis H1" "intersects_x_axis H2"
    using assms
    by auto
  thus ?thesis
    using assms
  proof (transfer, transfer)
    fix H1 H2
    assume hh: "hermitean H1 \<and> H1 \<noteq> mat_zero"  "hermitean H2 \<and> H2 \<noteq> mat_zero"
    obtain A1 B1 C1 D1 A2 B2 C2 D2 where *: "H1 = (A1, B1, C1, D1)" "H2 = (A2, B2, C2, D2)"
      by (cases H1, cases H2, auto)
    have "is_real A1" "is_real A2"
      using hermitean_elems * hh
      by auto
    assume 1: "intersects_x_axis_positive_cmat H1" "intersects_x_axis_positive_cmat H2"
    assume 2: "intersects_x_axis_cmat H1" "intersects_x_axis_cmat H2"
    assume 3: "is_poincare_line_cmat H1" "is_poincare_line_cmat H2"
    assume 4: "outward_cmat H1 H2"
    have "A1 \<noteq> 0" "A2 \<noteq> 0"
      using * \<open>is_real A1\<close> \<open>is_real A2\<close> 1 complex.expand[of A1 0] complex.expand[of A2 0]
      by auto
    hence "(sgn (Re B2) * sqrt ((Re B2)\<^sup>2 - (Re A2)\<^sup>2) - Re B2) / Re A2
         \<le> (sgn (Re B1) * sqrt ((Re B1)\<^sup>2 - (Re A1)\<^sup>2) - Re B1) / Re A1"
      using calc_x_axis_intersection_mono[of "Re B1" "Re A1" "Re B2" "Re A2"]
      using 1 4 *
      by simp
    moreover
    have "(sgn (Re B2) * sqrt ((Re B2)\<^sup>2 - (Re A2)\<^sup>2) - Re B2) / Re A2 = 
          Re ((cor (sgn (Re B2)) * cor (sqrt ((Re B2)\<^sup>2 - (Re A2)\<^sup>2)) - cor (Re B2)) / A2)"
      using \<open>is_real A2\<close> \<open>A2 \<noteq> 0\<close>
      by (simp add: Re_divide_real)
    moreover
    have "(sgn (Re B1) * sqrt ((Re B1)\<^sup>2 - (Re A1)\<^sup>2) - Re B1) / Re A1 =
           Re ((cor (sgn (Re B1)) * cor (sqrt ((Re B1)\<^sup>2 - (Re A1)\<^sup>2)) - cor (Re B1)) / A1)"
      using \<open>is_real A1\<close> \<open>A1 \<noteq> 0\<close>
      by (simp add: Re_divide_real)
    ultimately
    show "Re (to_complex_cvec (calc_x_axis_intersection_cmat_cvec H2))
          \<le> Re (to_complex_cvec (calc_x_axis_intersection_cmat_cvec H1))"
      using 2 3 \<open>A1 \<noteq> 0\<close> \<open>A2 \<noteq> 0\<close> * \<open>is_real A1\<close> \<open>is_real A2\<close>
      by (simp del: is_poincare_line_cmat_def intersects_x_axis_cmat_def)
  qed    
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Ideal points and x-axis intersection\<close>
(* ------------------------------------------------------------------ *)

lemma ideal_points_intersects_x_axis:               
  assumes "is_poincare_line H" and "ideal_points H = {i1, i2}" and "H \<noteq> x_axis"
  shows  "intersects_x_axis H \<longleftrightarrow> Im (to_complex i1) * Im (to_complex i2) < 0"
  using assms
proof-
  have "i1 \<noteq> i2"
    using assms(1) assms(2) ex_poincare_line_points ideal_points_different(1)
    by blast

  have "calc_ideal_points H = {i1, i2}"
    using assms
    using ideal_points_unique
    by auto

  have "\<forall> i1 \<in> calc_ideal_points H. 
        \<forall> i2 \<in> calc_ideal_points H. 
             is_poincare_line H \<and> H \<noteq> x_axis \<and> i1 \<noteq> i2 \<longrightarrow> (Im (to_complex i1) * Im (to_complex i2) < 0 \<longleftrightarrow> intersects_x_axis H)"
  proof (transfer, transfer, (rule ballI)+, rule impI, (erule conjE)+, case_tac H, case_tac i1, case_tac i2)
    fix i11 i12 i21 i22 A B C D H i1 i2
    assume H: "H = (A, B, C, D)" "hermitean H" "H \<noteq> mat_zero"
    assume line: "is_poincare_line_cmat H"
    assume i1: "i1 = (i11, i12)" "i1 \<in> calc_ideal_points_cmat_cvec H"
    assume i2: "i2 = (i21, i22)" "i2 \<in> calc_ideal_points_cmat_cvec H"
    assume different: "\<not> i1 \<approx>\<^sub>v i2"
    assume not_x_axis:  "\<not> circline_eq_cmat H x_axis_cmat"

    have "is_real A" "is_real D" "C = cnj B"
      using H hermitean_elems
      by auto
    have "(cmod A)\<^sup>2 < (cmod B)\<^sup>2" "A = D"
      using line H
      by auto

    let ?discr =  "sqrt ((cmod B)\<^sup>2 - (Re D)\<^sup>2)"
    let ?den = "(cmod B)\<^sup>2"
    let ?i1 = "B * (- D - \<i> * ?discr)"
    let ?i2 = "B * (- D + \<i> * ?discr)"

    have "i11 = ?i1 \<or> i11 = ?i2" "i12 = ?den"
         "i21 = ?i1 \<or> i21 = ?i2" "i22 = ?den"  
      using i1 i2 H line
      by (auto split: if_split_asm)
    hence i: "i11 = ?i1 \<and> i21 = ?i2 \<or> i11 = ?i2 \<and> i21 = ?i1"
      using `\<not> i1 \<approx>\<^sub>v i2` i1 i2
      by auto

    have "Im (i11 / i12) * Im (i21 / i22) = Im (?i1 / ?den) * Im (?i2 / ?den)"
      using i `i12 = ?den` `i22 = ?den`
      by auto
    also have "... = Im (?i1) * Im (?i2) / ?den\<^sup>2"
      by simp
    also have "... = (Im B * (Im B * (Re D * Re D)) - Re B * (Re B * ((cmod B)\<^sup>2 - (Re D)\<^sup>2))) / cmod B ^ 4"
      using `(cmod B)\<^sup>2 > (cmod A)\<^sup>2` `A = D`
      using `is_real D` cmod_eq_Re[of A]
      by (auto simp add: field_simps)
    also have "... = ((Im B)\<^sup>2 * (Re D)\<^sup>2 - (Re B)\<^sup>2 * ((Re B)\<^sup>2 + (Im B)\<^sup>2 - (Re D)\<^sup>2)) / cmod B ^ 4"
    proof-
      have "cmod B * cmod B = Re B * Re B + Im B * Im B"
        by (metis cmod_power2 power2_eq_square)
      thus ?thesis
        by (simp add: power2_eq_square)
    qed
    also have "... = (((Re D)\<^sup>2 - (Re B)\<^sup>2) * ((Re B)\<^sup>2 + (Im B)\<^sup>2)) / cmod B ^ 4"
      by (simp add: power2_eq_square field_simps)
    finally have Im_product: "Im (i11 / i12) * Im (i21 / i22) = ((Re D)\<^sup>2 - (Re B)\<^sup>2) * ((Re B)\<^sup>2 + (Im B)\<^sup>2) / cmod B ^ 4"
      .

    show "Im (to_complex_cvec i1) * Im (to_complex_cvec i2) < 0 \<longleftrightarrow> intersects_x_axis_cmat H"
    proof safe
      assume opposite: "Im (to_complex_cvec i1) * Im (to_complex_cvec i2) < 0"
      show "intersects_x_axis_cmat H"
      proof-
        have "((Re D)\<^sup>2 - (Re B)\<^sup>2) * ((Re B)\<^sup>2 + (Im B)\<^sup>2) / cmod B ^ 4 < 0"
          using Im_product opposite i1 i2
          by simp
        hence "((Re D)\<^sup>2 - (Re B)\<^sup>2) * ((Re B)\<^sup>2 + (Im B)\<^sup>2) < 0"
          by (simp add: divide_less_0_iff)
        hence "(Re D)\<^sup>2 < (Re B)\<^sup>2"
          by (simp add: mult_less_0_iff not_sum_power2_lt_zero)
        thus ?thesis
          using H `A = D`  `is_real D`
          by auto
      qed
    next
      have *: "(\<forall>k. k * Im B = 1 \<longrightarrow> k = 0) \<longrightarrow> Im B = 0"
        apply (safe, erule_tac x="1 / Im B" in allE)
        using divide_cancel_left by fastforce
      assume "intersects_x_axis_cmat H"
      hence "Re D = 0 \<or> (Re D)\<^sup>2 < (Re B)\<^sup>2"
        using H `A = D`
        by auto
      hence "(Re D)\<^sup>2 < (Re B)\<^sup>2" 
        using `is_real D` line  H `C = cnj B`
        using not_x_axis *
        by (auto simp add: complex_eq_iff)
      hence "((Re D)\<^sup>2 - (Re B)\<^sup>2) * ((Re B)\<^sup>2 + (Im B)\<^sup>2) < 0"
        by (metis add_cancel_left_left diff_less_eq mult_eq_0_iff mult_less_0_iff power2_eq_square power2_less_0 sum_squares_gt_zero_iff)
      thus "Im (to_complex_cvec i1) * Im (to_complex_cvec i2) < 0" 
        using Im_product i1 i2
        using divide_eq_0_iff divide_less_0_iff prod.simps(2) to_complex_cvec_def zero_complex.simps(1) zero_less_norm_iff 
        by fastforce
    qed
  qed
  thus ?thesis
    using assms `calc_ideal_points H = {i1, i2}` `i1 \<noteq> i2`
    by auto
qed

end
