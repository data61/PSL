theory Poincare_Perpendicular
  imports Poincare_Lines_Axis_Intersections
begin

(* ------------------------------------------------------------------ *)
section\<open>H-perpendicular h-lines in the Poincar\'e model\<close>
(* ------------------------------------------------------------------ *)

definition perpendicular_to_x_axis_cmat :: "complex_mat \<Rightarrow> bool" where
 [simp]: "perpendicular_to_x_axis_cmat H \<longleftrightarrow> (let (A, B, C, D) = H in is_real B)"

lift_definition perpendicular_to_x_axis_clmat :: "circline_mat \<Rightarrow> bool" is perpendicular_to_x_axis_cmat
  done

lift_definition perpendicular_to_x_axis :: "circline \<Rightarrow> bool" is perpendicular_to_x_axis_clmat
  by transfer auto

lemma perpendicular_to_x_axis:
  assumes "is_poincare_line H"
  shows "perpendicular_to_x_axis H \<longleftrightarrow> perpendicular x_axis H"
  using assms
  unfolding perpendicular_def
proof (transfer, transfer)
  fix H
  assume hh: "hermitean H \<and> H \<noteq> mat_zero" "is_poincare_line_cmat H"
  obtain A B C D where *: "H = (A, B, C, D)"
    by (cases H, auto)
  hence "is_real A" "(cmod B)\<^sup>2 > (cmod A)\<^sup>2" "H = (A, B, cnj B, A)"
    using hermitean_elems[of A B C D] hh
    by auto
  thus "perpendicular_to_x_axis_cmat H =
        (cos_angle_cmat (of_circline_cmat x_axis_cmat) (of_circline_cmat H) = 0)"
    using cmod_square[of B] cmod_square[of A]
    by simp
qed

lemma perpendicular_to_x_axis_y_axis:
  assumes "perpendicular_to_x_axis (poincare_line 0\<^sub>h (of_complex z))" "z \<noteq> 0"
  shows "is_imag z"
  using assms
  by (transfer, transfer, simp)


lemma wlog_perpendicular_axes:
  assumes in_disc: "u \<in> unit_disc" "v \<in> unit_disc" "z \<in> unit_disc"
  assumes perpendicular: "is_poincare_line H1" "is_poincare_line H2" "perpendicular H1 H2"
  assumes "z \<in> circline_set H1 \<inter> circline_set H2" "u \<in> circline_set H1" "v \<in> circline_set H2"
  assumes axes: "\<And> x y. \<lbrakk>is_real x; 0 \<le> Re x; Re x < 1; is_imag y; 0 \<le> Im y; Im y < 1\<rbrakk> \<Longrightarrow> P 0\<^sub>h (of_complex x) (of_complex y)"
  assumes moebius: "\<And> M u v w. \<lbrakk>unit_disc_fix M; u \<in> unit_disc; v \<in> unit_disc; w \<in> unit_disc; P (moebius_pt M u) (moebius_pt M v) (moebius_pt M w) \<rbrakk> \<Longrightarrow> P u v w"
  assumes conjugate: "\<And> u v w. \<lbrakk>u \<in> unit_disc; v \<in> unit_disc; w \<in> unit_disc; P (conjugate u) (conjugate v) (conjugate w) \<rbrakk> \<Longrightarrow> P u v w"
  shows "P z u v"
proof-
  have "\<forall> v H1 H2. is_poincare_line H1 \<and> is_poincare_line H2 \<and> perpendicular H1 H2 \<and>
                   z \<in> circline_set H1 \<inter> circline_set H2 \<and> u \<in> circline_set H1 \<and> v \<in> circline_set H2 \<and> v \<in> unit_disc \<longrightarrow> P z u v" (is "?P z u")
  proof (rule wlog_x_axis[where P="?P"])
    fix x
    assume x: "is_real x" "Re x \<ge> 0" "Re x < 1"
    have "of_complex x \<in> unit_disc"
      using x
      by (simp add: cmod_eq_Re)

    show "?P 0\<^sub>h (of_complex x)"
    proof safe
      fix v H1 H2
      assume "v \<in> unit_disc"
      then obtain y where y: "v = of_complex y"
        using inf_or_of_complex[of v]
        by auto

      assume 1: "is_poincare_line H1" "is_poincare_line H2" "perpendicular H1 H2"
      assume 2: "0\<^sub>h \<in> circline_set H1" "0\<^sub>h \<in> circline_set H2" "of_complex x \<in> circline_set H1" "v \<in> circline_set H2"

      show "P 0\<^sub>h (of_complex x) v"
      proof (cases "of_complex x = 0\<^sub>h")
        case True
        show "P 0\<^sub>h (of_complex x) v"
        proof (cases "v = 0\<^sub>h")
          case True
          thus ?thesis
            using \<open>of_complex x = 0\<^sub>h\<close>
            using axes[of 0 0]
            by simp
        next
          case False
          show ?thesis
          proof (rule wlog_rotation_to_positive_y_axis)
            show "v \<in> unit_disc" "v \<noteq> 0\<^sub>h"
              by fact+
          next
            fix y
            assume "is_imag y" "0 < Im y" "Im y < 1"
            thus "P 0\<^sub>h (of_complex x) (of_complex y)"
              using x axes[of x y]
              by simp
          next
            fix \<phi> u
            assume "u \<in> unit_disc" "u \<noteq> 0\<^sub>h"
                   "P 0\<^sub>h (of_complex x) (moebius_pt (moebius_rotation \<phi>) u)"
            thus "P 0\<^sub>h (of_complex x) u"
              using \<open>of_complex x = 0\<^sub>h\<close>
              using moebius[of "moebius_rotation \<phi>"  "0\<^sub>h" "0\<^sub>h" u]
              by simp
          qed
        qed
      next
        case False
        hence *: "poincare_line 0\<^sub>h (of_complex x) = x_axis"
          using x poincare_line_0_real_is_x_axis[of "of_complex x"]
          unfolding circline_set_x_axis
          by auto
        hence "H1 = x_axis"
          using unique_poincare_line[of "0\<^sub>h" "of_complex x" H1] 1 2
          using \<open>of_complex x \<in> unit_disc\<close> False
          by simp
        have "is_imag y"
        proof (cases "y = 0")
          case True
          thus ?thesis
            by simp
        next
          case False
          hence "0\<^sub>h \<noteq> of_complex y"
            using of_complex_zero_iff[of y]
            by metis
          hence "H2 = poincare_line 0\<^sub>h (of_complex y)"
            using 1 2 \<open>v \<in> unit_disc\<close>
            using unique_poincare_line[of "0\<^sub>h" "of_complex y" H2] y
            by simp
          thus ?thesis
            using 1 \<open>H1 = x_axis\<close>
            using perpendicular_to_x_axis_y_axis[of y] False
            using perpendicular_to_x_axis[of H2]
            by simp
        qed
        show "P 0\<^sub>h (of_complex x) v"
        proof (cases "Im y \<ge> 0")
          case True
          thus ?thesis
            using axes[of x y] x y \<open>is_imag y\<close> \<open>v \<in> unit_disc\<close>
            by (simp add: cmod_eq_Im)
        next
          case False
          show ?thesis
          proof (rule conjugate)
            have "Im (cnj y) < 1"
              using \<open>v \<in> unit_disc\<close> y \<open>is_imag y\<close> eq_minus_cnj_iff_imag[of y]
              by (simp add: cmod_eq_Im)
            thus "P (conjugate 0\<^sub>h) (conjugate (of_complex x)) (conjugate v)"
              using \<open>is_real x\<close> eq_cnj_iff_real[of x] y \<open>is_imag y\<close>
              using axes[OF x, of "cnj y"] False
              by simp
            show "0\<^sub>h \<in> unit_disc" "of_complex x \<in> unit_disc" "v \<in> unit_disc"
              by (simp, fact+)
          qed
        qed
      qed
    qed
  next
    show "z \<in> unit_disc" "u \<in> unit_disc"
      by fact+
  next
    fix M u v
    assume *: "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc"
    assume **: "?P (moebius_pt M u) (moebius_pt M v)"
    show "?P u v"
    proof safe
      fix w H1 H2
      assume ***: "is_poincare_line H1" "is_poincare_line H2" "perpendicular H1 H2"
                  "u \<in> circline_set H1" "u \<in> circline_set H2"
                  "v \<in> circline_set H1" "w \<in> circline_set H2" "w \<in> unit_disc"
      thus "P u v w"
        using moebius[of M u v w] *
        using **[rule_format, of "moebius_circline M H1" "moebius_circline M H2" "moebius_pt M w"]
        by simp
    qed
  qed
  thus ?thesis
    using assms
    by blast
qed

lemma wlog_perpendicular_foot:
  assumes in_disc: "u \<in> unit_disc" "v \<in> unit_disc" "w \<in> unit_disc" "z \<in> unit_disc"
  assumes perpendicular: "u \<noteq> v" "is_poincare_line H" "perpendicular (poincare_line u v) H"
  assumes "z \<in> circline_set (poincare_line u v) \<inter> circline_set H" "w \<in> circline_set H"
  assumes axes: "\<And> u v w. \<lbrakk>is_real u; 0 < Re u; Re u < 1; is_real v; -1 < Re v; Re v < 1; Re u \<noteq> Re v; is_imag w; 0 \<le> Im w; Im w < 1\<rbrakk> \<Longrightarrow> P 0\<^sub>h (of_complex u) (of_complex v) (of_complex w)"
  assumes moebius: "\<And> M z u v w. \<lbrakk>unit_disc_fix M; u \<in> unit_disc; v \<in> unit_disc; w \<in> unit_disc; z \<in> unit_disc; P (moebius_pt M z) (moebius_pt M u) (moebius_pt M v) (moebius_pt M w) \<rbrakk> \<Longrightarrow> P z u v w"
  assumes conjugate: "\<And> z u v w. \<lbrakk>u \<in> unit_disc; v \<in> unit_disc; w \<in> unit_disc; P (conjugate z) (conjugate u) (conjugate v) (conjugate w) \<rbrakk> \<Longrightarrow> P z u v w"
  assumes perm: "P z v u w \<Longrightarrow> P z u v w"
  shows "P z u v w"
proof-
  obtain m n where mn: "m = u \<or> m = v" "n = u \<or> n = v" "m \<noteq> n" "m \<noteq> z"
    using \<open>u \<noteq> v\<close>
    by auto

  have "n \<in> circline_set (poincare_line z m)"
    using \<open>z \<in> circline_set (poincare_line u v) \<inter> circline_set H\<close>
    using mn
    using unique_poincare_line[of z m "poincare_line u v", symmetric] in_disc
    by auto

  have "\<forall> n. n \<in> unit_disc \<and> m \<noteq> n \<and> n \<in> circline_set (poincare_line z m) \<and> m \<noteq> z \<longrightarrow> P z m n w" (is "?Q z m w")
  proof (rule wlog_perpendicular_axes[where P="?Q"])
    show "is_poincare_line (poincare_line u v)"
      using \<open>u \<noteq> v\<close>
      by auto
  next
    show "is_poincare_line H"
      by fact
  next
    show "m \<in> unit_disc" "m \<in> circline_set (poincare_line u v)"
      using mn in_disc
      by auto
  next
    show "w \<in> unit_disc" "z \<in> unit_disc"
      by fact+
  next
    show "z \<in> circline_set (poincare_line u v) \<inter> circline_set H"
      by fact
  next
    show "perpendicular (poincare_line u v) H"
      by fact
  next
    show "w \<in> circline_set H"
      by fact
  next
    fix x y
    assume xy: "is_real x" "0 \<le> Re x" "Re x < 1" "is_imag y" "0 \<le> Im y" "Im y < 1"
    show "?Q 0\<^sub>h (of_complex x) (of_complex y)"
    proof safe
      fix n
      assume "n \<in> unit_disc" "of_complex x \<noteq> n"
      assume "n \<in> circline_set (poincare_line 0\<^sub>h (of_complex x))" "of_complex x \<noteq> 0\<^sub>h"
      hence "n \<in> circline_set x_axis"
        using poincare_line_0_real_is_x_axis[of "of_complex x"] xy
        by (auto simp add: circline_set_x_axis)
      then obtain n' where n': "n = of_complex n'"
        using inf_or_of_complex[of n] \<open>n \<in> unit_disc\<close>
        by auto
      hence "is_real n'"
        using \<open>n \<in> circline_set x_axis\<close>
        using of_complex_inj
        unfolding circline_set_x_axis
        by auto
      hence "-1 < Re n'" "Re n' < 1"
        using \<open>n \<in> unit_disc\<close> n'
        by (auto simp add: cmod_eq_Re)

      have "Re n' \<noteq> Re x"
        using complex.expand[of n' x] \<open>is_real n'\<close> \<open>is_real x\<close> \<open>of_complex x \<noteq> n\<close> n'
        by auto

      have "Re x > 0"
        using xy \<open>of_complex x \<noteq> 0\<^sub>h\<close>
        by (cases "Re x = 0", auto simp add: complex.expand)

      show "P 0\<^sub>h (of_complex x) n (of_complex y)"
        using axes[of x n' y] xy n' \<open>Re x > 0\<close> \<open>is_real n'\<close> \<open>-1 < Re n'\<close> \<open>Re n' < 1\<close> \<open>Re n' \<noteq> Re x\<close>
        by simp
    qed
  next
    fix M u v w
    assume 1: "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc" "w \<in> unit_disc"
    assume 2: "?Q (moebius_pt M u) (moebius_pt M v) (moebius_pt M w)"
    show "?Q u v w"
    proof safe
      fix n
      assume "n \<in> unit_disc" "v \<noteq> n" "n \<in> circline_set (poincare_line u v)" "v \<noteq> u"
      thus "P u v n w"
        using moebius[of M v n w u] 1 2[rule_format, of "moebius_pt M n"]
        by fastforce
    qed
  next
    fix u v w
    assume 1: "u \<in> unit_disc" "v \<in> unit_disc" "w \<in> unit_disc"
    assume 2: "?Q (conjugate u) (conjugate v) (conjugate w)"
    show "?Q u v w"
    proof safe
      fix n
      assume "n \<in> unit_disc" "v \<noteq> n" "n \<in> circline_set (poincare_line u v)" "v \<noteq> u"
      thus "P u v n w"
        using conjugate[of v n w u] 1 2[rule_format, of "conjugate n"]
        using conjugate_inj
        by auto
    qed
  qed
  thus ?thesis
    using mn in_disc \<open>n \<in> circline_set (poincare_line z m)\<close> perm
    by auto
qed

lemma perpendicular_to_x_axis_intersects_x_axis:
  assumes "is_poincare_line H" "perpendicular_to_x_axis H"
  shows "intersects_x_axis H"
  using assms hermitean_elems
  by (transfer, transfer, auto simp add: cmod_eq_Re)


lemma perpendicular_intersects:
  assumes "is_poincare_line H1" "is_poincare_line H2"
  assumes "perpendicular H1 H2"
  shows "\<exists> z. z \<in> unit_disc \<and> z \<in> circline_set H1 \<inter> circline_set H2" (is "?P' H1 H2")
proof-
  have "\<forall> H2. is_poincare_line H2 \<and> perpendicular H1 H2 \<longrightarrow> ?P' H1 H2" (is "?P H1")
  proof (rule wlog_line_x_axis)
    show "?P x_axis"
    proof safe
      fix H2
      assume "is_poincare_line H2" "perpendicular x_axis H2"
      thus "\<exists>z. z \<in> unit_disc \<and> z \<in> circline_set x_axis \<inter> circline_set H2"
        using perpendicular_to_x_axis[of H2]
        using perpendicular_to_x_axis_intersects_x_axis[of H2]
        using intersects_x_axis_iff[of H2]
        by auto
    qed
  next
    fix M
    assume "unit_disc_fix M"
    assume *: "?P (moebius_circline M H1)"
    show "?P H1"
    proof safe
      fix H2
      assume "is_poincare_line H2" "perpendicular H1 H2"
      then obtain z where "z \<in> unit_disc" "z \<in> circline_set (moebius_circline M H1) \<and> z \<in> circline_set (moebius_circline M H2)"
        using *[rule_format, of "moebius_circline M H2"] \<open>unit_disc_fix M\<close>
        by auto
      thus "\<exists>z. z \<in> unit_disc \<and> z \<in> circline_set H1 \<inter> circline_set H2"
        using \<open>unit_disc_fix M\<close>
        by (rule_tac x="moebius_pt (-M) z" in exI)
           (metis IntI add.inverse_inverse circline_set_moebius_circline_iff moebius_pt_comp_inv_left uminus_moebius_def unit_disc_fix_discI unit_disc_fix_moebius_uminus)
    qed
  next
    show "is_poincare_line H1"
      by fact
  qed
  thus ?thesis
    using assms
    by auto
qed


definition calc_perpendicular_to_x_axis_cmat :: "complex_vec \<Rightarrow> complex_mat" where
 [simp]: "calc_perpendicular_to_x_axis_cmat z =
     (let (z1, z2) = z
       in if z1*cnj z2 + z2*cnj z1 = 0 then
          (0, 1, 1, 0)
       else
          let A = z1*cnj z2 + z2*cnj z1;
              B = -(z1*cnj z1 + z2*cnj z2)
           in (A, B, B, A)
     )"

lift_definition calc_perpendicular_to_x_axis_clmat :: "complex_homo_coords \<Rightarrow> circline_mat" is calc_perpendicular_to_x_axis_cmat
  by (auto simp add: hermitean_def mat_adj_def mat_cnj_def Let_def split: if_split_asm)

lift_definition calc_perpendicular_to_x_axis :: "complex_homo \<Rightarrow> circline" is calc_perpendicular_to_x_axis_clmat
proof (transfer)
  fix z w
  assume "z \<noteq> vec_zero" "w \<noteq> vec_zero"
  obtain z1 z2 w1 w2 where zw: "z = (z1, z2)" "w = (w1, w2)"
    by (cases z, cases w, auto)
  assume "z \<approx>\<^sub>v w"
  then obtain k where *: "k \<noteq> 0" "w1 = k*z1" "w2 = k*z2"
    using zw
    by auto
  have "w1 * cnj w2 + w2 * cnj w1 = (k * cnj k) * (z1 * cnj z2 + z2 * cnj z1)"
    using *
    by (auto simp add: field_simps)
  moreover
  have "w1 * cnj w1 + w2 * cnj w2 = (k * cnj k) * (z1 * cnj z1 + z2 * cnj z2)"
    using *
    by (auto simp add: field_simps)
  ultimately
  show "circline_eq_cmat (calc_perpendicular_to_x_axis_cmat z) (calc_perpendicular_to_x_axis_cmat w)"
    using zw *
    apply (auto simp add: Let_def)
    apply (rule_tac x="Re (k * cnj k)" in exI, auto simp add: complex.expand field_simps)
    done
qed

lemma calc_perpendicular_to_x_axis:
  assumes "z \<noteq> of_complex 1" "z \<noteq> of_complex (-1)"
  shows "z \<in> circline_set (calc_perpendicular_to_x_axis z) \<and>
         is_poincare_line (calc_perpendicular_to_x_axis z) \<and>
         perpendicular_to_x_axis (calc_perpendicular_to_x_axis z)"
  using assms
  unfolding circline_set_def perpendicular_def
proof (simp, transfer, transfer)
  fix z :: complex_vec
  obtain z1 z2 where z: "z = (z1, z2)"
    by (cases z, auto)
  assume **: "\<not> z \<approx>\<^sub>v of_complex_cvec 1" "\<not> z \<approx>\<^sub>v of_complex_cvec (- 1)"
  show "on_circline_cmat_cvec (calc_perpendicular_to_x_axis_cmat z) z \<and>
        is_poincare_line_cmat (calc_perpendicular_to_x_axis_cmat z) \<and>
        perpendicular_to_x_axis_cmat (calc_perpendicular_to_x_axis_cmat z)"
  proof (cases "z1*cnj z2 + z2*cnj z1 = 0")
    case True
    thus ?thesis
      using z
      by (simp add: vec_cnj_def hermitean_def mat_adj_def mat_cnj_def mult.commute)
  next
    case False
    hence "z2 \<noteq> 0"
      using z
      by auto
    hence "Re (z2 * cnj z2) \<noteq> 0"
      using \<open>z2 \<noteq> 0\<close>
      by (auto simp add: complex.expand)

    have "z1 \<noteq> -z2 \<and> z1 \<noteq> z2"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "z \<approx>\<^sub>v of_complex_cvec 1 \<or> z \<approx>\<^sub>v of_complex_cvec (-1)"
        using z \<open>z2 \<noteq> 0\<close>
        by auto
      thus False
        using **
        by auto
    qed

    let ?A = "z1*cnj z2 + z2*cnj z1" and ?B = "-(z1*cnj z1 + z2*cnj z2)"
    have "Re(z1*cnj z1 + z2*cnj z2) \<ge> 0"
      by auto
    hence "Re ?B \<le> 0"
      by (smt uminus_complex.simps(1))
    hence "abs (Re ?B) = - Re ?B"
      by auto
    also have "... = (Re z1)\<^sup>2 + (Im z1)\<^sup>2 + (Re z2)\<^sup>2 + (Im z2)\<^sup>2"
      by (simp add: power2_eq_square[symmetric])
    also have "... > abs (Re ?A)"
    proof (cases "Re ?A \<ge> 0")
      case False
      have "(Re z1 + Re z2)\<^sup>2 + (Im z1 + Im z2)\<^sup>2 > 0"
        using \<open>z1 \<noteq> -z2 \<and> z1 \<noteq> z2\<close>
        by (metis add.commute add.inverse_unique complex_neq_0 plus_complex.code plus_complex.simps)
      thus ?thesis
        using False
        by (simp add: power2_sum power2_eq_square field_simps)
    next
      case True
      have "(Re z1 - Re z2)\<^sup>2 + (Im z1 - Im z2)\<^sup>2 > 0"
        using \<open>z1 \<noteq> -z2 \<and> z1 \<noteq> z2\<close>
        by (meson complex_eq_iff right_minus_eq sum_power2_gt_zero_iff)
      thus ?thesis
        using True
        by (simp add: power2_sum power2_eq_square field_simps)
    qed
    finally
    have "abs (Re ?B) > abs (Re ?A)"
      .
    moreover
    have "cmod ?B = abs (Re ?B)" "cmod ?A = abs (Re ?A)"
      by (simp_all add: cmod_eq_Re)
    ultimately
    have "(cmod ?B)\<^sup>2 > (cmod ?A)\<^sup>2"
      by (smt power2_le_imp_le)
    thus ?thesis
      using z False
      by (simp_all add: Let_def hermitean_def mat_adj_def mat_cnj_def cmod_eq_Re vec_cnj_def field_simps)
  qed
qed

lemma ex_perpendicular:
  assumes "is_poincare_line H" "z \<in> unit_disc"
  shows "\<exists> H'. is_poincare_line H' \<and> perpendicular H H' \<and> z \<in> circline_set H'" (is "?P' H z")
proof-
  have "\<forall> z. z \<in> unit_disc \<longrightarrow> ?P' H z" (is "?P H")
  proof (rule wlog_line_x_axis)
    show "?P x_axis"
    proof safe
      fix z
      assume "z \<in> unit_disc"
      then have "z \<noteq> of_complex 1" "z \<noteq> of_complex (-1)"
        by auto
      thus "?P' x_axis z"
        using \<open>z \<in> unit_disc\<close>
        using calc_perpendicular_to_x_axis[of z] perpendicular_to_x_axis
        by (rule_tac x = "calc_perpendicular_to_x_axis z" in exI, auto)
    qed
  next
    fix M
    assume "unit_disc_fix M"
    assume *: "?P (moebius_circline M H)"
    show "?P H"
    proof safe
      fix z
      assume "z \<in> unit_disc"
      hence "moebius_pt M z \<in> unit_disc"
        using \<open>unit_disc_fix M\<close>
        by auto
      then obtain H' where *: "is_poincare_line H'" "perpendicular (moebius_circline M H) H'" "moebius_pt M z \<in> circline_set H'"
        using *
        by auto
      have h: "H = moebius_circline (-M) (moebius_circline M H)"   
        by auto
      show "?P' H z"
        using * \<open>unit_disc_fix M\<close>
        apply (subst h)
        apply (rule_tac x="moebius_circline (-M) H'" in exI)
        apply (simp del: moebius_circline_comp_inv_left)
        done
    qed
  qed fact
  thus ?thesis
    using assms
    by simp
qed

lemma ex_perpendicular_foot:
  assumes "is_poincare_line H" "z \<in> unit_disc"
  shows "\<exists> H'. is_poincare_line H' \<and> z \<in> circline_set H' \<and> perpendicular H H' \<and>
              (\<exists> z' \<in> unit_disc. z' \<in> circline_set H' \<inter> circline_set H)"
  using assms
  using ex_perpendicular[OF assms]
  using perpendicular_intersects[of H]
  by blast

lemma Pythagoras:
  assumes in_disc: "u \<in> unit_disc" "v \<in> unit_disc" "w \<in> unit_disc" "v \<noteq> w"
  assumes "distinct[u, v, w] \<longrightarrow> perpendicular (poincare_line u v) (poincare_line u w)"
  shows "cosh (poincare_distance v w) = cosh (poincare_distance u v) * cosh (poincare_distance u w)" (is "?P' u v w")
proof (cases "distinct [u, v, w]")
  case False
  thus "?thesis"
    using in_disc
    by (auto simp add: poincare_distance_sym)
next
  case True
  have "distinct [u, v, w] \<longrightarrow> ?P' u v w" (is "?P u v w")
  proof (rule wlog_perpendicular_axes[where P="?P"])
    show "is_poincare_line (poincare_line u v)" "is_poincare_line (poincare_line u w)"
      using \<open>distinct [u, v, w]\<close>
      by simp_all
  next
    show "perpendicular (poincare_line u v) (poincare_line u w)"
      using True assms
      by simp
  next
    show "u \<in> unit_disc" "v \<in> unit_disc" "w \<in> unit_disc"
      by fact+
  next
    show "v \<in> circline_set (poincare_line u v)" "w \<in> circline_set (poincare_line u w)"
         "u \<in> circline_set (poincare_line u v) \<inter> circline_set (poincare_line u w)"
      using \<open>distinct [u, v, w]\<close>
      by auto
  next
    fix x y
    assume x: "is_real x" "0 \<le> Re x" "Re x < 1"
    assume y: "is_imag y" "0 \<le> Im y" "Im y < 1"

    have "of_complex x \<in> unit_disc" "of_complex y \<in> unit_disc"
      using x y
      by (simp_all add: cmod_eq_Re cmod_eq_Im)

    show "?P 0\<^sub>h (of_complex x) (of_complex y)"
    proof
      assume "distinct [0\<^sub>h, of_complex x, of_complex y]"
      hence "x \<noteq> 0" "y \<noteq> 0"
        by auto

      let ?den1 = "1 - (cmod x)\<^sup>2" and ?den2 = "1 - (cmod y)\<^sup>2"
      have "?den1 > 0" "?den2 > 0"
        using x y
        by (simp_all add: cmod_eq_Re cmod_eq_Im abs_square_less_1)

      let ?d1 = "1 + 2 * (cmod x)\<^sup>2 / ?den1"
      have "cosh (poincare_distance 0\<^sub>h (of_complex x)) = ?d1"
        using \<open>?den1 > 0\<close>
        using poincare_distance_formula[of "0\<^sub>h" "of_complex x"] \<open>of_complex x \<in> unit_disc\<close>
        by simp

      moreover

      let ?d2 = "1 + 2 * (cmod y)\<^sup>2 / ?den2"
      have "cosh (poincare_distance 0\<^sub>h (of_complex y)) = ?d2"
        using \<open>?den2 > 0\<close> \<open>of_complex y \<in> unit_disc\<close>
        using poincare_distance_formula[of "0\<^sub>h" "of_complex y"]
        by simp

      moreover
      let ?den = "?den1 * ?den2"
      let ?d3 = "1 + 2 * (cmod (x - y))\<^sup>2 / ?den"
      have "cosh (poincare_distance (of_complex x) (of_complex y)) = ?d3"
        using \<open>of_complex x \<in> unit_disc\<close> \<open>of_complex y \<in> unit_disc\<close>
        using \<open>?den1 > 0\<close> \<open>?den2 > 0\<close>
        using poincare_distance_formula[of "of_complex x" "of_complex y"]
        by simp
      moreover
      have "?d1 * ?d2 = ?d3"
      proof-
        have "?d3 = ((1 - (cmod x)\<^sup>2) * (1 - (cmod y)\<^sup>2) + 2 * (cmod (x - y))\<^sup>2) / ?den"
          using \<open>?den1 > 0\<close> \<open>?den2 > 0\<close>
          by (subst add_num_frac, simp, simp)
        also have "... = (Re ((1 - x * cnj x) * (1 - y * cnj y) + 2 * (x - y)*cnj (x - y)) / ?den)"
          using \<open>is_real x\<close> \<open>is_imag y\<close>
          by ((subst cmod_square)+, simp)
        also have "... = Re (1 + x * cnj x * y * cnj y
                               + x * cnj x - 2 * y * cnj x - 2 * x * cnj y + y * cnj y) / ?den"
          by (simp add: field_simps)
        also have "... = Re ((1 + y * cnj y) * (1 + x * cnj x)) / ?den"
          using \<open>is_real x\<close> \<open>is_imag y\<close>
          by (simp add: field_simps)
        finally
        show ?thesis
          using \<open>?den1 > 0\<close> \<open>?den2 > 0\<close>
          apply (subst add_num_frac, simp)
          apply (subst add_num_frac, simp)
          apply simp
          apply (subst cmod_square)+
          apply (simp add: field_simps)
          done
      qed
      ultimately
      show "?P' 0\<^sub>h (of_complex x) (of_complex y)"
        by simp
    qed
  next
    fix M u v w
    assume 1: "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc" "w \<in> unit_disc"
    assume 2: "?P (moebius_pt M u) (moebius_pt M v) (moebius_pt M w)"
    show "?P u v w"
      using 1 2
      by auto
  next
    fix u v w
    assume 1:  "u \<in> unit_disc" "v \<in> unit_disc" "w \<in> unit_disc"
    assume 2: "?P (conjugate u) (conjugate v) (conjugate w)"
    show "?P u v w"
      using 1 2
      by (auto simp add: conjugate_inj)
  qed
  thus ?thesis
    using True
    by simp
qed

end