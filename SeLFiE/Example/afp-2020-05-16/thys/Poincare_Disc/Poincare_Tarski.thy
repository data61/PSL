section \<open>Poincar\'e model satisfies Tarski axioms\<close>

theory Poincare_Tarski
  imports Poincare Poincare_Lines_Axis_Intersections Tarski
begin

(* ------------------------------------------------------------------ *)
subsection\<open>Pasch axiom\<close>
(* ------------------------------------------------------------------ *)

lemma Pasch_fun_mono:
  fixes r1 r2 :: real
  assumes "0 < r1" and "r1 \<le> r2" and "r2 < 1"
  shows "r1 + 1/r1 \<ge> r2 + 1/r2"
proof (cases "r1 = r2")
  case True
  thus ?thesis
    by simp
next
  case False
  hence "r2 - r1 > 0"
    using assms
    by simp

  have "r1 * r2 < 1"
    using assms
    by (smt mult_le_cancel_left1)
  hence "1 / (r1 * r2) > 1"
    using assms
    by simp
  hence "(r2 - r1) / (r1 * r2) > (r2 - r1)"
    using \<open>r2 - r1 > 0\<close>
    using mult_less_cancel_left_pos[of "r2 - r1" 1 "1 / (r1 * r2)"]
    by simp
  hence "1 / r1 - 1 / r2 > r2 - r1"
    using assms
    by (simp add: field_simps)
  thus ?thesis
    by simp
qed

text\<open>Pasch axiom, non-degenerative case.\<close>
lemma Pasch_nondeg:
  assumes "x \<in> unit_disc" and "y \<in> unit_disc" and "z \<in> unit_disc" and "u \<in> unit_disc" and "v \<in> unit_disc"
  assumes "distinct [x, y, z, u, v]" 
  assumes "\<not> poincare_collinear {x, y, z}" 
  assumes "poincare_between x u z" and "poincare_between y v z"
  shows "\<exists> a. a \<in> unit_disc \<and> poincare_between u a y \<and> poincare_between x a v"
proof-
  have "\<forall> y z u. distinct [x, y, z, u, v] \<and> \<not> poincare_collinear {x, y, z} \<and> y \<in> unit_disc \<and> z \<in> unit_disc \<and> u \<in> unit_disc \<and>
                 poincare_between x u z \<and> poincare_between y v z \<longrightarrow> (\<exists> a. a \<in> unit_disc \<and> poincare_between u a y \<and> poincare_between x a v)" (is "?P x v")
  proof (rule wlog_positive_x_axis[where P="?P"])
    fix v
    assume v: "is_real v" "0 < Re v" "Re v < 1"
    hence "of_complex v \<in> unit_disc"
      by (auto simp add: cmod_eq_Re)
    show "?P 0\<^sub>h (of_complex v)"
    proof safe
      fix y z u
      assume distinct: "distinct [0\<^sub>h, y, z, u, of_complex v]"
      assume in_disc: "y \<in> unit_disc" "z \<in> unit_disc" "u \<in> unit_disc"
      then obtain y' z' u'
        where *: "y = of_complex y'" "z = of_complex z'" "u = of_complex u'"
        using inf_or_of_complex inf_notin_unit_disc
        by metis

      have "y' \<noteq> 0" "z' \<noteq> 0" "u' \<noteq> 0" "v \<noteq> 0" "y' \<noteq> z'" "y' \<noteq> u'" "z' \<noteq> u'" "y \<noteq> z" "y \<noteq> u" "z \<noteq> u"
        using of_complex_inj distinct *
        by auto

      note distinct = distinct this

      assume "\<not> poincare_collinear {0\<^sub>h, y, z}"

      hence nondeg_yz: "y'*cnj z' \<noteq> cnj y' * z'"
        using * poincare_collinear_zero_iff[of y' z'] in_disc distinct
        by auto

      assume "poincare_between 0\<^sub>h u z"

      hence "arg u' = arg z'" "cmod u' \<le> cmod z'"
        using * poincare_between_0uv[of u z] distinct in_disc
        by auto

      then obtain \<phi> ru rz where
        uz_polar: "u' = cor ru * cis \<phi>" "z' = cor rz * cis \<phi>" "0 < ru" "ru \<le> rz" "0 < rz" and
                  "\<phi> = arg u'" "\<phi> = arg z'"
        using * \<open>u' \<noteq> 0\<close> \<open>z' \<noteq> 0\<close>
        by (smt cmod_cis norm_le_zero_iff)

      obtain \<theta> ry where
        y_polar: "y' = cor ry * cis \<theta>" "ry > 0" and "\<theta> = arg y'"
        using \<open>y' \<noteq> 0\<close>
        by (smt cmod_cis norm_le_zero_iff)

      from in_disc * \<open>u' = cor ru * cis \<phi>\<close> \<open>z' = cor rz * cis \<phi>\<close> \<open>y' = cor ry * cis \<theta>\<close>
      have "ru < 1" "rz < 1" "ry < 1"
        by simp_all

      note polar = this y_polar uz_polar

      have nondeg: "cis \<theta> * cis (- \<phi>) \<noteq> cis (- \<theta>) * cis \<phi>"
        using nondeg_yz polar
        by simp

      let ?yz = "poincare_line y z"
      let ?v = "calc_x_axis_intersection ?yz"

      assume "poincare_between y (of_complex v) z"

      hence "of_complex v \<in> circline_set ?yz"
        using in_disc \<open>of_complex v \<in> unit_disc\<close>
        using distinct poincare_between_poincare_collinear[of y "of_complex v" z]
        using unique_poincare_line[of y z]
        by (auto simp add: poincare_collinear_def)
      moreover
      have "of_complex v \<in> circline_set x_axis"
        using \<open>is_real v\<close>
        unfolding circline_set_x_axis
        by auto
      moreover
      have "?yz \<noteq> x_axis"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence "{0\<^sub>h, y, z} \<subseteq> circline_set (poincare_line y z)"
          unfolding circline_set_def
          using distinct poincare_line[of y z]
          by auto
        hence "poincare_collinear {0\<^sub>h, y, z}"
          unfolding poincare_collinear_def
          using distinct
          by force
        thus False
          using \<open>\<not> poincare_collinear {0\<^sub>h, y, z}\<close>
          by simp
      qed
      ultimately
      have "?v = of_complex v" "intersects_x_axis ?yz"
        using unique_calc_x_axis_intersection[of "poincare_line y z" "of_complex v"]
        using intersects_x_axis_iff[of ?yz]
        using distinct \<open>of_complex v \<in> unit_disc\<close>
        by (metis IntI is_poincare_line_poincare_line)+

      have "intersects_x_axis_positive ?yz"
        using \<open>Re v > 0\<close> \<open>of_complex v \<in> unit_disc\<close>
        using \<open>of_complex v \<in> circline_set ?yz\<close> \<open>of_complex v \<in> circline_set x_axis\<close>
        using intersects_x_axis_positive_iff[of ?yz] \<open>y \<noteq> z\<close> \<open>?yz \<noteq> x_axis\<close>
        unfolding positive_x_axis_def
        by force

      have "y \<notin> circline_set x_axis"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        moreover
        hence "poincare_line y (of_complex v) = x_axis"
          using distinct \<open>of_complex v \<in> circline_set x_axis\<close>
          using in_disc \<open>of_complex v \<in> unit_disc\<close>
          using unique_poincare_line[of y "of_complex v" x_axis]
          by simp
        moreover
        have "z \<in> circline_set (poincare_line y (of_complex v))"
          using \<open>of_complex v \<in> circline_set ?yz\<close>
          using unique_poincare_line[of y "of_complex v" "poincare_line y z"]
          using in_disc \<open>of_complex v \<in> unit_disc\<close> distinct
          using poincare_line[of y z]
          unfolding circline_set_def
          by (metis distinct_length_2_or_more is_poincare_line_poincare_line mem_Collect_eq)
        ultimately
        have "y \<in> circline_set x_axis" "z \<in> circline_set x_axis"
          by auto
        hence "poincare_collinear {0\<^sub>h, y, z}"
          unfolding poincare_collinear_def
          by force
        thus False
          using \<open>\<not> poincare_collinear {0\<^sub>h, y, z}\<close>
          by simp
      qed

      moreover

      have "z \<notin> circline_set x_axis"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        moreover
        hence "poincare_line z (of_complex v) = x_axis"
          using distinct \<open>of_complex v \<in> circline_set x_axis\<close>
          using in_disc \<open>of_complex v \<in> unit_disc\<close>
          using unique_poincare_line[of z "of_complex v" x_axis]
          by simp
        moreover
        have "y \<in> circline_set (poincare_line z (of_complex v))"
          using \<open>of_complex v \<in> circline_set ?yz\<close>
          using unique_poincare_line[of z "of_complex v" "poincare_line y z"]
          using in_disc \<open>of_complex v \<in> unit_disc\<close> distinct
          using poincare_line[of y z]
          unfolding circline_set_def
          by (metis distinct_length_2_or_more is_poincare_line_poincare_line mem_Collect_eq)
        ultimately
        have "y \<in> circline_set x_axis" "z \<in> circline_set x_axis"
          by auto
        hence "poincare_collinear {0\<^sub>h, y, z}"
          unfolding poincare_collinear_def
          by force
        thus False
          using \<open>\<not> poincare_collinear {0\<^sub>h, y, z}\<close>
          by simp
      qed

      ultimately

      have "\<phi> * \<theta> < 0"
        using \<open>poincare_between y (of_complex v) z\<close>
        using poincare_between_x_axis_intersection[of y z "of_complex v"]
        using in_disc \<open>of_complex v \<in> unit_disc\<close> distinct
        using \<open>of_complex v \<in> circline_set ?yz\<close> \<open>of_complex v \<in> circline_set x_axis\<close>
        using \<open>\<phi> = arg z'\<close> \<open>\<theta> = arg y'\<close> *
        by (simp add: field_simps)

      have "\<phi> \<noteq> pi" "\<phi> \<noteq> 0"
        using \<open>z \<notin> circline_set x_axis\<close> * polar cis_pi
        unfolding circline_set_x_axis
        by auto

      have "\<theta> \<noteq> pi" "\<theta> \<noteq> 0"
        using \<open>y \<notin> circline_set x_axis\<close> * polar cis_pi
        unfolding circline_set_x_axis
        by auto

      have phi_sin: "\<phi> > 0 \<longleftrightarrow> sin \<phi> > 0" "\<phi> < 0 \<longleftrightarrow> sin \<phi> < 0"
        using \<open>\<phi> = arg z'\<close> \<open>\<phi> \<noteq> 0\<close> \<open>\<phi> \<noteq> pi\<close>
        using arg_bounded[of z']
        by (smt sin_gt_zero sin_le_zero sin_pi_minus sin_0_iff_canon sin_ge_zero)+

      have theta_sin: "\<theta> > 0 \<longleftrightarrow> sin \<theta> > 0" "\<theta> < 0 \<longleftrightarrow> sin \<theta> < 0"
        using \<open>\<theta> = arg y'\<close> \<open>\<theta> \<noteq> 0\<close> \<open>\<theta> \<noteq> pi\<close>
        using arg_bounded[of y']
        by (smt sin_gt_zero sin_le_zero sin_pi_minus sin_0_iff_canon sin_ge_zero)+

      have "sin \<phi> * sin \<theta> < 0"
        using \<open>\<phi> * \<theta> < 0\<close> phi_sin theta_sin
        by (simp add: mult_less_0_iff)

      have "sin (\<phi> - \<theta>) \<noteq> 0"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence "sin (\<phi> - \<theta>) = 0"
          by simp
        have "- 2 * pi < \<phi> - \<theta>" "\<phi> - \<theta> < 2 * pi"
          using \<open>\<phi> = arg z'\<close> \<open>\<theta> = arg y'\<close> arg_bounded[of z'] arg_bounded[of y'] \<open>\<phi> \<noteq> pi\<close> \<open>\<theta> \<noteq> pi\<close>
          by auto
        hence "\<phi> - \<theta> = -pi \<or> \<phi> - \<theta> = 0 \<or> \<phi> - \<theta> = pi"
          using \<open>sin (\<phi> - \<theta>) = 0\<close>
          by (smt sin_0_iff_canon sin_periodic_pi2)
        moreover
        {
          assume "\<phi> - \<theta> = - pi"
          hence "\<phi> = \<theta> - pi"
            by simp
          hence False
            using nondeg_yz
            using \<open>y' = cor ry * cis \<theta>\<close> \<open>z' = cor rz * cis \<phi>\<close> \<open>rz > 0\<close> \<open>ry > 0\<close>
            by auto
        }
        moreover
        {
          assume "\<phi> - \<theta> = 0"
          hence "\<phi> = \<theta>"
            by simp
          hence False
            using \<open>y' = cor ry * cis \<theta>\<close> \<open>z' = cor rz * cis \<phi>\<close> \<open>rz > 0\<close> \<open>ry > 0\<close>
            using nondeg_yz
            by auto
        }
        moreover
        {
          assume "\<phi> - \<theta> = pi"
          hence "\<phi> = \<theta> + pi"
            by simp
          hence False
            using \<open>y' = cor ry * cis \<theta>\<close> \<open>z' = cor rz * cis \<phi>\<close> \<open>rz > 0\<close> \<open>ry > 0\<close>
            using nondeg_yz
            by auto
        }
        ultimately
        show False
          by auto
      qed

      have "u \<notin> circline_set x_axis"
      proof-
        have "\<not> is_real u'"
          using * polar in_disc
          using \<open>\<phi> \<noteq> 0\<close> \<open>\<phi> = arg u'\<close> \<open>\<phi> \<noteq> pi\<close>  phi_sin(1) phi_sin(2)
          by (metis is_real_arg2)
        moreover
        have "u \<noteq> \<infinity>\<^sub>h"
          using in_disc
          by auto
        ultimately
        show ?thesis
          using * of_complex_inj[of u']
          unfolding circline_set_x_axis
          by auto
      qed

      let ?yu = "poincare_line y u"
      have nondeg_yu: "y' * cnj u' \<noteq> cnj u' * u'"
        using nondeg_yz polar \<open>ru > 0\<close> \<open>rz > 0\<close> distinct
        by auto

      {
        (* derive results simultaneously for both u and z *)
        fix r :: real
        assume "r > 0"

        have den: "cor ry * cis \<theta> * cnj 1 * cnj (cor r * cis \<phi>) * 1 - cor r * cis \<phi> * cnj 1 * cnj (cor ry * cis \<theta>) * 1 \<noteq> 0"
          using \<open>0 < r\<close> \<open>0 < ry\<close> nondeg
          by auto

        let ?A = "2 * r * ry * sin(\<phi> - \<theta>)"
        let ?B = "\<i> * (r * cis \<phi> * (1 + ry\<^sup>2) - ry * cis \<theta> * (1 + r\<^sup>2))"
        let ?ReB = "ry * (1 + r\<^sup>2) * sin \<theta> - r * (1 + ry\<^sup>2) * sin \<phi>"

        have "Re (\<i> * (r * cis (-\<phi>) * ry * cis (\<theta>) - ry * cis (-\<theta>) * r * cis (\<phi>))) = ?A"
          by (simp add: sin_diff field_simps)
        moreover
        have "cor ry * cis (- \<theta>) * (cor ry * cis \<theta>) = ry\<^sup>2"  "cor r * cis (- \<phi>) * (cor r * cis \<phi>) = r\<^sup>2"
          by (metis cis_inverse cis_neq_zero divide_complex_def cor_squared nonzero_mult_div_cancel_right power2_eq_square semiring_normalization_rules(15))+
        ultimately
        have 1: "poincare_line_cvec_cmat (of_complex_cvec (cor ry * cis \<theta>)) (of_complex_cvec (cor r * cis \<phi>)) = (?A, ?B, cnj ?B, ?A)"
          using den
          unfolding poincare_line_cvec_cmat_def of_complex_cvec_def Let_def prod.case
          by (simp add: field_simps)

        have 2: "is_real ?A"
          by simp
        let ?mix = "cis \<theta> * cis (- \<phi>) - cis (- \<theta>) * cis \<phi>"
        have "is_imag ?mix"
          using eq_minus_cnj_iff_imag[of ?mix]
          by simp
        hence "Im ?mix \<noteq> 0"
          using nondeg
          using complex.expand[of ?mix 0]
          by auto
        hence 3: "Re ?A \<noteq> 0"
          using \<open>r > 0\<close> \<open>ry > 0\<close>
          by (simp add: sin_diff field_simps)

        have "?A \<noteq> 0"
          using 2 3
          by auto
        hence 4: "cor ?A \<noteq> 0"
          using 2 3
          by (metis zero_complex.simps(1))

        have 5: "?ReB / ?A = (sin \<theta>) / (2 * sin(\<phi> - \<theta>)) * (1/r + r) - (sin \<phi>) / (2 * sin (\<phi> - \<theta>)) * (1/ry + ry)" 
          using \<open>ry > 0\<close> \<open>r > 0\<close>
          apply (subst diff_divide_distrib)             
          apply (subst add_frac_num, simp)
          apply (subst add_frac_num, simp)
          apply (simp add: power2_eq_square mult.commute)
          apply (simp add: field_simps)
          done

        have "poincare_line_cvec_cmat (of_complex_cvec (cor ry * cis \<theta>)) (of_complex_cvec (cor r * cis \<phi>)) = (?A, ?B, cnj ?B, ?A) \<and>
                is_real ?A \<and> Re ?A \<noteq> 0 \<and> ?A \<noteq> 0 \<and> cor ?A \<noteq> 0 \<and>
                Re ?B = ?ReB \<and>
                ?ReB / ?A = (sin \<theta>) / (2 * sin(\<phi> - \<theta>)) * (1/r + r) - (sin \<phi>) / (2 * sin (\<phi> - \<theta>)) * (1/ry + ry)"
          using 1 2 3 4 5
          by auto
      }
      note ** = this

      let ?Ayz = "2 * rz * ry * sin (\<phi> - \<theta>)"
      let ?Byz = "\<i> * (rz * cis \<phi> * (1 + ry\<^sup>2) - ry * cis \<theta> * (1 + rz\<^sup>2))"
      let ?ReByz = "ry * (1 + rz\<^sup>2) * sin \<theta> - rz * (1 + ry\<^sup>2) * sin \<phi>"
      let ?Kz = "(sin \<theta>) / (2 * sin(\<phi> - \<theta>)) * (1/rz + rz) - (sin \<phi>) / (2 * sin (\<phi> - \<theta>)) * (1/ry + ry)"
      have yz: "poincare_line_cvec_cmat (of_complex_cvec (cor ry * cis \<theta>)) (of_complex_cvec (cor rz * cis \<phi>)) = (?Ayz, ?Byz, cnj ?Byz, ?Ayz)"
        "is_real ?Ayz" "Re ?Ayz \<noteq> 0" "?Ayz \<noteq> 0" "cor ?Ayz \<noteq> 0" "Re ?Byz = ?ReByz" and Kz: "?ReByz / ?Ayz = ?Kz"
        using **[OF \<open>0 < rz\<close>]
        by auto

      let ?Ayu = "2 * ru * ry * sin (\<phi> - \<theta>)"
      let ?Byu = "\<i> * (ru * cis \<phi> * (1 + ry\<^sup>2) - ry * cis \<theta> * (1 + ru\<^sup>2))"
      let ?ReByu = "ry * (1 + ru\<^sup>2) * sin \<theta> - ru * (1 + ry\<^sup>2) * sin \<phi>"
      let ?Ku = "(sin \<theta>) / (2 * sin(\<phi> - \<theta>)) * (1/ru + ru) - (sin \<phi>) / (2 * sin (\<phi> - \<theta>)) * (1/ry + ry)"
      have yu: "poincare_line_cvec_cmat (of_complex_cvec (cor ry * cis \<theta>)) (of_complex_cvec (cor ru * cis \<phi>)) = (?Ayu, ?Byu, cnj ?Byu, ?Ayu)"
        "is_real ?Ayu" "Re ?Ayu \<noteq> 0" "?Ayu \<noteq> 0" "cor ?Ayu \<noteq> 0" "Re ?Byu = ?ReByu" and Ku: "?ReByu / ?Ayu = ?Ku"
        using **[OF \<open>0 < ru\<close>]
        by auto

      have "?Ayz \<noteq> 0"
        using \<open>sin (\<phi> - \<theta>) \<noteq> 0\<close> \<open>ry > 0\<close> \<open>rz > 0\<close>
        by auto

      have "Re ?Byz / ?Ayz < -1"
        using \<open>intersects_x_axis_positive ?yz\<close>
          * \<open>y' = cor ry * cis \<theta>\<close> \<open>z' = cor rz * cis \<phi>\<close> \<open>u' = cor ru * cis \<phi>\<close>
        apply simp
        apply (transfer fixing: ry rz ru \<theta> \<phi>)
        apply (transfer fixing: ry rz ru \<theta> \<phi>)
      proof-
        assume "intersects_x_axis_positive_cmat (poincare_line_cvec_cmat (of_complex_cvec (cor ry * cis \<theta>)) (of_complex_cvec (cor rz * cis \<phi>)))"
        thus "(ry * sin \<theta> * (1 + rz\<^sup>2) - rz * sin \<phi> * (1 + ry\<^sup>2)) / (2 * rz * ry * sin (\<phi> - \<theta>)) < - 1"
          using yz
          by simp
      qed

      have "?ReByz / ?Ayz \<ge> ?ReByu / ?Ayu"
      proof (cases "sin \<phi> > 0")
        case True
        hence "sin \<theta> < 0"
          using \<open>sin \<phi> * sin \<theta> < 0\<close>
          by (smt mult_nonneg_nonneg)

        have "?ReByz < 0"
        proof-
          have "ry * (1 + rz\<^sup>2) * sin \<theta> < 0"
            using \<open>ry > 0\<close> \<open>rz > 0\<close>
            using \<open>sin \<theta> < 0\<close>
            by (smt mult_pos_neg mult_pos_pos zero_less_power)
          moreover
          have "rz * (1 + ry\<^sup>2) * sin \<phi> > 0"
            using \<open>ry > 0\<close> \<open>rz > 0\<close>
            using \<open>sin \<phi> > 0\<close>
            by (smt mult_pos_neg mult_pos_pos zero_less_power)
          ultimately
          show ?thesis
            by simp
        qed
        have "?Ayz > 0"
          using \<open>Re ?Byz / ?Ayz < -1\<close> \<open>Re ?Byz = ?ReByz\<close> \<open>?ReByz < 0\<close>
          by (smt divide_less_0_iff)
        hence "sin (\<phi> - \<theta>) > 0"
          using \<open>ry > 0\<close> \<open>rz > 0\<close>
          by (smt mult_pos_pos zero_less_mult_pos)

        have "1 / ru + ru \<ge> 1 / rz + rz"
          using Pasch_fun_mono[of ru rz] \<open>0 < ru\<close> \<open>ru \<le> rz\<close> \<open>rz < 1\<close>
          by simp
        hence "sin \<theta> * (1 / ru + ru) \<le> sin \<theta> * (1 / rz + rz)"
          using \<open>sin \<theta> < 0\<close>
          by auto
        thus ?thesis
          using \<open>ru > 0\<close> \<open>rz > 0\<close> \<open>ru \<le> rz\<close> \<open>rz < 1\<close> \<open>?Ayz > 0\<close> \<open>sin (\<phi> - \<theta>) > 0\<close>
          using divide_right_mono[of "sin \<theta> * (1 / ru + ru)" "sin \<theta> * (1 / rz + rz)" "2 * sin (\<phi> - \<theta>)"]
          by (subst Kz, subst Ku) simp
      next
        assume "\<not> sin \<phi> > 0"
        hence "sin \<phi> < 0"
          using \<open>sin \<phi> * sin \<theta> < 0\<close>
          by (cases "sin \<phi> = 0", simp_all)
        hence "sin \<theta> > 0"
          using \<open>sin \<phi> * sin \<theta> < 0\<close>
          by (smt mult_nonpos_nonpos)
        have "?ReByz > 0"
        proof-
          have "ry * (1 + rz\<^sup>2) * sin \<theta> > 0"
            using \<open>ry > 0\<close> \<open>rz > 0\<close>
            using \<open>sin \<theta> > 0\<close>
            by (smt mult_pos_neg mult_pos_pos zero_less_power)
          moreover
          have "rz * (1 + ry\<^sup>2) * sin \<phi> < 0"
            using \<open>ry > 0\<close> \<open>rz > 0\<close>
            using \<open>sin \<phi> < 0\<close>
            by (smt mult_pos_neg mult_pos_pos zero_less_power)
          ultimately
          show ?thesis
            by simp
        qed
        have "?Ayz < 0"
          using \<open>Re ?Byz / ?Ayz < -1\<close> \<open>?Ayz \<noteq> 0\<close> \<open>Re ?Byz = ?ReByz\<close> \<open>?ReByz > 0\<close>
          by (smt divide_less_0_iff)
        hence "sin (\<phi> - \<theta>) < 0"
          using \<open>ry > 0\<close> \<open>rz > 0\<close>
          by (smt mult_nonneg_nonneg)

        have "1 / ru + ru \<ge> 1 / rz + rz"
          using Pasch_fun_mono[of ru rz] \<open>0 < ru\<close> \<open>ru \<le> rz\<close> \<open>rz < 1\<close>
          by simp
        hence "sin \<theta> * (1 / ru + ru) \<ge> sin \<theta> * (1 / rz + rz)"
          using \<open>sin \<theta> > 0\<close>
          by auto
        thus ?thesis
          using \<open>ru > 0\<close> \<open>rz > 0\<close> \<open>ru \<le> rz\<close> \<open>rz < 1\<close> \<open>?Ayz < 0\<close> \<open>sin (\<phi> - \<theta>) < 0\<close>
          using divide_right_mono_neg[of  "sin \<theta> * (1 / rz + rz)" "sin \<theta> * (1 / ru + ru)" "2 * sin (\<phi> - \<theta>)"]
          by (subst Kz, subst Ku) simp
      qed

      have "intersects_x_axis_positive ?yu"
        using * \<open>y' = cor ry * cis \<theta>\<close> \<open>z' = cor rz * cis \<phi>\<close> \<open>u' = cor ru * cis \<phi>\<close>
        apply simp
        apply (transfer fixing: ry rz ru \<theta> \<phi>)
        apply (transfer fixing: ry rz ru \<theta> \<phi>)
      proof-
        have "Re ?Byu / ?Ayu < -1"
          using \<open>Re ?Byz / ?Ayz < -1\<close> \<open>?ReByz / ?Ayz \<ge> ?ReByu / ?Ayu\<close>
          by (subst (asm) \<open>Re ?Byz = ?ReByz\<close>, subst \<open>Re ?Byu = ?ReByu\<close>) simp
        thus "intersects_x_axis_positive_cmat (poincare_line_cvec_cmat (of_complex_cvec (cor ry * cis \<theta>)) (of_complex_cvec (cor ru * cis \<phi>)))"
          using yu
          by simp
      qed

      let ?a = "calc_x_axis_intersection ?yu"
      have "?a \<in> positive_x_axis" "?a \<in> circline_set ?yu" "?a \<in> unit_disc"
        using \<open>intersects_x_axis_positive ?yu\<close>
        using intersects_x_axis_positive_iff'[of ?yu] \<open>y \<noteq> u\<close>
        by auto

      then obtain a' where a': "?a = of_complex a'" "is_real a'" "Re a' > 0" "Re a' < 1"
        unfolding positive_x_axis_def circline_set_x_axis
        by (auto simp add: cmod_eq_Re)

      have "intersects_x_axis ?yz" "intersects_x_axis ?yu"
        using \<open>intersects_x_axis_positive ?yz\<close> \<open>intersects_x_axis_positive ?yu\<close>
        by auto

      show "\<exists>a. a \<in> unit_disc \<and> poincare_between u a y \<and> poincare_between 0\<^sub>h a (of_complex v)"
      proof (rule_tac x="?a" in exI, safe)
        show "poincare_between u ?a y"
          using poincare_between_x_axis_intersection[of y u ?a]
          using calc_x_axis_intersection[OF is_poincare_line_poincare_line[OF \<open>y \<noteq> u\<close>] \<open>intersects_x_axis ?yu\<close>]
          using calc_x_axis_intersection_in_unit_disc[OF is_poincare_line_poincare_line[OF \<open>y \<noteq> u\<close>] \<open>intersects_x_axis ?yu\<close>]
          using in_disc \<open>y \<noteq> u\<close> \<open>y \<notin> circline_set x_axis\<close> \<open>u \<notin> circline_set x_axis\<close>
          using * \<open>\<phi> = arg u'\<close> \<open>\<theta> = arg y'\<close> \<open>\<phi> * \<theta> < 0\<close>
          by (subst poincare_between_rev, auto simp add: mult.commute)
      next
        show "poincare_between 0\<^sub>h ?a (of_complex v)"
        proof-
          have "-?ReByz / ?Ayz \<le> -?ReByu / ?Ayu"
            using \<open>?ReByz / ?Ayz \<ge> ?ReByu / ?Ayu\<close>
            by linarith
          have "outward ?yz ?yu"
            using * \<open>y' = cor ry * cis \<theta>\<close> \<open>z' = cor rz * cis \<phi>\<close> \<open>u' = cor ru * cis \<phi>\<close>
            apply simp
            apply (transfer fixing: ry rz ru \<theta> \<phi>)
            apply (transfer fixing: ry rz ru \<theta> \<phi>)
            apply (subst yz yu)+
            unfolding outward_cmat_def
            apply (simp only: Let_def prod.case)
            apply (subst yz yu)+
            using \<open>-?ReByz / ?Ayz \<le> -?ReByu / ?Ayu\<close>
            by simp
          hence "Re a' \<le> Re v"
            using \<open>?v = of_complex v\<close>
            using \<open>?a = of_complex a'\<close>
            using \<open>intersects_x_axis_positive ?yz\<close> \<open>intersects_x_axis_positive ?yu\<close>
            using outward[OF is_poincare_line_poincare_line[OF \<open>y \<noteq> z\<close>] is_poincare_line_poincare_line[OF \<open>y \<noteq> u\<close>]]
            by simp
          thus ?thesis
            using \<open>?v = of_complex v\<close>
            using poincare_between_x_axis_0uv[of "Re a'" "Re v"] a' v
            by simp
        qed
      next
        show "?a \<in> unit_disc"
          by fact
      qed
    qed
  next
    show "x \<in> unit_disc" "v \<in> unit_disc" "x \<noteq> v"
      using assms
      by auto
  next
    fix M x v
    let ?Mx = "moebius_pt M x" and ?Mv = "moebius_pt M v"
    assume 1: "unit_disc_fix M" "x \<in> unit_disc" "v \<in> unit_disc" "x \<noteq> v"
    assume 2: "?P ?Mx ?Mv"
    show "?P x v"
    proof safe
      fix y z u
      let ?My = "moebius_pt M y" and ?Mz = "moebius_pt M z" and ?Mu = "moebius_pt M u"
      assume "distinct [x, y, z, u, v]" "\<not> poincare_collinear {x, y, z}" "y \<in> unit_disc" "z \<in> unit_disc" "u \<in> unit_disc"
             "poincare_between x u z" "poincare_between y v z"
      hence "\<exists> Ma. Ma \<in> unit_disc \<and> poincare_between ?Mu Ma ?My \<and> poincare_between ?Mx Ma ?Mv"
        using 1 2[rule_format, of ?My ?Mz ?Mu]
        by simp
      then obtain Ma where Ma: "Ma \<in> unit_disc" "poincare_between ?Mu Ma ?My \<and> poincare_between ?Mx Ma ?Mv"
        by blast
      let ?a = "moebius_pt (-M) Ma"
      let ?Ma = "moebius_pt M ?a"
      have "?Ma = Ma"
        by (metis moebius_pt_invert uminus_moebius_def)
      hence "?Ma \<in> unit_disc" "poincare_between ?Mu ?Ma ?My \<and> poincare_between ?Mx ?Ma ?Mv"
        using Ma
        by auto
      thus "\<exists>a. a \<in> unit_disc \<and> poincare_between u a y \<and> poincare_between x a v"
        using unit_disc_fix_moebius_inv[OF \<open>unit_disc_fix M\<close>] \<open>unit_disc_fix M\<close> \<open>Ma \<in> unit_disc\<close>
        using \<open>u \<in> unit_disc\<close> \<open>v \<in> unit_disc\<close> \<open>x \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close>
        by (rule_tac x="?a" in exI, simp del: moebius_pt_comp_inv_right)
    qed
  qed
  thus ?thesis
    using assms
    by auto
qed

text\<open>Pasch axiom, only degenerative cases.\<close>
lemma Pasch_deg:
  assumes "x \<in> unit_disc" and "y \<in> unit_disc" and "z \<in> unit_disc" and "u \<in> unit_disc" and "v \<in> unit_disc"
  assumes "\<not> distinct [x, y, z, u, v] \<or> poincare_collinear {x, y, z}"
  assumes "poincare_between x u z" and "poincare_between y v z"
  shows "\<exists> a. a \<in> unit_disc \<and> poincare_between u a y \<and> poincare_between x a v"
proof(cases "poincare_collinear {x, y, z}")
  case True
  hence "poincare_between x y z \<or> poincare_between y x z \<or> poincare_between y z x"
    using assms(1, 2, 3) poincare_collinear3_between poincare_between_rev by blast
  show ?thesis
  proof(cases "poincare_between x y z")
    case True
    have "poincare_between x y v"
      using True assms poincare_between_transitivity
      by (meson poincare_between_rev)
    thus ?thesis
      using assms(2)
      by (rule_tac x="y" in exI, simp)
  next
    case False
    hence "poincare_between y x z \<or> poincare_between y z x"
      using \<open>poincare_between x y z \<or> poincare_between y x z \<or> poincare_between y z x\<close>
      by simp
    show ?thesis
    proof(cases "poincare_between y x z")
      case True
      hence "poincare_between u x y"
        using assms
        by (meson poincare_between_rev poincare_between_transitivity)
      thus ?thesis
        using assms
        by (rule_tac x="x" in exI, simp)
    next
      case False
      hence "poincare_between y z x"
        using \<open>poincare_between y x z \<or> poincare_between y z x\<close>
        by auto
      hence "poincare_between x z v"
        using assms
        by (meson poincare_between_rev poincare_between_transitivity)
      hence "poincare_between x u v"
        using assms poincare_between_transitivity poincare_between_rev
        by (smt poincare_between_sum_distances)
      thus ?thesis
        using assms
        by (rule_tac x="u" in exI, simp)
    qed
  qed
next
  case False
  hence "\<not> distinct [x, y, z, u, v]"
    using assms(6) by auto
  show ?thesis
  proof(cases "u=z")
    case True
    thus ?thesis
      using assms
      apply(rule_tac x="v" in exI)
      by(simp add:poincare_between_rev)
  next
    case False (* "u \<noteq> z" *)
    hence "x \<noteq> z"
      using assms poincare_between_sandwich by blast
    show ?thesis
    proof(cases "v=z")
      case True
      thus ?thesis
        using assms
        by (rule_tac x="u" in exI, simp)
    next
      case False (* v \<noteq> z *)
      hence "y \<noteq> z"
        using assms poincare_between_sandwich by blast
      show ?thesis
      proof(cases "u = x")
        case True
        thus ?thesis
          using assms
          by (rule_tac x="x" in exI, simp)
      next
        case False (*u \<noteq> x*)
        have "x \<noteq> y"
          using assms \<open>\<not> poincare_collinear {x, y, z}\<close>
          by fastforce
        have "x \<noteq> v"
          using assms \<open>\<not> poincare_collinear {x, y, z}\<close>
          by (metis insert_commute poincare_between_poincare_collinear)
        have "u \<noteq> y"
          using assms \<open>\<not> poincare_collinear {x, y, z}\<close>
          using poincare_between_poincare_collinear by blast
        have "u \<noteq> v"
        proof(rule ccontr)
          assume "\<not> u \<noteq> v"
          hence "poincare_between x v z"
            using assms by auto
          hence "x \<in> circline_set (poincare_line z v)"
            using poincare_between_rev[of x v z]
            using poincare_between_poincare_line_uvz[of z v x]
            using assms \<open>v \<noteq> z\<close>
            by auto
          have "y \<in> circline_set (poincare_line z v)"
            using assms \<open>\<not> u \<noteq> v\<close> 
            using poincare_between_rev[of y v z]
            using poincare_between_poincare_line_uvz[of z v y]
            using assms \<open>v \<noteq> z\<close>
            by auto
          have "z \<in> circline_set (poincare_line z v)"
            using ex_poincare_line_two_points[of z v] \<open>v \<noteq> z\<close>
            by auto
          have "is_poincare_line (poincare_line z v)"
            using \<open>v \<noteq> z\<close>
            by auto
          hence "poincare_collinear {x, y, z}"
            using \<open>x \<in> circline_set (poincare_line z v)\<close>
            using \<open>y \<in> circline_set (poincare_line z v)\<close>
            using \<open>z \<in> circline_set (poincare_line z v)\<close>
            unfolding poincare_collinear_def
            by (rule_tac x="poincare_line z v" in exI, simp)            
          thus False
            using \<open>\<not> poincare_collinear {x, y, z}\<close> by simp
        qed
        have "v = y"
          using \<open>u \<noteq> v\<close> \<open>u \<noteq> y\<close> \<open>x \<noteq> v\<close> \<open>x \<noteq> y\<close> \<open>u \<noteq> x\<close> \<open>y \<noteq> z\<close> \<open>v \<noteq> z\<close> \<open>x \<noteq> z\<close> \<open>u \<noteq> z\<close>
          using \<open>\<not> distinct [x, y, z, u, v]\<close>
          by auto
        thus ?thesis
          using assms
          by (rule_tac x="y" in exI, simp)
      qed
    qed
  qed
qed

text \<open>Axiom of Pasch\<close>
lemma Pasch:
  assumes "x \<in> unit_disc" and "y \<in> unit_disc" and "z \<in> unit_disc" and "u \<in> unit_disc" and "v \<in> unit_disc"
  assumes "poincare_between x u z" and "poincare_between y v z"
  shows "\<exists> a. a \<in> unit_disc \<and> poincare_between u a y \<and> poincare_between x a v"
proof(cases "distinct [x, y, z, u, v] \<and> \<not> poincare_collinear {x, y, z}")
  case True
  thus ?thesis
    using assms Pasch_nondeg by auto
next
  case False
  thus ?thesis
    using assms Pasch_deg by auto
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Segment construction axiom\<close>
(* ------------------------------------------------------------------ *)

lemma segment_construction:
  assumes "x \<in> unit_disc" and "y \<in> unit_disc"
  assumes "a \<in> unit_disc" and "b \<in> unit_disc"
  shows "\<exists> z. z \<in> unit_disc \<and> poincare_between x y z \<and> poincare_distance y z = poincare_distance a b"
proof-
  obtain d where d: "d = poincare_distance a b"
    by auto
  have "d \<ge> 0"
    using assms
    by (simp add: d poincare_distance_ge0)

  have "\<exists> z. z \<in> unit_disc \<and> poincare_between x y z \<and> poincare_distance y z = d" (is "?P x y")
  proof (cases "x = y")
    case True
    have "\<exists> z. z \<in> unit_disc \<and> poincare_distance x z = d"
    proof (rule wlog_zero)
      show "\<exists> z. z \<in> unit_disc \<and> poincare_distance 0\<^sub>h z = d"
        using ex_x_axis_poincare_distance_negative[of d] \<open>d \<ge> 0\<close>
        by blast
    next
      show "x \<in> unit_disc"
        by fact
    next
      fix a u
      assume "u \<in> unit_disc" "cmod a < 1"
      assume "\<exists>z. z \<in> unit_disc \<and> poincare_distance (moebius_pt (blaschke a) u) z = d"
      then obtain z where *: "z \<in> unit_disc" "poincare_distance (moebius_pt (blaschke a) u) z = d"
        by auto
      obtain z' where z': "z = moebius_pt (blaschke a) z'" "z' \<in> unit_disc"
        using \<open>z \<in> unit_disc\<close>
        using unit_disc_fix_iff[of "blaschke a"] \<open>cmod a < 1\<close>
        using blaschke_unit_disc_fix[of a]
        by blast

      show "\<exists>z. z \<in> unit_disc \<and> poincare_distance u z = d"
        using * z' \<open>u : unit_disc\<close>
        using blaschke_unit_disc_fix[of a] \<open>cmod a < 1\<close>
        by (rule_tac x=z' in exI, simp)
    qed
    thus ?thesis
      using \<open>x = y\<close>
      unfolding poincare_between_def
      by auto
  next
    case False
    show ?thesis
    proof (rule wlog_positive_x_axis[where P="\<lambda> y x. ?P x y"])
      fix x
      assume "is_real x" "0 < Re x" "Re x < 1"

      then obtain z where z: "is_real z" "Re z \<le> 0" "- 1 < Re z" "of_complex z \<in> unit_disc"
        "of_complex z \<in> unit_disc" "of_complex z \<in> circline_set x_axis" "poincare_distance 0\<^sub>h (of_complex z) = d"
        using ex_x_axis_poincare_distance_negative[of d] \<open>d \<ge> 0\<close>
        by auto

      have "poincare_between (of_complex x) 0\<^sub>h (of_complex z)"
      proof (cases "z = 0")
        case True
        thus ?thesis
          unfolding poincare_between_def
          by auto
      next
        case False
        have "x \<noteq> 0"
          using \<open>is_real x\<close> \<open>Re x > 0\<close>
          by auto
        thus ?thesis
          using poincare_between_x_axis_u0v[of x z]
          using z \<open>is_real x\<close> \<open>x \<noteq> 0\<close> \<open>Re x > 0\<close> False
          using complex_eq_if_Re_eq mult_pos_neg
          by fastforce
    qed
    thus "?P (of_complex x) 0\<^sub>h"
      using \<open>poincare_distance 0\<^sub>h (of_complex z) = d\<close> \<open>of_complex z \<in> unit_disc\<close>
      by blast
  next
    show "x \<in> unit_disc" "y \<in> unit_disc"
      by fact+
  next
    show "y \<noteq> x" using \<open>x \<noteq> y\<close> by simp
  next
    fix M u v
    assume "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
    assume "?P (moebius_pt M v) (moebius_pt M u)"
    then obtain z where *: "z \<in> unit_disc" "poincare_between (moebius_pt M v) (moebius_pt M u) z" "poincare_distance (moebius_pt M u) z = d"
      by auto
    obtain z' where z': "z = moebius_pt M z'" "z' \<in> unit_disc"
        using \<open>z \<in> unit_disc\<close>
        using unit_disc_fix_iff[of M] \<open>unit_disc_fix M\<close>
        by blast
      thus "?P v u"
        using * \<open>u \<in> unit_disc\<close> \<open>v \<in> unit_disc\<close> \<open>unit_disc_fix M\<close>
        by auto
    qed
  qed
  thus ?thesis
    using assms d
    by auto
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Five segment axiom\<close>
(* ------------------------------------------------------------------ *)

lemma five_segment_axiom:
  assumes
     in_disc: "x \<in> unit_disc"  "y \<in> unit_disc" "z \<in> unit_disc" "u \<in> unit_disc" and
     in_disc': "x' \<in> unit_disc" "y' \<in> unit_disc" "z' \<in> unit_disc" "u' \<in> unit_disc" and
      "x \<noteq> y" and
      betw: "poincare_between x y z" "poincare_between x' y' z'" and
      xy: "poincare_distance x y = poincare_distance x' y'" and
      xu: "poincare_distance x u = poincare_distance x' u'" and
      yu: "poincare_distance y u = poincare_distance y' u'" and
      yz: "poincare_distance y z = poincare_distance y' z'"
    shows
     "poincare_distance z u = poincare_distance z' u'"
proof-
  from assms obtain M where
  M: "unit_disc_fix_f M" "M x = x'" "M u = u'" "M y = y'"
    using unit_disc_fix_f_congruent_triangles[of x y u]
    by blast
  have "M z = z'"
  proof (rule unique_poincare_distance_on_ray[where u=x' and v=y' and y="M z" and z=z' and d="poincare_distance x z"])
    show "0 \<le> poincare_distance x z"
      using poincare_distance_ge0 in_disc
      by simp
  next
    show "x' \<noteq> y'"
      using M \<open>x \<noteq> y\<close>
      using in_disc in_disc' poincare_distance_eq_0_iff xy
      by auto
  next
    show "poincare_distance x' (M z) = poincare_distance x z"
      using M in_disc
      unfolding unit_disc_fix_f_def
      by auto
  next
    show "M z \<in> unit_disc"
      using M in_disc
      unfolding unit_disc_fix_f_def
      by auto
  next
    show "poincare_distance x' z' = poincare_distance x z"
      using xy yz betw
      using poincare_between_sum_distances[of x y z]
      using poincare_between_sum_distances[of x' y' z']
      using in_disc in_disc'
      by auto
  next
    show "poincare_between x' y' (M z)"
      using M
      using in_disc betw
      unfolding unit_disc_fix_f_def
      by auto
  qed fact+
  thus ?thesis
    using \<open>unit_disc_fix_f M\<close>
    using in_disc in_disc'
    \<open>M u = u'\<close>
    unfolding unit_disc_fix_f_def
    by auto
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Upper dimension axiom\<close>
(* ------------------------------------------------------------------ *)

lemma upper_dimension_axiom:
  assumes in_disc: "x \<in> unit_disc" "y \<in> unit_disc" "z \<in> unit_disc" "u \<in> unit_disc" "v \<in> unit_disc"
  assumes "poincare_distance x u = poincare_distance x v"
          "poincare_distance y u = poincare_distance y v"
          "poincare_distance z u = poincare_distance z v"
          "u \<noteq> v"
  shows "poincare_between x y z \<or> poincare_between y z x \<or> poincare_between z x y"
proof (cases "x = y \<or> y = z \<or> x = z")
  case True
  thus ?thesis
    using in_disc
    by auto
next
  case False
  hence "x \<noteq> y" "x \<noteq> z" "y \<noteq> z"
    by auto
  let ?cong = "\<lambda> a b a' b'. poincare_distance a b = poincare_distance a' b'"
  have "\<forall> z u v. z \<in> unit_disc \<and> u \<in> unit_disc \<and> v \<in> unit_disc \<and>
                 ?cong x u x v \<and> ?cong y u y v \<and> ?cong z u z v  \<and> u \<noteq> v \<longrightarrow>
                 poincare_collinear {x, y, z}" (is "?P x y")
  proof (rule wlog_positive_x_axis[where P="?P"])
    fix x
    assume x: "is_real x" "0 < Re x" "Re x < 1"
    hence "x \<noteq> 0"
      by auto
    have "0\<^sub>h \<in> circline_set x_axis"
      by simp
    show "?P 0\<^sub>h (of_complex x)"
    proof safe
      fix z u v
      assume in_disc: "z \<in> unit_disc" "u \<in> unit_disc" "v \<in> unit_disc"
      then obtain z' u' v' where zuv: "z = of_complex z'" "u = of_complex u'" "v = of_complex v'"
        using inf_or_of_complex[of z] inf_or_of_complex[of u] inf_or_of_complex[of v]
        by auto

      assume cong: "?cong 0\<^sub>h u 0\<^sub>h v" "?cong (of_complex x) u (of_complex x) v" "?cong z u z v" "u \<noteq> v"

      let ?r0 = "poincare_distance 0\<^sub>h u" and
          ?rx = "poincare_distance (of_complex x) u"

      have "?r0 > 0" "?rx > 0"
        using in_disc  cong
        using poincare_distance_eq_0_iff[of "0\<^sub>h" u] poincare_distance_ge0[of "0\<^sub>h" u]
        using poincare_distance_eq_0_iff[of "0\<^sub>h" v] poincare_distance_ge0[of "0\<^sub>h" v]
        using poincare_distance_eq_0_iff[of "of_complex x" u] poincare_distance_ge0[of "of_complex x" u]
        using poincare_distance_eq_0_iff[of "of_complex x" v] poincare_distance_ge0[of "of_complex x" v]
        using x
        by (auto simp add: cmod_eq_Re)

      let ?pc0 = "poincare_circle 0\<^sub>h ?r0" and
          ?pcx = "poincare_circle (of_complex x) ?rx"
      have "u \<in> ?pc0 \<inter> ?pcx" "v \<in> ?pc0 \<inter> ?pcx"
        using in_disc cong
        by (auto simp add: poincare_circle_def)
      hence "u = conjugate v"
        using intersect_poincare_circles_x_axis[of 0 x ?r0 ?rx u v]
        using x \<open>x \<noteq> 0\<close> \<open>u \<noteq> v\<close> \<open>?r0 > 0\<close> \<open>?rx > 0\<close>
        by simp

      let ?ru = "poincare_distance u z"
      have "?ru > 0"
        using poincare_distance_ge0[of u z] in_disc
        using cong
        using poincare_distance_eq_0_iff[of z u] poincare_distance_eq_0_iff[of z v]
        using poincare_distance_eq_0_iff
        by force

      have "z \<in> poincare_circle u ?ru \<inter> poincare_circle v ?ru"
        using cong in_disc
        unfolding poincare_circle_def
        by (simp add: poincare_distance_sym)

      hence "is_real z'"
        using intersect_poincare_circles_conjugate_centers[of u v ?ru z] \<open>u = conjugate v\<close> zuv
        using in_disc \<open>u \<noteq> v\<close> \<open>?ru > 0\<close>
        by simp

      thus "poincare_collinear {0\<^sub>h, of_complex x, z}"
        using poincare_line_0_real_is_x_axis[of "of_complex x"] x \<open>x \<noteq> 0\<close> zuv \<open>0\<^sub>h \<in> circline_set x_axis\<close>
        unfolding poincare_collinear_def
        by (rule_tac x=x_axis in exI, auto simp add: circline_set_x_axis)
    qed
  next
    fix M x y
    assume 1: "unit_disc_fix M" "x \<in> unit_disc" "y \<in> unit_disc" "x \<noteq> y"
    assume 2: "?P (moebius_pt M x) (moebius_pt M y)"
    show "?P x y"
    proof safe
      fix z u v
      assume "z \<in> unit_disc" "u \<in> unit_disc" "v \<in> unit_disc"
             "?cong x u x v" "?cong y u y v" "?cong z u z v" "u \<noteq> v"
      hence "poincare_collinear {moebius_pt M x, moebius_pt M y, moebius_pt M z}"
        using 1 2[rule_format, of "moebius_pt M z" "moebius_pt M u" "moebius_pt M v"]
        by simp
      then obtain p where "is_poincare_line p" "{moebius_pt M x, moebius_pt M y, moebius_pt M z} \<subseteq> circline_set p"
        unfolding poincare_collinear_def
        by auto
      thus "poincare_collinear {x, y, z}"
        using \<open>unit_disc_fix M\<close>
        unfolding poincare_collinear_def
        by (rule_tac x="moebius_circline (-M) p" in exI, auto)
    qed
  qed fact+

  thus ?thesis
    using assms
    using poincare_collinear3_between[of x y z]
    using poincare_between_rev
    by auto
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Lower dimension axiom\<close>
(* ------------------------------------------------------------------ *)

lemma lower_dimension_axiom:
  shows "\<exists> a \<in> unit_disc. \<exists> b \<in> unit_disc. \<exists> c \<in> unit_disc.
            \<not> poincare_between a b c \<and> \<not> poincare_between b c a \<and> \<not> poincare_between c a b"
proof-
  let ?u = "of_complex (1/2)" and ?v = "of_complex (\<i>/2)"
  have 1: "0\<^sub>h \<in> unit_disc" and 2: "?u \<in> unit_disc" and 3: "?v \<in> unit_disc"
    by simp_all
  have *: "\<not> poincare_collinear {0\<^sub>h, ?u, ?v}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain p where "is_poincare_line p" "{0\<^sub>h, ?u, ?v} \<subseteq> circline_set p"
      unfolding poincare_collinear_def
      by auto
    moreover
    have "of_complex (1 / 2) \<noteq> of_complex (\<i> / 2)"
      using of_complex_inj
      by fastforce
    ultimately
    have "0\<^sub>h \<in> circline_set (poincare_line ?u ?v)"
      using unique_poincare_line[of ?u ?v p]
      by auto
    thus False
      unfolding circline_set_def
      by simp (transfer, transfer, simp add: vec_cnj_def)
  qed
  show ?thesis
    apply (rule_tac x="0\<^sub>h" in bexI, rule_tac x="?u" in bexI, rule_tac x="?v" in bexI)
    apply (rule ccontr, auto)
    using *
    using poincare_between_poincare_collinear[OF 1 2 3]
    using poincare_between_poincare_collinear[OF 2 3 1]
    using poincare_between_poincare_collinear[OF 3 1 2]
    by (metis insert_commute)+
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Negated Euclidean axiom\<close>
(* ------------------------------------------------------------------ *)

lemma negated_euclidean_axiom_aux:
  assumes "on_circline H (of_complex (1/2 + \<i>/2))" and "is_poincare_line H"
  assumes "intersects_x_axis_positive H"
  shows "\<not> intersects_y_axis_positive H"
  using assms
proof (transfer, transfer)
  fix H
  assume hh: "hermitean H \<and> H \<noteq> mat_zero" "is_poincare_line_cmat H"
  obtain A B C D where "H = (A, B, C, D)"
    by (cases H, auto)
  hence *: "is_real A" "H = (A, B, cnj B, A)" "(cmod B)\<^sup>2 > (cmod A)\<^sup>2"
    using hermitean_elems[of A B C D] hh
    by auto

  assume "intersects_x_axis_positive_cmat H"
  hence "Re A \<noteq> 0" "Re B / Re A < - 1"
    using *
    by auto

  assume "on_circline_cmat_cvec H (of_complex_cvec (1 / 2 + \<i> / 2))"
  hence "6*A + 4*Re B + 4*Im B = 0"
    using *
    unfolding cor_mult
    apply (subst Re_express_cnj[of B])
    apply (subst Im_express_cnj[of B])
    apply (simp add: vec_cnj_def)
    apply (simp add: field_simps)
    done
  hence "Re (6*A + 4*Re B + 4*Im B) = 0"
    by simp
  hence "3*Re A + 2*Re B + 2*Im B = 0"
    using \<open>is_real A\<close>
    by simp

  hence "3/2 + Re B/Re A + Im B/Re A = 0"
    using \<open>Re A \<noteq> 0\<close>
    by (simp add: field_simps)

  hence "-Im B/Re A - 3/2 < -1"
    using \<open>Re B / Re A < -1\<close>
    by simp
  hence "Im B/Re A > -1/2"
    by (simp add: field_simps)
  thus "\<not> intersects_y_axis_positive_cmat H"
    using *
    by simp
qed

lemma negated_euclidean_axiom:
  shows "\<exists> a b c d t.
           a \<in> unit_disc \<and> b \<in> unit_disc \<and> c \<in> unit_disc \<and> d \<in> unit_disc \<and> t \<in> unit_disc \<and>
           poincare_between a d t \<and> poincare_between b d c \<and> a \<noteq> d \<and>
                (\<forall> x y. x \<in> unit_disc \<and> y \<in> unit_disc \<and>
                        poincare_between a b x \<and> poincare_between x t y \<longrightarrow> \<not> poincare_between a c y)"
proof-
  let ?a = "0\<^sub>h"
  let ?b = "of_complex (1/2)"
  let ?c = "of_complex (\<i>/2)"
  let ?dl = "(5 - sqrt 17) / 4"
  let ?d = "of_complex (?dl + \<i>*?dl)"
  let ?t = "of_complex (1/2 + \<i>/2)"

  have "?dl \<noteq> 0"
  proof-
    have "(sqrt 17)\<^sup>2 \<noteq> 5\<^sup>2"
      by simp
    hence "sqrt 17 \<noteq> 5"
      by force
    thus ?thesis
      by simp
  qed

  have "?d \<noteq> ?a"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "?dl + \<i>*?dl = 0"
      by simp
    hence "Re (?dl + \<i>*?dl) = 0"
      by simp
    thus False
      using \<open>?dl \<noteq> 0\<close>
      by simp
  qed

  have "?dl > 0"
  proof-
    have "(sqrt 17)\<^sup>2 < 5\<^sup>2"
      by (simp add: power2_eq_square)
    hence "sqrt 17 < 5"
      by (rule power2_less_imp_less, simp)
    thus ?thesis
      by simp
  qed

  have "?a \<noteq> ?b"
    by (metis divide_eq_0_iff of_complex_zero_iff zero_neq_numeral zero_neq_one)

  have "?a \<noteq> ?c"
    by (metis complex_i_not_zero divide_eq_0_iff of_complex_zero_iff zero_neq_numeral)

  show ?thesis
  proof (rule_tac x="?a" in exI, rule_tac x="?b" in exI, rule_tac x="?c" in exI, rule_tac x="?d" in exI, rule_tac x="?t" in exI, safe)


    show "?a \<in> unit_disc" "?b \<in> unit_disc" "?c \<in> unit_disc" "?t \<in> unit_disc"
      by (auto simp add: cmod_def power2_eq_square)

    have cmod_d: "cmod (?dl + \<i>*?dl) = ?dl * sqrt 2"
      using \<open>?dl > 0\<close>
      unfolding cmod_def
      by (simp add: real_sqrt_mult)

    show "?d \<in> unit_disc"
    proof-
      have "?dl < 1 / sqrt 2"
      proof-
        have "17\<^sup>2 < (5 * sqrt 17)\<^sup>2"
          by (simp add: field_simps)
        hence "17 < 5 * sqrt 17"
          by (rule power2_less_imp_less, simp)
        hence "?dl\<^sup>2 < (1 / sqrt 2)\<^sup>2"
          by (simp add: power2_eq_square field_simps)
        thus "?dl < 1 / sqrt 2"
          by (rule power2_less_imp_less, simp)
      qed
      thus ?thesis
        using cmod_d
        by (simp add: field_simps)
    qed

    have cmod_d: "1 - (cmod (to_complex ?d))\<^sup>2 = (-17 + 5*sqrt 17) / 4" (is "_ = ?cmod_d")
      apply (simp only: to_complex_of_complex)
      apply (subst cmod_d)
      apply (simp add: power_mult_distrib)
      apply (simp add: power2_eq_square field_simps)
      done

    have cmod_d_c: "(cmod (to_complex ?d - to_complex ?c))\<^sup>2 = (17 - 4*sqrt 17) / 4" (is "_ = ?cmod_dc")
      unfolding cmod_square
      by (simp add: field_simps)

    have cmod_c: "1 - (cmod (to_complex ?c))\<^sup>2 = 3/4" (is "_ = ?cmod_c")
      by (simp add: power2_eq_square)

    have xx: "\<And> x::real. x + x = 2*x"
      by simp

    have "cmod ((to_complex ?b) - (to_complex ?d)) = cmod ((to_complex ?d) - (to_complex ?c))"
      by (simp add: cmod_def power2_eq_square field_simps)
    moreover
    have "cmod (to_complex ?b) = cmod (to_complex ?c)"
      by simp
    ultimately
    have *: "poincare_distance_formula' (to_complex ?b) (to_complex ?d) =
             poincare_distance_formula' (to_complex ?d) (to_complex ?c)"
      unfolding poincare_distance_formula'_def
      by simp

    have **: "poincare_distance_formula' (to_complex ?d) (to_complex ?c) = (sqrt 17) / 3"
      unfolding poincare_distance_formula'_def
    proof (subst cmod_d, subst cmod_c, subst cmod_d_c)
      have "(sqrt 17 * 15)\<^sup>2 \<noteq> 51\<^sup>2"
        by simp
      hence "sqrt 17 * 15 \<noteq> 51"
        by force
      hence "sqrt 17 * 15 - 51 \<noteq> 0"
        by simp

      have "(5 * sqrt 17)\<^sup>2 \<noteq> 17\<^sup>2"
        by simp
      hence "5 * sqrt 17 \<noteq> 17"
        by force
      hence "?cmod_d * ?cmod_c \<noteq> 0"
        by simp
      hence "1 + 2 * (?cmod_dc / (?cmod_d * ?cmod_c)) =  (?cmod_d * ?cmod_c + 2 * ?cmod_dc) / (?cmod_d * ?cmod_c)"
        using add_frac_num[of "?cmod_d * ?cmod_c" "2 * ?cmod_dc" 1]
        by (simp add: field_simps)
      also have "... = (64 * (85 - sqrt 17 * 17)) / (64 * (sqrt 17 * 15 - 51))"
        by (simp add: field_simps)
      also have "... = (85 - sqrt 17 * 17) / (sqrt 17 * 15 - 51)"
        by (rule mult_divide_mult_cancel_left, simp)
      also have "... = sqrt 17 / 3"
        by (subst frac_eq_eq, fact, simp, simp add: field_simps)
      finally
      show "1 + 2 * (?cmod_dc / (?cmod_d * ?cmod_c)) = sqrt 17 / 3"
        .
    qed

    have "sqrt 17 \<ge> 3"
    proof-
      have "(sqrt 17)\<^sup>2 \<ge> 3\<^sup>2"
        by simp
      thus ?thesis
        by (rule power2_le_imp_le, simp)
    qed
    thus "poincare_between ?b ?d ?c"
      unfolding poincare_between_sum_distances[OF \<open>?b \<in> unit_disc\<close> \<open>?d \<in> unit_disc\<close> \<open>?c \<in> unit_disc\<close>]
      unfolding poincare_distance_formula[OF \<open>?b \<in> unit_disc\<close> \<open>?d \<in> unit_disc\<close>]
      unfolding poincare_distance_formula[OF \<open>?d \<in> unit_disc\<close> \<open>?c \<in> unit_disc\<close>]
      unfolding poincare_distance_formula[OF \<open>?b \<in> unit_disc\<close> \<open>?c \<in> unit_disc\<close>]
      unfolding poincare_distance_formula_def
      apply (subst *, subst xx, subst **, subst arcosh_double)
      apply (simp_all add: cmod_def power2_eq_square)
      done

    show "poincare_between ?a ?d ?t"
    proof (subst poincare_between_0uv[OF \<open>?d \<in> unit_disc\<close> \<open>?t \<in> unit_disc\<close> \<open>?d \<noteq> ?a\<close>])
      show "?t \<noteq> 0\<^sub>h"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence "1/2 + \<i>/2 = 0"
          by simp
        hence "Re (1/2 + \<i>/2) = 0"
          by simp
        thus False
          by simp
      qed
    next
      have "19\<^sup>2 \<le> (5 * sqrt 17)\<^sup>2"
        by simp
      hence "19 \<le> 5 * sqrt 17"
        by (rule power2_le_imp_le, simp)
      hence "cmod (to_complex ?d) \<le> cmod (to_complex ?t)"
        by (simp add: Let_def cmod_def power2_eq_square field_simps)
      moreover
      have "arg (to_complex ?d) = arg (to_complex ?t)"
      proof-
        have 1: "to_complex ?d = ((5 - sqrt 17) / 4) * (1 + \<i>)"
          by (simp add: field_simps)

        have 2: "to_complex ?t = (cor (1/2)) * (1 + \<i>)"
          by (simp add: field_simps)

        have "(sqrt 17)\<^sup>2 < 5\<^sup>2"
          by simp
        hence "sqrt 17 < 5"
          by (rule power2_less_imp_less, simp)
        hence 3: "(5 - sqrt 17) / 4 > 0"
          by simp

        have 4: "(1::real) / 2 > 0"
          by simp

        show ?thesis
          apply (subst 1, subst 2)
          apply (subst arg_mult_real_positive[OF 3])
          apply (subst arg_mult_real_positive[OF 4])
          by simp
      qed
      ultimately
      show "let d' = to_complex ?d; t' = to_complex ?t in arg d' = arg t' \<and> cmod d' \<le> cmod t'"
        by simp
    qed

    show "?a = ?d \<Longrightarrow> False"
      using \<open>?d \<noteq> ?a\<close>
      by simp

    fix x y
    assume "x \<in> unit_disc" "y \<in> unit_disc"

    assume abx: "poincare_between ?a ?b x"
    hence "x \<in> circline_set x_axis"
      using poincare_between_poincare_line_uvz[of ?a ?b x] \<open>x \<in> unit_disc\<close> \<open>?a \<noteq> ?b\<close>
      using poincare_line_0_real_is_x_axis[of ?b]
      by (auto simp add: circline_set_x_axis)

    have "x \<noteq> 0\<^sub>h"
      using abx poincare_between_sandwich[of ?a ?b] \<open>?a \<noteq> ?b\<close>
      by auto

    have "x \<in> positive_x_axis"
      using \<open>x \<in> circline_set x_axis\<close> \<open>x \<noteq> 0\<^sub>h\<close> \<open>x \<in> unit_disc\<close>
      using abx poincare_between_x_axis_0uv[of "1/2" "Re (to_complex x)"]
      unfolding circline_set_x_axis positive_x_axis_def
      by (auto simp add: cmod_eq_Re abs_less_iff complex_eq_if_Re_eq)

    assume acy: "poincare_between ?a ?c y"
    hence "y \<in> circline_set y_axis"
      using poincare_between_poincare_line_uvz[of ?a ?c y] \<open>y \<in> unit_disc\<close> \<open>?a \<noteq> ?c\<close>
      using poincare_line_0_imag_is_y_axis[of ?c]
      by (auto simp add: circline_set_y_axis)

    have "y \<noteq> 0\<^sub>h"
      using acy poincare_between_sandwich[of ?a ?c] \<open>?a \<noteq> ?c\<close>
      by auto

    have "y \<in> positive_y_axis"
    proof-
      have " \<And>x. \<lbrakk>x \<noteq> 0; poincare_between 0\<^sub>h (of_complex (\<i> / 2)) (of_complex x); is_imag x; - 1 < Im x\<rbrakk> \<Longrightarrow> 0 < Im x"
        by (smt add.left_neutral complex.expand divide_complex_def complex_eq divide_less_0_1_iff divide_less_eq_1_pos imaginary_unit.simps(1) mult.left_neutral of_real_1 of_real_add of_real_divide of_real_eq_0_iff one_add_one poincare_between_y_axis_0uv zero_complex.simps(1) zero_complex.simps(2) zero_less_divide_1_iff)
      thus ?thesis
        using \<open>y \<in> circline_set y_axis\<close> \<open>y \<noteq> 0\<^sub>h\<close> \<open>y \<in> unit_disc\<close>
        using acy
        unfolding circline_set_y_axis positive_y_axis_def
        by (auto simp add: cmod_eq_Im abs_less_iff)
    qed

    have "x \<noteq> y"
      using \<open>x \<in> positive_x_axis\<close> \<open>y \<in> positive_y_axis\<close>
      unfolding positive_x_axis_def positive_y_axis_def circline_set_x_axis circline_set_y_axis
      by auto

    assume xty: "poincare_between x ?t y"

    let ?xy = "poincare_line x y"

    have "?t \<in> circline_set ?xy"
      using xty poincare_between_poincare_line_uzv[OF \<open>x \<noteq> y\<close> \<open>x \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close> \<open>?t \<in> unit_disc\<close>]
      by simp

    moreover

    have "?xy \<noteq> x_axis"
      using poincare_line_circline_set[OF \<open>x \<noteq> y\<close>] \<open>y \<in> positive_y_axis\<close>
      by (auto simp add: circline_set_x_axis positive_y_axis_def)
    hence "intersects_x_axis_positive ?xy"
      using intersects_x_axis_positive_iff[of "?xy"] \<open>x \<noteq> y\<close> \<open>x \<in> unit_disc\<close> \<open>x \<in> positive_x_axis\<close>
      by auto

    moreover

    have "?xy \<noteq> y_axis"
      using poincare_line_circline_set[OF \<open>x \<noteq> y\<close>] \<open>x \<in> positive_x_axis\<close>
      by (auto simp add: circline_set_y_axis positive_x_axis_def)
    hence "intersects_y_axis_positive ?xy"
      using intersects_y_axis_positive_iff[of "?xy"] \<open>x \<noteq> y\<close> \<open>y \<in> unit_disc\<close> \<open>y \<in> positive_y_axis\<close>
      by auto

    ultimately

    show False
      using negated_euclidean_axiom_aux[of ?xy] \<open>x \<noteq> y\<close>
      unfolding circline_set_def
      by auto
  qed
qed

text \<open>Alternate form of the Euclidean axiom -- this one is much easier to prove\<close>
lemma negated_euclidean_axiom':
  shows "\<exists> a b c.
           a \<in> unit_disc \<and> b \<in> unit_disc \<and> c \<in> unit_disc \<and> \<not>(poincare_collinear {a, b, c})  \<and>
                \<not>(\<exists> x. x \<in> unit_disc \<and> 
                  poincare_distance a x = poincare_distance b x \<and>
                  poincare_distance a x = poincare_distance c x)"
proof-
  let ?a = "of_complex (\<i>/2)"
  let ?b = "of_complex (-\<i>/2)"
  let ?c = "of_complex (1/5)"

  have "(\<i>/2) \<noteq> (-\<i>/2)"
    by simp
  hence "?a \<noteq> ?b"
    by (metis to_complex_of_complex)
  have "(\<i>/2) \<noteq> (1/5)"
    by simp
  hence "?a \<noteq> ?c"
    by (metis to_complex_of_complex)
  have "(-\<i>/2) \<noteq> (1/5)"
    by (metis add.inverse_inverse cmod_divide div_by_1 divide_divide_eq_right inverse_eq_divide minus_divide_left mult.commute norm_ii norm_minus_cancel norm_numeral norm_one numeral_One numeral_eq_iff semiring_norm(88))
  hence "?b \<noteq> ?c"
    by (metis to_complex_of_complex)

  have "?a \<in> unit_disc" "?b \<in> unit_disc" "?c \<in> unit_disc"
    by auto

  moreover

  have "\<not>(poincare_collinear {?a, ?b, ?c})"
    unfolding poincare_collinear_def
  proof(rule ccontr)
    assume " \<not> (\<nexists>p. is_poincare_line p \<and> {?a, ?b, ?c} \<subseteq> circline_set p)"
    then obtain p where "is_poincare_line p \<and> {?a, ?b, ?c} \<subseteq> circline_set p"
      by auto
    let ?ab = "poincare_line ?a ?b"
    have "p = ?ab"
      using \<open>is_poincare_line p \<and> {?a, ?b, ?c} \<subseteq> circline_set p\<close>
      using unique_poincare_line[of ?a ?b] \<open>?a \<noteq> ?b\<close> \<open>?a \<in> unit_disc\<close> \<open>?b \<in> unit_disc\<close>
      by auto
    have "?c \<notin> circline_set ?ab"
    proof(rule ccontr)
      assume "\<not> ?c \<notin> circline_set ?ab"
      have "poincare_between ?a 0\<^sub>h ?b"
        unfolding poincare_between_def
        using cross_ratio_0inf by auto
      hence "0\<^sub>h \<in> circline_set ?ab"
        using \<open>?a \<noteq> ?b\<close> \<open>?a \<in> unit_disc\<close> \<open>?b \<in> unit_disc\<close>
        using poincare_between_poincare_line_uzv zero_in_unit_disc 
        by blast
      hence "?ab = poincare_line 0\<^sub>h ?a"
        using unique_poincare_line[of ?a ?b] \<open>?a \<noteq> ?b\<close> \<open>?a \<in> unit_disc\<close> \<open>?b \<in> unit_disc\<close>
        using \<open>is_poincare_line p \<and> {?a, ?b, ?c} \<subseteq> circline_set p\<close> 
        using \<open>p = ?ab\<close> poincare_line_circline_set(1) unique_poincare_line
        by (metis add.inverse_neutral divide_minus_left of_complex_zero_iff  zero_in_unit_disc)
      hence "(\<i>/2) * cnj(1/5) = cnj(\<i>/2) * (1/5)"
        using poincare_collinear_zero_iff[of "(\<i>/2)" "(1/5)"]
        using \<open>?a \<noteq> ?c\<close> \<open>\<not> ?c \<notin> circline_set ?ab\<close> \<open>?a \<in> unit_disc\<close> \<open>?c \<in> unit_disc\<close> \<open>p = ?ab\<close>
        using \<open>0\<^sub>h \<in> circline_set ?ab\<close> \<open>is_poincare_line p \<and> {?a, ?b, ?c} \<subseteq> circline_set p\<close> 
        using poincare_collinear_def by auto
      thus False
        by simp
    qed 
    thus False
      using \<open>p = ?ab\<close> \<open>is_poincare_line p \<and> {?a, ?b, ?c} \<subseteq> circline_set p\<close> 
      by auto
  qed

  moreover

  have "\<not>(\<exists> x. x \<in> unit_disc \<and> 
                  poincare_distance ?a x = poincare_distance ?b x \<and>
                  poincare_distance ?a x = poincare_distance ?c x)"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    then obtain x where "x \<in> unit_disc" "poincare_distance ?a x = poincare_distance ?b x"
                        "poincare_distance ?a x = poincare_distance ?c x"
      by blast
    let ?x = "to_complex x"
    have "poincare_distance_formula' (\<i>/2) ?x = poincare_distance_formula' (-\<i>/2) ?x"
      using \<open>poincare_distance ?a x = poincare_distance ?b x\<close>
      using \<open>x \<in> unit_disc\<close> \<open>?a \<in> unit_disc\<close> \<open>?b \<in> unit_disc\<close>
      by (metis cosh_dist to_complex_of_complex)
    hence "(cmod (\<i> / 2 - ?x))\<^sup>2 = (cmod (- \<i> / 2 - ?x))\<^sup>2"
      unfolding poincare_distance_formula'_def
      apply (simp add:field_simps)
      using \<open>x \<in> unit_disc\<close> unit_disc_cmod_square_lt_1 by fastforce
    hence "Im ?x = 0"
      unfolding cmod_def
      by (simp add: power2_eq_iff)

    have "1 - (Re ?x)\<^sup>2 \<noteq> 0"
      using \<open>x \<in> unit_disc\<close> unit_disc_cmod_square_lt_1
      using cmod_power2 by force
    hence "24 - 24 * (Re ?x)\<^sup>2 \<noteq> 0"
      by simp
    have "poincare_distance_formula' (\<i>/2) ?x = poincare_distance_formula' (1/5) ?x"
      using \<open>poincare_distance ?a x = poincare_distance ?c x\<close>
      using \<open>x \<in> unit_disc\<close> \<open>?a \<in> unit_disc\<close> \<open>?c \<in> unit_disc\<close>
      by (metis cosh_dist to_complex_of_complex)
    hence "(2 + 8 * (Re ?x)\<^sup>2) /(3 - 3 * (Re ?x)\<^sup>2) = 2 * (1 - Re ?x * 5)\<^sup>2 / (24 - 24 * (Re ?x)\<^sup>2)" (is "?lhs = ?rhs")
      unfolding poincare_distance_formula'_def
      apply (simp add:field_simps)
      unfolding cmod_def 
      using \<open>Im ?x = 0\<close> 
      by (simp add:field_simps)
    hence *: "?lhs * (24 - 24 * (Re ?x)\<^sup>2)  = ?rhs * (24 - 24 * (Re ?x)\<^sup>2) "
      using \<open>(24 - 24 * (Re ?x)\<^sup>2) \<noteq> 0\<close> 
      by simp
    have "?lhs * (24 - 24 * (Re ?x)\<^sup>2) = (2 + 8 * (Re ?x)\<^sup>2) * 8"
      using \<open>(24 - 24 * (Re ?x)\<^sup>2) \<noteq> 0\<close> \<open>1 - (Re ?x)\<^sup>2 \<noteq> 0\<close>
      by (simp add:field_simps)
    have "?rhs * (24 - 24 * (Re ?x)\<^sup>2) = 2 * (1 - Re ?x * 5)\<^sup>2"
      using \<open>(24 - 24 * (Re ?x)\<^sup>2) \<noteq> 0\<close> \<open>1 - (Re ?x)\<^sup>2 \<noteq> 0\<close>
      by (simp add:field_simps)
    hence "(2 + 8 * (Re ?x)\<^sup>2) * 8 = 2 * (1 - Re ?x * 5)\<^sup>2"
      using * \<open>?lhs * (24 - 24 * (Re ?x)\<^sup>2) = (2 + 8 * (Re ?x)\<^sup>2) * 8\<close>
      by simp      
    hence "7 * (Re ?x)\<^sup>2 + 10 * (Re ?x) + 7 = 0"
      by (simp add:field_simps comm_ring_1_class.power2_diff)
    thus False
      using discriminant_iff[of 7 "Re (to_complex x)" 10 7] discrim_def[of 7 10 7]
      by auto
  qed

  ultimately show ?thesis
    apply (rule_tac x="?a" in exI)
    apply (rule_tac x="?b" in exI)
    apply (rule_tac x="?c" in exI)
    by auto
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Continuity axiom\<close>
(* ------------------------------------------------------------------ *)

text \<open>The set $\phi$ is on the left of the set $\psi$\<close>
abbreviation set_order where
 "set_order A \<phi> \<psi> \<equiv> \<forall>x\<in> unit_disc. \<forall>y\<in> unit_disc.  \<phi> x \<and> \<psi> y \<longrightarrow> poincare_between A x y"
text \<open>The point $B$ is between the sets $\phi$ and $\psi$\<close>
abbreviation point_between_sets where
 "point_between_sets \<phi> B \<psi> \<equiv> \<forall>x\<in> unit_disc. \<forall>y\<in> unit_disc.  \<phi> x \<and> \<psi> y \<longrightarrow> poincare_between x B y"

lemma  continuity:
  assumes "\<exists> A \<in> unit_disc. set_order A \<phi> \<psi>"
  shows   "\<exists> B \<in> unit_disc. point_between_sets \<phi> B \<psi>"
proof (cases "(\<exists> x0 \<in> unit_disc. \<phi> x0) \<and> (\<exists> y0 \<in> unit_disc. \<psi> y0)")
  case False
  thus ?thesis
    using assms by blast
next
  case True
  then obtain Y0 where "\<psi> Y0" "Y0 \<in> unit_disc"
    by auto
  obtain A where *: "A \<in> unit_disc" "set_order A \<phi> \<psi>"
    using assms
    by auto
  show ?thesis
  proof(cases "\<forall> x \<in> unit_disc. \<phi> x \<longrightarrow> x = A")
    case True
    thus ?thesis
      using \<open>A \<in> unit_disc\<close>
      using poincare_between_nonstrict(1) by blast
  next
    case False
    then obtain X0 where "\<phi> X0" "X0 \<noteq> A" "X0 \<in> unit_disc"
      by auto
    have "Y0 \<noteq> A"
    proof(rule ccontr)
      assume "\<not> Y0 \<noteq> A"
      hence "\<forall> x \<in> unit_disc. \<phi> x \<longrightarrow> poincare_between A x A"
        using * \<open>\<psi> Y0\<close>
        by (cases A) force
      hence "\<forall> x \<in> unit_disc. \<phi> x \<longrightarrow> x = A"
        using * poincare_between_sandwich by blast
      thus False
        using False by auto
    qed

    show ?thesis
    proof (cases "\<exists> B \<in> unit_disc. \<phi> B \<and> \<psi> B")
      case True
      then obtain B where "B \<in> unit_disc" "\<phi> B" "\<psi> B"
        by auto
      hence "\<forall> x \<in> unit_disc. \<phi> x \<longrightarrow> poincare_between A x B"
        using * by auto
      have "\<forall> y \<in> unit_disc. \<psi> y \<longrightarrow> poincare_between A B y"
        using * \<open>B \<in> unit_disc\<close> \<open>\<phi> B\<close>
        by auto

      show ?thesis
      proof(rule+)
        show "B \<in> unit_disc"
          by fact
      next
        fix x y
        assume "x \<in> unit_disc" "y \<in> unit_disc" "\<phi> x \<and> \<psi> y"
        hence "poincare_between A x B" "poincare_between A B y"
          using \<open>\<forall> x \<in> unit_disc. \<phi> x \<longrightarrow> poincare_between A x B\<close>
          using \<open>\<forall> y \<in> unit_disc. \<psi> y \<longrightarrow> poincare_between A B y\<close>
          by simp+
        thus "poincare_between x B y"
          using \<open>x \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close> \<open>B \<in> unit_disc\<close> \<open>A \<in> unit_disc\<close>
          using poincare_between_transitivity[of A x B y]
          by simp
      qed
    next
      case False
      have "poincare_between A X0 Y0"
        using \<open>\<phi> X0\<close> \<open>\<psi> Y0\<close> * \<open>Y0 \<in> unit_disc\<close> \<open>X0 \<in> unit_disc\<close>
        by auto
      have "\<forall> \<phi>. \<forall> \<psi>. set_order A \<phi> \<psi> \<and> \<not> (\<exists> B \<in> unit_disc. \<phi> B \<and> \<psi> B) \<and> \<phi> X0 \<and> 
                      (\<exists> y \<in> unit_disc. \<psi> y) \<and> (\<exists> x \<in> unit_disc. \<phi> x)
                   \<longrightarrow> (\<exists> B \<in> unit_disc. point_between_sets \<phi> B \<psi>)"
            (is "?P A X0")
      proof (rule wlog_positive_x_axis[where P="?P"])
        show "A \<in> unit_disc"
          by fact
      next
        show "X0 \<in> unit_disc"
          by fact
      next
        show "A \<noteq> X0"
          using \<open>X0 \<noteq> A\<close> by simp
      next
        fix M u v
        let ?M = "\<lambda> x. moebius_pt M x"
        let ?Mu = "?M u" and ?Mv = "?M v"
        assume hip: "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
               "?P ?Mu ?Mv"
        show "?P u v"
        proof safe
          fix \<phi> \<psi> x y
          assume "set_order u \<phi> \<psi>" "\<not> (\<exists>B\<in>unit_disc. \<phi> B \<and> \<psi> B)" "\<phi> v"
                  "y \<in> unit_disc" "\<psi> y" "x \<in> unit_disc" "\<phi> x"

          let ?M\<phi> = "\<lambda> X'. \<exists> X. \<phi> X \<and> ?M X = X'" 
          let ?M\<psi> = "\<lambda> X'. \<exists> X. \<psi> X \<and> ?M X = X'"

          obtain M\<phi> where "M\<phi> = ?M\<phi>" by simp
          obtain M\<psi> where "M\<psi> = ?M\<psi>" by simp

          have "M\<phi> ?Mv"
            using \<open>\<phi> v\<close> using \<open>M\<phi> = ?M\<phi>\<close> 
            by blast
          moreover
          have "\<not> (\<exists> B \<in>unit_disc. M\<phi> B \<and> M\<psi> B)"
            using \<open>\<not> (\<exists>B\<in>unit_disc. \<phi> B \<and> \<psi> B)\<close>
            using \<open>M\<phi> = ?M\<phi>\<close> \<open>M\<psi> = ?M\<psi>\<close>
            by (metis hip(1) moebius_pt_invert unit_disc_fix_discI unit_disc_fix_moebius_inv)
          moreover
          have "\<exists> y \<in> unit_disc. M\<psi> y"
            using \<open>y \<in> unit_disc\<close> \<open>\<psi> y\<close>  \<open>M\<psi> = ?M\<psi>\<close> \<open>unit_disc_fix M\<close>
            by auto
          moreover
          have "set_order ?Mu ?M\<phi> ?M\<psi>"
          proof ((rule ballI)+, rule impI)                                       
            fix Mx My
            assume "Mx \<in> unit_disc" "My \<in> unit_disc" "?M\<phi> Mx \<and> ?M\<psi> My"
            then obtain x y where "\<phi> x \<and> ?M x = Mx" "\<psi> y \<and> ?M y = My"
              by blast

            hence "x \<in> unit_disc" "y \<in> unit_disc"
              using \<open>Mx \<in> unit_disc\<close> \<open>My \<in> unit_disc\<close> \<open>unit_disc_fix M\<close>
              by (metis moebius_pt_comp_inv_left unit_disc_fix_discI unit_disc_fix_moebius_inv)+

            hence "poincare_between u x y"
              using \<open>set_order u \<phi> \<psi>\<close>
              using \<open>Mx \<in> unit_disc\<close> \<open>My \<in> unit_disc\<close> \<open>\<phi> x \<and> ?M x = Mx\<close> \<open>\<psi> y \<and> ?M y = My\<close>
              by blast
            then show "poincare_between ?Mu Mx My"
              using \<open>\<phi> x \<and> ?M x = Mx\<close> \<open>\<psi> y \<and> ?M y = My\<close>
              using \<open>x \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close> \<open>u \<in> unit_disc\<close> \<open>unit_disc_fix M\<close> 
              using unit_disc_fix_moebius_preserve_poincare_between by blast
          qed

          hence  "set_order ?Mu M\<phi> M\<psi>"
            using \<open>M\<phi> = ?M\<phi>\<close> \<open>M\<psi> = ?M\<psi>\<close>
            by simp
          ultimately
          have "\<exists> Mb \<in> unit_disc. point_between_sets M\<phi> Mb M\<psi>"
            using hip(5)
            by blast
          then obtain Mb where bbb: 
            "Mb \<in> unit_disc" "point_between_sets ?M\<phi> Mb ?M\<psi>"
            using \<open>M\<phi> = ?M\<phi>\<close> \<open>M\<psi> = ?M\<psi>\<close>
            by auto

          let ?b = "moebius_pt (moebius_inv M) Mb"
          show "\<exists> b \<in> unit_disc. point_between_sets \<phi> b \<psi>"
          proof (rule_tac x="?b" in bexI, (rule ballI)+, rule impI)
            fix x y
            assume "x \<in> unit_disc" "y \<in> unit_disc" "\<phi> x \<and> \<psi> y"
            hence "poincare_between u x y"
              using \<open>set_order u \<phi> \<psi>\<close>
              by blast
            
            let ?Mx = "?M x" and ?My = "?M y"

            have "?M\<phi> ?Mx" "?M\<psi> ?My"
              using \<open>\<phi> x \<and> \<psi> y\<close>
              by blast+
            have "?Mx \<in> unit_disc" "?My \<in> unit_disc"
              using \<open>x \<in> unit_disc\<close> \<open>unit_disc_fix M\<close> \<open>y \<in> unit_disc\<close>
              by auto

            hence "poincare_between ?Mx Mb ?My"
              using \<open>?M\<phi> ?Mx\<close> \<open>?M\<psi> ?My\<close> \<open>?Mx \<in> unit_disc\<close> \<open>?My \<in> unit_disc\<close> bbb
              by auto

            then show "poincare_between x ?b y"
              using \<open>unit_disc_fix M\<close> 
              using \<open>x \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close> \<open>Mb \<in> unit_disc\<close> \<open>?Mx \<in> unit_disc\<close> \<open>?My \<in> unit_disc\<close>
              using unit_disc_fix_moebius_preserve_poincare_between[of M x ?b y]
              by auto
          next
            show "?b \<in> unit_disc"
              using bbb \<open>unit_disc_fix M\<close>
              by auto
          qed
        qed
      next
        fix X
        assume xx: "is_real X" "0 < Re X" "Re X < 1"
        let ?X = "of_complex X"
        show "?P 0\<^sub>h ?X"
        proof ((rule allI)+, rule impI, (erule conjE)+)
          fix \<phi> \<psi>
          assume "set_order 0\<^sub>h \<phi> \<psi>" "\<not> (\<exists>B\<in>unit_disc. \<phi> B \<and> \<psi> B)" "\<phi> ?X" 
                 "\<exists>y\<in>unit_disc. \<psi> y" "\<exists>x\<in>unit_disc. \<phi> x"
          have "?X \<in> unit_disc"
            using xx
            by (simp add: cmod_eq_Re)

          have \<psi>pos: "\<forall> y \<in> unit_disc. \<psi> y \<longrightarrow> (is_real (to_complex y) \<and> Re (to_complex y) > 0)"
          proof(rule ballI, rule impI)
            fix y
            let ?y = "to_complex y"
            assume "y \<in> unit_disc" "\<psi> y"

            hence "poincare_between 0\<^sub>h ?X y"
              using \<open>set_order 0\<^sub>h \<phi> \<psi>\<close>
              using \<open>?X \<in> unit_disc\<close> \<open>\<phi> ?X\<close>
              by auto

            thus "is_real ?y \<and> 0 < Re ?y"
              using xx \<open>?X \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close>
              by (metis (mono_tags, hide_lams) arg_0_iff of_complex_zero_iff poincare_between_0uv poincare_between_sandwich to_complex_of_complex unit_disc_to_complex_inj zero_in_unit_disc)
          qed

          have \<phi>noneg: "\<forall> x \<in> unit_disc. \<phi> x \<longrightarrow> (is_real (to_complex x) \<and> Re (to_complex x) \<ge> 0)"
          proof(rule ballI, rule impI)
            fix x
            assume "x \<in> unit_disc" "\<phi> x"

            obtain y where "y \<in> unit_disc" "\<psi> y"
              using \<open>\<exists> y \<in> unit_disc. \<psi> y\<close> by blast

            let ?x = "to_complex x" and ?y = "to_complex y"

            have "is_real ?y" "Re ?y > 0"
              using \<psi>pos \<open>\<psi> y\<close> \<open>y \<in> unit_disc\<close>
              by auto

            have "poincare_between 0\<^sub>h x y"
              using \<open>set_order 0\<^sub>h \<phi> \<psi>\<close>
              using \<open>x \<in> unit_disc\<close> \<open>\<phi> x\<close> \<open>y\<in>unit_disc\<close> \<open>\<psi> y\<close>
              by auto

            thus "is_real ?x \<and> 0 \<le> Re ?x"
              using \<open>x \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close> \<open>is_real (to_complex y)\<close> \<open>\<psi> y\<close>
              using \<open>set_order 0\<^sub>h \<phi> \<psi>\<close>
              using \<open>\<phi> ?X\<close> \<open>?X \<in> unit_disc\<close> \<open>Re ?y > 0\<close>
              by (metis arg_0_iff le_less of_complex_zero poincare_between_0uv to_complex_of_complex zero_complex.simps(1) zero_complex.simps(2))
          qed

          have \<phi>less\<psi>: "\<forall>x\<in>unit_disc. \<forall>y\<in>unit_disc. \<phi> x \<and> \<psi> y \<longrightarrow> Re (to_complex x) < Re (to_complex y)"
          proof((rule ballI)+, rule impI)
            fix x y
            let ?x = "to_complex x" and ?y = "to_complex y"
            assume "x \<in> unit_disc" "y \<in> unit_disc" "\<phi> x \<and> \<psi> y"

            hence "poincare_between 0\<^sub>h x y"
              using \<open>set_order 0\<^sub>h \<phi> \<psi>\<close>
              by auto
            moreover
            have "is_real ?x" "Re ?x \<ge> 0"
              using \<phi>noneg
              using \<open>x \<in> unit_disc\<close> \<open>\<phi> x \<and> \<psi> y\<close> by auto
            moreover
            have "is_real ?y" "Re ?y > 0"
              using \<psi>pos
              using \<open>y \<in> unit_disc\<close> \<open>\<phi> x \<and> \<psi> y\<close> by auto
            ultimately
            have "Re ?x \<le> Re ?y"
              using \<open>x \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close>
              by (metis Re_complex_of_real arg_0_iff le_less of_complex_zero poincare_between_0uv rcis_cmod_arg rcis_zero_arg to_complex_of_complex)

            have "Re ?x \<noteq> Re ?y"
              using \<open>\<phi> x \<and> \<psi> y\<close> \<open>is_real ?x\<close> \<open>is_real ?y\<close>
              using \<open>\<not> (\<exists>B\<in>unit_disc. \<phi> B \<and> \<psi> B)\<close> \<open>x \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close>
              by (metis complex.expand unit_disc_to_complex_inj)

            thus "Re ?x < Re ?y"
              using \<open>Re ?x \<le> Re ?y\<close> by auto
          qed

          have "\<exists> b \<in> unit_disc. \<forall> x \<in> unit_disc. \<forall> y \<in> unit_disc. 
                    is_real (to_complex b) \<and> 
                    (\<phi> x \<and> \<psi> y \<longrightarrow> (Re (to_complex x) \<le> Re (to_complex b) \<and> Re (to_complex b) \<le> Re (to_complex y)))"
          proof-
            let ?Phi = "{x. (of_complex (cor x)) \<in> unit_disc \<and> \<phi> (of_complex (cor x))}"

            have "\<forall> x \<in> unit_disc. \<phi> x \<longrightarrow> Re (to_complex x) \<le> Sup ?Phi"
            proof(safe)
              fix x
              let ?x = "to_complex x"
              assume "x \<in> unit_disc" "\<phi> x"
              hence "is_real ?x" "Re ?x \<ge> 0"
                using \<phi>noneg
                by auto
              hence "cor (Re ?x) = ?x"
                 using complex_of_real_Re by blast
              hence "of_complex (cor (Re ?x)) \<in> unit_disc"
                using \<open>x \<in> unit_disc\<close> 
                by (metis inf_notin_unit_disc of_complex_to_complex)
              moreover
              have "\<phi> (of_complex (cor (Re ?x)))"
                using \<open>cor (Re ?x) = ?x\<close> \<open>\<phi> x\<close> \<open>x \<in> unit_disc\<close>
                by (metis inf_notin_unit_disc of_complex_to_complex)
              ultimately
              have "Re ?x \<in> ?Phi"
                by auto

              have "\<exists>M. \<forall>x \<in> ?Phi. x \<le> M"
                using \<phi>less\<psi>
                using \<open>\<exists> y \<in> unit_disc. \<psi> y\<close>
                by (metis (mono_tags, lifting) Re_complex_of_real le_less mem_Collect_eq to_complex_of_complex)

              thus "Re ?x \<le> Sup ?Phi"
                using cSup_upper[of "Re ?x" ?Phi]
                unfolding bdd_above_def
                using \<open>Re ?x \<in> ?Phi\<close>
                by auto                
            qed

            have "\<forall> y \<in> unit_disc. \<psi> y \<longrightarrow> Sup ?Phi \<le> Re (to_complex y)"
            proof (safe)
              fix y
              let ?y = "to_complex y"
              assume "\<psi> y" "y \<in> unit_disc"
              show "Sup ?Phi \<le> Re ?y"
              proof (rule ccontr)
                assume "\<not> ?thesis"
                hence "Re ?y < Sup ?Phi"
                  by auto

                have "\<exists> x. \<phi> (of_complex (cor x)) \<and> (of_complex (cor x)) \<in> unit_disc"
                proof -
                  obtain x' where "x' \<in> unit_disc" "\<phi> x'"
                    using \<open>\<exists> x \<in> unit_disc. \<phi> x\<close> by blast
                  let ?x' = "to_complex x'"
                  have "is_real ?x'"
                    using \<open>x' \<in> unit_disc\<close> \<open>\<phi> x'\<close>
                    using \<phi>noneg
                    by auto
                  hence "cor (Re ?x') = ?x'"
                    using complex_of_real_Re by blast
                  hence "x' = of_complex (cor (Re ?x'))"
                    using \<open>x' \<in> unit_disc\<close>
                    by (metis inf_notin_unit_disc of_complex_to_complex)
                  show ?thesis
                    apply (rule_tac x="Re ?x'" in exI)
                    using \<open>x' \<in> unit_disc\<close> 
                    apply (subst (asm) \<open>x' = of_complex (cor (Re ?x'))\<close>, simp)
                    using \<open>\<phi> x'\<close>
                    by (subst (asm) (2) \<open>x' = of_complex (cor (Re ?x'))\<close>, simp)               
                qed

                hence "?Phi \<noteq> {}"
                  by auto

                then obtain x where "\<phi> (of_complex (cor x))" "Re ?y < x"
                                    "(of_complex (cor x)) \<in> unit_disc"
                  using \<open>Re ?y < Sup ?Phi\<close>
                  using less_cSupE[of "Re ?y" ?Phi]
                  by auto
                moreover
                have "Re ?y < Re (to_complex (of_complex (cor x)))"
                  using \<open>Re ?y < x\<close> 
                  by simp
                ultimately
                show False
                  using \<phi>less\<psi>
                  using \<open>\<psi> y\<close> \<open>y \<in> unit_disc\<close>
                  by (metis less_not_sym)
              qed
            qed

            thus ?thesis
              using \<open>\<forall> x \<in> unit_disc. \<phi> x \<longrightarrow> Re (to_complex x) \<le> Sup ?Phi\<close>
              apply (rule_tac x="(of_complex (cor (Sup ?Phi)))" in bexI, simp)
              using \<open>\<exists>y\<in>unit_disc. \<psi> y\<close> \<open>\<phi> ?X\<close> \<open>?X \<in> unit_disc\<close>
              using \<open>\<forall>y\<in>unit_disc. \<psi> y \<longrightarrow> is_real (to_complex y) \<and> 0 < Re (to_complex y)\<close>
              by (smt complex_of_real_Re inf_notin_unit_disc norm_of_real of_complex_to_complex to_complex_of_complex unit_disc_iff_cmod_lt_1 xx(2))
          qed

          then obtain B where "B \<in> unit_disc" "is_real (to_complex B)"
            "\<forall>x\<in>unit_disc. \<forall>y\<in>unit_disc. \<phi> x \<and> \<psi> y \<longrightarrow> Re (to_complex x) \<le> Re (to_complex B) \<and>
             Re (to_complex B) \<le> Re (to_complex y)"
            by blast

          show "\<exists> b \<in> unit_disc. point_between_sets \<phi> b \<psi>"
          proof (rule_tac x="B" in bexI)
            show "B \<in> unit_disc"
              by fact
          next
            show "point_between_sets \<phi> B \<psi>"
            proof ((rule ballI)+, rule impI)
              fix x y 
              let ?x = "to_complex x" and ?y = "to_complex y" and ?B = "to_complex B"
              assume "x \<in> unit_disc" "y \<in> unit_disc" "\<phi> x \<and> \<psi> y"

              hence "Re ?x \<le> Re ?B \<and> Re ?B \<le> Re ?y"
                using \<open>\<forall>x\<in>unit_disc. \<forall>y\<in>unit_disc. \<phi> x \<and> \<psi> y \<longrightarrow> Re (to_complex x) \<le> Re ?B \<and>
                       Re (to_complex B) \<le> Re (to_complex y)\<close>
                by auto
              moreover
              have "is_real ?x" "Re ?x \<ge> 0"
                using \<phi>noneg
                using \<open>x \<in> unit_disc\<close> \<open>\<phi> x \<and> \<psi> y\<close>
                by auto
              moreover
              have "is_real ?y" "Re ?y > 0"
                using \<psi>pos
                using \<open>y \<in> unit_disc\<close> \<open>\<phi> x \<and> \<psi> y\<close>
                by auto
              moreover
              have "cor (Re ?x) = ?x"
                using complex_of_real_Re \<open>is_real ?x\<close> by blast
              hence "x = of_complex (cor (Re ?x))"
                using \<open>x \<in> unit_disc\<close>
                by (metis inf_notin_unit_disc of_complex_to_complex)
              moreover
              have "cor (Re ?y) = ?y"
                using complex_of_real_Re \<open>is_real ?y\<close> by blast
              hence "y = of_complex (cor (Re ?y))"
                using \<open>y \<in> unit_disc\<close>
                by (metis inf_notin_unit_disc of_complex_to_complex)
              moreover
              have "cor (Re ?B) = ?B"
                using complex_of_real_Re \<open>is_real (to_complex  B)\<close> by blast
              hence "B = of_complex (cor (Re ?B))"
                using \<open>B \<in> unit_disc\<close>
                by (metis inf_notin_unit_disc of_complex_to_complex)
              ultimately
              show "poincare_between x B y"
                using \<open>is_real (to_complex B)\<close> \<open>x \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close> \<open>B \<in> unit_disc\<close>
                using poincare_between_x_axis_uvw[of "Re (to_complex x)" "Re (to_complex B)" "Re (to_complex y)"]
                by (smt Re_complex_of_real arg_0_iff poincare_between_nonstrict(1) rcis_cmod_arg rcis_zero_arg unit_disc_iff_cmod_lt_1)
            qed
          qed            
        qed
      qed 
      thus ?thesis
        using False \<open>\<phi> X0\<close> \<open>\<psi> Y0\<close> * \<open>Y0 \<in> unit_disc\<close> \<open>X0 \<in> unit_disc\<close>
        by auto
    qed      
  qed
qed


(* ------------------------------------------------------------------ *)
subsection\<open>Limiting parallels axiom\<close>
(* ------------------------------------------------------------------ *)

text \<open>Auxiliary definitions\<close>

definition poincare_on_line where
  "poincare_on_line p a b \<longleftrightarrow> poincare_collinear {p, a, b}"

definition poincare_on_ray where 
  "poincare_on_ray p a b \<longleftrightarrow> poincare_between a p b \<or> poincare_between a b p"

definition poincare_in_angle where
  "poincare_in_angle p a b c \<longleftrightarrow>
      b \<noteq> a \<and> b \<noteq> c \<and> p \<noteq> b \<and> (\<exists> x \<in> unit_disc. poincare_between a x c \<and> x \<noteq> a \<and> x \<noteq> c \<and> poincare_on_ray p b x)"

definition poincare_ray_meets_line where
  "poincare_ray_meets_line a b c d \<longleftrightarrow> (\<exists> x \<in> unit_disc. poincare_on_ray x a b \<and> poincare_on_line x c d)"

text \<open>All points on ray are collinear\<close>
lemma poincare_on_ray_poincare_collinear:
  assumes "p \<in> unit_disc" and "a \<in> unit_disc" and "b \<in> unit_disc" and "poincare_on_ray p a b"
  shows "poincare_collinear {p, a, b}"
  using assms poincare_between_poincare_collinear
  unfolding poincare_on_ray_def
  by (metis insert_commute)

text \<open>H-isometries preserve all defined auxiliary relations\<close>

lemma unit_disc_fix_preserves_poincare_on_line [simp]:
  assumes "unit_disc_fix M" and "p \<in> unit_disc" "a \<in> unit_disc" "b \<in> unit_disc"
  shows "poincare_on_line (moebius_pt M p) (moebius_pt M a) (moebius_pt M b) \<longleftrightarrow> poincare_on_line p a b"
  using assms
  unfolding poincare_on_line_def
  by auto

lemma unit_disc_fix_preserves_poincare_on_ray [simp]:
  assumes "unit_disc_fix M" "p \<in> unit_disc" "a \<in> unit_disc" "b \<in> unit_disc"
  shows "poincare_on_ray (moebius_pt M p) (moebius_pt M a) (moebius_pt M b) \<longleftrightarrow> poincare_on_ray p a b"
  using assms
  unfolding poincare_on_ray_def
  by auto

lemma unit_disc_fix_preserves_poincare_in_angle [simp]:
  assumes "unit_disc_fix M" "p \<in> unit_disc" "a \<in> unit_disc" "b \<in> unit_disc" "c \<in> unit_disc"
  shows "poincare_in_angle (moebius_pt M p) (moebius_pt M a) (moebius_pt M b) (moebius_pt M c) \<longleftrightarrow> poincare_in_angle p a b c" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  then obtain Mx where *: "Mx \<in> unit_disc"
      "poincare_between (moebius_pt M a) Mx (moebius_pt M c)"
      "Mx \<noteq> moebius_pt M a" "Mx \<noteq> moebius_pt M c"  "poincare_on_ray (moebius_pt M p) (moebius_pt M b) Mx"
      "moebius_pt M b \<noteq> moebius_pt M a" "moebius_pt M b \<noteq> moebius_pt M c" "moebius_pt M p \<noteq> moebius_pt M b"
    unfolding poincare_in_angle_def
    by auto
  obtain x where "Mx = moebius_pt M x" "x \<in> unit_disc"
    by (metis "*"(1) assms(1) image_iff unit_disc_fix_iff)
  thus ?rhs
    using * assms
    unfolding poincare_in_angle_def
    by auto
next
  assume ?rhs
  then obtain x where *: "x \<in> unit_disc"
      "poincare_between a x c"
      "x \<noteq> a" "x \<noteq> c"  "poincare_on_ray p b x"
      "b \<noteq> a" "b \<noteq> c" "p \<noteq> b"
    unfolding poincare_in_angle_def
    by auto
  thus ?lhs
    using assms
    unfolding poincare_in_angle_def
    by auto (rule_tac x="moebius_pt M x" in bexI, auto)
qed

lemma unit_disc_fix_preserves_poincare_ray_meets_line [simp]:
  assumes "unit_disc_fix M" "a \<in> unit_disc" "b \<in> unit_disc" "c \<in> unit_disc" "d \<in> unit_disc"
  shows "poincare_ray_meets_line (moebius_pt M a) (moebius_pt M b) (moebius_pt M c) (moebius_pt M d) \<longleftrightarrow> poincare_ray_meets_line a b c d" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain Mx where *: "Mx \<in> unit_disc" "poincare_on_ray Mx (moebius_pt M a) (moebius_pt M b)" 
    "poincare_on_line Mx (moebius_pt M c) (moebius_pt M d)"
    unfolding poincare_ray_meets_line_def
    by auto
  obtain x where "Mx = moebius_pt M x" "x \<in> unit_disc"
    by (metis "*"(1) assms(1) image_iff unit_disc_fix_iff)
  thus ?rhs
    using assms *
    unfolding poincare_ray_meets_line_def poincare_on_line_def
    by auto
next
  assume ?rhs
  then obtain x where *: "x \<in> unit_disc" "poincare_on_ray x a b" 
    "poincare_on_line x c d"
    unfolding poincare_ray_meets_line_def
    by auto
  thus ?lhs
    using assms *
    unfolding poincare_ray_meets_line_def poincare_on_line_def
    by auto (rule_tac x="moebius_pt M x" in bexI, auto)
qed

text \<open>H-lines that intersect on the absolute do not meet (they do not share a common h-point)\<close>
lemma tangent_not_meet:
  assumes "x1 \<in> unit_disc" and "x2 \<in> unit_disc" and "x1 \<noteq> x2" and "\<not> poincare_collinear {0\<^sub>h, x1, x2}"
  assumes "i \<in> ideal_points (poincare_line x1 x2)" "a \<in> unit_disc" "a \<noteq> 0\<^sub>h" "poincare_collinear {0\<^sub>h, a, i}"
  shows "\<not> poincare_ray_meets_line 0\<^sub>h a x1 x2"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain x where "x \<in> unit_disc" "poincare_on_ray x 0\<^sub>h a" "poincare_collinear {x, x1, x2}"
    unfolding poincare_ray_meets_line_def poincare_on_line_def
    by auto

  have "poincare_collinear {0\<^sub>h, a, x}"
    using `poincare_on_ray x 0\<^sub>h a` `x \<in> unit_disc` `a \<in> unit_disc`
    by (meson poincare_between_poincare_collinear poincare_between_rev poincare_on_ray_def poincare_on_ray_poincare_collinear zero_in_unit_disc)

  have "x \<noteq> 0\<^sub>h"
    using `\<not> poincare_collinear {0\<^sub>h, x1, x2}` `poincare_collinear {x, x1, x2}`
    unfolding poincare_collinear_def
    by (auto simp add: assms(2) assms(3) poincare_between_rev)

  let ?l1 = "poincare_line 0\<^sub>h a"
  let ?l2 = "poincare_line x1 x2"

  have "i \<in> circline_set unit_circle"
    using `i \<in> ideal_points (poincare_line x1 x2)`
    using assms(3) ideal_points_on_unit_circle is_poincare_line_poincare_line by blast

  have "i \<in> circline_set ?l1"
    using `poincare_collinear {0\<^sub>h, a, i}`
    unfolding poincare_collinear_def
    using \<open>a \<in> unit_disc\<close> \<open>a \<noteq> 0\<^sub>h\<close>
    by (metis insert_subset unique_poincare_line zero_in_unit_disc)

  moreover

  have "x \<in> circline_set ?l1"
    using `a \<in> unit_disc` `a \<noteq> 0\<^sub>h` `poincare_collinear {0\<^sub>h, a, x}` `x \<in> unit_disc`
    by (metis poincare_collinear3_between poincare_between_poincare_line_uvz poincare_between_poincare_line_uzv poincare_line_sym zero_in_unit_disc)

  moreover

  have "inversion x \<in> circline_set ?l1"
    using `poincare_collinear {0\<^sub>h, a, x}`
    using poincare_line_inversion_full[of "0\<^sub>h" a x] `a \<in> unit_disc` `a \<noteq> 0\<^sub>h` `x \<in> unit_disc`
    by (metis poincare_collinear3_between is_poincare_line_inverse_point is_poincare_line_poincare_line poincare_between_poincare_line_uvz poincare_between_poincare_line_uzv poincare_line_sym zero_in_unit_disc)

  moreover

  have "x \<in> circline_set ?l2"
    using `poincare_collinear {x, x1, x2}` `x1 \<noteq> x2` `x1 \<in> unit_disc` `x2 \<in> unit_disc` `x \<in> unit_disc`
    by (metis insert_commute inversion_noteq_unit_disc poincare_between_poincare_line_uvz poincare_between_poincare_line_uzv poincare_collinear3_iff poincare_line_sym_general)

  moreover

  hence "inversion x \<in> circline_set ?l2"
    using  `x1 \<noteq> x2` `x1 \<in> unit_disc` `x2 \<in> unit_disc` `x \<in> unit_disc`
    using poincare_line_inversion_full[of x1 x2 x]
    unfolding circline_set_def
    by auto

  moreover

  have "i \<in> circline_set ?l2"
    using `x1 \<noteq> x2` `x1 \<in> unit_disc` `x2 \<in> unit_disc`
    using `i \<in> ideal_points ?l2`
    by (simp add: ideal_points_on_circline)

  moreover

  have "x \<noteq> inversion x"
    using `x \<in> unit_disc`
    using inversion_noteq_unit_disc by fastforce

  moreover

  have "x \<noteq> i"
    using `x \<in> unit_disc`
    using \<open>i \<in> circline_set unit_circle\<close> circline_set_def inversion_noteq_unit_disc 
    by fastforce+

  moreover

  have "inversion x \<noteq> i"
    using \<open>i \<in> circline_set unit_circle\<close> \<open>x \<noteq> i\<close> circline_set_def inversion_unit_circle 
    by fastforce

  ultimately
          
  have "?l1 = ?l2"
    using unique_circline_set[of x "inversion x" i]
    by blast

  hence "0\<^sub>h \<in> circline_set ?l2"
    by (metis \<open>a \<noteq> 0\<^sub>h\<close> poincare_line_circline_set(1))

  thus False
    using `\<not> poincare_collinear {0\<^sub>h, x1, x2}`
    unfolding poincare_collinear_def
    using \<open>poincare_collinear {x, x1, x2}\<close> \<open>x1 \<noteq> x2\<close> `x1 \<in> unit_disc` `x2 \<in> unit_disc` poincare_collinear_def unique_poincare_line
    by auto
qed 

lemma limiting_parallels:
  assumes "a \<in> unit_disc" and "x1 \<in> unit_disc" and "x2 \<in> unit_disc" and "\<not> poincare_on_line a x1 x2"
  shows "\<exists>a1\<in>unit_disc. \<exists>a2\<in>unit_disc.
          \<not> poincare_on_line a a1 a2 \<and>
          \<not> poincare_ray_meets_line a a1 x1 x2 \<and> \<not> poincare_ray_meets_line a a2 x1 x2 \<and>
          (\<forall>a'\<in>unit_disc. poincare_in_angle a' a1 a a2 \<longrightarrow> poincare_ray_meets_line a a' x1 x2)" (is "?P a x1 x2")
proof-
  have "\<not> poincare_collinear {a, x1, x2}"
    using `\<not> poincare_on_line a x1 x2`
    unfolding poincare_on_line_def
    by simp

  have "\<forall> x1 x2. x1 \<in> unit_disc \<and> x2 \<in> unit_disc \<and> \<not> poincare_collinear {a, x1, x2} \<longrightarrow> ?P a x1 x2" (is "?Q a")
  proof (rule wlog_zero[OF `a \<in> unit_disc`])
    fix a u
    assume *: "u \<in> unit_disc" "cmod a < 1"
    hence uf: "unit_disc_fix (blaschke a)"
      by simp
    assume **: "?Q (moebius_pt (blaschke a) u)"
    show "?Q u"
    proof safe
      fix x1 x2
      let ?M = "moebius_pt (blaschke a)"
      assume xx: "x1 \<in> unit_disc" "x2 \<in> unit_disc" "\<not> poincare_collinear {u, x1, x2}"
      hence MM: "?M x1 \<in> unit_disc \<and> ?M x2\<in> unit_disc \<and> \<not> poincare_collinear {?M u, ?M x1, ?M x2}"   
        using *
        by auto
      show "?P u x1 x2" (is "\<exists>a1\<in>unit_disc. \<exists>a2\<in>unit_disc. ?P' a1 a2 u x1 x2")
      proof-
        obtain Ma1 Ma2 where MM: "Ma1 \<in> unit_disc" "Ma2 \<in> unit_disc" "?P' Ma1 Ma2 (?M u) (?M x1) (?M x2)"   
          using **[rule_format, OF MM]
          by blast
        hence MM': "\<forall>a'\<in>unit_disc. poincare_in_angle a' Ma1 (?M u) Ma2 \<longrightarrow> poincare_ray_meets_line (?M u) a' (?M x1) (?M x2)"
          by auto
        obtain a1 a2 where a: "a1 \<in> unit_disc" "a2 \<in> unit_disc" "?M a1 = Ma1" "?M a2 = Ma2"
          using uf
          by (metis \<open>Ma1 \<in> unit_disc\<close> \<open>Ma2 \<in> unit_disc\<close> image_iff unit_disc_fix_iff)

        have "\<forall>a'\<in>unit_disc. poincare_in_angle a' a1 u a2 \<longrightarrow> poincare_ray_meets_line u a' x1 x2"
        proof safe
          fix a'
          assume "a' \<in> unit_disc" "poincare_in_angle a' a1 u a2"
          thus "poincare_ray_meets_line u a' x1 x2"
            using MM(1-2) MM'[rule_format, of "?M a'"] * uf a xx
            by (meson unit_disc_fix_discI unit_disc_fix_preserves_poincare_in_angle unit_disc_fix_preserves_poincare_ray_meets_line)
        qed

        hence "?P' a1 a2 u x1 x2"
          using MM * uf xx a
          by auto
          
        thus ?thesis
          using `a1 \<in> unit_disc` `a2 \<in> unit_disc`
          by blast
      qed
    qed
  next
    show "?Q 0\<^sub>h"
    proof safe
      fix x1 x2
      assume "x1 \<in> unit_disc" "x2 \<in> unit_disc"
      assume "\<not> poincare_collinear {0\<^sub>h, x1, x2}"
      show "?P 0\<^sub>h x1 x2"
      proof-
        let ?lx = "poincare_line x1 x2"

        have "x1 \<noteq> x2"
          using `x1 \<in> unit_disc` `x2 \<in> unit_disc``\<not> poincare_collinear  {0\<^sub>h, x1, x2}`
          using poincare_collinear3_between                  
          by auto

        have lx: "is_poincare_line ?lx"
          using is_poincare_line_poincare_line[OF `x1 \<noteq> x2`]
          by simp

        obtain i1 i2 where "ideal_points ?lx = {i1, i2}"
          by (meson \<open>x1 \<noteq> x2\<close> is_poincare_line_poincare_line obtain_ideal_points)
      
        let ?li = "poincare_line i1 i2"
        let ?i1 = "to_complex i1"
        let ?i2 = "to_complex i2"

        have "i1 \<in> unit_circle_set" "i2 \<in> unit_circle_set"
          using lx \<open>ideal_points ?lx = {i1, i2}\<close>
          unfolding unit_circle_set_def
          by (metis ideal_points_on_unit_circle insertI1, metis ideal_points_on_unit_circle insertI1 insertI2)
                                                               
        have "i1 \<noteq> i2"
          using \<open>ideal_points ?lx = {i1, i2}\<close> \<open>x1 \<in> unit_disc\<close> \<open>x1 \<noteq> x2\<close> \<open>x2 \<in> unit_disc\<close> ideal_points_different(1) 
          by blast

        let ?a1 = "of_complex (?i1 / 2)"
        let ?a2 = "of_complex (?i2 / 2)"
        let ?la = "poincare_line ?a1 ?a2"

        have "?a1 \<in> unit_disc" "?a2 \<in> unit_disc"
          using `i1 \<in> unit_circle_set` `i2 \<in> unit_circle_set`
          unfolding unit_circle_set_def unit_disc_def disc_def circline_set_def
          by auto (transfer, transfer, case_tac i1, case_tac i2, simp add: vec_cnj_def)+

        have "?a1 \<noteq> 0\<^sub>h" "?a2 \<noteq> 0\<^sub>h" 
          using `i1 \<in> unit_circle_set` `i2 \<in> unit_circle_set`
          unfolding unit_circle_set_def
          by auto

        have "?a1 \<noteq> ?a2"
          using `i1 \<noteq> i2`
          by (metis \<open>i1 \<in> unit_circle_set\<close> \<open>i2 \<in> unit_circle_set\<close> circline_set_def divide_cancel_right inversion_infty inversion_unit_circle mem_Collect_eq of_complex_to_complex of_complex_zero to_complex_of_complex unit_circle_set_def zero_neq_numeral)

        have "poincare_collinear {0\<^sub>h, ?a1, i1}"
          unfolding poincare_collinear_def
          using `?a1 \<noteq> 0\<^sub>h`[symmetric] is_poincare_line_poincare_line[of "0\<^sub>h" ?a1]
          unfolding circline_set_def
          apply (rule_tac x="poincare_line 0\<^sub>h ?a1" in exI, auto)
          apply (transfer, transfer, auto simp add: vec_cnj_def)
          done                                                               

        have "poincare_collinear {0\<^sub>h, ?a2, i2}"
          unfolding poincare_collinear_def
          using `?a2 \<noteq> 0\<^sub>h`[symmetric] is_poincare_line_poincare_line[of "0\<^sub>h" ?a2]
          unfolding circline_set_def
          apply (rule_tac x="poincare_line 0\<^sub>h ?a2" in exI, auto)
          apply (transfer, transfer, auto simp add: vec_cnj_def)
          done                                                               

        have "\<not> poincare_ray_meets_line 0\<^sub>h ?a1 x1 x2"
          using tangent_not_meet[of x1 x2 i1 ?a1]
          using `x1 \<in> unit_disc` `x2 \<in> unit_disc` `?a1 \<in> unit_disc` `x1 \<noteq> x2` `\<not> poincare_collinear {0\<^sub>h, x1, x2}`
          using `ideal_points ?lx = {i1, i2}` `?a1 \<noteq> 0\<^sub>h` `poincare_collinear {0\<^sub>h, ?a1, i1}`
          by simp

        moreover

        have "\<not> poincare_ray_meets_line 0\<^sub>h ?a2 x1 x2"
          using tangent_not_meet[of x1 x2 i2 ?a2]
          using `x1 \<in> unit_disc` `x2 \<in> unit_disc` `?a2 \<in> unit_disc` `x1 \<noteq> x2` `\<not> poincare_collinear {0\<^sub>h, x1, x2}`
          using `ideal_points ?lx = {i1, i2}` `?a2 \<noteq> 0\<^sub>h` `poincare_collinear {0\<^sub>h, ?a2, i2}`
          by simp

        moreover

        have "\<forall>a' \<in> unit_disc. poincare_in_angle a' ?a1 0\<^sub>h ?a2 \<longrightarrow> poincare_ray_meets_line 0\<^sub>h a' x1 x2"
          unfolding poincare_in_angle_def
        proof safe
          fix a' a
          assume *: "a' \<in> unit_disc" "a \<in> unit_disc" "poincare_on_ray a' 0\<^sub>h a" "a' \<noteq> 0\<^sub>h"
                    "poincare_between ?a1 a ?a2" "a \<noteq> ?a1" "a \<noteq> ?a2"
          show "poincare_ray_meets_line 0\<^sub>h a' x1 x2"
          proof-
            have "\<forall> a' a1 a2 x1 x2 i1 i2.
                  a' \<in> unit_disc \<and> x1 \<in> unit_disc \<and> x2 \<in> unit_disc \<and> x1 \<noteq> x2 \<and>
                  \<not> poincare_collinear {0\<^sub>h, x1, x2} \<and> ideal_points (poincare_line x1 x2) = {i1, i2} \<and>
                  a1 = of_complex (to_complex i1 / 2) \<and> a2 = of_complex (to_complex i2 / 2) \<and>
                  i1 \<noteq> i2 \<and> a1 \<noteq> a2 \<and> poincare_collinear {0\<^sub>h, a1, i1} \<and> poincare_collinear {0\<^sub>h, a2, i2} \<and>
                  a1 \<in> unit_disc \<and> a2 \<in> unit_disc \<and> i1 \<in> unit_circle_set \<and> i2 \<in> unit_circle_set \<and>
                  poincare_on_ray a' 0\<^sub>h a \<and> a' \<noteq> 0\<^sub>h \<and> poincare_between a1 a a2 \<and> a \<noteq> a1 \<and> a \<noteq> a2 \<longrightarrow>
                  poincare_ray_meets_line 0\<^sub>h a' x1 x2" (is "\<forall> a' a1 a2 x1 x2 i1 i2. ?R 0\<^sub>h a' a1 a2 x1 x2 i1 i2 a")
            proof (rule wlog_rotation_to_positive_x_axis[OF `a \<in> unit_disc`])
              let ?R' = "\<lambda> a zero. \<forall> a' a1 a2 x1 x2 i1 i2. ?R zero a' a1 a2 x1 x2 i1 i2 a"
              fix xa
              assume xa: "is_real xa" "0 < Re xa" "Re xa < 1"
              let ?a = "of_complex xa"
              show "?R' ?a 0\<^sub>h"
              proof safe
                fix a' a1 a2 x1 x2 i1 i2
                let ?i1 = "to_complex i1" and ?i2 = "to_complex i2"
                let ?a1 = "of_complex (?i1 / 2)" and ?a2 = "of_complex (?i2 / 2)"
                let ?la = "poincare_line ?a1 ?a2" and ?lx = "poincare_line x1 x2" and ?li = "poincare_line i1 i2"
                assume "a' \<in> unit_disc" "x1 \<in> unit_disc" "x2 \<in> unit_disc" "x1 \<noteq> x2"
                assume "\<not> poincare_collinear {0\<^sub>h, x1, x2}" "ideal_points ?lx = {i1, i2}"
                assume "poincare_on_ray a' 0\<^sub>h ?a" "a' \<noteq> 0\<^sub>h"
                assume "poincare_between ?a1 ?a ?a2"  "?a \<noteq> ?a1" "?a \<noteq> ?a2"
                assume "i1 \<noteq> i2" "?a1 \<noteq> ?a2" "poincare_collinear {0\<^sub>h, ?a1, i1}"  "poincare_collinear {0\<^sub>h, ?a2, i2}"
                assume "?a1 \<in> unit_disc"  "?a2 \<in> unit_disc"
                assume "i1 \<in> unit_circle_set" "i2 \<in> unit_circle_set"
                show "poincare_ray_meets_line 0\<^sub>h a' x1 x2"
                proof-   
                  have "?lx = ?li"
                    using \<open>ideal_points ?lx = {i1, i2}\<close> \<open>x1 \<noteq> x2\<close> ideal_points_line_unique
                    by auto

                  have lx: "is_poincare_line ?lx"
                    using is_poincare_line_poincare_line[OF `x1 \<noteq> x2`]
                    by simp

                  have "x1 \<in> circline_set ?lx" "x2 \<in> circline_set ?lx"
                    using lx \<open>x1 \<noteq> x2\<close>
                    by auto

                  have "?lx \<noteq> x_axis"
                    using `\<not> poincare_collinear {0\<^sub>h, x1, x2}` `x1 \<in> circline_set ?lx` `x2 \<in> circline_set ?lx` lx
                    unfolding poincare_collinear_def 
                    by auto

                  have "0\<^sub>h \<notin> circline_set ?lx"
                    using `\<not> poincare_collinear {0\<^sub>h, x1, x2}` lx `x1 \<in> circline_set ?lx` `x2 \<in> circline_set ?lx`
                    unfolding poincare_collinear_def
                    by auto

                  have "xa \<noteq> 0" "?a \<noteq> 0\<^sub>h" 
                    using xa
                    by auto
                  hence "0\<^sub>h \<noteq> ?a"
                    by metis

                  have "?a \<in> positive_x_axis"
                    using xa
                    unfolding positive_x_axis_def 
                    by simp

                  have "?a \<in> unit_disc"
                    using xa
                    by (auto simp add: cmod_eq_Re)

                  have "?a \<in> circline_set ?la"
                    using `poincare_between ?a1 ?a ?a2`
                    using \<open>?a1 \<noteq> ?a2\<close> \<open>?a \<in> unit_disc\<close> \<open>?a1 \<in> unit_disc\<close> \<open>?a2 \<in> unit_disc\<close> poincare_between_poincare_line_uzv 
                    by blast
                                                
                  have "?a1 \<in> circline_set ?la" "?a2 \<in> circline_set ?la"
                    by (auto simp add: \<open>?a1 \<noteq> ?a2\<close>)

                  have la: "is_poincare_line ?la"
                    using is_poincare_line_poincare_line[OF `?a1 \<noteq> ?a2`]
                    by  simp

                  have inv: "inversion i1 = i1" "inversion i2 = i2"
                    using `i1 \<in> unit_circle_set` `i2 \<in> unit_circle_set`
                    by (auto simp add: circline_set_def unit_circle_set_def)

                  have  "i1 \<noteq> \<infinity>\<^sub>h" "i2 \<noteq> \<infinity>\<^sub>h"
                    using inv
                    by auto

                  have "?a1 \<notin> circline_set x_axis \<and> ?a2 \<notin> circline_set x_axis"
                  proof (rule ccontr)
                    assume "\<not> ?thesis"
                    hence "?a1 \<in> circline_set x_axis \<or> ?a2 \<in> circline_set x_axis"
                      by auto
                    hence "?la = x_axis"
                    proof
                      assume "?a1 \<in> circline_set x_axis"
                      hence "{?a, ?a1} \<subseteq> circline_set ?la \<inter> circline_set x_axis"
                        using `?a \<in> circline_set ?la` `?a1 \<in> circline_set ?la``?a \<in> positive_x_axis`
                        using circline_set_x_axis_I xa(1) 
                        by blast
                      thus "?la = x_axis"
                        using unique_is_poincare_line[of ?a ?a1 ?la x_axis]
                        using `?a1 \<in> unit_disc` `?a \<in> unit_disc` la `?a \<noteq> ?a1`
                        by auto
                    next
                      assume "?a2 \<in> circline_set x_axis"
                      hence "{?a, ?a2} \<subseteq> circline_set ?la \<inter> circline_set x_axis"
                        using `?a \<in> circline_set ?la` `?a2 \<in> circline_set ?la` `?a \<in> positive_x_axis`
                        using circline_set_x_axis_I xa(1) 
                        by blast
                      thus "?la = x_axis"
                        using unique_is_poincare_line[of ?a ?a2 ?la x_axis]
                        using `?a2 \<in> unit_disc` `?a \<in> unit_disc` la `?a \<noteq> ?a2`
                        by auto
                    qed

                    hence "i1 \<in> circline_set x_axis \<and> i2 \<in> circline_set x_axis"
                      using `?a1 \<in> circline_set ?la` `?a2 \<in> circline_set ?la`
                      by (metis \<open>i1 \<noteq> \<infinity>\<^sub>h\<close> \<open>i2 \<noteq> \<infinity>\<^sub>h\<close> \<open>of_complex (to_complex i1 / 2) \<in> unit_disc\<close> \<open>of_complex (to_complex i2 / 2) \<in> unit_disc\<close> \<open>poincare_collinear {0\<^sub>h, of_complex (to_complex i1 / 2), i1}\<close> \<open>poincare_collinear {0\<^sub>h, of_complex (to_complex i2 / 2), i2}\<close> divide_eq_0_iff inf_not_of_complex inv(1) inv(2) inversion_noteq_unit_disc of_complex_to_complex of_complex_zero_iff poincare_collinear3_poincare_lines_equal_general poincare_line_0_real_is_x_axis poincare_line_circline_set(2) zero_in_unit_disc zero_neq_numeral)

                    thus False
                      using `?lx \<noteq> x_axis` unique_is_poincare_line_general[of i1 i2 ?li x_axis] `i1 \<noteq> i2` inv `?lx = ?li`
                      by auto
                  qed

                  hence "?la \<noteq> x_axis"
                    using \<open>?a1 \<noteq> ?a2\<close> poincare_line_circline_set(1)      
                    by fastforce

                  have "intersects_x_axis_positive ?la"
                    using intersects_x_axis_positive_iff[of ?la] `?la \<noteq> x_axis` `?a \<in> circline_set ?la` la
                    using `?a \<in> unit_disc` `?a \<in> positive_x_axis`
                    by auto

                  have "intersects_x_axis ?lx"
                  proof-
                    have "arg (to_complex ?a1) * arg (to_complex ?a2) < 0"
                      using `poincare_between ?a1 ?a ?a2` `?a1 \<in> unit_disc` `?a2 \<in> unit_disc`
                      using poincare_between_x_axis_intersection[of ?a1 ?a2 "of_complex xa"]
                      using `?a1 \<noteq> ?a2` `?a \<in> unit_disc` `?a1 \<notin> circline_set x_axis \<and> ?a2 \<notin> circline_set x_axis` `?a \<in> positive_x_axis`
                      using `?a \<in> circline_set ?la`                                                                                         
                      unfolding positive_x_axis_def
                      by simp

                    moreover

                    have "\<And> x y x' y' :: real. \<lbrakk>sgn x' = sgn x; sgn y' = sgn y\<rbrakk> \<Longrightarrow> x*y < 0 \<longleftrightarrow> x'*y' < 0"
                      by (metis sgn_less sgn_mult)

                    ultimately

                    have "Im (to_complex ?a1) * Im (to_complex ?a2) < 0"
                      using arg_Im_sgn[of "to_complex ?a1"] arg_Im_sgn[of "to_complex ?a2"]
                      using `?a1 \<in> unit_disc` `?a2 \<in> unit_disc` `?a1 \<notin> circline_set x_axis \<and> ?a2 \<notin> circline_set x_axis` 
                      using inf_or_of_complex[of ?a1] inf_or_of_complex[of ?a2] circline_set_x_axis
                      by (metis circline_set_x_axis_I to_complex_of_complex)

                    thus ?thesis
                      using ideal_points_intersects_x_axis[of ?lx i1 i2]
                      using `ideal_points ?lx = {i1, i2}` lx `?lx \<noteq> x_axis`
                      by simp
                  qed

                  have "intersects_x_axis_positive ?lx"
                  proof-
                    have "cmod ?i1 = 1" "cmod ?i2 = 1"                
                      using \<open>i1 \<in> unit_circle_set\<close> \<open>i2 \<in> unit_circle_set\<close> 
                      unfolding unit_circle_set_def 
                      by auto

                    let ?a1' = "?i1 / 2" and ?a2' = "?i2 / 2"
                    let ?Aa1 = "\<i> * (?a1' * cnj ?a2' - ?a2' * cnj ?a1')" and 
                        ?Ba1 = "\<i> * (?a2' * cor ((cmod ?a1')\<^sup>2 + 1) - ?a1' * cor ((cmod ?a2')\<^sup>2 + 1))"

                    have "?Aa1 \<noteq> 0 \<or> ?Ba1 \<noteq> 0"
                      using `cmod (to_complex i1) = 1`  `cmod (to_complex i2) = 1` `?a1 \<noteq> ?a2`              
                      by (auto simp add: power_divide complex_mult_cnj_cmod)

                    have "is_real ?Aa1"
                      by simp

                    have "?a1 \<noteq> inversion ?a2"
                      using \<open>?a1 \<in> unit_disc\<close> \<open>?a2 \<in> unit_disc\<close> inversion_noteq_unit_disc by fastforce

                    hence "Re ?Ba1 / Re ?Aa1 < -1"
                      using `intersects_x_axis_positive ?la` `?a1 \<noteq> ?a2`
                      using intersects_x_axis_positive_mk_circline[of ?Aa1 ?Ba1] `?Aa1 \<noteq> 0 \<or> ?Ba1 \<noteq> 0` `is_real ?Aa1`
                      using poincare_line_non_homogenous[of ?a1 ?a2]
                      by (simp add: Let_def)

                    moreover

                    let ?i1' = "to_complex i1" and ?i2' = "to_complex i2"
                    let ?Ai1 = "\<i> * (?i1' * cnj ?i2' - ?i2' * cnj ?i1')" and 
                        ?Bi1 = "\<i> * (?i2' * cor ((cmod ?i1')\<^sup>2 + 1) - ?i1' * cor ((cmod ?i2')\<^sup>2 + 1))"

                    have "?Ai1 \<noteq> 0 \<or> ?Bi1 \<noteq> 0"
                      using `cmod (to_complex i1) = 1`  `cmod (to_complex i2) = 1` `?a1 \<noteq> ?a2`              
                      by (auto simp add: power_divide complex_mult_cnj_cmod)

                    have "is_real ?Ai1"
                      by simp

                    have "sgn (Re ?Bi1 / Re ?Ai1) = sgn (Re ?Ba1 / Re ?Aa1)"  
                    proof-
                      have "Re ?Bi1 / Re ?Ai1 = (Im ?i1 * 2 - Im ?i2 * 2) /
                                                (Im ?i2 * (Re ?i1 * 2) - Im ?i1 * (Re ?i2 * 2))"
                        using `cmod ?i1 = 1`  `cmod ?i2 = 1`
                        by (auto simp add: complex_mult_cnj_cmod field_simps)
                      also have "... =  (Im ?i1 - Im ?i2) /
                                        (Im ?i2 * (Re ?i1) - Im ?i1 * (Re ?i2))" (is "... = ?expr")
                        apply (subst left_diff_distrib[symmetric])
                        apply (subst semiring_normalization_rules(18))+
                        apply (subst left_diff_distrib[symmetric])
                        by (metis mult.commute mult_divide_mult_cancel_left_if zero_neq_numeral)
                      finally have 1: "Re ?Bi1 / Re ?Ai1 = (Im ?i1 - Im ?i2) / (Im ?i2 * (Re ?i1) - Im ?i1 * (Re ?i2))"
                        .

                
                      have "Re ?Ba1 / Re ?Aa1 = (Im ?i1 * 20 - Im ?i2 * 20) /
                                                (Im ?i2 * (Re ?i1 * 16) - Im ?i1 * (Re ?i2 * 16))"
                        using `cmod (to_complex i1) = 1`  `cmod (to_complex i2) = 1`
                        by (auto simp add: complex_mult_cnj_cmod field_simps)
                      also have "... = (20 / 16) * ((Im ?i1 - Im ?i2) /
                                       (Im ?i2 * (Re ?i1) - Im ?i1 * (Re ?i2)))"
                        apply (subst left_diff_distrib[symmetric])+
                        apply (subst semiring_normalization_rules(18))+
                        apply (subst left_diff_distrib[symmetric])+
                        by (metis (no_types, hide_lams)  field_class.field_divide_inverse mult.commute times_divide_times_eq)
                      finally have 2: "Re ?Ba1 / Re ?Aa1 = (5 / 4) * ((Im ?i1 - Im ?i2) / (Im ?i2 * (Re ?i1) - Im ?i1 * (Re ?i2)))"
                        by simp

                      have "?expr \<noteq> 0"
                        using `Re ?Ba1 / Re ?Aa1 < -1`
                        apply  (subst (asm) 2)
                        by linarith
                      thus ?thesis
                        apply (subst 1, subst 2)
                        apply (simp only: sgn_mult)
                        by simp
                    qed
                      

                    moreover

                    have "i1 \<noteq> inversion i2"
                      by (simp add: \<open>i1 \<noteq> i2\<close> inv(2))

                    have "(Re ?Bi1 / Re ?Ai1)\<^sup>2 > 1"
                    proof-
                      have "?Ai1 = 0 \<or> (Re ?Bi1)\<^sup>2 > (Re ?Ai1)\<^sup>2"
                        using `intersects_x_axis ?lx`
                        using `i1 \<noteq> i2` `i1 \<noteq> \<infinity>\<^sub>h` `i2 \<noteq> \<infinity>\<^sub>h` `i1 \<noteq> inversion i2`
                        using intersects_x_axis_mk_circline[of ?Ai1 ?Bi1] `?Ai1 \<noteq> 0 \<or> ?Bi1 \<noteq> 0` `is_real ?Ai1`
                        using poincare_line_non_homogenous[of i1 i2] `?lx = ?li`
                        by metis
                                                  
                      moreover
                      have "?Ai1 \<noteq> 0"
                      proof (rule ccontr)
                        assume "\<not> ?thesis"
                        hence "0\<^sub>h \<in> circline_set ?li"
                          unfolding circline_set_def
                          apply simp
                          apply (transfer, transfer, case_tac i1, case_tac i2)
                          by (auto simp add: vec_cnj_def field_simps)
                        thus False
                          using `0\<^sub>h \<notin> circline_set ?lx` `?lx = ?li`
                          by simp
                      qed

                      ultimately

                      have "(Re ?Bi1)\<^sup>2 > (Re ?Ai1)\<^sup>2"    
                        by auto

                      moreover

                      have "Re ?Ai1 \<noteq> 0"
                        using `is_real ?Ai1` `?Ai1 \<noteq> 0`
                        by (simp add: complex_eq_iff)

                      ultimately

                      show ?thesis
                        by (simp add: power_divide)
                    qed

                    moreover

                    {
                      fix x1 x2 :: real
                      assume "sgn x1 = sgn x2" "x1 < -1" "x2\<^sup>2 > 1"
                      hence "x2 < -1"
                        by (smt one_power2 real_sqrt_abs real_sqrt_less_iff sgn_neg sgn_pos)
                    }

                    ultimately

                    have "Re ?Bi1 / Re ?Ai1 < -1"
                      by metis

                    thus ?thesis
                      using `i1 \<noteq> i2` `i1 \<noteq> \<infinity>\<^sub>h` `i2 \<noteq> \<infinity>\<^sub>h` `i1 \<noteq> inversion i2`
                      using intersects_x_axis_positive_mk_circline[of ?Ai1 ?Bi1] `?Ai1 \<noteq> 0 \<or> ?Bi1 \<noteq> 0` `is_real ?Ai1`
                      using poincare_line_non_homogenous[of i1 i2] `?lx = ?li`
                      by (simp add: Let_def)
                  qed

                  then obtain x where x: "x \<in> unit_disc" "x \<in> circline_set ?lx \<inter> positive_x_axis"
                    using intersects_x_axis_positive_iff[OF lx `?lx \<noteq> x_axis`]
                    by auto

                  have "poincare_on_ray x 0\<^sub>h a' \<and> poincare_collinear {x1, x2, x}"
                  proof
                    show "poincare_collinear {x1, x2, x}"
                      using x lx `x1 \<in> circline_set ?lx` `x2 \<in> circline_set ?lx`
                      unfolding poincare_collinear_def
                      by auto
                  next
                    show "poincare_on_ray x 0\<^sub>h a'"
                      unfolding poincare_on_ray_def
                    proof-
                      have  "a' \<in> circline_set x_axis"
                        using `poincare_on_ray a' 0\<^sub>h ?a` xa `0\<^sub>h \<noteq> ?a` `xa \<noteq> 0` `a' \<in> unit_disc`
                        unfolding poincare_on_ray_def 
                        using poincare_line_0_real_is_x_axis[of "of_complex xa"]
                        using poincare_between_poincare_line_uvz[of "0\<^sub>h" "of_complex xa" a']
                        using poincare_between_poincare_line_uzv[of "0\<^sub>h" "of_complex xa" a']
                        by (auto simp  add: cmod_eq_Re)

                      then obtain xa' where xa': "a' = of_complex xa'" "is_real xa'"
                        using `a' \<in> unit_disc`
                        using circline_set_def on_circline_x_axis 
                        by auto

                      hence "-1 < Re xa'" "Re xa' < 1" "xa' \<noteq> 0"
                        using `a' \<in> unit_disc` `a' \<noteq> 0\<^sub>h`
                        by (auto simp add: cmod_eq_Re)

                      hence "Re xa' > 0" "Re xa' < 1" "is_real xa'"
                        using `poincare_on_ray a' 0\<^sub>h (of_complex xa)`
                        using poincare_between_x_axis_0uv[of "Re xa'" "Re xa"]
                        using poincare_between_x_axis_0uv[of "Re xa" "Re xa'"]
                        using circline_set_positive_x_axis_I[of "Re xa'"]
                        using xa xa' complex_of_real_Re
                        unfolding poincare_on_ray_def
                        by (smt of_real_0, linarith, blast)

                      moreover

                      obtain xx where "is_real xx" "Re xx > 0" "Re xx < 1" "x = of_complex xx"
                        using x
                        unfolding positive_x_axis_def
                        using circline_set_def cmod_eq_Re on_circline_x_axis
                        by auto

                      ultimately

                      show "poincare_between 0\<^sub>h x a' \<or> poincare_between 0\<^sub>h a' x"
                        using `a' = of_complex xa'`
                        by (smt \<open>a' \<in> unit_disc\<close> arg_0_iff poincare_between_0uv poincare_between_def to_complex_of_complex x(1))
                    qed

                  qed

                  thus ?thesis               
                    using `x \<in> unit_disc`
                    unfolding poincare_ray_meets_line_def poincare_on_line_def
                    by (metis insert_commute)
                qed
              qed
            next
              show "a \<noteq> 0\<^sub>h"
              proof (rule ccontr)
                assume "\<not> ?thesis"
                then obtain k where "k<0" "to_complex ?a1 = cor k * to_complex ?a2"
                  using poincare_between_u0v[OF `?a1 \<in> unit_disc` `?a2 \<in> unit_disc` `?a1 \<noteq> 0\<^sub>h` `?a2 \<noteq> 0\<^sub>h`]
                  using `poincare_between ?a1 a ?a2`
                  by auto
                hence "to_complex i1 = cor k * to_complex i2" "k < 0"
                  by auto
                hence "0\<^sub>h \<in> circline_set (poincare_line x1 x2)"
                  using ideal_points_proportional[of "poincare_line x1 x2" i1 i2 k] `ideal_points (poincare_line x1 x2) = {i1, i2}`
                  using is_poincare_line_poincare_line[OF `x1 \<noteq> x2`]
                  by simp
                thus False
                  using `\<not> poincare_collinear {0\<^sub>h, x1, x2}`
                  using is_poincare_line_poincare_line[OF `x1 \<noteq> x2`]
                  unfolding poincare_collinear_def
                  by (meson \<open>x1 \<noteq> x2\<close> empty_subsetI insert_subset poincare_line_circline_set(1) poincare_line_circline_set(2))
              qed
            next
              fix \<phi> u
              let ?R' = "\<lambda> a zero. \<forall> a' a1 a2 x1 x2 i1 i2. ?R zero a' a1 a2 x1 x2 i1 i2 a"
              let ?M = "moebius_pt (moebius_rotation \<phi>)"
              assume *: "u \<in> unit_disc" "u \<noteq> 0\<^sub>h" and **: "?R' (?M u) 0\<^sub>h"
              have uf: "unit_disc_fix (moebius_rotation \<phi>)"
                by simp
              have "?M 0\<^sub>h = 0\<^sub>h"
                by auto
              hence **: "?R' (?M u) (?M 0\<^sub>h)"
                using **
                by simp
              show "?R' u 0\<^sub>h"
              proof (rule allI)+
                fix a' a1 a2 x1 x2 i1 i2
                have i1: "i1 \<in> unit_circle_set \<longrightarrow> moebius_pt (moebius_rotation \<phi>) (of_complex (to_complex i1 / 2)) = of_complex (to_complex (moebius_pt (moebius_rotation \<phi>) i1) / 2)"
                  using unit_circle_set_def by force
                
                have i2: "i2 \<in> unit_circle_set \<longrightarrow> moebius_pt (moebius_rotation \<phi>) (of_complex (to_complex i2 / 2)) = of_complex (to_complex (moebius_pt (moebius_rotation \<phi>) i2) / 2)"
                  using unit_circle_set_def by force
                
                show "?R 0\<^sub>h a' a1 a2 x1 x2 i1 i2 u"
                  using **[rule_format, of "?M a'" "?M x1" "?M x2" "?M i1" "?M i2" "?M a1" "?M a2"] uf * 
                  apply (auto simp del:  moebius_pt_moebius_rotation_zero moebius_pt_moebius_rotation)
                  using i1 i2
                  by simp
              qed
            qed
            thus ?thesis                                                                  
              using `a' \<in> unit_disc` `x1 \<in> unit_disc` `x2 \<in> unit_disc` `x1 \<noteq> x2` 
              using `\<not> poincare_collinear {0\<^sub>h, x1, x2}` `ideal_points ?lx = {i1, i2}` `i1 \<noteq> i2`
              using `?a1 \<noteq> ?a2` `poincare_collinear {0\<^sub>h, ?a1, i1}` `poincare_collinear {0\<^sub>h, ?a2, i2}`
              using `?a1 \<in> unit_disc` `?a2 \<in> unit_disc` `i1 \<in> unit_circle_set` `i2 \<in> unit_circle_set`
              using `poincare_on_ray a' 0\<^sub>h a` `a' \<noteq> 0\<^sub>h` `poincare_between ?a1 a ?a2` `a \<noteq> ?a1` `a \<noteq> ?a2`
              by blast
          qed
        qed

        moreover

        have "\<not> poincare_on_line 0\<^sub>h ?a1 ?a2"
        proof
          assume *: "poincare_on_line 0\<^sub>h ?a1 ?a2"
          hence "poincare_collinear {0\<^sub>h, ?a1, ?a2}"
            unfolding poincare_on_line_def
            by simp
          hence "poincare_line 0\<^sub>h ?a1 = poincare_line 0\<^sub>h ?a2"
            using poincare_collinear3_poincare_lines_equal_general[of "0\<^sub>h" ?a1 ?a2]
            using \<open>?a1 \<in> unit_disc\<close> \<open>?a1 \<noteq> 0\<^sub>h\<close> \<open>?a2 \<in> unit_disc\<close> \<open>?a2 \<noteq> 0\<^sub>h\<close> 
            by (metis inversion_noteq_unit_disc zero_in_unit_disc)

          have "i1 \<in> circline_set (poincare_line 0\<^sub>h ?a1)"
            using `poincare_collinear {0\<^sub>h, ?a1, i1}`
            using poincare_collinear3_poincare_line_general[of i1 "0\<^sub>h" ?a1]
            using \<open>?a1 \<in> unit_disc\<close> `?a1 \<noteq> 0\<^sub>h`
            by (metis insert_commute inversion_noteq_unit_disc zero_in_unit_disc)
          moreover
          have "i2 \<in> circline_set (poincare_line 0\<^sub>h ?a1)"
            using `poincare_collinear {0\<^sub>h, ?a2, i2}`
            using poincare_collinear3_poincare_line_general[of i2 "0\<^sub>h" ?a2]
            using \<open>?a2 \<in> unit_disc\<close> `?a2 \<noteq> 0\<^sub>h` \<open>poincare_line 0\<^sub>h ?a1 = poincare_line 0\<^sub>h ?a2\<close>
            by (metis insert_commute inversion_noteq_unit_disc zero_in_unit_disc)

          ultimately

          have "poincare_collinear {0\<^sub>h, i1, i2}"
            using \<open>?a1 \<in> unit_disc\<close> \<open>?a1 \<noteq> 0\<^sub>h\<close> \<open>poincare_collinear {0\<^sub>h, ?a1, i1}\<close>
            by (smt insert_subset poincare_collinear_def unique_poincare_line zero_in_unit_disc)
          hence "0\<^sub>h \<in> circline_set (poincare_line i1 i2)"
            using poincare_collinear3_poincare_line_general[of "0\<^sub>h" i1 i2]
            using \<open>i1 \<noteq> i2\<close> \<open>i2 \<in> unit_circle_set\<close> unit_circle_set_def
            by force

          moreover

          have "?lx = ?li"
            using \<open>ideal_points ?lx = {i1, i2}\<close> \<open>x1 \<noteq> x2\<close> ideal_points_line_unique
            by auto

          ultimately

          show False
            using \<open>\<not> poincare_collinear {0\<^sub>h, x1, x2}\<close>
            using \<open>x1 \<noteq> x2\<close> poincare_line_poincare_collinear3_general
            by auto
        qed          

        ultimately

        show ?thesis
          using `?a1 \<in> unit_disc` `?a2 \<in> unit_disc`
          by blast
      qed
    qed
  qed
  thus ?thesis
    using `x1 \<in> unit_disc` `x2 \<in> unit_disc` `\<not> poincare_collinear {a, x1, x2}`
    by blast
qed                                                                        

subsection\<open>Interpretation of locales\<close>

global_interpretation PoincareTarskiAbsolute: TarskiAbsolute where cong  = p_congruent and betw = p_between
  defines p_on_line = PoincareTarskiAbsolute.on_line and
          p_on_ray = PoincareTarskiAbsolute.on_ray and
          p_in_angle = PoincareTarskiAbsolute.in_angle and
          p_ray_meets_line = PoincareTarskiAbsolute.ray_meets_line
proof-
  show "TarskiAbsolute p_congruent p_between"
  proof
    text\<open> 1. Reflexivity of congruence \<close>
    fix x y
    show "p_congruent x y y x"
      unfolding p_congruent_def
      by transfer (simp add: poincare_distance_sym)
  next
    text\<open> 2. Transitivity of congruence \<close>
    fix x y z u v w
    show "p_congruent x y z u \<and> p_congruent x y v w \<longrightarrow> p_congruent z u v w"
      by (transfer, simp)
  next
    text\<open> 3. Identity of congruence \<close>
    fix x y z
    show "p_congruent x y z z \<longrightarrow> x = y"
      unfolding p_congruent_def
      by transfer (simp add: poincare_distance_eq_0_iff)
  next
    text\<open> 4. Segment construction \<close>
    fix x y a b
    show "\<exists> z. p_between x y z \<and> p_congruent y z a b"
      using segment_construction
      unfolding p_congruent_def
      by transfer (simp, blast)
  next
    text\<open> 5. Five segment \<close>
    fix x y z x' y' z' u u'
    show "x \<noteq> y \<and> p_between x y z \<and> p_between x' y' z' \<and>
      p_congruent x y x' y' \<and> p_congruent y z y' z' \<and>
      p_congruent x u x' u' \<and> p_congruent y u y' u' \<longrightarrow>
      p_congruent z u z' u'"
      unfolding p_congruent_def
      apply transfer
      using five_segment_axiom                                             
      by meson
  next
    text\<open> 6. Identity of betweeness \<close>
    fix x y
    show "p_between x y x \<longrightarrow> x = y"
      by transfer (simp add: poincare_between_sum_distances poincare_distance_eq_0_iff poincare_distance_sym)
  next
    text\<open> 7. Pasch \<close>
    fix x y z u v
    show "p_between x u z \<and> p_between y v z \<longrightarrow> (\<exists> a. p_between u a y \<and> p_between x a v)"
      apply transfer
      using Pasch
      by blast
  next
    text\<open> 8. Lower dimension \<close>
    show "\<exists> a. \<exists> b. \<exists> c. \<not> p_between a b c \<and> \<not> p_between b c a \<and> \<not> p_between c a b"
      apply (transfer)
      using lower_dimension_axiom
      by simp
  next
    text\<open> 9. Upper dimension \<close>
    fix x y z u v
    show "p_congruent x u x v \<and> p_congruent y u y v \<and> p_congruent z u z v \<and> u \<noteq> v \<longrightarrow>
          p_between x y z \<or> p_between y z x \<or> p_between z x y"
      unfolding p_congruent_def
      by (transfer, simp add: upper_dimension_axiom)
  qed
qed 


interpretation PoincareTarskiHyperbolic: TarskiHyperbolic
  where cong = p_congruent and betw = p_between
proof
  text\<open> 10. Euclid negation \<close>
  show "\<exists> a b c d t. p_between a d t \<and> p_between b d c \<and> a \<noteq> d \<and>
                   (\<forall> x y. p_between a b x \<and> p_between a c y \<longrightarrow> \<not> p_between x t y)"
    using negated_euclidean_axiom
    by transfer (auto, blast)
next
  fix a x1  x2
  assume "\<not> TarskiAbsolute.on_line p_between a x1 x2"
  hence "\<not> p_on_line a x1 x2"
    using TarskiAbsolute.on_line_def[OF PoincareTarskiAbsolute.TarskiAbsolute_axioms]
    using PoincareTarskiAbsolute.on_line_def
    by simp
  text\<open> 11. Limiting parallels  \<close>
  thus "\<exists>a1 a2.
          \<not> TarskiAbsolute.on_line p_between a a1 a2 \<and>
          \<not> TarskiAbsolute.ray_meets_line p_between a a1 x1 x2 \<and>
          \<not> TarskiAbsolute.ray_meets_line p_between a a2 x1 x2 \<and>
          (\<forall>a'. TarskiAbsolute.in_angle p_between a' a1 a a2 \<longrightarrow> TarskiAbsolute.ray_meets_line p_between a a' x1 x2)"
    unfolding TarskiAbsolute.in_angle_def[OF PoincareTarskiAbsolute.TarskiAbsolute_axioms]
    unfolding TarskiAbsolute.on_ray_def[OF PoincareTarskiAbsolute.TarskiAbsolute_axioms]
    unfolding TarskiAbsolute.ray_meets_line_def[OF PoincareTarskiAbsolute.TarskiAbsolute_axioms]
    unfolding TarskiAbsolute.on_ray_def[OF PoincareTarskiAbsolute.TarskiAbsolute_axioms]
    unfolding TarskiAbsolute.on_line_def[OF PoincareTarskiAbsolute.TarskiAbsolute_axioms]
    unfolding PoincareTarskiAbsolute.on_line_def
    apply transfer
  proof- 
    fix a x1 x2
    assume *: "a \<in> unit_disc" "x1 \<in> unit_disc" "x2 \<in> unit_disc"
              "\<not> (poincare_between a x1 x2 \<or> poincare_between x1 a x2 \<or> poincare_between x1 x2 a)"
    hence "\<not> poincare_on_line a x1 x2"
      using poincare_collinear3_iff[of a x1 x2]
      using poincare_between_rev poincare_on_line_def by blast
    hence "\<exists>a1\<in>unit_disc.
            \<exists>a2\<in>unit_disc.
            \<not> poincare_on_line a a1 a2 \<and>
            \<not> poincare_ray_meets_line a a1 x1 x2 \<and>
            \<not> poincare_ray_meets_line a a2 x1 x2 \<and>
            (\<forall>a'\<in>unit_disc.
                poincare_in_angle a' a1 a a2 \<longrightarrow>
                poincare_ray_meets_line a a' x1 x2)"
      using limiting_parallels[of a x1 x2] *
      by blast
    then obtain a1 a2 where **: "a1\<in>unit_disc" "a2\<in>unit_disc" "\<not> poincare_on_line a a1 a2"
                            "\<not> poincare_ray_meets_line a a2 x1 x2"
                            "\<not> poincare_ray_meets_line a a1 x1 x2"
                            "\<forall>a'\<in>unit_disc.
                                  poincare_in_angle a' a1 a a2 \<longrightarrow>
                                  poincare_ray_meets_line a a' x1 x2"
      by blast
    have "\<not> (\<exists>x\<in>{z. z \<in> unit_disc}.
                    (poincare_between a x a1 \<or>
                     poincare_between a a1 x) \<and>
                    (poincare_between x x1 x2 \<or>
                     poincare_between x1 x x2 \<or>
                     poincare_between x1 x2 x))"
      using `\<not> poincare_ray_meets_line a a1 x1 x2`
      unfolding poincare_on_line_def poincare_ray_meets_line_def poincare_on_ray_def
      using poincare_collinear3_iff[of _ x1 x2] poincare_between_rev *(2, 3)
      by auto
    moreover
    have "\<not> (\<exists>x\<in>{z. z \<in> unit_disc}.
                    (poincare_between a x a2 \<or>
                     poincare_between a a2 x) \<and>
                    (poincare_between x x1 x2 \<or>
                     poincare_between x1 x x2 \<or>
                     poincare_between x1 x2 x))"
      using `\<not> poincare_ray_meets_line a a2 x1 x2`
      unfolding poincare_on_line_def poincare_ray_meets_line_def poincare_on_ray_def
      using poincare_collinear3_iff[of _ x1 x2] poincare_between_rev *(2, 3)
      by auto
    moreover
    have "\<not> (poincare_between a a1 a2 \<or> poincare_between a1 a a2 \<or> poincare_between a1 a2 a)"
      using `\<not> poincare_on_line a a1 a2` poincare_collinear3_iff[of a a1 a2]
      using *(1) **(1-2)
      unfolding poincare_on_line_def
      by simp
    moreover 
    have "(\<forall>a'\<in>{z. z \<in> unit_disc}.
                 a \<noteq> a1 \<and>
                 a \<noteq> a2 \<and>
                 a' \<noteq> a \<and>
                 (\<exists>x\<in>{z. z \<in> unit_disc}.
                     poincare_between a1 x a2 \<and>
                     x \<noteq> a1 \<and>
                     x \<noteq> a2 \<and>
                     (poincare_between a a' x \<or>
                      poincare_between a x a')) \<longrightarrow>
                 (\<exists>x\<in>{z. z \<in> unit_disc}.
                     (poincare_between a x a' \<or>
                      poincare_between a a' x) \<and>
                     (poincare_between x x1 x2 \<or>
                      poincare_between x1 x x2 \<or>
                      poincare_between x1 x2 x)))"
      using **(6)
      unfolding poincare_on_line_def poincare_in_angle_def poincare_ray_meets_line_def poincare_on_ray_def
      using poincare_collinear3_iff[of _ x1 x2] poincare_between_rev *(2, 3)
      by auto
    ultimately
    show "\<exists>a1\<in>{z. z \<in> unit_disc}.
           \<exists>a2\<in>{z. z \<in> unit_disc}.
             \<not> (poincare_between a a1 a2 \<or> poincare_between a1 a a2 \<or> poincare_between a1 a2 a) \<and>
             \<not> (\<exists>x\<in>{z. z \<in> unit_disc}.
                    (poincare_between a x a1 \<or>
                     poincare_between a a1 x) \<and>
                    (poincare_between x x1 x2 \<or>
                     poincare_between x1 x x2 \<or>
                     poincare_between x1 x2 x)) \<and>
             \<not> (\<exists>x\<in>{z. z \<in> unit_disc}.
                    (poincare_between a x a2 \<or>
                     poincare_between a a2 x) \<and>
                    (poincare_between x x1 x2 \<or>
                     poincare_between x1 x x2 \<or>
                     poincare_between x1 x2 x)) \<and>
             (\<forall>a'\<in>{z. z \<in> unit_disc}.
                 a \<noteq> a1 \<and>
                 a \<noteq> a2 \<and>
                 a' \<noteq> a \<and>
                 (\<exists>x\<in>{z. z \<in> unit_disc}.
                     poincare_between a1 x a2 \<and>
                     x \<noteq> a1 \<and>
                     x \<noteq> a2 \<and>
                     (poincare_between a a' x \<or>
                      poincare_between a x a')) \<longrightarrow>
                 (\<exists>x\<in>{z. z \<in> unit_disc}.
                     (poincare_between a x a' \<or>
                      poincare_between a a' x) \<and>
                     (poincare_between x x1 x2 \<or>
                      poincare_between x1 x x2 \<or>
                      poincare_between x1 x2 x)))" 
      using **(1, 2)
      by auto
   qed
qed

interpretation PoincareElementaryTarskiHyperbolic: ElementaryTarskiHyperbolic p_congruent p_between
proof
  text\<open> 12.  Continuity \<close>
  fix \<phi> \<psi>
  assume "\<exists> a. \<forall> x. \<forall> y. \<phi> x \<and> \<psi> y \<longrightarrow> p_between a x y"
  thus "\<exists> b. \<forall> x. \<forall> y. \<phi> x \<and> \<psi> y \<longrightarrow> p_between x b y"
    apply transfer
    using continuity
    by auto
qed

end
