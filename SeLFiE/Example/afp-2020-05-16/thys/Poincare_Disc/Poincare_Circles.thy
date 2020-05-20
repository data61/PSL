theory Poincare_Circles
  imports Poincare_Distance
begin
(* -------------------------------------------------------------------------- *)
section\<open>H-circles in the Poincar\'e model\<close>
(* -------------------------------------------------------------------------- *)

text\<open>Circles consist of points that are at the same distance from the center.\<close>
definition poincare_circle :: "complex_homo \<Rightarrow> real \<Rightarrow> complex_homo set" where
  "poincare_circle z r = {z'. z' \<in> unit_disc \<and> poincare_distance z z' = r}"

text\<open>Each h-circle in the Poincar\'e model is represented by an Euclidean circle in the model ---
the center and radius of that euclidean circle are determined by the following formulas.\<close>
definition poincare_circle_euclidean :: "complex_homo \<Rightarrow> real \<Rightarrow> euclidean_circle" where
  "poincare_circle_euclidean z r =
      (let R = (cosh r - 1) / 2;
           z' = to_complex z;
           cz = 1 - (cmod z')\<^sup>2;
           k = cz * R + 1
        in (z' / k, cz * sqrt(R * (R + 1)) / k))"

text\<open>That Euclidean circle has a positive radius and is always fully within the disc.\<close>
lemma poincare_circle_in_disc:
  assumes "r > 0" and "z \<in> unit_disc" and "(ze, re) = poincare_circle_euclidean z r"
  shows "cmod ze < 1" "re > 0" "\<forall> x \<in> circle ze re. cmod x < 1"
proof-
  let ?R = "(cosh r - 1) / 2"
  let ?z' = "to_complex z"
  let ?cz = "1 - (cmod ?z')\<^sup>2"
  let ?k = "?cz * ?R + 1"
  let ?ze = "?z' / ?k"
  let ?re = "?cz * sqrt(?R * (?R + 1)) / ?k"

  from \<open>z \<in> unit_disc\<close>
  obtain z' where z': "z = of_complex z'"
    using inf_or_of_complex[of z]
    by auto

  hence "z' = ?z'"
    by simp

  obtain cz where cz: "cz = (1 - (cmod z')\<^sup>2)"
    by auto

  have "cz > 0" "cz \<le> 1"
    using \<open>z \<in> unit_disc\<close> z' cz
    using unit_disc_cmod_square_lt_1
    by fastforce+

  obtain R where R: "R = ?R"
    by blast

  have "R > 0"
    using cosh_gt_1[of r] \<open>r > 0\<close>
    by (subst R) simp

  obtain k where k: "k = cz * R + 1"
    by auto

  have "k > 1"
    using k \<open>R > 0\<close> \<open>cz > 0\<close>
    by simp

  hence "cmod k = k"
    by simp

  let ?RR = "cz * sqrt(R * (R + 1)) / k"

  have "cmod z' + cz * sqrt(R * (R + 1)) < k"
  proof-
    have "((R+1)-R)\<^sup>2 > 0"
      by simp
    hence "(R+1)\<^sup>2 - 2*R*(R+1) + R\<^sup>2 > 0"
      unfolding power2_diff
      by (simp add: field_simps)
    hence "(R+1)\<^sup>2 + 2*R*(R+1) + R\<^sup>2 - 4*R*(R+1) > 0"
      by simp
    hence "(2*R+1)\<^sup>2 / 4 > R*(R+1)"
      using power2_sum[of "R+1" R]
      by (simp add: field_simps)
    hence "sqrt(R*(R+1)) < (2*R+1) / 2"
      using \<open>R > 0\<close>
      by (smt arith_geo_mean_sqrt power_divide real_sqrt_four real_sqrt_pow2 zero_le_mult_iff)
    hence "sqrt(R*(R+1)) - R < 1/2"
      by (simp add: field_simps)
    hence "(1 + (cmod z')) * (sqrt(R*(R+1)) - R) < (1 + (cmod z')) *  (1 / 2)"
      by (subst mult_strict_left_mono, simp, smt norm_not_less_zero, simp)
    also have "... < 1"
      using \<open>z \<in> unit_disc\<close> z'
      by auto
    finally have "(1 - cmod z') * ((1 + cmod z') * (sqrt(R*(R+1)) - R)) < (1 - cmod z') * 1"
      using \<open>z \<in> unit_disc\<close> z'
      by (subst mult_strict_left_mono, simp_all)
    hence "cz * (sqrt (R*(R+1)) - R) < 1 - cmod z'"
      using square_diff_square_factored[of 1 "cmod z'"]
      by (subst cz, subst (asm) mult.assoc[symmetric], simp add: power2_eq_square field_simps)
    hence "cmod z' + cz * sqrt(R*(R+1)) < 1 + R * cz"
      by (simp add: field_simps)
    thus ?thesis
      using k
      by (simp add: field_simps)
  qed
  hence "cmod z' / k + cz * sqrt(R * (R + 1)) / k < 1"
    using \<open>k > 1\<close>
    unfolding add_divide_distrib[symmetric]
    by simp
  hence "cmod (z' / k) + cz * sqrt(R * (R + 1)) / k < 1"
    using \<open>k > 1\<close>
    by simp
  hence "cmod ?ze + ?re < 1"
    using k cz \<open>R = ?R\<close> z'
    by simp

  moreover

  have "cz * sqrt(R * (R + 1)) / k > 0"
    using \<open>cz > 0\<close> \<open>R > 0\<close> \<open>k > 1\<close>
    by auto
  hence "?re > 0"
    using k cz \<open>R = ?R\<close> z'
    by simp

  moreover

  have "cmod ?ze < 1"
    using \<open>cmod ?ze + ?re < 1\<close> \<open>?re > 0\<close>
    by simp

  moreover

  have "ze = ?ze" "re = ?re"
    using \<open>(ze, re) = poincare_circle_euclidean z r\<close>
    unfolding poincare_circle_euclidean_def Let_def
    by simp_all

  moreover

  have "\<forall> x \<in> circle ze re. cmod x \<le> cmod ze + re"
    using norm_triangle_ineq2[of _ ze]
    unfolding circle_def
    by (smt mem_Collect_eq)

  ultimately

  show "cmod ze < 1" "re > 0" "\<forall> x \<in> circle ze re. cmod x < 1"
    by auto
qed

text\<open>The connection between the points on the h-circle and its corresponding Euclidean circle.\<close>
lemma poincare_circle_is_euclidean_circle:
  assumes "z \<in> unit_disc" and "r > 0"
  shows  "let (Ze, Re) = poincare_circle_euclidean z r
           in of_complex ` (circle Ze Re) = poincare_circle z r"
proof-
  {
    fix x
    let ?z = "to_complex z"

    from assms obtain z' where z': "z = of_complex z'" "cmod z' < 1"
      using inf_or_of_complex[of z]
      by auto

    have *: "\<And> x. cmod x < 1 \<Longrightarrow> 1 - (cmod x)\<^sup>2 > 0"
      by (metis less_iff_diff_less_0 minus_diff_eq mult.left_neutral neg_less_0_iff_less norm_mult_less norm_power power2_eq_square)

    let ?R = "(cosh r - 1) / 2"
    obtain R where R: "R = ?R"
      by blast

    let ?cx = "1 - (cmod x)\<^sup>2" and ?cz = "1 - (cmod z')\<^sup>2"  and ?czx = "(cmod (z' - x))\<^sup>2"

    let ?k = "1 + R * ?cz"
    obtain k where k: "k = ?k"
      by blast
    have "R > 0"
      using R cosh_gt_1[OF \<open>r > 0\<close>]
      by simp

    hence "k > 1"
      using assms z' k *[of z']
      by auto
    hence **: "cor k \<noteq> 0"
      by (smt of_real_eq_0_iff)


    have "of_complex x \<in> poincare_circle z r \<longleftrightarrow> cmod x < 1 \<and> poincare_distance z (of_complex x) = r"
      unfolding poincare_circle_def
      by auto
    also have "... \<longleftrightarrow> cmod x < 1 \<and> poincare_distance_formula' ?z x = cosh r"
      using poincare_distance_formula[of z "of_complex x"] cosh_dist[of z "of_complex x"]
      unfolding poincare_distance_formula_def
      using assms
      using arcosh_cosh_real
      by auto
    also have "... \<longleftrightarrow> cmod x < 1 \<and> ?czx / (?cz * ?cx) = ?R"
      using z'
      by (simp add: field_simps)
    also have "... \<longleftrightarrow> cmod x < 1 \<and> ?czx = ?R * ?cx * ?cz"
      using assms z' *[of z'] *[of x]
      using nonzero_divide_eq_eq[of "(1 - (cmod x)\<^sup>2) * (1 - (cmod z')\<^sup>2)" "(cmod (z' - x))\<^sup>2" ?R]
      by (auto, simp add: field_simps)
    also have "... \<longleftrightarrow> cmod x < 1 \<and> (z' - x) * (cnj z' - cnj x) = R * ?cz * (1 - x * cnj x)" (is "_ \<longleftrightarrow> _ \<and> ?l = ?r")
    proof-
      let ?l = "(z' - x) * (cnj z' - cnj x)" and ?r = "R * (1 - Re (z' * cnj z')) * (1 - x * cnj x)"
      have "is_real ?l"
        using eq_cnj_iff_real[of "?l"]
        by simp
      moreover
      have "is_real ?r"
        using eq_cnj_iff_real[of "1 - x * cnj x"]
        using Im_complex_of_real[of "R * (1 - Re (z' * cnj z'))"]
        by simp
      ultimately
      show ?thesis
        apply (subst R[symmetric])
        apply (subst cmod_square)+
        apply (subst complex_eq_if_Re_eq, simp_all add: field_simps)
        done
    qed
    also have "... \<longleftrightarrow> cmod x < 1 \<and> z' * cnj z' - x * cnj z' - cnj x * z' + x * cnj x = R * ?cz - R * ?cz * x * cnj x"
      unfolding right_diff_distrib left_diff_distrib
      by (simp add: field_simps)
    also have "... \<longleftrightarrow> cmod x < 1 \<and> k * (x * cnj x) - x * cnj z' - cnj x * z' + z' * cnj z' = R * ?cz" (is "_ \<longleftrightarrow> _ \<and> ?lhs = ?rhs")
      by (subst k) (auto simp add: field_simps)
    also have "... \<longleftrightarrow> cmod x < 1 \<and> (k * x * cnj x - x * cnj z' - cnj x * z' + z' * cnj z') / k = (R * ?cz) / k"
      using **
      by (auto simp add: Groups.mult_ac(1))
    also have "... \<longleftrightarrow> cmod x < 1 \<and> x * cnj x - x * cnj z' / k - cnj x * z' / k + z' * cnj z' / k = (R * ?cz) / k"
      using **
      unfolding add_divide_distrib diff_divide_distrib
      by auto
    also have "... \<longleftrightarrow> cmod x < 1 \<and> (x - z'/k) * cnj(x - z'/k) = (R * ?cz) / k + (z' / k) * cnj(z' / k) - z' * cnj z' / k"
      by (auto simp add: field_simps diff_divide_distrib)
    also have "... \<longleftrightarrow> cmod x < 1 \<and> (cmod (x - z'/k))\<^sup>2 = (R * ?cz) / k + (cmod z')\<^sup>2 / k\<^sup>2 - (cmod z')\<^sup>2 / k"
      apply (subst complex_mult_cnj_cmod)+
      apply (subst complex_eq_if_Re_eq)
      apply (simp_all add: power_divide)
      done
    also have "... \<longleftrightarrow> cmod x < 1 \<and> (cmod (x - z'/k))\<^sup>2 = (R * ?cz * k + (cmod z')\<^sup>2 - (cmod z')\<^sup>2 * k) / k\<^sup>2"
      using **
      unfolding add_divide_distrib diff_divide_distrib
      by (simp add: power2_eq_square)
    also have "... \<longleftrightarrow> cmod x < 1 \<and> (cmod (x - z'/k))\<^sup>2 = ?cz\<^sup>2 * R * (R + 1) / k\<^sup>2" (is "_ \<longleftrightarrow> _ \<and> ?a\<^sup>2 = ?b")
    proof-
      have *: "R * (1 - (cmod z')\<^sup>2) * k + (cmod z')\<^sup>2 - (cmod z')\<^sup>2 * k = (1 - (cmod z')\<^sup>2)\<^sup>2 * R * (R + 1)"
        by (subst k)+ (simp add: field_simps power2_diff)
      thus ?thesis
        by (subst *, simp)
    qed
    also have "... \<longleftrightarrow> cmod x < 1 \<and> cmod (x - z'/k) = ?cz * sqrt (R * (R + 1)) / k"
      using \<open>R > 0\<close> *[of z'] ** \<open>k > 1\<close> \<open>z \<in> unit_disc\<close> z'
      using real_sqrt_unique[of ?a ?b, symmetric]
      by (auto simp add: real_sqrt_divide real_sqrt_mult power_divide power_mult_distrib)
    finally
    have "of_complex x \<in> poincare_circle z r \<longleftrightarrow> cmod x < 1 \<and> x \<in> circle (z'/k) (?cz * sqrt(R * (R+1)) / k)"
      unfolding circle_def z' k R
      by simp
    hence "of_complex x \<in> poincare_circle z r \<longleftrightarrow> (let (Ze, Re) = poincare_circle_euclidean z r in cmod x < 1 \<and> x \<in> circle Ze Re)"
      unfolding poincare_circle_euclidean_def Let_def circle_def
      using z' R k
      by (simp add: field_simps)
    hence "of_complex x \<in> poincare_circle z r \<longleftrightarrow> (let (Ze, Re) = poincare_circle_euclidean z r in x \<in> circle Ze Re)"
      using poincare_circle_in_disc[OF \<open>r > 0\<close> \<open>z \<in> unit_disc\<close>]
      by auto
  } note * = this
  show ?thesis
    unfolding Let_def
  proof safe
    fix Ze Re x
    assume "poincare_circle_euclidean z r = (Ze, Re)" "x \<in> circle Ze Re"
    thus "of_complex x \<in> poincare_circle z r"
      using *[of x]
      by simp
  next
    fix Ze Re x
    assume **: "poincare_circle_euclidean z r = (Ze, Re)" "x \<in> poincare_circle z r"
    then obtain x' where x': "x = of_complex x'"
      unfolding poincare_circle_def
      using inf_or_of_complex[of x]
      by auto
    hence "x' \<in> circle Ze Re"
      using *[of x'] **
      by simp
    thus "x \<in> of_complex ` circle Ze Re"
      using x'
      by auto
  qed
qed

subsection \<open>Intersection of circles in special positions\<close>

text \<open>Two h-circles centered at the x-axis intersect at mutually conjugate points\<close>
lemma intersect_poincare_circles_x_axis:
  assumes z: "is_real z1" and "is_real z2" and "r1 > 0" and "r2 > 0" and
             "-1 < Re z1" and "Re z1 < 1" and "-1 < Re z2" and "Re z2 < 1" and
             "z1 \<noteq> z2"
  assumes x1: "x1 \<in> poincare_circle (of_complex z1) r1 \<inter> poincare_circle (of_complex z2) r2" and
          x2: "x2 \<in> poincare_circle (of_complex z1) r1 \<inter> poincare_circle (of_complex z2) r2" and
              "x1 \<noteq> x2"
  shows "x1 = conjugate x2"
proof-
  have in_disc: "of_complex z1 \<in> unit_disc" "of_complex z2 \<in> unit_disc"
    using assms
    by (auto simp add: cmod_eq_Re)

  obtain x1' x2' where x': "x1 = of_complex x1'" "x2 = of_complex x2'"
    using x1 x2
    using inf_or_of_complex[of x1] inf_or_of_complex[of x2]
    unfolding poincare_circle_def
    by auto

  obtain Ze1 Re1 where 1: "(Ze1, Re1) = poincare_circle_euclidean (of_complex z1) r1"
    by (metis poincare_circle_euclidean_def)
  obtain Ze2 Re2 where 2: "(Ze2, Re2) = poincare_circle_euclidean (of_complex z2) r2"
    by (metis poincare_circle_euclidean_def)
  have circle: "x1' \<in> circle Ze1 Re1 \<inter> circle Ze2 Re2"  "x2' \<in> circle Ze1 Re1 \<inter> circle Ze2 Re2"
    using poincare_circle_is_euclidean_circle[of "of_complex z1" r1]
    using poincare_circle_is_euclidean_circle[of "of_complex z2" r2]
    using assms 1 2 \<open>of_complex z1 \<in> unit_disc\<close> \<open>of_complex z2 \<in> unit_disc\<close> x'
    by auto (metis image_iff of_complex_inj)+

  have "is_real Ze1" "is_real Ze2"
    using 1 2 \<open>is_real z1\<close> \<open>is_real z2\<close>
    by (simp_all add: poincare_circle_euclidean_def Let_def)

  have "Re1 > 0" "Re2 > 0"
    using 1 2 in_disc \<open>r1 > 0\<close> \<open>r2 > 0\<close>
    using poincare_circle_in_disc(2)[of r1 "of_complex z1" Ze1 Re1]
    using poincare_circle_in_disc(2)[of r2 "of_complex z2" Ze2 Re2]
    by auto

  have "Ze1 \<noteq> Ze2"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence eq: "Ze1 = Ze2" "Re1 = Re2"
      using circle(1)
      unfolding circle_def
      by auto

    let ?A = "Ze1 - Re1" and ?B = "Ze1 + Re1"
    have "?A \<in> circle Ze1 Re1" "?B \<in> circle Ze1 Re1"
      using \<open>Re1 > 0\<close>
      unfolding circle_def
      by simp_all
    hence "of_complex ?A \<in> poincare_circle (of_complex z1) r1" "of_complex ?B \<in> poincare_circle (of_complex z1) r1"
          "of_complex ?A \<in> poincare_circle (of_complex z2) r2" "of_complex ?B \<in> poincare_circle (of_complex z2) r2"
      using eq
      using poincare_circle_is_euclidean_circle[OF \<open>of_complex z1 \<in> unit_disc\<close> \<open>r1 > 0\<close>]
      using poincare_circle_is_euclidean_circle[OF \<open>of_complex z2 \<in> unit_disc\<close> \<open>r2 > 0\<close>]
      using 1 2
      by auto blast+
    hence "poincare_distance (of_complex z1) (of_complex ?A) = poincare_distance (of_complex z1) (of_complex ?B)"
          "poincare_distance (of_complex z2) (of_complex ?A) = poincare_distance (of_complex z2) (of_complex ?B)"
          "-1 < Re (Ze1 - Re1)" "Re (Ze1 - Re1) < 1" "-1 < Re (Ze1 + Re1)" "Re (Ze1 + Re1) < 1"
      using \<open>is_real Ze1\<close> \<open>is_real Ze2\<close>
      unfolding poincare_circle_def
      by (auto simp add: cmod_eq_Re)
    hence "z1 = z2"
      using unique_midpoint_x_axis[of "Ze1 - Re1" "Ze1 + Re1"]
      using \<open>is_real Ze1\<close> \<open>is_real z1\<close> \<open>is_real z2\<close> \<open>Re1 > 0\<close> \<open>-1 < Re z1\<close> \<open>Re z1 < 1\<close> \<open>-1 < Re z2\<close> \<open>Re z2 < 1\<close>
      by auto
    thus False
      using \<open>z1 \<noteq> z2\<close>
      by simp
  qed

  hence *: "(Re x1')\<^sup>2 + (Im x1')\<^sup>2 - 2 * Re x1' * Ze1 + Ze1 * Ze1 - cor (Re1 * Re1) = 0"
           "(Re x1')\<^sup>2 + (Im x1')\<^sup>2 - 2 * Re x1' * Ze2 + Ze2 * Ze2 - cor (Re2 * Re2) = 0"
           "(Re x2')\<^sup>2 + (Im x2')\<^sup>2 - 2 * Re x2' * Ze1 + Ze1 * Ze1 - cor (Re1 * Re1) = 0"
           "(Re x2')\<^sup>2 + (Im x2')\<^sup>2 - 2 * Re x2' * Ze2 + Ze2 * Ze2 - cor (Re2 * Re2) = 0"
    using circle_equation[of Re1 Ze1] circle_equation[of Re2 Ze2] circle
    using eq_cnj_iff_real[of Ze1] \<open>is_real Ze1\<close> \<open>Re1 > 0\<close>
    using eq_cnj_iff_real[of Ze2] \<open>is_real Ze2\<close> \<open>Re2 > 0\<close>
    using complex_add_cnj[of x1']  complex_add_cnj[of x2']
    using distrib_left[of Ze1 x1' "cnj x1'"] distrib_left[of Ze2 x1' "cnj x1'"]
    using distrib_left[of Ze1 x2' "cnj x2'"] distrib_left[of Ze2 x2' "cnj x2'"]
    by (auto simp add: complex_mult_cnj power2_eq_square field_simps)

  hence "- 2 * Re x1' * Ze1 + Ze1 * Ze1 - cor (Re1 * Re1) = - 2 * Re x1' * Ze2 + Ze2 * Ze2 - cor (Re2 * Re2)"
        "- 2 * Re x2' * Ze1 + Ze1 * Ze1 - cor (Re1 * Re1) = - 2 * Re x2' * Ze2 + Ze2 * Ze2 - cor (Re2 * Re2)"
    by (smt add_diff_cancel_right' add_diff_eq eq_iff_diff_eq_0 minus_diff_eq mult_minus_left of_real_minus)+
  hence "2 * Re x1' * (Ze2 - Ze1) =  (Ze2 * Ze2 - cor (Re2 * Re2)) - (Ze1 * Ze1 - cor (Re1 * Re1))"
        "2 * Re x2' * (Ze2 - Ze1) =  (Ze2 * Ze2 - cor (Re2 * Re2)) - (Ze1 * Ze1 - cor (Re1 * Re1))"
    by simp_all (simp add: field_simps)+
  hence "2 * Re x1' * (Ze2 - Ze1) = 2 * Re x2' * (Ze2 - Ze1)"
    by simp
  hence "Re x1' = Re x2'"
    using \<open>Ze1 \<noteq> Ze2\<close>
    by simp
  moreover
  hence "(Im x1')\<^sup>2 = (Im x2')\<^sup>2"
    using *(1) *(3)
    by (simp add: \<open>is_real Ze1\<close> complex_eq_if_Re_eq)
  hence "Im x1' = Im x2' \<or> Im x1' = -Im x2'"
    using power2_eq_iff
    by blast
  ultimately
  show ?thesis
    using x' `x1 \<noteq> x2`
    using complex.expand
    by (metis cnj.code complex_surj conjugate_of_complex)
qed


text \<open>Two h-circles of the same radius centered at mutually conjugate points intersect at the x-axis\<close>
lemma intersect_poincare_circles_conjugate_centers:
  assumes in_disc: "z1 \<in> unit_disc" "z2 \<in> unit_disc" and 
          "z1 \<noteq> z2" and "z1 = conjugate z2" and "r > 0" and
          u: "u \<in> poincare_circle z1 r \<inter> poincare_circle z2 r"
  shows "is_real (to_complex u)"
proof-
  obtain z1e r1e z2e r2e where
   euclidean: "(z1e, r1e) = poincare_circle_euclidean z1 r"
              "(z2e, r2e) = poincare_circle_euclidean z2 r"
    by (metis poincare_circle_euclidean_def)
  obtain z1' z2' where z': "z1 = of_complex z1'" "z2 = of_complex z2'"
    using inf_or_of_complex[of z1] inf_or_of_complex[of z2] in_disc
    by auto
  obtain u' where u': "u = of_complex u'"
    using u inf_or_of_complex[of u]
    by (auto simp add: poincare_circle_def)
  have "z1' = cnj z2'"
    using \<open>z1 = conjugate z2\<close> z'
    by (auto simp add: of_complex_inj)
  moreover
  let ?cz = "1 - (cmod z2')\<^sup>2"
  let ?den = "?cz * (cosh r - 1) / 2 + 1"
  have "?cz > 0"
    using in_disc z'
    by (simp add: cmod_def)
  hence "?den \<ge> 1"
    using cosh_gt_1[OF \<open>r > 0\<close>]
    by auto
  hence "?den \<noteq> 0"
    by simp
  hence "cor ?den \<noteq> 0"
    using of_real_eq_0_iff
    by blast
  ultimately
  have "r1e = r2e" "z1e = cnj z2e" "z1e \<noteq> z2e"
    using z' euclidean \<open>z1 \<noteq> z2\<close>
    unfolding poincare_circle_euclidean_def Let_def
    by simp_all metis

  hence "u' \<in> circle (cnj z2e) r2e \<inter> circle z2e r2e" "z2e \<noteq> cnj z2e"
    using euclidean u u'
    using poincare_circle_is_euclidean_circle[of z1 r]
    using poincare_circle_is_euclidean_circle[of z2 r]
    using in_disc \<open>r > 0\<close>
    by auto (metis image_iff of_complex_inj)+
  hence "(cmod (u' - z2e))\<^sup>2 = (cmod(u' - cnj z2e))\<^sup>2"
    by (simp add: circle_def)
  hence "(u' - z2e) * (cnj u' - cnj z2e) = (u' - cnj z2e) * (cnj u' - z2e)"
    by (metis complex_cnj_cnj complex_cnj_diff complex_norm_square)
  hence "(z2e - cnj z2e) * (u' - cnj u') = 0"
    by (simp add: field_simps)
  thus ?thesis
    using u' \<open>z2e \<noteq> cnj z2e\<close> eq_cnj_iff_real[of u']
    by simp
qed

subsection \<open>Congruent triangles\<close>

text\<open>For every pair of triangles such that its three pairs of sides are pairwise equal there is an
h-isometry (a unit disc preserving Möbius transform, eventually composed with a conjugation) that
maps one triangle onto the other.\<close>
lemma unit_disc_fix_f_congruent_triangles:
  assumes
    in_disc: "u \<in> unit_disc" "v \<in> unit_disc" "w \<in> unit_disc" and
    in_disc': "u' \<in> unit_disc" "v' \<in> unit_disc" "w' \<in> unit_disc" and 
    d: "poincare_distance u v = poincare_distance u' v'"
       "poincare_distance v w = poincare_distance v' w'"
       "poincare_distance u w = poincare_distance u' w'"
  shows
    "\<exists> M. unit_disc_fix_f M \<and> M u = u' \<and> M v = v' \<and> M w = w'"
proof (cases "u = v \<or> u = w \<or> v = w")
  case True
  thus ?thesis
    using assms
    using poincare_distance_eq_0_iff[of u' v']
    using poincare_distance_eq_0_iff[of v' w']
    using poincare_distance_eq_0_iff[of u' w']
    using poincare_distance_eq_ex_moebius[of v w v' w']
    using poincare_distance_eq_ex_moebius[of u w u' w']
    using poincare_distance_eq_ex_moebius[of u v u' v']
    by (metis unit_disc_fix_f_def)
next
  case False

  have "\<forall> w u' v' w'. w \<in> unit_disc \<and> u' \<in> unit_disc \<and> v' \<in> unit_disc \<and> w' \<in> unit_disc \<and> w \<noteq> u \<and> w \<noteq> v \<and>
    poincare_distance u v = poincare_distance u' v' \<and>
    poincare_distance v w = poincare_distance v' w' \<and>
    poincare_distance u w = poincare_distance u' w' \<longrightarrow>
    (\<exists> M. unit_disc_fix_f M \<and> M u = u' \<and> M v = v' \<and> M w = w')" (is "?P u v")
  proof (rule wlog_positive_x_axis[where P="?P"])
    show "v \<in> unit_disc" "u \<in> unit_disc"
      by fact+
  next
    show "u \<noteq> v"
      using False
      by simp
  next
    fix x
    assume x: "is_real x" "0 < Re x" "Re x < 1"

    hence "of_complex x \<noteq> 0\<^sub>h"
      using of_complex_zero_iff[of x]
      by (auto simp add: complex.expand)

    show "?P 0\<^sub>h (of_complex x)"
    proof safe
      fix w u' v' w'
      assume in_disc: "w \<in> unit_disc" "u' \<in> unit_disc" "v' \<in> unit_disc" "w' \<in> unit_disc"
      assume "poincare_distance 0\<^sub>h (of_complex x) = poincare_distance u' v'"
      then obtain M' where M': "unit_disc_fix M'" "moebius_pt M' u' = 0\<^sub>h" "moebius_pt M' v' = (of_complex x)"
        using poincare_distance_eq_ex_moebius[of u' v' "0\<^sub>h" "of_complex x"] in_disc x
        by (auto simp add: cmod_eq_Re)

      let ?w = "moebius_pt M' w'"
      have "?w \<in> unit_disc"
        using \<open>unit_disc_fix M'\<close> \<open>w' \<in> unit_disc\<close>
        by simp

      assume "w \<noteq> 0\<^sub>h" "w \<noteq> of_complex x"
      hence dist_gt_0: "poincare_distance 0\<^sub>h w > 0" "poincare_distance (of_complex x) w > 0"
        using poincare_distance_eq_0_iff[of "0\<^sub>h" w] in_disc poincare_distance_ge0[of "0\<^sub>h" w]
        using poincare_distance_eq_0_iff[of "of_complex x" w] in_disc poincare_distance_ge0[of "of_complex x" w]
        using x
        by (simp_all add: cmod_eq_Re)

      assume "poincare_distance (of_complex x) w = poincare_distance v' w'"
             "poincare_distance 0\<^sub>h w = poincare_distance u' w'"
      hence "poincare_distance 0\<^sub>h ?w = poincare_distance 0\<^sub>h w"
            "poincare_distance (of_complex x) ?w = poincare_distance (of_complex x) w"
        using M'(1) M'(2)[symmetric] M'(3)[symmetric] in_disc
        using unit_disc_fix_preserve_poincare_distance[of M' u' w']
        using unit_disc_fix_preserve_poincare_distance[of M' v' w']
        by simp_all
      hence "?w \<in> poincare_circle 0\<^sub>h (poincare_distance 0\<^sub>h w) \<inter> poincare_circle (of_complex x) (poincare_distance (of_complex x) w)"
            "w \<in> poincare_circle 0\<^sub>h (poincare_distance 0\<^sub>h w) \<inter> poincare_circle (of_complex x) (poincare_distance (of_complex x) w)"
        using \<open>?w \<in> unit_disc\<close> \<open>w \<in> unit_disc\<close>
        unfolding poincare_circle_def
        by simp_all
      hence "?w = w \<or> ?w = conjugate w"
        using intersect_poincare_circles_x_axis[of 0 x "poincare_distance 0\<^sub>h w" "poincare_distance (of_complex x) w" ?w w] x
        using \<open>of_complex x \<noteq> 0\<^sub>h\<close> dist_gt_0
        using poincare_distance_eq_0_iff
        by auto
      thus "\<exists>M. unit_disc_fix_f M \<and> M 0\<^sub>h = u' \<and> M (of_complex x) = v' \<and> M w = w'"
      proof
        assume "moebius_pt M' w' = w"
        thus ?thesis
          using M'
          using moebius_pt_invert[of M' u' "0\<^sub>h"]
          using moebius_pt_invert[of M' v' "of_complex x"]
          using moebius_pt_invert[of M' w' "w"]
          apply (rule_tac x="moebius_pt (-M')" in exI)
          apply (simp add: unit_disc_fix_f_def)
          apply (rule_tac x="-M'" in exI, simp)
          done
      next
        let ?M = "moebius_pt (-M') \<circ> conjugate"
        assume "moebius_pt M' w' = conjugate w"
        hence "?M w = w'"
          using moebius_pt_invert[of  M' w' "conjugate w"]
          by simp
        moreover
        have "?M 0\<^sub>h = u'" "?M (of_complex x) = v'"
          using moebius_pt_invert[of M' u' "0\<^sub>h"]
          using moebius_pt_invert[of M' v' "of_complex x"]
          using M' \<open>is_real x\<close> eq_cnj_iff_real[of x]
          by simp_all
        moreover
        have "unit_disc_fix_f ?M"
          using \<open>unit_disc_fix M'\<close>
          unfolding unit_disc_fix_f_def
          by (rule_tac x="-M'" in exI, simp)
        ultimately
        show ?thesis
          by blast
      qed
    qed
  next
    fix M u v
    assume 1: "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc"
    let ?Mu = "moebius_pt M u" and ?Mv = "moebius_pt M v"
    assume 2: "?P ?Mu ?Mv"
    show "?P u v"
    proof safe
      fix w u' v' w'
      let ?Mw = "moebius_pt M w" and ?Mu' = "moebius_pt M u'" and ?Mv' = "moebius_pt M v'" and ?Mw' = "moebius_pt M w'"
      assume "w \<in> unit_disc" "u' \<in> unit_disc" "v' \<in> unit_disc" "w' \<in> unit_disc" "w \<noteq> u" "w \<noteq> v"
             "poincare_distance u v = poincare_distance u' v'"
             "poincare_distance v w = poincare_distance v' w'"
             "poincare_distance u w = poincare_distance u' w'"
      then obtain M' where M': "unit_disc_fix_f M'" "M' ?Mu = ?Mu'" "M' ?Mv = ?Mv'" "M' ?Mw = ?Mw'"
        using 1 2[rule_format, of ?Mw ?Mu' ?Mv' ?Mw']
        by auto

      let ?M = "moebius_pt (-M) \<circ> M' \<circ> moebius_pt M"
      show "\<exists>M. unit_disc_fix_f M \<and> M u = u' \<and> M v = v' \<and> M w = w'"
      proof (rule_tac x="?M" in exI, safe)
        show "unit_disc_fix_f ?M"
          using M'(1) \<open>unit_disc_fix M\<close>
          by (subst unit_disc_fix_f_comp, subst unit_disc_fix_f_comp, simp_all)
      next
        show "?M u = u'" "?M v = v'" "?M w = w'"
          using M'
          by auto
      qed
    qed
  qed
  thus ?thesis
    using assms False
    by auto
qed

end