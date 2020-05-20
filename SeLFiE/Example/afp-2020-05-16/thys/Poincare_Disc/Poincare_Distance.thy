theory Poincare_Distance
  imports Poincare_Lines_Ideal_Points Hyperbolic_Functions
begin

(* ------------------------------------------------------------------ *)
section \<open>H-distance in the Poincar\'e model\<close>
(* ------------------------------------------------------------------ *)

text\<open>Informally, the \emph{h-distance} between the two h-points is defined as the absolute value of
the logarithm of the cross ratio between those two points and the two ideal points.\<close>

abbreviation Re_cross_ratio where "Re_cross_ratio z u v w \<equiv> Re (to_complex (cross_ratio z u v w))"

definition calc_poincare_distance :: "complex_homo \<Rightarrow> complex_homo \<Rightarrow> complex_homo \<Rightarrow> complex_homo \<Rightarrow> real" where
  [simp]: "calc_poincare_distance u i1 v i2 = abs (ln (Re_cross_ratio u i1 v i2))"

definition poincare_distance_pred :: "complex_homo \<Rightarrow> complex_homo \<Rightarrow> real \<Rightarrow> bool" where
  [simp]: "poincare_distance_pred u v d \<longleftrightarrow>
            (u = v \<and> d = 0) \<or> (u \<noteq> v \<and> (\<forall> i1 i2. ideal_points (poincare_line u v) = {i1, i2} \<longrightarrow> d = calc_poincare_distance u i1 v i2))"

definition poincare_distance :: "complex_homo \<Rightarrow> complex_homo \<Rightarrow> real" where
  "poincare_distance u v = (THE d. poincare_distance_pred u v d)"

text\<open>We shown that the described cross-ratio is always finite,
positive real number.\<close>
lemma distance_cross_ratio_real_positive:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc" and "u \<noteq> v"
  shows "\<forall> i1 i2. ideal_points (poincare_line u v) = {i1, i2} \<longrightarrow> 
                  cross_ratio u i1 v i2 \<noteq> \<infinity>\<^sub>h \<and> is_real (to_complex (cross_ratio u i1 v i2)) \<and> Re_cross_ratio u i1 v i2 > 0" (is "?P u v")
proof (rule wlog_positive_x_axis[OF assms])
  fix x
  assume *: "is_real x" "0 < Re x" "Re x < 1"
  hence "x \<noteq> -1" "x \<noteq> 1"
    by auto
  hence **: "of_complex x \<noteq> \<infinity>\<^sub>h" "of_complex x \<noteq> 0\<^sub>h" "of_complex x \<noteq> of_complex (-1)" "of_complex 1 \<noteq> of_complex x"
        "of_complex x \<in> circline_set x_axis"
    using *
    unfolding circline_set_x_axis
    by (auto simp add: of_complex_inj)

  have ***:  "0\<^sub>h \<noteq> of_complex (-1)" "0\<^sub>h \<noteq> of_complex 1"
    by (metis of_complex_zero_iff zero_neq_neg_one, simp)

  have ****: "- x - 1 \<noteq> 0" "x - 1 \<noteq> 0"
    using \<open>x \<noteq> -1\<close> \<open>x \<noteq> 1\<close>
    by (metis add.inverse_inverse eq_iff_diff_eq_0, simp)

  have "poincare_line 0\<^sub>h (of_complex x) = x_axis"
    using **
    by (simp add: poincare_line_0_real_is_x_axis)
  thus "?P 0\<^sub>h (of_complex x)"
    using * ** *** ****
    using cross_ratio_not_inf[of "0\<^sub>h" "of_complex 1" "of_complex (-1)" "of_complex x"]
    using cross_ratio_not_inf[of "0\<^sub>h" "of_complex (-1)" "of_complex 1" "of_complex x"]
    using cross_ratio_real[of 0 "-1" x 1] cross_ratio_real[of 0 1 x "-1"]
    apply (auto simp add: poincare_line_0_real_is_x_axis doubleton_eq_iff circline_set_x_axis)
    apply (subst cross_ratio, simp_all, subst Re_complex_div_gt_0, simp, subst mult_neg_neg, simp_all)+
    done
next
  fix M u v
  let ?Mu = "moebius_pt M u" and ?Mv = "moebius_pt M v"
  assume *: "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
            "?P ?Mu ?Mv"
  show "?P u v"
  proof safe
    fix i1 i2
    let ?cr = "cross_ratio u i1 v i2"
    assume **: "ideal_points (poincare_line u v) = {i1, i2}"
    have "i1 \<noteq> u" "i1 \<noteq> v" "i2 \<noteq> u" "i2 \<noteq> v" "i1 \<noteq> i2"
      using ideal_points_different[OF *(2-3), of i1 i2] ** \<open>u \<noteq> v\<close>
      by auto
    hence "0 < Re (to_complex ?cr) \<and> is_real (to_complex ?cr) \<and> ?cr \<noteq> \<infinity>\<^sub>h"
      using * **
      apply (erule_tac x="moebius_pt M i1" in allE)
      apply (erule_tac x="moebius_pt M i2" in allE)
      apply (subst (asm) ideal_points_poincare_line_moebius[of M u v i1 i2], simp_all)
      done
    thus "0 < Re (to_complex ?cr)" "is_real (to_complex ?cr)" "?cr = \<infinity>\<^sub>h \<Longrightarrow> False"
      by simp_all
  qed
qed

text\<open>Next we can show that for every different points from the unit disc there is exactly one number
that satisfies the h-distance predicate.\<close>
lemma distance_unique:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc"
  shows "\<exists>! d. poincare_distance_pred u v d"
proof (cases "u = v")
  case True
  thus ?thesis
    by auto
next
  case False
  obtain i1 i2 where *: "i1 \<noteq> i2" "ideal_points (poincare_line u v) = {i1, i2}"
    using obtain_ideal_points[OF is_poincare_line_poincare_line] \<open>u \<noteq> v\<close>
    by blast
  let ?d = "calc_poincare_distance u i1 v i2"
  show ?thesis
  proof (rule ex1I)
    show "poincare_distance_pred u v ?d"
      using * \<open>u \<noteq> v\<close>
    proof (simp del: calc_poincare_distance_def, safe)
      fix i1' i2'
      assume "{i1, i2} = {i1', i2'}"
      hence **: "(i1' = i1 \<and> i2' = i2) \<or> (i1' = i2 \<and> i2' = i1)"
        using doubleton_eq_iff[of i1 i2 i1' i2']
        by blast
      have all_different: "u \<noteq> i1" "u \<noteq> i2" "v \<noteq> i1" "v \<noteq> i2" "u \<noteq> i1'" "u \<noteq> i2'" "v \<noteq> i1'" "v \<noteq> i2'" "i1 \<noteq> i2"
        using ideal_points_different[OF assms, of i1 i2] * ** \<open>u \<noteq> v\<close>
        by auto

      show "calc_poincare_distance u i1 v i2 = calc_poincare_distance u i1' v i2'"
      proof-
        let ?cr = "cross_ratio u i1 v i2"
        let ?cr' = "cross_ratio u i1' v i2'"

        have "Re (to_complex ?cr) > 0" "is_real (to_complex ?cr)"
             "Re (to_complex ?cr') > 0" "is_real (to_complex ?cr')"
          using False distance_cross_ratio_real_positive[OF assms(1-2)] * **
          by auto

        thus ?thesis
          using **
          using cross_ratio_not_zero cross_ratio_not_inf all_different
          by auto (subst cross_ratio_commute_24, subst reciprocal_real, simp_all add: ln_div)
      qed
    qed
  next
    fix d
    assume "poincare_distance_pred u v d"
    thus "d = ?d"
      using * \<open>u \<noteq> v\<close>
      by auto
  qed
qed

lemma poincare_distance_satisfies_pred [simp]:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc"
  shows "poincare_distance_pred u v (poincare_distance u v)"
    using distance_unique[OF assms] theI'[of "poincare_distance_pred u v"]
    unfolding poincare_distance_def
    by blast

lemma poincare_distance_I:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc" and "u \<noteq> v" and "ideal_points (poincare_line u v) = {i1, i2}"
  shows "poincare_distance u v = calc_poincare_distance u i1 v i2"
  using assms
  using poincare_distance_satisfies_pred[OF assms(1-2)]
  by simp

lemma poincare_distance_refl [simp]:
  assumes "u \<in> unit_disc"
  shows "poincare_distance u u = 0"
  using assms
  using poincare_distance_satisfies_pred[OF assms assms]
  by simp

text\<open>Unit disc preserving Möbius transformations preserve h-distance. \<close>
lemma unit_disc_fix_preserve_poincare_distance [simp]:
  assumes "unit_disc_fix M" and "u \<in> unit_disc" and "v \<in> unit_disc"
  shows "poincare_distance (moebius_pt M u) (moebius_pt M v) = poincare_distance u v"
proof (cases "u = v")
  case True
  have "moebius_pt M u \<in> unit_disc" "moebius_pt M v \<in> unit_disc"
    using unit_disc_fix_iff[OF assms(1), symmetric] assms
    by blast+
  thus ?thesis
    using assms \<open>u = v\<close>
    by simp
next
  case False
  obtain i1 i2 where *: "ideal_points (poincare_line u v) = {i1, i2}"
    using \<open>u \<noteq> v\<close>
    by (rule obtain_ideal_points[OF is_poincare_line_poincare_line[of u v]])
  let ?Mu = "moebius_pt M u" and ?Mv = "moebius_pt M v" and ?Mi1 = "moebius_pt M i1" and ?Mi2 = "moebius_pt M i2"

  have **: "?Mu \<in> unit_disc" "?Mv \<in> unit_disc"
    using assms
    using unit_disc_fix_iff
    by blast+

  have ***: "?Mu \<noteq> ?Mv"   
    using \<open>u \<noteq> v\<close> 
    by simp

  have "poincare_distance u v = calc_poincare_distance u i1 v i2"
    using poincare_distance_I[OF assms(2-3) \<open>u \<noteq> v\<close> *]
    by auto
  moreover
  have "unit_circle_fix M"
    using assms
    by simp
  hence ++: "ideal_points (poincare_line ?Mu ?Mv) = {?Mi1, ?Mi2}"
    using \<open>u \<noteq> v\<close> assms *
    by simp
  have "poincare_distance ?Mu ?Mv = calc_poincare_distance ?Mu ?Mi1 ?Mv ?Mi2"
    by (rule poincare_distance_I[OF ** *** ++])
  moreover
  have "calc_poincare_distance ?Mu ?Mi1 ?Mv ?Mi2 = calc_poincare_distance u i1 v i2"
    using ideal_points_different[OF assms(2-3) \<open>u \<noteq> v\<close> *]
    unfolding calc_poincare_distance_def
    by (subst moebius_preserve_cross_ratio[symmetric], simp_all)
  ultimately
  show ?thesis
    by simp
qed


text\<open>Knowing ideal points for x-axis, we can easily explicitly calculate distances.\<close>
lemma poincare_distance_x_axis_x_axis:
  assumes "x \<in> unit_disc" and "y \<in> unit_disc" and "x \<in> circline_set x_axis" and "y \<in> circline_set x_axis"
  shows "poincare_distance x y =
            (let x' = to_complex x; y' = to_complex y
              in abs (ln (Re (((1 + x') * (1 - y')) / ((1 - x') * (1 + y'))))))"
proof-
  obtain x' y' where *: "x = of_complex x'" "y = of_complex y'"
    using inf_or_of_complex[of x] inf_or_of_complex[of y] \<open>x \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close>
    by auto

  have "cmod x' < 1" "cmod y' < 1"
    using \<open>x \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close> *
    by (metis unit_disc_iff_cmod_lt_1)+
  hence **: "x' \<noteq> 1" "x' \<noteq> 1" "y' \<noteq> -1" "y' \<noteq> 1"
    by auto

  have "1 + y' \<noteq> 0"
    using **
    by (metis add.left_cancel add_neg_numeral_special(7))

  show ?thesis
  proof (cases "x = y")
    case True
    thus ?thesis
      using assms(1-2)
      using unit_disc_iff_cmod_lt_1[of "to_complex x"] * ** `1 + y' \<noteq> 0`
      by auto
      
  next
    case False
    hence "poincare_line x y = x_axis"
      using poincare_line_x_axis[OF assms]
      by simp
    hence "ideal_points (poincare_line x y) = {of_complex (-1), of_complex 1}"
      by simp
    hence "poincare_distance x y = calc_poincare_distance x (of_complex (-1)) y (of_complex 1)"
      using poincare_distance_I assms \<open>x \<noteq> y\<close>
      by auto
    also have "... = abs (ln (Re (((x' + 1) * (y' - 1)) / ((x' - 1) * (y' + 1)))))"
      using * \<open>cmod x' < 1\<close> \<open>cmod y' < 1\<close>
      by (simp, transfer, transfer, auto)
    finally
    show ?thesis
      using *
      by (metis (no_types, lifting) add.commute minus_diff_eq minus_divide_divide mult_minus_left mult_minus_right to_complex_of_complex)
  qed
qed

lemma poincare_distance_zero_x_axis:
  assumes "x \<in> unit_disc" and "x \<in> circline_set x_axis"
  shows "poincare_distance 0\<^sub>h x = (let x' = to_complex x in abs (ln (Re ((1 - x') / (1 + x')))))"
  using assms
  using poincare_distance_x_axis_x_axis[of "0\<^sub>h" x]
  by (simp add: Let_def)

lemma poincare_distance_zero:
  assumes "x \<in> unit_disc"
  shows "poincare_distance 0\<^sub>h x = (let x' = to_complex x in abs (ln (Re ((1 - cmod x') / (1 + cmod x')))))" (is "?P x")
proof (cases "x = 0\<^sub>h")
  case True
  thus ?thesis
    by auto
next
  case False
  show ?thesis
  proof (rule wlog_rotation_to_positive_x_axis)
    show "x \<in> unit_disc" "x \<noteq> 0\<^sub>h" by fact+
  next
    fix \<phi> u
    assume "u \<in> unit_disc" "u \<noteq> 0\<^sub>h" "?P (moebius_pt (moebius_rotation \<phi>) u)"
    thus "?P u"
      using unit_disc_fix_preserve_poincare_distance[of "moebius_rotation \<phi>" "0\<^sub>h" u]
      by (cases "u = \<infinity>\<^sub>h") (simp_all add: Let_def)
  next
    fix x
    assume "is_real x" "0 < Re x" "Re x < 1"
    thus "?P (of_complex x)"
      using poincare_distance_zero_x_axis[of "of_complex x"]
      by simp (auto simp add: circline_set_x_axis cmod_eq_Re complex_is_Real_iff)
  qed
qed

lemma poincare_distance_zero_opposite [simp]:
  assumes "of_complex z \<in> unit_disc"
  shows "poincare_distance 0\<^sub>h (of_complex (- z)) = poincare_distance 0\<^sub>h (of_complex z)"
proof-
  have *: "of_complex (-z) \<in> unit_disc"
    using assms
    by auto
  show ?thesis
    using poincare_distance_zero[OF assms]
    using poincare_distance_zero[OF *]
    by simp
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Distance explicit formula\<close>
(* ------------------------------------------------------------------ *)

text\<open>Instead of the h-distance itself, very frequently its hyperbolic cosine is analyzed.\<close>

abbreviation "cosh_dist u v \<equiv> cosh (poincare_distance u v)"

lemma cosh_poincare_distance_cross_ratio_average:
  assumes "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v" "ideal_points (poincare_line u v) = {i1, i2}"
  shows "cosh_dist u v =
           ((Re_cross_ratio u i1 v i2) + (Re_cross_ratio v i1 u i2)) / 2"
proof-
  let ?cr = "cross_ratio u i1 v i2"
  let ?crRe = "Re (to_complex ?cr)"
  have "?cr \<noteq> \<infinity>\<^sub>h" "is_real (to_complex ?cr)" "?crRe > 0" 
    using distance_cross_ratio_real_positive[OF assms(1-3)] assms(4)
    by simp_all
  then obtain cr where *: "cross_ratio u i1 v i2 = of_complex cr" "cr \<noteq> 0" "is_real cr" "Re cr > 0"
    using inf_or_of_complex[of "cross_ratio u i1 v i2"]
    by (smt to_complex_of_complex zero_complex.simps(1))
  thus ?thesis
    using *
    using assms cross_ratio_commute_13[of v i1 u i2]
    unfolding poincare_distance_I[OF assms] calc_poincare_distance_def cosh_def
    by (cases "Re cr \<ge> 1")
       (auto simp add: ln_div[of 0] exp_minus field_simps Re_divide power2_eq_square complex.expand)
qed

definition poincare_distance_formula' :: "complex \<Rightarrow> complex \<Rightarrow> real" where
[simp]: "poincare_distance_formula' u v = 1 + 2 * ((cmod (u - v))\<^sup>2 / ((1 - (cmod u)\<^sup>2) * (1 - (cmod v)\<^sup>2)))"

text\<open>Next we show that the following formula expresses h-distance between any two h-points (note
that the ideal points do not figure anymore).\<close>

definition poincare_distance_formula :: "complex \<Rightarrow> complex \<Rightarrow> real" where
  [simp]: "poincare_distance_formula u v = arcosh (poincare_distance_formula' u v)"

lemma blaschke_preserve_distance_formula [simp]:
  assumes "of_complex k \<in> unit_disc" "u \<in> unit_disc" "v \<in> unit_disc"
  shows "poincare_distance_formula (to_complex (moebius_pt (blaschke k) u)) (to_complex (moebius_pt (blaschke k) v)) =
         poincare_distance_formula (to_complex u) (to_complex v)"
proof (cases "k = 0")
  case True
  thus ?thesis
    by simp
next
  case False
  obtain u' v' where *: "u' = to_complex u" "v' = to_complex v"
    by auto

  have "cmod u' < 1" "cmod v' < 1" "cmod k < 1"
    using assms *
    using inf_or_of_complex[of u] inf_or_of_complex[of v]
    by auto

  obtain nu du nv dv d kk ddu ddv where
    **: "nu = u' - k" "du = 1 - cnj k *u'" "nv = v' - k" "dv = 1 - cnj k * v'"
        "d = u' - v'" "ddu = 1 - u'*cnj u'" "ddv = 1 - v'*cnj v'" "kk = 1 - k*cnj k"
    by auto

  have d: "nu*dv - nv*du = d*kk"                          
    by (subst **)+ (simp add: field_simps)
  have ddu: "du*cnj du - nu*cnj nu = ddu*kk"
    by (subst **)+ (simp add: field_simps)
  have ddv: "dv*cnj dv - nv*cnj nv = ddv*kk"
    by (subst **)+ (simp add: field_simps)

  have "du \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "cmod (1 - cnj k * u') = 0"
      using \<open>du = 1 - cnj k * u'\<close>
      by auto
    hence "cmod (cnj k * u') = 1"
      by auto
    hence "cmod k * cmod u' = 1"
      by auto
    thus False
      using \<open>cmod k < 1\<close> \<open>cmod u' < 1\<close>
      using mult_strict_mono[of "cmod k" 1 "cmod u'" 1]
      by simp
  qed

  have "dv \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "cmod (1 - cnj k * v') = 0"
      using \<open>dv = 1 - cnj k * v'\<close>
      by auto
    hence "cmod (cnj k * v') = 1"
      by auto
    hence "cmod k * cmod v' = 1"
      by auto
    thus False
      using \<open>cmod k < 1\<close> \<open>cmod v' < 1\<close>
      using mult_strict_mono[of "cmod k" 1 "cmod v'" 1]
      by simp
  qed

  have "kk \<noteq> 0" 
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "cmod (1 - k * cnj k) = 0"
      using \<open>kk = 1 - k * cnj k\<close>
      by auto
    hence "cmod (k * cnj k) = 1"
      by auto
    hence "cmod k * cmod k = 1"
      by auto
    thus False
      using \<open>cmod k < 1\<close>
      using mult_strict_mono[of "cmod k" 1 "cmod k" 1]
      by simp
  qed

  note nz = \<open>du \<noteq> 0\<close> \<open>dv \<noteq> 0\<close> \<open>kk \<noteq> 0\<close>


  have "nu / du - nv / dv = (nu*dv - nv*du) / (du * dv)"              
    using nz
    by (simp add: field_simps)                               
  hence "(cmod (nu/du - nv/dv))\<^sup>2 = cmod ((d*kk) / (du*dv) * (cnj ((d*kk) / (du*dv))))" (is "?lhs = _")
    unfolding complex_mod_mult_cnj[symmetric]
    by (subst (asm) d) simp
  also have "... = cmod ((d*cnj d*kk*kk) / (du*cnj du*dv*cnj dv))"
    by (simp add: field_simps)
  finally have 1: "?lhs = cmod ((d*cnj d*kk*kk) / (du*cnj du*dv*cnj dv))"
    .                                                                           

  have "(1 - ((cmod nu) / (cmod du))\<^sup>2)*(1 - ((cmod nv) / (cmod dv))\<^sup>2) =
        (1 - cmod((nu * cnj nu) / (du * cnj du)))*(1 - cmod((nv * cnj nv) / (dv * cnj dv)))" (is "?rhs = _")
    by (metis cmod_divide complex_mod_mult_cnj power_divide)
  also have "... = cmod(((du*cnj du - nu*cnj nu) / (du * cnj du)) * ((dv*cnj dv - nv*cnj nv) / (dv * cnj dv)))"
  proof-
    have "u' \<noteq> 1 / cnj k" "v' \<noteq> 1 / cnj k"
      using \<open>cmod u' < 1\<close> \<open>cmod v' < 1\<close> \<open>cmod k < 1\<close>
      by (auto simp add: False)
    moreover
    have "cmod k \<noteq> 1"
      using \<open>cmod k < 1\<close>
      by linarith
    ultimately
    have "cmod (nu/du) < 1" "cmod (nv/dv) < 1"
      using **(1-4)
      using unit_disc_fix_discI[OF blaschke_unit_disc_fix[OF \<open>cmod k < 1\<close>] \<open>u \<in> unit_disc\<close>] \<open>u' = to_complex u\<close>
      using unit_disc_fix_discI[OF blaschke_unit_disc_fix[OF \<open>cmod k < 1\<close>] \<open>v \<in> unit_disc\<close>] \<open>v' = to_complex v\<close>
      using inf_or_of_complex[of u] \<open>u \<in> unit_disc\<close> inf_or_of_complex[of v] \<open>v \<in> unit_disc\<close>
      using moebius_pt_blaschke[of k u'] using moebius_pt_blaschke[of k v'] 
      by auto
    hence "(cmod (nu/du))\<^sup>2 < 1" "(cmod (nv/dv))\<^sup>2 < 1"
      by (simp_all add: cmod_def)
    hence "cmod (nu * cnj nu / (du * cnj du)) < 1"  "cmod (nv * cnj nv / (dv * cnj dv)) < 1"
      by (metis complex_mod_mult_cnj norm_divide power_divide)+
    moreover
    have "is_real (nu * cnj nu / (du * cnj du))" "is_real (nv * cnj nv / (dv * cnj dv))"
      using eq_cnj_iff_real[of "nu * cnj nu / (du * cnj du)"]      
      using eq_cnj_iff_real[of "nv * cnj nv / (dv * cnj dv)"]      
      by (auto simp add: mult.commute)
    moreover          
    have "Re (nu * cnj nu / (du * cnj du)) \<ge> 0"  "Re (nv * cnj nv / (dv * cnj dv)) \<ge> 0"
      using \<open>du \<noteq> 0\<close> \<open>dv \<noteq> 0\<close>
      unfolding complex_mult_cnj_cmod
      by simp_all
    ultimately                           
    have "1 - cmod (nu * cnj nu / (du * cnj du)) = cmod (1 - nu * cnj nu / (du * cnj du))"
         "1 - cmod (nv * cnj nv / (dv * cnj dv)) = cmod (1 - nv * cnj nv / (dv * cnj dv))"     
      by (simp_all add: cmod_def)
    thus ?thesis
      using nz
      apply simp
      apply (subst diff_divide_eq_iff, simp, simp)
      apply (subst diff_divide_eq_iff, simp, simp)
      done
  qed    
  also have "... = cmod(((ddu * kk) / (du * cnj du)) * ((ddv * kk) / (dv * cnj dv)))"
    by (subst ddu, subst ddv, simp)
  also have "... = cmod((ddu*ddv*kk*kk) / (du*cnj du*dv*cnj dv))"
    by (simp add: field_simps)
  finally have 2: "?rhs = cmod((ddu*ddv*kk*kk) / (du*cnj du*dv*cnj dv))"
    .

  have "?lhs / ?rhs =
       cmod ((d*cnj d*kk*kk) / (du*cnj du*dv*cnj dv)) / cmod((ddu*ddv*kk*kk) / (du*cnj du*dv*cnj dv))"
    by (subst 1, subst 2, simp)
  also have "... = cmod ((d*cnj d)/(ddu*ddv))"
    using nz
    by simp
  also have "... = (cmod d)\<^sup>2 / ((1 - (cmod u')\<^sup>2)*(1 - (cmod v')\<^sup>2))"
  proof-
    have "(cmod u')\<^sup>2 < 1" "(cmod v')\<^sup>2 < 1"
      using \<open>cmod u' < 1\<close> \<open>cmod v' < 1\<close>
      by (simp_all add: cmod_def)
    hence "cmod (1 - u' * cnj u') = 1 - (cmod u')\<^sup>2" "cmod (1 - v' * cnj v') = 1 - (cmod v')\<^sup>2"
      by (auto simp add: cmod_eq_Re cmod_power2 power2_eq_square[symmetric])
    thus ?thesis
      using nz
      apply (subst **)+
      unfolding complex_mod_mult_cnj[symmetric]      
      by simp
  qed
  finally
  have 3: "?lhs / ?rhs = (cmod d)\<^sup>2 / ((1 - (cmod u')\<^sup>2)*(1 - (cmod v')\<^sup>2))"
    .

  have "cmod k \<noteq> 1" "u' \<noteq> 1 / cnj k" "v' \<noteq> 1 / cnj k" "u \<noteq> \<infinity>\<^sub>h" "v \<noteq> \<infinity>\<^sub>h"
    using \<open>cmod k < 1\<close> \<open>u \<in> unit_disc\<close> \<open>v \<in> unit_disc\<close> * \<open>k \<noteq> 0\<close> ** \<open>kk \<noteq> 0\<close> nz
    by auto
  thus ?thesis using assms
    using * ** 3
    using moebius_pt_blaschke[of k u']
    using moebius_pt_blaschke[of k v']
    by simp
qed

text \<open>To prove the equivalence between the h-distance definition and the distance formula, we shall
employ the without loss of generality principle. Therefore, we must show that the distance formula
is preserved by h-isometries.\<close>

text\<open>Rotation preserve @{term poincare_distance_formula}.\<close>
lemma rotation_preserve_distance_formula [simp]:
  assumes "u \<in> unit_disc" "v \<in> unit_disc"
  shows "poincare_distance_formula (to_complex (moebius_pt (moebius_rotation \<phi>) u)) (to_complex (moebius_pt (moebius_rotation \<phi>) v)) =
         poincare_distance_formula (to_complex u) (to_complex v)"
  using assms
  using inf_or_of_complex[of u] inf_or_of_complex[of v]
  by auto

text\<open>Unit disc fixing Möbius preserve @{term poincare_distance_formula}.\<close>
lemma unit_disc_fix_preserve_distance_formula [simp]:
  assumes "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc"
  shows "poincare_distance_formula (to_complex (moebius_pt M u)) (to_complex (moebius_pt M v)) =
         poincare_distance_formula (to_complex u) (to_complex v)" (is "?P' u v M")
proof-
  have "\<forall> u \<in> unit_disc. \<forall> v \<in> unit_disc. ?P' u v M" (is "?P M")
  proof (rule wlog_unit_disc_fix[OF assms(1)])
    fix k
    assume "cmod k < 1"
    hence "of_complex k \<in> unit_disc"
      by simp
    thus  "?P (blaschke k)"
      using blaschke_preserve_distance_formula
      by simp
  next
    fix \<phi>
    show "?P (moebius_rotation \<phi>)"
      using rotation_preserve_distance_formula
      by simp
  next
    fix M1 M2
    assume *: "?P M1" and **: "?P M2"  and u11: "unit_disc_fix M1" "unit_disc_fix M2"
    thus "?P (M1 + M2)"
      by (auto simp del: poincare_distance_formula_def)
  qed
  thus ?thesis
    using assms
    by simp
qed

text\<open>The equivalence between the two h-distance representations.\<close>
lemma poincare_distance_formula:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc"
  shows "poincare_distance u v = poincare_distance_formula (to_complex u) (to_complex v)" (is "?P u v")
proof (rule wlog_x_axis)
  fix x
  assume *: "is_real x" "0 \<le> Re x" "Re x < 1"
  show "?P  0\<^sub>h (of_complex x)" (is "?lhs = ?rhs")
  proof-
    have "of_complex x \<in> unit_disc" "of_complex x \<in> circline_set x_axis" "cmod x < 1"
      using * cmod_eq_Re
      by (auto simp add: circline_set_x_axis)
    hence "?lhs = \<bar>ln (Re ((1 - x) / (1 + x)))\<bar>"
      using poincare_distance_zero_x_axis[of "of_complex x"]
      by simp
    moreover
    have "?rhs = \<bar>ln (Re ((1 - x) / (1 + x)))\<bar>"
    proof-
      let ?x = "1 + 2 * (cmod x)\<^sup>2 / (1 - (cmod x)\<^sup>2)"
      have "0 \<le> 2 * (cmod x)\<^sup>2 / (1 - (cmod x)\<^sup>2)"
        by (smt \<open>cmod x < 1\<close> divide_nonneg_nonneg norm_ge_zero power_le_one zero_le_power2)
      hence arcosh_real_gt: "1 \<le> ?x"
        by auto
      have "?rhs = arcosh ?x"
        by simp
      also have "... = ln ((1 + (cmod x)\<^sup>2) / (1 - (cmod x)\<^sup>2) + 2 * (cmod x) / (1 - (cmod x)\<^sup>2))"
      proof-
        have "1 - (cmod x)\<^sup>2 > 0"
          using \<open>cmod x < 1\<close>
          by (smt norm_not_less_zero one_power2 power2_eq_imp_eq power_mono)
        hence 1: "?x = (1 + (cmod x)\<^sup>2) / (1 - (cmod x)\<^sup>2)"
          by (simp add: field_simps)
        have 2: "?x\<^sup>2 - 1 = (4 * (cmod x)\<^sup>2) / (1 - (cmod x)\<^sup>2)\<^sup>2"
          using \<open>1 - (cmod x)\<^sup>2 > 0\<close>       
          apply (subst 1)
          unfolding power_divide
          by (subst divide_diff_eq_iff, simp, simp add: power2_eq_square field_simps)
        show ?thesis
          using \<open>1 - (cmod x)\<^sup>2 > 0\<close>
          apply (subst arcosh_real_def[OF arcosh_real_gt])
          apply (subst 2)
          apply (subst 1)
          apply (subst real_sqrt_divide)
          apply (subst real_sqrt_mult)
          apply simp
          done
      qed
      also have "... = ln (((1 + (cmod x))\<^sup>2) / (1 - (cmod x)\<^sup>2))"
        apply (subst add_divide_distrib[symmetric])
        apply (simp add: field_simps power2_eq_square)
        done
      also have "... = ln ((1 + cmod x) / (1 - (cmod x)))"
        using \<open>cmod x < 1\<close>      
        using square_diff_square_factored[of 1 "cmod x"]
        by (simp add: power2_eq_square)
      also have "... = \<bar>ln (Re ((1 - x) / (1 + x)))\<bar>"
      proof-
        have *: "Re ((1 - x) / (1 + x)) \<le> 1" "Re ((1 - x) / (1 + x)) > 0"
          using \<open>is_real x\<close> \<open>Re x \<ge> 0\<close> \<open>Re x < 1\<close>
          using complex_is_Real_iff
          by auto
        hence "\<bar>ln (Re ((1 - x) / (1 + x)))\<bar> = - ln (Re ((1 - x) / (1 + x)))"
          by auto
        hence "\<bar>ln (Re ((1 - x) / (1 + x)))\<bar> = ln (Re ((1 + x) / (1 - x)))"
          using ln_div[of 1 "Re ((1 - x)/(1 + x))"] * \<open>is_real x\<close>
          by (simp add: complex_is_Real_iff)
        moreover
        have "ln ((1 + cmod x) / (1 - cmod x)) = ln ((1 + Re x) / (1 - Re x))"
          using \<open>Re x \<ge> 0\<close> \<open>is_real x\<close>
          using cmod_eq_Re by auto
        moreover
        have "(1 + Re x) / (1 - Re x) = Re ((1 + x) / (1 - x))"
          using \<open>is_real x\<close> \<open>Re x < 1\<close>
          by (smt Re_divide_real eq_iff_diff_eq_0 minus_complex.simps one_complex.simps plus_complex.simps)
        ultimately
        show ?thesis
          by simp
      qed
      finally
      show ?thesis
        .
    qed
    ultimately
    show ?thesis
      by simp
  qed
next
  fix M u v
  assume *: "unit_disc_fix M"  "u \<in> unit_disc" "v \<in> unit_disc"
  assume "?P (moebius_pt M u) (moebius_pt M v)"
  thus "?P u v"
    using *(1-3)
    by (simp del: poincare_distance_formula_def)
next
  show "u \<in> unit_disc" "v \<in> unit_disc"
    by fact+
qed

text\<open>Some additional properties proved easily using the distance formula.\<close>


text \<open>@{term poincare_distance} is symmetric.\<close>
lemma poincare_distance_sym:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc"
  shows "poincare_distance u v = poincare_distance v u"
  using assms
  using poincare_distance_formula[OF assms(1) assms(2)]
  using poincare_distance_formula[OF assms(2) assms(1)]
  by (simp add: mult.commute norm_minus_commute)

lemma poincare_distance_formula'_ge_1:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc"
  shows "1 \<le> poincare_distance_formula' (to_complex u) (to_complex v)"
  using unit_disc_cmod_square_lt_1[OF assms(1)] unit_disc_cmod_square_lt_1[OF assms(2)]
  by auto

text\<open>@{term poincare_distance} is non-negative.\<close>
lemma poincare_distance_ge0:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc"
  shows "poincare_distance u v \<ge> 0"
  using poincare_distance_formula'_ge_1
  unfolding poincare_distance_formula[OF assms(1) assms(2)]
  unfolding poincare_distance_formula_def
  unfolding poincare_distance_formula'_def
  by (rule arcosh_ge_0, simp_all add: assms)

lemma cosh_dist:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc"
  shows "cosh_dist u v = poincare_distance_formula' (to_complex u) (to_complex v)"
  using poincare_distance_formula[OF assms] poincare_distance_formula'_ge_1[OF assms]
  by simp

text\<open>@{term poincare_distance}  is zero only if the two points are equal.\<close>
lemma poincare_distance_eq_0_iff:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc"
  shows "poincare_distance u v = 0 \<longleftrightarrow> u = v"
  using assms
  apply auto
  using poincare_distance_formula'_ge_1[OF assms]
  using unit_disc_cmod_square_lt_1[OF assms(1)] unit_disc_cmod_square_lt_1[OF assms(2)]
  unfolding poincare_distance_formula[OF assms(1) assms(2)]
  unfolding poincare_distance_formula_def
  unfolding poincare_distance_formula'_def
  apply (subst (asm) arcosh_eq_0_iff)
  apply assumption
  apply (simp add: unit_disc_to_complex_inj)
  done

text\<open>Conjugate preserve @{term poincare_distance_formula}.\<close>
lemma conjugate_preserve_poincare_distance [simp]:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc"
  shows "poincare_distance (conjugate u) (conjugate v) = poincare_distance u v"
proof-
  obtain u' v' where *: "u = of_complex u'" "v = of_complex v'"
    using assms inf_or_of_complex[of u] inf_or_of_complex[of v]
    by auto

  have **: "conjugate u \<in> unit_disc" "conjugate v \<in> unit_disc"
    using * assms
    by auto

  show ?thesis
    using *
    using poincare_distance_formula[OF assms]
    using poincare_distance_formula[OF **]
    by (metis complex_cnj_diff complex_mod_cnj conjugate_of_complex poincare_distance_def poincare_distance_formula'_def poincare_distance_formula_def to_complex_of_complex)
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Existence and uniqueness of points with a given distance\<close>
(* ------------------------------------------------------------------ *)

lemma ex_x_axis_poincare_distance_negative':
  fixes d :: real
  assumes "d \<ge> 0"
  shows "let z = (1 - exp d) / (1 + exp d)
          in is_real z \<and> Re z \<le> 0 \<and> Re z > -1 \<and>
              of_complex z \<in> unit_disc \<and> of_complex z \<in> circline_set x_axis \<and>
              poincare_distance 0\<^sub>h (of_complex z) = d"
proof-
  have "exp d \<ge> 1"
    using assms
    using one_le_exp_iff[of d, symmetric]
    by blast

  hence "1 + exp d \<noteq> 0"
    by linarith

  let ?z = "(1 - exp d) / (1 + exp d)"

  have "?z \<le> 0"
    using \<open>exp d \<ge> 1\<close>
    by (simp add: divide_nonpos_nonneg)

  moreover

  have "?z > -1"
    using exp_gt_zero[of d]
    by (smt divide_less_eq_1_neg nonzero_minus_divide_right)

  moreover

  hence "abs ?z < 1"
    using \<open>?z \<le> 0\<close>
    by simp
  hence "cmod ?z < 1"
    by (metis norm_of_real)
  hence "of_complex ?z \<in> unit_disc"
    by simp

  moreover
  have "of_complex ?z \<in> circline_set x_axis"
    unfolding circline_set_x_axis
    by simp

  moreover
  have "(1 - ?z) / (1 + ?z) = exp d"
  proof-
    have "1 + ?z = 2 / (1 + exp d)"
      using \<open>1 + exp d \<noteq> 0\<close>
      by (subst add_divide_eq_iff, auto)
    moreover
    have "1 - ?z = 2 * exp d / (1 + exp d)"
      using \<open>1 + exp d \<noteq> 0\<close>
      by (subst diff_divide_eq_iff, auto)
    ultimately
    show ?thesis
      using \<open>1 + exp d \<noteq> 0\<close>
      by simp
  qed

  ultimately
  show ?thesis
    using poincare_distance_zero_x_axis[of "of_complex ?z"]
    using \<open>d \<ge> 0\<close> \<open>exp d \<ge> 1\<close>
    by simp (simp add: cmod_eq_Re)
qed

lemma ex_x_axis_poincare_distance_negative:
  assumes "d \<ge> 0"
  shows "\<exists> z. is_real z \<and> Re z \<le> 0 \<and> Re z > -1 \<and>
              of_complex z \<in> unit_disc \<and> of_complex z \<in> circline_set x_axis \<and>
              poincare_distance 0\<^sub>h (of_complex z) = d" (is "\<exists> z. ?P z")
  using ex_x_axis_poincare_distance_negative'[OF assms]
  unfolding Let_def
  by blast

text\<open>For each real number $d$ there is exactly one point on the positive x-axis such that h-distance
between 0 and that point is $d$.\<close>
lemma unique_x_axis_poincare_distance_negative:
  assumes "d \<ge> 0"
  shows "\<exists>! z. is_real z \<and> Re z \<le> 0 \<and> Re z > -1 \<and>
              poincare_distance 0\<^sub>h (of_complex z) = d" (is "\<exists>! z. ?P z")
proof-
  let ?z = "(1 - exp d) / (1 + exp d)"

  have "?P ?z"
    using ex_x_axis_poincare_distance_negative'[OF assms]
    unfolding Let_def
    by blast

  moreover

  have "\<forall> z'. ?P z' \<longrightarrow> z' = ?z"
  proof-
    let ?g = "\<lambda> x'. \<bar>ln (Re ((1 - x') / (1 + x')))\<bar>"
    let ?A = "{x. is_real x \<and> Re x > -1 \<and> Re x \<le> 0}"
    have "inj_on (poincare_distance 0\<^sub>h \<circ> of_complex) ?A"
    proof (rule comp_inj_on)
      show "inj_on of_complex ?A"
        using of_complex_inj
        unfolding inj_on_def
        by blast
    next
      show "inj_on (poincare_distance 0\<^sub>h) (of_complex ` ?A)" (is "inj_on ?f (of_complex ` ?A)")
      proof (subst inj_on_cong)
        have *: "of_complex ` ?A =
                 {z. z \<in> unit_disc \<and> z \<in> circline_set x_axis \<and> Re (to_complex z) \<le> 0}" (is "_ = ?B")
          by (auto simp add: cmod_eq_Re circline_set_x_axis)

        fix x
        assume "x \<in> of_complex ` ?A"
        hence "x \<in> ?B"
          using *
          by simp
        thus "poincare_distance 0\<^sub>h x = (?g \<circ> to_complex) x"
          using poincare_distance_zero_x_axis
          by (simp add: Let_def)
      next
        have *: "to_complex ` of_complex ` ?A = ?A"
          by (auto simp add: image_iff)

        show "inj_on (?g \<circ> to_complex) (of_complex ` ?A)"
        proof (rule comp_inj_on)
          show "inj_on to_complex (of_complex ` ?A)"
            unfolding inj_on_def
            by auto
        next
          have "inj_on ?g ?A"
            unfolding inj_on_def
          proof(safe)
            fix x y
            assume hh: "is_real x" "is_real y" "- 1 < Re x" "Re x \<le> 0"
              "- 1 < Re y" "Re y \<le> 0" "\<bar>ln (Re ((1 - x) / (1 + x)))\<bar> = \<bar>ln (Re ((1 - y) / (1 + y)))\<bar>"

            have "is_real ((1 - x)/(1 + x))"
              using \<open>is_real x\<close> div_reals[of "1-x" "1+x"]
              by auto
            have "is_real ((1 - y)/(1 + y))"
              using \<open>is_real y\<close> div_reals[of "1-y" "1+y"]
              by auto

            have "Re (1 + x) > 0"
              using \<open>- 1 < Re x\<close> by auto
            hence "1 + x \<noteq> 0"
              by force
            have "Re (1 - x) \<ge> 0"
              using \<open>Re x \<le> 0\<close> by auto
            hence "Re ((1 - x)/(1 + x)) > 0"
              using Re_divide_real \<open>0 < Re (1 + x)\<close> complex_eq_if_Re_eq hh(1) hh(4) by auto
            have "Re(1 - x) \<ge> Re ( 1 + x)"
              using hh by auto
            hence "Re ((1 - x)/(1 + x)) \<ge> 1"
              using \<open>Re (1 + x) > 0\<close> \<open>is_real ((1 - x)/(1 + x))\<close>
              by (smt Re_divide_real arg_0_iff hh(1) le_divide_eq_1_pos one_complex.simps(2) plus_complex.simps(2))            

            have "Re (1 + y) > 0"
              using \<open>- 1 < Re y\<close> by auto
            hence "1 + y \<noteq> 0"
              by force
            have "Re (1 - y) \<ge> 0"
              using \<open>Re y \<le> 0\<close> by auto
            hence "Re ((1 - y)/(1 + y)) > 0"
              using Re_divide_real \<open>0 < Re (1 + y)\<close> complex_eq_if_Re_eq hh by auto
            have "Re(1 - y) \<ge> Re ( 1 + y)"
              using hh by auto
            hence "Re ((1 - y)/(1 + y)) \<ge> 1"
              using \<open>Re (1 + y) > 0\<close> \<open>is_real ((1 - y)/(1 + y))\<close>
              by (smt Re_divide_real arg_0_iff hh le_divide_eq_1_pos one_complex.simps(2) plus_complex.simps(2))

            have "ln (Re ((1 - x) / (1 + x))) = ln (Re ((1 - y) / (1 + y)))"
              using \<open>Re ((1 - y)/(1 + y)) \<ge> 1\<close> \<open>Re ((1 - x)/(1 + x)) \<ge> 1\<close> hh
              by auto
            hence "Re ((1 - x) / (1 + x)) = Re ((1 - y) / (1 + y))"
              using \<open>Re ((1 - y)/(1 + y)) > 0\<close> \<open>Re ((1 - x)/(1 + x)) > 0\<close>
              by auto
            hence "(1 - x) / (1 + x) = (1 - y) / (1 + y)"
              using \<open>is_real ((1 - y)/(1 + y))\<close> \<open>is_real ((1 - x)/(1 + x))\<close>
              using complex_eq_if_Re_eq by blast
            hence "(1 - x) * (1 + y) = (1 - y) * (1 + x)"
              using \<open>1 + y \<noteq> 0\<close> \<open>1 + x \<noteq> 0\<close> 
              by (simp add:field_simps)
            thus "x = y"
              by (simp add:field_simps)
          qed            
          thus "inj_on ?g (to_complex ` of_complex ` ?A)"
            using *
            by simp
        qed
      qed
    qed
    thus ?thesis
      using \<open>?P ?z\<close>
      unfolding inj_on_def
      by auto
  qed
  ultimately
  show ?thesis
    by blast
qed

lemma ex_x_axis_poincare_distance_positive:
  assumes "d \<ge> 0"
  shows "\<exists> z. is_real z \<and> Re z \<ge> 0 \<and> Re z < 1 \<and>
              of_complex z \<in> unit_disc \<and> of_complex z \<in> circline_set x_axis \<and>
              poincare_distance 0\<^sub>h (of_complex z) = d" (is "\<exists> z. is_real z \<and> Re z \<ge> 0 \<and> Re z < 1 \<and> ?P z")
proof-
  obtain z where *: "is_real z" "Re z \<le> 0" "Re z > -1" "?P z"
    using ex_x_axis_poincare_distance_negative[OF assms]
    by auto
  hence **: "of_complex z \<in> unit_disc" "of_complex z \<in> circline_set x_axis"
    by (auto simp add: cmod_eq_Re)
  have "is_real (-z) \<and> Re (-z) \<ge> 0 \<and> Re (-z) < 1 \<and> ?P (-z)"
    using * **
    by (simp add: circline_set_x_axis)
  thus ?thesis
    by blast
qed

lemma unique_x_axis_poincare_distance_positive:
  assumes "d \<ge> 0"
  shows "\<exists>! z. is_real z \<and> Re z \<ge> 0 \<and> Re z < 1 \<and>
               poincare_distance 0\<^sub>h (of_complex z) = d" (is "\<exists>! z. is_real z \<and> Re z \<ge> 0 \<and> Re z < 1 \<and> ?P z")
proof-
  obtain z where *: "is_real z" "Re z \<le> 0" "Re z > -1" "?P z"
    using unique_x_axis_poincare_distance_negative[OF assms]
    by auto
  hence **: "of_complex z \<in> unit_disc" "of_complex z \<in> circline_set x_axis"
    by (auto simp add: cmod_eq_Re circline_set_x_axis)
  show ?thesis
  proof
    show "is_real (-z) \<and> Re (-z) \<ge> 0 \<and> Re (-z) < 1 \<and> ?P (-z)"
      using * **
      by simp
  next
    fix z'
    assume "is_real z' \<and> Re z' \<ge> 0 \<and> Re z' < 1 \<and> ?P z'"
    hence "is_real (-z') \<and> Re (-z') \<le> 0 \<and> Re (-z') > -1 \<and> ?P (-z')"
      by (auto simp add: circline_set_x_axis cmod_eq_Re)
    hence "-z' = z"
      using unique_x_axis_poincare_distance_negative[OF assms] *
      by blast
    thus "z' = -z"
      by auto
  qed
qed

text\<open>Equal distance implies that segments are isometric - this means that congruence could be
defined either by two segments having the same distance or by requiring existence of an isometry
that maps one segment to the other.\<close>
lemma poincare_distance_eq_ex_moebius:
  assumes in_disc: "u \<in> unit_disc" and "v \<in> unit_disc" and "u' \<in> unit_disc" and "v' \<in> unit_disc"
  assumes "poincare_distance u v = poincare_distance u' v'"
  shows "\<exists> M. unit_disc_fix M \<and> moebius_pt M u = u' \<and> moebius_pt M v = v'" (is "?P' u v u' v'")
proof (cases "u = v")
  case True
  thus ?thesis
    using assms poincare_distance_eq_0_iff[of u' v']
    by (simp add: unit_disc_fix_transitive)
next
  case False
  have "\<forall> u' v'. u \<noteq> v \<and> u' \<in> unit_disc \<and> v' \<in> unit_disc \<and> poincare_distance u v = poincare_distance u' v' \<longrightarrow>
                 ?P' u' v' u v" (is "?P u v")
  proof (rule wlog_positive_x_axis[where P="?P"])
    fix x
    assume "is_real x" "0 < Re x" "Re x < 1"
    hence "of_complex x \<in> unit_disc" "of_complex x \<in> circline_set x_axis"
      unfolding circline_set_x_axis
      by (auto simp add: cmod_eq_Re)

    show "?P 0\<^sub>h (of_complex x)"
    proof safe
      fix u' v'
      assume "0\<^sub>h \<noteq> of_complex x" and in_disc: "u' \<in> unit_disc" "v' \<in> unit_disc" and
             "poincare_distance 0\<^sub>h (of_complex x) = poincare_distance u' v'"
      hence "u' \<noteq> v'" "poincare_distance u' v' > 0"
        using poincare_distance_eq_0_iff[of "0\<^sub>h" "of_complex x"] \<open>of_complex x \<in> unit_disc\<close>
        using poincare_distance_ge0[of "0\<^sub>h" "of_complex x"]
        by auto
      then obtain M where M: "unit_disc_fix M" "moebius_pt M u' = 0\<^sub>h" "moebius_pt M v' \<in> positive_x_axis"
        using ex_unit_disc_fix_to_zero_positive_x_axis[of u' v'] in_disc
        by auto

      then obtain Mv' where Mv': "moebius_pt M v' = of_complex Mv'"
        using inf_or_of_complex[of "moebius_pt M v'"] in_disc unit_disc_fix_iff[of M]
        by (metis image_eqI inf_notin_unit_disc)

      have "moebius_pt M v' \<in> unit_disc"
        using M(1) \<open>v' \<in> unit_disc\<close>
        by auto

      have "Re Mv' > 0" "is_real Mv'" "Re Mv' < 1"
        using M Mv' of_complex_inj \<open>moebius_pt M v' \<in> unit_disc\<close>
        unfolding positive_x_axis_def circline_set_x_axis
        using cmod_eq_Re
        by auto fastforce

      have "poincare_distance 0\<^sub>h (moebius_pt M v') = poincare_distance u' v'"
        using M(1)
        using in_disc
        by (subst M(2)[symmetric], simp)

      have "Mv' = x"
        using \<open>poincare_distance 0\<^sub>h (moebius_pt M v') = poincare_distance u' v'\<close> Mv'
        using \<open>poincare_distance 0\<^sub>h (of_complex x) = poincare_distance u' v'\<close>
        using unique_x_axis_poincare_distance_positive[of "poincare_distance u' v'"]
          \<open>poincare_distance u' v' > 0\<close>
        using \<open>Re Mv' > 0\<close> \<open>Re Mv' < 1\<close> \<open>is_real Mv'\<close>
        using \<open>is_real x\<close> \<open>Re x > 0\<close> \<open>Re x < 1\<close>
        unfolding positive_x_axis_def
        by auto

      thus "?P' u' v' 0\<^sub>h (of_complex x)"
        using M Mv'
        by auto
    qed
  next
    show "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
      by fact+
  next
    fix M u v
    let ?Mu = "moebius_pt M u" and ?Mv = "moebius_pt M v"
    assume 1: "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
    hence 2: "?Mu \<noteq> ?Mv" "?Mu \<in> unit_disc" "?Mv \<in> unit_disc"
      by auto
    assume 3: "?P (moebius_pt M u) (moebius_pt M v)"
    show "?P u v"
    proof safe
      fix u' v'
      assume 4: "u' \<in> unit_disc" "v' \<in> unit_disc" "poincare_distance u v = poincare_distance u' v'"
      hence "poincare_distance ?Mu ?Mv = poincare_distance u v"
        using 1
        by simp
      then obtain M' where 5: "unit_disc_fix M'" "moebius_pt M' u' = ?Mu" "moebius_pt M' v' = ?Mv"
        using 2 3 4
        by auto
      let ?M = "(-M) + M'"
      have "unit_disc_fix ?M \<and> moebius_pt ?M u' = u \<and> moebius_pt ?M v' = v"
        using 5 \<open>unit_disc_fix M\<close>
        using unit_disc_fix_moebius_comp[of "-M" "M'"]
        using unit_disc_fix_moebius_inv[of M]
        by simp
      thus "\<exists>M. unit_disc_fix M \<and> moebius_pt M u' = u \<and> moebius_pt M v' = v"
        by blast
    qed
  qed
  then obtain M where "unit_disc_fix M \<and> moebius_pt M u' = u \<and> moebius_pt M v' = v"
    using assms \<open>u \<noteq> v\<close>
    by blast
  hence "unit_disc_fix (-M) \<and> moebius_pt (-M) u = u' \<and> moebius_pt (-M) v = v'"
    using unit_disc_fix_moebius_inv[of M]
    by auto
  thus ?thesis
    by blast
qed

lemma unique_midpoint_x_axis:
  assumes x: "is_real x" "-1 < Re x" "Re x < 1" and
          y: "is_real y" "-1 < Re y" "Re y < 1" and
          "x \<noteq> y"
  shows "\<exists>! z. -1 < Re z \<and> Re z < 1 \<and> is_real z \<and> poincare_distance (of_complex z) (of_complex x) = poincare_distance (of_complex z) (of_complex y)" (is "\<exists>! z. ?R z (of_complex x) (of_complex y)")
proof-
  let ?x = "of_complex x" and ?y = "of_complex y"
  let ?P = "\<lambda> x y. \<exists>! z. ?R z x y"
  have "\<forall> x. -1 < Re x \<and> Re x < 1 \<and> is_real x \<and> of_complex x \<noteq> ?y \<longrightarrow> ?P (of_complex x) ?y" (is "?Q (of_complex y)")
  proof (rule wlog_real_zero)
    show "?y \<in> unit_disc"
      using y
      by (simp add: cmod_eq_Re)
  next
    show "is_real (to_complex ?y)"
      using y
      by simp
  next
    show "?Q 0\<^sub>h"
    proof (rule allI, rule impI, (erule conjE)+)
      fix x
      assume x: "-1 < Re x" "Re x < 1" "is_real x" 
      let ?x = "of_complex x"
      assume "?x \<noteq> 0\<^sub>h"
      hence "x \<noteq> 0"
        by auto
      hence "Re x \<noteq> 0"
        using x
        using complex_neq_0
        by auto

      have *: "\<forall> a. -1 < a \<and> a < 1 \<longrightarrow> 
                 (poincare_distance (of_complex (cor a)) ?x = poincare_distance (of_complex (cor a)) 0\<^sub>h \<longleftrightarrow>
                 (Re x) * a * a - 2 * a + Re x = 0)"
      proof (rule allI, rule impI)
        fix a :: real
        assume "-1 < a \<and> a < 1"
        hence "of_complex (cor a) \<in> unit_disc"
          by auto
        moreover
        have "(a - Re x)\<^sup>2 / ((1 - a\<^sup>2) * (1 - (Re x)\<^sup>2)) = a\<^sup>2 / (1 - a\<^sup>2) \<longleftrightarrow>
              (Re x) * a * a - 2 * a + Re x = 0" (is "?lhs \<longleftrightarrow> ?rhs")
        proof-
          have "1 - a\<^sup>2 \<noteq> 0"
            using \<open>-1 < a \<and> a < 1\<close>
            by (metis cancel_comm_monoid_add_class.diff_cancel diff_eq_diff_less less_numeral_extra(4) power2_eq_1_iff right_minus_eq)
          hence "?lhs \<longleftrightarrow> (a - Re x)\<^sup>2 / (1 - (Re x)\<^sup>2) = a\<^sup>2"
            by (smt divide_cancel_right divide_divide_eq_left mult.commute)
          also have "... \<longleftrightarrow> (a - Re x)\<^sup>2 = a\<^sup>2 * (1 - (Re x)\<^sup>2)"
          proof-
            have "1 - (Re x)\<^sup>2 \<noteq> 0"
              using x
              by (smt power2_eq_1_iff)
            thus ?thesis
              by (simp add: divide_eq_eq)
          qed
          also have "... \<longleftrightarrow> a\<^sup>2 * (Re x)\<^sup>2 - 2*a*Re x + (Re x)\<^sup>2 = 0"
            by (simp add: power2_diff field_simps)
          also have "... \<longleftrightarrow> Re x * (a\<^sup>2 * Re x - 2 * a + Re x) = 0"
            by (simp add: power2_eq_square field_simps)
          also have "... \<longleftrightarrow> ?rhs"
            using \<open>Re x \<noteq> 0\<close>
            by (simp add: mult.commute mult.left_commute power2_eq_square)
          finally
          show ?thesis
            .
        qed
        moreover 
        have "arcosh (1 + 2 * ((a - Re x)\<^sup>2 / ((1 - a\<^sup>2) * (1 - (Re x)\<^sup>2)))) = arcosh (1 + 2 * a\<^sup>2 / (1 - a\<^sup>2)) \<longleftrightarrow> ?lhs"
          using \<open>-1 < a \<and> a < 1\<close> x mult_left_cancel[of "2::real" "(a - Re x)\<^sup>2 / ((1 - a\<^sup>2) * (1 - (Re x)\<^sup>2))" "a\<^sup>2 / (1 - a\<^sup>2)"]
          by (subst arcosh_eq_iff, simp_all add: square_le_1)
        ultimately
        show "poincare_distance (of_complex (cor a)) (of_complex x) = poincare_distance (of_complex (cor a)) 0\<^sub>h \<longleftrightarrow>
              (Re x) * a * a - 2 * a + Re x = 0"
          using x
          by (auto simp add: poincare_distance_formula cmod_eq_Re)
      qed

      show "?P ?x 0\<^sub>h"
      proof
        let ?a = "(1 - sqrt(1 - (Re x)\<^sup>2)) / (Re x)"        
        let ?b = "(1 + sqrt(1 - (Re x)\<^sup>2)) / (Re x)"

        have "is_real ?a"
          by simp                                                       
        moreover
        have "1 - (Re x)\<^sup>2 > 0"
          using x
          by (smt power2_eq_1_iff square_le_1)
        have "\<bar>?a\<bar> < 1"
        proof (cases "Re x > 0")
          case True
          have "(1 - Re x)\<^sup>2 < 1 - (Re x)\<^sup>2"
            using \<open>Re x > 0\<close> x
            by (simp add: power2_eq_square field_simps)
          hence "1 - Re x < sqrt (1 - (Re x)\<^sup>2)"
            using real_less_rsqrt by fastforce
          thus ?thesis
            using \<open>1 - (Re x)\<^sup>2 > 0\<close> \<open>Re x > 0\<close>
            by simp
        next
          case False
          hence "Re x < 0"
            using \<open>Re x \<noteq> 0\<close>
            by simp

          have "1 + Re x > 0"
            using \<open>Re x > -1\<close>           
            by simp
          hence "2*Re x + 2*Re x*Re x < 0"
            using \<open>Re x < 0\<close>
            by (metis comm_semiring_class.distrib mult.commute mult_2_right mult_less_0_iff one_add_one zero_less_double_add_iff_zero_less_single_add)
          hence "(1 + Re x)\<^sup>2 < 1 - (Re x)\<^sup>2"
            by (simp add: power2_eq_square field_simps)
          hence "1 + Re x < sqrt (1 - (Re x)\<^sup>2)"
            using \<open>1 - (Re x)\<^sup>2 > 0\<close>
            using real_less_rsqrt by blast
          thus ?thesis
            using \<open>Re x < 0\<close>
            by (simp add: field_simps)
        qed
        hence "-1 < ?a" "?a < 1"
          by linarith+
        moreover
        have "(Re x) * ?a * ?a - 2 * ?a + Re x = 0"
          using \<open>Re x \<noteq> 0\<close> \<open>1 - (Re x)\<^sup>2 > 0\<close>
          by (simp add: field_simps power2_eq_square)
        ultimately
        show "-1 < Re (cor ?a) \<and> Re (cor ?a) < 1 \<and> is_real ?a \<and> poincare_distance (of_complex ?a) (of_complex x) = poincare_distance (of_complex ?a) 0\<^sub>h"
          using *
          by auto

        fix z
        assume **: "- 1 < Re z \<and> Re z < 1 \<and> is_real z \<and>
               poincare_distance (of_complex z) (of_complex x) = poincare_distance (of_complex z) 0\<^sub>h"
        hence "Re x * Re z * Re z - 2 * Re z + Re x = 0"
          using *[rule_format, of "Re z"] x
          by auto
        moreover 
        have "sqrt (4 - 4 * Re x * Re x) = 2 * sqrt(1 - Re x * Re x)"
        proof-
          have "sqrt (4 - 4 * Re x * Re x) = sqrt(4 * (1 - Re x * Re x))"
            by simp
          thus ?thesis
            by (simp only: real_sqrt_mult, simp)
        qed
        moreover
        have "(2 - 2 * sqrt (1 - Re x * Re x)) / (2 * Re x) = ?a"
        proof-
          have "(2 - 2 * sqrt (1 - Re x * Re x)) / (2 * Re x) = 
               (2 * (1 - sqrt (1 - Re x * Re x))) / (2 * Re x)"
            by simp
          thus ?thesis
            by (subst (asm) mult_divide_mult_cancel_left) (auto simp add: power2_eq_square)
        qed
        moreover
        have "(2 + 2 * sqrt (1 - Re x * Re x)) / (2 * Re x) = ?b"
        proof-
          have "(2 + 2 * sqrt (1 - Re x * Re x)) / (2 * Re x) = 
               (2 * (1 + sqrt (1 - Re x * Re x))) / (2 * Re x)"
            by simp
          thus ?thesis
            by (subst (asm) mult_divide_mult_cancel_left) (auto simp add: power2_eq_square)
        qed
        ultimately
        have "Re z = ?a \<or> Re z = ?b"
          using discriminant_nonneg[of "Re x" "-2" "Re x" "Re z"] discrim_def[of "Re x" "-2" "Re x"]
          using \<open>Re x \<noteq> 0\<close> \<open>-1 < Re x\<close> \<open>Re x < 1\<close> \<open>1 - (Re x)\<^sup>2 > 0\<close>
          by (auto simp add:power2_eq_square)    
        have "\<bar>?b\<bar> > 1"
        proof (cases "Re x > 0")
          case True
          have "(Re x - 1)\<^sup>2 < 1 - (Re x)\<^sup>2"
            using \<open>Re x > 0\<close> x
            by (simp add: power2_eq_square field_simps)
          hence "Re x - 1 < sqrt (1 - (Re x)\<^sup>2)"
            using real_less_rsqrt
            by simp
          thus ?thesis
            using \<open>1 - (Re x)\<^sup>2 > 0\<close> \<open>Re x > 0\<close>
            by simp
        next
          case False
          hence "Re x < 0"
            using \<open>Re x \<noteq> 0\<close>
            by simp      
          have "1 + Re x > 0"
            using \<open>Re x > -1\<close>
            by simp
          hence "2*Re x + 2*Re x*Re x < 0"
            using \<open>Re x < 0\<close>
            by (metis comm_semiring_class.distrib mult.commute mult_2_right mult_less_0_iff one_add_one zero_less_double_add_iff_zero_less_single_add)
          hence "1 - (Re x)\<^sup>2 > (- 1 - (Re x))\<^sup>2"
            by (simp add: field_simps power2_eq_square)
          hence "sqrt (1 - (Re x)\<^sup>2) > -1 - Re x"
            using real_less_rsqrt
            by simp
          thus ?thesis
            using \<open>Re x < 0\<close>
            by (simp add: field_simps)
        qed
        hence "?b < -1 \<or> ?b > 1"
          by auto

        hence "Re z = ?a"
          using \<open>Re z = ?a \<or> Re z = ?b\<close> **
          by auto
        thus "z = ?a"
          using ** complex_of_real_Re
          by fastforce
      qed
    qed
  next
    fix a u
    let ?M = "moebius_pt (blaschke a)"
    let ?Mu = "?M u"
    assume "u \<in> unit_disc" "is_real a" "cmod a < 1"
    assume *: "?Q ?Mu"
    show "?Q u"
    proof (rule allI, rule impI, (erule conjE)+)
      fix x                                    
      assume x: "-1 < Re x" "Re x < 1" "is_real x" "of_complex x \<noteq> u"
      let ?Mx = "?M (of_complex x)"
      have "of_complex x \<in> unit_disc"
        using x cmod_eq_Re
        by auto
      hence "?Mx \<in> unit_disc"
        using \<open>is_real a\<close> \<open>cmod a < 1\<close> blaschke_unit_disc_fix[of a]
        using unit_disc_fix_discI
        by blast
      hence "?Mx \<noteq> \<infinity>\<^sub>h"
        by auto
      moreover
      have "of_complex x \<in> circline_set x_axis"
        using x
        by auto
      hence "?Mx \<in> circline_set x_axis"
        using blaschke_real_preserve_x_axis[OF \<open>is_real a\<close> \<open>cmod a < 1\<close>, of "of_complex x"]
        by auto
      hence "-1 < Re (to_complex ?Mx) \<and> Re (to_complex ?Mx) < 1 \<and> is_real (to_complex ?Mx)"
        using \<open>?Mx \<noteq> \<infinity>\<^sub>h\<close> \<open>?Mx \<in> unit_disc\<close>
        unfolding circline_set_x_axis
        by (auto simp add: cmod_eq_Re)
      moreover
      have "?Mx \<noteq> ?Mu"
        using \<open>of_complex x \<noteq> u\<close>
        by simp
      ultimately
      have "?P ?Mx ?Mu"
        using *[rule_format, of "to_complex ?Mx"] \<open>?Mx \<noteq> \<infinity>\<^sub>h\<close>
        by simp
      then obtain Mz where
        "?R Mz ?Mx ?Mu"
        by blast
      have "of_complex Mz \<in> unit_disc" "of_complex Mz \<in> circline_set x_axis"
        using \<open>?R Mz ?Mx ?Mu\<close>
        using cmod_eq_Re 
        by auto

      let ?Minv = "- (blaschke a)"
      let ?z = "moebius_pt ?Minv (of_complex Mz)"
      have "?z \<in> unit_disc"
        using \<open>of_complex Mz \<in> unit_disc\<close> \<open>cmod a < 1\<close>
        by auto
      moreover
      have "?z \<in> circline_set x_axis"
        using \<open>of_complex Mz \<in> circline_set x_axis\<close>
        using blaschke_real_preserve_x_axis \<open>is_real a\<close> \<open>cmod a < 1\<close>
        by fastforce
      ultimately
      have z1: "-1 < Re (to_complex ?z)" "Re (to_complex ?z) < 1" "is_real (to_complex ?z)"
        using inf_or_of_complex[of "?z"]
        unfolding circline_set_x_axis
        by (auto simp add: cmod_eq_Re)
      
      have z2: "poincare_distance ?z (of_complex x) = poincare_distance ?z u"
        using \<open>?R Mz ?Mx ?Mu\<close> \<open>cmod a < 1\<close> \<open>?z \<in> unit_disc\<close> \<open>of_complex x \<in> unit_disc\<close> \<open>u \<in> unit_disc\<close>
        by (metis blaschke_preserve_distance_formula blaschke_unit_disc_fix moebius_pt_comp_inv_right poincare_distance_formula uminus_moebius_def unit_disc_fix_discI unit_disc_iff_cmod_lt_1)
      show "?P (of_complex x) u"
      proof
        show "?R (to_complex ?z) (of_complex x) u"
          using z1 z2 \<open>?z \<in> unit_disc\<close> inf_or_of_complex[of ?z]
          by auto
      next
        fix z'
        assume "?R z' (of_complex x) u"
        hence "of_complex z' \<in> unit_disc" "of_complex z' \<in> circline_set x_axis"
          by (auto simp add: cmod_eq_Re)
        let ?Mz' = "?M (of_complex z')"
        have "?Mz' \<in> unit_disc" "?Mz' \<in> circline_set x_axis"
          using \<open>of_complex z' \<in> unit_disc\<close> \<open>of_complex z' \<in> circline_set x_axis\<close> \<open>cmod a < 1\<close> \<open>is_real a\<close>
          using  blaschke_unit_disc_fix unit_disc_fix_discI
          using blaschke_real_preserve_x_axis circline_set_x_axis
          by blast+
        hence "-1 < Re (to_complex ?Mz')" "Re (to_complex ?Mz') < 1" "is_real (to_complex ?Mz')"
          unfolding circline_set_x_axis
          by (auto simp add: cmod_eq_Re)
        moreover
        have "poincare_distance ?Mz' ?Mx = poincare_distance ?Mz' ?Mu"
          using \<open>?R z' (of_complex x) u\<close>
          using \<open>cmod a < 1\<close> \<open>of_complex x \<in> unit_disc\<close> \<open>of_complex z' \<in> unit_disc\<close> \<open>u \<in> unit_disc\<close>
          by auto
        ultimately
        have "?R (to_complex ?Mz') ?Mx ?Mu"
          using \<open>?Mz' \<in> unit_disc\<close> inf_or_of_complex[of ?Mz']
          by auto
        hence "?Mz' = of_complex Mz"
          using \<open>?P ?Mx ?Mu\<close> \<open>?R Mz ?Mx ?Mu\<close>
          by (metis \<open>moebius_pt (blaschke a) (of_complex z') \<in> unit_disc\<close> \<open>of_complex Mz \<in> unit_disc\<close> to_complex_of_complex unit_disc_to_complex_inj)
        thus "z' = to_complex ?z"
          using moebius_pt_invert by auto
      qed
    qed
  qed
  thus ?thesis
    using assms
    by (metis to_complex_of_complex)
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Triangle inequality\<close>
(* ------------------------------------------------------------------ *)

lemma poincare_distance_formula_zero_sum:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc"
  shows "poincare_distance u 0\<^sub>h + poincare_distance 0\<^sub>h v =
         (let u' = cmod (to_complex u); v' = cmod (to_complex v)
           in arcosh (((1 + u'\<^sup>2) * (1 + v'\<^sup>2) + 4 * u' * v') / ((1 - u'\<^sup>2) * (1 - v'\<^sup>2))))"
proof-
  obtain u' v' where uv: "u' = to_complex u" "v' = to_complex v"
    by auto
  have uv': "u = of_complex u'" "v = of_complex v'"
    using uv assms inf_or_of_complex[of u] inf_or_of_complex[of v]
    by auto

  let ?u' = "cmod u'" and ?v' = "cmod v'"

  have disc: "?u'\<^sup>2 < 1" "?v'\<^sup>2 < 1"
    using unit_disc_cmod_square_lt_1[OF \<open>u \<in> unit_disc\<close>]
    using unit_disc_cmod_square_lt_1[OF \<open>v \<in> unit_disc\<close>] uv
    by auto
  thm arcosh_add
  have "arcosh (1 + 2 * ?u'\<^sup>2 / (1 - ?u'\<^sup>2)) + arcosh (1 + 2 * ?v'\<^sup>2 / (1 - ?v'\<^sup>2)) =
        arcosh (((1 + ?u'\<^sup>2) * (1 + ?v'\<^sup>2) + 4 * ?u' * ?v') / ((1 - ?u'\<^sup>2) * (1 - ?v'\<^sup>2)))" (is "arcosh ?ll + arcosh ?rr = arcosh ?r")
  proof (subst arcosh_add)
    show "?ll \<ge> 1"  "?rr \<ge> 1"
      using disc
      by auto
  next
    show "arcosh ((1 + 2 * ?u'\<^sup>2 / (1 - ?u'\<^sup>2)) * (1 + 2 * ?v'\<^sup>2 / (1 - ?v'\<^sup>2)) +
                  sqrt (((1 + 2 * ?u'\<^sup>2 / (1 - ?u'\<^sup>2))\<^sup>2 - 1) * ((1 + 2 * ?v'\<^sup>2 / (1 - ?v'\<^sup>2))\<^sup>2 - 1))) =
          arcosh ?r" (is "arcosh ?l = _")
    proof-
      have "1 + 2 * ?u'\<^sup>2 / (1 - ?u'\<^sup>2) = (1 + ?u'\<^sup>2) / (1 - ?u'\<^sup>2)"
        using disc
        by (subst add_divide_eq_iff, simp_all)
      moreover
      have "1 + 2 * ?v'\<^sup>2 / (1 - ?v'\<^sup>2) = (1 + ?v'\<^sup>2) / (1 - ?v'\<^sup>2)"
        using disc
        by (subst add_divide_eq_iff, simp_all)
      moreover
      have "sqrt (((1 + 2 * ?u'\<^sup>2 / (1 - ?u'\<^sup>2))\<^sup>2 - 1) * ((1 + 2 * ?v'\<^sup>2 / (1 - ?v'\<^sup>2))\<^sup>2 - 1)) =
               (4  * ?u' * ?v') / ((1 - ?u'\<^sup>2) * (1 - ?v'\<^sup>2))" (is "sqrt ?s = ?t")
      proof-
        have "?s = ?t\<^sup>2"
          using disc
          apply (subst add_divide_eq_iff, simp)+
          apply (subst power_divide)+
          apply simp
          apply (subst divide_diff_eq_iff, simp)+
          apply (simp add: power2_eq_square field_simps)
          done
        thus ?thesis
          using disc
          by simp
      qed
      ultimately
      have "?l = ?r"
        using disc
        by simp (subst add_divide_distrib, simp)
      thus ?thesis
        by simp
    qed
  qed
  thus ?thesis
    using uv' assms
    using poincare_distance_formula
    by (simp add: Let_def)
qed

lemma poincare_distance_triangle_inequality:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc" and "w \<in> unit_disc"
  shows "poincare_distance u v + poincare_distance v w \<ge> poincare_distance u w" (is "?P' u v w")
proof-
  have "\<forall> w. w \<in> unit_disc \<longrightarrow> ?P' u v w"  (is "?P v u")
  proof (rule wlog_x_axis[where P="?P"])
    fix x
    assume "is_real x" "0 \<le> Re x" "Re x < 1"
    hence "of_complex x \<in> unit_disc"
      by (simp add: cmod_eq_Re)

    show "?P 0\<^sub>h (of_complex x)"
    proof safe
      fix w
      assume "w \<in> unit_disc"
      then obtain w' where w: "w = of_complex w'"
        using inf_or_of_complex[of w]
        by auto

      let ?x = "cmod x" and ?w = "cmod w'" and ?xw = "cmod (x - w')"

      have disc: "?x\<^sup>2 < 1" "?w\<^sup>2 < 1"
        using unit_disc_cmod_square_lt_1[OF \<open>of_complex x \<in> unit_disc\<close>]
        using unit_disc_cmod_square_lt_1[OF \<open>w \<in> unit_disc\<close>] w
        by auto

      have "poincare_distance (of_complex x) 0\<^sub>h + poincare_distance 0\<^sub>h w =
           arcosh (((1 + ?x\<^sup>2) * (1 + ?w\<^sup>2) + 4 * ?x * ?w) / ((1 - ?x\<^sup>2) * (1 - ?w\<^sup>2)))" (is "_ = arcosh ?r1")
        using poincare_distance_formula_zero_sum[OF \<open>of_complex x \<in> unit_disc\<close> \<open>w \<in> unit_disc\<close>] w
        by (simp add: Let_def)
      moreover
      have "poincare_distance (of_complex x) (of_complex w') =
            arcosh (((1 - ?x\<^sup>2) * (1 - ?w\<^sup>2) + 2 * ?xw\<^sup>2) / ((1 - ?x\<^sup>2) * (1 - ?w\<^sup>2)))" (is "_ = arcosh ?r2")
        using disc
        using poincare_distance_formula[OF \<open>of_complex x \<in> unit_disc\<close> \<open>w \<in> unit_disc\<close>] w
        by (subst add_divide_distrib) simp
      moreover
      have *: "(1 - ?x\<^sup>2) * (1 - ?w\<^sup>2) + 2 * ?xw\<^sup>2 \<le> (1 + ?x\<^sup>2) * (1 + ?w\<^sup>2) + 4 * ?x * ?w"
      proof-
        have "(cmod (x - w'))\<^sup>2 \<le> (cmod x + cmod w')\<^sup>2"
          using norm_triangle_ineq4[of x w']
          by (simp add: power_mono)
        thus ?thesis
          by (simp add: field_simps power2_sum)
      qed
      have "arcosh ?r1 \<ge> arcosh ?r2"
      proof (subst arcosh_mono)
        show "?r1 \<ge> 1"
          using disc
          by (smt "*" le_divide_eq_1_pos mult_pos_pos zero_le_power2)
      next
        show "?r2 \<ge> 1"
          using disc
          by simp
      next
        show "?r1 \<ge> ?r2"
          using disc
          using *
          by (subst divide_right_mono, simp_all)
      qed
      ultimately
      show "poincare_distance (of_complex x) w \<le> poincare_distance (of_complex x) 0\<^sub>h + poincare_distance 0\<^sub>h w"
        using \<open>of_complex x \<in> unit_disc\<close> \<open>w \<in> unit_disc\<close> w
        using poincare_distance_formula
        by simp
    qed
  next
    show "v \<in> unit_disc" "u \<in> unit_disc"
      by fact+
  next
    fix M u v
    assume *: "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc"
    assume **: "?P (moebius_pt M u) (moebius_pt M v)"
    show "?P u v"
    proof safe
      fix w
      assume "w \<in> unit_disc"
      thus "?P' v u w"
        using * **[rule_format, of "moebius_pt M w"]
        by simp
    qed
  qed
  thus ?thesis
    using assms
    by auto
qed

end