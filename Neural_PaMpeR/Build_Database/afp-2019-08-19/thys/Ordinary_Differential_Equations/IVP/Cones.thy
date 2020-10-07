theory Cones
imports
  "HOL-Analysis.Analysis"
  Triangle.Triangle
  "../ODE_Auxiliarities"
begin

lemma arcsin_eq_zero_iff[simp]: "-1 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> arcsin x = 0 \<longleftrightarrow> x = 0"
  using sin_arcsin by fastforce

definition conemem :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a" where "conemem u v t = cos t *\<^sub>R u + sin t *\<^sub>R v"
definition "conesegment u v = conemem u v ` {0.. pi / 2}"

lemma
  bounded_linear_image_conemem:
  assumes "bounded_linear F"
  shows "F (conemem u v t) = conemem (F u) (F v) t"
proof -
  from assms interpret bounded_linear F .
  show ?thesis
    by (auto simp: conemem_def[abs_def] cone_hull_expl closed_segment_def add scaleR)
qed

lemma
  bounded_linear_image_conesegment:
  assumes "bounded_linear F"
  shows "F ` conesegment u v = conesegment (F u) (F v)"
proof -
  from assms interpret bounded_linear F .
  show ?thesis
    apply (auto simp: conesegment_def conemem_def[abs_def] cone_hull_expl closed_segment_def add scaleR)
    apply (auto simp: add[symmetric] scaleR[symmetric])
    done
qed

(* This is vangle in $AFP/Triangles/Angles *)

lemma discriminant: "a * x\<^sup>2 + b * x + c = (0::real) \<Longrightarrow> 0 \<le> b\<^sup>2 - 4 * a * c" 
  by (sos "(((A<0 * R<1) + (R<1 * (R<1 * [2*a*x + b]^2))))")

lemma quadratic_eq_factoring:
  assumes D: "D = b\<^sup>2 - 4 * a * c"
  assumes nn: "0 \<le> D"
  assumes x1: "x\<^sub>1 = (-b + sqrt D) / (2 * a)"
  assumes x2: "x\<^sub>2 = (-b - sqrt D) / (2 * a)"
  assumes a: "a \<noteq> 0"
  shows "a * x\<^sup>2 + b * x + c = a * (x - x\<^sub>1) * (x - x\<^sub>2)"
  using nn
  by (simp add: D x1 x2)
    (simp add: assms algebra_simps power2_eq_square power3_eq_cube divide_simps)

lemma quadratic_eq_zeroes_iff:
  assumes D: "D = b\<^sup>2 - 4 * a * c"
  assumes x1: "x\<^sub>1 = (-b + sqrt D) / (2 * a)"
  assumes x2: "x\<^sub>2 = (-b - sqrt D) / (2 * a)"
  assumes a: "a \<noteq> 0"
  shows "a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow> (D \<ge> 0 \<and> (x = x\<^sub>1 \<or> x = x\<^sub>2))" (is "?z \<longleftrightarrow> _")
  using quadratic_eq_factoring[OF D _ x1 x2 a, of x] discriminant[of a x b c] a
  by (auto simp: D)

lemma quadratic_ex_zero_iff:
  "(\<exists>x. a * x\<^sup>2 + b * x + c = 0) \<longleftrightarrow> (a \<noteq> 0 \<and> b\<^sup>2 - 4 * a * c \<ge> 0 \<or> a = 0 \<and> (b = 0 \<longrightarrow> c = 0))"
  for a b c::real
  apply (cases "a = 0")
  subgoal by (auto simp: intro: exI[where x="- c / b"])
  subgoal by (subst quadratic_eq_zeroes_iff[OF refl refl refl]) auto
  done

lemma Cauchy_Schwarz_eq_iff:
  shows "(inner x y)\<^sup>2 = inner x x * inner y y \<longleftrightarrow> ((\<exists>k. x = k *\<^sub>R y) \<or> y = 0)"
proof safe
  assume eq: "(x \<bullet> y)\<^sup>2 = x \<bullet> x * (y \<bullet> y)" and "y \<noteq> 0"
  define f where "f \<equiv> \<lambda>l. inner (x - l *\<^sub>R y) (x - l *\<^sub>R y)"
  have f_quadratic: "f l = inner y y * l\<^sup>2 + - 2 * inner x y * l + inner x x" for l
    by (auto simp: f_def algebra_simps power2_eq_square inner_commute)
  have "\<exists>l. f l = 0"
    unfolding f_quadratic quadratic_ex_zero_iff
    using \<open>y \<noteq> 0\<close>
    by (auto simp: eq)
  then show "(\<exists>k. x = k *\<^sub>R y)"
    by (auto simp: f_def)
qed (auto simp: power2_eq_square)

lemma Cauchy_Schwarz_strict_ineq:
  "(inner x y)\<^sup>2 < inner x x * inner y y" if "y \<noteq> 0" "\<And>k. x \<noteq> k *\<^sub>R y"
  apply (rule neq_le_trans)
  subgoal
    using that
    unfolding Cauchy_Schwarz_eq_iff
    by auto
  subgoal by (rule Cauchy_Schwarz_ineq)
  done

lemma Cauchy_Schwarz_eq2_iff:
  "\<bar>inner x y\<bar> = norm x * norm y \<longleftrightarrow> ((\<exists>k. x = k *\<^sub>R y) \<or> y = 0)"
  using Cauchy_Schwarz_eq_iff[of x y]
  by (subst power_eq_iff_eq_base[symmetric, where n = 2])
     (simp_all add: dot_square_norm power_mult_distrib)

lemma Cauchy_Schwarz_strict_ineq2:
  "\<bar>inner x y\<bar> < norm x * norm y" if "y \<noteq> 0" "\<And>k. x \<noteq> k *\<^sub>R y"
  apply (rule neq_le_trans)
  subgoal
    using that
    unfolding Cauchy_Schwarz_eq2_iff
    by auto
  subgoal by (rule Cauchy_Schwarz_ineq2)
  done

lemma gt_minus_one_absI: "abs k < 1 \<Longrightarrow> - 1 < k" for k::real
  by auto
lemma gt_one_absI: "abs k < 1 \<Longrightarrow> k < 1" for k::real
  by auto

lemma abs_impossible:
  "\<bar>y1\<bar> < x1 \<Longrightarrow> \<bar>y2\<bar> < x2 \<Longrightarrow> x1 * x2 + y1 * y2 \<noteq> 0" for x1 x2::real
proof goal_cases
  case 1
  have "- y1 * y2 \<le> abs y1 * abs y2"
    by (metis abs_ge_minus_self abs_mult mult.commute mult_minus_right)
  also have "\<dots> < x1 * x2"
    apply (rule mult_strict_mono)
    using 1 by auto
  finally show ?case by auto
qed

lemma vangle_eq_arctan_minus:\<comment> \<open>TODO: generalize?!\<close>
  assumes ij: "i \<in> Basis" "j \<in> Basis" and ij_neq: "i \<noteq> j"
  assumes xy1: "\<bar>y1\<bar> < x1"
  assumes xy2: "\<bar>y2\<bar> < x2"
  assumes less: "y2 / x2 > y1 / x1"
  shows "vangle (x1 *\<^sub>R i + y1 *\<^sub>R j) (x2 *\<^sub>R i + y2 *\<^sub>R j) = arctan (y2 / x2) - arctan (y1 / x1)"
    (is "vangle ?u ?v = _")
proof -
  from assms have less2: "x2 * y1 - x1 * y2 < 0"
    by (auto simp: divide_simps abs_real_def algebra_simps split: if_splits)
  have norm_eucl: "norm (x *\<^sub>R i + y *\<^sub>R j) = sqrt ((norm x)\<^sup>2 + (norm y)\<^sup>2)" for x y
    apply (subst norm_eq_sqrt_inner)
    using ij ij_neq
    by (auto simp: inner_simps inner_Basis power2_eq_square)
  have nonzeroes: "x1 *\<^sub>R i + y1 *\<^sub>R j \<noteq> 0" "x2 *\<^sub>R i + y2 *\<^sub>R j \<noteq> 0"
     apply (auto simp: euclidean_eq_iff[where 'a='a] inner_simps intro!: bexI[where x=i])
    using assms
    by (auto simp: inner_Basis)
  have indep: "x1 *\<^sub>R i + y1 *\<^sub>R j \<noteq> k *\<^sub>R (x2 *\<^sub>R i + y2 *\<^sub>R j)" for k
  proof
    assume "x1 *\<^sub>R i + y1 *\<^sub>R j = k *\<^sub>R (x2 *\<^sub>R i + y2 *\<^sub>R j)"
    then have "x1 / x2 = k" "y1 = k * y2"
      using ij ij_neq xy1 xy2
       apply (auto simp: abs_real_def divide_simps algebra_simps euclidean_eq_iff[where 'a='a] inner_simps
          split: if_splits)
      by (auto simp: inner_Basis split: if_splits)
    then have "y1 = x1 / x2 * y2" by simp
    with less show False using xy1 by (auto split: if_splits)
  qed
  have "((x1\<^sup>2 + y1\<^sup>2) * (x2\<^sup>2 + y2\<^sup>2) *
          (1 - ((x1 *\<^sub>R i + y1 *\<^sub>R j) \<bullet> (x2 *\<^sub>R i + y2 *\<^sub>R j))\<^sup>2 / ((x1\<^sup>2 + y1\<^sup>2) * (x2\<^sup>2 + y2\<^sup>2)))) =
    ((x1\<^sup>2 + y1\<^sup>2) * (x2\<^sup>2 + y2\<^sup>2) *
          (1 - (x1 * x2 + y1 * y2)\<^sup>2 / ((x1\<^sup>2 + y1\<^sup>2) * (x2\<^sup>2 + y2\<^sup>2))))"
    using ij_neq ij
    by (auto simp: algebra_simps divide_simps inner_simps inner_Basis)
  also have "\<dots> = (x1\<^sup>2 + y1\<^sup>2) * (x2\<^sup>2 + y2\<^sup>2) - (x1 * x2 + y1 * y2)\<^sup>2"
    unfolding right_diff_distrib by simp
  also have "\<dots> = (x2 * y1 - x1 * y2)^2"
    by (auto simp: algebra_simps power2_eq_square)
  also have "sqrt \<dots> = \<bar>x2 * y1 - x1 * y2\<bar>"
    by simp
  also have "\<dots> = x1 * y2 - x2 * y1"
    using less2
    by (simp add: abs_real_def)
  finally have sqrt_eq: "sqrt ((x1\<^sup>2 + y1\<^sup>2) * (x2\<^sup>2 + y2\<^sup>2) *
        (1 - ((x1 *\<^sub>R i + y1 *\<^sub>R j) \<bullet> (x2 *\<^sub>R i + y2 *\<^sub>R j))\<^sup>2 / ((x1\<^sup>2 + y1\<^sup>2) * (x2\<^sup>2 + y2\<^sup>2)))) =
    x1 * y2 - x2 * y1"
    .
  show ?thesis
    using ij xy1 xy2
    unfolding vangle_def
    apply (subst arccos_arctan)
    subgoal
      apply (rule gt_minus_one_absI)
      apply (simp add: )
      apply (subst pos_divide_less_eq)
      subgoal
        apply (rule mult_pos_pos)
        using nonzeroes
        by auto
      subgoal
        apply simp
        apply (rule Cauchy_Schwarz_strict_ineq2)
        using nonzeroes indep
        by auto
      done
    subgoal
      apply (rule gt_one_absI)
      apply (simp add: )
      apply (subst pos_divide_less_eq)
      subgoal
        apply (rule mult_pos_pos)
        using nonzeroes
        by auto
      subgoal
        apply simp
        apply (rule Cauchy_Schwarz_strict_ineq2)
        using nonzeroes indep
        by auto
      done
    subgoal
      apply (auto simp: nonzeroes)
      apply (subst (3) diff_conv_add_uminus)
      apply (subst arctan_minus[symmetric])
      apply (subst arctan_add)
        apply force
       apply force
      apply (subst arctan_inverse[symmetric])
      subgoal
        apply (rule divide_pos_pos)
        subgoal
          apply (auto simp add: inner_simps inner_Basis algebra_simps )
           apply (thin_tac "_ \<in> Basis")+ apply (thin_tac "j = i")
           apply (sos "((((A<0 * (A<1 * (A<2 * A<3))) * R<1) + ((A<=0 * (A<0 * (A<2 * R<1))) * (R<1 * [1]^2))))")
          apply (thin_tac "_ \<in> Basis")+ apply (thin_tac "j \<noteq> i")
          by (sos "((((A<0 * (A<1 * (A<2 * A<3))) * R<1) + (((A<2 * (A<3 * R<1)) * (R<1/3 * [y1]^2)) + (((A<1 * (A<3 * R<1)) * ((R<1/12 * [x2 + y1]^2) + (R<1/12 * [x1 + y2]^2))) + (((A<1 * (A<2 * R<1)) * (R<1/12 * [~1*x1 + x2 + y1 + y2]^2)) + (((A<0 * (A<3 * R<1)) * (R<1/12 * [~1*x1 + x2 + ~1*y1 + ~1*y2]^2)) + (((A<0 * (A<2 * R<1)) * ((R<1/12 * [x2 + ~1*y1]^2) + (R<1/12 * [~1*x1 + y2]^2))) + (((A<0 * (A<1 * R<1)) * (R<1/3 * [y2]^2)) + ((A<=0 * R<1) * (R<1/3 * [x1 + x2]^2))))))))))")
        subgoal
          apply (intro mult_pos_pos)
          using nonzeroes indep
            apply auto
          apply (rule gt_one_absI)
          apply (simp add: power_divide power_mult_distrib power2_norm_eq_inner)
          apply (rule Cauchy_Schwarz_strict_ineq)
           apply auto
          done
        done
      subgoal
        apply (rule arg_cong[where f=arctan])
        using nonzeroes ij_neq
        apply (auto simp: norm_eucl)
        apply (subst real_sqrt_mult[symmetric])
        apply (subst real_sqrt_mult[symmetric])
        apply (subst real_sqrt_mult[symmetric])
        apply (subst power_divide)
        apply (subst real_sqrt_pow2)
         apply simp
        apply (subst nonzero_divide_eq_eq)
        subgoal
          apply (auto simp: algebra_simps inner_simps inner_Basis)
          by (auto simp: algebra_simps divide_simps abs_real_def abs_impossible)
        apply (subst sqrt_eq)
        apply (auto simp: algebra_simps inner_simps inner_Basis)
        apply (auto simp: algebra_simps divide_simps abs_real_def abs_impossible)
        by (auto split: if_splits)
      done
    done
qed

lemma vangle_le_pi2: "0 \<le> u \<bullet> v \<Longrightarrow> vangle u v \<le> pi/2"
  unfolding vangle_def atLeastAtMost_iff
  apply (simp del: le_divide_eq_numeral1)
  apply (intro impI arccos_le_pi2 arccos_lbound)
  using Cauchy_Schwarz_ineq2[of u v]
  by (auto simp: divide_simps sign_simps)

lemma inner_eq_vangle: "u \<bullet> v = cos (vangle u v) * (norm u * norm v)"
  by (simp add: cos_vangle)

lemma vangle_scaleR_self:
  "vangle (k *\<^sub>R v) v = (if k = 0 \<or> v = 0 then pi / 2 else if k > 0 then 0 else pi)"
  "vangle v (k *\<^sub>R v) = (if k = 0 \<or> v = 0 then pi / 2 else if k > 0 then 0 else pi)"
  by (auto simp: vangle_def dot_square_norm power2_eq_square)

lemma vangle_scaleR:
  "vangle (k *\<^sub>R v) w = vangle v w" "vangle w (k *\<^sub>R v) = vangle w v" if "k > 0"
  using that
  by (auto simp: vangle_def)

lemma cos_vangle_eq_zero_iff_vangle:
  "cos (vangle u v) = 0 \<longleftrightarrow> (u = 0 \<or> v = 0 \<or> u \<bullet> v = 0)"
  using Cauchy_Schwarz_ineq2[of u v]
  by (auto simp: vangle_def divide_simps sign_simps split: if_splits)

lemma ortho_imp_angle_pi_half: "u \<bullet> v = 0 \<Longrightarrow> vangle u v = pi / 2"
  using orthogonal_iff_vangle[of u v]
  by (auto simp: orthogonal_def)

lemma arccos_eq_zero_iff: "arccos x = 0 \<longleftrightarrow> x = 1" if "-1 \<le> x" "x \<le> 1"
  using that
  apply auto
  using cos_arccos by fastforce


lemma vangle_eq_zeroD: "vangle u v = 0 \<Longrightarrow> (\<exists>k. v = k *\<^sub>R u)"
  apply (auto simp: vangle_def split: if_splits)
   apply (subst (asm) arccos_eq_zero_iff)
  apply (auto simp: divide_simps mult_less_0_iff split: if_splits)
  apply (metis Real_Vector_Spaces.norm_minus_cancel inner_minus_left minus_le_iff norm_cauchy_schwarz)
    apply (metis norm_cauchy_schwarz)
  by (metis Cauchy_Schwarz_eq2_iff abs_of_pos inner_commute mult.commute mult_sign_intros(5) zero_less_norm_iff)

lemma less_one_multI:\<comment> \<open>TODO: also in AA!\<close>
  fixes e x::real
  shows "e \<le> 1 \<Longrightarrow> 0 < x \<Longrightarrow> x < 1 \<Longrightarrow> e * x < 1"
  by (metis (erased, hide_lams) less_eq_real_def monoid_mult_class.mult.left_neutral
    mult_strict_mono zero_less_one)

lemma conemem_expansion_estimate:
  fixes u v u' v'::"'a::euclidean_space"
  assumes "t \<in> {0 .. pi / 2}"
  assumes angle_pos: "0 < vangle u v" "vangle u v < pi / 2"
  assumes angle_le: "(vangle u' v') \<le> (vangle u v)"
  assumes "norm u = 1" "norm v = 1"
  shows "norm (conemem u' v' t) \<ge> min (norm u') (norm v') * norm (conemem u v t)"
proof -
  define e_pre where "e_pre = min (norm u') (norm v')"
  let ?w = "conemem u v"
  let ?w' = "conemem u' v'"
  have cos_angle_le: "cos (vangle u' v') \<ge> cos (vangle u v)"
    using angle_pos vangle_bounds
    by (auto intro!: cos_monotone_0_pi_le angle_le)
  have e_pre_le: "e_pre\<^sup>2 \<le> norm u' * norm v'"
    by (auto simp: e_pre_def min_def power2_eq_square intro: mult_left_mono mult_right_mono)
  have lt: "0 < 1 + 2 * (u \<bullet> v) * sin t * cos t"
  proof -
    have "\<bar>u \<bullet> v\<bar> < norm u * norm v"
      apply (rule Cauchy_Schwarz_strict_ineq2)
      using assms
       apply auto
      apply (subst (asm) vangle_scaleR_self)+
      by (auto simp: split: if_splits)
    then have "abs (u \<bullet> v * sin (2 * t)) < 1"
      using assms
      apply (auto simp add: abs_mult)
      apply (subst mult.commute)
      apply (rule less_one_multI)
      apply (auto simp add: abs_mult inner_eq_vangle )
      by (auto simp: cos_vangle_eq_zero_iff_vangle dest!: ortho_imp_angle_pi_half)
    then show ?thesis
      by (subst mult.assoc sin_times_cos)+ auto
  qed
  have le: "0 \<le> 1 + 2 * (u \<bullet> v) * sin t * cos t"
  proof -
    have "\<bar>u \<bullet> v\<bar> \<le> norm u * norm v"
      by (rule Cauchy_Schwarz_ineq2)
    then have "abs (u \<bullet> v * sin (2 * t)) \<le> 1"
      by (auto simp add: abs_mult assms intro!: mult_le_one)
    then show ?thesis
      by (subst mult.assoc sin_times_cos)+ auto
  qed
  have "(norm (?w t))\<^sup>2 = (cos t)\<^sup>2 *\<^sub>R (norm u)\<^sup>2 + (sin t)\<^sup>2 *\<^sub>R (norm v)\<^sup>2 + 2 * (u \<bullet> v) * sin t * cos t"
    by (auto simp: conemem_def algebra_simps power2_norm_eq_inner)
      (auto simp: power2_eq_square inner_commute)
  also have "\<dots> = 1 + 2 * (u \<bullet> v) * sin t * cos t"
    by (auto simp: sin_squared_eq algebra_simps assms)
  finally have "(norm (conemem u v t))\<^sup>2 = 1 + 2 * (u \<bullet> v) * sin t * cos t" by simp
  moreover
  have "(norm (?w' t))\<^sup>2 = (cos t)\<^sup>2 *\<^sub>R (norm u')\<^sup>2 + (sin t)\<^sup>2 *\<^sub>R (norm v')\<^sup>2 + 2 * (u' \<bullet> v') * sin t * cos t"
    by (auto simp: conemem_def algebra_simps power2_norm_eq_inner)
      (auto simp: power2_eq_square inner_commute)
  ultimately
  have "(norm (?w' t) / norm (?w t))\<^sup>2 =
    ((cos t)\<^sup>2 *\<^sub>R (norm u')\<^sup>2 + (sin t)\<^sup>2 *\<^sub>R (norm v')\<^sup>2 + 2 * (u' \<bullet> v') * sin t * cos t) /
    (1 + 2 * (u \<bullet> v) * sin t * cos t)"
    (is "_ = (?a + ?b) / ?c")
    by (auto simp: divide_inverse power_mult_distrib) (auto simp: inverse_eq_divide power2_eq_square)
  also have "\<dots> \<ge> (e_pre\<^sup>2 + ?b) / ?c"
    apply (rule divide_right_mono)
     apply (rule add_right_mono)
    subgoal using assms e_pre_def
      apply (auto simp: min_def)
      subgoal by (auto simp: algebra_simps cos_squared_eq intro!: mult_right_mono power_mono)
      subgoal by (auto simp: algebra_simps sin_squared_eq intro!: mult_right_mono power_mono)
      done
    subgoal by (rule le)
    done
  also (xtrans)
  have inner_nonneg: "u' \<bullet> v' \<ge> 0"
    using angle_le(1) angle_pos vangle_bounds[of u' v']
    by (auto simp: inner_eq_vangle intro!: mult_nonneg_nonneg cos_ge_zero)
  from vangle_bounds[of u' v'] vangle_le_pi2[OF this]
  have u'v'e_pre: "u' \<bullet> v' \<ge> cos (vangle u' v') * e_pre\<^sup>2"
    apply (subst inner_eq_vangle)
    apply (rule mult_left_mono)
     apply (rule e_pre_le)
    apply (rule cos_ge_zero)
    by auto
  have "(e_pre\<^sup>2 + ?b) / ?c \<ge> (e_pre\<^sup>2 + 2 * (cos (vangle u' v') * e_pre\<^sup>2) * sin t * cos t) / ?c"
    (is "_ \<ge> ?ddd")
    apply (intro divide_right_mono add_left_mono mult_right_mono mult_left_mono u'v'e_pre)
    using \<open>t \<in> _\<close>
    by (auto intro!: mult_right_mono sin_ge_zero divide_right_mono le cos_ge_zero
        simp: sin_times_cos u'v'e_pre)
  also (xtrans) have "?ddd = e_pre\<^sup>2 * ((1 + 2 * cos (vangle u' v') * sin t * cos t) / ?c)" (is "_ = ?ddd")
    by (auto simp add: divide_simps algebra_simps)
  also (xtrans)
  have sc_ge_0: "0 \<le> sin t * cos t"
    using \<open>t \<in> _\<close>
    by (auto simp: assms cos_angle_le intro!: mult_nonneg_nonneg sin_ge_zero cos_ge_zero)
  have "?ddd \<ge> e_pre\<^sup>2"
    apply (subst mult_le_cancel_left1)
    apply (auto simp add: divide_simps split: if_splits)
      apply (rule mult_right_mono)
    using lt
    by (auto simp: assms inner_eq_vangle intro!: mult_right_mono sc_ge_0 cos_angle_le)
  finally (xtrans)
  have "(norm (conemem u' v' t))\<^sup>2 \<ge> (e_pre * norm (conemem u v t))\<^sup>2"
    by (simp add: divide_simps power_mult_distrib split: if_splits)
  then show "norm (conemem u' v' t) \<ge> e_pre * norm (conemem u v t)"
    using norm_imp_pos_and_ge power2_le_imp_le by blast
qed

lemma conemem_commute: "conemem a b t = conemem b a (pi / 2 - t)" if "0 \<le> t" "t \<le> pi / 2"
  using that by (auto simp: conemem_def cos_sin_eq algebra_simps)

lemma conesegment_commute: "conesegment a b = conesegment b a"
  apply (auto simp: conesegment_def )
   apply (subst conemem_commute)
  apply auto
   apply (subst conemem_commute)
    apply auto
  done


definition "conefield u v = cone hull (conesegment u v)"

lemma conefield_alt_def: "conefield u v = cone hull {u--v}"
  apply (auto simp: conesegment_def conefield_def cone_hull_expl in_segment)
  subgoal premises prems for c t
  proof -
    from prems
    have sc_pos: "sin t + cos t > 0"
      apply (cases "t = 0")
      subgoal
        by (rule add_nonneg_pos) auto
      subgoal
         by (auto intro!: add_pos_nonneg sin_gt_zero cos_ge_zero)
       done
    then have 1: "(sin t / (sin t + cos t) + cos t / (sin t + cos t)) = 1"
      by (auto simp: divide_simps)
    have "\<exists>c x. c > 0 \<and> 0 \<le> x \<and> x \<le> 1 \<and> c *\<^sub>R conemem u v t = (1 - x) *\<^sub>R u + x *\<^sub>R v"
      apply (auto simp: algebra_simps conemem_def)
      apply (rule exI[where x="1 / (sin t + cos t)"])
      using prems
      by (auto intro!: exI[where x="(1 / (sin t + cos t) * sin t)"] sc_pos
          divide_nonneg_nonneg sin_ge_zero add_nonneg_nonneg cos_ge_zero
          simp: scaleR_add_left[symmetric] 1 divide_le_eq_1)
    then obtain d x where dx: "d > 0" "conemem u v t = (1 / d) *\<^sub>R ((1 - x) *\<^sub>R u + x *\<^sub>R v)"
        "0 \<le> x" "x \<le> 1"
      by (auto simp: eq_vector_fraction_iff)
    show ?thesis
      apply (rule exI[where x="c / d"])
      using dx
      by (auto simp: intro!: divide_nonneg_nonneg prems )
  qed
  subgoal premises prems for c t
  proof -
    let ?x = "arctan (t / (1 - t))"
    let ?s = "t / sin ?x"
    have *: "c *\<^sub>R ((1 - t) *\<^sub>R u + t *\<^sub>R v) = (c * ?s) *\<^sub>R (cos ?x *\<^sub>R u + sin ?x *\<^sub>R v)"
      if "0 < t" "t < 1"
      using that
      by (auto simp: scaleR_add_right sin_arctan cos_arctan divide_simps)
    show ?thesis
      apply (cases "t = 0")
      subgoal
        apply simp
        apply (rule exI[where x=c])
        apply (rule exI[where x=u])
        using prems
        by (auto simp: conemem_def[abs_def] intro!: image_eqI[where x=0])
      subgoal apply (cases "t = 1")
        subgoal
          apply simp
          apply (rule exI[where x=c])
          apply (rule exI[where x=v])
          using prems
          by (auto simp: conemem_def[abs_def] intro!: image_eqI[where x="pi/2"])
        subgoal
          apply (rule exI[where x="(c * ?s)"])
          apply (rule exI[where x="(cos ?x *\<^sub>R u + sin ?x *\<^sub>R v)"])
          using prems * arctan_ubound[of "t / (1 - t)"] 
          apply (auto simp: conemem_def[abs_def]  intro!: imageI)
          by (auto simp: scaleR_add_right sin_arctan)
        done
      done
  qed
  done

lemma
  bounded_linear_image_cone_hull:
  assumes "bounded_linear F"
  shows "F ` (cone hull T) = cone hull (F ` T)"
proof -
  from assms interpret bounded_linear F .
  show ?thesis
    apply (auto simp: conefield_def cone_hull_expl closed_segment_def add scaleR)
     apply (auto simp: )
    apply (auto simp: add[symmetric] scaleR[symmetric])
    done
qed

lemma
  bounded_linear_image_conefield:
  assumes "bounded_linear F"
  shows "F ` conefield u v = conefield (F u) (F v)"
  unfolding conefield_def
  using assms
  by (auto simp: bounded_linear_image_conesegment bounded_linear_image_cone_hull)

lemma conefield_commute: "conefield x y = conefield y x"
  by (auto simp: conefield_def conesegment_commute)

lemma convex_conefield: "convex (conefield x y)"
  by (auto simp: conefield_alt_def convex_cone_hull)

lemma conefield_scaleRI: "v \<in> conefield (r *\<^sub>R x) y" if "v \<in> conefield x y" "r > 0"
  using that
  using \<open>r > 0\<close>
  unfolding conefield_alt_def cone_hull_expl
  apply (auto simp: in_segment)
proof goal_cases
  case (1 c u)
  let ?d = "c * (1 - u) / r + c * u"
  let ?t = "c * u / ?d"
  have "c * (1 - u) = ?d * (1 - ?t) * r" if "0 < u"
    using \<open>0 < r\<close> that(1) 1(3,5) mult_pos_pos
    by (force simp: divide_simps ac_simps ring_distribs[symmetric])
  then have eq1: "(c * (1 - u)) *\<^sub>R x = (?d * (1 - ?t) * r) *\<^sub>R x" if "0 < u"
    using that by simp
  have "c * u = ?d * ?t" if "u < 1"
    using \<open>0 < r\<close> that(1) 1(3,4,5) mult_pos_pos
    apply (auto simp: divide_simps ac_simps ring_distribs[symmetric])
  proof -
    assume "0 \<le> u"
      "0 < r"
      "1 - u + r * u = 0"
      "u < 1"
    then have False
      by (sos "((((A<0 * A<1) * R<1) + (([~1*r] * A=0) + ((A<=0 * R<1) * (R<1 * [r]^2)))))")
    then show "u = 0"
      by metis
  qed
  then have eq2: "(c * u) *\<^sub>R y = (?d * ?t) *\<^sub>R y" if "u < 1"
    using that by simp
  have *: "c *\<^sub>R ((1 - u) *\<^sub>R x + u *\<^sub>R y) = ?d *\<^sub>R ((1 - ?t) *\<^sub>R r *\<^sub>R x + ?t *\<^sub>R y)"
    if "0 < u" "u < 1"
    using that eq1 eq2
    by (auto simp: algebra_simps)
  show ?case
    apply (cases "u = 0")
    subgoal using 1 by (intro exI[where x="c / r"] exI[where x="r *\<^sub>R x"]) auto
    apply (cases "u = 1")
    subgoal using 1 by (intro exI[where x="c"] exI[where x="y"]) (auto intro!: exI[where x=1])
    subgoal
      apply (rule exI[where x="?d"])
      apply (rule exI[where x="((1 - ?t) *\<^sub>R r *\<^sub>R x + ?t *\<^sub>R y)"])
      apply (subst *)
      using 1
        apply (auto intro!: exI[where x = ?t])
      apply (auto simp: algebra_simps divide_simps)
      defer
    proof -
      assume a1: "c + c * (r * u) < c * u"
      assume a2: "0 \<le> c"
      assume a3: "0 \<le> u"
      assume a4: "u \<noteq> 0"
      assume a5: "0 < r"
      have "c + c * (r * u) \<le> c * u"
        using a1 less_eq_real_def by blast
      then show "c \<le> c * u"
        using a5 a4 a3 a2 by (metis (no_types) less_add_same_cancel1 less_eq_real_def
            mult_pos_pos order_trans real_scaleR_def real_vector.scale_zero_left)
    next
      assume a1: "0 \<le> c"
      assume a2: "u \<le> 1"
      have f3: "\<forall>x0. ((x0::real) < 1) = (\<not> 1 \<le> x0)"
        by auto
      have f4: "\<forall>x0. ((1::real) < x0) = (\<not> x0 \<le> 1)"
        by fastforce
      have "\<forall>x0 x1. ((x1::real) < x1 * x0) = (\<not> 0 \<le> x1 + - 1 * (x1 * x0))"
        by auto
      then have "(\<forall>r ra. ((r::real) < r * ra) = ((0 \<le> r \<longrightarrow> 1 < ra) \<and> (r \<le> 0 \<longrightarrow> ra < 1))) = (\<forall>r ra. (\<not> (0::real) \<le> r + - 1 * (r * ra)) = ((\<not> 0 \<le> r \<or> \<not> ra \<le> 1) \<and> (\<not> r \<le> 0 \<or> \<not> 1 \<le> ra)))"
        using f4 f3 by presburger
      then have "0 \<le> c + - 1 * (c * u)"
        using a2 a1 mult_less_cancel_left1 by blast
      then show "c * u \<le> c"
        by auto
    qed
    done
qed

lemma conefield_scaleRD: "v \<in> conefield x y" if "v \<in> conefield (r *\<^sub>R x) y" "r > 0"
  using conefield_scaleRI[OF that(1) positive_imp_inverse_positive[OF that(2)]] that(2)
  by auto

lemma conefield_scaleR: "conefield (r *\<^sub>R x) y = conefield x y" if "r > 0"
  using conefield_scaleRD conefield_scaleRI that
  by blast

lemma conefield_expansion_estimate:
  fixes u v::"'a::euclidean_space" and F::"'a \<Rightarrow> 'a"
  assumes "t \<in> {0 .. pi / 2}"
  assumes angle_pos: "0 < vangle u v" "vangle u v < pi / 2"
  assumes angle_le: "vangle (F u) (F v) \<le> vangle u v"
  assumes "bounded_linear F"
  assumes "x \<in> conefield u v"
  shows "norm (F x) \<ge> min (norm (F u)/norm u) (norm (F v)/norm v) * norm x"
proof cases
  assume [simp]: "x \<noteq> 0"
  from assms have [simp]: "u \<noteq> 0" "v \<noteq> 0" by auto
  interpret bounded_linear F by fact
  define u1 where "u1 = u /\<^sub>R norm u"
  define v1 where "v1 = v /\<^sub>R norm v"
  note \<open>x \<in> conefield u v\<close>
  also have \<open>conefield u v = conefield u1 v1\<close>
    by (auto simp: u1_def v1_def conefield_scaleR conefield_commute[of u])
  finally obtain c t where x: "x = c *\<^sub>R conemem u1 v1 t" "t \<in> {0 .. pi / 2}" "c \<ge> 0"
    by (auto simp: conefield_def cone_hull_expl conesegment_def)
  then have xc: "x /\<^sub>R c = conemem u1 v1 t"
    by (auto simp: divide_simps)
  also have "F \<dots> = conemem (F u1) (F v1) t"
    by (simp add: bounded_linear_image_conemem assms)
  also have "norm \<dots> \<ge> min (norm (F u1)) (norm (F v1)) * norm (conemem u1 v1 t)"
    apply (rule conemem_expansion_estimate)
    subgoal by fact
    subgoal using angle_pos by (simp add: u1_def v1_def vangle_scaleR)
    subgoal using angle_pos by (simp add: u1_def v1_def vangle_scaleR)
    subgoal using angle_le by (simp add: u1_def v1_def scaleR vangle_scaleR)
    subgoal using angle_le by (simp add: u1_def v1_def scaleR vangle_scaleR)
    subgoal using angle_le by (simp add: u1_def v1_def scaleR vangle_scaleR)
    done
  finally show "norm (F x) \<ge> min (norm (F u)/norm u) (norm (F v)/norm v) * norm x"
    unfolding xc[symmetric] scaleR u1_def v1_def norm_scaleR x
    using \<open>c \<ge> 0\<close>
    by (simp add: divide_simps split: if_splits)
qed simp

lemma conefield_rightI:
  assumes ij: "i \<in> Basis" "j \<in> Basis" and ij_neq: "i \<noteq> j"
  assumes "y \<in> {y1 .. y2}"
  shows "(i + y *\<^sub>R j) \<in> conefield (i + y1 *\<^sub>R j) (i + y2 *\<^sub>R j)"
  unfolding conefield_alt_def
  apply (rule hull_inc)
  using assms
  by (auto simp: in_segment divide_simps inner_Basis algebra_simps
      intro!: exI[where x="(y - y1) / (y2 - y1)"] euclidean_eqI[where 'a='a] )

lemma conefield_right_vangleI:
  assumes ij: "i \<in> Basis" "j \<in> Basis" and ij_neq: "i \<noteq> j"
  assumes "y \<in> {y1 .. y2}" "y1 < y2"
  shows "(i + y *\<^sub>R j) \<in> conefield (i + y1 *\<^sub>R j) (i + y2 *\<^sub>R j)"
  unfolding conefield_alt_def
  apply (rule hull_inc)
  using assms
  by (auto simp: in_segment divide_simps inner_Basis algebra_simps
      intro!: exI[where x="(y - y1) / (y2 - y1)"] euclidean_eqI[where 'a='a] )

lemma cone_conefield[intro, simp]: "cone (conefield x y)"
  unfolding conefield_def
  by (rule cone_cone_hull)

lemma conefield_mk_rightI:
  assumes ij: "i \<in> Basis" "j \<in> Basis" and ij_neq: "i \<noteq> j"
  assumes "(i + (y / x) *\<^sub>R j) \<in> conefield (i + (y1 / x1) *\<^sub>R j) (i + (y2 / x2) *\<^sub>R j)"
  assumes "x > 0" "x1 > 0" "x2 > 0"
  shows "(x *\<^sub>R i + y *\<^sub>R j) \<in> conefield (x1 *\<^sub>R i + y1 *\<^sub>R j) (x2 *\<^sub>R i + y2 *\<^sub>R j)"
proof -
  have rescale: "(x *\<^sub>R i + y *\<^sub>R j) = x *\<^sub>R (i + (y / x) *\<^sub>R j)" if "x > 0" for x y
    using that by (auto simp: algebra_simps)
  show ?thesis
    unfolding rescale[OF \<open>x > 0\<close>] rescale[OF \<open>x1 > 0\<close>] rescale[OF \<open>x2 > 0\<close>]
      conefield_scaleR[OF \<open>x1 > 0\<close>]
    apply (subst conefield_commute)
    unfolding conefield_scaleR[OF \<open>x2 > 0\<close>]
    apply (rule mem_cone)
      apply simp
     apply (subst conefield_commute)
    by (auto intro!: assms less_imp_le)
qed

lemma conefield_prod3I:
  assumes "x > 0" "x1 > 0" "x2 > 0"
  assumes "y1 / x1 \<le> y / x" "y / x \<le> y2 / x2"
  shows "(x, y, 0) \<in> (conefield (x1, y1, 0) (x2, y2, 0)::(real*real*real) set)"
proof -
  have "(x *\<^sub>R (1, 0, 0) + y *\<^sub>R (0, 1, 0)) \<in>
    (conefield (x1 *\<^sub>R (1, 0, 0) + y1 *\<^sub>R (0, 1, 0)) (x2 *\<^sub>R (1, 0, 0) + y2 *\<^sub>R (0, 1, 0))::(real*real*real) set)"
    apply (rule conefield_mk_rightI)
    subgoal by (auto simp: Basis_prod_def zero_prod_def)
    subgoal by (auto simp: Basis_prod_def zero_prod_def)
    subgoal by (auto simp: Basis_prod_def zero_prod_def)
    subgoal using assms by (intro conefield_rightI) (auto simp: Basis_prod_def zero_prod_def)
    by (auto intro: assms)
  then show ?thesis by simp
qed

end
