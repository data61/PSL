theory Poincare_Between
  imports Poincare_Distance
begin

(* ------------------------------------------------------------------ *)
section\<open>H-betweenness in the Poincar\'e model\<close>
(* ------------------------------------------------------------------ *)

subsection \<open>H-betwenness expressed by a cross-ratio\<close>

text\<open>The point $v$ is h-between $u$ and $w$ if the cross-ratio between the pairs $u$ and $w$ and $v$
and inverse of $v$ is real and negative.\<close>
definition poincare_between :: "complex_homo \<Rightarrow> complex_homo \<Rightarrow> complex_homo \<Rightarrow> bool" where
  "poincare_between u v w \<longleftrightarrow>
         u = v \<or> v = w \<or>
         (let cr = cross_ratio u v w (inversion v)
           in is_real (to_complex cr) \<and> Re (to_complex cr) < 0)"

subsubsection \<open>H-betwenness is preserved by h-isometries\<close>

text \<open>Since they preserve cross-ratio and inversion, h-isometries (unit disc preserving Möbius
transformations and conjugation) preserve h-betweeness.\<close>

lemma unit_disc_fix_moebius_preserve_poincare_between [simp]:
  assumes "unit_disc_fix M" and "u \<in> unit_disc" and "v \<in> unit_disc" and "w \<in> unit_disc"
  shows "poincare_between (moebius_pt M u) (moebius_pt M v) (moebius_pt M w) \<longleftrightarrow>
         poincare_between u v w"
proof (cases "u = v \<or> v = w")
  case True
  thus ?thesis
    using assms
    unfolding poincare_between_def
    by auto
next
  case False
  moreover
  hence "moebius_pt M u \<noteq> moebius_pt M v \<and> moebius_pt M v \<noteq> moebius_pt M w"
    by auto
  moreover
  have "v \<noteq> inversion v" "w \<noteq> inversion v"
    using inversion_noteq_unit_disc[of v w]
    using inversion_noteq_unit_disc[of v v]
    using \<open>v \<in> unit_disc\<close> \<open>w \<in> unit_disc\<close>
    by auto
  ultimately
  show ?thesis
    using assms
    using unit_circle_fix_moebius_pt_inversion[of M v, symmetric]
    unfolding poincare_between_def
    by (simp del: unit_circle_fix_moebius_pt_inversion)
qed

lemma conjugate_preserve_poincare_between [simp]:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc" and "w \<in> unit_disc"
  shows "poincare_between (conjugate u) (conjugate v) (conjugate w) \<longleftrightarrow>
         poincare_between u v w"
proof (cases "u = v \<or> v = w")
  case True
  thus ?thesis
    using assms
    unfolding poincare_between_def
    by auto
next
  case False
  moreover
  hence "conjugate u \<noteq> conjugate v \<and> conjugate v \<noteq> conjugate w"
    using conjugate_inj by blast
  moreover
  have "v \<noteq> inversion v" "w \<noteq> inversion v"
    using inversion_noteq_unit_disc[of v w]
    using inversion_noteq_unit_disc[of v v]
    using \<open>v \<in> unit_disc\<close> \<open>w \<in> unit_disc\<close>
    by auto
  ultimately
  show ?thesis
    using assms
    using conjugate_cross_ratio[of v w "inversion v" u]
    unfolding poincare_between_def
    by (metis conjugate_id_iff conjugate_involution inversion_def inversion_sym o_apply)
qed


subsubsection \<open>Some elementary properties of h-betwenness\<close>

lemma poincare_between_nonstrict [simp]:
  shows "poincare_between u u v" and "poincare_between u v v"
  by (simp_all add: poincare_between_def)                       

lemma poincare_between_sandwich:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc"
  assumes "poincare_between u v u"
  shows "u = v"
proof (rule ccontr)
  assume "\<not> ?thesis"
  thus False
    using assms
    using inversion_noteq_unit_disc[of v u]
    using cross_ratio_1[of v u "inversion v"]
    unfolding poincare_between_def Let_def
    by auto
qed

lemma poincare_between_rev:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc" and "w \<in> unit_disc"
  shows "poincare_between u v w \<longleftrightarrow> poincare_between w v u"       
  using assms 
  using inversion_noteq_unit_disc[of v w]
  using inversion_noteq_unit_disc[of v u]
  using cross_ratio_commute_13[of u v w "inversion v"]
  using cross_ratio_not_inf[of w "inversion v" v u]
  using cross_ratio_not_zero[of w v u "inversion v"]
  using inf_or_of_complex[of "cross_ratio w v u (inversion v)"]
  unfolding poincare_between_def
  by (auto simp add: Let_def Im_complex_div_eq_0 Re_divide divide_less_0_iff)

subsubsection \<open>H-betwenness and h-collinearity\<close>

text\<open>Three points can be in an h-between relation only when they are h-collinear.\<close>
lemma poincare_between_poincare_collinear [simp]:       
  assumes in_disc: "u \<in> unit_disc"  "v \<in> unit_disc"  "w \<in> unit_disc"
  assumes betw: "poincare_between u v w"
  shows "poincare_collinear {u, v, w}"
proof (cases "u = v \<or> v = w")
  case True
  thus ?thesis
    using assms
    by auto
next
  case False
  hence distinct: "distinct [u, v, w, inversion v]"
    using in_disc inversion_noteq_unit_disc[of v v] inversion_noteq_unit_disc[of v u] inversion_noteq_unit_disc[of v w]
    using betw poincare_between_sandwich[of w v]
    by (auto simp add: poincare_between_def Let_def)

  then obtain H where *: "{u, v, w, inversion v} \<subseteq> circline_set H"
    using assms
    unfolding poincare_between_def
    using four_points_on_circline_iff_cross_ratio_real[of u v w "inversion v"]
    by auto
  hence "H = poincare_line u v"
    using assms distinct
    using unique_circline_set[of u v "inversion v"]
    using poincare_line[of u v] poincare_line_inversion[of u v]
    unfolding circline_set_def
    by auto
  thus ?thesis
    using * assms False
    unfolding poincare_collinear_def
    by (rule_tac x="poincare_line u v" in exI) simp
qed

lemma poincare_between_poincare_line_uvz:
  assumes "u \<noteq> v" and "u \<in> unit_disc" and "v \<in> unit_disc" and
          "z \<in> unit_disc" and "poincare_between u v z"
  shows "z \<in> circline_set (poincare_line u v)"
  using assms
  using poincare_between_poincare_collinear[of u v z]
  using unique_poincare_line[OF assms(1-3)]
  unfolding poincare_collinear_def
  by auto

lemma poincare_between_poincare_line_uzv:
  assumes "u \<noteq> v" and "u \<in> unit_disc" and "v \<in> unit_disc" and
          "z \<in> unit_disc" "poincare_between u z v"
  shows "z \<in> circline_set (poincare_line u v)"
  using assms
  using poincare_between_poincare_collinear[of u z v]
  using unique_poincare_line[OF assms(1-3)]
  unfolding poincare_collinear_def
  by auto

subsubsection \<open>H-betweeness on Euclidean segments\<close> 

text\<open>If the three points lie on an h-line that is a Euclidean line (e.g., if it contains zero),
h-betweenness can be characterized much simpler than in the definition.\<close>

lemma poincare_between_x_axis_u0v:
  assumes "is_real u'" and "u' \<noteq> 0" and "v' \<noteq> 0"
  shows "poincare_between (of_complex u') 0\<^sub>h (of_complex v') \<longleftrightarrow> is_real v' \<and> Re u' * Re v' < 0"
proof-
  have "Re u' \<noteq> 0"
    using \<open>is_real u'\<close> \<open>u' \<noteq> 0\<close>
    using complex_eq_if_Re_eq
    by auto
  have nz: "of_complex u' \<noteq> 0\<^sub>h" "of_complex v' \<noteq> 0\<^sub>h"
    by (simp_all add: \<open>u' \<noteq> 0\<close> \<open>v' \<noteq> 0\<close>)
  hence "0\<^sub>h \<noteq> of_complex v'"
    by metis

  let ?cr = "cross_ratio (of_complex u') 0\<^sub>h (of_complex v') \<infinity>\<^sub>h"
  have "is_real (to_complex ?cr) \<and> Re (to_complex ?cr) < 0 \<longleftrightarrow> is_real v' \<and> Re u' * Re v' < 0"
    using cross_ratio_0inf[of v' u'] \<open>v' \<noteq> 0\<close> \<open>u' \<noteq> 0\<close> \<open>is_real u'\<close>
    by (metis Re_complex_div_lt_0 Re_mult_real complex_cnj_divide divide_cancel_left eq_cnj_iff_real to_complex_of_complex)
  thus ?thesis
    unfolding poincare_between_def inversion_zero
    using \<open>of_complex u' \<noteq> 0\<^sub>h\<close> \<open>0\<^sub>h \<noteq> of_complex v'\<close>
    by simp
qed

lemma poincare_between_u0v:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc" and "u \<noteq> 0\<^sub>h" and "v \<noteq> 0\<^sub>h"
  shows "poincare_between u 0\<^sub>h v \<longleftrightarrow> (\<exists> k < 0. to_complex u = cor k * to_complex v)" (is "?P u v")
proof (cases "u = v")
  case True
  thus ?thesis
    using assms
    using inf_or_of_complex[of v]
    using poincare_between_sandwich[of u "0\<^sub>h"]      
    by auto
next                                                 
  case False
  have "\<forall> u. u \<in> unit_disc \<and> u \<noteq> 0\<^sub>h \<longrightarrow> ?P u v" (is "?P' v")
  proof (rule wlog_rotation_to_positive_x_axis)
    fix \<phi> v
    let ?M = "moebius_pt (moebius_rotation \<phi>)"
    assume 1: "v \<in> unit_disc" "v \<noteq> 0\<^sub>h"
    assume 2: "?P' (?M v)"
    show "?P' v"
    proof (rule allI, rule impI, (erule conjE)+)
      fix u
      assume 3: "u \<in> unit_disc" "u \<noteq> 0\<^sub>h"  
      have "poincare_between (?M u) 0\<^sub>h (?M v) \<longleftrightarrow> poincare_between u 0\<^sub>h v"
        using \<open>u \<in> unit_disc\<close> \<open>v \<in> unit_disc\<close>
        using unit_disc_fix_moebius_preserve_poincare_between unit_disc_fix_rotation zero_in_unit_disc 
        by fastforce
      thus "?P u v"
        using 1 2[rule_format, of "?M u"] 3
        using inf_or_of_complex[of u] inf_or_of_complex[of v]
        by auto
    qed
  next
    fix x
    assume 1: "is_real x" "0 < Re x" "Re x < 1"
    hence "x \<noteq> 0"
      by auto
    show "?P' (of_complex x)"    
    proof (rule allI, rule impI, (erule conjE)+)
      fix u
      assume 2: "u \<in> unit_disc" "u \<noteq> 0\<^sub>h"
      then obtain u' where "u = of_complex u'"
        using inf_or_of_complex[of u]
        by auto
      show "?P u (of_complex x)"
        using 1 2 \<open>x \<noteq> 0\<close> \<open>u = of_complex u'\<close>
        using poincare_between_rev[of u "0\<^sub>h" "of_complex x"]
        using poincare_between_x_axis_u0v[of x u'] \<open>is_real x\<close>
        apply (auto simp add: cmod_eq_Re)
        apply (rule_tac x="Re u' / Re x" in exI, simp add: divide_neg_pos algebra_split_simps)
        using mult_neg_pos mult_pos_neg
        by blast
    qed
  qed fact+
  thus ?thesis
    using assms
    by auto
qed

lemma poincare_between_u0v_polar_form:
  assumes "x \<in> unit_disc" and "y \<in> unit_disc" and "x \<noteq> 0\<^sub>h" and "y \<noteq> 0\<^sub>h" and 
          "to_complex x = cor rx * cis \<phi>" "to_complex y = cor ry * cis \<phi>"
  shows "poincare_between x 0\<^sub>h y \<longleftrightarrow> rx * ry < 0" (is "?P x y rx ry")
proof-
  from assms have "rx \<noteq> 0" "ry \<noteq> 0"
    using inf_or_of_complex[of x] inf_or_of_complex[of y]
    by auto

  have "(\<exists>k<0. cor rx = cor k * cor ry ) = (rx * ry < 0)"
  proof
    assume "\<exists>k<0. cor rx = cor k * cor ry"
    then obtain k where "k < 0" "cor rx = cor k * cor ry"
      by auto
    hence "rx = k * ry"
      using of_real_eq_iff
      by fastforce
    thus "rx * ry < 0" 
      using \<open>k < 0\<close> \<open>rx \<noteq> 0\<close> \<open>ry \<noteq> 0\<close>
      by (smt divisors_zero mult_nonneg_nonpos mult_nonpos_nonpos zero_less_mult_pos2)
  next
    assume "rx * ry < 0"
    hence "rx = (rx/ry)*ry" "rx / ry < 0"
      using \<open>rx \<noteq> 0\<close> \<open>ry \<noteq> 0\<close>
      by (auto simp add: divide_less_0_iff algebra_split_simps)
    thus "\<exists>k<0. cor rx = cor k * cor ry"
      using \<open>rx \<noteq> 0\<close> \<open>ry \<noteq> 0\<close>
      by (rule_tac x="rx / ry" in exI, simp)
  qed
  thus ?thesis
    using assms                                 
    using poincare_between_u0v[OF assms(1-4)]
    by auto
qed

lemma poincare_between_x_axis_0uv:
  fixes x y :: real
  assumes "-1 < x" and "x < 1" and "x \<noteq> 0"
  assumes "-1 < y" and "y < 1" and "y \<noteq> 0"
  shows "poincare_between 0\<^sub>h (of_complex x) (of_complex y) \<longleftrightarrow>
        (x < 0 \<and> y < 0 \<and> y \<le> x) \<or> (x > 0 \<and> y > 0 \<and> x \<le> y)" (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "x = y")
  case True
  thus ?thesis
    using assms
    unfolding poincare_between_def
    by auto
next
  case False
  let ?x = "of_complex x" and ?y = "of_complex y"

  have "?x \<in> unit_disc" "?y \<in> unit_disc"
    using assms
    by auto

  have distinct: "distinct [0\<^sub>h, ?x, ?y, inversion ?x]"
    using \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> \<open>x \<noteq> y\<close> \<open>?x \<in> unit_disc\<close> \<open>?y \<in> unit_disc\<close>
    using inversion_noteq_unit_disc[of ?x ?y]
    using inversion_noteq_unit_disc[of ?x ?x]
    using inversion_noteq_unit_disc[of ?x "0\<^sub>h"]
    using of_complex_inj[of x y]
    by (metis distinct_length_2_or_more distinct_singleton of_complex_zero_iff of_real_eq_0_iff of_real_eq_iff zero_in_unit_disc)

  let ?cr = "cross_ratio 0\<^sub>h ?x ?y (inversion ?x)"
  have "Re (to_complex ?cr) = x\<^sup>2 * (x*y - 1) / (x * (y - x))"
    using \<open>x \<noteq> 0\<close> \<open>x \<noteq> y\<close>
    unfolding inversion_def
    by simp (transfer, transfer, auto simp add: vec_cnj_def power2_eq_square field_simps split: if_split_asm)
  moreover
  { 
    fix a b :: real
    assume "b \<noteq> 0"
    hence "a < 0 \<longleftrightarrow> b\<^sup>2 * a < (0::real)"
      by (metis mult.commute mult_eq_0_iff mult_neg_pos mult_pos_pos not_less_iff_gr_or_eq not_real_square_gt_zero power2_eq_square)
  }
  hence "x\<^sup>2 * (x*y - 1) < 0"
    using assms
    by (smt minus_mult_minus mult_le_cancel_left1)
  moreover
  have "x * (y - x) > 0 \<longleftrightarrow> ?rhs"
    using \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> \<open>x \<noteq> y\<close>
    by (smt mult_le_0_iff)
  ultimately
  have *: "Re (to_complex ?cr) < 0 \<longleftrightarrow> ?rhs"
    by (simp add: divide_less_0_iff)

  show ?thesis
  proof
    assume ?lhs
    have "is_real (to_complex ?cr)" "Re (to_complex ?cr) < 0"
      using \<open>?lhs\<close> distinct
      unfolding poincare_between_def Let_def
      by auto
    thus ?rhs
      using *
      by simp
  next
    assume ?rhs
    hence "Re (to_complex ?cr) < 0"
      using *
      by simp
    moreover
    have "{0\<^sub>h, of_complex (cor x), of_complex (cor y), inversion (of_complex (cor x))} \<subseteq> circline_set x_axis"
      using \<open>x \<noteq> 0\<close> is_real_inversion[of "cor x"]
      using inf_or_of_complex[of "inversion ?x"]
      by (auto simp del: inversion_of_complex)
    hence "is_real (to_complex ?cr)"
      using four_points_on_circline_iff_cross_ratio_real[OF distinct]
      by auto
    ultimately
    show ?lhs
      using distinct
      unfolding poincare_between_def Let_def
      by auto
  qed
qed

lemma poincare_between_0uv:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc" and "u \<noteq> 0\<^sub>h" and "v \<noteq> 0\<^sub>h"
  shows "poincare_between 0\<^sub>h u v \<longleftrightarrow>
         (let u' = to_complex u; v' = to_complex v in arg u' = arg v' \<and> cmod u' \<le> cmod v')" (is "?P u v")
proof (cases "u = v")
  case True
  thus ?thesis
    by simp
next
  case False
  have "\<forall> v. v \<in> unit_disc \<and> v \<noteq> 0\<^sub>h \<and> v \<noteq> u \<longrightarrow> (poincare_between 0\<^sub>h u v \<longleftrightarrow> (let u' = to_complex u; v' = to_complex v in arg u' = arg v' \<and> cmod u' \<le> cmod v'))" (is "?P' u")
  proof (rule wlog_rotation_to_positive_x_axis)
    show "u \<in> unit_disc" "u \<noteq> 0\<^sub>h"
      by fact+
  next
    fix x
    assume *: "is_real x" "0 < Re x" "Re x < 1"
    hence "of_complex x \<in> unit_disc" "of_complex x \<noteq> 0\<^sub>h" "of_complex x \<in> circline_set x_axis"
      unfolding circline_set_x_axis
      by (auto simp add: cmod_eq_Re)
    show "?P' (of_complex x)"
    proof safe
      fix v
      assume "v \<in> unit_disc" "v \<noteq> 0\<^sub>h" "v \<noteq> of_complex x" "poincare_between 0\<^sub>h (of_complex x) v"
      hence "v \<in> circline_set x_axis"
        using poincare_between_poincare_line_uvz[of "0\<^sub>h" "of_complex x" v]
        using poincare_line_0_real_is_x_axis[of "of_complex x"]
        using \<open>of_complex x \<noteq> 0\<^sub>h\<close> \<open>v \<noteq> 0\<^sub>h\<close> \<open>v \<noteq> of_complex x\<close> \<open>of_complex x \<in> unit_disc\<close> \<open>of_complex x \<in> circline_set x_axis\<close>
        by auto
      obtain v' where "v = of_complex v'"
        using \<open>v \<in> unit_disc\<close>
        using inf_or_of_complex[of v]
        by auto
      hence **: "v = of_complex v'" "-1 < Re v'" "Re v' < 1" "Re v' \<noteq> 0" "is_real v'"
        using \<open>v \<in> unit_disc\<close> \<open>v \<noteq> 0\<^sub>h\<close> \<open>v \<in> circline_set x_axis\<close> of_complex_inj[of v']
        unfolding circline_set_x_axis
        by (auto simp add: cmod_eq_Re real_imag_0)
      show "let u' = to_complex (of_complex x); v' = to_complex v in arg u' = arg v' \<and> cmod u' \<le> cmod v'"
        using poincare_between_x_axis_0uv[of "Re x" "Re v'"] * **
        using \<open>poincare_between 0\<^sub>h (of_complex x) v\<close>
        using arg_complex_of_real_positive[of "Re x"] arg_complex_of_real_negative[of "Re x"]
        using arg_complex_of_real_positive[of "Re v'"] arg_complex_of_real_negative[of "Re v'"]
        by (auto simp add: cmod_eq_Re)
    next
      fix v
      assume "v \<in> unit_disc" "v \<noteq> 0\<^sub>h" "v \<noteq> of_complex x"
      then obtain v' where **: "v = of_complex v'" "v' \<noteq> 0" "v' \<noteq> x"
        using inf_or_of_complex[of v]
        by auto blast
      assume "let u' = to_complex (of_complex x); v' = to_complex v in arg u' = arg v' \<and> cmod u' \<le> cmod v'"
      hence ***: "Re x < 0 \<and> Re v' < 0 \<and> Re v' \<le> Re x \<or> 0 < Re x \<and> 0 < Re v' \<and> Re x \<le> Re v'" "is_real v'"
        using arg_pi_iff[of x] arg_pi_iff[of v']
        using arg_0_iff[of x] arg_0_iff[of v']
        using * **
        by (smt cmod_Re_le_iff to_complex_of_complex)+
      have "-1 < Re v'" "Re v' < 1" "Re v' \<noteq> 0" "is_real v'"
        using \<open>v \<in> unit_disc\<close> ** \<open>is_real v'\<close>
        by (auto simp add: cmod_eq_Re complex_eq_if_Re_eq)
      thus "poincare_between 0\<^sub>h (of_complex x) v"
        using poincare_between_x_axis_0uv[of "Re x" "Re v'"] * ** ***
        by simp
    qed
  next
    fix \<phi> u
    assume "u \<in> unit_disc" "u \<noteq> 0\<^sub>h"
    let ?M = "moebius_rotation \<phi>"
    assume *: "?P' (moebius_pt ?M u)"
    show "?P' u"
    proof (rule allI, rule impI, (erule conjE)+)
      fix v
      assume "v \<in> unit_disc" "v \<noteq> 0\<^sub>h" "v \<noteq> u"
      have "moebius_pt ?M v \<noteq> moebius_pt ?M u"
        using \<open>v \<noteq> u\<close>
        by auto
      obtain u' v' where "v = of_complex v'" "u = of_complex u'" "v' \<noteq> 0" "u' \<noteq> 0"
        using inf_or_of_complex[of u] inf_or_of_complex[of v]
        using \<open>v \<in> unit_disc\<close> \<open>u \<in> unit_disc\<close> \<open>v \<noteq> 0\<^sub>h\<close> \<open>u \<noteq> 0\<^sub>h\<close>
        by auto
      thus "?P u v"
        using *[rule_format, of "moebius_pt ?M v"]
        using \<open>moebius_pt ?M v \<noteq> moebius_pt ?M u\<close>
        using unit_disc_fix_moebius_preserve_poincare_between[of ?M "0\<^sub>h" u v]
        using \<open>v \<in> unit_disc\<close> \<open>u \<in> unit_disc\<close> \<open>v \<noteq> 0\<^sub>h\<close> \<open>u \<noteq> 0\<^sub>h\<close>
        using arg_mult_eq[of "cis \<phi>" u' v']
        by simp (auto simp add: arg_mult)
    qed
  qed
  thus ?thesis
    using assms False
    by auto
qed

lemma poincare_between_y_axis_0uv:
  fixes x y :: real
  assumes "-1 < x" and "x < 1" and "x \<noteq> 0"
  assumes "-1 < y" and "y < 1" and "y \<noteq> 0"
  shows "poincare_between 0\<^sub>h (of_complex (\<i> * x)) (of_complex (\<i> * y)) \<longleftrightarrow>
        (x < 0 \<and> y < 0 \<and> y \<le> x) \<or> (x > 0 \<and> y > 0 \<and> x \<le> y)" (is "?lhs \<longleftrightarrow> ?rhs")
  using assms
  using poincare_between_0uv[of "of_complex (\<i> * x)" "of_complex (\<i> * y)"]
  using arg_pi2_iff[of "\<i> * cor x"] arg_pi2_iff[of "\<i> * cor y"]
  using arg_minus_pi2_iff[of "\<i> * cor x"] arg_minus_pi2_iff[of "\<i> * cor y"]
  apply simp
  apply (cases "x > 0")
  apply (cases "y > 0", simp, simp)
  apply (cases "y > 0")
  apply simp
  using pi_gt_zero apply linarith
  apply simp
  done

lemma poincare_between_x_axis_uvw:
  fixes x y z :: real
  assumes "-1 < x" and "x < 1" 
  assumes "-1 < y" and "y < 1" and "y \<noteq> x"
  assumes "-1 < z" and "z < 1" and "z \<noteq> x"
  shows "poincare_between (of_complex x) (of_complex y) (of_complex z) \<longleftrightarrow>
        (y < x \<and> z < x \<and> z \<le> y) \<or> (y > x \<and> z > x \<and> y \<le> z)"  (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "x = 0 \<or> y = 0 \<or> z = 0")
  case True
  thus ?thesis
  proof (cases "x = 0")
    case True
    thus ?thesis
      using poincare_between_x_axis_0uv assms
      by simp
  next
    case False
    show ?thesis
    proof (cases "z = 0")
      case True
      thus ?thesis
        using poincare_between_x_axis_0uv assms poincare_between_rev
        by (smt norm_of_real of_complex_zero of_real_0 poincare_between_nonstrict(2) unit_disc_iff_cmod_lt_1)
    next
      case False
      have "y = 0"
        using `x \<noteq> 0` `z \<noteq> 0` `x = 0 \<or> y = 0 \<or> z = 0`
        by simp

      have "poincare_between (of_complex x) 0\<^sub>h (of_complex z) = (is_real z \<and> x * z < 0)"
        using `x \<noteq> 0` `z \<noteq> 0` poincare_between_x_axis_u0v 
        by auto
      moreover
      have "x * z < 0 \<longleftrightarrow> ?rhs"
        using True \<open>x \<noteq> 0\<close> \<open>z \<noteq> 0\<close>
        by (smt zero_le_mult_iff)
      ultimately
      show ?thesis
        using `y = 0`
        by auto
    qed
  qed
next
  case False
  thus ?thesis
  proof (cases "z = y")
    case True
    thus ?thesis
      using assms
      unfolding poincare_between_def
      by auto
  next
    case False
    let ?x = "of_complex x" and ?y = "of_complex y" and ?z = "of_complex z"
  
    have "?x \<in> unit_disc" "?y \<in> unit_disc" "?z \<in> unit_disc"
      using assms
      by auto
  
    have distinct: "distinct [?x, ?y, ?z, inversion ?y]"
      using \<open>y \<noteq> x\<close> \<open>z \<noteq> x\<close> False \<open>?x \<in> unit_disc\<close> \<open>?y \<in> unit_disc\<close> \<open>?z \<in> unit_disc\<close>
      using inversion_noteq_unit_disc[of ?y ?y]
      using inversion_noteq_unit_disc[of ?y ?x]
      using inversion_noteq_unit_disc[of ?y ?z]
      using of_complex_inj[of x y]  of_complex_inj[of y z]  of_complex_inj[of x z]
      by auto

    have "cor y * cor x \<noteq> 1"
      using assms
      by (smt minus_mult_minus mult_less_cancel_left2 mult_less_cancel_right2 of_real_1 of_real_eq_iff of_real_mult)
  
    let ?cr = "cross_ratio ?x ?y ?z (inversion ?y)"
    have "Re (to_complex ?cr) = (x - y) * (z*y - 1)/ ((x*y - 1)*(z - y))"
    proof-
      have " \<And>y x z. \<lbrakk>y \<noteq> x; z \<noteq> x; z \<noteq> y; cor y * cor x \<noteq> 1; x \<noteq> 0; y \<noteq> 0; z \<noteq> 0\<rbrakk> \<Longrightarrow> 
           (y * y + y * (y * (x * z)) - (y * x + y * (y * (y * z)))) /
           (y * y + y * (y * (x * z)) - (y * z + y * (y * (y * x)))) =
           (y + y * (x * z) - (x + y * (y * z))) / (y + y * (x * z) - (z + y * (y * x)))"
        by (metis (no_types, hide_lams) ab_group_add_class.ab_diff_conv_add_uminus distrib_left mult_divide_mult_cancel_left_if mult_minus_right)
      thus ?thesis
        using \<open>y \<noteq> x\<close> \<open>z \<noteq> x\<close> False \<open>\<not> (x = 0 \<or> y = 0 \<or> z = 0)\<close>
        using \<open>cor y * cor x \<noteq> 1\<close>
        unfolding inversion_def
        by (transfer, transfer, auto simp add: vec_cnj_def power2_eq_square field_simps split: if_split_asm)
    qed
      
    moreover
    have "(x*y - 1) < 0"
      using assms
      by (smt minus_mult_minus mult_less_cancel_right2 zero_less_mult_iff)
    moreover
    have "(z*y - 1) < 0"
      using assms
      by (smt minus_mult_minus mult_less_cancel_right2 zero_less_mult_iff)
    moreover
    have "(x - y) / (z - y) < 0 \<longleftrightarrow> ?rhs"
      using \<open>y \<noteq> x\<close> \<open>z \<noteq> x\<close> False \<open>\<not> (x = 0 \<or> y = 0 \<or> z = 0)\<close>
      by (smt divide_less_cancel divide_nonneg_nonpos divide_nonneg_pos divide_nonpos_nonneg divide_nonpos_nonpos)
    ultimately
    have *: "Re (to_complex ?cr) < 0 \<longleftrightarrow> ?rhs"
      by (smt algebra_split_simps(24) minus_divide_left zero_less_divide_iff zero_less_mult_iff)
    show ?thesis
    proof
      assume ?lhs
      have "is_real (to_complex ?cr)" "Re (to_complex ?cr) < 0"
        using \<open>?lhs\<close> distinct
        unfolding poincare_between_def Let_def
        by auto
      thus ?rhs
        using *
        by simp
    next
      assume ?rhs
      hence "Re (to_complex ?cr) < 0"
        using *
        by simp
      moreover
      have "{of_complex (cor x), of_complex (cor y), of_complex (cor z), inversion (of_complex (cor y))} \<subseteq> circline_set x_axis"
        using \<open>\<not> (x = 0 \<or> y = 0 \<or> z = 0)\<close> is_real_inversion[of "cor y"]
        using inf_or_of_complex[of "inversion ?y"]
        by (auto simp del: inversion_of_complex)
      hence "is_real (to_complex ?cr)"
        using four_points_on_circline_iff_cross_ratio_real[OF distinct]
        by auto
      ultimately
      show ?lhs
        using distinct
        unfolding poincare_between_def Let_def
        by auto
    qed
  qed
qed

subsubsection \<open>H-betweenness and h-collinearity\<close>

text\<open>For three h-collinear points at least one of the three possible h-betweeness relations must
hold.\<close>
lemma poincare_collinear3_between:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc" and "w \<in> unit_disc"
  assumes "poincare_collinear {u, v, w}"
  shows "poincare_between u v w \<or> poincare_between u w v \<or> poincare_between v u w" (is "?P' u v w")
proof (cases "u=v")
  case True
  thus ?thesis
    using assms
    by auto
next
  case False
  have "\<forall> w. w \<in> unit_disc \<and> poincare_collinear {u, v, w} \<longrightarrow> ?P' u v w" (is "?P u v")
  proof (rule wlog_positive_x_axis[where P="?P"])
    fix x
    assume x: "is_real x" "0 < Re x" "Re x < 1"
    hence "x \<noteq> 0"
      using complex.expand[of x 0]
      by auto
    hence *: "poincare_line 0\<^sub>h (of_complex x) = x_axis"
      using x poincare_line_0_real_is_x_axis[of "of_complex x"]
      unfolding circline_set_x_axis
      by auto
    have "of_complex x \<in> unit_disc"
      using x
      by (auto simp add: cmod_eq_Re)
    have "of_complex x \<noteq> 0\<^sub>h"
      using \<open>x \<noteq> 0\<close>
      by auto
    show "?P 0\<^sub>h (of_complex x)"
    proof safe
      fix w
      assume "w \<in> unit_disc"
      assume "poincare_collinear {0\<^sub>h, of_complex x, w}"
      hence "w \<in> circline_set x_axis"
        using * unique_poincare_line[of "0\<^sub>h" "of_complex x"] \<open>of_complex x \<in> unit_disc\<close> \<open>x \<noteq> 0\<close> \<open>of_complex x \<noteq> 0\<^sub>h\<close>
        unfolding poincare_collinear_def
        by auto
      then obtain w' where w': "w = of_complex w'" "is_real w'"
        using \<open>w \<in> unit_disc\<close>
        using inf_or_of_complex[of w]
        unfolding circline_set_x_axis
        by auto
      hence "-1 < Re w'" "Re w' < 1"
        using \<open>w \<in> unit_disc\<close>
        by (auto simp add: cmod_eq_Re)
      assume 1: "\<not> poincare_between (of_complex x) 0\<^sub>h w"
      hence "w \<noteq> 0\<^sub>h" "w' \<noteq> 0"
        using w'
        unfolding poincare_between_def
        by auto
      hence "Re w' \<noteq> 0"
        using w' complex.expand[of w' 0]
        by auto

      have "Re w' \<ge> 0"
        using 1 poincare_between_x_axis_u0v[of x w'] \<open>Re x > 0\<close> \<open>is_real x\<close> \<open>x \<noteq> 0\<close> \<open>w' \<noteq> 0\<close> w'
        using mult_pos_neg
        by force

      moreover

      assume "\<not> poincare_between 0\<^sub>h (of_complex x) w"
      hence "Re w' < Re x"
        using poincare_between_x_axis_0uv[of "Re x" "Re w'"]
        using w' x \<open>-1 < Re w'\<close> \<open>Re w' < 1\<close> \<open>Re w' \<noteq> 0\<close>
        by auto

      ultimately
      show "poincare_between 0\<^sub>h w (of_complex x)"
        using poincare_between_x_axis_0uv[of "Re w'" "Re x"]
        using w' x \<open>-1 < Re w'\<close> \<open>Re w' < 1\<close> \<open>Re w' \<noteq> 0\<close>
        by auto
    qed
  next
    show "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
      by fact+
  next
    fix M u v
    assume 1: "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
    let ?Mu = "moebius_pt M u" and ?Mv = "moebius_pt M v"
    assume 2: "?P ?Mu ?Mv"
    show "?P u v"
    proof safe
      fix w
      assume "w \<in> unit_disc" "poincare_collinear {u, v, w}" "\<not> poincare_between u v w" "\<not> poincare_between v u w"
      thus "poincare_between u w v"
        using 1 2[rule_format, of "moebius_pt M w"]
        by simp
    qed
  qed
  thus ?thesis
    using assms
    by simp
qed

lemma poincare_collinear3_iff:
  assumes "u \<in> unit_disc" "v \<in> unit_disc"  "w \<in> unit_disc"
  shows "poincare_collinear {u, v, w} \<longleftrightarrow> poincare_between u v w \<or> poincare_between v u w \<or> poincare_between v w u"
  using assms 
  by (metis poincare_collinear3_between insert_commute poincare_between_poincare_collinear poincare_between_rev)

subsection \<open>Some properties of betweenness\<close>

lemma poincare_between_transitivity:
  assumes "a \<in> unit_disc" and "x \<in> unit_disc" and "b \<in> unit_disc" and "y \<in> unit_disc" and
          "poincare_between a x b" and "poincare_between a b y"
  shows "poincare_between x b y"
proof(cases "a = b")
  case True
  thus ?thesis
    using assms
    using poincare_between_sandwich by blast
next
  case False
  have "\<forall> x. \<forall> y. poincare_between a x b \<and> poincare_between a b y \<and> x \<in> unit_disc
                  \<and> y \<in> unit_disc \<longrightarrow> poincare_between x b y" (is "?P a b")
  proof (rule wlog_positive_x_axis[where P="?P"])
    show "a \<in> unit_disc"
      using assms by simp
  next
    show "b \<in> unit_disc"
      using assms by simp
  next
    show "a \<noteq> b"
      using False by simp
  next
    fix M u v
    assume *: "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v" 
              "\<forall>x y. poincare_between (moebius_pt M u) x (moebius_pt M v) \<and> 
                  poincare_between (moebius_pt M u) (moebius_pt M v) y \<and>
                  x \<in> unit_disc \<and> y \<in> unit_disc \<longrightarrow>
                  poincare_between x (moebius_pt M v) y"
    show "\<forall>x y. poincare_between u x v \<and> poincare_between u v y \<and> x \<in> unit_disc \<and> y \<in> unit_disc 
                \<longrightarrow> poincare_between x v y"
    proof safe
      fix x y
      assume "poincare_between u x v" "poincare_between u v y" " x \<in> unit_disc" "y \<in> unit_disc"

      have "poincare_between (moebius_pt M u) (moebius_pt M x) (moebius_pt M v)" 
        using \<open>poincare_between u x v\<close> \<open>unit_disc_fix M\<close> \<open>x \<in> unit_disc\<close> \<open>u \<in> unit_disc\<close> \<open>v \<in> unit_disc\<close>
        by simp
      moreover
      have "poincare_between (moebius_pt M u) (moebius_pt M v) (moebius_pt M y)"
        using \<open>poincare_between u v y\<close> \<open>unit_disc_fix M\<close> \<open>y \<in> unit_disc\<close> \<open>u \<in> unit_disc\<close> \<open>v \<in> unit_disc\<close>
        by simp
      moreover
      have "(moebius_pt M x) \<in> unit_disc"
        using \<open>unit_disc_fix M\<close> \<open>x \<in> unit_disc\<close> by simp
      moreover
      have "(moebius_pt M y) \<in> unit_disc"
        using \<open>unit_disc_fix M\<close> \<open>y \<in> unit_disc\<close> by simp
      ultimately
      have "poincare_between (moebius_pt M x) (moebius_pt M v) (moebius_pt M y)"
        using * by blast
      thus "poincare_between x v y"
        using \<open>y \<in> unit_disc\<close> * \<open>x \<in> unit_disc\<close> by simp
    qed
  next
    fix x
    assume xx: "is_real x" "0 < Re x" "Re x < 1"
    hence "of_complex x \<in> unit_disc"
      using cmod_eq_Re by auto
    hence "of_complex x \<noteq> \<infinity>\<^sub>h"
      by simp
    have " of_complex x \<noteq> 0\<^sub>h"
      using xx by auto
    have "of_complex x \<in> circline_set x_axis"
      using xx by simp
    show "\<forall>m n. poincare_between 0\<^sub>h m (of_complex x) \<and> poincare_between 0\<^sub>h (of_complex x) n \<and>
            m \<in> unit_disc \<and> n \<in> unit_disc \<longrightarrow> poincare_between m (of_complex x) n"
    proof safe
      fix m n
      assume **: "poincare_between 0\<^sub>h m (of_complex x)" "poincare_between 0\<^sub>h (of_complex x) n"
                 "m \<in> unit_disc" " n \<in> unit_disc"
      show "poincare_between m (of_complex x) n"
      proof(cases "m = 0\<^sub>h")
        case True
        thus ?thesis
          using ** by auto
      next
        case False
        hence "m \<in> circline_set x_axis"
          using poincare_between_poincare_line_uzv[of "0\<^sub>h" "of_complex x" m]
          using poincare_line_0_real_is_x_axis[of "of_complex x"] 
          using \<open>of_complex x \<in> unit_disc\<close> \<open>of_complex x \<noteq> \<infinity>\<^sub>h\<close> \<open>of_complex x \<noteq> 0\<^sub>h\<close>
          using \<open>of_complex x \<in> circline_set x_axis\<close> \<open>m \<in> unit_disc\<close> **(1)
          by simp
        then obtain m' where "m = of_complex m'" "is_real m'"
          using inf_or_of_complex[of m] \<open>m \<in> unit_disc\<close>
          unfolding circline_set_x_axis
          by auto
        hence "Re m' \<le> Re x"
          using \<open>poincare_between 0\<^sub>h m (of_complex x)\<close> xx \<open>of_complex x \<noteq> 0\<^sub>h\<close>
          using False ** \<open>of_complex x \<in> unit_disc\<close>
          using cmod_Re_le_iff poincare_between_0uv by auto
 
        have "n \<noteq> 0\<^sub>h"
          using **(2, 4) \<open>of_complex x \<noteq> 0\<^sub>h\<close> \<open>of_complex x \<in> unit_disc\<close>
          using poincare_between_sandwich by fastforce
        have "n \<in> circline_set x_axis"
          using poincare_between_poincare_line_uvz[of "0\<^sub>h" "of_complex x" n]
          using poincare_line_0_real_is_x_axis[of "of_complex x"] 
          using \<open>of_complex x \<in> unit_disc\<close> \<open>of_complex x \<noteq> \<infinity>\<^sub>h\<close> \<open>of_complex x \<noteq> 0\<^sub>h\<close>
          using \<open>of_complex x \<in> circline_set x_axis\<close> \<open>n \<in> unit_disc\<close> **(2)
          by simp
        then obtain n' where "n = of_complex n'" "is_real n'"
          using inf_or_of_complex[of n] \<open>n \<in> unit_disc\<close>
          unfolding circline_set_x_axis
          by auto
        hence "Re x \<le> Re n'"
          using \<open>poincare_between 0\<^sub>h (of_complex x) n\<close> xx \<open>of_complex x \<noteq> 0\<^sub>h\<close>
          using False ** \<open>of_complex x \<in> unit_disc\<close> \<open>n \<noteq> 0\<^sub>h\<close>
          using cmod_Re_le_iff poincare_between_0uv
          by (metis Re_complex_of_real arg_0_iff rcis_cmod_arg rcis_zero_arg to_complex_of_complex)
        
        have "poincare_between (of_complex m') (of_complex x) (of_complex n')" 
          using \<open>Re x \<le> Re n'\<close> \<open>Re m' \<le> Re x\<close>
          using poincare_between_x_axis_uvw[of "Re m'" "Re x" "Re n'"]
          using \<open>is_real n'\<close> \<open>is_real m'\<close> \<open>n \<in> unit_disc\<close> \<open>n = of_complex n'\<close>
          using xx \<open>m = of_complex m'\<close> \<open>m \<in> unit_disc\<close>
          by (smt complex_of_real_Re norm_of_real poincare_between_def unit_disc_iff_cmod_lt_1)

        thus ?thesis
          using \<open>n = of_complex n'\<close> \<open>m = of_complex m'\<close>
          by auto
      qed
    qed
  qed 
  thus ?thesis
    using assms
    by blast
qed

(* ------------------------------------------------------------------ *)
subsection\<open>Poincare between - sum distances\<close>
(* ------------------------------------------------------------------ *)

text\<open>Another possible definition of the h-betweenness relation is given in terms of h-distances
between pairs of points. We prove it as a characterization equivalent to our cross-ratio based
definition.\<close>

lemma poincare_between_sum_distances_x_axis_u0v:
  assumes "of_complex u' \<in> unit_disc" "of_complex v' \<in> unit_disc"
  assumes "is_real u'" "u' \<noteq> 0" "v' \<noteq> 0"
  shows  "poincare_distance (of_complex u') 0\<^sub>h + poincare_distance 0\<^sub>h (of_complex v') = poincare_distance (of_complex u') (of_complex v') \<longleftrightarrow>
          is_real v' \<and> Re u' * Re v' < 0" (is "?P u' v' \<longleftrightarrow> ?Q u' v'")
proof-
  have "Re u' \<noteq> 0"
    using \<open>is_real u'\<close> \<open>u' \<noteq> 0\<close>
    using complex_eq_if_Re_eq
    by simp

  let ?u = "cmod u'" and ?v = "cmod v'" and ?uv = "cmod (u' - v')"
  have disc: "?u\<^sup>2 < 1" "?v\<^sup>2 < 1"
    using unit_disc_cmod_square_lt_1[OF assms(1)]
    using unit_disc_cmod_square_lt_1[OF assms(2)]
    by auto
  have "poincare_distance (of_complex u') 0\<^sub>h + poincare_distance 0\<^sub>h (of_complex v') =
              arcosh (((1 + ?u\<^sup>2) * (1 + ?v\<^sup>2) + 4 * ?u * ?v) / ((1 - ?u\<^sup>2) * (1 - ?v\<^sup>2)))" (is "_ = arcosh ?r1")
          using poincare_distance_formula_zero_sum[OF assms(1-2)]
          by (simp add: Let_def)
  moreover
  have "poincare_distance (of_complex u') (of_complex v') =
              arcosh (((1 - ?u\<^sup>2) * (1 - ?v\<^sup>2) + 2 * ?uv\<^sup>2) / ((1 - ?u\<^sup>2) * (1 - ?v\<^sup>2)))" (is "_ = arcosh ?r2")
    using disc
    using poincare_distance_formula[OF assms(1-2)]
    by (subst add_divide_distrib) simp
  moreover
  have "arcosh ?r1 = arcosh ?r2 \<longleftrightarrow> ?Q u' v'"
  proof
    assume "arcosh ?r1 = arcosh ?r2"
    hence "?r1 = ?r2"
    proof (subst (asm) arcosh_eq_iff)
      show "?r1 \<ge> 1"
      proof-
        have "(1 - ?u\<^sup>2) * (1 - ?v\<^sup>2) \<le> (1 + ?u\<^sup>2) * (1 + ?v\<^sup>2) + 4 * ?u * ?v"
          by (simp add: field_simps)
        thus ?thesis
          using disc
          by simp
      qed
    next
      show "?r2 \<ge> 1"
        using disc
        by simp
    qed
    hence "(1 + ?u\<^sup>2) * (1 + ?v\<^sup>2) + 4 * ?u * ?v = (1 - ?u\<^sup>2) * (1 - ?v\<^sup>2) + 2 * ?uv\<^sup>2"
      using disc
      by auto              
    hence "(cmod (u' - v'))\<^sup>2 = (cmod u' + cmod v')\<^sup>2"
      by (simp add: field_simps power2_eq_square)
    hence *: "Re u' * Re v' + \<bar>Re u'\<bar> * sqrt ((Im v')\<^sup>2 + (Re v')\<^sup>2) = 0"
      using \<open>is_real u'\<close>
      unfolding cmod_power2 cmod_def
      by (simp add: field_simps) (simp add: power2_eq_square field_simps)
    hence "sqrt ((Im v')\<^sup>2 + (Re v')\<^sup>2) = \<bar>Re v'\<bar>"
      using \<open>Re u' \<noteq> 0\<close> \<open>v' \<noteq> 0\<close>
      by (smt complex_neq_0 mult.commute mult_cancel_right mult_minus_left real_sqrt_gt_0_iff)
    hence "Im v' = 0"
      by (smt Im_eq_0 norm_complex_def)
    moreover
    hence "Re u' * Re v' = - \<bar>Re u'\<bar> * \<bar>Re v'\<bar>"
      using *
      by simp
    hence "Re u' * Re v' < 0"
      using \<open>Re u' \<noteq> 0\<close> \<open>v' \<noteq> 0\<close>
      by (simp add: \<open>is_real v'\<close> complex_eq_if_Re_eq)
    ultimately
    show "?Q u' v'"
      by simp
  next
    assume "?Q u' v'"
    hence "is_real v'" "Re u' * Re v' < 0"
      by auto
    have "?r1 = ?r2"
    proof (cases "Re u' > 0")
      case True
      hence "Re v' < 0"
        using \<open>Re u' * Re v' < 0\<close>
        by (smt zero_le_mult_iff)
      show ?thesis
        using disc \<open>is_real u'\<close> \<open>is_real v'\<close>
        using \<open>Re u' > 0\<close> \<open>Re v' < 0\<close>
        unfolding cmod_power2 cmod_def
        by simp (simp add: power2_eq_square field_simps)
    next
      case False
      hence "Re u' < 0"
        using \<open>Re u' \<noteq> 0\<close>
        by simp
      hence "Re v' > 0"
        using \<open>Re u' * Re v' < 0\<close>
        by (smt zero_le_mult_iff)
      show ?thesis
        using disc \<open>is_real u'\<close> \<open>is_real v'\<close>
        using \<open>Re u' < 0\<close> \<open>Re v' > 0\<close>
        unfolding cmod_power2 cmod_def
        by simp (simp add: power2_eq_square field_simps)
    qed
    thus "arcosh ?r1 = arcosh ?r2"
      by metis
  qed
  ultimately
  show ?thesis
    by simp
qed

text\<open>
  Different proof of the previous theorem relying on the cross-ratio definition, and not the distance formula.
  We suppose that this could be also used to prove the triangle inequality.
\<close>
lemma poincare_between_sum_distances_x_axis_u0v_different_proof:
  assumes "of_complex u' \<in> unit_disc" "of_complex v' \<in> unit_disc"
  assumes "is_real u'" "u' \<noteq> 0" "v' \<noteq> 0" (* additional condition *) "is_real v'"
  shows  "poincare_distance (of_complex u') 0\<^sub>h + poincare_distance 0\<^sub>h (of_complex v') = poincare_distance (of_complex u') (of_complex v') \<longleftrightarrow>
          Re u' * Re v' < 0" (is "?P u' v' \<longleftrightarrow> ?Q u' v'")
proof-
  have "-1 < Re u'" "Re u' < 1" "Re u' \<noteq> 0"
    using assms
    by (auto simp add: cmod_eq_Re complex_eq_if_Re_eq)
  have "-1 < Re v'" "Re v' < 1" "Re v' \<noteq> 0"
    using assms
    by (auto simp add: cmod_eq_Re complex_eq_if_Re_eq)

  have "\<bar>ln (Re ((1 - u') / (1 + u')))\<bar> + \<bar>ln (Re ((1 - v') / (1 + v')))\<bar> =
        \<bar>ln (Re ((1 + u') * (1 - v') / ((1 - u') * (1 + v'))))\<bar> \<longleftrightarrow> Re u' * Re v' < 0" (is "\<bar>ln ?a1\<bar>  + \<bar>ln ?a2\<bar> = \<bar>ln ?a3\<bar> \<longleftrightarrow> _")
  proof-
    have 1: "0 < ?a1" "ln ?a1 > 0 \<longleftrightarrow> Re u' < 0"
      using \<open>Re u' < 1\<close> \<open>Re u' > -1\<close> \<open>is_real u'\<close>
      using complex_is_Real_iff
      by auto
    have 2: "0 < ?a2" "ln ?a2 > 0 \<longleftrightarrow> Re v' < 0"
      using \<open>Re v' < 1\<close> \<open>Re v' > -1\<close> \<open>is_real v'\<close>
      using complex_is_Real_iff
      by auto
    have 3: "0 < ?a3" "ln ?a3 > 0 \<longleftrightarrow> Re v' < Re u'"
      using \<open>Re u' < 1\<close> \<open>Re u' > -1\<close> \<open>is_real u'\<close>
      using \<open>Re v' < 1\<close> \<open>Re v' > -1\<close> \<open>is_real v'\<close>
      using complex_is_Real_iff
       by auto (simp add: field_simps)+
    show ?thesis
    proof
      assume *: "Re u' * Re v' < 0"
      show "\<bar>ln ?a1\<bar> + \<bar>ln ?a2\<bar> = \<bar>ln ?a3\<bar>"
      proof (cases "Re u' > 0")
        case True
        hence "Re v' < 0"
          using *
          by (smt mult_nonneg_nonneg)
        show ?thesis
          using 1 2 3 \<open>Re u' > 0\<close> \<open>Re v' < 0\<close>
          using \<open>Re u' < 1\<close> \<open>Re u' > -1\<close> \<open>is_real u'\<close>
          using \<open>Re v' < 1\<close> \<open>Re v' > -1\<close> \<open>is_real v'\<close>
          using complex_is_Real_iff
          using ln_div ln_mult
          by simp
      next
        case False
        hence "Re v' > 0" "Re u' < 0"
          using *
          by (smt zero_le_mult_iff)+
        show ?thesis
          using 1 2 3 \<open>Re u' < 0\<close> \<open>Re v' > 0\<close>
          using \<open>Re u' < 1\<close> \<open>Re u' > -1\<close> \<open>is_real u'\<close>
          using \<open>Re v' < 1\<close> \<open>Re v' > -1\<close> \<open>is_real v'\<close>
          using complex_is_Real_iff
          using ln_div ln_mult
          by simp
      qed
    next
      assume *: "\<bar>ln ?a1\<bar> + \<bar>ln ?a2\<bar> = \<bar>ln ?a3\<bar>"
      {
        assume "Re u' > 0" "Re v' > 0"
        hence False
          using * 1 2 3
          using \<open>Re u' < 1\<close> \<open>Re u' > -1\<close> \<open>is_real u'\<close>
          using \<open>Re v' < 1\<close> \<open>Re v' > -1\<close> \<open>is_real v'\<close>
          using complex_is_Real_iff
          using ln_mult ln_div
          by (cases "Re v' < Re u'") auto
      }
      moreover
      {
        assume "Re u' < 0" "Re v' < 0"
        hence False
          using * 1 2 3
          using \<open>Re u' < 1\<close> \<open>Re u' > -1\<close> \<open>is_real u'\<close>
          using \<open>Re v' < 1\<close> \<open>Re v' > -1\<close> \<open>is_real v'\<close>
          using complex_is_Real_iff
          using ln_mult ln_div
          by (cases "Re v' < Re u'") auto
      }
      ultimately
      show "Re u' * Re v' < 0"
        using \<open>Re u' \<noteq> 0\<close> \<open>Re v' \<noteq> 0\<close>
        by (smt divisors_zero mult_le_0_iff)
    qed
  qed
  thus ?thesis
    using assms
    apply (subst poincare_distance_sym, simp, simp)
    apply (subst poincare_distance_zero_x_axis, simp, simp add: circline_set_x_axis)
    apply (subst poincare_distance_zero_x_axis, simp, simp add: circline_set_x_axis)
    apply (subst poincare_distance_x_axis_x_axis, simp, simp, simp add: circline_set_x_axis, simp add: circline_set_x_axis)
    apply simp
    done
qed

lemma poincare_between_sum_distances:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc" and "w \<in> unit_disc"
  shows "poincare_between u v w \<longleftrightarrow> 
         poincare_distance u v + poincare_distance v w = poincare_distance u w" (is "?P' u v w")
proof (cases "u = v")
  case True
  thus ?thesis
    using assms
    by simp
next
  case False
  have "\<forall> w. w \<in> unit_disc \<longrightarrow> (poincare_between u v w \<longleftrightarrow> poincare_distance u v + poincare_distance v w = poincare_distance u w)" (is "?P u v")
  proof (rule wlog_positive_x_axis)
    fix x
    assume "is_real x" "0 < Re x" "Re x < 1"
    have "of_complex x \<in> circline_set x_axis"
      using \<open>is_real x\<close>
      by (auto simp add: circline_set_x_axis)

    have "of_complex x \<in> unit_disc"
      using \<open>is_real x\<close> \<open>0 < Re x\<close> \<open>Re x < 1\<close>
      by (simp add: cmod_eq_Re)

    have "x \<noteq> 0"
      using \<open>is_real x\<close> \<open>Re x > 0\<close>
      by auto

    show "?P (of_complex x) 0\<^sub>h"
    proof (rule allI, rule impI)
      fix w
      assume "w \<in> unit_disc"
      then obtain w' where "w = of_complex w'"
        using inf_or_of_complex[of w]
        by auto

      show "?P' (of_complex x) 0\<^sub>h w"
      proof (cases "w = 0\<^sub>h")
        case True
        thus ?thesis
          by simp
      next
        case False
        hence "w' \<noteq> 0"
          using \<open>w = of_complex w'\<close>
          by auto

        show ?thesis
          using \<open>is_real x\<close> \<open>x \<noteq> 0\<close> \<open>w = of_complex w'\<close> \<open>w' \<noteq> 0\<close>
          using \<open>of_complex x \<in> unit_disc\<close> \<open>w \<in> unit_disc\<close>
          apply simp
          apply (subst poincare_between_x_axis_u0v, simp_all)
          apply (subst poincare_between_sum_distances_x_axis_u0v, simp_all)
          done
      qed
    qed
  next
    show "v \<in> unit_disc" "u \<in> unit_disc"
      using assms
      by auto
  next
    show "v \<noteq> u"
      using \<open>u \<noteq> v\<close>
      by simp
  next
    fix M u v
    assume *: "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v" and
          **: "?P (moebius_pt M v) (moebius_pt M u)"
    show "?P v u"
    proof (rule allI, rule impI)
      fix w
      assume "w \<in> unit_disc"
      hence "moebius_pt M w \<in> unit_disc"
        using \<open>unit_disc_fix M\<close>
        by auto
      thus "?P' v u w"
        using \<open>u \<in> unit_disc\<close> \<open>v \<in> unit_disc\<close> \<open>w \<in> unit_disc\<close> \<open>unit_disc_fix M\<close>
        using **[rule_format, of "moebius_pt M w"]
        by auto
    qed
  qed
  thus ?thesis
    using assms
    by simp
qed

subsection \<open>Some more properties of h-betweenness.\<close>

text \<open>Some lemmas proved earlier are proved almost directly using the sum of distances characterization.\<close>

lemma unit_disc_fix_moebius_preserve_poincare_between':
  assumes "unit_disc_fix M" and "u \<in> unit_disc" and "v \<in> unit_disc" and "w \<in> unit_disc"
  shows "poincare_between (moebius_pt M u) (moebius_pt M v) (moebius_pt M w) \<longleftrightarrow>
         poincare_between u v w"
  using assms
  using poincare_between_sum_distances
  by simp

lemma conjugate_preserve_poincare_between':
  assumes "u \<in> unit_disc" "v \<in> unit_disc" "w \<in> unit_disc"
  shows "poincare_between (conjugate u) (conjugate v) (conjugate w) \<longleftrightarrow> poincare_between u v w"
  using assms
  using poincare_between_sum_distances
  by simp

text \<open>There is a unique point on a ray on the given distance from the given starting point\<close>
lemma unique_poincare_distance_on_ray:
  assumes "d \<ge> 0" "u \<noteq> v" "u \<in> unit_disc" "v \<in> unit_disc"
  assumes "y \<in> unit_disc" "poincare_distance u y = d" "poincare_between u v y"
  assumes "z \<in> unit_disc" "poincare_distance u z = d" "poincare_between u v z"
  shows "y = z"
proof-
  have "\<forall> d y z. d \<ge> 0 \<and>
        y \<in> unit_disc \<and> poincare_distance u y = d \<and> poincare_between u v y \<and>
        z \<in> unit_disc \<and> poincare_distance u z = d \<and> poincare_between u v z \<longrightarrow> y = z" (is "?P u v")
  proof (rule wlog_positive_x_axis[where P="?P"])
    fix x
    assume x: "is_real x" "0 < Re x" "Re x < 1"
    hence "x \<noteq> 0"
      using complex.expand[of x 0]
      by auto
    hence *: "poincare_line 0\<^sub>h (of_complex x) = x_axis"
      using x poincare_line_0_real_is_x_axis[of "of_complex x"]
      unfolding circline_set_x_axis
      by auto
    have "of_complex x \<in> unit_disc"
      using x
      by (auto simp add: cmod_eq_Re)
    have "arg x = 0"
      using x
      using arg_0_iff by blast
    show "?P 0\<^sub>h (of_complex x)"
    proof safe
      fix y z
      assume "y \<in> unit_disc" "z \<in> unit_disc"
      then obtain y' z' where yz: "y = of_complex y'" "z = of_complex z'"
        using inf_or_of_complex[of y] inf_or_of_complex[of z]
        by auto
      assume betw: "poincare_between 0\<^sub>h (of_complex x) y"  "poincare_between 0\<^sub>h (of_complex x) z"
      hence "y \<noteq> 0\<^sub>h" "z \<noteq> 0\<^sub>h"
        using \<open>x \<noteq> 0\<close> \<open>of_complex x \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close>
        using poincare_between_sandwich[of "0\<^sub>h" "of_complex x"]
        using of_complex_zero_iff[of x]
        by force+

      hence "arg y' = 0" "cmod y' \<ge> cmod x" "arg z' = 0" "cmod z' \<ge> cmod x"
        using poincare_between_0uv[of "of_complex x" y] poincare_between_0uv[of "of_complex x" z]
        using \<open>of_complex x \<in> unit_disc\<close> \<open>x \<noteq> 0\<close> \<open>arg x = 0\<close> \<open>y \<in> unit_disc\<close> \<open>z \<in> unit_disc\<close> betw yz
        by (simp_all add: Let_def)
      hence *: "is_real y'" "is_real z'" "Re y' > 0" "Re z' > 0"
        using arg_0_iff[of y'] arg_0_iff[of z'] x \<open>y \<noteq> 0\<^sub>h\<close> \<open>z \<noteq> 0\<^sub>h\<close> yz
        by auto
      assume "poincare_distance 0\<^sub>h z = poincare_distance 0\<^sub>h y" "0 \<le> poincare_distance 0\<^sub>h y"
      thus "y = z"
        using * yz \<open>y \<in> unit_disc\<close> \<open>z \<in> unit_disc\<close>
        using unique_x_axis_poincare_distance_positive[of "poincare_distance 0\<^sub>h y"]
        by (auto simp add: cmod_eq_Re unit_disc_to_complex_inj)
    qed
  next
    show "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
      by fact+
  next
    fix M u v
    assume *: "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
    assume **: "?P (moebius_pt M u) (moebius_pt M v)"
    show "?P u v"
    proof safe
      fix d y z
      assume ***: "0 \<le> poincare_distance u y"
             "y \<in> unit_disc" "poincare_between u v y"
             "z \<in> unit_disc" "poincare_between u v z"
             "poincare_distance u z = poincare_distance u y"
      let ?Mu = "moebius_pt M u" and ?Mv = "moebius_pt M v" and ?My = "moebius_pt M y" and ?Mz = "moebius_pt M z"
      have "?Mu \<in> unit_disc" "?Mv \<in> unit_disc" "?My \<in> unit_disc" "?Mz \<in> unit_disc"
        using \<open>u \<in> unit_disc\<close> \<open>v \<in> unit_disc\<close> \<open>y \<in> unit_disc\<close> \<open>z \<in> unit_disc\<close>
        using \<open>unit_disc_fix M\<close>
        by auto
      hence "?My = ?Mz"
        using * ***
        using **[rule_format, of "poincare_distance ?Mu ?My" ?My ?Mz]
        by simp
      thus "y = z"
        using bij_moebius_pt[of M]
        unfolding bij_def inj_on_def
        by blast
    qed
  qed
  thus ?thesis
    using assms
    by auto
qed

end