(* ----------------------------------------------------------------- *)
section \<open>Elementary complex geometry\<close>
(* ----------------------------------------------------------------- *)

text \<open>In this section equations and basic properties of the most fundamental objects and relations in
geometry -- collinearity, lines, circles and circlines. These are defined by equations in
$\mathbb{C}$ (not extended by an infinite point). Later these equations will be generalized to
equations in the extended complex plane, over homogenous coordinates.\<close>

theory Elementary_Complex_Geometry
imports More_Complex Linear_Systems Angles
begin

(* ----------------------------------------------------------------- *)
subsection \<open>Collinear points\<close>
(* ----------------------------------------------------------------- *)

definition collinear :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> bool" where
  "collinear z1 z2 z3 \<longleftrightarrow> z1 = z2 \<or> Im ((z3 - z1) / (z2 - z1)) = 0"

lemma collinear_ex_real:
  shows "collinear z1 z2 z3 \<longleftrightarrow>
         (\<exists> k::real. z1 = z2 \<or> z3 - z1 = complex_of_real k * (z2 - z1))"
  unfolding collinear_def
  by (metis Im_complex_of_real add_diff_cancel_right' complex_eq diff_zero legacy_Complex_simps(15) nonzero_mult_div_cancel_right right_minus_eq times_divide_eq_left zero_complex.code)

text \<open>Collinearity characterization using determinants\<close>
lemma collinear_det:
  assumes "\<not> collinear z1 z2 z3"
  shows "det2 (z3 - z1) (cnj (z3 - z1)) (z1 - z2) (cnj (z1 - z2)) \<noteq> 0"
proof-
  from assms have "((z3 - z1) / (z2 - z1)) - cnj ((z3 - z1) / (z2 - z1)) \<noteq> 0" "z2 \<noteq> z1"
    unfolding collinear_def
    using Complex_Im_express_cnj[of "(z3 - z1) / (z2 - z1)"]
    by (auto simp add: Complex_eq)
  thus ?thesis
    by (auto simp add: field_simps)
qed

text \<open>Properties of three collinear points\<close>

lemma collinear_sym1:
  shows "collinear z1 z2 z3 \<longleftrightarrow> collinear z1 z3 z2"
  unfolding collinear_def
  using div_reals[of "1" "(z3 - z1)/(z2 - z1)"]  div_reals[of "1" "(z2 - z1)/(z3 - z1)"]
  by auto

lemma collinear_sym2':
  assumes "collinear z1 z2 z3"
  shows "collinear z2 z1 z3"
proof-
  obtain k where "z1 = z2 \<or> z3 - z1 = complex_of_real k * (z2 - z1)"
    using assms
    unfolding collinear_ex_real
    by auto
  thus ?thesis
  proof
    assume "z3 - z1 = complex_of_real k * (z2 - z1)"
    thus ?thesis
      unfolding collinear_ex_real
      by (rule_tac x="1-k" in exI) (auto simp add: field_simps)
  qed (simp add: collinear_def)
qed

lemma collinear_sym2:
  shows "collinear z1 z2 z3 \<longleftrightarrow> collinear z2 z1 z3"
  using collinear_sym2'[of z1 z2 z3] collinear_sym2'[of z2 z1 z3]
  by auto

text \<open>Properties of four collinear points\<close>

lemma collinear_trans1:
  assumes "collinear z0 z2 z1" and "collinear z0 z3 z1" and "z0 \<noteq> z1"
  shows "collinear z0 z2 z3"
  using assms
  unfolding collinear_ex_real
  by (cases "z0 = z2", auto) (rule_tac x="k/ka" in exI, case_tac "ka = 0", auto simp add: field_simps)


(* ----------------------------------------------------------------- *)
subsection \<open>Euclidean line\<close>
(* ----------------------------------------------------------------- *)

text \<open>Line is defined by using collinearity\<close>
definition line :: "complex \<Rightarrow> complex \<Rightarrow> complex set" where
  "line z1 z2 = {z. collinear z1 z2 z}"

lemma line_points_collinear:
  assumes "z1 \<in> line z z'" and "z2 \<in> line z z'" and "z3 \<in> line z z'" and "z \<noteq> z'"
  shows "collinear z1 z2 z3"
  using assms
  unfolding line_def
  by (smt collinear_sym1 collinear_sym2' collinear_trans1 mem_Collect_eq)

text \<open>Parametric equation of a line\<close>
lemma line_param:
  shows "z1 + cor k * (z2 - z1) \<in> line z1 z2"
  unfolding line_def
  by (auto simp add: collinear_def)

text \<open>Equation of the line containing two different given points\<close>
lemma line_equation:
  assumes "z1 \<noteq> z2" and "\<mu> = rot90 (z2 - z1)"
  shows "line z1 z2 = {z. cnj \<mu>*z + \<mu>*cnj z - (cnj \<mu> * z1 + \<mu> * cnj z1)  = 0}"
proof-
  {
    fix z
    have "z \<in> line z1 z2 \<longleftrightarrow> Im ((z - z1)/(z2 - z1)) = 0"
      using assms
      by (simp add: line_def collinear_def)
    also have "... \<longleftrightarrow> (z - z1)/(z2 - z1) = cnj ((z - z1)/(z2 - z1))"
      using complex_diff_cnj[of "(z - z1)/(z2 - z1)"]
      by auto
    also have "... \<longleftrightarrow> (z - z1)*(cnj z2 - cnj z1) = (cnj z - cnj z1)*(z2 - z1)"
      using assms(1)
      using \<open>(z \<in> line z1 z2) = is_real ((z - z1) / (z2 - z1))\<close> calculation is_real_div
      by auto
    also have "... \<longleftrightarrow> cnj(z2 - z1)*z - (z2 - z1)*cnj z - (cnj(z2 - z1)*z1 - (z2 - z1)*cnj z1) = 0"
      by (simp add: field_simps)
    also have "... \<longleftrightarrow> cnj \<mu> * z + \<mu> * cnj z  - (cnj \<mu> * z1 + \<mu> * cnj z1) = 0"
      apply (subst assms)+
      apply (subst cnj_mix_minus)+
      by simp
    finally have "z \<in> line z1 z2 \<longleftrightarrow> cnj \<mu> * z + \<mu> * cnj z  - (cnj \<mu> * z1 + \<mu> * cnj z1) = 0"
      .
  }
  thus ?thesis
    by auto
qed

(* -------------------------------------------------------------------------- *)
subsection \<open>Euclidean circle\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Definition of the circle with given center and radius. It consists of all
points on the distance $r$ from the center $\mu$.\<close>
definition circle :: "complex \<Rightarrow> real \<Rightarrow> complex set" where
  "circle \<mu> r = {z. cmod (z - \<mu>) = r}"

text \<open>Equation of the circle centered at $\mu$ with the radius $r$.\<close>
lemma circle_equation:
  assumes "r \<ge> 0"
  shows "circle \<mu> r = {z. z*cnj z - z*cnj \<mu> - cnj z*\<mu> + \<mu>*cnj \<mu> - cor (r*r) = 0}"
proof (safe)
  fix z
  assume "z \<in> circle \<mu> r"
  hence "(z - \<mu>)*cnj (z - \<mu>) = complex_of_real (r*r)"
    unfolding circle_def
    using complex_mult_cnj_cmod[of "z - \<mu>"]
    by (auto simp add: power2_eq_square)
  thus "z * cnj z - z * cnj \<mu> - cnj z * \<mu> + \<mu> * cnj \<mu> - cor (r * r) = 0"
    by (auto simp add: field_simps)
next
  fix z
  assume "z * cnj z - z * cnj \<mu> - cnj z * \<mu> + \<mu> * cnj \<mu> - cor (r * r) = 0"
  hence "(z - \<mu>)*cnj (z - \<mu>) = cor (r*r)"
    by (auto simp add: field_simps)
  thus "z \<in> circle \<mu> r"
    using assms
    using complex_mult_cnj_cmod[of "z - \<mu>"]
    using power2_eq_imp_eq[of "cmod (z - \<mu>)" r]
    unfolding circle_def power2_eq_square[symmetric] complex_of_real_def
    by auto
qed

(* -------------------------------------------------------------------------- *)
subsection \<open>Circline\<close>
(* -------------------------------------------------------------------------- *)

text \<open>A very important property of the extended complex plane is that it is possible to treat circles
and lines in a uniform way. The basic object is \emph{generalized circle}, or \emph{circline} for
short. We introduce circline equation given in $\mathbb{C}$, and it will later be generalized to an
equation in the extended complex plane $\overline{\mathbb{C}}$ given in matrix form using a
Hermitean matrix and a quadratic form over homogenous coordinates.\<close>

definition circline where
  "circline A BC D = {z. cor A*z*cnj z + cnj BC*z + BC*cnj z + cor D = 0}"

text \<open>Connection between circline and Euclidean circle\<close>

text \<open>Every circline with positive determinant and $A \neq 0$ represents an Euclidean circle\<close>

lemma circline_circle:
  assumes "A \<noteq> 0" and "A * D \<le> (cmod BC)\<^sup>2"
  "cl = circline A BC D" and
  "\<mu> = -BC/cor A" and 
  "r2 = ((cmod BC)\<^sup>2 - A*D) / A\<^sup>2" and "r = sqrt r2"
  shows "cl = circle \<mu> r"
proof-
  have *: "cl = {z. z * cnj z + cnj (BC / cor A) * z + (BC / cor A) * cnj z + cor (D / A) = 0}"
    using \<open>cl = circline A BC D\<close> \<open>A \<noteq> 0\<close>
    by (auto simp add: circline_def field_simps)

  have "r2 \<ge> 0"
  proof-
    have "(cmod BC)\<^sup>2 - A * D \<ge>  0"
      using \<open>A * D \<le> (cmod BC)\<^sup>2\<close>
      by auto
    thus ?thesis
      using \<open>A \<noteq> 0\<close> \<open>r2 = ((cmod BC)\<^sup>2 - A*D) / A\<^sup>2\<close>
      by (metis zero_le_divide_iff zero_le_power2)
  qed
  hence **: "r * r = r2" "r \<ge> 0"
    using \<open>r = sqrt r2\<close>
    by (auto simp add: real_sqrt_mult[symmetric])

  have ***: "- \<mu> * - cnj \<mu> - cor r2 = cor (D / A)"
    using \<open>\<mu> = - BC / complex_of_real A\<close> \<open>r2 = ((cmod BC)\<^sup>2 - A * D) / A\<^sup>2\<close>
    by (auto simp add: power2_eq_square complex_mult_cnj_cmod field_simps)
       (simp add: add_divide_eq_iff assms(1))
  thus ?thesis
    using \<open>r2 = ((cmod BC)\<^sup>2 - A*D) / A\<^sup>2\<close> \<open>\<mu> = - BC / cor A\<close>
    by (subst *, subst circle_equation[of r \<mu>, OF \<open>r \<ge> 0\<close>], subst **) (auto simp add: field_simps power2_eq_square)
qed

lemma circline_ex_circle:
  assumes "A \<noteq> 0" and "A * D \<le> (cmod BC)\<^sup>2" and "cl = circline A BC D"
  shows "\<exists> \<mu> r. cl = circle \<mu> r"
  using circline_circle[OF assms]
  by auto

text \<open>Every Euclidean circle can be represented by a circline\<close>

lemma circle_circline:
  assumes "cl = circle \<mu> r" and "r \<ge> 0"
  shows "cl = circline 1 (-\<mu>) ((cmod \<mu>)\<^sup>2 - r\<^sup>2)"
proof-
  have "complex_of_real ((cmod \<mu>)\<^sup>2 - r\<^sup>2) = \<mu> * cnj \<mu> - complex_of_real (r\<^sup>2)"
    by (auto simp add: complex_mult_cnj_cmod)
  thus "cl = circline 1 (- \<mu>) ((cmod \<mu>)\<^sup>2 - r\<^sup>2)"
    using assms
    using circle_equation[of r \<mu>]
    unfolding circline_def power2_eq_square
    by (simp add: field_simps)
qed

lemma circle_ex_circline:
  assumes "cl = circle \<mu> r" and "r \<ge> 0"
  shows "\<exists> A BC D. A \<noteq> 0 \<and> A*D \<le> (cmod BC)\<^sup>2 \<and> cl = circline A BC D"
  using circle_circline[OF assms]
  using \<open>r \<ge> 0\<close>
  by (rule_tac x=1 in exI, rule_tac x="-\<mu>" in exI, rule_tac x="Re (\<mu> * cnj \<mu>) - (r * r)" in exI) (simp add: complex_mult_cnj_cmod power2_eq_square)

text \<open>Connection between circline and Euclidean line\<close>

text \<open>Every circline with a positive determinant and $A = 0$ represents an Euclidean line\<close>

lemma circline_line:
  assumes
    "A = 0" and "BC \<noteq> 0" and
    "cl = circline A BC D" and
    "z1 = - cor D * BC / (2 * BC * cnj BC)" and
    "z2 = z1 + \<i> * sgn (if arg BC > 0 then -BC else BC)"
  shows
    "cl = line z1 z2"
proof-
  have "cl = {z. cnj BC*z + BC*cnj z + complex_of_real D = 0}"
    using assms
    by (simp add: circline_def)
    have "{z. cnj BC*z + BC*cnj z + complex_of_real D = 0} =
          {z. cnj BC*z + BC*cnj z - (cnj BC*z1 + BC*cnj z1) = 0}"
      using  \<open>BC \<noteq> 0\<close> assms
      by simp
    moreover
    have "z1 \<noteq> z2"
      using \<open>BC \<noteq> 0\<close> assms
      by (auto simp add: sgn_eq)
    moreover
    have "\<exists> k. k \<noteq> 0 \<and> BC = cor k*rot90 (z2 - z1)"
    proof (cases "arg BC > 0")
      case True
      thus ?thesis
        using assms
        by (rule_tac x="(cmod BC)" in exI, auto simp add: Complex_scale4)
    next
      case False
      thus ?thesis
        using assms
        by (rule_tac x="-(cmod BC)" in exI, simp)
           (smt Complex.Re_sgn Im_sgn cis_arg complex_minus complex_surj mult_minus_right rcis_cmod_arg rcis_def)
    qed
    then obtain k where "cor k \<noteq> 0" "BC = cor k*rot90 (z2 - z1)"
      by auto
    moreover
    have *: "\<And> z. cnj_mix (BC / cor k) z - cnj_mix (BC / cor k) z1 = (1/cor k) * (cnj_mix BC z - cnj_mix BC z1)"
      using \<open>cor k \<noteq> 0\<close>
      by (simp add: field_simps)
    hence "{z. cnj_mix BC z - cnj_mix BC z1 = 0} = {z. cnj_mix (BC / cor k) z - cnj_mix (BC / cor k) z1 = 0}"
      using \<open>cor k \<noteq> 0\<close>
      by auto
    ultimately
    have "cl = line z1 z2"
      using line_equation[of z1 z2 "BC/cor k"] \<open>cl = {z. cnj BC*z + BC*cnj z + complex_of_real D = 0}\<close>
      by auto
    thus ?thesis
      using \<open>z1 \<noteq> z2\<close>
      by blast
qed

lemma circline_ex_line:
  assumes "A = 0" and "BC \<noteq> 0" and "cl = circline A BC D"
  shows "\<exists> z1 z2. z1 \<noteq> z2 \<and> cl = line z1 z2"
proof-
  let ?z1 = "- cor D * BC / (2 * BC * cnj BC)"
  let ?z2 = "?z1 + \<i> * sgn (if 0 < arg BC then - BC else BC)"
  have "?z1 \<noteq> ?z2"
    using \<open>BC \<noteq> 0\<close>
    by (simp add: sgn_eq)
  thus ?thesis
    using circline_line[OF assms, of ?z1 ?z2] \<open>BC \<noteq> 0\<close>
    by (rule_tac x="?z1" in exI, rule_tac x="?z2" in exI, simp)
qed

text \<open>Every Euclidean line can be represented by a circline\<close>

lemma line_ex_circline:
  assumes "cl = line z1 z2" and "z1 \<noteq> z2"
  shows "\<exists> BC D. BC \<noteq> 0 \<and> cl = circline 0 BC D"
proof-
  let ?BC = "rot90 (z2 - z1)"
  let ?D = "Re (- 2 * scalprod z1 ?BC)"
  show ?thesis
  proof (rule_tac x="?BC" in exI, rule_tac x="?D" in exI, rule conjI)
    show "?BC \<noteq> 0"
      using \<open>z1 \<noteq> z2\<close> rot90_ii[of "z2 - z1"]
      by auto
  next
    have *: "complex_of_real (Re (- 2 * scalprod z1 (rot90 (z2 - z1)))) = - (cnj_mix z1 (rot90 (z2 - z1)))"
      using rot90_ii[of "z2 - z1"]
      by (cases z1, cases z2, simp add: Complex_eq field_simps)
    show "cl = circline 0 ?BC ?D"
      apply (subst assms, subst line_equation[of z1 z2 ?BC])
      unfolding circline_def
      by (fact, simp, subst *, simp add: field_simps)
  qed
qed

lemma circline_line':
  assumes "z1 \<noteq> z2"
  shows "circline 0 (\<i> * (z2 - z1)) (Re (- cnj_mix (\<i> * (z2 - z1)) z1)) = line z1 z2"
proof-
  let ?B = "\<i> * (z2 - z1)"
  let ?D = "Re (- cnj_mix ?B z1)"
  have "circline 0 ?B ?D = {z. cnj ?B*z + ?B*cnj z + complex_of_real ?D = 0}"
    using assms
    by (simp add: circline_def)
  moreover
  have "is_real (- cnj_mix (\<i> * (z2 - z1)) z1)"
    using cnj_mix_real[of ?B z1]
    by auto
  hence "{z. cnj ?B*z + ?B*cnj z + complex_of_real ?D = 0} =
         {z. cnj ?B*z + ?B*cnj z - (cnj ?B*z1 + ?B*cnj z1) = 0}"
    apply (subst complex_of_real_Re, simp)
    unfolding diff_conv_add_uminus
    by simp
  moreover
  have "line z1 z2 = {z. cnj_mix (\<i> * (z2 - z1)) z - cnj_mix (\<i> * (z2 - z1)) z1 = 0}"
    using line_equation[of z1 z2 ?B] assms
    unfolding rot90_ii
    by simp
  ultimately
  show ?thesis
    by simp
qed

(* ---------------------------------------------------------------------------- *)
subsection \<open>Angle between two circles\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Given a center $\mu$ of an Euclidean circle and a point $E$ on it, we define the tangent vector
in $E$ as the radius vector $\overrightarrow{\mu E}$, rotated by $\pi/2$, clockwise or
counterclockwise, depending on the circle orientation. The Boolean @{term p} encodes the orientation
of the circle, and the function @{term "sgn_bool p"} returns $1$ when @{term p} is true, and
$-1$ when @{term p} is false.\<close>

abbreviation sgn_bool where
  "sgn_bool p \<equiv> if p then 1 else -1"

definition circ_tang_vec :: "complex \<Rightarrow> complex \<Rightarrow> bool \<Rightarrow> complex" where
  "circ_tang_vec \<mu> E p = sgn_bool p * \<i> * (E - \<mu>)"

text \<open>Tangent vector is orthogonal to the radius.\<close>
lemma circ_tang_vec_ortho:
  shows "scalprod (E - \<mu>) (circ_tang_vec \<mu> E p) = 0"
  unfolding circ_tang_vec_def Let_def
  by auto

text \<open>Changing the circle orientation gives the opposite tangent vector.\<close>
lemma circ_tang_vec_opposite_orient:
  shows "circ_tang_vec \<mu> E p = - circ_tang_vec \<mu> E (\<not> p)"
  unfolding circ_tang_vec_def
  by auto

text \<open>Angle between two oriented circles at their common point $E$ is defined as the angle between
tangent vectors at $E$. Again we define three different angle measures.\<close>

text \<open>The oriented angle between two circles at the point $E$. The first circle is
centered at $\mu_1$ and its orientation is given by the Boolean $p_1$, 
while the second circle is centered at $\mu_2$ and its orientation is given by 
the Boolea $p_2$.\<close>
definition ang_circ where 
  "ang_circ E \<mu>1 \<mu>2 p1 p2 = \<angle> (circ_tang_vec \<mu>1 E p1) (circ_tang_vec \<mu>2 E p2)"

text \<open>The unoriented angle between the two circles\<close>
definition ang_circ_c where
  "ang_circ_c E \<mu>1 \<mu>2 p1 p2 = \<angle>c (circ_tang_vec \<mu>1 E p1) (circ_tang_vec \<mu>2 E p2)"

text \<open>The acute angle between the two circles\<close>
definition ang_circ_a where
  "ang_circ_a E \<mu>1 \<mu>2 p1 p2 = \<angle>a (circ_tang_vec \<mu>1 E p1) (circ_tang_vec \<mu>2 E p2)"

text \<open>Explicit expression for oriented angle between two circles\<close>
lemma ang_circ_simp:
  assumes "E \<noteq> \<mu>1" and "E \<noteq> \<mu>2"
  shows "ang_circ E \<mu>1 \<mu>2 p1 p2 =
         \<downharpoonright>arg (E - \<mu>2) - arg (E - \<mu>1) + sgn_bool p1 * pi / 2 - sgn_bool p2 * pi / 2\<downharpoonleft>"
  unfolding ang_circ_def ang_vec_def circ_tang_vec_def
  apply (rule canon_ang_eq)
  using assms
  using arg_mult_2kpi[of "sgn_bool p2*\<i>" "E - \<mu>2"]
  using arg_mult_2kpi[of "sgn_bool p1*\<i>" "E - \<mu>1"]
  apply auto
     apply (rule_tac x="x-xa" in exI, auto simp add: field_simps)
    apply (rule_tac x="-1+x-xa" in exI, auto simp add: field_simps)
   apply (rule_tac x="1+x-xa" in exI, auto simp add: field_simps)
  apply (rule_tac x="x-xa" in exI, auto simp add: field_simps)
  done

text \<open>Explicit expression for the cosine of angle between two circles\<close>
lemma cos_ang_circ_simp:
  assumes "E \<noteq> \<mu>1" and "E \<noteq> \<mu>2"
  shows "cos (ang_circ E \<mu>1 \<mu>2 p1 p2) =
         sgn_bool (p1 = p2) * cos (arg (E - \<mu>2) - arg (E - \<mu>1))"
  using assms
  using cos_periodic_pi2[of "arg (E - \<mu>2) - arg (E - \<mu>1)"]
  using cos_minus_pi[of "arg (E - \<mu>2) - arg (E - \<mu>1)"]
  using ang_circ_simp[OF assms, of p1 p2]
  by auto

text \<open>Explicit expression for the unoriented angle between two circles\<close>
lemma ang_circ_c_simp:
  assumes "E \<noteq> \<mu>1" and "E \<noteq> \<mu>2"
  shows "ang_circ_c E \<mu>1 \<mu>2 p1 p2 = 
        \<bar>\<downharpoonright>arg (E - \<mu>2) - arg (E - \<mu>1) + sgn_bool p1 * pi / 2 - sgn_bool p2 * pi / 2\<downharpoonleft>\<bar>"
  unfolding ang_circ_c_def ang_vec_c_def
  using ang_circ_simp[OF assms]
  unfolding ang_circ_def
  by auto

text \<open>Explicit expression for the acute angle between two circles\<close>
lemma ang_circ_a_simp:
  assumes "E \<noteq> \<mu>1" and "E \<noteq> \<mu>2"
  shows "ang_circ_a E \<mu>1 \<mu>2 p1 p2 = 
         acute_ang (abs (canon_ang (arg(E - \<mu>2) - arg(E - \<mu>1) + (sgn_bool p1) * pi/2 - (sgn_bool p2) * pi/2)))"
  unfolding ang_circ_a_def ang_vec_a_def
  using ang_circ_c_simp[OF assms]
  unfolding ang_circ_c_def
  by auto

text \<open>Acute angle between two circles does not depend on the circle orientation.\<close>
lemma ang_circ_a_pTrue:
  assumes "E \<noteq> \<mu>1" and "E \<noteq> \<mu>2"
  shows "ang_circ_a E \<mu>1 \<mu>2 p1 p2 = ang_circ_a E \<mu>1 \<mu>2 True True"
proof (cases "p1")
  case True
  show ?thesis
  proof (cases "p2")
    case True
    show ?thesis
      using \<open>p1\<close> \<open>p2\<close>
      by simp
  next
    case False
    show ?thesis
      using \<open>p1\<close> \<open>\<not> p2\<close>
      unfolding ang_circ_a_def
      using circ_tang_vec_opposite_orient[of \<mu>2 E p2]
      using ang_vec_a_opposite2
      by simp
  qed
next
  case False
  show ?thesis
  proof (cases "p2")
    case True
    show ?thesis
      using \<open>\<not> p1\<close> \<open>p2\<close>
      unfolding ang_circ_a_def
      using circ_tang_vec_opposite_orient[of \<mu>1 E p1]
      using ang_vec_a_opposite1
      by simp
  next
    case False
    show ?thesis
      using \<open>\<not> p1\<close> \<open>\<not> p2\<close>
      unfolding ang_circ_a_def
      using circ_tang_vec_opposite_orient[of \<mu>1 E p1] circ_tang_vec_opposite_orient[of \<mu>2 E p2]
      using ang_vec_a_opposite1  ang_vec_a_opposite2
      by simp
  qed
qed

text \<open>Definition of the acute angle between the two unoriented circles \<close>
abbreviation ang_circ_a' where
  "ang_circ_a' E \<mu>1 \<mu>2 \<equiv> ang_circ_a E \<mu>1 \<mu>2 True True"

text \<open>A very simple expression for the acute angle between the two circles\<close>
lemma ang_circ_a_simp1:
  assumes "E \<noteq> \<mu>1" and "E \<noteq> \<mu>2"
  shows "ang_circ_a E \<mu>1 \<mu>2 p1 p2 = \<angle>a (E - \<mu>1) (E - \<mu>2)"
  unfolding ang_vec_a_def ang_vec_c_def ang_vec_def
  by (subst ang_circ_a_pTrue[OF assms, of p1 p2], subst ang_circ_a_simp[OF assms, of True True]) (metis add_diff_cancel)

lemma ang_circ_a'_simp:
  assumes "E \<noteq> \<mu>1" and "E \<noteq> \<mu>2"
  shows "ang_circ_a' E \<mu>1 \<mu>2 = \<angle>a (E - \<mu>1) (E - \<mu>2)"
  by (rule ang_circ_a_simp1[OF assms])

end
