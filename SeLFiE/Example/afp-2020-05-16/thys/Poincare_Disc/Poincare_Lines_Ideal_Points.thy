theory Poincare_Lines_Ideal_Points
imports Poincare_Lines
begin

(* ------------------------------------------------------------------ *)
subsection\<open>Ideal points of h-lines\<close>
(* ------------------------------------------------------------------ *)

(* TODO: Introduce ideal points for the oriented circline - 
   it would be a list, not a set of two points *)

text\<open>\emph{Ideal points} of an h-line are points where the h-line intersects the unit disc.\<close>

(* ------------------------------------------------------------------ *)
subsubsection \<open>Calculation of ideal points\<close>
(* ------------------------------------------------------------------ *)

text \<open>We decided to define ideal points constructively, i.e., we calculate the coordinates of ideal
points for a given h-line explicitly. Namely, if the h-line is determined by $A$ and $B$, the two
intersection points are $$\frac{B}{|B|^2}\left(-A \pm i\cdot \sqrt{|B|^2 - A^2}\right).$$\<close>

definition calc_ideal_point1_cvec :: "complex \<Rightarrow> complex \<Rightarrow> complex_vec" where
 [simp]:  "calc_ideal_point1_cvec A B =
    (let discr = Re ((cmod B)\<^sup>2 - (Re A)\<^sup>2) in
         (B*(-A - \<i>*sqrt(discr)), (cmod B)\<^sup>2))"

definition calc_ideal_point2_cvec :: "complex \<Rightarrow> complex \<Rightarrow> complex_vec" where
  [simp]: "calc_ideal_point2_cvec A B =
    (let discr = Re ((cmod B)\<^sup>2 - (Re A)\<^sup>2) in
         (B*(-A + \<i>*sqrt(discr)), (cmod B)\<^sup>2))"

definition calc_ideal_points_cmat_cvec :: "complex_mat \<Rightarrow> complex_vec set" where
 [simp]:  "calc_ideal_points_cmat_cvec H =
    (if is_poincare_line_cmat H then
        let (A, B, C, D) = H
         in {calc_ideal_point1_cvec A B, calc_ideal_point2_cvec A B}
     else
        {(-1, 1), (1, 1)})"

lift_definition calc_ideal_points_clmat_hcoords :: "circline_mat \<Rightarrow> complex_homo_coords set" is calc_ideal_points_cmat_cvec
  by (auto simp add: Let_def split: if_split_asm)

lift_definition calc_ideal_points :: "circline \<Rightarrow> complex_homo set" is calc_ideal_points_clmat_hcoords
proof transfer
  fix H1 H2
  assume hh: "hermitean H1 \<and> H1 \<noteq> mat_zero" "hermitean H2 \<and> H2 \<noteq> mat_zero"
  obtain A1 B1 C1 D1 A2 B2 C2 D2 where *: "H1 = (A1, B1, C1, D1)" "H2 = (A2, B2, C2, D2)"
    by (cases H1, cases H2, auto)
  assume "circline_eq_cmat H1 H2"
  then obtain k where k: "k \<noteq> 0" "H2 = cor k *\<^sub>s\<^sub>m H1"
    by auto
  thus "rel_set (\<approx>\<^sub>v) (calc_ideal_points_cmat_cvec H1) (calc_ideal_points_cmat_cvec H2)"
  proof (cases "is_poincare_line_cmat H1")
    case True
    hence "is_poincare_line_cmat H2"
      using k * hermitean_mult_real[of H1 k] hh
      by (auto simp add: power2_eq_square)
    have **: "sqrt (\<bar>k\<bar> * cmod B1 * (\<bar>k\<bar> * cmod B1) - k * Re D1 * (k * Re D1)) =
         \<bar>k\<bar> * sqrt(cmod B1 * cmod B1 - Re D1 * Re D1)"
    proof-
      have "\<bar>k\<bar> * cmod B1 * (\<bar>k\<bar> * cmod B1) - k * Re D1 * (k * Re D1) =
            k\<^sup>2 * (cmod B1 * cmod B1 - Re D1 * Re D1)"
        by (simp add: power2_eq_square field_simps)
      thus ?thesis
        by (simp add: real_sqrt_mult)
    qed
    show ?thesis
      using \<open>is_poincare_line_cmat H1\<close> \<open>is_poincare_line_cmat H2\<close>
      using * k
      apply (simp add: Let_def)
      apply safe
      apply (simp add: power2_eq_square rel_set_def)
      apply safe
         apply (cases "k > 0")
          apply (rule_tac x="(cor k)\<^sup>2" in exI)
          apply (subst **)
          apply (simp add: power2_eq_square field_simps)
         apply (erule notE, rule_tac x="(cor k)\<^sup>2" in exI)
         apply (subst **)
         apply (simp add: power2_eq_square field_simps)
        apply (cases "k > 0")
        apply (erule notE, rule_tac x="(cor k)\<^sup>2" in exI)
        apply (subst **)
        apply (simp add: power2_eq_square field_simps)
        apply (rule_tac x="(cor k)\<^sup>2" in exI)
        apply (subst **)
        apply (simp add: power2_eq_square field_simps)
       apply (cases "k > 0")
        apply (rule_tac x="(cor k)\<^sup>2" in exI)
        apply (subst **)
        apply (simp add: power2_eq_square field_simps)
       apply (erule notE, rule_tac x="(cor k)\<^sup>2" in exI)
       apply (subst **)
       apply (simp add: power2_eq_square field_simps)
      apply (cases "k > 0")
       apply (erule notE, rule_tac x="(cor k)\<^sup>2" in exI)
       apply (subst **)
       apply (simp add: power2_eq_square field_simps)
      apply (rule_tac x="(cor k)\<^sup>2" in exI)
      apply (subst **)
      apply (simp add: power2_eq_square field_simps)
      done
  next
    case False
    hence "\<not> is_poincare_line_cmat H2"
      using k * hermitean_mult_real[of H1 k] hh
      by (auto simp add: power2_eq_square)
    have "rel_set (\<approx>\<^sub>v) {(- 1, 1), (1, 1)} {(- 1, 1), (1, 1)}"
      by (simp add: rel_set_def)
    thus ?thesis
      using \<open>\<not> is_poincare_line_cmat H1\<close> \<open>\<not> is_poincare_line_cmat H2\<close>
      using *
      apply (simp add: Let_def)
      apply safe
      done
  qed
qed

text \<open>Correctness of the calculation\<close>

text\<open>We show that for every h-line its two calculated ideal points are different and are on the
intersection of that line and the unit circle.\<close>

text \<open>Calculated ideal points are on the unit circle\<close>

lemma calc_ideal_point_1_unit:
  assumes "is_real A" "(cmod B)\<^sup>2 > (cmod A)\<^sup>2"
  assumes "(z1, z2) = calc_ideal_point1_cvec A B"
  shows "z1 * cnj z1 = z2 * cnj z2"
proof-
  let ?discr = "Re ((cmod B)\<^sup>2 - (Re A)\<^sup>2)"
  have "?discr > 0"
    using assms
    by (simp add: cmod_power2)
  have "(B*(-A - \<i>*sqrt(?discr))) * cnj (B*(-A - \<i>*sqrt(?discr))) = (B * cnj B) * (A\<^sup>2 + cor (abs ?discr))"
    using \<open>is_real A\<close> eq_cnj_iff_real[of A]
    by (simp add: field_simps power2_eq_square)
  also have "... = (B * cnj B) * (cmod B)\<^sup>2"
    using \<open>?discr > 0\<close>
    using assms
    using complex_of_real_Re[of "(cmod B)\<^sup>2 - (Re A)\<^sup>2"] complex_of_real_Re[of A] \<open>is_real A\<close>
    by (simp add: power2_eq_square)
  also have "... = (cmod B)\<^sup>2 * cnj ((cmod B)\<^sup>2)"
    using complex_cnj_complex_of_real complex_mult_cnj_cmod
    by presburger
  finally show ?thesis
    using assms
    by simp
qed

lemma calc_ideal_point_2_unit:
  assumes "is_real A" "(cmod B)\<^sup>2 > (cmod A)\<^sup>2"
  assumes "(z1, z2) = calc_ideal_point2_cvec A B"
  shows "z1 * cnj z1 = z2 * cnj z2"
proof-
  let ?discr = "Re ((cmod B)\<^sup>2 - (Re A)\<^sup>2)"
  have "?discr > 0"
    using assms
    by (simp add: cmod_power2)
  have "(B*(-A + \<i>*sqrt(?discr))) * cnj (B*(-A + \<i>*sqrt(?discr))) = (B * cnj B) * (A\<^sup>2 + cor (abs ?discr))"
    using \<open>is_real A\<close> eq_cnj_iff_real[of A]
    by (simp add: field_simps power2_eq_square)
  also have "... = (B * cnj B) * (cmod B)\<^sup>2"
    using \<open>?discr > 0\<close>
    using assms
    using complex_of_real_Re[of "(cmod B)\<^sup>2 - (Re A)\<^sup>2"] complex_of_real_Re[of A] \<open>is_real A\<close>
    by (simp add: power2_eq_square)
  also have "... = (cmod B)\<^sup>2 * cnj ((cmod B)\<^sup>2)"
    using complex_cnj_complex_of_real complex_mult_cnj_cmod
    by presburger
  finally show ?thesis
    using assms
    by simp
qed

lemma calc_ideal_points_on_unit_circle:
  shows "\<forall> z \<in> calc_ideal_points H. z \<in> circline_set unit_circle"
  unfolding circline_set_def
  apply simp
proof (transfer, transfer)
  fix H
  assume hh: "hermitean H \<and> H \<noteq> mat_zero"
  obtain A B C D where *: "H = (A, B, C, D)"
    by (cases H, auto)
  have "\<forall> (z1, z2) \<in> calc_ideal_points_cmat_cvec H. z1 * cnj z1 = z2 * cnj z2"
    using hermitean_elems[of A B C D]
    unfolding calc_ideal_points_cmat_cvec_def
    using calc_ideal_point_1_unit[of A B]
    using calc_ideal_point_2_unit[of A B]
    using hh *
    apply (cases "calc_ideal_point1_cvec A B", cases "calc_ideal_point2_cvec A B")
    apply (auto simp add: Let_def simp del: calc_ideal_point1_cvec_def calc_ideal_point2_cvec_def)
    done
  thus "Ball (calc_ideal_points_cmat_cvec H) (on_circline_cmat_cvec unit_circle_cmat)"
    using on_circline_cmat_cvec_unit
    by (auto simp del: on_circline_cmat_cvec_def calc_ideal_points_cmat_cvec_def)
qed

text \<open>Calculated ideal points are on the h-line\<close>

lemma calc_ideal_point1_sq:
  assumes "(z1, z2) = calc_ideal_point1_cvec A B" "is_real A" "(cmod B)\<^sup>2 > (cmod A)\<^sup>2"
  shows "z1 * cnj z1 + z2 * cnj z2 = 2 * (B * cnj B)\<^sup>2"
proof-
  let ?discr = "Re ((cmod B)\<^sup>2 - (Re A)\<^sup>2)"
  have "?discr > 0"
    using assms
    by (simp add: cmod_power2)
  have "z1 * cnj z1 = (B * cnj B) * (-A + \<i>*sqrt(?discr))*(-A - \<i>*sqrt(?discr))"
    using assms eq_cnj_iff_real[of A]
    by (simp)
  also have "... = (B * cnj B) * (A\<^sup>2 + ?discr)"
    using complex_of_real_Re[of A] \<open>is_real A\<close> \<open>?discr > 0\<close>
    by (simp add: power2_eq_square field_simps)
  finally
  have "z1 * cnj z1 = (B * cnj B)\<^sup>2"
    using complex_of_real_Re[of "(cmod B)\<^sup>2 - (Re A)\<^sup>2"] complex_of_real_Re[of A] \<open>is_real A\<close>
    using complex_mult_cnj_cmod[of B]
    by (simp add: power2_eq_square)
  moreover
  have "z2 * cnj z2 = (B * cnj B)\<^sup>2"
    using assms
    by simp
  ultimately
  show ?thesis
    by simp
qed

lemma calc_ideal_point2_sq:
  assumes "(z1, z2) = calc_ideal_point2_cvec A B" "is_real A" "(cmod B)\<^sup>2 > (cmod A)\<^sup>2"
  shows "z1 * cnj z1 + z2 * cnj z2 = 2 * (B * cnj B)\<^sup>2"
proof-
  let ?discr = "Re ((cmod B)\<^sup>2 - (Re A)\<^sup>2)"
  have "?discr > 0"
    using assms
    by (simp add: cmod_power2)
  have "z1 * cnj z1 = (B * cnj B) * (-A + \<i>*sqrt(?discr))*(-A - \<i>*sqrt(?discr))"
    using assms eq_cnj_iff_real[of A]
    by simp
  also have "... = (B * cnj B) * (A\<^sup>2 + ?discr)"
    using complex_of_real_Re[of A] \<open>is_real A\<close> \<open>?discr > 0\<close>
    by (simp add: power2_eq_square field_simps)
  finally
  have "z1 * cnj z1 = (B * cnj B)\<^sup>2"
    using complex_of_real_Re[of "(cmod B)\<^sup>2 - (Re A)\<^sup>2"] complex_of_real_Re[of A] \<open>is_real A\<close>
    using complex_mult_cnj_cmod[of B]
    by (simp add: power2_eq_square)
  moreover
  have "z2 * cnj z2 = (B * cnj B)\<^sup>2"
    using assms
    by simp
  ultimately
  show ?thesis
    by simp
qed

lemma calc_ideal_point1_mix:
  assumes "(z1, z2) = calc_ideal_point1_cvec A B" "is_real A" "(cmod B)\<^sup>2 > (cmod A)\<^sup>2"
  shows "B * cnj z1 * z2 + cnj B * z1 * cnj z2 = - 2 * A * (B * cnj B)\<^sup>2 "
proof-
  have "B*cnj z1 + cnj B*z1 = -2*A*B*cnj B"
    using assms eq_cnj_iff_real[of A]
    by (simp, simp add: field_simps)
  moreover
  have "cnj z2 = z2"
    using assms
    by simp
  hence "B*cnj z1*z2 + cnj B*z1*cnj z2 = (B*cnj z1 + cnj B*z1)*z2"
    by (simp add: field_simps)
  ultimately
  have "B*cnj z1*z2 + cnj B*z1*cnj z2 = -2*A*(B* cnj B)*z2"
    by simp
  also have "\<dots> = -2*A*(B * cnj B)\<^sup>2"
    using assms
    using complex_mult_cnj_cmod[of B]
    by (simp add: power2_eq_square)
  finally
  show ?thesis
    .
qed

lemma calc_ideal_point2_mix:
  assumes "(z1, z2) = calc_ideal_point2_cvec A B" "is_real A" "(cmod B)\<^sup>2 > (cmod A)\<^sup>2"
  shows "B * cnj z1 * z2 + cnj B * z1 * cnj z2 = - 2 * A * (B * cnj B)\<^sup>2 "
proof-
  have "B*cnj z1 + cnj B*z1 = -2*A*B*cnj B"
    using assms eq_cnj_iff_real[of A]
    by (simp, simp add: field_simps)
  moreover
  have "cnj z2 = z2"
    using assms
    by simp
  hence "B*cnj z1*z2 + cnj B*z1*cnj z2 = (B*cnj z1 + cnj B*z1)*z2"
    by (simp add: field_simps)
  ultimately
  have "B*cnj z1*z2 + cnj B*z1*cnj z2 = -2*A*(B* cnj B)*z2"
    by simp
  also have "\<dots> = -2*A*(B * cnj B)\<^sup>2"
    using assms
    using complex_mult_cnj_cmod[of B]
    by (simp add: power2_eq_square)
  finally
  show ?thesis
    .
qed

lemma calc_ideal_point1_on_circline:
  assumes "(z1, z2) = calc_ideal_point1_cvec A B" "is_real A" "(cmod B)\<^sup>2 > (cmod A)\<^sup>2"
  shows "A*z1*cnj z1 + B*cnj z1*z2 + cnj B*z1*cnj z2 + A*z2*cnj z2 = 0" (is "?lhs = 0")
proof-
  have "?lhs = A * (z1 * cnj z1 + z2 * cnj z2) + (B * cnj z1 * z2 + cnj B * z1 * cnj z2)"
    by (simp add: field_simps)
  also have "... = 2*A*(B*cnj B)\<^sup>2 + (-2*A*(B*cnj B)\<^sup>2)"
    using calc_ideal_point1_sq[OF assms]
    using calc_ideal_point1_mix[OF assms]
    by simp
  finally
  show ?thesis
    by simp
qed

lemma calc_ideal_point2_on_circline:
  assumes "(z1, z2) = calc_ideal_point2_cvec A B" "is_real A" "(cmod B)\<^sup>2 > (cmod A)\<^sup>2"
  shows "A*z1*cnj z1 + B*cnj z1*z2 + cnj B*z1*cnj z2 + A*z2*cnj z2 = 0" (is "?lhs = 0")
proof-
  have "?lhs = A * (z1 * cnj z1 + z2 * cnj z2) + (B * cnj z1 * z2 + cnj B * z1 * cnj z2)"
    by (simp add: field_simps)
  also have "... = 2*A*(B*cnj B)\<^sup>2 + (-2*A*(B*cnj B)\<^sup>2)"
    using calc_ideal_point2_sq[OF assms]
    using calc_ideal_point2_mix[OF assms]
    by simp
  finally
  show ?thesis
    by simp
qed

lemma calc_ideal_points_on_circline:
  assumes "is_poincare_line H"
  shows "\<forall> z \<in> calc_ideal_points H. z \<in> circline_set H"
  using assms
  unfolding circline_set_def
  apply simp
proof (transfer, transfer)
  fix H
  assume hh: "hermitean H \<and> H \<noteq> mat_zero"
  obtain A B C D where *: "H = (A, B, C, D)"
    by (cases H, auto)
  obtain z11 z12 z21 z22 where **: "(z11, z12) = calc_ideal_point1_cvec A B" "(z21, z22) = calc_ideal_point2_cvec A B"
    by (cases "calc_ideal_point1_cvec A B", cases "calc_ideal_point2_cvec A B") auto

  assume "is_poincare_line_cmat H"
  hence "\<forall> (z1, z2) \<in> calc_ideal_points_cmat_cvec H. A*z1*cnj z1 + B*cnj z1*z2 + C*z1*cnj z2 + D*z2*cnj z2 = 0"
    using * ** hh
    using hermitean_elems[of A B C D]
    using calc_ideal_point1_on_circline[of z11 z12 A B]
    using calc_ideal_point2_on_circline[of z21 z22 A B]
    by (auto simp del: calc_ideal_point1_cvec_def calc_ideal_point2_cvec_def)
  thus "Ball (calc_ideal_points_cmat_cvec H) (on_circline_cmat_cvec H)"
    using on_circline_cmat_cvec_circline_equation *
    by (auto simp del: on_circline_cmat_cvec_def calc_ideal_points_cmat_cvec_def simp add: field_simps)
qed

text \<open>Calculated ideal points of an h-line are different\<close>

lemma calc_ideal_points_cvec_different [simp]:
  assumes "(cmod B)\<^sup>2 > (cmod A)\<^sup>2" "is_real A"
  shows "\<not> (calc_ideal_point1_cvec A B \<approx>\<^sub>v calc_ideal_point2_cvec A B)"
  using assms
  by (auto) (auto simp add: cmod_def)

lemma calc_ideal_points_different:
  assumes "is_poincare_line H"
  shows  "\<exists> i1 \<in> (calc_ideal_points H). \<exists> i2 \<in> (calc_ideal_points H). i1 \<noteq> i2"
  using assms
proof (transfer, transfer)
  fix H
  assume hh: "hermitean H \<and> H \<noteq> mat_zero" "is_poincare_line_cmat H"
  obtain A B C D where *: "H = (A, B, C, D)"
    by (cases H, auto)
  hence "is_real A" using hh hermitean_elems by auto
  thus "\<exists>i1\<in>calc_ideal_points_cmat_cvec H. \<exists>i2\<in>calc_ideal_points_cmat_cvec H. \<not> i1 \<approx>\<^sub>v i2"
    using * hh calc_ideal_points_cvec_different[of A B]
    apply (rule_tac x="calc_ideal_point1_cvec A B" in bexI)
    apply (rule_tac x="calc_ideal_point2_cvec A B" in bexI)
    by auto
qed

lemma two_calc_ideal_points [simp]:
  assumes "is_poincare_line H"                
  shows "card (calc_ideal_points H) = 2"
proof-
  have  "\<exists> x \<in> calc_ideal_points H. \<exists> y \<in> calc_ideal_points H. \<forall> z \<in> calc_ideal_points H. z = x \<or> z = y"
    by (transfer, transfer, case_tac H, simp del: calc_ideal_point1_cvec_def calc_ideal_point2_cvec_def)
  then obtain x y where *: "calc_ideal_points H = {x, y}"
    by auto
  moreover
  have "x \<noteq> y"
    using calc_ideal_points_different[OF assms] *
    by auto
  ultimately
  show ?thesis
    by auto
qed

subsubsection \<open>Ideal points\<close>

text \<open>Next we give a genuine definition of ideal points -- these are the intersections of the h-line with the unit circle\<close>

definition ideal_points :: "circline \<Rightarrow> complex_homo set" where
  "ideal_points H = circline_intersection H unit_circle"

text \<open>Ideal points are on the unit circle and on the h-line\<close>
lemma ideal_points_on_unit_circle:
  shows "\<forall> z \<in> ideal_points H. z \<in> circline_set unit_circle"
  unfolding ideal_points_def circline_intersection_def circline_set_def
  by simp

lemma ideal_points_on_circline:
  shows "\<forall> z \<in> ideal_points H. z \<in> circline_set H"
  unfolding ideal_points_def circline_intersection_def circline_set_def
  by simp


text \<open>For each h-line there are exactly two ideal points\<close>
lemma two_ideal_points:
  assumes "is_poincare_line H"
  shows "card (ideal_points H) = 2"
proof-
  have "H \<noteq> unit_circle"
    using assms not_is_poincare_line_unit_circle
    by auto
  let ?int = "circline_intersection H unit_circle"
  obtain i1 i2 where "i1 \<in> ?int" "i2 \<in> ?int" "i1 \<noteq> i2"
    using calc_ideal_points_on_circline[OF assms]
    using calc_ideal_points_on_unit_circle[of H]
    using calc_ideal_points_different[OF assms]
    unfolding circline_intersection_def circline_set_def
    by auto
  thus ?thesis
    unfolding ideal_points_def
    using circline_intersection_at_most_2_points[OF \<open>H \<noteq> unit_circle\<close>]
    using card_geq_2_iff_contains_2_elems[of ?int]
    by auto
qed

text \<open>They are exactly the two points that our calculation finds\<close>
lemma ideal_points_unique:
  assumes "is_poincare_line H"
  shows "ideal_points H = calc_ideal_points H"
proof-
  have "calc_ideal_points H \<subseteq> ideal_points H"
    using calc_ideal_points_on_circline[OF assms]
    using calc_ideal_points_on_unit_circle[of H]
    unfolding ideal_points_def circline_intersection_def circline_set_def
    by auto
  moreover
  have "H \<noteq> unit_circle"
    using not_is_poincare_line_unit_circle assms
    by auto
  hence "finite (ideal_points H)"
    using circline_intersection_at_most_2_points[of H unit_circle]
    unfolding ideal_points_def
    by auto
  ultimately
  show ?thesis
    using card_subset_eq[of "ideal_points H" "calc_ideal_points H"]
    using two_calc_ideal_points[OF assms]
    using two_ideal_points[OF assms]
    by auto
qed

text \<open>For each h-line we can obtain two different ideal points\<close>
lemma obtain_ideal_points:
  assumes "is_poincare_line H"
  obtains i1 i2 where "i1 \<noteq> i2" "ideal_points H = {i1, i2}"
  using two_ideal_points[OF assms] card_eq_2_iff_doubleton[of "ideal_points H"]
  by blast

text \<open>Ideal points of each h-line constructed from two points in the disc are different than those two points\<close>
lemma ideal_points_different:
  assumes "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
  assumes "ideal_points (poincare_line u v) = {i1, i2}"
  shows "i1 \<noteq> i2" "u \<noteq> i1" "u \<noteq> i2" "v \<noteq> i1" "v \<noteq> i2"
proof-
  have "i1 \<in> ocircline_set ounit_circle" "i2 \<in> ocircline_set ounit_circle"
    using assms(3) assms(4) ideal_points_on_unit_circle is_poincare_line_poincare_line
    by fastforce+
  thus "u \<noteq> i1" "u \<noteq> i2" "v \<noteq> i1" "v \<noteq> i2"
    using assms(1-2)
    using disc_inter_ocircline_set[of ounit_circle]
    unfolding unit_disc_def
    by auto
  show "i1 \<noteq> i2"
    using assms
    by (metis doubleton_eq_iff is_poincare_line_poincare_line obtain_ideal_points)
qed

text \<open>H-line is uniquely determined by its ideal points\<close>
lemma ideal_points_line_unique:        
  assumes "is_poincare_line H" "ideal_points H = {i1, i2}"
  shows "H = poincare_line i1 i2"
  by (smt assms(1) assms(2) calc_ideal_points_on_unit_circle circline_set_def ex_poincare_line_points ideal_points_different(1) ideal_points_on_circline ideal_points_unique insertI1 insert_commute inversion_unit_circle mem_Collect_eq unique_poincare_line_general)

text \<open>Ideal points of some special h-lines\<close>

text\<open>Ideal points of @{term x_axis}\<close>
lemma ideal_points_x_axis
  [simp]: "ideal_points x_axis = {of_complex (-1), of_complex 1}"
proof (subst ideal_points_unique, simp)
  have "calc_ideal_points_clmat_hcoords x_axis_clmat = {of_complex_hcoords (- 1), of_complex_hcoords 1}"
    by transfer auto
  thus "calc_ideal_points x_axis = {of_complex (- 1), of_complex 1}"
    by (simp add: calc_ideal_points.abs_eq of_complex.abs_eq x_axis_def)
qed

text \<open>Ideal points are proportional vectors only if h-line is a line segment passing trough zero\<close>
lemma ideal_points_proportional:
  assumes "is_poincare_line H" "ideal_points H = {i1, i2}" "to_complex i1 = cor k * to_complex i2"
  shows "0\<^sub>h \<in> circline_set H"
proof-
  have "i1 \<noteq> i2"
    using `ideal_points H = {i1, i2}`
    using `is_poincare_line H` ex_poincare_line_points ideal_points_different(1) by blast

  have "i1 \<in> circline_set unit_circle" "i2 \<in> circline_set unit_circle"
    using assms calc_ideal_points_on_unit_circle ideal_points_unique 
    by blast+

  hence "cmod (cor k) = 1"
    using `to_complex i1 = cor k * to_complex i2`
    by (metis (mono_tags, lifting) circline_set_unit_circle imageE mem_Collect_eq mult.right_neutral norm_mult to_complex_of_complex unit_circle_set_def)
  hence "k = -1"
    using `to_complex i1 = cor k * to_complex i2` `i1 \<noteq> i2`
    using \<open>i1 \<in> circline_set unit_circle\<close> \<open>i2 \<in> circline_set unit_circle\<close> 
    by (metis (no_types, lifting) circline_set_unit_circle complex_cnj_complex_of_real complex_mult_cnj_cmod cor_neg_one imageE mult_cancel_right2 norm_one of_real_eq_iff square_eq_1_iff to_complex_of_complex)

  have "\<forall> i1 \<in> calc_ideal_points H. \<forall> i2 \<in> calc_ideal_points H. is_poincare_line H \<and> i1 \<noteq> i2 \<and> to_complex i1 = - to_complex i2 \<longrightarrow> 
           0\<^sub>h \<in> circline_set H"
    unfolding circline_set_def
  proof (simp, transfer, transfer, safe)
    fix A B C D i11 i12 i21 i22 k
    assume H:"hermitean (A, B, C, D)" "(A, B, C, D) \<noteq> mat_zero" 
    assume line: "is_poincare_line_cmat (A, B, C, D)"
    assume i1: "(i11, i12) \<in> calc_ideal_points_cmat_cvec (A, B, C, D)"
    assume i2:"(i21, i22) \<in> calc_ideal_points_cmat_cvec (A, B, C, D)"
    assume "\<not> (i11, i12) \<approx>\<^sub>v (i21, i22)"
    assume opposite: "to_complex_cvec (i11, i12) = - to_complex_cvec (i21, i22)"


    let ?discr =  "sqrt ((cmod B)\<^sup>2 - (Re D)\<^sup>2)"
    let ?den = "(cmod B)\<^sup>2"
    let ?i1 = "B * (- D - \<i> * ?discr)"
    let ?i2 = "B * (- D + \<i> * ?discr)"

    have "i11 = ?i1 \<or> i11 = ?i2" "i12 = ?den"
      "i21 = ?i1 \<or> i21 = ?i2" "i22 = ?den"  
      using i1 i2 H line
      by (auto split: if_split_asm)
    hence i: "i11 = ?i1 \<and> i21 = ?i2 \<or> i11 = ?i2 \<and> i21 = ?i1"
      using `\<not> (i11, i12) \<approx>\<^sub>v (i21, i22)`
      by auto

    have "?den \<noteq> 0"
      using line
      by auto

    hence "i11 = - i21"
      using opposite `i12 = ?den` `i22 = ?den`
      by (simp add: nonzero_neg_divide_eq_eq2)

    hence "?i1 = - ?i2"
      using i 
      by (metis add.inverse_inverse)

    hence "D = 0"
      using `?den \<noteq> 0`
      by (simp add: field_simps)

    thus "on_circline_cmat_cvec (A, B, C, D) 0\<^sub>v"
      by (simp add: vec_cnj_def)
  qed

  thus ?thesis
    using assms `k = -1`
    using calc_ideal_points_different ideal_points_unique
    by fastforce
qed

text \<open>Transformations of ideal points\<close>

text \<open>Möbius transformations that fix the unit disc when acting on h-lines map their ideal points to ideal points.\<close>
lemma ideal_points_moebius_circline [simp]:
  assumes  "unit_circle_fix M" "is_poincare_line H"
  shows "ideal_points (moebius_circline M H) = (moebius_pt M) ` (ideal_points H)" (is "?I' = ?M ` ?I")
proof-
  obtain i1 i2 where *: "i1 \<noteq> i2" "?I = {i1, i2}"
    using assms(2)
    by (rule obtain_ideal_points)
  let ?Mi1 = "?M i1" and ?Mi2 = "?M i2"
  have "?Mi1 \<in> ?M ` (circline_set H)"
       "?Mi2 \<in> ?M ` (circline_set H)"
       "?Mi1 \<in> ?M ` (circline_set unit_circle)"
       "?Mi2 \<in> ?M ` (circline_set unit_circle)"
    using *
    unfolding ideal_points_def circline_intersection_def circline_set_def
    by blast+
  hence "?Mi1 \<in> ?I'"
        "?Mi2 \<in> ?I'"
    using unit_circle_fix_iff[of M] assms
    unfolding ideal_points_def circline_intersection_def circline_set_def
    by (metis mem_Collect_eq moebius_circline)+
  moreover
  have "?Mi1 \<noteq> ?Mi2"
    using bij_moebius_pt[of M] *
    using moebius_pt_invert by blast
  moreover
  have "is_poincare_line (moebius_circline M H)"
    using assms unit_circle_fix_preserve_is_poincare_line
    by simp
  ultimately
  have "?I' = {?Mi1, ?Mi2}"
    using two_ideal_points[of "moebius_circline M H"]
    using card_eq_2_doubleton[of ?I' ?Mi1 ?Mi2]
    by simp
  thus ?thesis
    using *(2)
    by auto
qed

lemma ideal_points_poincare_line_moebius [simp]:
  assumes "unit_disc_fix M"  "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
  assumes "ideal_points (poincare_line u v) = {i1, i2}"
  shows "ideal_points (poincare_line (moebius_pt M u) (moebius_pt M v)) = {moebius_pt M i1, moebius_pt M i2}"
  using assms
  by auto

text \<open>Conjugation also maps ideal points to ideal points\<close>
lemma ideal_points_conjugate [simp]:
  assumes "is_poincare_line H"
  shows "ideal_points (conjugate_circline H) = conjugate ` (ideal_points H)" (is "?I' = ?M ` ?I")
proof-
  obtain i1 i2 where *: "i1 \<noteq> i2" "?I = {i1, i2}"
    using assms
    by (rule obtain_ideal_points)
  let ?Mi1 = "?M i1" and ?Mi2 = "?M i2"
  have "?Mi1 \<in> ?M ` (circline_set H)"
       "?Mi2 \<in> ?M ` (circline_set H)"
       "?Mi1 \<in> ?M ` (circline_set unit_circle)"
       "?Mi2 \<in> ?M ` (circline_set unit_circle)"
    using *
    unfolding ideal_points_def circline_intersection_def circline_set_def
    by blast+                                   
  hence "?Mi1 \<in> ?I'"
        "?Mi2 \<in> ?I'"
    unfolding ideal_points_def circline_intersection_def circline_set_def
    using circline_set_conjugate_circline circline_set_def conjugate_unit_circle_set 
    by blast+
  moreover
  have "?Mi1 \<noteq> ?Mi2"
    using \<open>i1 \<noteq> i2\<close>
    by (auto simp add: conjugate_inj)
  moreover
  have "is_poincare_line (conjugate_circline H)"
    using assms
    by simp
  ultimately
  have "?I' = {?Mi1, ?Mi2}"
    using two_ideal_points[of "conjugate_circline H"]
    using card_eq_2_doubleton[of ?I' ?Mi1 ?Mi2]
    by simp
  thus ?thesis
    using *(2)
    by auto
qed

lemma ideal_points_poincare_line_conjugate [simp]:
  assumes"u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
  assumes "ideal_points (poincare_line u v) = {i1, i2}"
  shows "ideal_points (poincare_line (conjugate u) (conjugate v)) = {conjugate i1, conjugate i2}"
  using assms
  by auto

end
