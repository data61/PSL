(*
  File:    Triangle.thy
  Author:  Manuel Eberl <eberlm@in.tum.de>

  Sine and cosine laws, angle sum in a triangle, congruence theorems,
  Isosceles Triangle Theorem
*)

section \<open>Basic Properties of Triangles\<close>
theory Triangle
imports
  Complex_Main
  "HOL-Analysis.Topology_Euclidean_Space"
  Angles
begin

text \<open>
  We prove a number of basic geometric properties of triangles. All theorems hold
  in any real inner product space.
\<close>
subsection \<open>Thales' theorem\<close>

theorem thales:
  fixes A B C :: "'a :: real_inner"
  assumes "dist B (midpoint A C) = dist A C / 2"
  shows   "orthogonal (A - B) (C - B)"
proof -
  have "dist A C ^ 2 = dist B (midpoint A C) ^ 2 * 4"
    by (subst assms) (simp add: field_simps power2_eq_square)
  thus ?thesis
    by (auto simp: orthogonal_def dist_norm power2_norm_eq_inner midpoint_def
                   algebra_simps inner_commute)
qed

subsection \<open>Sine and cosine laws\<close>

text \<open>
  The proof of the Law of Cosines follows trivially from the definition of the angle,
  the definition of the norm in vector spaces with an inner product and the bilinearity
  of the inner product.
\<close>

lemma cosine_law_vector:
  "norm (u - v) ^ 2 = norm u ^ 2 + norm v ^ 2 - 2 * norm u * norm v * cos (vangle u v)"
  by (simp add: power2_norm_eq_inner cos_vangle algebra_simps inner_commute)

lemma cosine_law_triangle:
  "dist b c ^ 2 = dist a b ^ 2 + dist a c ^ 2 - 2 * dist a b * dist a c * cos (angle b a c)"
  using cosine_law_vector[of "b - a" "c - a"]
  by (simp add: dist_norm angle_def vangle_commute norm_minus_commute)


text \<open>
  According to our definition, angles are always between $0$ and $\pi$ and therefore,
  the sign of an angle is always non-negative. We can therefore look at
  $\sin(\alpha)^2$, which we can express in terms of $\cos(\alpha)$ using the
  identity $\sin(\alpha)^2 + \cos(\alpha)^2 = 1$. The remaining proof is then a
  trivial consequence of the definitions.
\<close>
lemma sine_law_triangle:
  "sin (angle a b c) * dist b c = sin (angle b a c) * dist a c" (is "?A = ?B")
proof (cases "a = b")
  assume neq: "a \<noteq> b"
  show ?thesis
  proof (rule power2_eq_imp_eq)
    from neq have "(sin (angle a b c) * dist b c) ^ 2 * dist a b ^ 2 =
                     dist a b ^ 2 * dist b c ^ 2 - ((a - b) \<bullet> (c - b)) ^ 2"
      by (simp add: sin_squared_eq cos_angle dist_commute field_simps)
    also have "\<dots> = dist a b ^ 2 * dist a c ^ 2 - ((b - a) \<bullet> (c - a)) ^ 2"
      by (simp only: dist_norm power2_norm_eq_inner)
         (simp add: power2_eq_square algebra_simps inner_commute)
    also from neq have "\<dots> = (sin (angle b a c) * dist a c) ^ 2 * dist a b ^ 2"
      by (simp add: sin_squared_eq cos_angle dist_commute field_simps)
    finally show "?A^2 = ?B^2" using neq by (subst (asm) mult_cancel_right) simp_all
  qed (auto intro!: mult_nonneg_nonneg sin_angle_nonneg)
qed simp_all


text \<open>
  The following forms of the Law of Sines/Cosines are more convenient for eliminating
  sines/cosines from a goal completely.
\<close>

lemma cosine_law_triangle':
  "2 * dist a b * dist a c * cos (angle b a c) = (dist a b ^ 2 + dist a c ^ 2 - dist b c ^ 2)"
  using cosine_law_triangle[of b c a] by simp

lemma cosine_law_triangle'':
  "cos (angle b a c) = (dist a b ^ 2 + dist a c ^ 2 - dist b c ^ 2) / (2 * dist a b * dist a c)"
  using cosine_law_triangle[of b c a] by simp

lemma sine_law_triangle':
  "b \<noteq> c \<Longrightarrow> sin (angle a b c) = sin (angle b a c) * dist a c / dist b c"
  using sine_law_triangle[of a b c] by (simp add: divide_simps)

lemma sine_law_triangle'':
  "b \<noteq> c \<Longrightarrow> sin (angle c b a) = sin (angle b a c) * dist a c / dist b c"
  using sine_law_triangle[of a b c] by (simp add: divide_simps angle_commute)


subsection \<open>Sum of angles\<close>

context
begin

private lemma gather_squares: "a * (a * b) = a^2 * (b :: real)"
  by (simp_all add: power2_eq_square)

private lemma eval_power: "x ^ numeral n = x * x ^ pred_numeral n"
  by (subst numeral_eq_Suc, subst power_Suc) simp

text \<open>
  The proof that the sum of the angles in a triangle is $\pi$ is somewhat more
  involved. Following the HOL Light proof by John Harrison, we first prove
  that $\cos(\alpha + \beta + \gamma) = -1$ and $\alpha + \beta + \gamma \in [0;3\pi)$,
  which then implies the theorem.

  The main work is proving $\cos(\alpha + \beta + \gamma)$. This is done using the
  addition theorems for the sine and cosine, then using the Laws of Sines to eliminate
  all $\sin$ terms save $\sin(\gamma)^2$, which only appears squared in the remaining goal.
  We then use $\sin(\gamma)^2 = 1 - \cos(\gamma)^2$ to eliminate this term and apply
  the law of cosines to eliminate this term as well.

  The remaining goal is a non-linear equation containing only the length of the sides
  of the triangle. It can be shown by simple algebraic rewriting.
\<close>
lemma angle_sum_triangle:
  assumes "a \<noteq> b \<or> b \<noteq> c \<or> a \<noteq> c"
  shows   "angle c a b + angle a b c + angle b c a = pi"
proof (rule cos_minus1_imp_pi)
  show "cos (angle c a b + angle a b c + angle b c a) = - 1"
  proof (cases "a \<noteq> b")
    case True
    thus "cos (angle c a b + angle a b c + angle b c a) = -1"
      apply (simp add: cos_add sin_add cosine_law_triangle'' field_simps
                       sine_law_triangle''[of a b c] sine_law_triangle''[of b a c]
                       angle_commute dist_commute gather_squares sin_squared_eq)
      apply (simp add: eval_power algebra_simps dist_commute)
      done
  qed (insert assms, auto)

  show "angle c a b + angle a b c + angle b c a < 3 * pi"
  proof (rule ccontr)
    assume "\<not>(angle c a b + angle a b c + angle b c a < 3 * pi)"
    with angle_le_pi[of c a b] angle_le_pi[of a b c] angle_le_pi[of b c a]
      have A: "angle c a b = pi" "angle a b c = pi" by simp_all
    thus False using angle_eq_pi_imp_dist_additive[of c a b]
                     angle_eq_pi_imp_dist_additive[of a b c] by (simp add: dist_commute)
  qed
qed (auto intro!: add_nonneg_nonneg angle_nonneg)

end


subsection \<open>Congruence Theorems\<close>

text \<open>
  If two triangles agree on two angles at a non-degenerate side, the third angle
  must also be equal.
\<close>
lemma similar_triangle_aa:
  assumes "b1 \<noteq> c1" "b2 \<noteq> c2"
  assumes "angle a1 b1 c1 = angle a2 b2 c2"
  assumes "angle b1 c1 a1 = angle b2 c2 a2"
  shows   "angle b1 a1 c1 = angle b2 a2 c2"
proof -
  from assms angle_sum_triangle[of a1 b1 c1] angle_sum_triangle[of a2 b2 c2, symmetric]
    show ?thesis by (auto simp: algebra_simps angle_commute)
qed

text \<open>
  A triangle is defined by its three angles and the lengths of three sides up to congruence.
  Two triangles are congruent if they have their angles are the same and their sides have
  the same length.
\<close>

locale congruent_triangle =
  fixes a1 b1 c1 :: "'a :: real_inner" and a2 b2 c2 :: "'b :: real_inner"
  assumes sides':  "dist a1 b1 = dist a2 b2" "dist a1 c1 = dist a2 c2" "dist b1 c1 = dist b2 c2"
      and angles': "angle b1 a1 c1 = angle b2 a2 c2" "angle a1 b1 c1 = angle a2 b2 c2"
                   "angle a1 c1 b1 = angle a2 c2 b2"
begin

lemma sides:
  "dist a1 b1 = dist a2 b2" "dist a1 c1 = dist a2 c2" "dist b1 c1 = dist b2 c2"
  "dist b1 a1 = dist a2 b2" "dist c1 a1 = dist a2 c2" "dist c1 b1 = dist b2 c2"
  "dist a1 b1 = dist b2 a2" "dist a1 c1 = dist c2 a2" "dist b1 c1 = dist c2 b2"
  "dist b1 a1 = dist b2 a2" "dist c1 a1 = dist c2 a2" "dist c1 b1 = dist c2 b2"
  using sides' by (simp_all add: dist_commute)

lemma angles:
  "angle b1 a1 c1 = angle b2 a2 c2" "angle a1 b1 c1 = angle a2 b2 c2" "angle a1 c1 b1 = angle a2 c2 b2"
  "angle c1 a1 b1 = angle b2 a2 c2" "angle c1 b1 a1 = angle a2 b2 c2" "angle b1 c1 a1 = angle a2 c2 b2"
  "angle b1 a1 c1 = angle c2 a2 b2" "angle a1 b1 c1 = angle c2 b2 a2" "angle a1 c1 b1 = angle b2 c2 a2"
  "angle c1 a1 b1 = angle c2 a2 b2" "angle c1 b1 a1 = angle c2 b2 a2" "angle b1 c1 a1 = angle b2 c2 a2"
  using angles' by (simp_all add: angle_commute)

end

lemmas congruent_triangleD = congruent_triangle.sides congruent_triangle.angles



text \<open>
  Given two triangles that agree on a subset of its side lengths and angles that are
  sufficient to define a triangle uniquely up to congruence, one can conclude that they
  must also agree on all remaining quantities, i.e. that they are congruent.

  The following four congruence theorems state what constitutes such a uniquely-defining
  subset of quantities. Each theorem states in its name which quantities are required and
  in which order (clockwise or counter-clockwise): an ``s'' stands for a side,
  an ``a'' stands for an angle.

  The lemma ``congruent-triangleI-sas, for example, requires that two adjacent sides and the
  angle inbetween are the same in both triangles.
\<close>

lemma congruent_triangleI_sss:
  fixes a1 b1 c1 :: "'a :: real_inner" and a2 b2 c2 :: "'b :: real_inner"
  assumes "dist a1 b1 = dist a2 b2"
  assumes "dist b1 c1 = dist b2 c2"
  assumes "dist a1 c1 = dist a2 c2"
  shows   "congruent_triangle a1 b1 c1 a2 b2 c2"
proof -
  have A: "angle a1 b1 c1 = angle a2 b2 c2"
    if "dist a1 b1 = dist a2 b2" "dist b1 c1 = dist b2 c2" "dist a1 c1 = dist a2 c2"
    for a1 b1 c1 :: 'a and a2 b2 c2 :: 'b
  proof -
    from that cosine_law_triangle''[of a1 b1 c1] cosine_law_triangle''[of a2 b2 c2]
      show ?thesis by (intro cos_angle_eqD) (simp add: dist_commute)
  qed
  from assms show ?thesis by unfold_locales (auto intro!: A simp: dist_commute)
qed

lemmas congruent_triangle_sss = congruent_triangleD[OF congruent_triangleI_sss]

lemma congruent_triangleI_sas:
  assumes "dist a1 b1 = dist a2 b2"
  assumes "dist b1 c1 = dist b2 c2"
  assumes "angle a1 b1 c1 = angle a2 b2 c2"
  shows   "congruent_triangle a1 b1 c1 a2 b2 c2"
proof (rule congruent_triangleI_sss)
  show "dist a1 c1 = dist a2 c2"
  proof (rule power2_eq_imp_eq)
    from cosine_law_triangle[of a1 c1 b1] cosine_law_triangle[of a2 c2 b2] assms
      show "(dist a1 c1)\<^sup>2 = (dist a2 c2)\<^sup>2" by (simp add: dist_commute)
  qed simp_all
qed fact+

lemmas congruent_triangle_sas = congruent_triangleD[OF congruent_triangleI_sas]

lemma congruent_triangleI_aas:
  assumes "angle a1 b1 c1 = angle a2 b2 c2"
  assumes "angle b1 c1 a1 = angle b2 c2 a2"
  assumes "dist a1 b1 = dist a2 b2"
  assumes "\<not>collinear {a1,b1,c1}"
  shows   "congruent_triangle a1 b1 c1 a2 b2 c2"
proof (rule congruent_triangleI_sas)
  from \<open>\<not>collinear {a1,b1,c1}\<close> have neq: "a1 \<noteq> b1" by auto
  with assms(3) have neq': "a2 \<noteq> b2" by auto
  have A: "angle c1 a1 b1 = angle c2 a2 b2" using neq neq' assms
    using angle_sum_triangle[of a1 b1 c1] angle_sum_triangle[of a2 b2 c2]
    by simp
  from assms have B: "angle b1 a1 c1 \<in> {0<..<pi}"
    by (intro not_collinear_angle) (simp_all add: insert_commute)
  from sine_law_triangle[of c1 a1 b1] sine_law_triangle[of c2 a2 b2] assms A B
    show "dist b1 c1 = dist b2 c2"
    by (auto simp: angle_commute dist_commute sin_angle_zero_iff)
qed fact+

lemmas congruent_triangle_aas = congruent_triangleD[OF congruent_triangleI_aas]

lemma congruent_triangleI_asa:
  assumes "angle a1 b1 c1 = angle a2 b2 c2"
  assumes "dist a1 b1 = dist a2 b2"
  assumes "angle b1 a1 c1 = angle b2 a2 c2"
  assumes "\<not>collinear {a1, b1, c1}"
  shows   "congruent_triangle a1 b1 c1 a2 b2 c2"
proof (rule congruent_triangleI_aas)
  from assms have neq: "a1 \<noteq> b1" "a2 \<noteq> b2" by auto
  show "angle b1 c1 a1 = angle b2 c2 a2"
    by (rule similar_triangle_aa) (insert assms neq, simp_all add: angle_commute)
qed fact+

lemmas congruent_triangle_asa = congruent_triangleD[OF congruent_triangleI_asa]


subsection \<open>Isosceles Triangle Theorem\<close>

text \<open>
  We now prove the Isosceles Triangle Theorem: in a triangle where two sides have
  the same length, the two angles that are adjacent to only one of the two sides
  must be equal.
\<close>
lemma isosceles_triangle:
  assumes "dist a c = dist b c"
  shows   "angle b a c = angle a b c"
  by (rule congruent_triangle_sss) (insert assms, simp_all add: dist_commute)


text \<open>
  For the non-degenerate case (i.e. the three points are not collinear), We also
  prove the converse.
\<close>
lemma isosceles_triangle_converse:
  assumes "angle a b c = angle b a c" "\<not>collinear {a,b,c}"
  shows   "dist a c = dist b c"
  by (rule congruent_triangle_asa[OF assms(1) _ _ assms(2)])
     (simp_all add: dist_commute angle_commute assms)


subsection\<open>Contributions by Lukas Bulwahn\<close>
  
lemma Pythagoras:
  fixes A B C :: "'a :: real_inner"
  assumes "orthogonal (A - C) (B - C)"
  shows "(dist B C) ^ 2 + (dist C A) ^ 2 = (dist A B) ^ 2"
proof -
  from assms have "cos (angle A C B) = 0"
    by (metis orthogonal_iff_angle cos_pi_half)
  from this show ?thesis
    by (simp add: cosine_law_triangle[of A B C] dist_commute)
qed

lemma isosceles_triangle_orthogonal_on_midpoint:
  fixes A B C :: "'a :: euclidean_space"
  assumes "dist C A = dist C B"
  shows "orthogonal (C - midpoint A B) (A - midpoint A B)"
proof (cases "A = B")
  assume "A \<noteq> B"
  let ?M = "midpoint A B"
  from \<open>A \<noteq> B\<close> have "angle A ?M C = pi - angle B ?M C"
    by (intro angle_inverse between_midpoint)
       (auto simp: between_midpoint eq_commute[of _ "midpoint A B" for A B])
  moreover have "angle A ?M C = angle C ?M B"
  proof -
    have congruence: "congruent_triangle C A ?M C B ?M"
    proof (rule congruent_triangleI_sss)
      show "dist C A = dist C B" using assms .
      show "dist A ?M = dist B ?M" by (simp add: dist_midpoint)
      show "dist C (midpoint A B) = dist C (midpoint A B)" ..
    qed
    from this show ?thesis by (simp add: congruent_triangle.angles(6))
  qed
  ultimately have "angle A ?M C = pi / 2" by (simp add: angle_commute)
  from this show ?thesis
    by (simp add: orthogonal_iff_angle orthogonal_commute)
next
  assume "A = B"
  from this show ?thesis
    by (simp add: orthogonal_clauses(1))
qed

end
