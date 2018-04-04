(*  Title:       The hyperbolic plane and Tarski's axioms
    Author:      Tim Makarios <tjm1983 at gmail.com>, 2012
    Maintainer:  Tim Makarios <tjm1983 at gmail.com>
*)

section "The hyperbolic plane and Tarski's axioms"

theory Hyperbolic_Tarski
imports Euclid_Tarski
  Projective
  "HOL-Library.Quadratic_Discriminant"
begin

subsection {* Characterizing a specific conic in the projective plane *}

definition M :: "real^3^3" where
  "M \<equiv> vector [
  vector [1, 0, 0],
  vector [0, 1, 0],
  vector [0, 0, -1]]"

lemma M_symmatrix: "symmatrix M"
  unfolding symmatrix_def and transpose_def and M_def
  by (simp add: vec_eq_iff forall_3 vector_3)

lemma M_self_inverse: "M ** M = mat 1"
  unfolding M_def and matrix_matrix_mult_def and mat_def and vector_def
  by (simp add: sum_3 vec_eq_iff forall_3)

lemma M_invertible: "invertible M"
  unfolding invertible_def
  using M_self_inverse
  by auto

definition polar :: "proj2 \<Rightarrow> proj2_line" where
  "polar p \<equiv> proj2_line_abs (M *v proj2_rep p)"

definition pole :: "proj2_line \<Rightarrow> proj2" where
  "pole l \<equiv> proj2_abs (M *v proj2_line_rep l)"

lemma polar_abs:
  assumes "v \<noteq> 0"
  shows "polar (proj2_abs v) = proj2_line_abs (M *v v)"
proof -
  from `v \<noteq> 0` and proj2_rep_abs2
  obtain k where "k \<noteq> 0" and "proj2_rep (proj2_abs v) = k *\<^sub>R v" by auto
  from `proj2_rep (proj2_abs v) = k *\<^sub>R v`
  have "polar (proj2_abs v) = proj2_line_abs (k *\<^sub>R (M *v v))"
    unfolding polar_def
    by (simp add: matrix_scalar_vector_ac scalar_matrix_vector_assoc)
  with `k \<noteq> 0` and proj2_line_abs_mult
  show "polar (proj2_abs v) = proj2_line_abs (M *v v)" by simp
qed

lemma pole_abs:
  assumes "v \<noteq> 0"
  shows "pole (proj2_line_abs v) = proj2_abs (M *v v)"
proof -
  from `v \<noteq> 0` and proj2_line_rep_abs
  obtain k where "k \<noteq> 0" and "proj2_line_rep (proj2_line_abs v) = k *\<^sub>R v"
    by auto
  from `proj2_line_rep (proj2_line_abs v) = k *\<^sub>R v`
  have "pole (proj2_line_abs v) = proj2_abs (k *\<^sub>R (M *v v))"
    unfolding pole_def
    by (simp add: matrix_scalar_vector_ac scalar_matrix_vector_assoc)
  with `k \<noteq> 0` and proj2_abs_mult
  show "pole (proj2_line_abs v) = proj2_abs (M *v v)" by simp
qed

lemma polar_rep_non_zero: "M *v proj2_rep p \<noteq> 0"
proof -
  have "proj2_rep p \<noteq> 0" by (rule proj2_rep_non_zero)
  with M_invertible
  show "M *v proj2_rep p \<noteq> 0" by (rule invertible_times_non_zero)
qed

lemma pole_polar: "pole (polar p) = p"
proof -
  from polar_rep_non_zero
  have "pole (polar p) = proj2_abs (M *v (M *v proj2_rep p))"
    unfolding polar_def
    by (rule pole_abs)
  with M_self_inverse
  show "pole (polar p) = p"
    by (simp add: matrix_vector_mul_assoc proj2_abs_rep matrix_vector_mul_lid)
qed

lemma pole_rep_non_zero: "M *v proj2_line_rep l \<noteq> 0"
proof -
  have "proj2_line_rep l \<noteq> 0" by (rule proj2_line_rep_non_zero)
  with M_invertible
  show "M *v proj2_line_rep l \<noteq> 0" by (rule invertible_times_non_zero)
qed

lemma polar_pole: "polar (pole l) = l"
proof -
  from pole_rep_non_zero
  have "polar (pole l) = proj2_line_abs (M *v (M *v proj2_line_rep l))"
    unfolding pole_def
    by (rule polar_abs)
  with M_self_inverse
  show "polar (pole l) = l"
    by (simp add: matrix_vector_mul_assoc proj2_line_abs_rep
      matrix_vector_mul_lid)
qed

lemma polar_inj:
  assumes "polar p = polar q"
  shows "p = q"
proof -
  from `polar p = polar q` have "pole (polar p) = pole (polar q)" by simp
  thus "p = q" by (simp add: pole_polar)
qed

definition conic_sgn :: "proj2 \<Rightarrow> real" where
  "conic_sgn p \<equiv> sgn (proj2_rep p \<bullet> (M *v proj2_rep p))"

lemma conic_sgn_abs:
  assumes "v \<noteq> 0"
  shows "conic_sgn (proj2_abs v) = sgn (v \<bullet> (M *v v))"
proof -
  from `v \<noteq> 0` and proj2_rep_abs2
  obtain j where "j \<noteq> 0" and "proj2_rep (proj2_abs v) = j *\<^sub>R v" by auto

  from `proj2_rep (proj2_abs v) = j *\<^sub>R v`
  have "conic_sgn (proj2_abs v) = sgn (j\<^sup>2 * (v \<bullet> (M *v v)))"
    unfolding conic_sgn_def
    by (simp add:
      matrix_scalar_vector_ac
      scalar_matrix_vector_assoc [symmetric]
      dot_scaleR_mult
      power2_eq_square
      algebra_simps)
  also have "\<dots> = sgn (j\<^sup>2) * sgn (v \<bullet> (M *v v))" by (rule sgn_mult)
  also from `j \<noteq> 0` have "\<dots> = sgn (v \<bullet> (M *v v))"
    by (simp add: power2_eq_square sgn_mult)
  finally show "conic_sgn (proj2_abs v) = sgn (v \<bullet> (M *v v))" .
qed

lemma sgn_conic_sgn: "sgn (conic_sgn p) = conic_sgn p"
  by (unfold conic_sgn_def) simp

definition S :: "proj2 set" where
  "S \<equiv> {p. conic_sgn p = 0}"

definition K2 :: "proj2 set" where
  "K2 \<equiv> {p. conic_sgn p < 0}"

lemma S_K2_empty: "S \<inter> K2 = {}"
  unfolding S_def and K2_def
  by auto

lemma K2_abs:
  assumes "v \<noteq> 0"
  shows "proj2_abs v \<in> K2 \<longleftrightarrow> v \<bullet> (M *v v) < 0"
proof -
  have "proj2_abs v \<in> K2 \<longleftrightarrow> conic_sgn (proj2_abs v) < 0"
    by (simp add: K2_def)
  with `v \<noteq> 0` and conic_sgn_abs
  show "proj2_abs v \<in> K2 \<longleftrightarrow> v \<bullet> (M *v v) < 0" by simp
qed

definition "K2_centre = proj2_abs (vector [0,0,1])"

lemma K2_centre_non_zero: "vector [0,0,1] \<noteq> (0 :: real^3)"
  by (unfold vector_def) (simp add: vec_eq_iff forall_3)

lemma K2_centre_in_K2: "K2_centre \<in> K2"
proof -
  from K2_centre_non_zero and proj2_rep_abs2
  obtain k where "k \<noteq> 0" and "proj2_rep K2_centre = k *\<^sub>R vector [0,0,1]"
    by (unfold K2_centre_def) auto
  from `k \<noteq> 0` have "0 < k\<^sup>2" by simp
  with `proj2_rep K2_centre = k *\<^sub>R vector [0,0,1]`
  show "K2_centre \<in> K2"
    unfolding K2_def
      and conic_sgn_def
      and M_def
      and matrix_vector_mult_def
      and inner_vec_def
      and vector_def
    by (simp add: vec_eq_iff sum_3 power2_eq_square)
qed

lemma K2_imp_M_neg:
  assumes "v \<noteq> 0" and "proj2_abs v \<in> K2"
  shows "v \<bullet> (M *v v) < 0"
  using assms
  by (simp add: K2_abs)

lemma M_neg_imp_z_squared_big:
  assumes "v \<bullet> (M *v v) < 0"
  shows "(v$3)\<^sup>2 > (v$1)\<^sup>2 + (v$2)\<^sup>2"
  using `v \<bullet> (M *v v) < 0`
  unfolding matrix_vector_mult_def and M_def and vector_def
  by (simp add: inner_vec_def sum_3 power2_eq_square)

lemma M_neg_imp_z_non_zero:
  assumes "v \<bullet> (M *v v) < 0"
  shows "v$3 \<noteq> 0"
proof -
  have "(v$1)\<^sup>2 + (v$2)\<^sup>2 \<ge> 0" by simp
  with M_neg_imp_z_squared_big [of v] and `v \<bullet> (M *v v) < 0`
  have "(v$3)\<^sup>2 > 0" by arith
  thus "v$3 \<noteq> 0" by simp
qed

lemma M_neg_imp_K2:
  assumes "v \<bullet> (M *v v) < 0"
  shows "proj2_abs v \<in> K2"
proof -
  from `v \<bullet> (M *v v) < 0` have "v$3 \<noteq> 0" by (rule M_neg_imp_z_non_zero)
  hence "v \<noteq> 0" by auto
  with `v \<bullet> (M *v v) < 0` and K2_abs show "proj2_abs v \<in> K2" by simp
qed

lemma M_reverse: "a \<bullet> (M *v b) = b \<bullet> (M *v a)"
  unfolding matrix_vector_mult_def and M_def and vector_def
  by (simp add: inner_vec_def sum_3)

lemma S_abs:
  assumes "v \<noteq> 0"
  shows "proj2_abs v \<in> S \<longleftrightarrow> v \<bullet> (M *v v) = 0"
proof -
  have "proj2_abs v \<in> S \<longleftrightarrow> conic_sgn (proj2_abs v) = 0"
    unfolding S_def
    by simp
  also from `v \<noteq> 0` and conic_sgn_abs
  have "\<dots> \<longleftrightarrow> sgn (v \<bullet> (M *v v)) = 0" by simp
  finally show "proj2_abs v \<in> S \<longleftrightarrow> v \<bullet> (M *v v) = 0" by (simp add: sgn_0_0)
qed

lemma S_alt_def: "p \<in> S \<longleftrightarrow> proj2_rep p \<bullet> (M *v proj2_rep p) = 0"
proof -
  have "proj2_rep p \<noteq> 0" by (rule proj2_rep_non_zero)
  hence "proj2_abs (proj2_rep p) \<in> S \<longleftrightarrow> proj2_rep p \<bullet> (M *v proj2_rep p) = 0"
    by (rule S_abs)
  thus "p \<in> S \<longleftrightarrow> proj2_rep p \<bullet> (M *v proj2_rep p) = 0"
    by (simp add: proj2_abs_rep)
qed

lemma incident_polar:
  "proj2_incident p (polar q) \<longleftrightarrow> proj2_rep p \<bullet> (M *v proj2_rep q) = 0"
  using polar_rep_non_zero
  unfolding polar_def
  by (rule proj2_incident_right_abs)

lemma incident_own_polar_in_S: "proj2_incident p (polar p) \<longleftrightarrow> p \<in> S"
  using incident_polar and S_alt_def
  by simp

lemma incident_polar_swap:
  assumes "proj2_incident p (polar q)"
  shows "proj2_incident q (polar p)"
proof -
  from `proj2_incident p (polar q)`
  have "proj2_rep p \<bullet> (M *v proj2_rep q) = 0" by (unfold incident_polar)
  hence "proj2_rep q \<bullet> (M *v proj2_rep p) = 0" by (simp add: M_reverse)
  thus "proj2_incident q (polar p)" by (unfold incident_polar)
qed

lemma incident_pole_polar:
  assumes "proj2_incident p l"
  shows "proj2_incident (pole l) (polar p)"
proof -
  from `proj2_incident p l`
  have "proj2_incident p (polar (pole l))" by (subst polar_pole)
  thus "proj2_incident (pole l) (polar p)" by (rule incident_polar_swap)
qed

definition z_zero :: "proj2_line" where
  "z_zero \<equiv> proj2_line_abs (vector [0,0,1])"

lemma z_zero:
  assumes "(proj2_rep p)$3 = 0"
  shows "proj2_incident p z_zero"
proof -
  from K2_centre_non_zero and proj2_line_rep_abs
  obtain k where "proj2_line_rep z_zero = k *\<^sub>R vector [0,0,1]"
    by (unfold z_zero_def) auto
  with `(proj2_rep p)$3 = 0`
  show "proj2_incident p z_zero"
    unfolding proj2_incident_def and inner_vec_def and vector_def
    by (simp add: sum_3)
qed

lemma z_zero_conic_sgn_1:
  assumes "proj2_incident p z_zero"
  shows "conic_sgn p = 1"
proof -
  let ?v = "proj2_rep p"
  have "(vector [0,0,1] :: real^3) \<noteq> 0"
    unfolding vector_def
    by (simp add: vec_eq_iff)
  with `proj2_incident p z_zero`
  have "?v \<bullet> vector [0,0,1] = 0"
    unfolding z_zero_def
    by (simp add: proj2_incident_right_abs)
  hence "?v$3 = 0"
    unfolding inner_vec_def and vector_def
    by (simp add: sum_3)
  hence "?v \<bullet> (M *v ?v) = (?v$1)\<^sup>2 + (?v$2)\<^sup>2"
    unfolding inner_vec_def
      and power2_eq_square
      and matrix_vector_mult_def
      and M_def
      and vector_def
      and sum_3
    by simp

  have "?v \<noteq> 0" by (rule proj2_rep_non_zero)
  with `?v$3 = 0` have "?v$1 \<noteq> 0 \<or> ?v$2 \<noteq> 0" by (simp add: vec_eq_iff forall_3)
  hence "(?v$1)\<^sup>2 > 0 \<or> (?v$2)\<^sup>2 > 0" by simp
  with add_sign_intros [of "(?v$1)\<^sup>2" "(?v$2)\<^sup>2"]
  have "(?v$1)\<^sup>2 + (?v$2)\<^sup>2 > 0" by auto
  with `?v \<bullet> (M *v ?v) = (?v$1)\<^sup>2 + (?v$2)\<^sup>2`
  have "?v \<bullet> (M *v ?v) > 0" by simp
  thus "conic_sgn p = 1"
    unfolding conic_sgn_def
    by simp
qed

lemma conic_sgn_not_1_z_non_zero:
  assumes "conic_sgn p \<noteq> 1"
  shows "z_non_zero p"
proof -
  from `conic_sgn p \<noteq> 1`
  have "\<not> proj2_incident p z_zero" by (auto simp add: z_zero_conic_sgn_1)
  thus "z_non_zero p" by (auto simp add: z_zero)
qed

lemma z_zero_not_in_S:
  assumes "proj2_incident p z_zero"
  shows "p \<notin> S"
proof -
  from `proj2_incident p z_zero` have "conic_sgn p = 1"
    by (rule z_zero_conic_sgn_1)
  thus "p \<notin> S"
    unfolding S_def
    by simp
qed

lemma line_incident_point_not_in_S: "\<exists> p. p \<notin> S \<and> proj2_incident p l"
proof -
  let ?p = "proj2_intersection l z_zero"
  have "proj2_incident ?p l" and "proj2_incident ?p z_zero"
    by (rule proj2_intersection_incident)+
  from `proj2_incident ?p z_zero` have "?p \<notin> S" by (rule z_zero_not_in_S)
  with `proj2_incident ?p l`
  show "\<exists> p. p \<notin> S \<and> proj2_incident p l" by auto
qed

lemma apply_cltn2_abs_abs_in_S:
  assumes "v \<noteq> 0" and "invertible J"
  shows "apply_cltn2 (proj2_abs v) (cltn2_abs J) \<in> S
  \<longleftrightarrow> v \<bullet> (J ** M ** transpose J *v v) = 0"
proof -
  from `v \<noteq> 0` and `invertible J`
  have "v v* J \<noteq> 0" by (rule non_zero_mult_invertible_non_zero)

  from `v \<noteq> 0` and `invertible J`
  have "apply_cltn2 (proj2_abs v) (cltn2_abs J) = proj2_abs (v v* J)"
    by (rule apply_cltn2_abs)
  also from `v v* J \<noteq> 0`
  have "\<dots> \<in> S \<longleftrightarrow> (v v* J) \<bullet> (M *v (v v* J)) = 0" by (rule S_abs)
  finally show "apply_cltn2 (proj2_abs v) (cltn2_abs J) \<in> S
    \<longleftrightarrow> v \<bullet> (J ** M ** transpose J *v v) = 0"
    by (simp add: dot_lmul_matrix matrix_vector_mul_assoc [symmetric])
qed

lemma apply_cltn2_right_abs_in_S:
  assumes "invertible J"
  shows "apply_cltn2 p (cltn2_abs J) \<in> S
  \<longleftrightarrow> (proj2_rep p) \<bullet> (J ** M ** transpose J *v (proj2_rep p)) = 0"
proof -
  have "proj2_rep p \<noteq> 0" by (rule proj2_rep_non_zero)
  with `invertible J`
  have "apply_cltn2 (proj2_abs (proj2_rep p)) (cltn2_abs J) \<in> S
    \<longleftrightarrow> proj2_rep p \<bullet> (J ** M ** transpose J *v proj2_rep p) = 0"
    by (simp add: apply_cltn2_abs_abs_in_S)
  thus "apply_cltn2 p (cltn2_abs J) \<in> S
    \<longleftrightarrow> proj2_rep p \<bullet> (J ** M ** transpose J *v proj2_rep p) = 0"
    by (simp add: proj2_abs_rep)
qed

lemma apply_cltn2_abs_in_S:
  assumes "v \<noteq> 0"
  shows "apply_cltn2 (proj2_abs v) C \<in> S
  \<longleftrightarrow> v \<bullet> (cltn2_rep C ** M ** transpose (cltn2_rep C) *v v) = 0"
proof -
  have "invertible (cltn2_rep C)" by (rule cltn2_rep_invertible)
  with `v \<noteq> 0`
  have "apply_cltn2 (proj2_abs v) (cltn2_abs (cltn2_rep C)) \<in> S
    \<longleftrightarrow> v \<bullet> (cltn2_rep C ** M ** transpose (cltn2_rep C) *v v) = 0"
    by (rule apply_cltn2_abs_abs_in_S)
  thus "apply_cltn2 (proj2_abs v) C \<in> S
    \<longleftrightarrow> v \<bullet> (cltn2_rep C ** M ** transpose (cltn2_rep C) *v v) = 0"
    by (simp add: cltn2_abs_rep)
qed

lemma apply_cltn2_in_S:
  "apply_cltn2 p C \<in> S
  \<longleftrightarrow> proj2_rep p \<bullet> (cltn2_rep C ** M ** transpose (cltn2_rep C) *v proj2_rep p)
  = 0"
proof -
  have "proj2_rep p \<noteq> 0" by (rule proj2_rep_non_zero)
  hence "apply_cltn2 (proj2_abs (proj2_rep p)) C \<in> S
    \<longleftrightarrow> proj2_rep p \<bullet> (cltn2_rep C ** M ** transpose (cltn2_rep C) *v proj2_rep p)
    = 0"
    by (rule apply_cltn2_abs_in_S)
  thus "apply_cltn2 p C \<in> S
    \<longleftrightarrow> proj2_rep p \<bullet> (cltn2_rep C ** M ** transpose (cltn2_rep C) *v proj2_rep p)
    = 0"
    by (simp add: proj2_abs_rep)
qed

lemma norm_M: "(vector2_append1 v) \<bullet> (M *v vector2_append1 v) = (norm v)\<^sup>2 - 1"
proof -
  have "(norm v)\<^sup>2 = (v$1)\<^sup>2 + (v$2)\<^sup>2"
    unfolding norm_vec_def
      and setL2_def
    by (simp add: sum_2)
  thus "(vector2_append1 v) \<bullet> (M *v vector2_append1 v) = (norm v)\<^sup>2 - 1"
    unfolding vector2_append1_def
      and inner_vec_def
      and matrix_vector_mult_def
      and vector_def
      and M_def
      and power2_norm_eq_inner
    by (simp add: sum_3 power2_eq_square)
qed

subsection {* Some specific points and lines of the projective plane *}

definition "east = proj2_abs (vector [1,0,1])"
definition "west = proj2_abs (vector [-1,0,1])"
definition "north = proj2_abs (vector [0,1,1])"
definition "south = proj2_abs (vector [0,-1,1])"
definition "far_north = proj2_abs (vector [0,1,0])"

lemmas compass_defs = east_def west_def north_def south_def

lemma compass_non_zero:
  shows "vector [1,0,1] \<noteq> (0 :: real^3)"
  and "vector [-1,0,1] \<noteq> (0 :: real^3)"
  and "vector [0,1,1] \<noteq> (0 :: real^3)"
  and "vector [0,-1,1] \<noteq> (0 :: real^3)"
  and "vector [0,1,0] \<noteq> (0 :: real^3)"
  and "vector [1,0,0] \<noteq> (0 :: real^3)"
  unfolding vector_def
  by (simp_all add: vec_eq_iff forall_3)

lemma east_west_distinct: "east \<noteq> west"
proof
  assume "east = west"
  with compass_non_zero
    and proj2_abs_abs_mult [of "vector [1,0,1]" "vector [-1,0,1]"]
  obtain k where "(vector [1,0,1] :: real^3) = k *\<^sub>R vector [-1,0,1]"
    unfolding compass_defs
    by auto
  thus False
    unfolding vector_def
    by (auto simp add: vec_eq_iff forall_3)
qed

lemma north_south_distinct: "north \<noteq> south"
proof
  assume "north = south"
  with compass_non_zero
    and proj2_abs_abs_mult [of "vector [0,1,1]" "vector [0,-1,1]"]
  obtain k where "(vector [0,1,1] :: real^3) = k *\<^sub>R vector [0,-1,1]"
    unfolding compass_defs
    by auto
  thus False
    unfolding vector_def
    by (auto simp add: vec_eq_iff forall_3)
qed

lemma north_not_east_or_west: "north \<notin> {east, west}"
proof
  assume "north \<in> {east, west}"
  hence "east = north \<or> west = north" by auto
  with compass_non_zero
    and proj2_abs_abs_mult [of _ "vector [0,1,1]"]
  obtain k where "(vector [1,0,1] :: real^3) = k *\<^sub>R vector [0,1,1]
    \<or> (vector [-1,0,1] :: real^3) = k *\<^sub>R vector [0,1,1]"
    unfolding compass_defs
    by auto
  thus False
    unfolding vector_def
    by (simp add: vec_eq_iff forall_3)
qed

lemma compass_in_S:
  shows "east \<in> S" and "west \<in> S" and "north \<in> S" and "south \<in> S"
  using compass_non_zero and S_abs
  unfolding compass_defs
    and M_def
    and inner_vec_def
    and matrix_vector_mult_def
    and vector_def
  by (simp_all add: sum_3)

lemma east_west_tangents:
  shows "polar east = proj2_line_abs (vector [-1,0,1])"
  and "polar west = proj2_line_abs (vector [1,0,1])"
proof -
  have "M *v vector [1,0,1] = (-1) *\<^sub>R vector [-1,0,1]"
    and "M *v vector [-1,0,1] = (-1) *\<^sub>R vector [1,0,1]"
    unfolding M_def and matrix_vector_mult_def and vector_def
    by (simp_all add: vec_eq_iff sum_3)
  with compass_non_zero and polar_abs
  have "polar east = proj2_line_abs ((-1) *\<^sub>R vector [-1,0,1])"
    and "polar west = proj2_line_abs ((-1) *\<^sub>R vector [1,0,1])"
    unfolding compass_defs
    by simp_all
  with proj2_line_abs_mult [of "-1"]
  show "polar east = proj2_line_abs (vector [-1,0,1])"
    and "polar west = proj2_line_abs (vector [1,0,1])"
    by simp_all
qed

lemma east_west_tangents_distinct: "polar east \<noteq> polar west"
proof
  assume "polar east = polar west"
  hence "east = west" by (rule polar_inj)
  with east_west_distinct show False ..
qed

lemma east_west_tangents_incident_far_north:
  shows "proj2_incident far_north (polar east)"
  and "proj2_incident far_north (polar west)"
  using compass_non_zero and proj2_incident_abs
  unfolding far_north_def and east_west_tangents and inner_vec_def
  by (simp_all add: sum_3 vector_3)

lemma east_west_tangents_far_north:
  "proj2_intersection (polar east) (polar west) = far_north"
  using east_west_tangents_distinct and east_west_tangents_incident_far_north
  by (rule proj2_intersection_unique [symmetric])

instantiation proj2 :: zero
begin
definition proj2_zero_def: "0 = proj2_pt 0"
instance ..
end

definition "equator \<equiv> proj2_line_abs (vector [0,1,0])"
definition "meridian \<equiv> proj2_line_abs (vector [1,0,0])"

lemma equator_meridian_distinct: "equator \<noteq> meridian"
proof
  assume "equator = meridian"
  with compass_non_zero
    and proj2_line_abs_abs_mult [of "vector [0,1,0]" "vector [1,0,0]"]
  obtain k where "(vector [0,1,0] :: real^3) = k *\<^sub>R vector [1,0,0]"
    by (unfold equator_def meridian_def) auto
  thus False by (unfold vector_def) (auto simp add: vec_eq_iff forall_3)
qed

lemma east_west_on_equator:
  shows "proj2_incident east equator" and "proj2_incident west equator"
  unfolding east_def and west_def and equator_def
  using compass_non_zero
  by (simp_all add: proj2_incident_abs inner_vec_def vector_def sum_3)

lemma north_far_north_distinct: "north \<noteq> far_north"
proof
  assume "north = far_north"
  with compass_non_zero
    and proj2_abs_abs_mult [of "vector [0,1,1]" "vector [0,1,0]"]
  obtain k where "(vector [0,1,1] :: real^3) = k *\<^sub>R vector [0,1,0]"
    by (unfold north_def far_north_def) auto
  thus False
    unfolding vector_def
    by (auto simp add: vec_eq_iff forall_3)
qed

lemma north_south_far_north_on_meridian:
  shows "proj2_incident north meridian" and "proj2_incident south meridian"
  and "proj2_incident far_north meridian"
  unfolding compass_defs and far_north_def and meridian_def
  using compass_non_zero
  by (simp_all add: proj2_incident_abs inner_vec_def vector_def sum_3)

lemma K2_centre_on_equator_meridian:
  shows "proj2_incident K2_centre equator"
  and "proj2_incident K2_centre meridian"
  unfolding K2_centre_def and equator_def and meridian_def
  using K2_centre_non_zero and compass_non_zero
  by (simp_all add: proj2_incident_abs inner_vec_def vector_def sum_3)

lemma on_equator_meridian_is_K2_centre:
  assumes "proj2_incident a equator" and "proj2_incident a meridian"
  shows "a = K2_centre"
  using assms and K2_centre_on_equator_meridian and equator_meridian_distinct
    and proj2_incident_unique
  by auto

definition "rep_equator_reflect \<equiv> vector [
  vector [1, 0,0],
  vector [0,-1,0],
  vector [0, 0,1]] :: real^3^3"
definition "rep_meridian_reflect \<equiv> vector [
  vector [-1,0,0],
  vector [ 0,1,0],
  vector [ 0,0,1]] :: real^3^3"
definition "equator_reflect \<equiv> cltn2_abs rep_equator_reflect"
definition "meridian_reflect \<equiv> cltn2_abs rep_meridian_reflect"

lemmas compass_reflect_defs = equator_reflect_def meridian_reflect_def
  rep_equator_reflect_def rep_meridian_reflect_def

lemma compass_reflect_self_inverse:
  shows "rep_equator_reflect ** rep_equator_reflect = mat 1"
  and "rep_meridian_reflect ** rep_meridian_reflect = mat 1"
  unfolding compass_reflect_defs matrix_matrix_mult_def mat_def
  by (simp_all add: vec_eq_iff forall_3 sum_3 vector_3)

lemma compass_reflect_invertible:
  shows "invertible rep_equator_reflect" and "invertible rep_meridian_reflect"
  unfolding invertible_def
  using compass_reflect_self_inverse
  by auto

lemma compass_reflect_compass:
  shows "apply_cltn2 east meridian_reflect = west"
  and "apply_cltn2 west meridian_reflect = east"
  and "apply_cltn2 north meridian_reflect = north"
  and "apply_cltn2 south meridian_reflect = south"
  and "apply_cltn2 K2_centre meridian_reflect = K2_centre"
  and "apply_cltn2 east equator_reflect = east"
  and "apply_cltn2 west equator_reflect = west"
  and "apply_cltn2 north equator_reflect = south"
  and "apply_cltn2 south equator_reflect = north"
  and "apply_cltn2 K2_centre equator_reflect = K2_centre"
proof -
  have "(vector [1,0,1] :: real^3) v* rep_meridian_reflect = vector [-1,0,1]"
    and "(vector [-1,0,1] :: real^3) v* rep_meridian_reflect = vector [1,0,1]"
    and "(vector [0,1,1] :: real^3) v* rep_meridian_reflect = vector [0,1,1]"
    and "(vector [0,-1,1] :: real^3) v* rep_meridian_reflect = vector [0,-1,1]"
    and "(vector [0,0,1] :: real^3) v* rep_meridian_reflect = vector [0,0,1]"
    and "(vector [1,0,1] :: real^3) v* rep_equator_reflect = vector [1,0,1]"
    and "(vector [-1,0,1] :: real^3) v* rep_equator_reflect = vector [-1,0,1]"
    and "(vector [0,1,1] :: real^3) v* rep_equator_reflect = vector [0,-1,1]"
    and "(vector [0,-1,1] :: real^3) v* rep_equator_reflect = vector [0,1,1]"
    and "(vector [0,0,1] :: real^3) v* rep_equator_reflect = vector [0,0,1]"
    unfolding rep_meridian_reflect_def and rep_equator_reflect_def
      and vector_matrix_mult_def
    by (simp_all add: vec_eq_iff forall_3 vector_3 sum_3)
  with compass_reflect_invertible and compass_non_zero and K2_centre_non_zero
  show "apply_cltn2 east meridian_reflect = west"
    and "apply_cltn2 west meridian_reflect = east"
    and "apply_cltn2 north meridian_reflect = north"
    and "apply_cltn2 south meridian_reflect = south"
    and "apply_cltn2 K2_centre meridian_reflect = K2_centre"
    and "apply_cltn2 east equator_reflect = east"
    and "apply_cltn2 west equator_reflect = west"
    and "apply_cltn2 north equator_reflect = south"
    and "apply_cltn2 south equator_reflect = north"
    and "apply_cltn2 K2_centre equator_reflect = K2_centre"
    unfolding compass_defs and K2_centre_def
      and meridian_reflect_def and equator_reflect_def
    by (simp_all add: apply_cltn2_abs)
qed

lemma on_equator_rep:
  assumes "z_non_zero a" and "proj2_incident a equator"
  shows "\<exists> x. a = proj2_abs (vector [x,0,1])"
proof -
  let ?ra = "proj2_rep a"
  let ?ca1 = "cart2_append1 a"
  let ?x = "?ca1$1"
  from compass_non_zero and `proj2_incident a equator`
  have "?ra \<bullet> vector [0,1,0] = 0"
    by (unfold equator_def) (simp add: proj2_incident_right_abs)
  hence "?ra$2 = 0" by (unfold inner_vec_def vector_def) (simp add: sum_3)
  hence "?ca1$2 = 0" by (unfold cart2_append1_def) simp
  moreover
  from `z_non_zero a` have "?ca1$3 = 1" by (rule cart2_append1_z)
  ultimately
  have "?ca1 = vector [?x,0,1]"
    by (unfold vector_def) (simp add: vec_eq_iff forall_3)
  with `z_non_zero a`
  have "proj2_abs (vector [?x,0,1]) = a" by (simp add: proj2_abs_cart2_append1)
  thus "\<exists> x. a = proj2_abs (vector [x,0,1])" by (simp add: exI [of _ ?x])
qed

lemma on_meridian_rep:
  assumes "z_non_zero a" and "proj2_incident a meridian"
  shows "\<exists> y. a = proj2_abs (vector [0,y,1])"
proof -
  let ?ra = "proj2_rep a"
  let ?ca1 = "cart2_append1 a"
  let ?y = "?ca1$2"
  from compass_non_zero and `proj2_incident a meridian`
  have "?ra \<bullet> vector [1,0,0] = 0"
    by (unfold meridian_def) (simp add: proj2_incident_right_abs)
  hence "?ra$1 = 0" by (unfold inner_vec_def vector_def) (simp add: sum_3)
  hence "?ca1$1 = 0" by (unfold cart2_append1_def) simp
  moreover
  from `z_non_zero a` have "?ca1$3 = 1" by (rule cart2_append1_z)
  ultimately
  have "?ca1 = vector [0,?y,1]"
    by (unfold vector_def) (simp add: vec_eq_iff forall_3)
  with `z_non_zero a`
  have "proj2_abs (vector [0,?y,1]) = a" by (simp add: proj2_abs_cart2_append1)
  thus "\<exists> y. a = proj2_abs (vector [0,y,1])" by (simp add: exI [of _ ?y])
qed

subsection {* Definition of the Klein--Beltrami model of the hyperbolic plane *}
abbreviation "hyp2 == K2"

typedef hyp2 = K2
  using K2_centre_in_K2
  by auto

definition hyp2_rep :: "hyp2 \<Rightarrow> real^2" where
  "hyp2_rep p \<equiv> cart2_pt (Rep_hyp2 p)"

definition hyp2_abs :: "real^2 \<Rightarrow> hyp2" where
  "hyp2_abs v = Abs_hyp2 (proj2_pt v)"

lemma norm_lt_1_iff_in_hyp2:
  shows "norm v < 1 \<longleftrightarrow> proj2_pt v \<in> hyp2"
proof -
  let ?v' = "vector2_append1 v"
  have "?v' \<noteq> 0" by (rule vector2_append1_non_zero)

  from real_less_rsqrt [of "norm v" 1]
    and abs_square_less_1 [of "norm v"]
  have "norm v < 1 \<longleftrightarrow> (norm v)\<^sup>2 < 1" by auto
  hence "norm v < 1 \<longleftrightarrow> ?v' \<bullet> (M *v ?v') < 0" by (simp add: norm_M)
  with `?v' \<noteq> 0` have "norm v < 1 \<longleftrightarrow> proj2_abs ?v' \<in> K2" by (subst K2_abs)
  thus "norm v < 1 \<longleftrightarrow> proj2_pt v \<in> hyp2" by (unfold proj2_pt_def)
qed

lemma norm_eq_1_iff_in_S:
  shows "norm v = 1 \<longleftrightarrow> proj2_pt v \<in> S"
proof -
  let ?v' = "vector2_append1 v"
  have "?v' \<noteq> 0" by (rule vector2_append1_non_zero)

  from real_sqrt_unique [of "norm v" 1]
  have "norm v = 1 \<longleftrightarrow> (norm v)\<^sup>2 = 1" by auto
  hence "norm v = 1 \<longleftrightarrow> ?v' \<bullet> (M *v ?v') = 0" by (simp add: norm_M)
  with `?v' \<noteq> 0` have "norm v = 1 \<longleftrightarrow> proj2_abs ?v' \<in> S" by (subst S_abs)
  thus "norm v = 1 \<longleftrightarrow> proj2_pt v \<in> S" by (unfold proj2_pt_def)
qed

lemma norm_le_1_iff_in_hyp2_S:
  "norm v \<le> 1 \<longleftrightarrow> proj2_pt v \<in> hyp2 \<union> S"
  using norm_lt_1_iff_in_hyp2 [of v] and norm_eq_1_iff_in_S [of v]
  by auto

lemma proj2_pt_hyp2_rep: "proj2_pt (hyp2_rep p) = Rep_hyp2 p"
proof -
  let ?p' = "Rep_hyp2 p"
  let ?v = "proj2_rep ?p'"
  have "?v \<noteq> 0" by (rule proj2_rep_non_zero)

  have "proj2_abs ?v = ?p'" by (rule proj2_abs_rep)

  have "?p' \<in> hyp2" by (rule Rep_hyp2)
  with `?v \<noteq> 0` and `proj2_abs ?v = ?p'`
  have "?v \<bullet> (M *v ?v) < 0" by (simp add: K2_imp_M_neg)
  hence "?v$3 \<noteq> 0" by (rule M_neg_imp_z_non_zero)
  hence "proj2_pt (cart2_pt ?p') = ?p'" by (rule proj2_cart2)
  thus "proj2_pt (hyp2_rep p) = ?p'" by (unfold hyp2_rep_def)
qed

lemma hyp2_rep_abs:
  assumes "norm v < 1"
  shows "hyp2_rep (hyp2_abs v) = v"
proof -
  from `norm v < 1`
  have "proj2_pt v \<in> hyp2" by (simp add: norm_lt_1_iff_in_hyp2)
  hence "Rep_hyp2 (Abs_hyp2 (proj2_pt v)) = proj2_pt v"
    by (simp add: Abs_hyp2_inverse)
  hence "hyp2_rep (hyp2_abs v) = cart2_pt (proj2_pt v)"
    by (unfold hyp2_rep_def hyp2_abs_def) simp
  thus "hyp2_rep (hyp2_abs v) = v" by (simp add: cart2_proj2)
qed

lemma hyp2_abs_rep: "hyp2_abs (hyp2_rep p) = p"
  by (unfold hyp2_abs_def) (simp add: proj2_pt_hyp2_rep Rep_hyp2_inverse)

lemma norm_hyp2_rep_lt_1: "norm (hyp2_rep p) < 1"
proof -
  have "proj2_pt (hyp2_rep p) = Rep_hyp2 p" by (rule proj2_pt_hyp2_rep)
  hence "proj2_pt (hyp2_rep p) \<in> hyp2" by (simp add: Rep_hyp2)
  thus "norm (hyp2_rep p) < 1" by (simp add: norm_lt_1_iff_in_hyp2)
qed

lemma hyp2_S_z_non_zero:
  assumes "p \<in> hyp2 \<union> S"
  shows "z_non_zero p"
proof -
  from `p \<in> hyp2 \<union> S`
  have "conic_sgn p \<le> 0" by (unfold K2_def S_def) auto
  hence "conic_sgn p \<noteq> 1" by simp
  thus "z_non_zero p" by (rule conic_sgn_not_1_z_non_zero)
qed

lemma hyp2_S_not_equal:
  assumes "a \<in> hyp2" and "p \<in> S"
  shows "a \<noteq> p"
  using assms and S_K2_empty
  by auto

lemma hyp2_S_cart2_inj:
  assumes "p \<in> hyp2 \<union> S" and "q \<in> hyp2 \<union> S" and "cart2_pt p = cart2_pt q"
  shows "p = q"
proof -
  from `p \<in> hyp2 \<union> S` and `q \<in> hyp2 \<union> S`
  have "z_non_zero p" and "z_non_zero q" by (simp_all add: hyp2_S_z_non_zero)
  hence "proj2_pt (cart2_pt p) = p" and "proj2_pt (cart2_pt q) = q"
    by (simp_all add: proj2_cart2)

  from `cart2_pt p = cart2_pt q`
  have "proj2_pt (cart2_pt p) = proj2_pt (cart2_pt q)" by simp
  with `proj2_pt (cart2_pt p) = p` [symmetric] and `proj2_pt (cart2_pt q) = q`
  show "p = q" by simp
qed

lemma on_equator_in_hyp2_rep:
  assumes "a \<in> hyp2" and "proj2_incident a equator"
  shows "\<exists> x. \<bar>x\<bar> < 1 \<and> a = proj2_abs (vector [x,0,1])"
proof -
  from `a \<in> hyp2` have "z_non_zero a" by (simp add: hyp2_S_z_non_zero)
  with `proj2_incident a equator` and on_equator_rep
  obtain x where "a = proj2_abs (vector [x,0,1])" (is "a = proj2_abs ?v")
    by auto

  have "?v \<noteq> 0" by (simp add: vec_eq_iff forall_3 vector_3)
  with `a \<in> hyp2` and `a = proj2_abs ?v`
  have "?v \<bullet> (M *v ?v) < 0" by (simp add: K2_abs)
  hence "x\<^sup>2 < 1"
    unfolding M_def matrix_vector_mult_def inner_vec_def
    by (simp add: sum_3 vector_3 power2_eq_square)
  with real_sqrt_abs [of x] and real_sqrt_less_iff [of "x\<^sup>2" 1]
  have "\<bar>x\<bar> < 1" by simp
  with `a = proj2_abs ?v`
  show "\<exists> x. \<bar>x\<bar> < 1 \<and> a = proj2_abs (vector [x,0,1])"
    by (simp add: exI [of _ x])
qed

lemma on_meridian_in_hyp2_rep:
  assumes "a \<in> hyp2" and "proj2_incident a meridian"
  shows "\<exists> y. \<bar>y\<bar> < 1 \<and> a = proj2_abs (vector [0,y,1])"
proof -
  from `a \<in> hyp2` have "z_non_zero a" by (simp add: hyp2_S_z_non_zero)
  with `proj2_incident a meridian` and on_meridian_rep
  obtain y where "a = proj2_abs (vector [0,y,1])" (is "a = proj2_abs ?v")
    by auto

  have "?v \<noteq> 0" by (simp add: vec_eq_iff forall_3 vector_3)
  with `a \<in> hyp2` and `a = proj2_abs ?v`
  have "?v \<bullet> (M *v ?v) < 0" by (simp add: K2_abs)
  hence "y\<^sup>2 < 1"
    unfolding M_def matrix_vector_mult_def inner_vec_def
    by (simp add: sum_3 vector_3 power2_eq_square)
  with real_sqrt_abs [of y] and real_sqrt_less_iff [of "y\<^sup>2" 1]
  have "\<bar>y\<bar> < 1" by simp
  with `a = proj2_abs ?v`
  show "\<exists> y. \<bar>y\<bar> < 1 \<and> a = proj2_abs (vector [0,y,1])"
    by (simp add: exI [of _ y])
qed

definition hyp2_cltn2 :: "hyp2 \<Rightarrow> cltn2 \<Rightarrow> hyp2" where
  "hyp2_cltn2 p A \<equiv> Abs_hyp2 (apply_cltn2 (Rep_hyp2 p) A)"

definition is_K2_isometry :: "cltn2 \<Rightarrow> bool" where
  "is_K2_isometry J \<equiv> (\<forall> p. apply_cltn2 p J \<in> S \<longleftrightarrow> p \<in> S)"

lemma cltn2_id_is_K2_isometry: "is_K2_isometry cltn2_id"
  unfolding is_K2_isometry_def
  by simp

lemma J_M_J_transpose_K2_isometry:
  assumes "k \<noteq> 0"
  and "repJ ** M ** transpose repJ = k *\<^sub>R M" (is "?N = _")
  shows "is_K2_isometry (cltn2_abs repJ)" (is "is_K2_isometry ?J")
proof -
  from `?N = k *\<^sub>R M`
  have "?N ** ((1/k) *\<^sub>R M) = mat 1"
    by (simp add: matrix_scalar_ac `k \<noteq> 0` M_self_inverse)
  with right_invertible_iff_invertible [of repJ]
  have "invertible repJ"
    by (simp add: matrix_mul_assoc
      exI [of _ "M ** transpose repJ ** ((1/k) *\<^sub>R M)"])

  have "\<forall> t. apply_cltn2 t ?J \<in> S \<longleftrightarrow> t \<in> S"
  proof
    fix t :: proj2
    have "proj2_rep t \<bullet> ((k *\<^sub>R M) *v proj2_rep t)
      = k * (proj2_rep t \<bullet> (M *v proj2_rep t))"
      by (simp add: scalar_matrix_vector_assoc [symmetric]  dot_scaleR_mult)
    with `?N = k *\<^sub>R M`
    have "proj2_rep t \<bullet> (?N *v proj2_rep t)
      = k * (proj2_rep t \<bullet> (M *v proj2_rep t))"
      by simp
    hence "proj2_rep t \<bullet> (?N *v proj2_rep t) = 0
      \<longleftrightarrow> k * (proj2_rep t \<bullet> (M *v proj2_rep t)) = 0"
      by simp
    with `k \<noteq> 0`
    have "proj2_rep t \<bullet> (?N *v proj2_rep t) = 0
      \<longleftrightarrow> proj2_rep t \<bullet> (M *v proj2_rep t) = 0"
      by simp
    with `invertible repJ`
    have "apply_cltn2 t ?J \<in> S \<longleftrightarrow> proj2_rep t \<bullet> (M *v proj2_rep t) = 0"
      by (simp add: apply_cltn2_right_abs_in_S)
    thus "apply_cltn2 t ?J \<in> S \<longleftrightarrow> t \<in> S" by (unfold S_alt_def)
  qed
  thus "is_K2_isometry ?J" by (unfold is_K2_isometry_def)
qed

lemma equator_reflect_K2_isometry:
  shows "is_K2_isometry equator_reflect"
  unfolding compass_reflect_defs
  by (rule J_M_J_transpose_K2_isometry [of 1])
     (simp_all add: M_def matrix_matrix_mult_def transpose_def
       vec_eq_iff forall_3 sum_3 vector_3)

lemma meridian_reflect_K2_isometry:
  shows "is_K2_isometry meridian_reflect"
  unfolding compass_reflect_defs
  by (rule J_M_J_transpose_K2_isometry [of 1])
     (simp_all add: M_def matrix_matrix_mult_def transpose_def
       vec_eq_iff forall_3 sum_3 vector_3)

lemma cltn2_compose_is_K2_isometry:
  assumes "is_K2_isometry H" and "is_K2_isometry J"
  shows "is_K2_isometry (cltn2_compose H J)"
  using `is_K2_isometry H` and `is_K2_isometry J`
  unfolding is_K2_isometry_def
  by (simp add: cltn2.act_act [simplified, symmetric])

lemma cltn2_inverse_is_K2_isometry:
  assumes "is_K2_isometry J"
  shows "is_K2_isometry (cltn2_inverse J)"
proof -
  { fix p
    from `is_K2_isometry J`
    have "apply_cltn2 p (cltn2_inverse J) \<in> S
      \<longleftrightarrow> apply_cltn2 (apply_cltn2 p (cltn2_inverse J)) J \<in> S"
      unfolding is_K2_isometry_def
      by simp
    hence "apply_cltn2 p (cltn2_inverse J) \<in> S \<longleftrightarrow> p \<in> S"
      by (simp add: cltn2.act_inv_act [simplified]) }
  thus "is_K2_isometry (cltn2_inverse J)"
    unfolding is_K2_isometry_def ..
qed

interpretation K2_isometry_subgroup: subgroup
  "Collect is_K2_isometry"
  "(|carrier = UNIV, mult = cltn2_compose, one = cltn2_id|)"
  unfolding subgroup_def
  by (simp add:
    cltn2_id_is_K2_isometry
    cltn2_compose_is_K2_isometry
    cltn2_inverse_is_K2_isometry)

interpretation K2_isometry: group
  "(|carrier = Collect is_K2_isometry, mult = cltn2_compose, one = cltn2_id|)"
  using cltn2.is_group and K2_isometry_subgroup.subgroup_is_group
  by simp

lemma K2_isometry_inverse_inv [simp]:
  assumes "is_K2_isometry J"
  shows "inv\<^bsub>(|carrier = Collect is_K2_isometry, mult = cltn2_compose, one = cltn2_id|)\<^esub> J
  = cltn2_inverse J"
  using cltn2_left_inverse
    and `is_K2_isometry J`
    and cltn2_inverse_is_K2_isometry
    and K2_isometry.inv_equality
  by simp

definition real_hyp2_C :: "[hyp2, hyp2, hyp2, hyp2] \<Rightarrow> bool"
  ("_ _ \<congruent>\<^sub>K _ _" [99,99,99,99] 50) where
  "p q \<congruent>\<^sub>K r s \<equiv>
    (\<exists> A. is_K2_isometry A \<and> hyp2_cltn2 p A = r \<and> hyp2_cltn2 q A = s)"

definition real_hyp2_B :: "[hyp2, hyp2, hyp2] \<Rightarrow> bool"
("B\<^sub>K _ _ _" [99,99,99] 50) where
  "B\<^sub>K p q r \<equiv> B\<^sub>\<real> (hyp2_rep p) (hyp2_rep q) (hyp2_rep r)"


subsection {* $K$-isometries map the interior of the conic to itself *}

lemma collinear_quadratic:
  assumes "t = i *\<^sub>R a + r"
  shows "t \<bullet> (M *v t) =
  (a \<bullet> (M *v a)) * i\<^sup>2 + 2 * (a \<bullet> (M *v r)) * i + r \<bullet> (M *v r)"
proof -
  from M_reverse have "i * (a \<bullet> (M *v r)) = i * (r \<bullet> (M *v a))" by simp
  with `t = i *\<^sub>R a + r`
  show "t \<bullet> (M *v t) =
    (a \<bullet> (M *v a)) * i\<^sup>2 + 2 * (a \<bullet> (M *v r)) * i + r \<bullet> (M *v r)"
    by (simp add:
      inner_add_left
      matrix_vector_right_distrib
      inner_add_right
      matrix_scalar_vector_ac
      inner_scaleR_right
      scalar_matrix_vector_assoc [symmetric]
      M_reverse
      power2_eq_square
      algebra_simps)
qed

lemma S_quadratic':
  assumes "p \<noteq> 0" and "q \<noteq> 0" and "proj2_abs p \<noteq> proj2_abs q"
  shows "proj2_abs (k *\<^sub>R p + q) \<in> S
  \<longleftrightarrow> p \<bullet> (M *v p) * k\<^sup>2 + p \<bullet> (M *v q) * 2 * k + q \<bullet> (M *v q) = 0"
proof -
  let ?r = "k *\<^sub>R p + q"
  from `p \<noteq> 0` and `q \<noteq> 0` and `proj2_abs p \<noteq> proj2_abs q`
    and dependent_proj2_abs [of p q k 1]
  have "?r \<noteq> 0" by auto
  hence "proj2_abs ?r \<in> S \<longleftrightarrow> ?r \<bullet> (M *v ?r) = 0" by (rule S_abs)
  with collinear_quadratic [of ?r k p q]
  show "proj2_abs ?r \<in> S
    \<longleftrightarrow> p \<bullet> (M *v p) * k\<^sup>2 + p \<bullet> (M *v q) * 2 * k + q \<bullet> (M *v q) = 0"
    by (simp add: dot_lmul_matrix [symmetric] algebra_simps)
qed

lemma S_quadratic:
  assumes "p \<noteq> q" and "r = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep q)"
  shows "r \<in> S
  \<longleftrightarrow> proj2_rep p \<bullet> (M *v proj2_rep p) * k\<^sup>2
      + proj2_rep p \<bullet> (M *v proj2_rep q) * 2 * k
      + proj2_rep q \<bullet> (M *v proj2_rep q)
    = 0"
proof -
  let ?u = "proj2_rep p"
  let ?v = "proj2_rep q"
  let ?w = "k *\<^sub>R ?u + ?v"
  have "?u \<noteq> 0" and "?v \<noteq> 0" by (rule proj2_rep_non_zero)+

  from `p \<noteq> q` have "proj2_abs ?u \<noteq> proj2_abs ?v" by (simp add: proj2_abs_rep)
  with `?u \<noteq> 0` and `?v \<noteq> 0` and `r = proj2_abs ?w`
  show "r \<in> S
    \<longleftrightarrow> ?u \<bullet> (M *v ?u) * k\<^sup>2 + ?u \<bullet> (M *v ?v) * 2 * k + ?v \<bullet> (M *v ?v) = 0"
    by (simp add: S_quadratic')
qed

definition quarter_discrim :: "real^3 \<Rightarrow> real^3 \<Rightarrow> real" where
  "quarter_discrim p q \<equiv> (p \<bullet> (M *v q))\<^sup>2 - p \<bullet> (M *v p) * (q \<bullet> (M *v q))"

lemma quarter_discrim_invariant:
  assumes "t = i *\<^sub>R a + r"
  shows "quarter_discrim a t = quarter_discrim a r"
proof -
  from `t = i *\<^sub>R a + r`
  have "a \<bullet> (M *v t) = i * (a \<bullet> (M *v a)) + a \<bullet> (M *v r)"
    by (simp add:
      matrix_vector_right_distrib
      inner_add_right
      matrix_scalar_vector_ac
      scalar_matrix_vector_assoc [symmetric])
  hence "(a \<bullet> (M *v t))\<^sup>2 =
    (a \<bullet> (M *v a))\<^sup>2 * i\<^sup>2 +
    2 * (a \<bullet> (M *v a)) * (a \<bullet> (M *v r)) * i +
    (a \<bullet> (M *v r))\<^sup>2"
    by (simp add: power2_eq_square algebra_simps)
  moreover from collinear_quadratic and `t = i *\<^sub>R a + r`
  have "a \<bullet> (M *v a) * (t \<bullet> (M *v t)) =
    (a \<bullet> (M *v a))\<^sup>2 * i\<^sup>2 +
    2 * (a \<bullet> (M *v a)) * (a \<bullet> (M *v r)) * i +
    a \<bullet> (M *v a) * (r \<bullet> (M *v r))"
    by (simp add: power2_eq_square algebra_simps)
  ultimately show "quarter_discrim a t = quarter_discrim a r"
    by (unfold quarter_discrim_def, simp)
qed

lemma quarter_discrim_positive:
  assumes "p \<noteq> 0"  and "q \<noteq> 0" and "proj2_abs p \<noteq> proj2_abs q" (is "?pp \<noteq> ?pq")
  and "proj2_abs p \<in> K2"
  shows "quarter_discrim p q > 0"
proof -
  let ?i = "-q$3/p$3"
  let ?t = "?i *\<^sub>R p + q"

  from `p \<noteq> 0` and `?pp \<in> K2`
  have "p \<bullet> (M *v p) < 0" by (subst K2_abs [symmetric])
  hence "p$3 \<noteq> 0" by (rule M_neg_imp_z_non_zero)
  hence "?t$3 = 0" by simp
  hence "?t \<bullet> (M *v ?t) = (?t$1)\<^sup>2 + (?t$2)\<^sup>2"
    unfolding matrix_vector_mult_def and M_def and vector_def
    by (simp add: inner_vec_def sum_3 power2_eq_square)

  from `p$3 \<noteq> 0` have "p \<noteq> 0" by auto
  with `q \<noteq> 0` and `?pp \<noteq> ?pq` and dependent_proj2_abs [of p q ?i 1]
  have "?t \<noteq> 0" by auto
  with `?t$3 = 0` have "?t$1 \<noteq> 0 \<or> ?t$2 \<noteq> 0" by (simp add: vec_eq_iff forall_3)
  hence "(?t$1)\<^sup>2 > 0 \<or> (?t$2)\<^sup>2 > 0" by simp
  moreover have "(?t$2)\<^sup>2 \<ge> 0" and "(?t$1)\<^sup>2 \<ge> 0" by simp_all
  ultimately have "(?t$1)\<^sup>2 + (?t$2)\<^sup>2 > 0" by arith
  with `?t \<bullet> (M *v ?t) = (?t$1)\<^sup>2 + (?t$2)\<^sup>2` have "?t \<bullet> (M *v ?t) > 0" by simp
  with mult_neg_pos [of "p \<bullet> (M *v p)"] and `p \<bullet> (M *v p) < 0`
  have "p \<bullet> (M *v p) * (?t \<bullet> (M *v ?t)) < 0" by simp
  moreover have "(p \<bullet> (M *v ?t))\<^sup>2 \<ge> 0" by simp
  ultimately
  have "(p \<bullet> (M *v ?t))\<^sup>2 - p \<bullet> (M *v p) * (?t \<bullet> (M *v ?t)) > 0" by arith
  with quarter_discrim_invariant [of ?t ?i p q]
  show "quarter_discrim p q > 0" by (unfold quarter_discrim_def, simp)
qed

lemma quarter_discrim_self_zero:
  assumes "proj2_abs a = proj2_abs b"
  shows "quarter_discrim a b = 0"
proof cases
  assume "b = 0"
  thus "quarter_discrim a b = 0" by (unfold quarter_discrim_def, simp)
next
  assume "b \<noteq> 0"
  with `proj2_abs a = proj2_abs b` and proj2_abs_abs_mult
  obtain k where "a = k *\<^sub>R b" by auto
  thus "quarter_discrim a b = 0"
    unfolding quarter_discrim_def
    by (simp add: power2_eq_square
      matrix_scalar_vector_ac
      scalar_matrix_vector_assoc [symmetric])
qed

definition S_intersection_coeff1 :: "real^3 \<Rightarrow> real^3 \<Rightarrow> real" where
  "S_intersection_coeff1 p q
  \<equiv> (-p \<bullet> (M *v q) + sqrt (quarter_discrim p q)) / (p \<bullet> (M *v p))"

definition S_intersection_coeff2 :: "real^3 \<Rightarrow> real^3 \<Rightarrow> real" where
  "S_intersection_coeff2 p q
  \<equiv> (-p \<bullet> (M *v q) - sqrt (quarter_discrim p q)) / (p \<bullet> (M *v p))"

definition S_intersection1_rep :: "real^3 \<Rightarrow> real^3 \<Rightarrow> real^3" where
  "S_intersection1_rep p q \<equiv> (S_intersection_coeff1 p q) *\<^sub>R p + q"

definition S_intersection2_rep :: "real^3 \<Rightarrow> real^3 \<Rightarrow> real^3" where
  "S_intersection2_rep p q \<equiv> (S_intersection_coeff2 p q) *\<^sub>R p + q"

definition S_intersection1 :: "real^3 \<Rightarrow> real^3 \<Rightarrow> proj2" where
  "S_intersection1 p q \<equiv> proj2_abs (S_intersection1_rep p q)"

definition S_intersection2 :: "real^3 \<Rightarrow> real^3 \<Rightarrow> proj2" where
  "S_intersection2 p q \<equiv> proj2_abs (S_intersection2_rep p q)"

lemmas S_intersection_coeffs_defs =
  S_intersection_coeff1_def S_intersection_coeff2_def

lemmas S_intersections_defs =
  S_intersection1_def S_intersection2_def
  S_intersection1_rep_def S_intersection2_rep_def

lemma S_intersection_coeffs_distinct:
  assumes "p \<noteq> 0" and "q \<noteq> 0" and "proj2_abs p \<noteq> proj2_abs q" (is "?pp \<noteq> ?pq")
  and "proj2_abs p \<in> K2"
  shows "S_intersection_coeff1 p q \<noteq> S_intersection_coeff2 p q"
proof -
  from `p \<noteq> 0` and `?pp \<in> K2`
  have "p \<bullet> (M *v p) < 0" by (subst K2_abs [symmetric])

  from assms have "quarter_discrim p q > 0" by (rule quarter_discrim_positive)
  with `p \<bullet> (M *v p) < 0`
  show "S_intersection_coeff1 p q \<noteq> S_intersection_coeff2 p q"
    by (unfold S_intersection_coeffs_defs, simp)
qed

lemma S_intersections_distinct:
  assumes "p \<noteq> 0" and "q \<noteq> 0" and "proj2_abs p \<noteq> proj2_abs q" (is "?pp \<noteq> ?pq")
  and "proj2_abs p \<in> K2"
  shows "S_intersection1 p q \<noteq> S_intersection2 p q"
proof-
  from `p \<noteq> 0` and `q \<noteq> 0` and `?pp \<noteq> ?pq` and `?pp \<in> K2`
  have "S_intersection_coeff1 p q \<noteq> S_intersection_coeff2 p q"
    by (rule S_intersection_coeffs_distinct)
  with `p \<noteq> 0` and `q \<noteq> 0` and `?pp \<noteq> ?pq` and proj2_Col_coeff_unique'
  show "S_intersection1 p q \<noteq> S_intersection2 p q"
    by (unfold S_intersections_defs, auto)
qed

lemma S_intersections_in_S:
  assumes "p \<noteq> 0"  and "q \<noteq> 0" and "proj2_abs p \<noteq> proj2_abs q" (is "?pp \<noteq> ?pq")
  and "proj2_abs p \<in> K2"
  shows "S_intersection1 p q \<in> S" and "S_intersection2 p q \<in> S"
proof -
  let ?j = "S_intersection_coeff1 p q"
  let ?k = "S_intersection_coeff2 p q"
  let ?a = "p \<bullet> (M *v p)"
  let ?b = "2 * (p \<bullet> (M *v q))"
  let ?c = "q \<bullet> (M *v q)"

  from `p \<noteq> 0` and `?pp \<in> K2` have "?a < 0" by (subst K2_abs [symmetric])

  have qd: "discrim ?a ?b ?c = 4 * quarter_discrim p q"
    unfolding discrim_def quarter_discrim_def
    by (simp add: power2_eq_square)
  with times_divide_times_eq [of
    2 2 "sqrt (quarter_discrim p q) - p \<bullet> (M *v q)" ?a]
    and times_divide_times_eq [of
    2 2 "-p \<bullet> (M *v q) - sqrt (quarter_discrim p q)" ?a]
    and real_sqrt_mult and real_sqrt_abs [of 2]
  have "?j = (-?b + sqrt (discrim ?a ?b ?c)) / (2 * ?a)"
    and "?k = (-?b - sqrt (discrim ?a ?b ?c)) / (2 * ?a)"
    by (unfold S_intersection_coeffs_defs, simp_all add: algebra_simps)

  from assms have "quarter_discrim p q > 0" by (rule quarter_discrim_positive)
  with qd
  have "discrim (p \<bullet> (M *v p)) (2 * (p \<bullet> (M *v q))) (q \<bullet> (M *v q)) > 0"
    by simp
  with `?j = (-?b + sqrt (discrim ?a ?b ?c)) / (2 * ?a)`
    and `?k = (-?b - sqrt (discrim ?a ?b ?c)) / (2 * ?a)`
    and `?a < 0` and discriminant_nonneg [of ?a ?b ?c ?j]
    and discriminant_nonneg [of ?a ?b ?c ?k]
  have "p \<bullet> (M *v p) * ?j\<^sup>2 + 2 * (p \<bullet> (M *v q)) * ?j + q \<bullet> (M *v q) = 0"
    and "p \<bullet> (M *v p) * ?k\<^sup>2 + 2 * (p \<bullet> (M *v q)) * ?k + q \<bullet> (M *v q) = 0"
    by (unfold S_intersection_coeffs_defs, auto)
  with `p \<noteq> 0` and `q \<noteq> 0` and `?pp \<noteq> ?pq` and S_quadratic'
  show "S_intersection1 p q \<in> S" and "S_intersection2 p q \<in> S"
    by (unfold S_intersections_defs, simp_all)
qed

lemma S_intersections_Col:
  assumes "p \<noteq> 0" and "q \<noteq> 0"
  shows "proj2_Col (proj2_abs p) (proj2_abs q) (S_intersection1 p q)"
  (is "proj2_Col ?pp ?pq ?pr")
    and "proj2_Col (proj2_abs p) (proj2_abs q) (S_intersection2 p q)"
  (is "proj2_Col ?pp ?pq ?ps")
proof -
  { assume "?pp = ?pq"
    hence "proj2_Col ?pp ?pq ?pr" and "proj2_Col ?pp ?pq ?ps"
      by (simp_all add: proj2_Col_coincide) }
  moreover
  { assume "?pp \<noteq> ?pq"
    with `p \<noteq> 0` and `q \<noteq> 0` and dependent_proj2_abs [of p q _ 1]
    have "S_intersection1_rep p q \<noteq> 0" (is "?r \<noteq> 0")
      and "S_intersection2_rep p q \<noteq> 0" (is "?s \<noteq> 0")
      by (unfold S_intersection1_rep_def S_intersection2_rep_def, auto)
    with `p \<noteq> 0` and `q \<noteq> 0`
      and proj2_Col_abs [of p q ?r "S_intersection_coeff1 p q" 1 "-1"]
      and proj2_Col_abs [of p q ?s "S_intersection_coeff2 p q" 1 "-1"]
    have "proj2_Col ?pp ?pq ?pr" and "proj2_Col ?pp ?pq ?ps"
      by (unfold S_intersections_defs, simp_all) }
  ultimately show "proj2_Col ?pp ?pq ?pr" and "proj2_Col ?pp ?pq ?ps" by fast+
qed

lemma S_intersections_incident:
  assumes "p \<noteq> 0" and "q \<noteq> 0" and "proj2_abs p \<noteq> proj2_abs q" (is "?pp \<noteq> ?pq")
  and "proj2_incident (proj2_abs p) l" and "proj2_incident (proj2_abs q) l"
  shows "proj2_incident (S_intersection1 p q) l" (is "proj2_incident ?pr l")
  and "proj2_incident (S_intersection2 p q) l" (is "proj2_incident ?ps l")
proof -
  from `p \<noteq> 0` and `q \<noteq> 0`
  have "proj2_Col ?pp ?pq ?pr" and "proj2_Col ?pp ?pq ?ps"
    by (rule S_intersections_Col)+
  with `?pp \<noteq> ?pq` and `proj2_incident ?pp l` and `proj2_incident ?pq l`
    and proj2_incident_iff_Col
  show "proj2_incident ?pr l" and "proj2_incident ?ps l" by fast+
qed

lemma K2_line_intersect_twice:
  assumes "a \<in> K2" and "a \<noteq> r"
  shows "\<exists> s u. s \<noteq> u \<and> s \<in> S \<and> u \<in> S \<and> proj2_Col a r s \<and> proj2_Col a r u"
proof -
  let ?a' = "proj2_rep a"
  let ?r' = "proj2_rep r"
  from proj2_rep_non_zero have "?a' \<noteq> 0" and "?r' \<noteq> 0" by simp_all

  from `?a' \<noteq> 0` and K2_imp_M_neg and proj2_abs_rep and `a \<in> K2`
  have "?a' \<bullet> (M *v ?a') < 0" by simp

  from `a \<noteq> r` have "proj2_abs ?a' \<noteq> proj2_abs ?r'" by (simp add: proj2_abs_rep)

  from `a \<in> K2` have "proj2_abs ?a' \<in> K2" by (simp add: proj2_abs_rep)
  with `?a' \<noteq> 0` and `?r' \<noteq> 0` and `proj2_abs ?a' \<noteq> proj2_abs ?r'`
  have "S_intersection1 ?a' ?r' \<noteq> S_intersection2 ?a' ?r'" (is "?s \<noteq> ?u")
    by (rule S_intersections_distinct)

  from `?a' \<noteq> 0` and `?r' \<noteq> 0` and `proj2_abs ?a' \<noteq> proj2_abs ?r'`
    and `proj2_abs ?a' \<in> K2`
  have "?s \<in> S" and "?u \<in> S" by (rule S_intersections_in_S)+

  from `?a' \<noteq> 0` and `?r' \<noteq> 0`
  have "proj2_Col (proj2_abs ?a') (proj2_abs ?r') ?s"
    and "proj2_Col (proj2_abs ?a') (proj2_abs ?r') ?u"
    by (rule S_intersections_Col)+
  hence "proj2_Col a r ?s" and "proj2_Col a r ?u"
    by (simp_all add: proj2_abs_rep)
  with `?s \<noteq> ?u` and `?s \<in> S` and `?u \<in> S`
  show "\<exists> s u. s \<noteq> u \<and> s \<in> S \<and> u \<in> S \<and> proj2_Col a r s \<and> proj2_Col a r u"
    by auto
qed

lemma point_in_S_polar_is_tangent:
  assumes "p \<in> S" and "q \<in> S" and "proj2_incident q (polar p)"
  shows "q = p"
proof -
  from `p \<in> S` have "proj2_incident p (polar p)"
    by (subst incident_own_polar_in_S)

  from line_incident_point_not_in_S
  obtain r where "r \<notin> S" and "proj2_incident r (polar p)" by auto
  let ?u = "proj2_rep r"
  let ?v = "proj2_rep p"
  from `r \<notin> S` and `p \<in> S` and `q \<in> S` have "r \<noteq> p" and "q \<noteq> r" by auto
  with `proj2_incident p (polar p)`
    and `proj2_incident q (polar p)`
    and `proj2_incident r (polar p)`
    and proj2_incident_iff [of r p "polar p" q]
  obtain k where "q = proj2_abs (k *\<^sub>R ?u + ?v)" by auto
  with `r \<noteq> p` and `q \<in> S` and S_quadratic
  have "?u \<bullet> (M *v ?u) * k\<^sup>2 + ?u \<bullet> (M *v ?v) * 2 * k + ?v \<bullet> (M *v ?v) = 0"
    by simp
  moreover from `p \<in> S` have "?v \<bullet> (M *v ?v) = 0" by (unfold S_alt_def)
  moreover from `proj2_incident r (polar p)`
  have "?u \<bullet> (M *v ?v) = 0" by (unfold incident_polar)
  moreover from `r \<notin> S` have "?u \<bullet> (M *v ?u) \<noteq> 0" by (unfold S_alt_def)
  ultimately have "k = 0" by simp
  with `q = proj2_abs (k *\<^sub>R ?u + ?v)`
  show "q = p" by (simp add: proj2_abs_rep)
qed

lemma line_through_K2_intersect_S_twice:
  assumes "p \<in> K2" and "proj2_incident p l"
  shows "\<exists> q r. q \<noteq> r \<and> q \<in> S \<and> r \<in> S \<and> proj2_incident q l \<and> proj2_incident r l"
proof -
  from proj2_another_point_on_line
  obtain s where "s \<noteq> p" and "proj2_incident s l" by auto
  from `p \<in> K2` and `s \<noteq> p` and K2_line_intersect_twice [of p s]
  obtain q and r where "q \<noteq> r" and "q \<in> S" and "r \<in> S"
    and "proj2_Col p s q" and "proj2_Col p s r"
    by auto
  with `s \<noteq> p` and `proj2_incident p l` and `proj2_incident s l`
    and proj2_incident_iff_Col [of p s]
  have "proj2_incident q l" and "proj2_incident r l" by fast+
  with `q \<noteq> r` and `q \<in> S` and `r \<in> S`
  show "\<exists> q r. q \<noteq> r \<and> q \<in> S \<and> r \<in> S \<and> proj2_incident q l \<and> proj2_incident r l"
    by auto
qed

lemma line_through_K2_intersect_S_again:
  assumes "p \<in> K2" and "proj2_incident p l"
  shows "\<exists> r. r \<noteq> q \<and> r \<in> S \<and> proj2_incident r l"
proof -
  from `p \<in> K2` and `proj2_incident p l`
    and line_through_K2_intersect_S_twice [of p l]
  obtain s and t where "s \<noteq> t" and "s \<in> S" and "t \<in> S"
    and "proj2_incident s l" and "proj2_incident t l"
    by auto
  show "\<exists> r. r \<noteq> q \<and> r \<in> S \<and> proj2_incident r l"
  proof cases
    assume "t = q"
    with `s \<noteq> t` and `s \<in> S` and `proj2_incident s l`
    have "s \<noteq> q \<and> s \<in> S \<and> proj2_incident s l" by simp
    thus "\<exists> r. r \<noteq> q \<and> r \<in> S \<and> proj2_incident r l" ..
  next
    assume "t \<noteq> q"
    with `t \<in> S` and `proj2_incident t l`
    have "t \<noteq> q \<and> t \<in> S \<and> proj2_incident t l" by simp
    thus "\<exists> r. r \<noteq> q \<and> r \<in> S \<and> proj2_incident r l" ..
  qed
qed

lemma line_through_K2_intersect_S:
  assumes "p \<in> K2" and "proj2_incident p l"
  shows "\<exists> r. r \<in> S \<and> proj2_incident r l"
proof -
  from assms
  have "\<exists> r. r \<noteq> p \<and> r \<in> S \<and> proj2_incident r l"
    by (rule line_through_K2_intersect_S_again)
  thus "\<exists> r. r \<in> S \<and> proj2_incident r l" by auto
qed

lemma line_intersect_S_at_most_twice:
  "\<exists> p q. \<forall> r\<in>S. proj2_incident r l \<longrightarrow> r = p \<or> r = q"
proof -
  from line_incident_point_not_in_S
  obtain s where "s \<notin> S" and "proj2_incident s l" by auto
  let ?v = "proj2_rep s"
  from proj2_another_point_on_line
  obtain t where "t \<noteq> s" and "proj2_incident t l" by auto
  let ?w = "proj2_rep t"
  have "?v \<noteq> 0" and "?w \<noteq> 0" by (rule proj2_rep_non_zero)+

  let ?a = "?v \<bullet> (M *v ?v)"
  let ?b = "2 * (?v \<bullet> (M *v ?w))"
  let ?c = "?w \<bullet> (M *v ?w)"
  from `s \<notin> S` have "?a \<noteq> 0"
    unfolding S_def and conic_sgn_def
    by auto
  let ?j = "(-?b + sqrt (discrim ?a ?b ?c)) / (2 * ?a)"
  let ?k = "(-?b - sqrt (discrim ?a ?b ?c)) / (2 * ?a)"
  let ?p = "proj2_abs (?j *\<^sub>R ?v + ?w)"
  let ?q = "proj2_abs (?k *\<^sub>R ?v + ?w)"
  have "\<forall> r\<in>S. proj2_incident r l \<longrightarrow> r = ?p \<or> r = ?q"
  proof
    fix r
    assume "r \<in> S"
    with `s \<notin> S` have "r \<noteq> s" by auto
    { assume "proj2_incident r l"
      with `t \<noteq> s` and `r \<noteq> s` and `proj2_incident s l` and `proj2_incident t l`
        and proj2_incident_iff [of s t l r]
      obtain i where "r = proj2_abs (i *\<^sub>R ?v + ?w)" by auto
      with `r \<in> S` and `t \<noteq> s` and S_quadratic
      have "?a * i\<^sup>2 + ?b * i + ?c = 0" by simp
      with `?a \<noteq> 0` and discriminant_iff have "i = ?j \<or> i = ?k" by simp
      with `r = proj2_abs (i *\<^sub>R ?v + ?w)` have "r = ?p \<or> r = ?q" by auto }
    thus "proj2_incident r l \<longrightarrow> r = ?p \<or> r = ?q" ..
  qed
  thus "\<exists> p q. \<forall> r\<in>S. proj2_incident r l \<longrightarrow> r = p \<or> r = q" by auto
qed

lemma card_line_intersect_S:
  assumes "T \<subseteq> S" and "proj2_set_Col T"
  shows "card T \<le> 2"
proof -
  from `proj2_set_Col T`
  obtain l where "\<forall> p\<in>T. proj2_incident p l" unfolding proj2_set_Col_def ..
  from line_intersect_S_at_most_twice [of l]
  obtain b and c where "\<forall> a\<in>S. proj2_incident a l \<longrightarrow> a = b \<or> a = c" by auto
  with `\<forall> p\<in>T. proj2_incident p l` and `T \<subseteq> S`
  have "T \<subseteq> {b,c}" by auto
  hence "card T \<le> card {b,c}" by (simp add: card_mono)
  also from card_suc_ge_insert [of b "{c}"] have "\<dots> \<le> 2" by simp
  finally show "card T \<le> 2" .
qed

lemma line_S_two_intersections_only:
  assumes "p \<noteq> q" and "p \<in> S" and "q \<in> S" and "r \<in> S"
  and "proj2_incident p l" and "proj2_incident q l" and "proj2_incident r l"
  shows "r = p \<or> r = q"
proof -
  from `p \<noteq> q` have "card {p,q} = 2" by simp

  from `p \<in> S` and `q \<in> S` and `r \<in> S` have "{r,p,q} \<subseteq> S" by simp_all

  from `proj2_incident p l` and `proj2_incident q l` and `proj2_incident r l`
  have "proj2_set_Col {r,p,q}"
    by (unfold proj2_set_Col_def) (simp add: exI [of _ l])
  with `{r,p,q} \<subseteq> S` have "card {r,p,q} \<le> 2" by (rule card_line_intersect_S)

  show "r = p \<or> r = q"
  proof (rule ccontr)
    assume "\<not> (r = p \<or> r = q)"
    hence "r \<notin> {p,q}" by simp
    with `card {p,q} = 2` and card_insert_disjoint [of "{p,q}" r]
    have "card {r,p,q} = 3" by simp
    with `card {r,p,q} \<le> 2` show False by simp
  qed
qed

lemma line_through_K2_intersect_S_exactly_twice:
  assumes "p \<in> K2" and "proj2_incident p l"
  shows "\<exists> q r. q \<noteq> r \<and> q \<in> S \<and> r \<in> S \<and> proj2_incident q l \<and> proj2_incident r l
  \<and> (\<forall> s\<in>S. proj2_incident s l \<longrightarrow> s = q \<or> s = r)"
proof -
  from `p \<in> K2` and `proj2_incident p l`
    and line_through_K2_intersect_S_twice [of p l]
  obtain q and r where "q \<noteq> r" and "q \<in> S" and "r \<in> S"
    and "proj2_incident q l" and "proj2_incident r l"
    by auto
  with line_S_two_intersections_only
  show "\<exists> q r. q \<noteq> r \<and> q \<in> S \<and> r \<in> S \<and> proj2_incident q l \<and> proj2_incident r l
    \<and> (\<forall> s\<in>S. proj2_incident s l \<longrightarrow> s = q \<or> s = r)"
    by blast
qed

lemma tangent_not_through_K2:
  assumes "p \<in> S" and "q \<in> K2"
  shows "\<not> proj2_incident q (polar p)"
proof
  assume "proj2_incident q (polar p)"
  with `q \<in> K2` and line_through_K2_intersect_S_again [of q "polar p" p]
  obtain r where "r \<noteq> p" and "r \<in> S" and "proj2_incident r (polar p)" by auto
  from `p \<in> S` and `r \<in> S` and `proj2_incident r (polar p)`
  have "r = p" by (rule point_in_S_polar_is_tangent)
  with `r \<noteq> p` show False ..
qed

lemma outside_exists_line_not_intersect_S:
  assumes "conic_sgn p = 1"
  shows "\<exists> l. proj2_incident p l \<and> (\<forall> q. proj2_incident q l \<longrightarrow> q \<notin> S)"
proof -
  let ?r = "proj2_intersection (polar p) z_zero"
  have "proj2_incident ?r (polar p)" and "proj2_incident ?r z_zero"
    by (rule proj2_intersection_incident)+
  from `proj2_incident ?r z_zero`
  have "conic_sgn ?r = 1" by (rule z_zero_conic_sgn_1)
  with `conic_sgn p = 1`
  have "proj2_rep p \<bullet> (M *v proj2_rep p) > 0"
    and "proj2_rep ?r \<bullet> (M *v proj2_rep ?r) > 0"
    by (unfold conic_sgn_def) (simp_all add: sgn_1_pos)

  from `proj2_incident ?r (polar p)`
  have "proj2_incident p (polar ?r)" by (rule incident_polar_swap)
  hence "proj2_rep p \<bullet> (M *v proj2_rep ?r) = 0" by (simp add: incident_polar)

  have "p \<noteq> ?r"
  proof
    assume "p = ?r"
    with `proj2_incident ?r (polar p)` have "proj2_incident p (polar p)" by simp
    hence "proj2_rep p \<bullet> (M *v proj2_rep p) = 0" by (simp add: incident_polar)
    with `proj2_rep p \<bullet> (M *v proj2_rep p) > 0` show False by simp
  qed

  let ?l = "proj2_line_through p ?r"
  have "proj2_incident p ?l" and "proj2_incident ?r ?l"
    by (rule proj2_line_through_incident)+

  have "\<forall> q. proj2_incident q ?l \<longrightarrow> q \<notin> S"
  proof
    fix q
    show "proj2_incident q ?l \<longrightarrow> q \<notin> S"
    proof
      assume "proj2_incident q ?l"
      with `p \<noteq> ?r` and `proj2_incident p ?l` and `proj2_incident ?r ?l`
      have "q = p \<or> (\<exists> k. q = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep ?r))"
        by (simp add: proj2_incident_iff [of p ?r ?l q])

      show "q \<notin> S"
      proof cases
        assume "q = p"
        with `conic_sgn p = 1` show "q \<notin> S" by (unfold S_def) simp
      next
        assume "q \<noteq> p"
        with `q = p \<or> (\<exists> k. q = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep ?r))`
        obtain k where "q = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep ?r)"
          by auto
        from `proj2_rep p \<bullet> (M *v proj2_rep p) > 0`
        have "proj2_rep p \<bullet> (M *v proj2_rep p) * k\<^sup>2 \<ge> 0"
          by simp
        with `proj2_rep p \<bullet> (M *v proj2_rep ?r) = 0`
          and `proj2_rep ?r \<bullet> (M *v proj2_rep ?r) > 0`
        have "proj2_rep p \<bullet> (M *v proj2_rep p) * k\<^sup>2
          + proj2_rep p \<bullet> (M *v proj2_rep ?r) * 2 * k
          + proj2_rep ?r \<bullet> (M *v proj2_rep ?r)
          > 0"
          by simp
        with `p \<noteq> ?r` and `q = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep ?r)`
        show "q \<notin> S" by (simp add: S_quadratic)
      qed
    qed
  qed
  with `proj2_incident p ?l`
  show "\<exists> l. proj2_incident p l \<and> (\<forall> q. proj2_incident q l \<longrightarrow> q \<notin> S)"
    by (simp add: exI [of _ ?l])
qed

lemma lines_through_intersect_S_twice_in_K2:
  assumes "\<forall> l. proj2_incident p l
  \<longrightarrow> (\<exists> q r. q \<noteq> r \<and> q \<in> S \<and> r \<in> S \<and> proj2_incident q l \<and> proj2_incident r l)"
  shows "p \<in> K2"
proof (rule ccontr)
  assume "p \<notin> K2"
  hence "conic_sgn p \<ge> 0" by (unfold K2_def) simp

  have "\<not> (\<forall> l. proj2_incident p l \<longrightarrow> (\<exists> q r.
    q \<noteq> r \<and> q \<in> S \<and> r \<in> S \<and> proj2_incident q l \<and> proj2_incident r l))"
  proof cases
    assume "conic_sgn p = 0"
    hence "p \<in> S" unfolding S_def ..
    hence "proj2_incident p (polar p)" by (simp add: incident_own_polar_in_S)
    let ?l = "polar p"
    have "\<not> (\<exists> q r.
      q \<noteq> r \<and> q \<in> S \<and> r \<in> S \<and> proj2_incident q ?l \<and> proj2_incident r ?l)"
    proof
      assume "\<exists> q r.
        q \<noteq> r \<and> q \<in> S \<and> r \<in> S \<and> proj2_incident q ?l \<and> proj2_incident r ?l"
      then obtain q and r where "q \<noteq> r" and "q \<in> S" and "r \<in> S"
        and "proj2_incident q ?l" and "proj2_incident r ?l"
        by auto
      from `p \<in> S` and `q \<in> S` and `proj2_incident q ?l`
        and `r \<in> S` and `proj2_incident r ?l`
      have "q = p" and "r = p" by (simp add: point_in_S_polar_is_tangent)+
      with `q \<noteq> r` show False by simp
    qed
    with `proj2_incident p ?l`
    show "\<not> (\<forall> l. proj2_incident p l \<longrightarrow> (\<exists> q r.
      q \<noteq> r \<and> q \<in> S \<and> r \<in> S \<and> proj2_incident q l \<and> proj2_incident r l))"
      by auto
  next
    assume "conic_sgn p \<noteq> 0"
    with `conic_sgn p \<ge> 0` have "conic_sgn p > 0" by simp
    hence "sgn (conic_sgn p) = 1" by simp
    hence "conic_sgn p = 1" by (simp add: sgn_conic_sgn)
    with outside_exists_line_not_intersect_S
    obtain l where "proj2_incident p l" and "\<forall> q. proj2_incident q l \<longrightarrow> q \<notin> S"
      by auto
    have "\<not> (\<exists> q r.
      q \<noteq> r \<and> q \<in> S \<and> r \<in> S \<and> proj2_incident q l \<and> proj2_incident r l)"
    proof
      assume "\<exists> q r.
        q \<noteq> r \<and> q \<in> S \<and> r \<in> S \<and> proj2_incident q l \<and> proj2_incident r l"
      then obtain q where "q \<in> S" and "proj2_incident q l" by auto
      from `proj2_incident q l` and `\<forall> q. proj2_incident q l \<longrightarrow> q \<notin> S`
      have "q \<notin> S" by simp
      with `q \<in> S` show False by simp
    qed
    with `proj2_incident p l`
    show "\<not> (\<forall> l. proj2_incident p l \<longrightarrow> (\<exists> q r.
      q \<noteq> r \<and> q \<in> S \<and> r \<in> S \<and> proj2_incident q l \<and> proj2_incident r l))"
      by auto
  qed
  with `\<forall> l. proj2_incident p l \<longrightarrow> (\<exists> q r.
    q \<noteq> r \<and> q \<in> S \<and> r \<in> S \<and> proj2_incident q l \<and> proj2_incident r l)`
  show False by simp
qed

lemma line_through_hyp2_pole_not_in_hyp2:
  assumes "a \<in> hyp2" and "proj2_incident a l"
  shows "pole l \<notin> hyp2"
proof -
  from assms and line_through_K2_intersect_S
  obtain p where "p \<in> S" and "proj2_incident p l" by auto

  from `proj2_incident p l`
  have "proj2_incident (pole l) (polar p)" by (rule incident_pole_polar)
  with `p \<in> S`
  show "pole l \<notin> hyp2"
    by (auto simp add: tangent_not_through_K2)
qed

lemma statement60_one_way:
  assumes "is_K2_isometry J" and "p \<in> K2"
  shows "apply_cltn2 p J \<in> K2" (is "?p' \<in> K2")
proof -
  let ?J' = "cltn2_inverse J"

  have "\<forall> l'. proj2_incident ?p' l' \<longrightarrow> (\<exists> q' r'.
    q' \<noteq> r' \<and> q' \<in> S \<and> r' \<in> S \<and> proj2_incident q' l' \<and> proj2_incident r' l')"
  proof
    fix l'
    let ?l = "apply_cltn2_line l' ?J'"
    show "proj2_incident ?p' l' \<longrightarrow> (\<exists> q' r'.
      q' \<noteq> r' \<and> q' \<in> S \<and> r' \<in> S \<and> proj2_incident q' l' \<and> proj2_incident r' l')"
    proof
      assume "proj2_incident ?p' l'"
      hence "proj2_incident p ?l"
        by (simp add: apply_cltn2_incident [of p l' ?J']
          cltn2.inv_inv [simplified])
      with `p \<in> K2` and line_through_K2_intersect_S_twice [of p ?l]
      obtain q and r where "q \<noteq> r" and "q \<in> S" and "r \<in> S"
        and "proj2_incident q ?l" and "proj2_incident r ?l"
        by auto
      let ?q' = "apply_cltn2 q J"
      let ?r' = "apply_cltn2 r J"
      from `q \<noteq> r` and apply_cltn2_injective [of q J r] have "?q' \<noteq> ?r'" by auto

      from `q \<in> S` and `r \<in> S` and `is_K2_isometry J`
      have "?q' \<in> S" and "?r' \<in> S" by (unfold is_K2_isometry_def) simp_all

      from `proj2_incident q ?l` and `proj2_incident r ?l`
      have "proj2_incident ?q' l'" and "proj2_incident ?r' l'"
        by (simp_all add: apply_cltn2_incident [of _ l' ?J']
          cltn2.inv_inv [simplified])
      with `?q' \<noteq> ?r'` and `?q' \<in> S` and `?r' \<in> S`
      show "\<exists> q' r'.
        q' \<noteq> r' \<and> q' \<in> S \<and> r' \<in> S \<and> proj2_incident q' l' \<and> proj2_incident r' l'"
        by auto
    qed
  qed
  thus "?p' \<in> K2" by (rule lines_through_intersect_S_twice_in_K2)
qed

lemma is_K2_isometry_hyp2_S:
  assumes "p \<in> hyp2 \<union> S" and "is_K2_isometry J"
  shows "apply_cltn2 p J \<in> hyp2 \<union> S"
proof cases
  assume "p \<in> hyp2"
  with `is_K2_isometry J`
  have "apply_cltn2 p J \<in> hyp2" by (rule statement60_one_way)
  thus "apply_cltn2 p J \<in> hyp2 \<union> S" ..
next
  assume "p \<notin> hyp2"
  with `p \<in> hyp2 \<union> S` have "p \<in> S" by simp
  with `is_K2_isometry J`
  have "apply_cltn2 p J \<in> S" by (unfold is_K2_isometry_def) simp
  thus "apply_cltn2 p J \<in> hyp2 \<union> S" ..
qed

lemma is_K2_isometry_z_non_zero:
  assumes "p \<in> hyp2 \<union> S" and "is_K2_isometry J"
  shows "z_non_zero (apply_cltn2 p J)"
proof -
  from `p \<in> hyp2 \<union> S` and `is_K2_isometry J`
  have "apply_cltn2 p J \<in> hyp2 \<union> S" by (rule is_K2_isometry_hyp2_S)
  thus "z_non_zero (apply_cltn2 p J)" by (rule hyp2_S_z_non_zero)
qed

lemma cart2_append1_apply_cltn2:
  assumes "p \<in> hyp2 \<union> S" and "is_K2_isometry J"
  shows "\<exists> k. k \<noteq> 0
  \<and> cart2_append1 p v* cltn2_rep J = k *\<^sub>R cart2_append1 (apply_cltn2 p J)"
proof -
  have "cart2_append1 p v* cltn2_rep J
    = (1 / (proj2_rep p)$3) *\<^sub>R (proj2_rep p v* cltn2_rep J)"
    by (unfold cart2_append1_def) (simp add: scalar_vector_matrix_assoc)

  from `p \<in> hyp2 \<union> S` have "(proj2_rep p)$3 \<noteq> 0" by (rule hyp2_S_z_non_zero)

  from apply_cltn2_imp_mult [of p J]
  obtain j where "j \<noteq> 0"
    and "proj2_rep p v* cltn2_rep J = j *\<^sub>R proj2_rep (apply_cltn2 p J)"
    by auto

  from `p \<in> hyp2 \<union> S` and `is_K2_isometry J`
  have "z_non_zero (apply_cltn2 p J)" by (rule is_K2_isometry_z_non_zero)
  hence "proj2_rep (apply_cltn2 p J)
    = (proj2_rep (apply_cltn2 p J))$3 *\<^sub>R cart2_append1 (apply_cltn2 p J)"
    by (rule proj2_rep_cart2_append1)

  let ?k = "1 / (proj2_rep p)$3 * j * (proj2_rep (apply_cltn2 p J))$3"
  from `(proj2_rep p)$3 \<noteq> 0` and `j \<noteq> 0`
    and `(proj2_rep (apply_cltn2 p J))$3 \<noteq> 0`
  have "?k \<noteq> 0" by simp

  from `cart2_append1 p v* cltn2_rep J
    = (1 / (proj2_rep p)$3) *\<^sub>R (proj2_rep p v* cltn2_rep J)`
    and `proj2_rep p v* cltn2_rep J = j *\<^sub>R proj2_rep (apply_cltn2 p J)`
  have "cart2_append1 p v* cltn2_rep J
    = (1 / (proj2_rep p)$ 3 * j) *\<^sub>R proj2_rep (apply_cltn2 p J)"
    by simp

  from `proj2_rep (apply_cltn2 p J)
    = (proj2_rep (apply_cltn2 p J))$3 *\<^sub>R cart2_append1 (apply_cltn2 p J)`
  have "(1 / (proj2_rep p)$3 * j) *\<^sub>R proj2_rep (apply_cltn2 p J)
    = (1 / (proj2_rep p)$3 * j) *\<^sub>R ((proj2_rep (apply_cltn2 p J))$3
    *\<^sub>R cart2_append1 (apply_cltn2 p J))"
    by simp
  with `cart2_append1 p v* cltn2_rep J
    = (1 / (proj2_rep p)$ 3 * j) *\<^sub>R proj2_rep (apply_cltn2 p J)`
  have "cart2_append1 p v* cltn2_rep J = ?k *\<^sub>R cart2_append1 (apply_cltn2 p J)"
    by simp
  with `?k \<noteq> 0`
  show "\<exists> k. k \<noteq> 0
    \<and> cart2_append1 p v* cltn2_rep J = k *\<^sub>R cart2_append1 (apply_cltn2 p J)"
    by (simp add: exI [of _ ?k])
qed

subsection {* The $K$-isometries form a group action *}

lemma hyp2_cltn2_id [simp]: "hyp2_cltn2 p cltn2_id = p"
  by (unfold hyp2_cltn2_def) (simp add: Rep_hyp2_inverse)

lemma apply_cltn2_Rep_hyp2:
  assumes "is_K2_isometry J"
  shows "apply_cltn2 (Rep_hyp2 p) J \<in> hyp2"
proof -
  from `is_K2_isometry J` and Rep_hyp2 [of p]
  show "apply_cltn2 (Rep_hyp2 p) J \<in> K2" by (rule statement60_one_way)
qed

lemma Rep_hyp2_cltn2:
  assumes "is_K2_isometry J"
  shows "Rep_hyp2 (hyp2_cltn2 p J) = apply_cltn2 (Rep_hyp2 p) J"
proof -
  from `is_K2_isometry J`
  have "apply_cltn2 (Rep_hyp2 p) J \<in> hyp2" by (rule apply_cltn2_Rep_hyp2)
  thus "Rep_hyp2 (hyp2_cltn2 p J) = apply_cltn2 (Rep_hyp2 p) J"
    by (unfold hyp2_cltn2_def) (rule Abs_hyp2_inverse)
qed

lemma hyp2_cltn2_compose:
  assumes "is_K2_isometry H"
  shows "hyp2_cltn2 (hyp2_cltn2 p H) J = hyp2_cltn2 p (cltn2_compose H J)"
proof -
  from `is_K2_isometry H`
  have "apply_cltn2 (Rep_hyp2 p) H \<in> hyp2" by (rule apply_cltn2_Rep_hyp2)
  thus "hyp2_cltn2 (hyp2_cltn2 p H) J = hyp2_cltn2 p (cltn2_compose H J)"
    by (unfold hyp2_cltn2_def) (simp add: Abs_hyp2_inverse apply_cltn2_compose)
qed

interpretation K2_isometry: action
  "(|carrier = Collect is_K2_isometry, mult = cltn2_compose, one = cltn2_id|)"
  hyp2_cltn2
proof
  let ?G =
    "(|carrier = Collect is_K2_isometry, mult = cltn2_compose, one = cltn2_id|)"
  fix p
  show "hyp2_cltn2 p \<one>\<^bsub>?G\<^esub> = p"
    by (unfold hyp2_cltn2_def) (simp add: Rep_hyp2_inverse)
  fix H J
  show "H \<in> carrier ?G \<and> J \<in> carrier ?G
    \<longrightarrow> hyp2_cltn2 (hyp2_cltn2 p H) J = hyp2_cltn2 p (H \<otimes>\<^bsub>?G\<^esub> J)"
    by (simp add: hyp2_cltn2_compose)
qed

subsection {* The Klein--Beltrami model satisfies Tarski's first three axioms *}

lemma three_in_S_tangent_intersection_no_3_Col:
  assumes "p \<in> S" and "q \<in> S" and "r \<in> S"
  and "p \<noteq> q" and "r \<notin> {p,q}"
  shows "proj2_no_3_Col {proj2_intersection (polar p) (polar q),r,p,q}"
  (is "proj2_no_3_Col {?s,r,p,q}")
proof -
  let ?T = "{?s,r,p,q}"

  from `p \<noteq> q` have "card {p,q} = 2" by simp
  with `r \<notin> {p,q}` have "card {r,p,q} = 3" by simp

  from `p \<in> S` and `q \<in> S` and `r \<in> S` have "{r,p,q} \<subseteq> S" by simp

  have "proj2_incident ?s (polar p)" and "proj2_incident ?s (polar q)"
    by (rule proj2_intersection_incident)+

  have "?s \<notin> S"
  proof
    assume "?s \<in> S"
    with `p \<in> S` and `proj2_incident ?s (polar p)`
      and `q \<in> S` and `proj2_incident ?s (polar q)`
    have "?s = p" and "?s = q" by (simp_all add: point_in_S_polar_is_tangent)
    hence "p = q" by simp
    with `p \<noteq> q` show False ..
  qed
  with `{r,p,q} \<subseteq> S` have "?s \<notin> {r,p,q}" by auto
  with `card {r,p,q} = 3` have "card {?s,r,p,q} = 4" by simp

  have "\<forall> t\<in>?T. \<not> proj2_set_Col (?T - {t})"
  proof standard+
    fix t
    assume "t \<in> ?T"
    assume "proj2_set_Col (?T - {t})"
    then obtain l where "\<forall> a \<in> (?T - {t}). proj2_incident a l"
      unfolding proj2_set_Col_def ..

    from `proj2_set_Col (?T - {t})`
    have "proj2_set_Col (S \<inter> (?T - {t}))"
      by (simp add: proj2_subset_Col [of "(S \<inter> (?T - {t}))" "?T - {t}"])
    hence "card (S \<inter> (?T - {t})) \<le> 2" by (simp add: card_line_intersect_S)

    show False
    proof cases
      assume "t = ?s"
      with `?s \<notin> {r,p,q}` have "?T - {t} = {r,p,q}" by simp
      with `{r,p,q} \<subseteq> S` have "S \<inter> (?T - {t}) = {r,p,q}" by simp
      with `card {r,p,q} = 3` and `card (S \<inter> (?T - {t})) \<le> 2` show False by simp
    next
      assume "t \<noteq> ?s"
      hence "?s \<in> ?T - {t}" by simp
      with `\<forall> a \<in> (?T - {t}). proj2_incident a l` have "proj2_incident ?s l" ..

      from `p \<noteq> q` have "{p,q} \<inter> ?T - {t} \<noteq> {}" by auto
      then obtain d where "d \<in> {p,q}" and "d \<in> ?T - {t}" by auto
      from `d \<in> ?T - {t}` and `\<forall> a \<in> (?T - {t}). proj2_incident a l`
      have "proj2_incident d l" by simp

      from `d \<in> {p,q}`
        and `proj2_incident ?s (polar p)`
        and `proj2_incident ?s (polar q)`
      have "proj2_incident ?s (polar d)" by auto

      from `d \<in> {p,q}` and `{r,p,q} \<subseteq> S` have "d \<in> S" by auto
      hence "proj2_incident d (polar d)" by (unfold incident_own_polar_in_S)

      from `d \<in> S` and `?s \<notin> S` have "d \<noteq> ?s" by auto
      with `proj2_incident ?s l`
        and `proj2_incident d l`
        and `proj2_incident ?s (polar d)`
        and `proj2_incident d (polar d)`
        and proj2_incident_unique
      have "l = polar d" by auto
      with `d \<in> S` and point_in_S_polar_is_tangent
      have "\<forall> a\<in>S. proj2_incident a l \<longrightarrow> a = d" by simp
      with `\<forall> a \<in> (?T - {t}). proj2_incident a l`
      have "S \<inter> (?T - {t}) \<subseteq> {d}" by auto
      with card_mono [of "{d}"] have "card (S \<inter> (?T - {t})) \<le> 1" by simp
      hence "card ((S \<inter> ?T) - {t}) \<le> 1" by (simp add: Int_Diff)

      have "S \<inter> ?T \<subseteq> insert t ((S \<inter> ?T) - {t})" by auto
      with card_suc_ge_insert [of t "(S \<inter> ?T) - {t}"]
        and card_mono [of "insert t ((S \<inter> ?T) - {t})" "S \<inter> ?T"]
      have "card (S \<inter> ?T) \<le> card ((S \<inter> ?T) - {t}) + 1" by simp
      with `card ((S \<inter> ?T) - {t}) \<le> 1` have "card (S \<inter> ?T) \<le> 2" by simp

      from `{r,p,q} \<subseteq> S` have "{r,p,q} \<subseteq> S \<inter> ?T" by simp
      with `card {r,p,q} = 3` and card_mono [of "S \<inter> ?T" "{r,p,q}"]
      have "card (S \<inter> ?T) \<ge> 3" by simp
      with `card (S \<inter> ?T) \<le> 2` show False by simp
    qed
  qed
  with `card ?T = 4` show "proj2_no_3_Col ?T" unfolding proj2_no_3_Col_def ..
qed

lemma statement65_special_case:
  assumes "p \<in> S" and "q \<in> S" and "r \<in> S" and "p \<noteq> q" and "r \<notin> {p,q}"
  shows "\<exists> J. is_K2_isometry J
  \<and> apply_cltn2 east J = p
  \<and> apply_cltn2 west J = q
  \<and> apply_cltn2 north J = r
  \<and> apply_cltn2 far_north J = proj2_intersection (polar p) (polar q)"
proof -
  let ?s = "proj2_intersection (polar p) (polar q)"
  let ?t = "vector [vector [?s,r,p,q], vector [far_north, north, east, west]]
    :: proj2^4^2"
  have "range (op $ (?t$1)) = {?s, r, p, q}"
    unfolding image_def
    by (auto simp add: UNIV_4 vector_4)
  with `p \<in> S` and `q \<in> S` and `r \<in> S` and `p \<noteq> q` and `r \<notin> {p,q}`
  have "proj2_no_3_Col (range (op $ (?t$1)))"
    by (simp add: three_in_S_tangent_intersection_no_3_Col)
  moreover have "range (op $ (?t$2)) = {far_north, north, east, west}"
    unfolding image_def
    by (auto simp add: UNIV_4 vector_4)
   with compass_in_S and east_west_distinct and north_not_east_or_west
     and east_west_tangents_far_north
     and three_in_S_tangent_intersection_no_3_Col [of east west north]
   have "proj2_no_3_Col (range (op $ (?t$2)))" by simp
   ultimately have "\<forall> i. proj2_no_3_Col (range (op $ (?t$i)))"
     by (simp add: forall_2)
   hence "\<exists> J. \<forall> j. apply_cltn2 (?t$0$j) J = ?t$1$j"
     by (rule statement53_existence)
   moreover have "0 = (2::2)" by simp
   ultimately obtain J where "\<forall> j. apply_cltn2 (?t$2$j) J = ?t$1$j" by auto
   hence "apply_cltn2 (?t$2$1) J = ?t$1$1"
     and "apply_cltn2 (?t$2$2) J = ?t$1$2"
     and "apply_cltn2 (?t$2$3) J = ?t$1$3"
     and "apply_cltn2 (?t$2$4) J = ?t$1$4"
     by simp_all
   hence "apply_cltn2 east J = p"
     and "apply_cltn2 west J = q"
     and "apply_cltn2 north J = r"
     and "apply_cltn2 far_north J = ?s"
     by (simp_all add: vector_2 vector_4)
   with compass_non_zero
   have "p = proj2_abs (vector [1,0,1] v* cltn2_rep J)"
     and "q = proj2_abs (vector [-1,0,1] v* cltn2_rep J)"
     and "r = proj2_abs (vector [0,1,1] v* cltn2_rep J)"
     and "?s = proj2_abs (vector [0,1,0] v* cltn2_rep J)"
     unfolding compass_defs and far_north_def
     by (simp_all add: apply_cltn2_left_abs)

   let ?N = "cltn2_rep J ** M ** transpose (cltn2_rep J)"
   from M_symmatrix have "symmatrix ?N" by (rule symmatrix_preserve)
   hence "?N$2$1 = ?N$1$2" and "?N$3$1 = ?N$1$3" and "?N$3$2 = ?N$2$3"
     unfolding symmatrix_def and transpose_def
     by (simp_all add: vec_eq_iff)

   from compass_non_zero and `apply_cltn2 east J = p` and `p \<in> S`
     and apply_cltn2_abs_in_S [of "vector [1,0,1]" J]
   have "(vector [1,0,1] :: real^3) \<bullet> (?N *v vector [1,0,1]) = 0"
     unfolding east_def
     by simp
   hence "?N$1$1 + ?N$1$3 + ?N$3$1 + ?N$3$3 = 0"
     unfolding inner_vec_def and matrix_vector_mult_def
     by (simp add: sum_3 vector_3)
   with `?N$3$1 = ?N$1$3` have "?N$1$1 + 2 * (?N$1$3) + ?N$3$3 = 0" by simp

   from compass_non_zero and `apply_cltn2 west J = q` and `q \<in> S`
     and apply_cltn2_abs_in_S [of "vector [-1,0,1]" J]
   have "(vector [-1,0,1] :: real^3) \<bullet> (?N *v vector [-1,0,1]) = 0"
     unfolding west_def
     by simp
   hence "?N$1$1 - ?N$1$3 - ?N$3$1 + ?N$3$3 = 0"
     unfolding inner_vec_def and matrix_vector_mult_def
     by (simp add: sum_3 vector_3)
   with `?N$3$1 = ?N$1$3` have "?N$1$1 - 2 * (?N$1$3) + ?N$3$3 = 0" by simp
   with `?N$1$1 + 2 * (?N$1$3) + ?N$3$3 = 0`
   have "?N$1$1 + 2 * (?N$1$3) + ?N$3$3 = ?N$1$1 - 2 * (?N$1$3) + ?N$3$3"
     by simp
   hence "?N$1$3 = 0" by simp
   with `?N$1$1 + 2 * (?N$1$3) + ?N$3$3 = 0` have "?N$3$3 = - (?N$1$1)" by simp

   from compass_non_zero and `apply_cltn2 north J = r` and `r \<in> S`
     and apply_cltn2_abs_in_S [of "vector [0,1,1]" J]
   have "(vector [0,1,1] :: real^3) \<bullet> (?N *v vector [0,1,1]) = 0"
     unfolding north_def
     by simp
   hence "?N$2$2 + ?N$2$3 + ?N$3$2 + ?N$3$3 = 0"
     unfolding inner_vec_def and matrix_vector_mult_def
     by (simp add: sum_3 vector_3)
   with `?N$3$2 = ?N$2$3` have "?N$2$2 + 2 * (?N$2$3) + ?N$3$3 = 0" by simp

   have "proj2_incident ?s (polar p)" and "proj2_incident ?s (polar q)"
     by (rule proj2_intersection_incident)+

   from compass_non_zero
   have "vector [1,0,1] v* cltn2_rep J \<noteq> 0"
     and "vector [-1,0,1] v* cltn2_rep J \<noteq> 0"
     and "vector [0,1,0] v* cltn2_rep J \<noteq> 0"
     by (simp_all add: non_zero_mult_rep_non_zero)
   from `vector [1,0,1] v* cltn2_rep J \<noteq> 0`
     and `vector [-1,0,1] v* cltn2_rep J \<noteq> 0`
     and `p = proj2_abs (vector [1,0,1] v* cltn2_rep J)`
     and `q = proj2_abs (vector [-1,0,1] v* cltn2_rep J)`
   have "polar p = proj2_line_abs (M *v (vector [1,0,1] v* cltn2_rep J))"
     and "polar q = proj2_line_abs (M *v (vector [-1,0,1] v* cltn2_rep J))"
     by (simp_all add: polar_abs)

   from `vector [1,0,1] v* cltn2_rep J \<noteq> 0`
     and `vector [-1,0,1] v* cltn2_rep J \<noteq> 0`
     and M_invertible
   have "M *v (vector [1,0,1] v* cltn2_rep J) \<noteq> 0"
     and "M *v (vector [-1,0,1] v* cltn2_rep J) \<noteq> 0"
     by (simp_all add: invertible_times_non_zero)
   with `vector [0,1,0] v* cltn2_rep J \<noteq> 0`
     and `polar p = proj2_line_abs (M *v (vector [1,0,1] v* cltn2_rep J))`
     and `polar q = proj2_line_abs (M *v (vector [-1,0,1] v* cltn2_rep J))`
     and `?s = proj2_abs (vector [0,1,0] v* cltn2_rep J)`
   have "proj2_incident ?s (polar p)
     \<longleftrightarrow> (vector [0,1,0] v* cltn2_rep J)
     \<bullet> (M *v (vector [1,0,1] v* cltn2_rep J)) = 0"
     and "proj2_incident ?s (polar q)
     \<longleftrightarrow> (vector [0,1,0] v* cltn2_rep J)
     \<bullet> (M *v (vector [-1,0,1] v* cltn2_rep J)) = 0"
     by (simp_all add: proj2_incident_abs)
   with `proj2_incident ?s (polar p)` and `proj2_incident ?s (polar q)`
   have "(vector [0,1,0] v* cltn2_rep J)
     \<bullet> (M *v (vector [1,0,1] v* cltn2_rep J)) = 0"
     and "(vector [0,1,0] v* cltn2_rep J)
     \<bullet> (M *v (vector [-1,0,1] v* cltn2_rep J)) = 0"
     by simp_all
   hence "vector [0,1,0] \<bullet> (?N *v vector [1,0,1]) = 0"
     and "vector [0,1,0] \<bullet> (?N *v vector [-1,0,1]) = 0"
     by (simp_all add: dot_lmul_matrix matrix_vector_mul_assoc [symmetric])
   hence "?N$2$1 + ?N$2$3 = 0" and "-(?N$2$1) + ?N$2$3 = 0"
     unfolding inner_vec_def and matrix_vector_mult_def
     by (simp_all add: sum_3 vector_3)
   hence "?N$2$1 + ?N$2$3 = -(?N$2$1) + ?N$2$3" by simp
   hence "?N$2$1 = 0" by simp
   with `?N$2$1 + ?N$2$3 = 0` have "?N$2$3 = 0" by simp
   with `?N$2$2 + 2 * (?N$2$3) + ?N$3$3 = 0` and `?N$3$3 = -(?N$1$1)`
   have "?N$2$2 = ?N$1$1" by simp
   with `?N$1$3 = 0` and `?N$2$1 = ?N$1$2` and `?N$1$3 = 0`
     and `?N$2$1 = 0` and `?N$2$2 = ?N$1$1` and `?N$2$3 = 0`
     and `?N$3$1 = ?N$1$3` and `?N$3$2 = ?N$2$3` and `?N$3$3 = -(?N$1$1)`
   have "?N = (?N$1$1) *\<^sub>R M"
     unfolding M_def
     by (simp add: vec_eq_iff vector_3 forall_3)

   have "invertible (cltn2_rep J)" by (rule cltn2_rep_invertible)
   with M_invertible
   have "invertible ?N" by (simp add: invertible_mult transpose_invertible)
   hence "?N \<noteq> 0" by (auto simp add: zero_not_invertible)
   with `?N = (?N$1$1) *\<^sub>R M` have "?N$1$1 \<noteq> 0" by auto
   with `?N = (?N$1$1) *\<^sub>R M`
   have "is_K2_isometry (cltn2_abs (cltn2_rep J))"
     by (simp add: J_M_J_transpose_K2_isometry)
   hence "is_K2_isometry J" by (simp add: cltn2_abs_rep)
   with `apply_cltn2 east J = p`
     and `apply_cltn2 west J = q`
     and `apply_cltn2 north J = r`
     and `apply_cltn2 far_north J = ?s`
   show "\<exists> J. is_K2_isometry J
     \<and> apply_cltn2 east J = p
     \<and> apply_cltn2 west J = q
     \<and> apply_cltn2 north J = r
     \<and> apply_cltn2 far_north J = ?s"
     by auto
qed

lemma statement66_existence:
  assumes "a1 \<in> K2" and "a2 \<in> K2" and "p1 \<in> S" and "p2 \<in> S"
  shows "\<exists> J. is_K2_isometry J \<and> apply_cltn2 a1 J = a2 \<and> apply_cltn2 p1 J = p2"
proof -
  let ?a = "vector [a1,a2] :: proj2^2"
  from `a1 \<in> K2` and `a2 \<in> K2` have "\<forall> i. ?a$i \<in> K2" by (simp add: forall_2)

  let ?p = "vector [p1,p2] :: proj2^2"
  from `p1 \<in> S` and `p2 \<in> S` have "\<forall> i. ?p$i \<in> S" by (simp add: forall_2)

  let ?l = "\<chi> i. proj2_line_through (?a$i) (?p$i)"
  have "\<forall> i. proj2_incident (?a$i) (?l$i)"
    by (simp add: proj2_line_through_incident)
  hence "proj2_incident (?a$1) (?l$1)" and "proj2_incident (?a$2) (?l$2)"
    by fast+

  have "\<forall> i. proj2_incident (?p$i) (?l$i)"
    by (simp add: proj2_line_through_incident)
  hence "proj2_incident (?p$1) (?l$1)" and "proj2_incident (?p$2) (?l$2)"
    by fast+

  let ?q = "\<chi> i. \<some> qi. qi \<noteq> ?p$i \<and> qi \<in> S \<and> proj2_incident qi (?l$i)"
  have "\<forall> i. ?q$i \<noteq> ?p$i \<and> ?q$i \<in> S \<and> proj2_incident (?q$i) (?l$i)"
  proof
    fix i
    from `\<forall> i. ?a$i \<in> K2` have "?a$i \<in> K2" ..

    from `\<forall> i. proj2_incident (?a$i) (?l$i)`
    have "proj2_incident (?a$i) (?l$i)" ..
    with `?a$i \<in> K2`
    have "\<exists> qi. qi \<noteq> ?p$i \<and> qi \<in> S \<and> proj2_incident qi (?l$i)"
      by (rule line_through_K2_intersect_S_again)
    with someI_ex [of "\<lambda> qi. qi \<noteq> ?p$i \<and> qi \<in> S \<and> proj2_incident qi (?l$i)"]
    show "?q$i \<noteq> ?p$i \<and> ?q$i \<in> S \<and> proj2_incident (?q$i) (?l$i)" by simp
  qed
  hence "?q$1 \<noteq> ?p$1" and "proj2_incident (?q$1) (?l$1)"
    and "proj2_incident (?q$2) (?l$2)"
    by fast+

  let ?r = "\<chi> i. proj2_intersection (polar (?q$i)) (polar (?p$i))"
  let ?m = "\<chi> i. proj2_line_through (?a$i) (?r$i)"
  have "\<forall> i. proj2_incident (?a$i) (?m$i)"
    by (simp add: proj2_line_through_incident)
  hence "proj2_incident (?a$1) (?m$1)" and "proj2_incident (?a$2) (?m$2)"
    by fast+

  have "\<forall> i. proj2_incident (?r$i) (?m$i)"
    by (simp add: proj2_line_through_incident)
  hence "proj2_incident (?r$1) (?m$1)" and "proj2_incident (?r$2) (?m$2)"
    by fast+

  let ?s = "\<chi> i. \<some> si. si \<noteq> ?r$i \<and> si \<in> S \<and> proj2_incident si (?m$i)"
  have "\<forall> i. ?s$i \<noteq> ?r$i \<and> ?s$i \<in> S \<and> proj2_incident (?s$i) (?m$i)"
  proof
    fix i
    from `\<forall> i. ?a$i \<in> K2` have "?a$i \<in> K2" ..

    from `\<forall> i. proj2_incident (?a$i) (?m$i)`
    have "proj2_incident (?a$i) (?m$i)" ..
    with `?a$i \<in> K2`
    have "\<exists> si. si \<noteq> ?r$i \<and> si \<in> S \<and> proj2_incident si (?m$i)"
      by (rule line_through_K2_intersect_S_again)
    with someI_ex [of "\<lambda> si. si \<noteq> ?r$i \<and> si \<in> S \<and> proj2_incident si (?m$i)"]
    show "?s$i \<noteq> ?r$i \<and> ?s$i \<in> S \<and> proj2_incident (?s$i) (?m$i)" by simp
  qed
  hence "?s$1 \<noteq> ?r$1" and "proj2_incident (?s$1) (?m$1)"
    and "proj2_incident (?s$2) (?m$2)"
    by fast+

  have "\<forall> i . \<forall> u. proj2_incident u (?m$i) \<longrightarrow> \<not> (u = ?p$i \<or> u = ?q$i)"
  proof standard+
    fix i :: 2
    fix u :: proj2
    assume "proj2_incident u (?m$i)"
    assume "u = ?p$i \<or> u = ?q$i"

    from `\<forall> i. ?p$i \<in> S` have "?p$i \<in> S" ..

    from `\<forall> i. ?q$i \<noteq> ?p$i \<and> ?q$i \<in> S \<and> proj2_incident (?q$i) (?l$i)`
    have "?q$i \<noteq> ?p$i" and "?q$i \<in> S"
      by simp_all

    from `?p$i \<in> S` and `?q$i \<in> S` and `u = ?p$i \<or> u = ?q$i`
    have "u \<in> S" by auto
    hence "proj2_incident u (polar u)"
      by (simp add: incident_own_polar_in_S)

    have "proj2_incident (?r$i) (polar (?p$i))"
      and "proj2_incident (?r$i) (polar (?q$i))"
      by (simp_all add: proj2_intersection_incident)
    with `u = ?p$i \<or> u = ?q$i`
    have "proj2_incident (?r$i) (polar u)" by auto

    from `\<forall> i. proj2_incident (?r$i) (?m$i)`
    have "proj2_incident (?r$i) (?m$i)" ..

    from `\<forall> i. proj2_incident (?a$i) (?m$i)`
    have "proj2_incident (?a$i) (?m$i)" ..

    from `\<forall> i. ?a$i \<in> K2` have "?a$i \<in> K2" ..

    have "u \<noteq> ?r$i"
    proof
      assume "u = ?r$i"
      with `proj2_incident (?r$i) (polar (?p$i))`
        and `proj2_incident (?r$i) (polar (?q$i))`
      have "proj2_incident u (polar (?p$i))"
        and "proj2_incident u (polar (?q$i))"
        by simp_all
      with `u \<in> S` and `?p$i \<in> S` and `?q$i \<in> S`
      have "u = ?p$i" and "u = ?q$i"
        by (simp_all add: point_in_S_polar_is_tangent)
      with `?q$i \<noteq> ?p$i` show False by simp
    qed
    with `proj2_incident (u) (polar u)`
      and `proj2_incident (?r$i) (polar u)`
      and `proj2_incident u (?m$i)`
      and `proj2_incident (?r$i) (?m$i)`
      and proj2_incident_unique
    have "?m$i = polar u" by auto
    with `proj2_incident (?a$i) (?m$i)`
    have "proj2_incident (?a$i) (polar u)" by simp
    with `u \<in> S` and `?a$i \<in> K2` and tangent_not_through_K2
    show False by simp
  qed

  let ?H = "\<chi> i. \<some> Hi. is_K2_isometry Hi
    \<and> apply_cltn2 east Hi = ?q$i
    \<and> apply_cltn2 west Hi = ?p$i
    \<and> apply_cltn2 north Hi = ?s$i
    \<and> apply_cltn2 far_north Hi = ?r$i"
  have "\<forall> i. is_K2_isometry (?H$i)
    \<and> apply_cltn2 east (?H$i) = ?q$i
    \<and> apply_cltn2 west (?H$i) = ?p$i
    \<and> apply_cltn2 north (?H$i) = ?s$i
    \<and> apply_cltn2 far_north (?H$i) = ?r$i"
  proof
    fix i :: 2
    from `\<forall> i. ?p$i \<in> S` have "?p$i \<in> S" ..

    from `\<forall> i. ?q$i \<noteq> ?p$i \<and> ?q$i \<in> S \<and> proj2_incident (?q$i) (?l$i)`
    have "?q$i \<noteq> ?p$i" and "?q$i \<in> S"
      by simp_all

    from `\<forall> i. ?s$i \<noteq> ?r$i \<and> ?s$i \<in> S \<and> proj2_incident (?s$i) (?m$i)`
    have "?s$i \<in> S" and "proj2_incident (?s$i) (?m$i)" by simp_all
    from `proj2_incident (?s$i) (?m$i)`
      and `\<forall> i. \<forall> u.  proj2_incident u (?m$i) \<longrightarrow> \<not> (u = ?p$i \<or> u = ?q$i)`
    have "?s$i \<notin> {?q$i, ?p$i}" by fast
    with `?q$i \<in> S` and `?p$i \<in> S` and `?s$i \<in> S` and `?q$i \<noteq> ?p$i`
    have "\<exists> Hi. is_K2_isometry Hi
      \<and> apply_cltn2 east Hi = ?q$i
      \<and> apply_cltn2 west Hi = ?p$i
      \<and> apply_cltn2 north Hi = ?s$i
      \<and> apply_cltn2 far_north Hi = ?r$i"
      by (simp add: statement65_special_case)
    with someI_ex [of "\<lambda> Hi. is_K2_isometry Hi
      \<and> apply_cltn2 east Hi = ?q$i
      \<and> apply_cltn2 west Hi = ?p$i
      \<and> apply_cltn2 north Hi = ?s$i
      \<and> apply_cltn2 far_north Hi = ?r$i"]
    show "is_K2_isometry (?H$i)
      \<and> apply_cltn2 east (?H$i) = ?q$i
      \<and> apply_cltn2 west (?H$i) = ?p$i
      \<and> apply_cltn2 north (?H$i) = ?s$i
      \<and> apply_cltn2 far_north (?H$i) = ?r$i"
      by simp
  qed
  hence "is_K2_isometry (?H$1)"
    and "apply_cltn2 east (?H$1) = ?q$1"
    and "apply_cltn2 west (?H$1) = ?p$1"
    and "apply_cltn2 north (?H$1) = ?s$1"
    and "apply_cltn2 far_north (?H$1) = ?r$1"
    and  "is_K2_isometry (?H$2)"
    and "apply_cltn2 east (?H$2) = ?q$2"
    and "apply_cltn2 west (?H$2) = ?p$2"
    and "apply_cltn2 north (?H$2) = ?s$2"
    and "apply_cltn2 far_north (?H$2) = ?r$2"
    by fast+

  let ?J = "cltn2_compose (cltn2_inverse (?H$1)) (?H$2)"
  from `is_K2_isometry (?H$1)` and `is_K2_isometry (?H$2)`
  have "is_K2_isometry ?J"
    by (simp only: cltn2_inverse_is_K2_isometry cltn2_compose_is_K2_isometry)

  from `apply_cltn2 west (?H$1) = ?p$1`
  have "apply_cltn2 p1 (cltn2_inverse (?H$1)) = west"
    by (simp add: cltn2.act_inv_iff [simplified])
  with `apply_cltn2 west (?H$2) = ?p$2`
  have "apply_cltn2 p1 ?J = p2"
    by (simp add: cltn2.act_act [simplified, symmetric])

  from `apply_cltn2 east (?H$1) = ?q$1`
  have "apply_cltn2 (?q$1) (cltn2_inverse (?H$1)) = east"
    by (simp add: cltn2.act_inv_iff [simplified])
  with `apply_cltn2 east (?H$2) = ?q$2`
  have "apply_cltn2 (?q$1) ?J = ?q$2"
    by (simp add: cltn2.act_act [simplified, symmetric])
  with `?q$1 \<noteq> ?p$1` and `apply_cltn2 p1 ?J = p2`
    and `proj2_incident (?p$1) (?l$1)`
    and `proj2_incident (?q$1) (?l$1)`
    and `proj2_incident (?p$2) (?l$2)`
    and `proj2_incident (?q$2) (?l$2)`
  have "apply_cltn2_line (?l$1) ?J = (?l$2)"
    by (simp add: apply_cltn2_line_unique)
  moreover from `proj2_incident (?a$1) (?l$1)`
  have "proj2_incident (apply_cltn2 (?a$1) ?J) (apply_cltn2_line (?l$1) ?J)"
    by simp
  ultimately have "proj2_incident (apply_cltn2 (?a$1) ?J) (?l$2)" by simp

  from `apply_cltn2 north (?H$1) = ?s$1`
  have "apply_cltn2 (?s$1) (cltn2_inverse (?H$1)) = north"
    by (simp add: cltn2.act_inv_iff [simplified])
  with `apply_cltn2 north (?H$2) = ?s$2`
  have "apply_cltn2 (?s$1) ?J = ?s$2"
    by (simp add: cltn2.act_act [simplified, symmetric])

  from `apply_cltn2 far_north (?H$1) = ?r$1`
  have "apply_cltn2 (?r$1) (cltn2_inverse (?H$1)) = far_north"
    by (simp add: cltn2.act_inv_iff [simplified])
  with `apply_cltn2 far_north (?H$2) = ?r$2`
  have "apply_cltn2 (?r$1) ?J = ?r$2"
    by (simp add: cltn2.act_act [simplified, symmetric])
  with `?s$1 \<noteq> ?r$1` and `apply_cltn2 (?s$1) ?J = (?s$2)`
    and `proj2_incident (?r$1) (?m$1)`
    and `proj2_incident (?s$1) (?m$1)`
    and `proj2_incident (?r$2) (?m$2)`
    and `proj2_incident (?s$2) (?m$2)`
  have "apply_cltn2_line (?m$1) ?J = (?m$2)"
    by (simp add: apply_cltn2_line_unique)
  moreover from `proj2_incident (?a$1) (?m$1)`
  have "proj2_incident (apply_cltn2 (?a$1) ?J) (apply_cltn2_line (?m$1) ?J)"
    by simp
  ultimately have "proj2_incident (apply_cltn2 (?a$1) ?J) (?m$2)" by simp

  from `\<forall> i. \<forall> u. proj2_incident u (?m$i) \<longrightarrow> \<not> (u = ?p$i \<or> u = ?q$i)`
  have "\<not> proj2_incident (?p$2) (?m$2)" by fast
  with `proj2_incident (?p$2) (?l$2)` have "?m$2 \<noteq> ?l$2" by auto
  with `proj2_incident (?a$2) (?l$2)`
    and `proj2_incident (?a$2) (?m$2)`
    and `proj2_incident (apply_cltn2 (?a$1) ?J) (?l$2)`
    and `proj2_incident (apply_cltn2 (?a$1) ?J) (?m$2)`
    and proj2_incident_unique
  have "apply_cltn2 a1 ?J = a2" by auto
  with `is_K2_isometry ?J` and `apply_cltn2 p1 ?J = p2`
  show "\<exists> J. is_K2_isometry J \<and> apply_cltn2 a1 J = a2 \<and> apply_cltn2 p1 J = p2"
    by auto
qed

lemma K2_isometry_swap:
  assumes "a \<in> hyp2" and "b \<in> hyp2"
  shows "\<exists> J. is_K2_isometry J \<and> apply_cltn2 a J = b \<and> apply_cltn2 b J = a"
proof -
  from `a \<in> hyp2` and `b \<in> hyp2`
  have "a \<in> K2" and "b \<in> K2" by simp_all

  let ?l = "proj2_line_through a b"
  have "proj2_incident a ?l" and "proj2_incident b ?l"
    by (rule proj2_line_through_incident)+
  from `a \<in> K2` and `proj2_incident a ?l`
    and line_through_K2_intersect_S_exactly_twice [of a ?l]
  obtain p and q where "p \<noteq> q"
    and "p \<in> S" and "q \<in> S"
    and "proj2_incident p ?l" and "proj2_incident q ?l"
    and "\<forall> r\<in>S. proj2_incident r ?l \<longrightarrow> r = p \<or> r = q"
    by auto
  from `a \<in> K2` and `b \<in> K2` and `p \<in> S` and `q \<in> S`
    and statement66_existence [of a b p q]
  obtain J where "is_K2_isometry J" and "apply_cltn2 a J = b"
    and "apply_cltn2 p J = q"
    by auto
  from `apply_cltn2 a J = b` and `apply_cltn2 p J = q`
    and `proj2_incident b ?l` and `proj2_incident q ?l`
  have "proj2_incident (apply_cltn2 a J) ?l"
    and "proj2_incident (apply_cltn2 p J) ?l"
    by simp_all

  from `a \<in> K2` and `p \<in> S` have "a \<noteq> p"
    unfolding S_def and K2_def
    by auto
  with `proj2_incident a ?l`
    and `proj2_incident p ?l`
    and `proj2_incident (apply_cltn2 a J) ?l`
    and `proj2_incident (apply_cltn2 p J) ?l`
  have "apply_cltn2_line ?l J = ?l" by (simp add: apply_cltn2_line_unique)
  with `proj2_incident q ?l` and apply_cltn2_preserve_incident [of q J ?l]
  have "proj2_incident (apply_cltn2 q J) ?l" by simp

  from `q \<in> S` and `is_K2_isometry J`
  have "apply_cltn2 q J \<in> S" by (unfold is_K2_isometry_def) simp
  with `proj2_incident (apply_cltn2 q J) ?l`
    and `\<forall> r\<in>S. proj2_incident r ?l \<longrightarrow> r = p \<or> r = q`
  have "apply_cltn2 q J = p \<or> apply_cltn2 q J = q" by simp

  have "apply_cltn2 q J \<noteq> q"
  proof
    assume "apply_cltn2 q J = q"
    with `apply_cltn2 p J = q`
    have "apply_cltn2 p J = apply_cltn2 q J" by simp
    hence "p = q" by (rule apply_cltn2_injective [of p J q])
    with `p \<noteq> q` show False ..
  qed
  with `apply_cltn2 q J = p \<or> apply_cltn2 q J = q`
  have "apply_cltn2 q J = p" by simp
  with `p \<noteq> q`
    and `apply_cltn2 p J = q`
    and `proj2_incident p ?l`
    and `proj2_incident q ?l`
    and `proj2_incident a ?l`
    and statement55
  have "apply_cltn2 (apply_cltn2 a J) J = a" by simp
  with `apply_cltn2 a J = b` have "apply_cltn2 b J = a" by simp
  with `is_K2_isometry J` and `apply_cltn2 a J = b`
  show "\<exists> J. is_K2_isometry J \<and> apply_cltn2 a J = b \<and> apply_cltn2 b J = a"
    by (simp add: exI [of _ J])
qed

theorem hyp2_axiom1: "\<forall> a b. a b \<congruent>\<^sub>K b a"
proof standard+
  fix a b
  let ?a' = "Rep_hyp2 a"
  let ?b' = "Rep_hyp2 b"
  from Rep_hyp2 and K2_isometry_swap [of ?a' ?b']
  obtain J where "is_K2_isometry J" and "apply_cltn2 ?a' J = ?b'"
    and "apply_cltn2 ?b' J = ?a'"
    by auto

  from `apply_cltn2 ?a' J = ?b'` and `apply_cltn2 ?b' J = ?a'`
  have "hyp2_cltn2 a J = b" and "hyp2_cltn2 b J = a"
    unfolding hyp2_cltn2_def by (simp_all add: Rep_hyp2_inverse)
  with `is_K2_isometry J`
  show "a b \<congruent>\<^sub>K b a"
    by (unfold real_hyp2_C_def) (simp add: exI [of _ J])
qed

theorem hyp2_axiom2: "\<forall> a b p q r s. a b \<congruent>\<^sub>K p q \<and> a b \<congruent>\<^sub>K r s \<longrightarrow> p q \<congruent>\<^sub>K r s"
proof standard+
  fix a b p q r s
  assume "a b \<congruent>\<^sub>K p q \<and> a b \<congruent>\<^sub>K r s"
  then obtain G and H where "is_K2_isometry G" and "is_K2_isometry H"
    and "hyp2_cltn2 a G = p" and "hyp2_cltn2 b G = q"
   and "hyp2_cltn2 a H = r" and "hyp2_cltn2 b H = s"
    by (unfold real_hyp2_C_def) auto
  let ?J = "cltn2_compose (cltn2_inverse G) H"
  from `is_K2_isometry G` have "is_K2_isometry (cltn2_inverse G)"
    by (rule cltn2_inverse_is_K2_isometry)
  with `is_K2_isometry H`
  have "is_K2_isometry ?J" by (simp only: cltn2_compose_is_K2_isometry)

  from `is_K2_isometry G` and `hyp2_cltn2 a G = p` and `hyp2_cltn2 b G = q`
    and K2_isometry.act_inv_iff
  have "hyp2_cltn2 p (cltn2_inverse G) = a"
    and "hyp2_cltn2 q (cltn2_inverse G) = b"
    by simp_all
  with `hyp2_cltn2 a H = r` and `hyp2_cltn2 b H = s`
    and `is_K2_isometry (cltn2_inverse G)` and `is_K2_isometry H`
    and K2_isometry.act_act [symmetric]
  have "hyp2_cltn2 p ?J = r" and "hyp2_cltn2 q ?J = s" by simp_all
  with `is_K2_isometry ?J`
  show "p q \<congruent>\<^sub>K r s"
    by (unfold real_hyp2_C_def) (simp add: exI [of _ ?J])
qed

theorem hyp2_axiom3: "\<forall> a b c. a b \<congruent>\<^sub>K c c \<longrightarrow> a = b"
proof standard+
  fix a b c
  assume "a b \<congruent>\<^sub>K c c"
  then obtain J where "is_K2_isometry J"
    and "hyp2_cltn2 a J = c" and "hyp2_cltn2 b J = c"
    by (unfold real_hyp2_C_def) auto
  from `hyp2_cltn2 a J = c` and `hyp2_cltn2 b J = c`
  have "hyp2_cltn2 a J = hyp2_cltn2 b J" by simp

  from `is_K2_isometry J`
  have "apply_cltn2 (Rep_hyp2 a) J \<in> hyp2"
    and "apply_cltn2 (Rep_hyp2 b) J \<in> hyp2"
    by (rule apply_cltn2_Rep_hyp2)+
  with `hyp2_cltn2 a J = hyp2_cltn2 b J`
  have "apply_cltn2 (Rep_hyp2 a) J = apply_cltn2 (Rep_hyp2 b) J"
    by (unfold hyp2_cltn2_def) (simp add: Abs_hyp2_inject)
  hence "Rep_hyp2 a = Rep_hyp2 b" by (rule apply_cltn2_injective)
  thus "a = b" by (simp add: Rep_hyp2_inject)
qed

interpretation hyp2: tarski_first3 real_hyp2_C
  using hyp2_axiom1 and hyp2_axiom2 and hyp2_axiom3
  by unfold_locales

subsection {* Some lemmas about betweenness *}

lemma S_at_edge:
  assumes "p \<in> S" and "q \<in> hyp2 \<union> S" and "r \<in> hyp2 \<union> S" and "proj2_Col p q r"
  shows "B\<^sub>\<real> (cart2_pt p) (cart2_pt q) (cart2_pt r)
  \<or> B\<^sub>\<real> (cart2_pt p) (cart2_pt r) (cart2_pt q)"
  (is "B\<^sub>\<real> ?cp ?cq ?cr \<or> _")
proof -
  from `p \<in> S` and `q \<in> hyp2 \<union> S` and `r \<in> hyp2 \<union> S`
  have "z_non_zero p" and "z_non_zero q" and "z_non_zero r"
    by (simp_all add: hyp2_S_z_non_zero)
  with `proj2_Col p q r`
  have "real_euclid.Col ?cp ?cq ?cr" by (simp add: proj2_Col_iff_euclid_cart2)

  with `z_non_zero p` and `z_non_zero q` and `z_non_zero r`
  have "proj2_pt ?cp = p" and "proj2_pt ?cq = q" and "proj2_pt ?cr = r"
    by (simp_all add: proj2_cart2)
  from `proj2_pt ?cp = p` and `p \<in> S`
  have "norm ?cp = 1" by (simp add: norm_eq_1_iff_in_S)

  from `proj2_pt ?cq = q` and `proj2_pt ?cr = r`
    and `q \<in> hyp2 \<union> S` and `r \<in> hyp2 \<union> S`
  have "norm ?cq \<le> 1" and "norm ?cr \<le> 1"
    by (simp_all add: norm_le_1_iff_in_hyp2_S)

  show "B\<^sub>\<real> ?cp ?cq ?cr \<or> B\<^sub>\<real> ?cp ?cr ?cq"
  proof cases
    assume "B\<^sub>\<real> ?cr ?cp ?cq"
    then obtain k where "k \<ge> 0" and "k \<le> 1"
      and "?cp - ?cr = k *\<^sub>R (?cq - ?cr)"
      by (unfold real_euclid_B_def) auto
    from `?cp - ?cr = k *\<^sub>R (?cq - ?cr)`
    have "?cp = k *\<^sub>R ?cq + (1 - k) *\<^sub>R ?cr" by (simp add: algebra_simps)
    with `norm ?cp = 1` have "norm (k *\<^sub>R ?cq + (1 - k) *\<^sub>R ?cr) = 1" by simp
    with norm_triangle_ineq [of "k *\<^sub>R ?cq" "(1 - k) *\<^sub>R ?cr"]
    have "norm (k *\<^sub>R ?cq) + norm ((1 - k) *\<^sub>R ?cr) \<ge> 1" by simp

    from `k \<ge> 0` and `k \<le> 1`
    have "norm (k *\<^sub>R ?cq) + norm ((1 - k) *\<^sub>R ?cr)
      = k * norm ?cq + (1 - k) * norm ?cr"
      by simp
    with `norm (k *\<^sub>R ?cq) + norm ((1 - k) *\<^sub>R ?cr) \<ge> 1`
    have "k * norm ?cq + (1 - k) * norm ?cr \<ge> 1" by simp

    from `norm ?cq \<le> 1` and `k \<ge> 0` and mult_mono [of k k "norm ?cq" 1]
    have "k * norm ?cq \<le> k" by simp

    from `norm ?cr \<le> 1` and `k \<le> 1`
      and mult_mono [of "1 - k" "1 - k" "norm ?cr" 1]
    have "(1 - k) * norm ?cr \<le> 1 - k" by simp
    with `k * norm ?cq \<le> k`
    have "k * norm ?cq + (1 - k) * norm ?cr \<le> 1" by simp
    with `k * norm ?cq + (1 - k) * norm ?cr \<ge> 1`
    have "k * norm ?cq + (1 - k) * norm ?cr = 1" by simp
    with `k * norm ?cq \<le> k` have "(1 - k) * norm ?cr \<ge> 1 - k" by simp
    with `(1 - k) * norm ?cr \<le> 1 - k` have "(1 - k) * norm ?cr = 1 - k" by simp
    with `k * norm ?cq + (1 - k) * norm ?cr = 1` have "k * norm ?cq = k" by simp

    have "?cp = ?cq \<or> ?cq = ?cr \<or> ?cr = ?cp"
    proof cases
      assume "k = 0 \<or> k = 1"
      with `?cp = k *\<^sub>R ?cq + (1 - k) *\<^sub>R ?cr`
      show "?cp = ?cq \<or> ?cq = ?cr \<or> ?cr = ?cp" by auto
    next
      assume "\<not> (k = 0 \<or> k = 1)"
      hence "k \<noteq> 0" and "k \<noteq> 1" by simp_all
      with `k * norm ?cq = k` and `(1 - k) * norm ?cr = 1 - k`
      have "norm ?cq = 1" and "norm ?cr = 1" by simp_all
      with `proj2_pt ?cq = q` and `proj2_pt ?cr = r`
      have "q \<in> S" and "r \<in> S" by (simp_all add: norm_eq_1_iff_in_S)
      with `p \<in> S` have "{p,q,r} \<subseteq> S" by simp

      from `proj2_Col p q r`
      have "proj2_set_Col {p,q,r}" by (simp add: proj2_Col_iff_set_Col)
      with `{p,q,r} \<subseteq> S` have "card {p,q,r} \<le> 2" by (rule card_line_intersect_S)

      have "p = q \<or> q = r \<or> r = p"
      proof (rule ccontr)
        assume "\<not> (p = q \<or> q = r \<or> r = p)"
        hence "p \<noteq> q" and "q \<noteq> r" and "r \<noteq> p" by simp_all
        from `q \<noteq> r` have "card {q,r} = 2" by simp
        with `p \<noteq> q` and `r \<noteq> p` have "card {p,q,r} = 3" by simp
        with `card {p,q,r} \<le> 2` show False by simp
      qed
      thus "?cp = ?cq \<or> ?cq = ?cr \<or> ?cr = ?cp" by auto
    qed
    thus "B\<^sub>\<real> ?cp ?cq ?cr \<or> B\<^sub>\<real> ?cp ?cr ?cq"
      by (auto simp add: real_euclid.th3_1 real_euclid.th3_2)
  next
    assume "\<not> B\<^sub>\<real> ?cr ?cp ?cq"
    with `real_euclid.Col ?cp ?cq ?cr`
    show "B\<^sub>\<real> ?cp ?cq ?cr \<or> B\<^sub>\<real> ?cp ?cr ?cq"
      unfolding real_euclid.Col_def
      by (auto simp add: real_euclid.th3_1 real_euclid.th3_2)
  qed
qed

lemma hyp2_in_middle:
  assumes "p \<in> S" and "q \<in> S" and "r \<in> hyp2 \<union> S" and "proj2_Col p q r"
  and "p \<noteq> q"
  shows "B\<^sub>\<real> (cart2_pt p) (cart2_pt r) (cart2_pt q)" (is "B\<^sub>\<real> ?cp ?cr ?cq")
proof (rule ccontr)
  assume "\<not> B\<^sub>\<real> ?cp ?cr ?cq"
  hence "\<not> B\<^sub>\<real> ?cq ?cr ?cp"
    by (auto simp add: real_euclid.th3_2 [of ?cq ?cr ?cp])

  from `p \<in> S` and `q \<in> S` and `r \<in> hyp2 \<union> S` and `proj2_Col p q r`
  have "B\<^sub>\<real> ?cp ?cq ?cr \<or> B\<^sub>\<real> ?cp ?cr ?cq" by (simp add: S_at_edge)
  with `\<not> B\<^sub>\<real> ?cp ?cr ?cq` have "B\<^sub>\<real> ?cp ?cq ?cr" by simp

  from `proj2_Col p q r` and proj2_Col_permute have "proj2_Col q p r" by fast
  with `q \<in> S` and `p \<in> S` and `r \<in> hyp2 \<union> S`
  have "B\<^sub>\<real> ?cq ?cp ?cr \<or> B\<^sub>\<real> ?cq ?cr ?cp" by (simp add: S_at_edge)
  with `\<not> B\<^sub>\<real> ?cq ?cr ?cp` have "B\<^sub>\<real> ?cq ?cp ?cr" by simp
  with `B\<^sub>\<real> ?cp ?cq ?cr` have "?cp = ?cq" by (rule real_euclid.th3_4)
  hence "proj2_pt ?cp = proj2_pt ?cq" by simp

  from `p \<in> S` and `q \<in> S`
  have "z_non_zero p" and "z_non_zero q" by (simp_all add: hyp2_S_z_non_zero)
  hence "proj2_pt ?cp = p" and "proj2_pt ?cq = q" by (simp_all add: proj2_cart2)
  with `proj2_pt ?cp = proj2_pt ?cq` have "p = q" by simp
  with `p \<noteq> q` show False ..
qed

lemma hyp2_incident_in_middle:
  assumes "p \<noteq> q" and "p \<in> S" and "q \<in> S" and "a \<in> hyp2 \<union> S"
  and "proj2_incident p l" and "proj2_incident q l" and "proj2_incident a l"
  shows "B\<^sub>\<real> (cart2_pt p) (cart2_pt a) (cart2_pt q)"
proof -
  from `proj2_incident p l` and `proj2_incident q l` and `proj2_incident a l`
  have "proj2_Col p q a" by (rule proj2_incident_Col)
  from `p \<in> S` and `q \<in> S` and `a \<in> hyp2 \<union> S` and this and `p \<noteq> q`
  show "B\<^sub>\<real> (cart2_pt p) (cart2_pt a) (cart2_pt q)"
    by (rule hyp2_in_middle)
qed

lemma extend_to_S:
  assumes "p \<in> hyp2 \<union> S" and "q \<in> hyp2 \<union> S"
  shows "\<exists> r\<in>S. B\<^sub>\<real> (cart2_pt p) (cart2_pt q) (cart2_pt r)"
  (is "\<exists> r\<in>S. B\<^sub>\<real> ?cp ?cq (cart2_pt r)")
proof cases
  assume "q \<in> S"

  have "B\<^sub>\<real> ?cp ?cq ?cq" by (rule real_euclid.th3_1)
  with `q \<in> S` show "\<exists> r\<in>S. B\<^sub>\<real> ?cp ?cq (cart2_pt r)" by auto
next
  assume "q \<notin> S"
  with `q \<in> hyp2 \<union> S` have "q \<in> K2" by simp

  let ?l = "proj2_line_through p q"
  have "proj2_incident p ?l" and "proj2_incident q ?l"
    by (rule proj2_line_through_incident)+
  from `q \<in> K2` and `proj2_incident q ?l`
    and line_through_K2_intersect_S_twice [of q ?l]
  obtain s and t where "s \<noteq> t" and "s \<in> S" and "t \<in> S"
    and "proj2_incident s ?l" and "proj2_incident t ?l"
    by auto
  let ?cs = "cart2_pt s"
  let ?ct = "cart2_pt t"

  from `proj2_incident s ?l`
    and `proj2_incident t ?l`
    and `proj2_incident p ?l`
    and `proj2_incident q ?l`
  have "proj2_Col s p q" and "proj2_Col t p q" and "proj2_Col s t q"
    by (simp_all add: proj2_incident_Col)
  from `proj2_Col s p q` and `proj2_Col t p q`
    and `s \<in> S` and `t \<in> S` and `p \<in> hyp2 \<union> S` and `q \<in> hyp2 \<union> S`
  have "B\<^sub>\<real> ?cs ?cp ?cq \<or> B\<^sub>\<real> ?cs ?cq ?cp" and "B\<^sub>\<real> ?ct ?cp ?cq \<or> B\<^sub>\<real> ?ct ?cq ?cp"
    by (simp_all add: S_at_edge)
  with real_euclid.th3_2
  have "B\<^sub>\<real> ?cq ?cp ?cs \<or> B\<^sub>\<real> ?cp ?cq ?cs" and "B\<^sub>\<real> ?cq ?cp ?ct \<or> B\<^sub>\<real> ?cp ?cq ?ct"
    by fast+

  from `s \<in> S` and `t \<in> S` and `q \<in> hyp2 \<union> S` and `proj2_Col s t q` and `s \<noteq> t`
  have "B\<^sub>\<real> ?cs ?cq ?ct" by (rule hyp2_in_middle)
  hence "B\<^sub>\<real> ?ct ?cq ?cs" by (rule real_euclid.th3_2)

  have "B\<^sub>\<real> ?cp ?cq ?cs \<or> B\<^sub>\<real> ?cp ?cq ?ct"
  proof (rule ccontr)
    assume "\<not> (B\<^sub>\<real> ?cp ?cq ?cs \<or> B\<^sub>\<real> ?cp ?cq ?ct)"
    hence "\<not> B\<^sub>\<real> ?cp ?cq ?cs" and "\<not> B\<^sub>\<real> ?cp ?cq ?ct" by simp_all
    with `B\<^sub>\<real> ?cq ?cp ?cs \<or> B\<^sub>\<real> ?cp ?cq ?cs`
      and `B\<^sub>\<real> ?cq ?cp ?ct \<or> B\<^sub>\<real> ?cp ?cq ?ct`
    have "B\<^sub>\<real> ?cq ?cp ?cs" and "B\<^sub>\<real> ?cq ?cp ?ct" by simp_all
    from `\<not> B\<^sub>\<real> ?cp ?cq ?cs` and `B\<^sub>\<real> ?cq ?cp ?cs` have "?cp \<noteq> ?cq" by auto
    with `B\<^sub>\<real> ?cq ?cp ?cs` and `B\<^sub>\<real> ?cq ?cp ?ct`
    have "B\<^sub>\<real> ?cq ?cs ?ct \<or> B\<^sub>\<real> ?cq ?ct ?cs"
      by (simp add: real_euclid_th5_1 [of ?cq ?cp ?cs ?ct])
    with `B\<^sub>\<real> ?cs ?cq ?ct` and `B\<^sub>\<real> ?ct ?cq ?cs`
    have "?cq = ?cs \<or> ?cq = ?ct" by (auto simp add: real_euclid.th3_4)
    with `q \<in> hyp2 \<union> S` and `s \<in> S` and `t \<in> S`
    have "q = s \<or> q = t" by (auto simp add: hyp2_S_cart2_inj)
    with `s \<in> S` and `t \<in> S` have "q \<in> S" by auto
    with `q \<notin> S` show False ..
  qed
  with `s \<in> S` and `t \<in> S` show "\<exists> r\<in>S. B\<^sub>\<real> ?cp ?cq (cart2_pt r)" by auto
qed

definition endpoint_in_S :: "proj2 \<Rightarrow> proj2 \<Rightarrow> proj2" where
  "endpoint_in_S a b
  \<equiv> \<some> p. p\<in>S \<and> B\<^sub>\<real> (cart2_pt a) (cart2_pt b) (cart2_pt p)"

lemma endpoint_in_S:
  assumes "a \<in> hyp2 \<union> S" and "b \<in> hyp2 \<union> S"
  shows "endpoint_in_S a b \<in> S" (is "?p \<in> S")
  and "B\<^sub>\<real> (cart2_pt a) (cart2_pt b) (cart2_pt (endpoint_in_S a b))"
  (is "B\<^sub>\<real> ?ca ?cb ?cp")
proof -
  from `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S` and extend_to_S
  have "\<exists> p. p \<in> S \<and> B\<^sub>\<real> ?ca ?cb (cart2_pt p)" by auto
  hence "?p \<in> S \<and> B\<^sub>\<real> ?ca ?cb ?cp"
    by (unfold endpoint_in_S_def) (rule someI_ex)
  thus "?p \<in> S" and "B\<^sub>\<real> ?ca ?cb ?cp" by simp_all
qed

lemma endpoint_in_S_swap:
  assumes "a \<noteq> b" and "a \<in> hyp2 \<union> S" and "b \<in> hyp2 \<union> S"
  shows "endpoint_in_S a b \<noteq> endpoint_in_S b a" (is "?p \<noteq> ?q")
proof
  let ?ca = "cart2_pt a"
  let ?cb = "cart2_pt b"
  let ?cp = "cart2_pt ?p"
  let ?cq = "cart2_pt ?q"
  from `a \<noteq> b` and `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S`
  have "B\<^sub>\<real> ?ca ?cb ?cp" and "B\<^sub>\<real> ?cb ?ca ?cq"
    by (simp_all add: endpoint_in_S)

  assume "?p = ?q"
  with `B\<^sub>\<real> ?cb ?ca ?cq` have "B\<^sub>\<real> ?cb ?ca ?cp" by simp
  with `B\<^sub>\<real> ?ca ?cb ?cp` have "?ca = ?cb" by (rule real_euclid.th3_4)
  with `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S` have "a = b" by (rule hyp2_S_cart2_inj)
  with `a \<noteq> b` show False ..
qed

lemma endpoint_in_S_incident:
  assumes "a \<noteq> b" and "a \<in> hyp2 \<union> S" and "b \<in> hyp2 \<union> S"
  and "proj2_incident a l" and "proj2_incident b l"
  shows "proj2_incident (endpoint_in_S a b) l" (is "proj2_incident ?p l")
proof -
  from `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S`
  have "?p \<in> S" and "B\<^sub>\<real> (cart2_pt a) (cart2_pt b) (cart2_pt ?p)"
    (is "B\<^sub>\<real> ?ca ?cb ?cp")
    by (rule endpoint_in_S)+

  from `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S` and `?p \<in> S`
  have "z_non_zero a" and "z_non_zero b" and "z_non_zero ?p"
    by (simp_all add: hyp2_S_z_non_zero)

  from `B\<^sub>\<real> ?ca ?cb ?cp`
  have "real_euclid.Col ?ca ?cb ?cp" unfolding real_euclid.Col_def ..
  with `z_non_zero a` and `z_non_zero b` and `z_non_zero ?p` and `a \<noteq> b`
    and `proj2_incident a l` and `proj2_incident b l`
  show "proj2_incident ?p l" by (rule euclid_Col_cart2_incident)
qed

lemma endpoints_in_S_incident_unique:
  assumes "a \<noteq> b" and "a \<in> hyp2 \<union> S" and "b \<in> hyp2 \<union> S" and "p \<in> S"
  and "proj2_incident a l" and "proj2_incident b l" and "proj2_incident p l"
  shows "p = endpoint_in_S a b \<or> p = endpoint_in_S b a"
  (is "p = ?q \<or> p = ?r")
proof -
  from `a \<noteq> b` and `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S`
  have "?q \<noteq> ?r" by (rule endpoint_in_S_swap)

  from `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S`
  have "?q \<in> S" and "?r \<in> S" by (simp_all add: endpoint_in_S)

  from `a \<noteq> b` and `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S`
    and `proj2_incident a l` and `proj2_incident b l`
  have "proj2_incident ?q l" and "proj2_incident ?r l"
    by (simp_all add: endpoint_in_S_incident)
  with `?q \<noteq> ?r` and `?q \<in> S` and `?r \<in> S` and `p \<in> S` and `proj2_incident p l`
  show "p = ?q \<or> p = ?r" by (simp add: line_S_two_intersections_only)
qed

lemma endpoint_in_S_unique:
  assumes "a \<noteq> b" and  "a \<in> hyp2 \<union> S" and "b \<in> hyp2 \<union> S" and "p \<in> S"
  and "B\<^sub>\<real> (cart2_pt a) (cart2_pt b) (cart2_pt p)" (is "B\<^sub>\<real> ?ca ?cb ?cp")
  shows "p = endpoint_in_S a b" (is "p = ?q")
proof (rule ccontr)
  from `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S` and `p \<in> S`
  have "z_non_zero a" and "z_non_zero b" and "z_non_zero p"
    by (simp_all add: hyp2_S_z_non_zero)
  with `B\<^sub>\<real> ?ca ?cb ?cp` and euclid_B_cart2_common_line [of a b p]
  obtain l where
    "proj2_incident a l" and "proj2_incident b l" and "proj2_incident p l"
    by auto
  with `a \<noteq> b` and `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S` and `p \<in> S`
  have "p = ?q \<or> p = endpoint_in_S b a" (is "p = ?q \<or> p = ?r")
    by (rule endpoints_in_S_incident_unique)

  assume "p \<noteq> ?q"
  with `p = ?q \<or> p = ?r` have "p = ?r" by simp
  with `b \<in> hyp2 \<union> S` and `a \<in> hyp2 \<union> S`
  have "B\<^sub>\<real> ?cb ?ca ?cp" by (simp add: endpoint_in_S)
  with `B\<^sub>\<real> ?ca ?cb ?cp` have "?ca = ?cb" by (rule real_euclid.th3_4)
  with `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S` have "a = b" by (rule hyp2_S_cart2_inj)
  with `a \<noteq> b` show False ..
qed

lemma between_hyp2_S:
  assumes "p \<in> hyp2 \<union> S" and "r \<in> hyp2 \<union> S" and "k \<ge> 0" and "k \<le> 1"
  shows "proj2_pt (k *\<^sub>R (cart2_pt r) + (1 - k) *\<^sub>R (cart2_pt p)) \<in> hyp2 \<union> S"
  (is "proj2_pt ?cq \<in> _")
proof -
  let ?cp = "cart2_pt p"
  let ?cr = "cart2_pt r"
  let ?q = "proj2_pt ?cq"
  from `p \<in> hyp2 \<union> S` and `r \<in> hyp2 \<union> S`
  have "z_non_zero p" and "z_non_zero r" by (simp_all add: hyp2_S_z_non_zero)
  hence "proj2_pt ?cp = p" and "proj2_pt ?cr = r" by (simp_all add: proj2_cart2)
  with `p \<in> hyp2 \<union> S` and `r \<in> hyp2 \<union> S`
  have "norm ?cp \<le> 1" and "norm ?cr \<le> 1"
    by (simp_all add: norm_le_1_iff_in_hyp2_S)

  from `k \<ge> 0` and `k \<le> 1`
    and norm_triangle_ineq [of "k *\<^sub>R ?cr" "(1 - k) *\<^sub>R ?cp"]
  have "norm ?cq \<le> k * norm ?cr + (1 - k) * norm ?cp" by simp

  from `k \<ge> 0` and `norm ?cr \<le> 1` and mult_mono [of k k "norm ?cr" 1]
  have "k * norm ?cr \<le> k" by simp

  from `k \<le> 1` and `norm ?cp \<le> 1`
    and mult_mono [of "1 - k" "1 - k" "norm ?cp" 1]
  have "(1 - k) * norm ?cp \<le> 1 - k" by simp
  with `norm ?cq \<le> k * norm ?cr + (1 - k) * norm ?cp` and `k * norm ?cr \<le> k`
  have "norm ?cq \<le> 1" by simp
  thus "?q \<in> hyp2 \<union> S" by (simp add: norm_le_1_iff_in_hyp2_S)
qed

subsection {* The Klein--Beltrami model satisfies axiom 4 *}

definition expansion_factor :: "proj2 \<Rightarrow> cltn2 \<Rightarrow> real" where
  "expansion_factor p J \<equiv> (cart2_append1 p v* cltn2_rep J)$3"

lemma expansion_factor:
  assumes "p \<in> hyp2 \<union> S" and "is_K2_isometry J"
  shows "expansion_factor p J \<noteq> 0"
  and "cart2_append1 p v* cltn2_rep J
  = expansion_factor p J *\<^sub>R cart2_append1 (apply_cltn2 p J)"
proof -
  from `p \<in> hyp2 \<union> S` and `is_K2_isometry J`
  have "z_non_zero (apply_cltn2 p J)" by (rule is_K2_isometry_z_non_zero)

  from `p \<in> hyp2 \<union> S` and `is_K2_isometry J`
  and cart2_append1_apply_cltn2
  obtain k where "k \<noteq> 0"
    and "cart2_append1 p v* cltn2_rep J = k *\<^sub>R cart2_append1 (apply_cltn2 p J)"
    by auto
  from `cart2_append1 p v* cltn2_rep J = k *\<^sub>R cart2_append1 (apply_cltn2 p J)`
    and `z_non_zero (apply_cltn2 p J)`
  have "expansion_factor p J = k"
    by (unfold expansion_factor_def) (simp add: cart2_append1_z)
  with `k \<noteq> 0`
    and `cart2_append1 p v* cltn2_rep J = k *\<^sub>R cart2_append1 (apply_cltn2 p J)`
  show "expansion_factor p J \<noteq> 0"
    and "cart2_append1 p v* cltn2_rep J
    = expansion_factor p J *\<^sub>R cart2_append1 (apply_cltn2 p J)"
    by simp_all
qed

lemma expansion_factor_linear_apply_cltn2:
  assumes "p \<in> hyp2 \<union> S" and "q \<in> hyp2 \<union> S" and "r \<in> hyp2 \<union> S"
  and "is_K2_isometry J"
  and "cart2_pt r = k *\<^sub>R cart2_pt p + (1 - k) *\<^sub>R cart2_pt q"
  shows "expansion_factor r J *\<^sub>R cart2_append1 (apply_cltn2 r J)
  = (k * expansion_factor p J) *\<^sub>R cart2_append1 (apply_cltn2 p J)
  + ((1 - k) * expansion_factor q J) *\<^sub>R cart2_append1 (apply_cltn2 q J)"
  (is "?er *\<^sub>R _ = (k * ?ep) *\<^sub>R _ + ((1 - k) * ?eq) *\<^sub>R _")
proof -
  let ?cp = "cart2_pt p"
  let ?cq = "cart2_pt q"
  let ?cr = "cart2_pt r"
  let ?cp1 = "cart2_append1 p"
  let ?cq1 = "cart2_append1 q"
  let ?cr1 = "cart2_append1 r"
  let ?repJ = "cltn2_rep J"
  from `p \<in> hyp2 \<union> S` and `q \<in> hyp2 \<union> S` and `r \<in> hyp2 \<union> S`
  have "z_non_zero p" and "z_non_zero q" and "z_non_zero r"
    by (simp_all add: hyp2_S_z_non_zero)

  from `?cr = k *\<^sub>R ?cp + (1 - k) *\<^sub>R ?cq`
  have "vector2_append1 ?cr
    = k *\<^sub>R vector2_append1 ?cp + (1 - k) *\<^sub>R vector2_append1 ?cq"
    by (unfold vector2_append1_def vector_def) (simp add: vec_eq_iff)
  with `z_non_zero p` and `z_non_zero q` and `z_non_zero r`
  have "?cr1 = k *\<^sub>R ?cp1 + (1 - k) *\<^sub>R ?cq1" by (simp add: cart2_append1)
  hence "?cr1 v* ?repJ = k *\<^sub>R (?cp1 v* ?repJ) + (1 - k) *\<^sub>R (?cq1 v* ?repJ)"
    by (simp add: vector_matrix_left_distrib
      scalar_vector_matrix_assoc [symmetric])
  with `p \<in> hyp2 \<union> S` and `q \<in> hyp2 \<union> S` and `r \<in> hyp2 \<union> S`
    and `is_K2_isometry J`
  show "?er *\<^sub>R cart2_append1 (apply_cltn2 r J)
    = (k * ?ep) *\<^sub>R cart2_append1 (apply_cltn2 p J)
    + ((1 - k) * ?eq) *\<^sub>R cart2_append1 (apply_cltn2 q J)"
    by (simp add: expansion_factor)
qed

lemma expansion_factor_linear:
  assumes "p \<in> hyp2 \<union> S" and "q \<in> hyp2 \<union> S" and "r \<in> hyp2 \<union> S"
  and "is_K2_isometry J"
  and "cart2_pt r = k *\<^sub>R cart2_pt p + (1 - k) *\<^sub>R cart2_pt q"
  shows "expansion_factor r J
  = k * expansion_factor p J + (1 - k) * expansion_factor q J"
  (is "?er = k * ?ep + (1 - k) * ?eq")
proof -
  from `p \<in> hyp2 \<union> S` and `q \<in> hyp2 \<union> S` and `r \<in> hyp2 \<union> S`
    and `is_K2_isometry J`
  have "z_non_zero (apply_cltn2 p J)"
    and "z_non_zero (apply_cltn2 q J)"
    and "z_non_zero (apply_cltn2 r J)"
    by (simp_all add: is_K2_isometry_z_non_zero)

  from `p \<in> hyp2 \<union> S` and `q \<in> hyp2 \<union> S` and `r \<in> hyp2 \<union> S`
    and `is_K2_isometry J`
    and `cart2_pt r = k *\<^sub>R cart2_pt p + (1 - k) *\<^sub>R cart2_pt q`
  have "?er *\<^sub>R cart2_append1 (apply_cltn2 r J)
    = (k * ?ep) *\<^sub>R cart2_append1 (apply_cltn2 p J)
    + ((1 - k) * ?eq) *\<^sub>R cart2_append1 (apply_cltn2 q J)"
    by (rule expansion_factor_linear_apply_cltn2)
  hence "(?er *\<^sub>R cart2_append1 (apply_cltn2 r J))$3
    = ((k * ?ep) *\<^sub>R cart2_append1 (apply_cltn2 p J)
    + ((1 - k) * ?eq) *\<^sub>R cart2_append1 (apply_cltn2 q J))$3"
    by simp
  with `z_non_zero (apply_cltn2 p J)`
    and `z_non_zero (apply_cltn2 q J)`
    and `z_non_zero (apply_cltn2 r J)`
  show "?er = k * ?ep + (1 - k) * ?eq" by (simp add: cart2_append1_z)
qed

lemma expansion_factor_sgn_invariant:
  assumes "p \<in> hyp2 \<union> S" and "q \<in> hyp2 \<union> S" and "is_K2_isometry J"
  shows "sgn (expansion_factor p J) = sgn (expansion_factor q J)"
  (is "sgn ?ep = sgn ?eq")
proof (rule ccontr)
  assume "sgn ?ep \<noteq> sgn ?eq"

  from `p \<in> hyp2 \<union> S` and `q \<in> hyp2 \<union> S` and `is_K2_isometry J`
  have "?ep \<noteq> 0" and "?eq \<noteq> 0" by (simp_all add: expansion_factor)
  hence "sgn ?ep \<in> {-1,1}" and "sgn ?eq \<in> {-1,1}"
    by (simp_all add: sgn_real_def)
  with `sgn ?ep \<noteq> sgn ?eq` have "sgn ?ep = - sgn ?eq" by auto
  hence "sgn ?ep = sgn (-?eq)" by (subst sgn_minus)
  with sgn_plus [of ?ep "-?eq"]
  have "sgn (?ep - ?eq) = sgn ?ep" by (simp add: algebra_simps)
  with `sgn ?ep \<in> {-1,1}` have "?ep - ?eq \<noteq> 0" by (auto simp add: sgn_real_def)

  let ?k = "-?eq / (?ep - ?eq)"
  from `sgn (?ep - ?eq) = sgn ?ep` and `sgn ?ep = sgn (-?eq)`
  have "sgn (?ep - ?eq) = sgn (-?eq)" by simp
  with `?ep - ?eq \<noteq> 0` and sgn_div [of "?ep - ?eq" "-?eq"]
  have "?k > 0" by simp

  from `?ep - ?eq \<noteq> 0`
  have "1 - ?k = ?ep / (?ep - ?eq)" by (simp add: field_simps)
  with `sgn (?ep - ?eq) = sgn ?ep` and `?ep - ?eq \<noteq> 0`
  have "1 - ?k > 0" by (simp add: sgn_div)
  hence "?k < 1" by simp

  let ?cp = "cart2_pt p"
  let ?cq = "cart2_pt q"
  let ?cr = "?k *\<^sub>R ?cp + (1 - ?k) *\<^sub>R ?cq"
  let ?r = "proj2_pt ?cr"
  let ?er = "expansion_factor ?r J"
  have "cart2_pt ?r = ?cr" by (rule cart2_proj2)

  from `p \<in> hyp2 \<union> S` and `q \<in> hyp2 \<union> S` and `?k > 0` and `?k < 1`
    and between_hyp2_S [of q p ?k]
  have "?r \<in> hyp2 \<union> S" by simp
  with `p \<in> hyp2 \<union> S` and `q \<in> hyp2 \<union> S` and `is_K2_isometry J`
    and `cart2_pt ?r = ?cr`
    and expansion_factor_linear [of p q ?r J ?k]
  have "?er = ?k * ?ep + (1 - ?k) * ?eq" by simp
  with `?ep - ?eq \<noteq> 0` have "?er = 0" by (simp add: field_simps)
  with `?r \<in> hyp2 \<union> S` and `is_K2_isometry J`
  show False by (simp add: expansion_factor)
qed

lemma statement_63:
  assumes "p \<in> hyp2 \<union> S" and "q \<in> hyp2 \<union> S" and "r \<in> hyp2 \<union> S"
  and "is_K2_isometry J" and "B\<^sub>\<real> (cart2_pt p) (cart2_pt q) (cart2_pt r)"
  shows "B\<^sub>\<real>
  (cart2_pt (apply_cltn2 p J))
  (cart2_pt (apply_cltn2 q J))
  (cart2_pt (apply_cltn2 r J))"
proof -
  let ?cp = "cart2_pt p"
  let ?cq = "cart2_pt q"
  let ?cr = "cart2_pt r"
  let ?ep = "expansion_factor p J"
  let ?eq = "expansion_factor q J"
  let ?er = "expansion_factor r J"
  from `q \<in> hyp2 \<union> S` and `is_K2_isometry J`
  have "?eq \<noteq> 0" by (rule expansion_factor)

  from `p \<in> hyp2 \<union> S` and `q \<in> hyp2 \<union> S` and `r \<in> hyp2 \<union> S`
    and `is_K2_isometry J` and expansion_factor_sgn_invariant
  have "sgn ?ep = sgn ?eq" and "sgn ?er = sgn ?eq" by fast+
  with `?eq \<noteq> 0`
  have "?ep / ?eq > 0" and "?er / ?eq > 0" by (simp_all add: sgn_div)

  from `B\<^sub>\<real> ?cp ?cq ?cr`
  obtain k where "k \<ge> 0" and "k \<le> 1" and "?cq = k *\<^sub>R ?cr + (1 - k) *\<^sub>R ?cp"
    by (unfold real_euclid_B_def) (auto simp add: algebra_simps)

  let ?c = "k * ?er / ?eq"
  from `k \<ge> 0` and `?er / ?eq > 0` and mult_nonneg_nonneg [of k "?er / ?eq"]
  have "?c \<ge> 0" by simp

  from `r \<in> hyp2 \<union> S` and `p \<in> hyp2 \<union> S` and `q \<in> hyp2 \<union> S`
    and `is_K2_isometry J` and `?cq = k *\<^sub>R ?cr + (1 - k) *\<^sub>R ?cp`
  have "?eq = k * ?er + (1 - k) * ?ep" by (rule expansion_factor_linear)
  with `?eq \<noteq> 0` have "1 - ?c = (1 - k) * ?ep / ?eq" by (simp add: field_simps)
  with `k \<le> 1` and `?ep / ?eq > 0`
    and mult_nonneg_nonneg [of "1 - k" "?ep / ?eq"]
  have "?c \<le> 1" by simp

  let ?pJ = "apply_cltn2 p J"
  let ?qJ = "apply_cltn2 q J"
  let ?rJ = "apply_cltn2 r J"
  let ?cpJ = "cart2_pt ?pJ"
  let ?cqJ = "cart2_pt ?qJ"
  let ?crJ = "cart2_pt ?rJ"
  let ?cpJ1 = "cart2_append1 ?pJ"
  let ?cqJ1 = "cart2_append1 ?qJ"
  let ?crJ1 = "cart2_append1 ?rJ"
  from `p \<in> hyp2 \<union> S` and `q \<in> hyp2 \<union> S` and `r \<in> hyp2 \<union> S`
    and `is_K2_isometry J`
  have "z_non_zero ?pJ" and "z_non_zero ?qJ" and "z_non_zero ?rJ"
    by (simp_all add: is_K2_isometry_z_non_zero)

  from `r \<in> hyp2 \<union> S` and `p \<in> hyp2 \<union> S` and `q \<in> hyp2 \<union> S`
    and `is_K2_isometry J` and `?cq = k *\<^sub>R ?cr + (1 - k) *\<^sub>R ?cp`
  have "?eq *\<^sub>R ?cqJ1 = (k * ?er) *\<^sub>R ?crJ1 + ((1 - k) * ?ep) *\<^sub>R ?cpJ1"
    by (rule expansion_factor_linear_apply_cltn2)
  hence "(1 / ?eq) *\<^sub>R (?eq *\<^sub>R ?cqJ1)
    = (1 / ?eq) *\<^sub>R ((k * ?er) *\<^sub>R ?crJ1 + ((1 - k) * ?ep) *\<^sub>R ?cpJ1)" by simp
  with `1 - ?c = (1 - k) * ?ep / ?eq` and `?eq \<noteq> 0`
  have "?cqJ1 = ?c *\<^sub>R ?crJ1 + (1 - ?c) *\<^sub>R ?cpJ1"
    by (simp add: scaleR_right_distrib)
  with `z_non_zero ?pJ` and `z_non_zero ?qJ` and `z_non_zero ?rJ`
  have "vector2_append1 ?cqJ
    = ?c *\<^sub>R vector2_append1 ?crJ + (1 - ?c) *\<^sub>R vector2_append1 ?cpJ"
    by (simp add: cart2_append1)
  hence "?cqJ = ?c *\<^sub>R ?crJ + (1 - ?c) *\<^sub>R ?cpJ"
    unfolding vector2_append1_def and vector_def
    by (simp add: vec_eq_iff forall_2 forall_3)
  with `?c \<ge> 0` and `?c \<le> 1`
  show "B\<^sub>\<real> ?cpJ ?cqJ ?crJ"
    by (unfold real_euclid_B_def) (simp add: algebra_simps exI [of _ ?c])
qed

theorem hyp2_axiom4: "\<forall> q a b c. \<exists> x. B\<^sub>K q a x \<and> a x \<congruent>\<^sub>K b c"
proof (rule allI)+
  fix q a b c :: hyp2
  let ?pq = "Rep_hyp2 q"
  let ?pa = "Rep_hyp2 a"
  let ?pb = "Rep_hyp2 b"
  let ?pc = "Rep_hyp2 c"
  have "?pq \<in> hyp2" and "?pa \<in> hyp2" and "?pb \<in> hyp2" and "?pc \<in> hyp2"
    by (rule Rep_hyp2)+
  let ?cq = "cart2_pt ?pq"
  let ?ca = "cart2_pt ?pa"
  let ?cb = "cart2_pt ?pb"
  let ?cc = "cart2_pt ?pc"
  let ?pp = "\<some> p. p \<in> S \<and> B\<^sub>\<real> ?cb ?cc (cart2_pt p)"
  let ?cp = "cart2_pt ?pp"
  from `?pb \<in> hyp2` and `?pc \<in> hyp2` and extend_to_S [of ?pb ?pc]
    and someI_ex [of "\<lambda> p. p \<in> S \<and> B\<^sub>\<real> ?cb ?cc (cart2_pt p)"]
  have "?pp \<in> S" and "B\<^sub>\<real> ?cb ?cc ?cp" by auto

  let ?pr = "\<some> r. r \<in> S \<and> B\<^sub>\<real> ?cq ?ca (cart2_pt r)"
  let ?cr = "cart2_pt ?pr"
  from `?pq \<in> hyp2` and `?pa \<in> hyp2` and extend_to_S [of ?pq ?pa]
    and someI_ex [of "\<lambda> r. r \<in> S \<and> B\<^sub>\<real> ?cq ?ca (cart2_pt r)"]
  have "?pr \<in> S" and "B\<^sub>\<real> ?cq ?ca ?cr" by auto

  from `?pb \<in> hyp2` and `?pa \<in> hyp2` and `?pp \<in> S` and `?pr \<in> S`
    and statement66_existence [of ?pb ?pa ?pp ?pr]
  obtain J where "is_K2_isometry J"
    and "apply_cltn2 ?pb J = ?pa" and "apply_cltn2 ?pp J = ?pr"
    by auto
  let ?px = "apply_cltn2 ?pc J"
  let ?cx = "cart2_pt ?px"
  let ?x = "Abs_hyp2 ?px"
  from `is_K2_isometry J` and `?pc \<in> hyp2`
  have "?px \<in> hyp2" by (rule statement60_one_way)
  hence "Rep_hyp2 ?x = ?px" by (rule Abs_hyp2_inverse)

  from `?pb \<in> hyp2` and `?pc \<in> hyp2` and `?pp \<in> S` and `is_K2_isometry J`
    and `B\<^sub>\<real> ?cb ?cc ?cp` and statement_63
  have "B\<^sub>\<real> (cart2_pt (apply_cltn2 ?pb J)) ?cx (cart2_pt (apply_cltn2 ?pp J))"
    by simp
  with `apply_cltn2 ?pb J = ?pa` and `apply_cltn2 ?pp J = ?pr`
  have "B\<^sub>\<real> ?ca ?cx ?cr" by simp
  with `B\<^sub>\<real> ?cq ?ca ?cr` have "B\<^sub>\<real> ?cq ?ca ?cx" by (rule real_euclid.th3_5_1)
  with `Rep_hyp2 ?x = ?px`
  have "B\<^sub>K q a ?x"
    unfolding real_hyp2_B_def and hyp2_rep_def
    by simp

  have "Abs_hyp2 ?pa = a" by (rule Rep_hyp2_inverse)
  with `apply_cltn2 ?pb J = ?pa`
  have "hyp2_cltn2 b J = a" by (unfold hyp2_cltn2_def) simp

  have "hyp2_cltn2 c J = ?x" unfolding hyp2_cltn2_def ..
  with `is_K2_isometry J` and `hyp2_cltn2 b J = a`
  have "b c \<congruent>\<^sub>K a ?x"
    by (unfold real_hyp2_C_def) (simp add: exI [of _ J])
  hence "a ?x \<congruent>\<^sub>K b c" by (rule hyp2.th2_2)
  with `B\<^sub>K q a ?x`
  show "\<exists> x. B\<^sub>K q a x \<and> a x \<congruent>\<^sub>K b c" by (simp add: exI [of _ ?x])
qed

subsection {* More betweenness theorems *}

lemma hyp2_S_points_fix_line:
  assumes "a \<in> hyp2" and "p \<in> S" and "is_K2_isometry J"
  and "apply_cltn2 a J = a" (is "?aJ = a")
  and "apply_cltn2 p J = p" (is "?pJ = p")
  and "proj2_incident a l" and "proj2_incident p l" and "proj2_incident b l"
  shows "apply_cltn2 b J = b" (is "?bJ = b")
proof -
  let ?lJ = "apply_cltn2_line l J"
  from `proj2_incident a l` and `proj2_incident p l`
  have "proj2_incident ?aJ ?lJ" and "proj2_incident ?pJ ?lJ" by simp_all
  with `?aJ = a` and `?pJ = p`
  have "proj2_incident a ?lJ" and "proj2_incident p ?lJ" by simp_all

  from `a \<in> hyp2` `proj2_incident a l` and line_through_K2_intersect_S_again [of a l]
  obtain q where "q \<noteq> p" and "q \<in> S" and "proj2_incident q l" by auto
  let ?qJ = "apply_cltn2 q J"

  from `a \<in> hyp2` and `p \<in> S` and `q \<in> S`
  have "a \<noteq> p" and "a \<noteq> q" by (simp_all add: hyp2_S_not_equal)

  from `a \<noteq> p` and `proj2_incident a l` and `proj2_incident p l`
    and `proj2_incident a ?lJ` and `proj2_incident p ?lJ`
    and proj2_incident_unique
  have "?lJ = l" by auto

  from `proj2_incident q l` have "proj2_incident ?qJ ?lJ" by simp
  with `?lJ = l` have "proj2_incident ?qJ l" by simp

  from `q \<in> S` and `is_K2_isometry J`
  have "?qJ \<in> S" by (unfold is_K2_isometry_def) simp
  with `q \<noteq> p` and `p \<in> S` and `q \<in> S` and `proj2_incident p l`
    and `proj2_incident q l` and `proj2_incident ?qJ l`
    and line_S_two_intersections_only
  have "?qJ = p \<or> ?qJ = q" by simp

  have "?qJ = q"
  proof (rule ccontr)
    assume "?qJ \<noteq> q"
    with `?qJ = p \<or> ?qJ = q` have "?qJ = p" by simp
    with `?pJ = p` have "?qJ = ?pJ" by simp
    with apply_cltn2_injective have "q = p" by fast
    with `q \<noteq> p` show False ..
  qed
  with `q \<noteq> p` and `a \<noteq> p` and `a \<noteq> q` and `proj2_incident p l`
    and `proj2_incident q l` and `proj2_incident a l`
    and `?pJ = p` and `?aJ = a` and `proj2_incident b l`
    and cltn2_three_point_line [of p q a l J b]
  show "?bJ = b" by simp
qed

lemma K2_isometry_endpoint_in_S:
  assumes "a \<noteq> b" and "a \<in> hyp2 \<union> S" and "b \<in> hyp2 \<union> S" and "is_K2_isometry J"
  shows "apply_cltn2 (endpoint_in_S a b) J
  = endpoint_in_S (apply_cltn2 a J) (apply_cltn2 b J)"
  (is "?pJ = endpoint_in_S ?aJ ?bJ")
proof -
  let ?p = "endpoint_in_S a b"

  from `a \<noteq> b` and apply_cltn2_injective have "?aJ \<noteq> ?bJ" by fast

  from `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S` and `is_K2_isometry J`
    and is_K2_isometry_hyp2_S
  have "?aJ \<in> hyp2 \<union> S" and "?bJ \<in> hyp2 \<union> S" by simp_all

  let ?ca = "cart2_pt a"
  let ?cb = "cart2_pt b"
  let ?cp = "cart2_pt ?p"
  from `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S`
  have "?p \<in> S" and "B\<^sub>\<real> ?ca ?cb ?cp" by (rule endpoint_in_S)+

  from `?p \<in> S` and `is_K2_isometry J`
  have "?pJ \<in> S" by (unfold is_K2_isometry_def) simp

  let ?caJ = "cart2_pt ?aJ"
  let ?cbJ = "cart2_pt ?bJ"
  let ?cpJ = "cart2_pt ?pJ"
  from `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S` and `?p \<in> S` and `is_K2_isometry J`
    and `B\<^sub>\<real> ?ca ?cb ?cp` and statement_63
  have "B\<^sub>\<real> ?caJ ?cbJ ?cpJ" by simp
  with `?aJ \<noteq> ?bJ` and `?aJ \<in> hyp2 \<union> S` and `?bJ \<in> hyp2 \<union> S` and `?pJ \<in> S`
  show "?pJ = endpoint_in_S ?aJ ?bJ" by (rule endpoint_in_S_unique)
qed

lemma between_endpoint_in_S:
  assumes "a \<noteq> b" and "b \<noteq> c"
  and "a \<in> hyp2 \<union> S" and "b \<in> hyp2 \<union> S" and "c \<in> hyp2 \<union> S"
  and "B\<^sub>\<real> (cart2_pt a) (cart2_pt b) (cart2_pt c)" (is "B\<^sub>\<real> ?ca ?cb ?cc")
  shows "endpoint_in_S a b = endpoint_in_S b c" (is "?p = ?q")
proof -
  from `b \<noteq> c` and `b \<in> hyp2 \<union> S` and `c \<in> hyp2 \<union> S` and hyp2_S_cart2_inj
  have "?cb \<noteq> ?cc" by auto

  let ?cq = "cart2_pt ?q"
  from `b \<in> hyp2 \<union> S` and `c \<in> hyp2 \<union> S`
  have "?q \<in> S" and "B\<^sub>\<real> ?cb ?cc ?cq" by (rule endpoint_in_S)+

  from `?cb \<noteq> ?cc` and `B\<^sub>\<real> ?ca ?cb ?cc` and `B\<^sub>\<real> ?cb ?cc ?cq`
  have "B\<^sub>\<real> ?ca ?cb ?cq" by (rule real_euclid.th3_7_2)
  with `a \<noteq> b` and `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S` and `?q \<in> S`
  have "?q = ?p" by (rule endpoint_in_S_unique)
  thus "?p = ?q" ..
qed

lemma hyp2_extend_segment_unique:
  assumes "a \<noteq> b" and "B\<^sub>K a b c" and "B\<^sub>K a b d" and "b c \<congruent>\<^sub>K b d"
  shows "c = d"
proof cases
  assume "b = c"
  with `b c \<congruent>\<^sub>K b d` show "c = d" by (simp add: hyp2.A3_reversed)
next
  assume "b \<noteq> c"

  have "b \<noteq> d"
  proof (rule ccontr)
    assume "\<not> b \<noteq> d"
    hence "b = d" by simp
    with `b c \<congruent>\<^sub>K b d` have "b c \<congruent>\<^sub>K b b" by simp
    hence "b = c" by (rule hyp2.A3')
    with `b \<noteq> c` show False ..
  qed
  with `a \<noteq> b` and `b \<noteq> c`
  have "Rep_hyp2 a \<noteq> Rep_hyp2 b" (is "?pa \<noteq> ?pb")
    and "Rep_hyp2 b \<noteq> Rep_hyp2 c" (is "?pb \<noteq> ?pc")
    and "Rep_hyp2 b \<noteq> Rep_hyp2 d" (is "?pb \<noteq> ?pd")
    by (simp_all add: Rep_hyp2_inject)

  have "?pa \<in> hyp2" and "?pb \<in> hyp2" and "?pc \<in> hyp2" and "?pd \<in> hyp2"
    by (rule Rep_hyp2)+

  let ?pp = "endpoint_in_S ?pb ?pc"
  let ?ca = "cart2_pt ?pa"
  let ?cb = "cart2_pt ?pb"
  let ?cc = "cart2_pt ?pc"
  let ?cd = "cart2_pt ?pd"
  let ?cp = "cart2_pt ?pp"
  from `?pb \<in> hyp2` and `?pc \<in> hyp2`
  have "?pp \<in> S" and "B\<^sub>\<real> ?cb ?cc ?cp" by (simp_all add: endpoint_in_S)

  from `b c \<congruent>\<^sub>K b d`
  obtain J where "is_K2_isometry J"
    and "hyp2_cltn2 b J = b" and "hyp2_cltn2 c J = d"
    by (unfold real_hyp2_C_def) auto

  from `hyp2_cltn2 b J = b` and `hyp2_cltn2 c J = d`
  have "Rep_hyp2 (hyp2_cltn2 b J) = ?pb"
    and "Rep_hyp2 (hyp2_cltn2 c J) = ?pd"
    by simp_all
  with `is_K2_isometry J`
  have "apply_cltn2 ?pb J = ?pb" and "apply_cltn2 ?pc J = ?pd"
    by (simp_all add: Rep_hyp2_cltn2)

  from `B\<^sub>K a b c` and `B\<^sub>K a b d`
  have "B\<^sub>\<real> ?ca ?cb ?cc" and "B\<^sub>\<real> ?ca ?cb ?cd"
    unfolding real_hyp2_B_def and hyp2_rep_def .

  from `?pb \<noteq> ?pc` and `?pb \<in> hyp2` and `?pc \<in> hyp2` and `is_K2_isometry J`
  have "apply_cltn2 ?pp J
    = endpoint_in_S (apply_cltn2 ?pb J) (apply_cltn2 ?pc J)"
    by (simp add: K2_isometry_endpoint_in_S)
  also from `apply_cltn2 ?pb J = ?pb` and `apply_cltn2 ?pc J = ?pd`
  have "\<dots> = endpoint_in_S ?pb ?pd" by simp
  also from `?pa \<noteq> ?pb` and `?pb \<noteq> ?pd`
    and `?pa \<in> hyp2` and `?pb \<in> hyp2` and `?pd \<in> hyp2` and `B\<^sub>\<real> ?ca ?cb ?cd`
  have "\<dots> = endpoint_in_S ?pa ?pb" by (simp add: between_endpoint_in_S)
  also from `?pa \<noteq> ?pb` and `?pb \<noteq> ?pc`
    and `?pa \<in> hyp2` and `?pb \<in> hyp2` and `?pc \<in> hyp2` and `B\<^sub>\<real> ?ca ?cb ?cc`
  have "\<dots> = endpoint_in_S ?pb ?pc" by (simp add: between_endpoint_in_S)
  finally have "apply_cltn2 ?pp J = ?pp" .

  from `?pb \<in> hyp2` and `?pc \<in> hyp2` and `?pp \<in> S`
  have "z_non_zero ?pb" and "z_non_zero ?pc" and "z_non_zero ?pp"
    by (simp_all add: hyp2_S_z_non_zero)
  with `B\<^sub>\<real> ?cb ?cc ?cp` and euclid_B_cart2_common_line [of ?pb ?pc ?pp]
  obtain l where "proj2_incident ?pb l" and "proj2_incident ?pp l"
    and "proj2_incident ?pc l"
    by auto
  with `?pb \<in> hyp2` and `?pp \<in> S` and `is_K2_isometry J`
    and `apply_cltn2 ?pb J = ?pb` and `apply_cltn2 ?pp J = ?pp`
  have "apply_cltn2 ?pc J = ?pc" by (rule hyp2_S_points_fix_line)
  with `apply_cltn2 ?pc J = ?pd` have "?pc = ?pd" by simp
  thus "c = d" by (subst Rep_hyp2_inject [symmetric])
qed

lemma line_S_match_intersections:
  assumes "p \<noteq> q" and "r \<noteq> s" and "p \<in> S" and "q \<in> S" and "r \<in> S" and "s \<in> S"
  and "proj2_set_Col {p,q,r,s}"
  shows "(p = r \<and> q = s) \<or> (q = r \<and> p = s)"
proof -
  from `proj2_set_Col {p,q,r,s}`
  obtain l where "proj2_incident p l" and "proj2_incident q l"
    and "proj2_incident r l" and "proj2_incident s l"
    by (unfold proj2_set_Col_def) auto
  with `r \<noteq> s` and `p \<in> S` and `q \<in> S` and `r \<in> S` and `s \<in> S`
  have "p = r \<or> p = s" and "q = r \<or> q = s"
    by (simp_all add: line_S_two_intersections_only)

  show "(p = r \<and> q = s) \<or> (q = r \<and> p = s)"
  proof cases
    assume "p = r"
    with `p \<noteq> q` and `q = r \<or> q = s`
    show "(p = r \<and> q = s) \<or> (q = r \<and> p = s)" by simp
  next
    assume "p \<noteq> r"
    with `p = r \<or> p = s` have "p = s" by simp
    with `p \<noteq> q` and `q = r \<or> q = s`
    show "(p = r \<and> q = s) \<or> (q = r \<and> p = s)" by simp
  qed
qed

definition are_endpoints_in_S :: "[proj2, proj2, proj2, proj2] \<Rightarrow> bool" where
  "are_endpoints_in_S p q a b
  \<equiv> p \<noteq> q \<and> p \<in> S \<and> q \<in> S \<and> a \<in> hyp2 \<and> b \<in> hyp2 \<and> proj2_set_Col {p,q,a,b}"

lemma are_endpoints_in_S':
  assumes "p \<noteq> q" and "a \<noteq> b" and "p \<in> S" and "q \<in> S" and "a \<in> hyp2 \<union> S"
  and "b \<in> hyp2 \<union> S" and "proj2_set_Col {p,q,a,b}"
  shows "(p = endpoint_in_S a b \<and> q = endpoint_in_S b a)
  \<or> (q = endpoint_in_S a b \<and> p = endpoint_in_S b a)"
  (is "(p = ?r \<and> q = ?s) \<or> (q = ?r \<and> p = ?s)")
proof -
  from `a \<noteq> b` and `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S`
  have "?r \<noteq> ?s" by (simp add: endpoint_in_S_swap)

  from `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S`
  have "?r \<in> S" and "?s \<in> S" by (simp_all add: endpoint_in_S)

  from `proj2_set_Col {p,q,a,b}`
  obtain l where "proj2_incident p l" and "proj2_incident q l"
    and "proj2_incident a l" and "proj2_incident b l"
    by (unfold proj2_set_Col_def) auto

  from `a \<noteq> b` and `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S` and `proj2_incident a l`
    and `proj2_incident b l`
  have "proj2_incident ?r l" and "proj2_incident ?s l"
    by (simp_all add: endpoint_in_S_incident)
  with `proj2_incident p l` and `proj2_incident q l`
  have "proj2_set_Col {p,q,?r,?s}"
    by (unfold proj2_set_Col_def) (simp add: exI [of _ l])
  with `p \<noteq> q` and `?r \<noteq> ?s` and `p \<in> S` and `q \<in> S` and `?r \<in> S` and `?s \<in> S`
  show "(p = ?r \<and> q = ?s) \<or> (q = ?r \<and> p = ?s)"
    by (rule line_S_match_intersections)
qed

lemma are_endpoints_in_S:
  assumes "a \<noteq> b" and "are_endpoints_in_S p q a b"
  shows "(p = endpoint_in_S a b \<and> q = endpoint_in_S b a)
  \<or> (q = endpoint_in_S a b \<and> p = endpoint_in_S b a)"
  using assms
  by (unfold are_endpoints_in_S_def) (simp add: are_endpoints_in_S')

lemma S_intersections_endpoints_in_S:
  assumes "a \<noteq> 0" and "b \<noteq> 0" and "proj2_abs a \<noteq> proj2_abs b" (is "?pa \<noteq> ?pb")
  and "proj2_abs a \<in> hyp2" and "proj2_abs b \<in> hyp2 \<union> S"
  shows "(S_intersection1 a b = endpoint_in_S ?pa ?pb
      \<and> S_intersection2 a b = endpoint_in_S ?pb ?pa)
    \<or> (S_intersection2 a b = endpoint_in_S ?pa ?pb
      \<and> S_intersection1 a b = endpoint_in_S ?pb ?pa)"
  (is "(?pp = ?pr \<and> ?pq = ?ps) \<or> (?pq = ?pr \<and> ?pp = ?ps)")
proof -
  from `a \<noteq> 0` and `b \<noteq> 0` and `?pa \<noteq> ?pb` and `?pa \<in> hyp2`
  have "?pp \<noteq> ?pq" by (simp add: S_intersections_distinct)

  from `a \<noteq> 0` and `b \<noteq> 0` and `?pa \<noteq> ?pb` and `proj2_abs a \<in> hyp2`
  have "?pp \<in> S" and "?pq \<in> S"
    by (simp_all add: S_intersections_in_S)

  let ?l = "proj2_line_through ?pa ?pb"
  have "proj2_incident ?pa ?l" and "proj2_incident ?pb ?l"
    by (rule proj2_line_through_incident)+
  with `a \<noteq> 0` and `b \<noteq> 0` and `?pa \<noteq> ?pb`
  have "proj2_incident ?pp ?l" and "proj2_incident ?pq ?l"
    by (rule S_intersections_incident)+
  with `proj2_incident ?pa ?l` and `proj2_incident ?pb ?l`
  have "proj2_set_Col {?pp,?pq,?pa,?pb}"
    by (unfold proj2_set_Col_def) (simp add: exI [of _ ?l])
  with `?pp \<noteq> ?pq` and `?pa \<noteq> ?pb` and `?pp \<in> S` and `?pq \<in> S` and `?pa \<in> hyp2`
    and `?pb \<in> hyp2 \<union> S`
  show "(?pp = ?pr \<and> ?pq = ?ps) \<or> (?pq = ?pr \<and> ?pp = ?ps)"
    by (simp add: are_endpoints_in_S')
qed

lemma between_endpoints_in_S:
  assumes "a \<noteq> b" and "a \<in> hyp2 \<union> S" and "b \<in> hyp2 \<union> S"
  shows "B\<^sub>\<real>
  (cart2_pt (endpoint_in_S a b)) (cart2_pt a) (cart2_pt (endpoint_in_S b a))"
  (is "B\<^sub>\<real> ?cp ?ca ?cq")
proof -
  let ?cb = "cart2_pt b"
  from `b \<in> hyp2 \<union> S` and `a \<in> hyp2 \<union> S` and `a \<noteq> b`
  have "?cb \<noteq> ?ca" by (auto simp add: hyp2_S_cart2_inj)

  from `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S`
  have "B\<^sub>\<real> ?ca ?cb ?cp" and "B\<^sub>\<real> ?cb ?ca ?cq" by (simp_all add: endpoint_in_S)

  from `B\<^sub>\<real> ?ca ?cb ?cp` have "B\<^sub>\<real> ?cp ?cb ?ca" by (rule real_euclid.th3_2)
  with `?cb \<noteq> ?ca` and `B\<^sub>\<real> ?cb ?ca ?cq`
  show "B\<^sub>\<real> ?cp ?ca ?cq" by (simp add: real_euclid.th3_7_1)
qed

lemma S_hyp2_S_cart2_append1:
  assumes "p \<noteq> q" and "p \<in> S" and "q \<in> S" and "a \<in> hyp2"
  and "proj2_incident p l" and "proj2_incident q l" and "proj2_incident a l"
  shows "\<exists> k. k > 0 \<and> k < 1
  \<and> cart2_append1 a = k *\<^sub>R cart2_append1 q + (1 - k) *\<^sub>R cart2_append1 p"
proof -
  from `p \<in> S` and `q \<in> S` and `a \<in> hyp2`
  have "z_non_zero p" and "z_non_zero q" and "z_non_zero a"
    by (simp_all add: hyp2_S_z_non_zero)

  from assms
  have "B\<^sub>\<real> (cart2_pt p) (cart2_pt a) (cart2_pt q)" (is "B\<^sub>\<real> ?cp ?ca ?cq")
    by (simp add: hyp2_incident_in_middle)

  from `p \<in> S` and `q \<in> S` and `a \<in> hyp2`
  have "a \<noteq> p" and "a \<noteq> q" by (simp_all add: hyp2_S_not_equal)

  with `z_non_zero p` and `z_non_zero a` and `z_non_zero q`
    and `B\<^sub>\<real> ?cp ?ca ?cq`
  show "\<exists> k. k > 0 \<and> k < 1
    \<and> cart2_append1 a = k *\<^sub>R cart2_append1 q + (1 - k) *\<^sub>R cart2_append1 p"
    by (rule cart2_append1_between_strict)
qed

lemma are_endpoints_in_S_swap_34:
  assumes "are_endpoints_in_S p q a b"
  shows "are_endpoints_in_S p q b a"
proof -
  have "{p,q,b,a} = {p,q,a,b}" by auto
  with `are_endpoints_in_S p q a b`
  show "are_endpoints_in_S p q b a" by (unfold are_endpoints_in_S_def) simp
qed

lemma proj2_set_Col_endpoints_in_S:
  assumes "a \<noteq> b" and "a \<in> hyp2 \<union> S" and "b \<in> hyp2 \<union> S"
  shows "proj2_set_Col {endpoint_in_S a b, endpoint_in_S b a, a, b}"
  (is "proj2_set_Col {?p,?q,a,b}")
proof -
  let ?l = "proj2_line_through a b"
  have "proj2_incident a ?l" and "proj2_incident b ?l"
    by (rule proj2_line_through_incident)+
  with `a \<noteq> b` and `a \<in> hyp2 \<union> S` and `b \<in> hyp2 \<union> S`
  have "proj2_incident ?p ?l" and "proj2_incident ?q ?l"
    by (simp_all add: endpoint_in_S_incident)
  with `proj2_incident a ?l` and `proj2_incident b ?l`
  show "proj2_set_Col {?p,?q,a,b}"
    by (unfold proj2_set_Col_def) (simp add: exI [of _ ?l])
qed

lemma endpoints_in_S_are_endpoints_in_S:
  assumes "a \<noteq> b" and "a \<in> hyp2" and "b \<in> hyp2"
  shows "are_endpoints_in_S (endpoint_in_S a b) (endpoint_in_S b a) a b"
  (is "are_endpoints_in_S ?p ?q a b")
proof -
  from `a \<noteq> b` and `a \<in> hyp2` and `b \<in> hyp2`
  have "?p \<noteq> ?q" by (simp add: endpoint_in_S_swap)

  from `a \<in> hyp2` and `b \<in> hyp2`
  have "?p \<in> S" and "?q \<in> S" by (simp_all add: endpoint_in_S)

  from assms
  have "proj2_set_Col {?p,?q,a,b}" by (simp add: proj2_set_Col_endpoints_in_S)
  with `?p \<noteq> ?q` and `?p \<in> S` and `?q \<in> S` and `a \<in> hyp2` and `b \<in> hyp2`
  show "are_endpoints_in_S ?p ?q a b" by (unfold are_endpoints_in_S_def) simp
qed

lemma endpoint_in_S_S_hyp2_distinct:
  assumes "p \<in> S" and "a \<in> hyp2 \<union> S" and "p \<noteq> a"
  shows "endpoint_in_S p a \<noteq> p"
proof
  from `p \<noteq> a` and `p \<in> S` and `a \<in> hyp2 \<union> S`
  have "B\<^sub>\<real> (cart2_pt p) (cart2_pt a) (cart2_pt (endpoint_in_S p a))"
    by (simp add: endpoint_in_S)

  assume "endpoint_in_S p a = p"
  with `B\<^sub>\<real> (cart2_pt p) (cart2_pt a) (cart2_pt (endpoint_in_S p a))`
  have "cart2_pt p = cart2_pt a" by (simp add: real_euclid.A6')
  with `p \<in> S` and `a \<in> hyp2 \<union> S` have "p = a" by (simp add: hyp2_S_cart2_inj)
  with `p \<noteq> a` show False ..
qed

lemma endpoint_in_S_S_strict_hyp2_distinct:
  assumes "p \<in> S" and "a \<in> hyp2"
  shows "endpoint_in_S p a \<noteq> p"
proof -
  from `a \<in> hyp2` and `p \<in> S`
  have "p \<noteq> a" by (rule hyp2_S_not_equal [symmetric])
  with assms
  show "endpoint_in_S p a \<noteq> p" by (simp add: endpoint_in_S_S_hyp2_distinct)
qed

lemma end_and_opposite_are_endpoints_in_S:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "p \<in> S"
  and "proj2_incident a l" and "proj2_incident b l" and "proj2_incident p l"
  shows "are_endpoints_in_S p (endpoint_in_S p b) a b"
  (is "are_endpoints_in_S p ?q a b")
proof -
  from `p \<in> S` and `b \<in> hyp2`
  have "p \<noteq> ?q" by (rule endpoint_in_S_S_strict_hyp2_distinct [symmetric])

  from `p \<in> S` and `b \<in> hyp2` have "?q \<in> S" by (simp add: endpoint_in_S)

  from `b \<in> hyp2` and `p \<in> S`
  have "p \<noteq> b" by (rule hyp2_S_not_equal [symmetric])
  with `p \<in> S` and `b \<in> hyp2` and `proj2_incident p l` and `proj2_incident b l`
  have "proj2_incident ?q l" by (simp add: endpoint_in_S_incident)
  with `proj2_incident p l` and `proj2_incident a l` and `proj2_incident b l`
  have "proj2_set_Col {p,?q,a,b}"
    by (unfold proj2_set_Col_def) (simp add: exI [of _ l])
  with `p \<noteq> ?q` and `p \<in> S` and `?q \<in> S` and `a \<in> hyp2` and `b \<in> hyp2`
  show "are_endpoints_in_S p ?q a b" by (unfold are_endpoints_in_S_def) simp
qed

lemma real_hyp2_B_hyp2_cltn2:
  assumes "is_K2_isometry J" and "B\<^sub>K a b c"
  shows "B\<^sub>K (hyp2_cltn2 a J) (hyp2_cltn2 b J) (hyp2_cltn2 c J)"
  (is "B\<^sub>K ?aJ ?bJ ?cJ")
proof -
  from `B\<^sub>K a b c`
  have "B\<^sub>\<real> (hyp2_rep a) (hyp2_rep b) (hyp2_rep c)" by (unfold real_hyp2_B_def)
  with `is_K2_isometry J`
  have "B\<^sub>\<real> (cart2_pt (apply_cltn2 (Rep_hyp2 a) J))
    (cart2_pt (apply_cltn2 (Rep_hyp2 b) J))
    (cart2_pt (apply_cltn2 (Rep_hyp2 c) J))"
    by (unfold hyp2_rep_def) (simp add: Rep_hyp2 statement_63)
  moreover from `is_K2_isometry J`
  have "apply_cltn2 (Rep_hyp2 a) J \<in> hyp2"
    and "apply_cltn2 (Rep_hyp2 b) J \<in> hyp2"
    and "apply_cltn2 (Rep_hyp2 c) J \<in> hyp2"
    by (rule apply_cltn2_Rep_hyp2)+
  ultimately show "B\<^sub>K (hyp2_cltn2 a J) (hyp2_cltn2 b J) (hyp2_cltn2 c J)"
    unfolding hyp2_cltn2_def and real_hyp2_B_def and hyp2_rep_def
    by (simp add: Abs_hyp2_inverse)
qed

lemma real_hyp2_C_hyp2_cltn2:
  assumes "is_K2_isometry J"
  shows "a b \<congruent>\<^sub>K (hyp2_cltn2 a J) (hyp2_cltn2 b J)" (is "a b \<congruent>\<^sub>K ?aJ ?bJ")
  using assms by (unfold real_hyp2_C_def) (simp add: exI [of _ J])

subsection {* Perpendicularity *}

definition M_perp :: "proj2_line \<Rightarrow> proj2_line \<Rightarrow> bool" where
  "M_perp l m \<equiv> proj2_incident (pole l) m"

lemma M_perp_sym:
  assumes "M_perp l m"
  shows "M_perp m l"
proof -
  from `M_perp l m` have "proj2_incident (pole l) m" by (unfold M_perp_def)
  hence "proj2_incident (pole m) (polar (pole l))" by (rule incident_pole_polar)
  hence "proj2_incident (pole m) l" by (simp add: polar_pole)
  thus "M_perp m l" by (unfold M_perp_def)
qed

lemma M_perp_to_compass:
  assumes "M_perp l m" and "a \<in> hyp2" and "proj2_incident a l"
  and "b \<in> hyp2" and "proj2_incident b m"
  shows "\<exists> J. is_K2_isometry J
  \<and> apply_cltn2_line equator J = l \<and> apply_cltn2_line meridian J = m"
proof -
  from `a \<in> K2` and `proj2_incident a l`
    and line_through_K2_intersect_S_twice [of a l]
  obtain p and q where "p \<noteq> q" and "p \<in> S" and "q \<in> S"
    and "proj2_incident p l" and "proj2_incident q l"
    by auto

  have "\<exists> r. r \<in> S \<and> r \<notin> {p,q} \<and> proj2_incident r m"
  proof cases
    assume "proj2_incident p m"

    from `b \<in> K2` and `proj2_incident b m`
      and line_through_K2_intersect_S_again [of b m]
    obtain r where "r \<in> S" and "r \<noteq> p" and "proj2_incident r m" by auto

    have "r \<notin> {p,q}"
    proof
      assume "r \<in> {p,q}"
      with `r \<noteq> p` have "r = q" by simp
      with `proj2_incident r m` have "proj2_incident q m" by simp
      with `proj2_incident p l` and `proj2_incident q l`
        and `proj2_incident p m` and `proj2_incident q m` and `p \<noteq> q`
        and proj2_incident_unique [of p l q m]
      have "l = m" by simp
      with `M_perp l m` have "M_perp l l" by simp
      hence "proj2_incident (pole l) l" (is "proj2_incident ?s l")
        by (unfold M_perp_def)
      hence "proj2_incident ?s (polar ?s)" by (subst polar_pole)
      hence "?s \<in> S" by (simp add: incident_own_polar_in_S)
      with `p \<in> S` and `q \<in> S` and `proj2_incident p l` and `proj2_incident q l`
        and point_in_S_polar_is_tangent [of ?s]
      have "p = ?s" and "q = ?s" by (auto simp add: polar_pole)
      with `p \<noteq> q` show False by simp
    qed
    with `r \<in> S` and `proj2_incident r m`
    show "\<exists> r. r \<in> S \<and> r \<notin> {p,q} \<and> proj2_incident r m"
      by (simp add: exI [of _ r])
  next
    assume "\<not> proj2_incident p m"

    from `b \<in> K2` and `proj2_incident b m`
      and line_through_K2_intersect_S_again [of b m]
    obtain r where "r \<in> S" and "r \<noteq> q" and "proj2_incident r m" by auto

    from `\<not> proj2_incident p m` and `proj2_incident r m` have "r \<noteq> p" by auto
    with `r \<in> S` and `r \<noteq> q` and `proj2_incident r m`
    show "\<exists> r. r \<in> S \<and> r \<notin> {p,q} \<and> proj2_incident r m"
      by (simp add: exI [of _ r])
  qed
  then obtain r where "r \<in> S" and "r \<notin> {p,q}" and "proj2_incident r m" by auto

  from `p \<in> S` and `q \<in> S` and `r \<in> S` and `p \<noteq> q` and `r \<notin> {p,q}`
    and statement65_special_case [of p q r]
  obtain J where "is_K2_isometry J" and "apply_cltn2 east J = p"
    and "apply_cltn2 west J = q" and "apply_cltn2 north J = r"
    and "apply_cltn2 far_north J = proj2_intersection (polar p) (polar q)"
    by auto

  from `apply_cltn2 east J = p` and `apply_cltn2 west J = q`
    and `proj2_incident p l` and `proj2_incident q l`
  have "proj2_incident (apply_cltn2 east J) l"
    and "proj2_incident (apply_cltn2 west J) l"
    by simp_all
  with east_west_distinct and east_west_on_equator
  have "apply_cltn2_line equator J = l" by (rule apply_cltn2_line_unique)

  from `apply_cltn2 north J = r` and `proj2_incident r m`
  have "proj2_incident (apply_cltn2 north J) m" by simp

  from `p \<noteq> q` and polar_inj have "polar p \<noteq> polar q" by fast

  from `proj2_incident p l` and `proj2_incident q l`
  have "proj2_incident (pole l) (polar p)"
    and "proj2_incident (pole l) (polar q)"
    by (simp_all add: incident_pole_polar)
  with `polar p \<noteq> polar q`
  have "pole l = proj2_intersection (polar p) (polar q)"
    by (rule proj2_intersection_unique)
  with `apply_cltn2 far_north J = proj2_intersection (polar p) (polar q)`
  have "apply_cltn2 far_north J = pole l" by simp
  with `M_perp l m`
  have "proj2_incident (apply_cltn2 far_north J) m" by (unfold M_perp_def) simp
  with north_far_north_distinct and north_south_far_north_on_meridian
    and `proj2_incident (apply_cltn2 north J) m`
  have "apply_cltn2_line meridian J = m" by (simp add: apply_cltn2_line_unique)
  with `is_K2_isometry J` and `apply_cltn2_line equator J = l`
  show "\<exists> J. is_K2_isometry J
    \<and> apply_cltn2_line equator J = l \<and> apply_cltn2_line meridian J = m"
    by (simp add: exI [of _ J])
qed

definition drop_perp :: "proj2 \<Rightarrow> proj2_line \<Rightarrow> proj2_line" where
  "drop_perp p l \<equiv> proj2_line_through p (pole l)"

lemma drop_perp_incident: "proj2_incident p (drop_perp p l)"
  by (unfold drop_perp_def) (rule proj2_line_through_incident)

lemma drop_perp_perp: "M_perp l (drop_perp p l)"
  by (unfold drop_perp_def M_perp_def) (rule proj2_line_through_incident)

definition perp_foot :: "proj2 \<Rightarrow> proj2_line \<Rightarrow> proj2" where
  "perp_foot p l \<equiv> proj2_intersection l (drop_perp p l)"

lemma perp_foot_incident:
  shows "proj2_incident (perp_foot p l) l"
  and "proj2_incident (perp_foot p l) (drop_perp p l)"
  by (unfold perp_foot_def) (rule proj2_intersection_incident)+

lemma M_perp_hyp2:
  assumes "M_perp l m" and "a \<in> hyp2" and "proj2_incident a l" and "b \<in> hyp2"
  and "proj2_incident b m" and "proj2_incident c l" and "proj2_incident c m"
  shows "c \<in> hyp2"
proof -
  from `M_perp l m` and `a \<in> hyp2` and `proj2_incident a l` and `b \<in> hyp2`
    and `proj2_incident b m` and M_perp_to_compass [of l m a b]
  obtain J where "is_K2_isometry J" and "apply_cltn2_line equator J = l"
    and "apply_cltn2_line meridian J = m"
    by auto

  from `is_K2_isometry J` and K2_centre_in_K2
  have "apply_cltn2 K2_centre J \<in> hyp2"
    by (rule statement60_one_way)

  from `proj2_incident c l` and `apply_cltn2_line equator J = l`
    and `proj2_incident c m` and `apply_cltn2_line meridian J = m`
  have "proj2_incident c (apply_cltn2_line equator J)"
    and "proj2_incident c (apply_cltn2_line meridian J)"
    by simp_all
  with equator_meridian_distinct and K2_centre_on_equator_meridian
  have "apply_cltn2 K2_centre J = c" by (rule apply_cltn2_unique)
  with `apply_cltn2 K2_centre J \<in> hyp2` show "c \<in> hyp2" by simp
qed

lemma perp_foot_hyp2:
  assumes "a \<in> hyp2" and "proj2_incident a l" and "b \<in> hyp2"
  shows "perp_foot b l \<in> hyp2"
  using drop_perp_perp [of l b] and `a \<in> hyp2` and `proj2_incident a l`
    and `b \<in> hyp2` and drop_perp_incident [of b l]
    and perp_foot_incident [of b l]
  by (rule M_perp_hyp2)

definition perp_up :: "proj2 \<Rightarrow> proj2_line \<Rightarrow> proj2" where
  "perp_up a l
  \<equiv> if proj2_incident a l then \<some> p. p \<in> S \<and> proj2_incident p (drop_perp a l)
  else endpoint_in_S (perp_foot a l) a"

lemma perp_up_degenerate_in_S_incident:
  assumes "a \<in> hyp2" and "proj2_incident a l"
  shows "perp_up a l \<in> S" (is "?p \<in> S")
  and "proj2_incident (perp_up a l) (drop_perp a l)"
proof -
  from `proj2_incident a l`
  have "?p = (\<some> p. p \<in> S \<and> proj2_incident p (drop_perp a l))"
    by (unfold perp_up_def) simp

  from `a \<in> hyp2` and drop_perp_incident [of a l]
  have "\<exists> p. p \<in> S \<and> proj2_incident p (drop_perp a l)"
    by (rule line_through_K2_intersect_S)
  hence "?p \<in> S \<and> proj2_incident ?p (drop_perp a l)"
    unfolding `?p = (\<some> p. p \<in> S \<and> proj2_incident p (drop_perp a l))`
    by (rule someI_ex)
  thus "?p \<in> S" and "proj2_incident ?p (drop_perp a l)" by simp_all
qed

lemma perp_up_non_degenerate_in_S_at_end:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "proj2_incident b l"
  and "\<not> proj2_incident a l"
  shows "perp_up a l \<in> S"
  and "B\<^sub>\<real> (cart2_pt (perp_foot a l)) (cart2_pt a) (cart2_pt (perp_up a l))"
proof -
  from `\<not> proj2_incident a l`
  have "perp_up a l = endpoint_in_S (perp_foot a l) a"
    by (unfold perp_up_def) simp

  from `b \<in> hyp2` and `proj2_incident b l` and `a \<in> hyp2`
  have "perp_foot a l \<in> hyp2" by (rule perp_foot_hyp2)
  with `a \<in> hyp2`
  show "perp_up a l \<in> S"
    and "B\<^sub>\<real> (cart2_pt (perp_foot a l)) (cart2_pt a) (cart2_pt (perp_up a l))"
    unfolding `perp_up a l = endpoint_in_S (perp_foot a l) a`
    by (simp_all add: endpoint_in_S)
qed

lemma perp_up_in_S:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "proj2_incident b l"
  shows "perp_up a l \<in> S"
proof cases
  assume "proj2_incident a l"
  with `a \<in> hyp2`
  show "perp_up a l \<in> S" by (rule perp_up_degenerate_in_S_incident)
next
  assume "\<not> proj2_incident a l"
  with assms
  show "perp_up a l \<in> S" by (rule perp_up_non_degenerate_in_S_at_end)
qed

lemma perp_up_incident:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "proj2_incident b l"
  shows "proj2_incident (perp_up a l) (drop_perp a l)"
  (is "proj2_incident ?p ?m")
proof cases
  assume "proj2_incident a l"
  with `a \<in> hyp2`
  show "proj2_incident ?p ?m" by (rule perp_up_degenerate_in_S_incident)
next
  assume "\<not> proj2_incident a l"
  hence "?p = endpoint_in_S (perp_foot a l) a" (is "?p = endpoint_in_S ?c a")
    by (unfold perp_up_def) simp

  from perp_foot_incident [of a l] and `\<not> proj2_incident a l`
  have "?c \<noteq> a" by auto

  from `b \<in> hyp2` and `proj2_incident b l` and `a \<in> hyp2`
  have "?c \<in> hyp2" by (rule perp_foot_hyp2)
  with `?c \<noteq> a` and `a \<in> hyp2` and drop_perp_incident [of a l]
    and perp_foot_incident [of a l]
  show "proj2_incident ?p ?m"
    by (unfold `?p = endpoint_in_S ?c a`) (simp add: endpoint_in_S_incident)
qed

lemma drop_perp_same_line_pole_in_S:
  assumes "drop_perp p l = l"
  shows "pole l \<in> S"
proof -
  from `drop_perp p l = l`
  have "l = proj2_line_through p (pole l)" by (unfold drop_perp_def) simp
  with proj2_line_through_incident [of "pole l" p]
  have "proj2_incident (pole l) l" by simp
  hence "proj2_incident (pole l) (polar (pole l))" by (subst polar_pole)
  thus "pole l \<in> S" by (unfold incident_own_polar_in_S)
qed

lemma hyp2_drop_perp_not_same_line:
  assumes "a \<in> hyp2"
  shows "drop_perp a l \<noteq> l"
proof
  assume "drop_perp a l = l"
  hence "pole l \<in> S" by (rule drop_perp_same_line_pole_in_S)
  with `a \<in> hyp2`
  have "\<not> proj2_incident a (polar (pole l))"
    by (simp add: tangent_not_through_K2)
  with `drop_perp a l = l`
  have "\<not> proj2_incident a (drop_perp a l)" by (simp add: polar_pole)
  with drop_perp_incident [of a l] show False by simp
qed

lemma hyp2_incident_perp_foot_same_point:
  assumes "a \<in> hyp2" and "proj2_incident a l"
  shows "perp_foot a l = a"
proof -
  from `a \<in> hyp2`
  have "drop_perp a l \<noteq> l" by (rule hyp2_drop_perp_not_same_line)
  with perp_foot_incident [of a l] and `proj2_incident a l`
    and drop_perp_incident [of a l] and proj2_incident_unique
  show "perp_foot a l = a" by fast
qed

lemma perp_up_at_end:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "proj2_incident b l"
  shows "B\<^sub>\<real> (cart2_pt (perp_foot a l)) (cart2_pt a) (cart2_pt (perp_up a l))"
proof cases
  assume "proj2_incident a l"
  with `a \<in> hyp2`
  have "perp_foot a l = a" by (rule hyp2_incident_perp_foot_same_point)
  thus "B\<^sub>\<real> (cart2_pt (perp_foot a l)) (cart2_pt a) (cart2_pt (perp_up a l))"
    by (simp add: real_euclid.th3_1 real_euclid.th3_2)
next
  assume "\<not> proj2_incident a l"
  with assms
  show "B\<^sub>\<real> (cart2_pt (perp_foot a l)) (cart2_pt a) (cart2_pt (perp_up a l))"
    by (rule perp_up_non_degenerate_in_S_at_end)
qed

definition perp_down :: "proj2 \<Rightarrow> proj2_line \<Rightarrow> proj2" where
  "perp_down a l \<equiv> endpoint_in_S (perp_up a l) a"

lemma perp_down_in_S:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "proj2_incident b l"
  shows "perp_down a l \<in> S"
proof -
  from assms have "perp_up a l \<in> S" by (rule perp_up_in_S)
  with `a \<in> hyp2`
  show "perp_down a l \<in> S" by (unfold perp_down_def) (simp add: endpoint_in_S)
qed

lemma perp_down_incident:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "proj2_incident b l"
  shows "proj2_incident (perp_down a l) (drop_perp a l)"
proof -
  from assms have "perp_up a l \<in> S" by (rule perp_up_in_S)
  with `a \<in> hyp2` have "perp_up a l \<noteq> a" by (rule hyp2_S_not_equal [symmetric])

  from assms
  have "proj2_incident (perp_up a l) (drop_perp a l)" by (rule perp_up_incident)
  with `perp_up a l \<noteq> a` and `perp_up a l \<in> S` and `a \<in> hyp2`
    and drop_perp_incident [of a l]
  show "proj2_incident (perp_down a l) (drop_perp a l)"
    by (unfold perp_down_def) (simp add: endpoint_in_S_incident)
qed

lemma perp_up_down_distinct:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "proj2_incident b l"
  shows "perp_up a l \<noteq> perp_down a l"
proof -
  from assms have "perp_up a l \<in> S" by (rule perp_up_in_S)
  with `a \<in> hyp2`
  show "perp_up a l \<noteq> perp_down a l"
    unfolding perp_down_def
    by (simp add: endpoint_in_S_S_strict_hyp2_distinct [symmetric])
qed

lemma perp_up_down_foot_are_endpoints_in_S:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "proj2_incident b l"
  shows "are_endpoints_in_S (perp_up a l) (perp_down a l) (perp_foot a l) a"
proof -
  from `b \<in> hyp2` and `proj2_incident b l` and `a \<in> hyp2`
  have "perp_foot a l \<in> hyp2" by (rule perp_foot_hyp2)

  from assms have "perp_up a l \<in> S" by (rule perp_up_in_S)

  from assms
  have "proj2_incident (perp_up a l) (drop_perp a l)" by (rule perp_up_incident)
  with `perp_foot a l \<in> hyp2` and `a \<in> hyp2` and `perp_up a l \<in> S`
    and perp_foot_incident(2) [of a l] and drop_perp_incident [of a l]
  show "are_endpoints_in_S (perp_up a l) (perp_down a l) (perp_foot a l) a"
    by (unfold perp_down_def) (rule end_and_opposite_are_endpoints_in_S)
qed

lemma perp_foot_opposite_endpoint_in_S:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "c \<in> hyp2" and "a \<noteq> b"
  shows
  "endpoint_in_S (endpoint_in_S a b) (perp_foot c (proj2_line_through a b))
  = endpoint_in_S b a"
  (is "endpoint_in_S ?p ?d = endpoint_in_S b a")
proof -
  let ?q = "endpoint_in_S ?p ?d"

  from `a \<in> hyp2` and `b \<in> hyp2` have "?p \<in> S" by (simp add: endpoint_in_S)

  let ?l = "proj2_line_through a b"
  have "proj2_incident a ?l" and "proj2_incident b ?l"
    by (rule proj2_line_through_incident)+
  with `a \<noteq> b` and `a \<in> hyp2` and `b \<in> hyp2`
  have "proj2_incident ?p ?l"
    by (simp_all add: endpoint_in_S_incident)

  from `a \<in> hyp2` and `proj2_incident a ?l` and `c \<in> hyp2`
  have "?d \<in> hyp2" by (rule perp_foot_hyp2)
  with `?p \<in> S` have "?q \<noteq> ?p" by (rule endpoint_in_S_S_strict_hyp2_distinct)

  from `?p \<in> S` and `?d \<in> hyp2` have "?q \<in> S" by (simp add: endpoint_in_S)

  from `?d \<in> hyp2` and `?p \<in> S`
  have "?p \<noteq> ?d" by (rule hyp2_S_not_equal [symmetric])
  with `?p \<in> S` and `?d \<in> hyp2` and `proj2_incident ?p ?l`
    and perp_foot_incident(1) [of c ?l]
  have "proj2_incident ?q ?l" by (simp add: endpoint_in_S_incident)
  with `a \<noteq> b` and `a \<in> hyp2` and `b \<in> hyp2` and `?q \<in> S`
    and `proj2_incident a ?l` and `proj2_incident b ?l`
  have "?q = ?p \<or> ?q = endpoint_in_S b a"
    by (simp add: endpoints_in_S_incident_unique)
  with `?q \<noteq> ?p` show "?q = endpoint_in_S b a" by simp
qed

lemma endpoints_in_S_perp_foot_are_endpoints_in_S:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "c \<in> hyp2" and "a \<noteq> b"
  and "proj2_incident a l" and "proj2_incident b l"
  shows "are_endpoints_in_S
  (endpoint_in_S a b) (endpoint_in_S b a) a (perp_foot c l)"
proof -
  def p \<equiv> "endpoint_in_S a b"
    and q \<equiv> "endpoint_in_S b a"
    and d \<equiv> "perp_foot c l"

  from `a \<noteq> b` and `a \<in> hyp2` and `b \<in> hyp2`
  have "p \<noteq> q" by (unfold p_def q_def) (simp add: endpoint_in_S_swap)

  from `a \<in> hyp2` and `b \<in> hyp2`
  have "p \<in> S" and "q \<in> S" by (unfold p_def q_def) (simp_all add: endpoint_in_S)

  from `a \<in> hyp2` and `proj2_incident a l` and `c \<in> hyp2`
  have "d \<in> hyp2" by (unfold d_def) (rule perp_foot_hyp2)

  from `a \<noteq> b` and `a \<in> hyp2` and `b \<in> hyp2` and `proj2_incident a l`
    and `proj2_incident b l`
  have "proj2_incident p l" and "proj2_incident q l"
    by (unfold p_def q_def) (simp_all add: endpoint_in_S_incident)
  with `proj2_incident a l` and perp_foot_incident(1) [of c l]
  have "proj2_set_Col {p,q,a,d}"
    by (unfold d_def proj2_set_Col_def) (simp add: exI [of _ l])
  with `p \<noteq> q` and `p \<in> S` and `q \<in> S` and `a \<in> hyp2` and `d \<in> hyp2`
  show "are_endpoints_in_S p q a d" by (unfold are_endpoints_in_S_def) simp
qed

definition right_angle :: "proj2 \<Rightarrow> proj2 \<Rightarrow> proj2 \<Rightarrow> bool" where
  "right_angle p a q
  \<equiv> p \<in> S \<and> q \<in> S \<and> a \<in> hyp2
  \<and> M_perp (proj2_line_through p a) (proj2_line_through a q)"

lemma perp_foot_up_right_angle:
  assumes "p \<in> S" and "a \<in> hyp2" and "b \<in> hyp2" and "proj2_incident p l"
  and "proj2_incident b l"
  shows "right_angle p (perp_foot a l) (perp_up a l)"
proof -
  def c \<equiv> "perp_foot a l"
  def q \<equiv> "perp_up a l"
  from `a \<in> hyp2` and `b \<in> hyp2` and `proj2_incident b l`
  have "q \<in> S" by (unfold q_def) (rule perp_up_in_S)

  from `b \<in> hyp2` and `proj2_incident b l` and `a \<in> hyp2`
  have "c \<in> hyp2" by (unfold c_def) (rule perp_foot_hyp2)
  with `p \<in> S` and `q \<in> S` have "c \<noteq> p" and "c \<noteq> q"
    by (simp_all add: hyp2_S_not_equal)

  from `c \<noteq> p` [symmetric] and `proj2_incident p l`
    and perp_foot_incident(1) [of a l]
  have "l = proj2_line_through p c"
    by (unfold c_def) (rule proj2_line_through_unique)

  def m \<equiv> "drop_perp a l"
  from `a \<in> hyp2` and `b \<in> hyp2` and `proj2_incident b l`
  have "proj2_incident q m" by (unfold q_def m_def) (rule perp_up_incident)
  with `c \<noteq> q` and perp_foot_incident(2) [of a l]
  have "m = proj2_line_through c q"
    by (unfold c_def m_def) (rule proj2_line_through_unique)
  with `p \<in> S` and `q \<in> S` and `c \<in> hyp2` and drop_perp_perp [of l a]
    and `l = proj2_line_through p c`
  show "right_angle p (perp_foot a l) (perp_up a l)"
    by (unfold right_angle_def q_def c_def m_def) simp
qed

lemma M_perp_unique:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "proj2_incident a l"
  and "proj2_incident b m" and "proj2_incident b n" and "M_perp l m"
  and "M_perp l n"
  shows "m = n"
proof -
  from `a \<in> hyp2` and `proj2_incident a l`
  have "pole l \<notin> hyp2" by (rule line_through_hyp2_pole_not_in_hyp2)
  with `b \<in> hyp2` have "b \<noteq> pole l" by auto
  with `proj2_incident b m` and `M_perp l m` and `proj2_incident b n`
    and `M_perp l n` and proj2_incident_unique
  show "m = n" by (unfold M_perp_def) auto
qed

lemma perp_foot_eq_implies_drop_perp_eq:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "proj2_incident a l"
  and "perp_foot b l = perp_foot c l"
  shows "drop_perp b l = drop_perp c l"
proof -
  from `a \<in> hyp2` and `proj2_incident a l` and `b \<in> hyp2`
  have "perp_foot b l \<in> hyp2" by (rule perp_foot_hyp2)

  from `perp_foot b l = perp_foot c l`
  have "proj2_incident (perp_foot b l) (drop_perp c l)"
    by (simp add: perp_foot_incident)
  with `a \<in> hyp2` and `perp_foot b l \<in> hyp2` and `proj2_incident a l`
    and perp_foot_incident(2) [of b l] and drop_perp_perp [of l]
  show "drop_perp b l = drop_perp c l" by (simp add: M_perp_unique)
qed

lemma right_angle_to_compass:
  assumes "right_angle p a q"
  shows "\<exists> J. is_K2_isometry J \<and> apply_cltn2 p J = east
  \<and> apply_cltn2 a J = K2_centre \<and> apply_cltn2 q J = north"
proof -
  from `right_angle p a q`
  have "p \<in> S" and "q \<in> S" and "a \<in> hyp2"
    and "M_perp (proj2_line_through p a) (proj2_line_through a q)"
    (is "M_perp ?l ?m")
    by (unfold right_angle_def) simp_all

  have "proj2_incident p ?l" and "proj2_incident a ?l"
    and "proj2_incident q ?m" and "proj2_incident a ?m"
    by (rule proj2_line_through_incident)+

  from `M_perp ?l ?m` and `a \<in> hyp2` and `proj2_incident a ?l`
    and `proj2_incident a ?m` and M_perp_to_compass [of ?l ?m a a]
  obtain J''i where "is_K2_isometry J''i"
    and "apply_cltn2_line equator J''i = ?l"
    and "apply_cltn2_line meridian J''i = ?m"
    by auto
  let ?J'' = "cltn2_inverse J''i"

  from `apply_cltn2_line equator J''i = ?l`
    and `apply_cltn2_line meridian J''i = ?m`
    and `proj2_incident p ?l` and `proj2_incident a ?l`
    and `proj2_incident q ?m` and `proj2_incident a ?m`
  have "proj2_incident (apply_cltn2 p ?J'') equator"
    and "proj2_incident (apply_cltn2 a ?J'') equator"
    and "proj2_incident (apply_cltn2 q ?J'') meridian"
    and "proj2_incident (apply_cltn2 a ?J'') meridian"
    by (simp_all add: apply_cltn2_incident [symmetric])

  from `proj2_incident (apply_cltn2 a ?J'') equator`
    and `proj2_incident (apply_cltn2 a ?J'') meridian`
  have "apply_cltn2 a ?J'' = K2_centre"
    by (rule on_equator_meridian_is_K2_centre)

  from `is_K2_isometry J''i`
  have "is_K2_isometry ?J''" by (rule cltn2_inverse_is_K2_isometry)
  with `p \<in> S` and `q \<in> S`
  have "apply_cltn2 p ?J'' \<in> S" and "apply_cltn2 q ?J'' \<in> S"
    by (unfold is_K2_isometry_def) simp_all
  with east_west_distinct and north_south_distinct and compass_in_S
    and east_west_on_equator and north_south_far_north_on_meridian
    and `proj2_incident (apply_cltn2 p ?J'') equator`
    and `proj2_incident (apply_cltn2 q ?J'') meridian`
  have "apply_cltn2 p ?J'' = east \<or> apply_cltn2 p ?J'' = west"
    and "apply_cltn2 q ?J'' = north \<or> apply_cltn2 q ?J'' = south"
    by (simp_all add: line_S_two_intersections_only)

  have "\<exists> J'. is_K2_isometry J' \<and> apply_cltn2 p J' = east
    \<and> apply_cltn2 a J' = K2_centre
    \<and> (apply_cltn2 q J' = north \<or> apply_cltn2 q J' = south)"
  proof cases
    assume "apply_cltn2 p ?J'' = east"
    with `is_K2_isometry ?J''` and `apply_cltn2 a ?J'' = K2_centre`
      and `apply_cltn2 q ?J'' = north \<or> apply_cltn2 q ?J'' = south`
    show "\<exists> J'. is_K2_isometry J' \<and> apply_cltn2 p J' = east
      \<and> apply_cltn2 a J' = K2_centre
      \<and> (apply_cltn2 q J' = north \<or> apply_cltn2 q J' = south)"
      by (simp add: exI [of _ ?J''])
  next
    assume "apply_cltn2 p ?J'' \<noteq> east"
    with `apply_cltn2 p ?J'' = east \<or> apply_cltn2 p ?J'' = west`
    have "apply_cltn2 p ?J'' = west" by simp

    let ?J' = "cltn2_compose ?J'' meridian_reflect"
    from `is_K2_isometry ?J''` and meridian_reflect_K2_isometry
    have "is_K2_isometry ?J'" by (rule cltn2_compose_is_K2_isometry)
    moreover
    from `apply_cltn2 p ?J'' = west` and `apply_cltn2 a ?J'' = K2_centre`
      and `apply_cltn2 q ?J'' = north \<or> apply_cltn2 q ?J'' = south`
      and compass_reflect_compass
    have "apply_cltn2 p ?J' = east" and "apply_cltn2 a ?J' = K2_centre"
      and "apply_cltn2 q ?J' = north \<or> apply_cltn2 q ?J' = south"
      by (auto simp add: cltn2.act_act [simplified, symmetric])
    ultimately
    show "\<exists> J'. is_K2_isometry J' \<and> apply_cltn2 p J' = east
      \<and> apply_cltn2 a J' = K2_centre
      \<and> (apply_cltn2 q J' = north \<or> apply_cltn2 q J' = south)"
      by (simp add: exI [of _ ?J'])
  qed
  then obtain J' where "is_K2_isometry J'" and "apply_cltn2 p J' = east"
    and "apply_cltn2 a J' = K2_centre"
    and "apply_cltn2 q J' = north \<or> apply_cltn2 q J' = south"
    by auto

  show "\<exists> J. is_K2_isometry J \<and> apply_cltn2 p J = east
    \<and> apply_cltn2 a J = K2_centre \<and> apply_cltn2 q J = north"
  proof cases
    assume "apply_cltn2 q J' = north"
    with `is_K2_isometry J'` and `apply_cltn2 p J' = east`
      and `apply_cltn2 a J' = K2_centre`
    show "\<exists> J. is_K2_isometry J \<and> apply_cltn2 p J = east
      \<and> apply_cltn2 a J = K2_centre \<and> apply_cltn2 q J = north"
      by (simp add: exI [of _ J'])
  next
    assume "apply_cltn2 q J' \<noteq> north"
    with `apply_cltn2 q J' = north \<or> apply_cltn2 q J' = south`
    have "apply_cltn2 q J' = south" by simp

    let ?J = "cltn2_compose J' equator_reflect"
    from `is_K2_isometry J'` and equator_reflect_K2_isometry
    have "is_K2_isometry ?J" by (rule cltn2_compose_is_K2_isometry)
    moreover
    from `apply_cltn2 p J' = east` and `apply_cltn2 a J' = K2_centre`
      and `apply_cltn2 q J' = south` and compass_reflect_compass
    have "apply_cltn2 p ?J = east" and "apply_cltn2 a ?J = K2_centre"
      and "apply_cltn2 q ?J = north"
      by (auto simp add: cltn2.act_act [simplified, symmetric])
    ultimately
    show "\<exists> J. is_K2_isometry J \<and> apply_cltn2 p J = east
      \<and> apply_cltn2 a J = K2_centre \<and> apply_cltn2 q J = north"
      by (simp add: exI [of _ ?J])
  qed
qed

lemma right_angle_to_right_angle:
  assumes "right_angle p a q" and "right_angle r b s"
  shows "\<exists> J. is_K2_isometry J
  \<and> apply_cltn2 p J = r \<and> apply_cltn2 a J = b \<and> apply_cltn2 q J = s"
proof -
  from `right_angle p a q` and right_angle_to_compass [of p a q]
  obtain H where "is_K2_isometry H" and "apply_cltn2 p H = east"
    and "apply_cltn2 a H = K2_centre" and "apply_cltn2 q H = north"
    by auto

  from `right_angle r b s` and right_angle_to_compass [of r b s]
  obtain K where "is_K2_isometry K" and "apply_cltn2 r K = east"
    and "apply_cltn2 b K = K2_centre" and "apply_cltn2 s K = north"
    by auto

  let ?Ki = "cltn2_inverse K"
  let ?J = "cltn2_compose H ?Ki"
  from `is_K2_isometry H` and `is_K2_isometry K`
  have "is_K2_isometry ?J"
    by (simp add: cltn2_inverse_is_K2_isometry cltn2_compose_is_K2_isometry)

  from `apply_cltn2 r K = east` and `apply_cltn2 b K = K2_centre`
    and `apply_cltn2 s K = north`
  have "apply_cltn2 east ?Ki = r" and "apply_cltn2 K2_centre ?Ki = b"
    and "apply_cltn2 north ?Ki = s"
    by (simp_all add: cltn2.act_inv_iff [simplified])
  with `apply_cltn2 p H = east` and `apply_cltn2 a H = K2_centre`
    and `apply_cltn2 q H = north`
  have "apply_cltn2 p ?J = r" and "apply_cltn2 a ?J = b"
    and "apply_cltn2 q ?J = s"
    by (simp_all add: cltn2.act_act [simplified,symmetric])
  with `is_K2_isometry ?J`
  show "\<exists> J. is_K2_isometry J
    \<and> apply_cltn2 p J = r \<and> apply_cltn2 a J = b \<and> apply_cltn2 q J = s"
    by (simp add: exI [of _ ?J])
qed

subsection {* Functions of distance *}

definition exp_2dist :: "proj2 \<Rightarrow> proj2 \<Rightarrow> real" where
  "exp_2dist a b
  \<equiv> if a = b
  then 1
  else cross_ratio (endpoint_in_S a b) (endpoint_in_S b a) a b"

definition cosh_dist :: "proj2 \<Rightarrow> proj2 \<Rightarrow> real" where
  "cosh_dist a b \<equiv> (sqrt (exp_2dist a b) + sqrt (1 / (exp_2dist a b))) / 2"

lemma exp_2dist_formula:
  assumes "a \<noteq> 0" and "b \<noteq> 0" and "proj2_abs a \<in> hyp2" (is "?pa \<in> hyp2")
  and "proj2_abs b \<in> hyp2" (is "?pb \<in> hyp2")
  shows "exp_2dist (proj2_abs a) (proj2_abs b)
    = (a \<bullet> (M *v b) + sqrt (quarter_discrim a b))
      / (a \<bullet> (M *v b) - sqrt (quarter_discrim a b))
  \<or> exp_2dist (proj2_abs a) (proj2_abs b)
    = (a \<bullet> (M *v b) - sqrt (quarter_discrim a b))
      / (a \<bullet> (M *v b) + sqrt (quarter_discrim a b))"
  (is "?e2d = (?aMb + ?sqd) / (?aMb - ?sqd)
    \<or> ?e2d = (?aMb - ?sqd) / (?aMb + ?sqd)")
proof cases
  assume "?pa = ?pb"
  hence "?e2d = 1" by (unfold exp_2dist_def, simp)

  from `?pa = ?pb`
  have "quarter_discrim a b = 0" by (rule quarter_discrim_self_zero)
  hence "?sqd = 0" by simp

  from `proj2_abs a = proj2_abs b` and `b \<noteq> 0` and proj2_abs_abs_mult
  obtain k where "a = k *\<^sub>R b" by auto

  from `b \<noteq> 0` and `proj2_abs b \<in> hyp2`
  have "b \<bullet> (M *v b) < 0" by (subst K2_abs [symmetric])
  with `a \<noteq> 0` and `a = k *\<^sub>R b` have "?aMb \<noteq> 0" by simp
  with `?e2d = 1` and `?sqd = 0`
  show "?e2d = (?aMb + ?sqd) / (?aMb - ?sqd)
    \<or> ?e2d = (?aMb - ?sqd) / (?aMb + ?sqd)"
    by simp
next
  assume "?pa \<noteq> ?pb"
  let ?l = "proj2_line_through ?pa ?pb"
  have "proj2_incident ?pa ?l" and "proj2_incident ?pb ?l"
    by (rule proj2_line_through_incident)+
  with `a \<noteq> 0` and `b \<noteq> 0` and `?pa \<noteq> ?pb`
  have "proj2_incident (S_intersection1 a b) ?l" (is "proj2_incident ?Si1 ?l")
    and "proj2_incident (S_intersection2 a b) ?l" (is "proj2_incident ?Si2 ?l")
    by (rule S_intersections_incident)+
  with `proj2_incident ?pa ?l` and `proj2_incident ?pb ?l`
  have "proj2_set_Col {?pa,?pb,?Si1,?Si2}" by (unfold proj2_set_Col_def, auto)

  have "{?pa,?pb,?Si2,?Si1} = {?pa,?pb,?Si1,?Si2}" by auto

  from `a \<noteq> 0` and `b \<noteq> 0` and `?pa \<noteq> ?pb` and `?pa \<in> hyp2`
  have "?Si1 \<in> S" and "?Si2 \<in> S"
    by (simp_all add: S_intersections_in_S)
  with `?pa \<in> hyp2` and `?pb \<in> hyp2`
  have "?Si1 \<noteq> ?pa" and "?Si2 \<noteq> ?pa" and "?Si1 \<noteq> ?pb" and "?Si2 \<noteq> ?pb"
    by (simp_all add: hyp2_S_not_equal [symmetric])
  with `proj2_set_Col {?pa,?pb,?Si1,?Si2}` and `?pa \<noteq> ?pb`
  have "cross_ratio_correct ?pa ?pb ?Si1 ?Si2"
    and "cross_ratio_correct ?pa ?pb ?Si2 ?Si1"
    unfolding cross_ratio_correct_def
    by (simp_all add: `{?pa,?pb,?Si2,?Si1} = {?pa,?pb,?Si1,?Si2}`)

  from `a \<noteq> 0` and `b \<noteq> 0` and `?pa \<noteq> ?pb` and `?pa \<in> hyp2`
  have "?Si1 \<noteq> ?Si2" by (simp add: S_intersections_distinct)
  with `cross_ratio_correct ?pa ?pb ?Si1 ?Si2`
    and `cross_ratio_correct ?pa ?pb ?Si2 ?Si1`
  have "cross_ratio ?Si1 ?Si2 ?pa ?pb = cross_ratio ?pa ?pb ?Si1 ?Si2"
    and "cross_ratio ?Si2 ?Si1 ?pa ?pb = cross_ratio ?pa ?pb ?Si2 ?Si1"
    by (simp_all add: cross_ratio_swap_13_24)

  from `a \<noteq> 0` and `proj2_abs a \<in> hyp2`
  have "a \<bullet> (M *v a) < 0" by (subst K2_abs [symmetric])
  with `a \<noteq> 0` and `b \<noteq> 0` and `?pa \<noteq> ?pb` and cross_ratio_abs [of a b 1 1]
  have "cross_ratio ?pa ?pb ?Si1 ?Si2 = (-?aMb - ?sqd) / (-?aMb + ?sqd)"
    by (unfold S_intersections_defs S_intersection_coeffs_defs, simp)
  with times_divide_times_eq [of "-1" "-1" "-?aMb - ?sqd" "-?aMb + ?sqd"]
  have "cross_ratio ?pa ?pb ?Si1 ?Si2 = (?aMb + ?sqd) / (?aMb - ?sqd)" by (simp add: ac_simps)
  with `cross_ratio ?Si1 ?Si2 ?pa ?pb = cross_ratio ?pa ?pb ?Si1 ?Si2`
  have "cross_ratio ?Si1 ?Si2 ?pa ?pb = (?aMb + ?sqd) / (?aMb - ?sqd)" by simp

  from `cross_ratio ?pa ?pb ?Si1 ?Si2 = (?aMb + ?sqd) / (?aMb - ?sqd)`
    and cross_ratio_swap_34 [of ?pa ?pb ?Si2 ?Si1]
  have "cross_ratio ?pa ?pb ?Si2 ?Si1 = (?aMb - ?sqd) / (?aMb + ?sqd)" by simp
  with `cross_ratio ?Si2 ?Si1 ?pa ?pb = cross_ratio ?pa ?pb ?Si2 ?Si1`
  have "cross_ratio ?Si2 ?Si1 ?pa ?pb = (?aMb - ?sqd) / (?aMb + ?sqd)" by simp

  from `a \<noteq> 0` and `b \<noteq> 0` and `?pa \<noteq> ?pb` and `?pa \<in> hyp2` and `?pb \<in> hyp2`
  have "(?Si1 = endpoint_in_S ?pa ?pb \<and> ?Si2 = endpoint_in_S ?pb ?pa)
    \<or> (?Si2 = endpoint_in_S ?pa ?pb \<and> ?Si1 = endpoint_in_S ?pb ?pa)"
    by (simp add: S_intersections_endpoints_in_S)
  with `cross_ratio ?Si1 ?Si2 ?pa ?pb = (?aMb + ?sqd) / (?aMb - ?sqd)`
    and `cross_ratio ?Si2 ?Si1 ?pa ?pb = (?aMb - ?sqd) / (?aMb + ?sqd)`
    and `?pa \<noteq> ?pb`
  show "?e2d = (?aMb + ?sqd) / (?aMb - ?sqd)
    \<or> ?e2d = (?aMb - ?sqd) / (?aMb + ?sqd)"
    by (unfold exp_2dist_def, auto)
qed

lemma cosh_dist_formula:
  assumes "a \<noteq> 0" and "b \<noteq> 0" and "proj2_abs a \<in> hyp2" (is "?pa \<in> hyp2")
  and "proj2_abs b \<in> hyp2" (is "?pb \<in> hyp2")
  shows "cosh_dist (proj2_abs a) (proj2_abs b)
  = \<bar>a \<bullet> (M *v b)\<bar> / sqrt (a \<bullet> (M *v a) * (b \<bullet> (M *v b)))"
  (is "cosh_dist ?pa ?pb = \<bar>?aMb\<bar> / sqrt (?aMa * ?bMb)")
proof -
  let ?qd = "quarter_discrim a b"
  let ?sqd = "sqrt ?qd"
  let ?e2d = "exp_2dist ?pa ?pb"
  from assms
  have "?e2d = (?aMb + ?sqd) / (?aMb - ?sqd)
    \<or> ?e2d = (?aMb - ?sqd) / (?aMb + ?sqd)"
    by (rule exp_2dist_formula)
  hence "cosh_dist ?pa ?pb
    = (sqrt ((?aMb + ?sqd) / (?aMb - ?sqd))
    + sqrt ((?aMb - ?sqd) / (?aMb + ?sqd)))
    / 2"
    by (unfold cosh_dist_def, auto)

  have "?qd \<ge> 0"
  proof cases
    assume "?pa = ?pb"
    thus "?qd \<ge> 0" by (simp add: quarter_discrim_self_zero)
  next
    assume "?pa \<noteq> ?pb"
    with `a \<noteq> 0` and `b \<noteq> 0` and `?pa \<in> hyp2`
    have "?qd > 0" by (simp add: quarter_discrim_positive)
    thus "?qd \<ge> 0" by simp
  qed
  with real_sqrt_pow2 [of ?qd] have "?sqd\<^sup>2 = ?qd" by simp
  hence "(?aMb + ?sqd) * (?aMb - ?sqd) = ?aMa * ?bMb"
    by (unfold quarter_discrim_def, simp add: algebra_simps power2_eq_square)

  from times_divide_times_eq [of
    "?aMb + ?sqd" "?aMb + ?sqd" "?aMb + ?sqd" "?aMb - ?sqd"]
  have "(?aMb + ?sqd) / (?aMb - ?sqd)
    = (?aMb + ?sqd)\<^sup>2 / ((?aMb + ?sqd) * (?aMb - ?sqd))"
    by (simp add: power2_eq_square)
  with `(?aMb + ?sqd) * (?aMb - ?sqd) = ?aMa * ?bMb`
  have "(?aMb + ?sqd) / (?aMb - ?sqd) = (?aMb + ?sqd)\<^sup>2 / (?aMa * ?bMb)" by simp
  hence "sqrt ((?aMb + ?sqd) / (?aMb - ?sqd))
    = \<bar>?aMb + ?sqd\<bar> / sqrt (?aMa * ?bMb)"
    by (simp add: real_sqrt_divide)

  from times_divide_times_eq [of
    "?aMb + ?sqd" "?aMb - ?sqd" "?aMb - ?sqd" "?aMb - ?sqd"]
  have "(?aMb - ?sqd) / (?aMb + ?sqd)
    = (?aMb - ?sqd)\<^sup>2 / ((?aMb + ?sqd) * (?aMb - ?sqd))"
    by (simp add: power2_eq_square)
  with `(?aMb + ?sqd) * (?aMb - ?sqd) = ?aMa * ?bMb`
  have "(?aMb - ?sqd) / (?aMb + ?sqd) = (?aMb - ?sqd)\<^sup>2 / (?aMa * ?bMb)" by simp
  hence "sqrt ((?aMb - ?sqd) / (?aMb + ?sqd))
    = \<bar>?aMb - ?sqd\<bar> / sqrt (?aMa * ?bMb)"
    by (simp add: real_sqrt_divide)

  from `a \<noteq> 0` and `b \<noteq> 0` and `?pa \<in> hyp2` and `?pb \<in> hyp2`
  have "?aMa < 0" and "?bMb < 0"
    by (simp_all add: K2_imp_M_neg)
  with `(?aMb + ?sqd) * (?aMb - ?sqd) = ?aMa * ?bMb`
  have "(?aMb + ?sqd) * (?aMb - ?sqd) > 0" by (simp add: mult_neg_neg)
  hence "?aMb + ?sqd \<noteq> 0" and "?aMb - ?sqd \<noteq> 0" by auto
  hence "sgn (?aMb + ?sqd) \<in> {-1,1}" and "sgn (?aMb - ?sqd) \<in> {-1,1}"
    by (simp_all add: sgn_real_def)

  from `(?aMb + ?sqd) * (?aMb - ?sqd) > 0`
  have "sgn ((?aMb + ?sqd) * (?aMb - ?sqd)) = 1" by simp
  hence "sgn (?aMb + ?sqd) * sgn (?aMb - ?sqd) = 1" by (simp add: sgn_mult)
  with `sgn (?aMb + ?sqd) \<in> {-1,1}` and `sgn (?aMb - ?sqd) \<in> {-1,1}`
  have "sgn (?aMb + ?sqd) = sgn (?aMb - ?sqd)" by auto
  with abs_plus [of "?aMb + ?sqd" "?aMb - ?sqd"]
  have "\<bar>?aMb + ?sqd\<bar> + \<bar>?aMb - ?sqd\<bar> = 2 * \<bar>?aMb\<bar>" by simp
  with `sqrt ((?aMb + ?sqd) / (?aMb - ?sqd))
    = \<bar>?aMb + ?sqd\<bar> / sqrt (?aMa * ?bMb)`
    and `sqrt ((?aMb - ?sqd) / (?aMb + ?sqd))
    = \<bar>?aMb - ?sqd\<bar> / sqrt (?aMa * ?bMb)`
    and add_divide_distrib [of
    "\<bar>?aMb + ?sqd\<bar>" "\<bar>?aMb - ?sqd\<bar>" "sqrt (?aMa * ?bMb)"]
  have "sqrt ((?aMb + ?sqd) / (?aMb - ?sqd))
    + sqrt ((?aMb - ?sqd) / (?aMb + ?sqd))
    = 2 * \<bar>?aMb\<bar> / sqrt (?aMa * ?bMb)"
    by simp
  with `cosh_dist ?pa ?pb
    = (sqrt ((?aMb + ?sqd) / (?aMb - ?sqd))
    + sqrt ((?aMb - ?sqd) / (?aMb + ?sqd)))
    / 2`
  show "cosh_dist ?pa ?pb = \<bar>?aMb\<bar> / sqrt (?aMa * ?bMb)" by simp
qed

lemma cosh_dist_perp_special_case:
  assumes "\<bar>x\<bar> < 1" and "\<bar>y\<bar> < 1"
  shows "cosh_dist (proj2_abs (vector [x,0,1])) (proj2_abs (vector [0,y,1]))
  = (cosh_dist K2_centre (proj2_abs (vector [x,0,1])))
  * (cosh_dist K2_centre (proj2_abs (vector [0,y,1])))"
  (is "cosh_dist ?pa ?pb = (cosh_dist ?po ?pa) * (cosh_dist ?po ?pb)")
proof -
  have "vector [x,0,1] \<noteq> (0::real^3)" (is "?a \<noteq> 0")
    and "vector [0,y,1] \<noteq> (0::real^3)" (is "?b \<noteq> 0")
    by (unfold vector_def, simp_all add: vec_eq_iff forall_3)

  have "?a \<bullet> (M *v ?a) = x\<^sup>2 - 1" (is "?aMa = x\<^sup>2 - 1")
    and "?b \<bullet> (M *v ?b) = y\<^sup>2 - 1" (is "?bMb = y\<^sup>2 - 1")
    unfolding vector_def and M_def and inner_vec_def
      and matrix_vector_mult_def
    by (simp_all add: sum_3 power2_eq_square)
  with `\<bar>x\<bar> < 1` and `\<bar>y\<bar> < 1`
  have "?aMa < 0" and "?bMb < 0" by (simp_all add: abs_square_less_1)
  hence "?pa \<in> hyp2" and "?pb \<in> hyp2"
    by (simp_all add: M_neg_imp_K2)
  with `?a \<noteq> 0` and `?b \<noteq> 0`
  have "cosh_dist ?pa ?pb = \<bar>?a \<bullet> (M *v ?b)\<bar> / sqrt (?aMa * ?bMb)"
    (is "cosh_dist ?pa ?pb = \<bar>?aMb\<bar> / sqrt (?aMa * ?bMb)")
    by (rule cosh_dist_formula)
  also from `?aMa = x\<^sup>2 - 1` and `?bMb = y\<^sup>2 - 1`
  have "\<dots> = \<bar>?aMb\<bar> / sqrt ((x\<^sup>2 - 1) * (y\<^sup>2 - 1))" by simp
  finally have "cosh_dist ?pa ?pb = 1 / sqrt ((1 - x\<^sup>2) * (1 - y\<^sup>2))"
    unfolding vector_def and M_def and inner_vec_def
      and matrix_vector_mult_def
    by (simp add: sum_3 algebra_simps)

  let ?o = "vector [0,0,1]"
  let ?oMa = "?o \<bullet> (M *v ?a)"
  let ?oMb = "?o \<bullet> (M *v ?b)"
  let ?oMo = "?o \<bullet> (M *v ?o)"
  from K2_centre_non_zero and `?a \<noteq> 0` and `?b \<noteq> 0`
    and K2_centre_in_K2 and `?pa \<in> hyp2` and `?pb \<in> hyp2`
    and cosh_dist_formula [of ?o]
  have "cosh_dist ?po ?pa = \<bar>?oMa\<bar> / sqrt (?oMo * ?aMa)"
    and "cosh_dist ?po ?pb = \<bar>?oMb\<bar> / sqrt (?oMo * ?bMb)"
    by (unfold K2_centre_def, simp_all)
  hence "cosh_dist ?po ?pa = 1 / sqrt (1 - x\<^sup>2)"
    and "cosh_dist ?po ?pb = 1 / sqrt (1 - y\<^sup>2)"
    unfolding vector_def and M_def and inner_vec_def
      and matrix_vector_mult_def
    by (simp_all add: sum_3 power2_eq_square)
  with `cosh_dist ?pa ?pb = 1 / sqrt ((1 - x\<^sup>2) * (1 - y\<^sup>2))`
  show "cosh_dist ?pa ?pb = cosh_dist ?po ?pa * cosh_dist ?po ?pb"
    by (simp add: real_sqrt_mult)
qed

lemma K2_isometry_cross_ratio_endpoints_in_S:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "is_K2_isometry J" and "a \<noteq> b"
  shows "cross_ratio (apply_cltn2 (endpoint_in_S a b) J)
  (apply_cltn2 (endpoint_in_S b a) J) (apply_cltn2 a J) (apply_cltn2 b J)
  = cross_ratio (endpoint_in_S a b) (endpoint_in_S b a) a b"
  (is "cross_ratio ?pJ ?qJ ?aJ ?bJ = cross_ratio ?p ?q a b")
proof -
  let ?l = "proj2_line_through a b"
  have "proj2_incident a ?l" and "proj2_incident b ?l"
    by (rule proj2_line_through_incident)+
  with `a \<noteq> b` and `a \<in> hyp2` and `b \<in> hyp2`
  have "proj2_incident ?p ?l" and "proj2_incident ?q ?l"
    by (simp_all add: endpoint_in_S_incident)
  with `proj2_incident a ?l` and `proj2_incident b ?l`
  have "proj2_set_Col {?p,?q,a,b}"
    by (unfold proj2_set_Col_def) (simp add: exI [of _ ?l])

  from `a \<noteq> b` and `a \<in> hyp2` and `b \<in> hyp2`
  have "?p \<noteq> ?q" by (simp add: endpoint_in_S_swap)

  from `a \<in> hyp2` and `b \<in> hyp2` have "?p \<in> S" by (simp add: endpoint_in_S)
  with `a \<in> hyp2` and `b \<in> hyp2`
  have "a \<noteq> ?p" and "b \<noteq> ?p" by (simp_all add: hyp2_S_not_equal)
  with `proj2_set_Col {?p,?q,a,b}` and `?p \<noteq> ?q`
  show "cross_ratio ?pJ ?qJ ?aJ ?bJ = cross_ratio ?p ?q a b"
    by (rule cross_ratio_cltn2)
qed

lemma K2_isometry_exp_2dist:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "is_K2_isometry J"
  shows "exp_2dist (apply_cltn2 a J) (apply_cltn2 b J) = exp_2dist a b"
  (is "exp_2dist ?aJ ?bJ = _")
proof cases
  assume "a = b"
  thus "exp_2dist ?aJ ?bJ = exp_2dist a b" by (unfold exp_2dist_def) simp
next
  assume "a \<noteq> b"
  with apply_cltn2_injective have "?aJ \<noteq> ?bJ" by fast

  let ?p = "endpoint_in_S a b"
  let ?q = "endpoint_in_S b a"
  let ?aJ = "apply_cltn2 a J"
    and ?bJ = "apply_cltn2 b J"
    and ?pJ = "apply_cltn2 ?p J"
    and ?qJ = "apply_cltn2 ?q J"
  from `a \<noteq> b` and `a \<in> hyp2` and `b \<in> hyp2` and `is_K2_isometry J`
  have "endpoint_in_S ?aJ ?bJ = ?pJ" and "endpoint_in_S ?bJ ?aJ = ?qJ"
    by (simp_all add: K2_isometry_endpoint_in_S)

  from assms and `a \<noteq> b`
  have "cross_ratio ?pJ ?qJ ?aJ ?bJ = cross_ratio ?p ?q a b"
    by (rule K2_isometry_cross_ratio_endpoints_in_S)
  with `endpoint_in_S ?aJ ?bJ = ?pJ` and `endpoint_in_S ?bJ ?aJ = ?qJ`
    and `a \<noteq> b` and `?aJ \<noteq> ?bJ`
  show "exp_2dist ?aJ ?bJ = exp_2dist a b" by (unfold exp_2dist_def) simp
qed

lemma K2_isometry_cosh_dist:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "is_K2_isometry J"
  shows "cosh_dist (apply_cltn2 a J) (apply_cltn2 b J) = cosh_dist a b"
  using assms
  by (unfold cosh_dist_def) (simp add: K2_isometry_exp_2dist)

lemma cosh_dist_perp:
  assumes "M_perp l m" and "a \<in> hyp2" and "b \<in> hyp2" and "c \<in> hyp2"
  and "proj2_incident a l" and "proj2_incident b l"
  and "proj2_incident b m" and "proj2_incident c m"
  shows "cosh_dist a c = cosh_dist b a * cosh_dist b c"
proof -
  from `M_perp l m` and `b \<in> hyp2` and `proj2_incident b l`
    and `proj2_incident b m` and M_perp_to_compass [of l m b b]
  obtain J where "is_K2_isometry J" and "apply_cltn2_line equator J = l"
    and "apply_cltn2_line meridian J = m"
    by auto

  let ?Ji = "cltn2_inverse J"
  let ?aJi = "apply_cltn2 a ?Ji"
  let ?bJi = "apply_cltn2 b ?Ji"
  let ?cJi = "apply_cltn2 c ?Ji"
  from `apply_cltn2_line equator J = l` and `apply_cltn2_line meridian J = m`
    and `proj2_incident a l` and `proj2_incident b l`
    and `proj2_incident b m` and `proj2_incident c m`
  have "proj2_incident ?aJi equator" and "proj2_incident ?bJi equator"
    and "proj2_incident ?bJi meridian" and "proj2_incident ?cJi meridian"
    by (auto simp add: apply_cltn2_incident)

  from `is_K2_isometry J`
  have "is_K2_isometry ?Ji" by (rule cltn2_inverse_is_K2_isometry)
  with `a \<in> hyp2` and `c \<in> hyp2`
  have "?aJi \<in> hyp2" and "?cJi \<in> hyp2"
    by (simp_all add: statement60_one_way)

  from `?aJi \<in> hyp2` and `proj2_incident ?aJi equator`
    and on_equator_in_hyp2_rep
  obtain x where "\<bar>x\<bar> < 1" and "?aJi = proj2_abs (vector [x,0,1])" by auto
  moreover
  from `?cJi \<in> hyp2` and `proj2_incident ?cJi meridian`
    and on_meridian_in_hyp2_rep
  obtain y where "\<bar>y\<bar> < 1" and "?cJi = proj2_abs (vector [0,y,1])" by auto
  moreover
  from `proj2_incident ?bJi equator` and `proj2_incident ?bJi meridian`
  have "?bJi = K2_centre" by (rule on_equator_meridian_is_K2_centre)
  ultimately
  have "cosh_dist ?aJi ?cJi = cosh_dist ?bJi ?aJi * cosh_dist ?bJi ?cJi"
    by (simp add: cosh_dist_perp_special_case)
  with `a \<in> hyp2` and `b \<in> hyp2` and `c \<in> hyp2` and `is_K2_isometry ?Ji`
  show "cosh_dist a c = cosh_dist b a * cosh_dist b c"
    by (simp add: K2_isometry_cosh_dist)
qed

lemma are_endpoints_in_S_ordered_cross_ratio:
  assumes "are_endpoints_in_S p q a b"
  and "B\<^sub>\<real> (cart2_pt a) (cart2_pt b) (cart2_pt p)" (is "B\<^sub>\<real> ?ca ?cb ?cp")
  shows "cross_ratio p q a b \<ge> 1"
proof -
  from `are_endpoints_in_S p q a b`
  have "p \<noteq> q" and "p \<in> S" and "q \<in> S" and "a \<in> hyp2" and "b \<in> hyp2"
    and "proj2_set_Col {p,q,a,b}"
     by (unfold are_endpoints_in_S_def) simp_all

   from `a \<in> hyp2` and `b \<in> hyp2` and `p \<in> S` and `q \<in> S`
   have "z_non_zero a" and "z_non_zero b" and "z_non_zero p" and "z_non_zero q"
     by (simp_all add: hyp2_S_z_non_zero)
  hence "proj2_abs (cart2_append1 p) = p" (is "proj2_abs ?cp1 = p")
    and "proj2_abs (cart2_append1 q) = q" (is "proj2_abs ?cq1 = q")
    and "proj2_abs (cart2_append1 a) = a" (is "proj2_abs ?ca1 = a")
    and "proj2_abs (cart2_append1 b) = b" (is "proj2_abs ?cb1 = b")
    by (simp_all add: proj2_abs_cart2_append1)

   from `b \<in> hyp2` and `p \<in> S` have "b \<noteq> p" by (rule hyp2_S_not_equal)
   with `z_non_zero a` and `z_non_zero b` and `z_non_zero p`
     and `B\<^sub>\<real> ?ca ?cb ?cp` and cart2_append1_between_right_strict [of a b p]
   obtain j where "j \<ge> 0" and "j < 1" and "?cb1 = j *\<^sub>R ?cp1 + (1-j) *\<^sub>R ?ca1"
     by auto

   from `proj2_set_Col {p,q,a,b}`
   obtain l where "proj2_incident q l" and "proj2_incident p l"
     and "proj2_incident a l"
     by (unfold proj2_set_Col_def) auto
   with `p \<noteq> q` and `q \<in> S` and `p \<in> S` and `a \<in> hyp2`
     and S_hyp2_S_cart2_append1 [of q p a l]
   obtain k where "k > 0" and "k < 1" and "?ca1 = k *\<^sub>R ?cp1 + (1-k) *\<^sub>R ?cq1"
     by auto

   from `z_non_zero p` and `z_non_zero q`
   have "?cp1 \<noteq> 0" and "?cq1 \<noteq> 0" by (simp_all add: cart2_append1_non_zero)

   from `p \<noteq> q` and `proj2_abs ?cp1 = p` and `proj2_abs ?cq1 = q`
   have "proj2_abs ?cp1 \<noteq> proj2_abs ?cq1" by simp

   from `k < 1` have "1-k \<noteq> 0" by simp
   with `j < 1` have "(1-j)*(1-k) \<noteq> 0" by simp

   from `j < 1` and `k > 0` have "(1-j)*k > 0" by simp

   from `?cb1 = j *\<^sub>R ?cp1 + (1-j) *\<^sub>R ?ca1`
   have "?cb1 = (j+(1-j)*k) *\<^sub>R ?cp1 + ((1-j)*(1-k)) *\<^sub>R ?cq1"
     by (unfold `?ca1 = k *\<^sub>R ?cp1 + (1-k) *\<^sub>R ?cq1`) (simp add: algebra_simps)
   with `?ca1 = k *\<^sub>R ?cp1 + (1-k) *\<^sub>R ?cq1`
   have "proj2_abs ?ca1 = proj2_abs (k *\<^sub>R ?cp1 + (1-k) *\<^sub>R ?cq1)"
     and "proj2_abs ?cb1
     = proj2_abs ((j+(1-j)*k) *\<^sub>R ?cp1 + ((1-j)*(1-k)) *\<^sub>R ?cq1)"
     by simp_all
   with `proj2_abs ?ca1 = a` and `proj2_abs ?cb1 = b`
   have "a = proj2_abs (k *\<^sub>R ?cp1 + (1-k) *\<^sub>R ?cq1)"
     and "b = proj2_abs ((j+(1-j)*k) *\<^sub>R ?cp1 + ((1-j)*(1-k)) *\<^sub>R ?cq1)"
     by simp_all
   with `proj2_abs ?cp1 = p` and `proj2_abs ?cq1 = q`
   have "cross_ratio p q a b
     = cross_ratio (proj2_abs ?cp1) (proj2_abs ?cq1)
     (proj2_abs (k *\<^sub>R ?cp1 + (1-k) *\<^sub>R ?cq1))
     (proj2_abs ((j+(1-j)*k) *\<^sub>R ?cp1 + ((1-j)*(1-k)) *\<^sub>R ?cq1))"
     by simp
   also from `?cp1 \<noteq> 0` and `?cq1 \<noteq> 0` and `proj2_abs ?cp1 \<noteq> proj2_abs ?cq1`
     and `1-k \<noteq> 0` and `(1-j)*(1-k) \<noteq> 0`
   have "\<dots> = (1-k)*(j+(1-j)*k) / (k*((1-j)*(1-k)))" by (rule cross_ratio_abs)
   also from `1-k \<noteq> 0` have "\<dots> = (j+(1-j)*k) / ((1-j)*k)" by simp
   also from `j \<ge> 0` and `(1-j)*k > 0` have "\<dots> \<ge> 1" by simp
   finally show "cross_ratio p q a b \<ge> 1" .
qed

lemma cross_ratio_S_S_hyp2_hyp2_positive:
  assumes "are_endpoints_in_S p q a b"
  shows "cross_ratio p q a b > 0"
proof cases
  assume "B\<^sub>\<real> (cart2_pt p) (cart2_pt b) (cart2_pt a)"
  hence "B\<^sub>\<real> (cart2_pt a) (cart2_pt b) (cart2_pt p)"
    by (rule real_euclid.th3_2)
  with assms have "cross_ratio p q a b \<ge> 1"
    by (rule are_endpoints_in_S_ordered_cross_ratio)
  thus "cross_ratio p q a b > 0" by simp
next
  assume "\<not> B\<^sub>\<real> (cart2_pt p) (cart2_pt b) (cart2_pt a)" (is "\<not> B\<^sub>\<real> ?cp ?cb ?ca")

  from `are_endpoints_in_S p q a b`
  have "are_endpoints_in_S p q b a" by (rule are_endpoints_in_S_swap_34)

  from `are_endpoints_in_S p q a b`
  have "p \<in> S" and "a \<in> hyp2" and "b \<in> hyp2" and "proj2_set_Col {p,q,a,b}"
    by (unfold are_endpoints_in_S_def) simp_all

  from `proj2_set_Col {p,q,a,b}`
  have "proj2_set_Col {p,a,b}"
    by (simp add: proj2_subset_Col [of "{p,a,b}" "{p,q,a,b}"])
  hence "proj2_Col p a b" by (subst proj2_Col_iff_set_Col)
  with `p \<in> S` and `a \<in> hyp2` and `b \<in> hyp2`
  have "B\<^sub>\<real> ?cp ?ca ?cb \<or> B\<^sub>\<real> ?cp ?cb ?ca" by (simp add: S_at_edge)
  with `\<not> B\<^sub>\<real> ?cp ?cb ?ca` have "B\<^sub>\<real> ?cp ?ca ?cb" by simp
  hence "B\<^sub>\<real> ?cb ?ca ?cp" by (rule real_euclid.th3_2)
  with `are_endpoints_in_S p q b a`
  have "cross_ratio p q b a \<ge> 1"
    by (rule are_endpoints_in_S_ordered_cross_ratio)
  thus "cross_ratio p q a b > 0" by (subst cross_ratio_swap_34) simp
qed

lemma cosh_dist_general:
  assumes "are_endpoints_in_S p q a b"
  shows "cosh_dist a b
  = (sqrt (cross_ratio p q a b) + 1 / sqrt (cross_ratio p q a b)) / 2"
proof -
  from `are_endpoints_in_S p q a b`
  have "p \<noteq> q" and "p \<in> S" and "q \<in> S" and "a \<in> hyp2" and "b \<in> hyp2"
    and "proj2_set_Col {p,q,a,b}"
    by (unfold are_endpoints_in_S_def) simp_all

  from `a \<in> hyp2` and `b \<in> hyp2` and `p \<in> S` and `q \<in> S`
  have "a \<noteq> p" and "a \<noteq> q" and "b \<noteq> p" and "b \<noteq> q"
    by (simp_all add: hyp2_S_not_equal)

  show "cosh_dist a b
    = (sqrt (cross_ratio p q a b) + 1 / sqrt (cross_ratio p q a b)) / 2"
  proof cases
    assume "a = b"
    hence "cosh_dist a b = 1" by (unfold cosh_dist_def exp_2dist_def) simp

    from `proj2_set_Col {p,q,a,b}`
    have "proj2_Col p q a" by (unfold `a = b`) (simp add: proj2_Col_iff_set_Col)
    with `p \<noteq> q` and `a \<noteq> p` and `a \<noteq> q`
    have "cross_ratio p q a b = 1" by (simp add: `a = b` cross_ratio_equal_1)
    hence "(sqrt (cross_ratio p q a b) + 1 / sqrt (cross_ratio p q a b)) / 2
      = 1"
      by simp
    with `cosh_dist a b = 1`
    show "cosh_dist a b
      = (sqrt (cross_ratio p q a b) + 1 / sqrt (cross_ratio p q a b)) / 2"
      by simp
  next
    assume "a \<noteq> b"

    let ?r = "endpoint_in_S a b"
    let ?s = "endpoint_in_S b a"
    from `a \<noteq> b`
    have "exp_2dist a b = cross_ratio ?r ?s a b" by (unfold exp_2dist_def) simp

    from `a \<noteq> b` and `are_endpoints_in_S p q a b`
    have "(p = ?r \<and> q = ?s) \<or> (q = ?r \<and> p = ?s)" by (rule are_endpoints_in_S)

    show "cosh_dist a b
      = (sqrt (cross_ratio p q a b) + 1 / sqrt (cross_ratio p q a b)) / 2"
    proof cases
      assume "p = ?r \<and> q = ?s"
      with `exp_2dist a b = cross_ratio ?r ?s a b`
      have "exp_2dist a b = cross_ratio p q a b" by simp
      thus "cosh_dist a b
        = (sqrt (cross_ratio p q a b) + 1 / sqrt (cross_ratio p q a b)) / 2"
        by (unfold cosh_dist_def) (simp add: real_sqrt_divide)
    next
      assume "\<not> (p = ?r \<and> q = ?s)"
      with `(p = ?r \<and> q = ?s) \<or> (q = ?r \<and> p = ?s)`
      have "q = ?r" and "p = ?s" by simp_all
      with `exp_2dist a b = cross_ratio ?r ?s a b`
      have "exp_2dist a b = cross_ratio q p a b" by simp

      have "{q,p,a,b} = {p,q,a,b}" by auto
      with `proj2_set_Col {p,q,a,b}` and `p \<noteq> q` and `a \<noteq> p` and `b \<noteq> p`
        and `a \<noteq> q` and `b \<noteq> q`
      have "cross_ratio_correct p q a b" and "cross_ratio_correct q p a b"
        by (unfold cross_ratio_correct_def) simp_all
      hence "cross_ratio q p a b = 1 / (cross_ratio p q a b)"
        by (rule cross_ratio_swap_12)
      with `exp_2dist a b = cross_ratio q p a b`
      have "exp_2dist a b = 1 / (cross_ratio p q a b)" by simp
      thus "cosh_dist a b
        = (sqrt (cross_ratio p q a b) + 1 / sqrt (cross_ratio p q a b)) / 2"
        by (unfold cosh_dist_def) (simp add: real_sqrt_divide)
    qed
  qed
qed

lemma exp_2dist_positive:
  assumes "a \<in> hyp2" and "b \<in> hyp2"
  shows "exp_2dist a b > 0"
proof cases
  assume "a = b"
  thus "exp_2dist a b > 0" by (unfold exp_2dist_def) simp
next
  assume "a \<noteq> b"

  let ?p = "endpoint_in_S a b"
  let ?q = "endpoint_in_S b a"
  from `a \<noteq> b` and `a \<in> hyp2` and `b \<in> hyp2`
  have "are_endpoints_in_S ?p ?q a b"
    by (rule endpoints_in_S_are_endpoints_in_S)
  hence "cross_ratio ?p ?q a b > 0" by (rule cross_ratio_S_S_hyp2_hyp2_positive)
  with `a \<noteq> b` show "exp_2dist a b > 0" by (unfold exp_2dist_def) simp
qed

lemma cosh_dist_at_least_1:
  assumes "a \<in> hyp2" and "b \<in> hyp2"
  shows "cosh_dist a b \<ge> 1"
proof -
  from assms have "exp_2dist a b > 0" by (rule exp_2dist_positive)
  with am_gm2(1) [of "sqrt (exp_2dist a b)" "sqrt (1 / exp_2dist a b)"]
  show "cosh_dist a b \<ge> 1"
    by (unfold cosh_dist_def) (simp add: real_sqrt_mult [symmetric])
qed

lemma cosh_dist_positive:
  assumes "a \<in> hyp2" and "b \<in> hyp2"
  shows "cosh_dist a b > 0"
proof -
  from assms have "cosh_dist a b \<ge> 1" by (rule cosh_dist_at_least_1)
  thus "cosh_dist a b > 0" by simp
qed

lemma cosh_dist_perp_divide:
  assumes "M_perp l m" and "a \<in> hyp2" and "b \<in> hyp2" and "c \<in> hyp2"
  and "proj2_incident a l" and "proj2_incident b l" and "proj2_incident b m"
  and "proj2_incident c m"
  shows "cosh_dist b c = cosh_dist a c / cosh_dist b a"
proof -
  from `b \<in> hyp2` and `a \<in> hyp2`
  have "cosh_dist b a > 0" by (rule cosh_dist_positive)

  from assms
  have "cosh_dist a c = cosh_dist b a * cosh_dist b c" by (rule cosh_dist_perp)
  with `cosh_dist b a > 0`
  show "cosh_dist b c = cosh_dist a c / cosh_dist b a" by simp
qed

lemma real_hyp2_C_cross_ratio_endpoints_in_S:
  assumes "a \<noteq> b" and "a b \<congruent>\<^sub>K c d"
  shows "cross_ratio (endpoint_in_S (Rep_hyp2 a) (Rep_hyp2 b))
  (endpoint_in_S (Rep_hyp2 b) (Rep_hyp2 a)) (Rep_hyp2 a) (Rep_hyp2 b)
  = cross_ratio (endpoint_in_S (Rep_hyp2 c) (Rep_hyp2 d))
  (endpoint_in_S (Rep_hyp2 d) (Rep_hyp2 c)) (Rep_hyp2 c) (Rep_hyp2 d)"
  (is "cross_ratio ?p ?q ?a' ?b' = cross_ratio ?r ?s ?c' ?d'")
proof -
  from `a \<noteq> b` and `a b \<congruent>\<^sub>K c d` have "c \<noteq> d" by (auto simp add: hyp2.A3')
  with `a \<noteq> b` have "?a' \<noteq> ?b'" and "?c' \<noteq> ?d'" by (unfold Rep_hyp2_inject)

  from `a b \<congruent>\<^sub>K c d`
  obtain J where "is_K2_isometry J" and "hyp2_cltn2 a J = c"
    and "hyp2_cltn2 b J = d"
    by (unfold real_hyp2_C_def) auto
  hence "apply_cltn2 ?a' J = ?c'" and "apply_cltn2 ?b' J = ?d'"
    by (simp_all add: Rep_hyp2_cltn2 [symmetric])
  with `?a' \<noteq> ?b'` and `is_K2_isometry J`
  have "apply_cltn2 ?p J = ?r" and "apply_cltn2 ?q J = ?s"
    by (simp_all add: Rep_hyp2 K2_isometry_endpoint_in_S)

  from `?a' \<noteq> ?b'`
  have "proj2_set_Col {?p,?q,?a',?b'}"
    by (simp add: Rep_hyp2 proj2_set_Col_endpoints_in_S)

  from `?a' \<noteq> ?b'` have "?p \<noteq> ?q" by (simp add: Rep_hyp2 endpoint_in_S_swap)

  have "?p \<in> S" by (simp add: Rep_hyp2 endpoint_in_S)
  hence "?a' \<noteq> ?p" and "?b' \<noteq> ?p" by (simp_all add: Rep_hyp2 hyp2_S_not_equal)
  with `proj2_set_Col {?p,?q,?a',?b'}` and `?p \<noteq> ?q`
  have "cross_ratio ?p ?q ?a' ?b'
    = cross_ratio (apply_cltn2 ?p J) (apply_cltn2 ?q J)
    (apply_cltn2 ?a' J) (apply_cltn2 ?b' J)"
    by (rule cross_ratio_cltn2 [symmetric])
  with `apply_cltn2 ?p J = ?r` and `apply_cltn2 ?q J = ?s`
    and `apply_cltn2 ?a' J = ?c'` and `apply_cltn2 ?b' J = ?d'`
  show "cross_ratio ?p ?q ?a' ?b' = cross_ratio ?r ?s ?c' ?d'" by simp
qed

lemma real_hyp2_C_exp_2dist:
  assumes "a b \<congruent>\<^sub>K c d"
  shows "exp_2dist (Rep_hyp2 a) (Rep_hyp2 b)
  = exp_2dist (Rep_hyp2 c) (Rep_hyp2 d)"
  (is "exp_2dist ?a' ?b' = exp_2dist ?c' ?d'")
proof -
  from `a b \<congruent>\<^sub>K c d`
  obtain J where "is_K2_isometry J" and "hyp2_cltn2 a J = c"
    and "hyp2_cltn2 b J = d"
    by (unfold real_hyp2_C_def) auto
  hence "apply_cltn2 ?a' J = ?c'" and "apply_cltn2 ?b' J = ?d'"
    by (simp_all add: Rep_hyp2_cltn2 [symmetric])

  from Rep_hyp2 [of a] and Rep_hyp2 [of b] and `is_K2_isometry J`
  have "exp_2dist (apply_cltn2 ?a' J) (apply_cltn2 ?b' J) = exp_2dist ?a' ?b'"
    by (rule K2_isometry_exp_2dist)
  with `apply_cltn2 ?a' J = ?c'` and `apply_cltn2 ?b' J = ?d'`
  show "exp_2dist ?a' ?b' = exp_2dist ?c' ?d'" by simp
qed

lemma real_hyp2_C_cosh_dist:
  assumes "a b \<congruent>\<^sub>K c d"
  shows "cosh_dist (Rep_hyp2 a) (Rep_hyp2 b)
  = cosh_dist (Rep_hyp2 c) (Rep_hyp2 d)"
  using assms
  by (unfold cosh_dist_def) (simp add: real_hyp2_C_exp_2dist)

lemma cross_ratio_in_terms_of_cosh_dist:
  assumes "are_endpoints_in_S p q a b"
  and "B\<^sub>\<real> (cart2_pt a) (cart2_pt b) (cart2_pt p)"
  shows "cross_ratio p q a b
  = 2 * (cosh_dist a b)\<^sup>2 + 2 * cosh_dist a b * sqrt ((cosh_dist a b)\<^sup>2 - 1) - 1"
  (is "?pqab = 2 * ?ab\<^sup>2 + 2 * ?ab * sqrt (?ab\<^sup>2 - 1) - 1")
proof -
  from `are_endpoints_in_S p q a b`
  have "?ab = (sqrt ?pqab + 1 / sqrt ?pqab) / 2" by (rule cosh_dist_general)
  hence "sqrt ?pqab - 2 * ?ab + 1 / sqrt ?pqab = 0" by simp
  hence "sqrt ?pqab * (sqrt ?pqab - 2 * ?ab + 1 / sqrt ?pqab) = 0" by simp
  moreover from assms
  have "?pqab \<ge> 1" by (rule are_endpoints_in_S_ordered_cross_ratio)
  ultimately have "?pqab - 2 * ?ab * (sqrt ?pqab) + 1 = 0"
    by (simp add: algebra_simps real_sqrt_mult [symmetric])
  with `?pqab \<ge> 1` and discriminant_iff [of 1 "sqrt ?pqab" "- 2 * ?ab" 1]
  have "sqrt ?pqab = (2 * ?ab + sqrt (4 * ?ab\<^sup>2 - 4)) / 2
    \<or> sqrt ?pqab = (2 * ?ab - sqrt (4 * ?ab\<^sup>2 - 4)) / 2"
    unfolding discrim_def
    by (simp add: real_sqrt_mult [symmetric] power2_eq_square)
  moreover have "sqrt (4 * ?ab\<^sup>2 - 4) = sqrt (4 * (?ab\<^sup>2 - 1))" by simp
  hence "sqrt (4 * ?ab\<^sup>2 - 4) = 2 * sqrt (?ab\<^sup>2 - 1)"
    by (unfold real_sqrt_mult) simp
  ultimately have "sqrt ?pqab = 2 * (?ab + sqrt (?ab\<^sup>2 - 1)) / 2
    \<or> sqrt ?pqab = 2 * (?ab - sqrt (?ab\<^sup>2 - 1)) / 2"
    by simp
  hence "sqrt ?pqab = ?ab + sqrt (?ab\<^sup>2 - 1)
    \<or> sqrt ?pqab = ?ab - sqrt (?ab\<^sup>2 - 1)"
    by (simp only: nonzero_mult_div_cancel_left [of 2])

  from `are_endpoints_in_S p q a b`
  have "a \<in> hyp2" and "b \<in> hyp2" by (unfold are_endpoints_in_S_def) simp_all
  hence "?ab \<ge> 1" by (rule cosh_dist_at_least_1)
  hence "?ab\<^sup>2 \<ge> 1" by simp
  hence "sqrt (?ab\<^sup>2 - 1) \<ge> 0" by simp
  hence "sqrt (?ab\<^sup>2 - 1) * sqrt (?ab\<^sup>2 - 1) = ?ab\<^sup>2 - 1"
    by (simp add: real_sqrt_mult [symmetric])
  hence "(?ab + sqrt (?ab\<^sup>2 - 1)) * (?ab - sqrt (?ab\<^sup>2 - 1)) = 1"
    by (simp add: algebra_simps power2_eq_square)

  have "?ab - sqrt (?ab\<^sup>2 - 1) \<le> 1"
  proof (rule ccontr)
    assume "\<not> (?ab - sqrt (?ab\<^sup>2 - 1) \<le> 1)"
    hence "1 < ?ab - sqrt (?ab\<^sup>2 - 1)" by simp
    also from `sqrt (?ab\<^sup>2 - 1) \<ge> 0`
    have "\<dots> \<le> ?ab + sqrt (?ab\<^sup>2 - 1)" by simp
    finally have "1 < ?ab + sqrt (?ab\<^sup>2 - 1)" by simp
    with `1 < ?ab - sqrt (?ab\<^sup>2 - 1)`
      and mult_strict_mono' [of
      1 "?ab + sqrt (?ab\<^sup>2 - 1)" 1 "?ab - sqrt (?ab\<^sup>2 - 1)"]
    have "1 < (?ab + sqrt (?ab\<^sup>2 - 1)) * (?ab - sqrt (?ab\<^sup>2 - 1))" by simp
    with `(?ab + sqrt (?ab\<^sup>2 - 1)) * (?ab - sqrt (?ab\<^sup>2 - 1)) = 1`
    show False by simp
  qed

  have "sqrt ?pqab = ?ab + sqrt (?ab\<^sup>2 - 1)"
  proof (rule ccontr)
    assume "sqrt ?pqab \<noteq> ?ab + sqrt (?ab\<^sup>2 - 1)"
    with `sqrt ?pqab = ?ab + sqrt (?ab\<^sup>2 - 1)
      \<or> sqrt ?pqab = ?ab - sqrt (?ab\<^sup>2 - 1)`
    have "sqrt ?pqab = ?ab - sqrt (?ab\<^sup>2 - 1)" by simp
    with `?ab - sqrt (?ab\<^sup>2 - 1) \<le> 1` have "sqrt ?pqab \<le> 1" by simp
    with `?pqab \<ge> 1` have "sqrt ?pqab = 1" by simp
    with `sqrt ?pqab = ?ab - sqrt (?ab\<^sup>2 - 1)`
      and `(?ab + sqrt (?ab\<^sup>2 - 1)) * (?ab - sqrt (?ab\<^sup>2 - 1)) = 1`
    have "?ab + sqrt (?ab\<^sup>2 - 1) = 1" by simp
    with `sqrt ?pqab = 1` have "sqrt ?pqab = ?ab + sqrt (?ab\<^sup>2 - 1)" by simp
    with `sqrt ?pqab \<noteq> ?ab + sqrt (?ab\<^sup>2 - 1)` show False ..
  qed
  moreover from `?pqab \<ge> 1` have "?pqab = (sqrt ?pqab)\<^sup>2" by simp
  ultimately have "?pqab = (?ab + sqrt (?ab\<^sup>2 - 1))\<^sup>2" by simp
  with `sqrt (?ab\<^sup>2 - 1) * sqrt (?ab\<^sup>2 - 1) = ?ab\<^sup>2 - 1`
  show "?pqab = 2 * ?ab\<^sup>2 + 2 * ?ab * sqrt (?ab\<^sup>2 - 1) - 1"
    by (simp add: power2_eq_square algebra_simps)
qed

lemma are_endpoints_in_S_cross_ratio_correct:
  assumes "are_endpoints_in_S p q a b"
  shows "cross_ratio_correct p q a b"
proof -
  from `are_endpoints_in_S p q a b`
  have "p \<noteq> q" and "p \<in> S" and "q \<in> S" and "a \<in> hyp2" and "b \<in> hyp2"
    and "proj2_set_Col {p,q,a,b}"
    by (unfold are_endpoints_in_S_def) simp_all

  from `a \<in> hyp2` and `b \<in> hyp2` and `p \<in> S` and `q \<in> S`
  have "a \<noteq> p" and "b \<noteq> p" and "a \<noteq> q" by (simp_all add: hyp2_S_not_equal)
  with `proj2_set_Col {p,q,a,b}` and `p \<noteq> q`
  show "cross_ratio_correct p q a b" by (unfold cross_ratio_correct_def) simp
qed

lemma endpoints_in_S_cross_ratio_correct:
  assumes "a \<noteq> b" and "a \<in> hyp2" and "b \<in> hyp2"
  shows "cross_ratio_correct (endpoint_in_S a b) (endpoint_in_S b a) a b"
proof -
  from assms
  have "are_endpoints_in_S (endpoint_in_S a b) (endpoint_in_S b a) a b"
    by (rule endpoints_in_S_are_endpoints_in_S)
  thus "cross_ratio_correct (endpoint_in_S a b) (endpoint_in_S b a) a b"
    by (rule are_endpoints_in_S_cross_ratio_correct)
qed

lemma endpoints_in_S_perp_foot_cross_ratio_correct:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "c \<in> hyp2" and "a \<noteq> b"
  and "proj2_incident a l" and "proj2_incident b l"
  shows "cross_ratio_correct
  (endpoint_in_S a b) (endpoint_in_S b a) a (perp_foot c l)"
  (is "cross_ratio_correct ?p ?q a ?d")
proof -
  from assms
  have "are_endpoints_in_S ?p ?q a ?d"
    by (rule endpoints_in_S_perp_foot_are_endpoints_in_S)
  thus "cross_ratio_correct ?p ?q a ?d"
    by (rule are_endpoints_in_S_cross_ratio_correct)
qed

lemma cosh_dist_unique:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "c \<in> hyp2" and "p \<in> S"
  and "B\<^sub>\<real> (cart2_pt a) (cart2_pt b) (cart2_pt p)" (is "B\<^sub>\<real> ?ca ?cb ?cp")
  and "B\<^sub>\<real> (cart2_pt a) (cart2_pt c) (cart2_pt p)" (is "B\<^sub>\<real> ?ca ?cc ?cp")
  and "cosh_dist a b = cosh_dist a c" (is "?ab = ?ac")
  shows "b = c"
proof -
  let ?q = "endpoint_in_S p a"

  from `a \<in> hyp2` and `b \<in> hyp2` and `c \<in> hyp2` and `p \<in> S`
  have "z_non_zero a" and "z_non_zero b" and "z_non_zero c" and "z_non_zero p"
    by (simp_all add: hyp2_S_z_non_zero)
  with `B\<^sub>\<real> ?ca ?cb ?cp` and `B\<^sub>\<real> ?ca ?cc ?cp`
  have "\<exists> l. proj2_incident a l \<and> proj2_incident b l \<and> proj2_incident p l"
    and "\<exists> m. proj2_incident a m \<and> proj2_incident c m \<and> proj2_incident p m"
    by (simp_all add: euclid_B_cart2_common_line)
  then obtain l and m where
    "proj2_incident a l" and "proj2_incident b l" and "proj2_incident p l"
    and "proj2_incident a m" and "proj2_incident c m" and "proj2_incident p m"
    by auto

  from `a \<in> hyp2` and `p \<in> S` have "a \<noteq> p" by (rule hyp2_S_not_equal)
  with `proj2_incident a l` and `proj2_incident p l`
    and `proj2_incident a m` and `proj2_incident p m` and proj2_incident_unique
  have "l = m" by fast
  with `proj2_incident c m` have "proj2_incident c l" by simp
  with `a \<in> hyp2` and `b \<in> hyp2` and `c \<in> hyp2` and `p \<in> S`
    and `proj2_incident a l` and `proj2_incident b l` and `proj2_incident p l`
  have "are_endpoints_in_S p ?q b a" and "are_endpoints_in_S p ?q c a"
    by (simp_all add: end_and_opposite_are_endpoints_in_S)
  with are_endpoints_in_S_swap_34
  have "are_endpoints_in_S p ?q a b" and "are_endpoints_in_S p ?q a c" by fast+
  hence "cross_ratio_correct p ?q a b" and "cross_ratio_correct p ?q a c"
    by (simp_all add: are_endpoints_in_S_cross_ratio_correct)
  moreover
  from `are_endpoints_in_S p ?q a b` and `are_endpoints_in_S p ?q a c`
    and `B\<^sub>\<real> ?ca ?cb ?cp` and `B\<^sub>\<real> ?ca ?cc ?cp`
  have "cross_ratio p ?q a b = 2 * ?ab\<^sup>2 + 2 * ?ab * sqrt (?ab\<^sup>2 - 1) - 1"
    and "cross_ratio p ?q a c = 2 * ?ac\<^sup>2 + 2 * ?ac * sqrt (?ac\<^sup>2 - 1) - 1"
    by (simp_all add: cross_ratio_in_terms_of_cosh_dist)
  with `?ab = ?ac` have "cross_ratio p ?q a b = cross_ratio p ?q a c" by simp
  ultimately show "b = c" by (rule cross_ratio_unique)
qed

lemma cosh_dist_swap:
  assumes "a \<in> hyp2" and "b \<in> hyp2"
  shows "cosh_dist a b = cosh_dist b a"
proof -
  from assms and K2_isometry_swap
  obtain J where "is_K2_isometry J" and "apply_cltn2 a J = b"
    and "apply_cltn2 b J = a"
    by auto

  from `b \<in> hyp2` and `a \<in> hyp2` and `is_K2_isometry J`
  have "cosh_dist (apply_cltn2 b J) (apply_cltn2 a J) = cosh_dist b a"
    by (rule K2_isometry_cosh_dist)
  with `apply_cltn2 a J = b` and `apply_cltn2 b J = a`
  show "cosh_dist a b = cosh_dist b a" by simp
qed

lemma exp_2dist_1_equal:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "exp_2dist a b = 1"
  shows "a = b"
proof (rule ccontr)
  assume "a \<noteq> b"
  with `a \<in> hyp2` and `b \<in> hyp2`
  have "cross_ratio_correct (endpoint_in_S a b) (endpoint_in_S b a) a b"
    (is "cross_ratio_correct ?p ?q a b")
    by (simp add: endpoints_in_S_cross_ratio_correct)
  moreover
  from `a \<noteq> b`
  have "exp_2dist a b = cross_ratio ?p ?q a b" by (unfold exp_2dist_def) simp
  with `exp_2dist a b = 1` have "cross_ratio ?p ?q a b = 1" by simp
  ultimately have "a = b" by (rule cross_ratio_1_equal)
  with `a \<noteq> b` show False ..
qed

subsubsection {* A formula for a cross ratio involving a perpendicular foot *}

lemma described_perp_foot_cross_ratio_formula:
  assumes "a \<noteq> b" and "c \<in> hyp2" and "are_endpoints_in_S p q a b"
  and "proj2_incident p l" and "proj2_incident q l" and "M_perp l m"
  and "proj2_incident d l" and "proj2_incident d m" and "proj2_incident c m"
  shows "cross_ratio p q d a
    = (cosh_dist b c * sqrt (cross_ratio p q a b) - cosh_dist a c)
      / (cosh_dist a c * cross_ratio p q a b
        - cosh_dist b c * sqrt (cross_ratio p q a b))"
  (is "?pqda = (?bc * sqrt ?pqab - ?ac) / (?ac * ?pqab - ?bc * sqrt ?pqab)")
proof -
  let ?da = "cosh_dist d a"
  let ?db = "cosh_dist d b"
  let ?dc = "cosh_dist d c"
  let ?pqdb = "cross_ratio p q d b"

  from `are_endpoints_in_S p q a b`
  have "p \<noteq> q" and "p \<in> S" and "q \<in> S" and "a \<in> hyp2" and "b \<in> hyp2"
    and "proj2_set_Col {p,q,a,b}"
    by (unfold are_endpoints_in_S_def) simp_all

  from `proj2_set_Col {p,q,a,b}`
  obtain l' where "proj2_incident p l'" and "proj2_incident q l'"
    and "proj2_incident a l'" and "proj2_incident b l'"
    by (unfold proj2_set_Col_def) auto

  from `p \<noteq> q` and `proj2_incident p l'` and `proj2_incident q l'`
    and `proj2_incident p l` and `proj2_incident q l` and proj2_incident_unique
  have "l' = l" by fast
  with `proj2_incident a l'` and `proj2_incident b l'`
  have "proj2_incident a l" and "proj2_incident b l" by simp_all

  from `M_perp l m` and `a \<in> hyp2` and `proj2_incident a l` and `c \<in> hyp2`
    and `proj2_incident c m` and `proj2_incident d l` and `proj2_incident d m`
  have "d \<in> hyp2" by (rule M_perp_hyp2)
  with `a \<in> hyp2` and `b \<in> hyp2` and `c \<in> hyp2`
  have "?bc > 0" and "?da > 0" and "?ac > 0"
    by (simp_all add: cosh_dist_positive)

  from `proj2_incident p l` and `proj2_incident q l` and `proj2_incident d l`
    and `proj2_incident a l` and `proj2_incident b l`
  have "proj2_set_Col {p,q,d,a}" and "proj2_set_Col {p,q,d,b}"
    and "proj2_set_Col {p,q,a,b}"
    by (unfold proj2_set_Col_def) (simp_all add: exI [of _ l])
  with `p \<noteq> q` and `p \<in> S` and `q \<in> S` and `d \<in> hyp2` and `a \<in> hyp2`
    and `b \<in> hyp2`
  have "are_endpoints_in_S p q d a" and "are_endpoints_in_S p q d b"
    and "are_endpoints_in_S p q a b"
    by (unfold are_endpoints_in_S_def) simp_all
  hence "?pqda > 0" and "?pqdb > 0" and "?pqab > 0"
    by (simp_all add: cross_ratio_S_S_hyp2_hyp2_positive)

  from `proj2_incident p l` and `proj2_incident q l` and `proj2_incident a l`
  have "proj2_Col p q a" by (rule proj2_incident_Col)

  from `a \<in> hyp2` and `b \<in> hyp2` and `p \<in> S` and `q \<in> S`
  have "a \<noteq> p" and "a \<noteq> q" and "b \<noteq> p" by (simp_all add: hyp2_S_not_equal)

  from `proj2_Col p q a` and `p \<noteq> q` and `a \<noteq> p` and `a \<noteq> q`
  have "?pqdb = ?pqda * ?pqab" by (rule cross_ratio_product [symmetric])

  from `M_perp l m` and `a \<in> hyp2` and `b \<in> hyp2` and `c \<in> hyp2` and `d \<in> hyp2`
    and `proj2_incident a l` and `proj2_incident b l` and `proj2_incident d l`
    and `proj2_incident d m` and `proj2_incident c m`
    and cosh_dist_perp_divide [of l m _ d c]
  have "?dc = ?ac / ?da" and "?dc = ?bc / ?db" by fast+
  hence "?ac / ?da = ?bc / ?db" by simp
  with `?bc > 0` and `?da > 0`
  have "?ac / ?bc = ?da / ?db" by (simp add: field_simps)
  also from `are_endpoints_in_S p q d a` and `are_endpoints_in_S p q d b`
  have "\<dots>
    = 2 * (sqrt ?pqda + 1 / (sqrt ?pqda))
    / (2 * (sqrt ?pqdb + 1 / (sqrt ?pqdb)))"
    by (simp add: cosh_dist_general)
  also
  have "\<dots> = (sqrt ?pqda + 1 / (sqrt ?pqda)) / (sqrt ?pqdb + 1 / (sqrt ?pqdb))"
    by (simp only: mult_divide_mult_cancel_left_if) simp
  also have "\<dots>
    = sqrt ?pqdb * (sqrt ?pqda + 1 / (sqrt ?pqda))
    / (sqrt ?pqdb * (sqrt ?pqdb + 1 / (sqrt ?pqdb)))"
    by simp
  also from `?pqdb > 0`
  have "\<dots> = (sqrt (?pqdb * ?pqda) + sqrt (?pqdb / ?pqda)) / (?pqdb + 1)"
    by (simp add: real_sqrt_mult [symmetric] real_sqrt_divide algebra_simps)
  also from `?pqdb = ?pqda * ?pqab` and `?pqda > 0` and real_sqrt_pow2
  have "\<dots> = (?pqda * sqrt ?pqab + sqrt ?pqab) / (?pqda * ?pqab + 1)"
    by (simp add: real_sqrt_mult power2_eq_square)
  finally
  have "?ac / ?bc = (?pqda * sqrt ?pqab + sqrt ?pqab) / (?pqda * ?pqab + 1)" .

  from `?pqda > 0` and `?pqab > 0`
  have "?pqda * ?pqab + 1 > 0" by (simp add: add_pos_pos)
  with `?bc > 0`
    and `?ac / ?bc = (?pqda * sqrt ?pqab + sqrt ?pqab) / (?pqda * ?pqab + 1)`
  have "?ac * (?pqda * ?pqab + 1) = ?bc * (?pqda * sqrt ?pqab + sqrt ?pqab)"
    by (simp add: field_simps)
  hence "?pqda * (?ac * ?pqab - ?bc * sqrt ?pqab) = ?bc * sqrt ?pqab - ?ac"
    by (simp add: algebra_simps)

  from `proj2_set_Col {p,q,a,b}` and `p \<noteq> q` and `a \<noteq> p` and `a \<noteq> q`
    and `b \<noteq> p`
  have "cross_ratio_correct p q a b" by (unfold cross_ratio_correct_def) simp

  have "?ac * ?pqab - ?bc * sqrt ?pqab \<noteq> 0"
  proof
    assume "?ac * ?pqab - ?bc * sqrt ?pqab = 0"
    with `?pqda * (?ac * ?pqab - ?bc * sqrt ?pqab) = ?bc * sqrt ?pqab - ?ac`
    have "?bc * sqrt ?pqab - ?ac = 0" by simp
    with `?ac * ?pqab - ?bc * sqrt ?pqab = 0` and `?ac > 0`
    have "?pqab = 1" by simp
    with `cross_ratio_correct p q a b`
    have "a = b" by (rule cross_ratio_1_equal)
    with `a \<noteq> b` show False ..
  qed
  with `?pqda * (?ac * ?pqab - ?bc * sqrt ?pqab) = ?bc * sqrt ?pqab - ?ac`
  show "?pqda = (?bc * sqrt ?pqab - ?ac) / (?ac * ?pqab - ?bc * sqrt ?pqab)"
    by (simp add: field_simps)
qed

lemma perp_foot_cross_ratio_formula:
  assumes "a \<in> hyp2" and "b \<in> hyp2" and "c \<in> hyp2" and "a \<noteq> b"
  shows "cross_ratio (endpoint_in_S a b) (endpoint_in_S b a)
      (perp_foot c (proj2_line_through a b)) a
    = (cosh_dist b c * sqrt (exp_2dist a b) - cosh_dist a c)
      / (cosh_dist a c * exp_2dist a b - cosh_dist b c * sqrt (exp_2dist a b))"
  (is "cross_ratio ?p ?q ?d a
    = (?bc * sqrt ?pqab - ?ac) / (?ac * ?pqab - ?bc * sqrt ?pqab)")
proof -
  from `a \<noteq> b` and `a \<in> hyp2` and `b \<in> hyp2`
  have "are_endpoints_in_S ?p ?q a b"
    by (rule endpoints_in_S_are_endpoints_in_S)

  let ?l = "proj2_line_through a b"
  have "proj2_incident a ?l" and "proj2_incident b ?l"
    by (rule proj2_line_through_incident)+
  with `a \<noteq> b` and `a \<in> hyp2` and `b \<in> hyp2`
  have "proj2_incident ?p ?l" and "proj2_incident ?q ?l"
    by (simp_all add: endpoint_in_S_incident)

  let ?m = "drop_perp c ?l"
  have "M_perp ?l ?m" by (rule drop_perp_perp)

  have "proj2_incident ?d ?l" and "proj2_incident ?d ?m"
    by (rule perp_foot_incident)+

  have "proj2_incident c ?m" by (rule drop_perp_incident)
  with `a \<noteq> b` and `c \<in> hyp2` and `are_endpoints_in_S ?p ?q a b`
    and `proj2_incident ?p ?l` and `proj2_incident ?q ?l` and `M_perp ?l ?m`
    and `proj2_incident ?d ?l` and `proj2_incident ?d ?m`
  have "cross_ratio ?p ?q ?d a
    = (?bc * sqrt (cross_ratio ?p ?q a b) - ?ac)
    / (?ac * (cross_ratio ?p ?q a b) - ?bc * sqrt (cross_ratio ?p ?q a b))"
    by (rule described_perp_foot_cross_ratio_formula)
  with `a \<noteq> b`
  show "cross_ratio ?p ?q ?d a
    = (?bc * sqrt ?pqab - ?ac) / (?ac * ?pqab - ?bc * sqrt ?pqab)"
    by (unfold exp_2dist_def) simp
qed

subsection {* The Klein--Beltrami model satisfies axiom 5 *}

lemma statement69:
  assumes "a b \<congruent>\<^sub>K a' b'" and "b c \<congruent>\<^sub>K b' c'" and "a c \<congruent>\<^sub>K a' c'"
  shows "\<exists> J. is_K2_isometry J
  \<and> hyp2_cltn2 a J = a' \<and> hyp2_cltn2 b J = b' \<and> hyp2_cltn2 c J = c'"
proof cases
  assume "a = b"
  with `a b \<congruent>\<^sub>K a' b'` have "a' = b'" by (simp add: hyp2.A3_reversed)
  with `a = b` and `b c \<congruent>\<^sub>K b' c'`
  show "\<exists> J. is_K2_isometry J
    \<and> hyp2_cltn2 a J = a' \<and> hyp2_cltn2 b J = b' \<and> hyp2_cltn2 c J = c'"
    by (unfold real_hyp2_C_def) simp
next
  assume "a \<noteq> b"
  with `a b \<congruent>\<^sub>K a' b'`
  have "a' \<noteq> b'" by (auto simp add: hyp2.A3')

  let ?pa = "Rep_hyp2 a"
    and ?pb = "Rep_hyp2 b"
    and ?pc = "Rep_hyp2 c"
    and ?pa' = "Rep_hyp2 a'"
    and ?pb' = "Rep_hyp2 b'"
    and ?pc' = "Rep_hyp2 c'"
  def pp \<equiv> "endpoint_in_S ?pa ?pb"
    and pq \<equiv> "endpoint_in_S ?pb ?pa"
    and l \<equiv> "proj2_line_through ?pa ?pb"
    and pp' \<equiv> "endpoint_in_S ?pa' ?pb'"
    and pq' \<equiv> "endpoint_in_S ?pb' ?pa'"
    and l' \<equiv> "proj2_line_through ?pa' ?pb'"
  def pd \<equiv> "perp_foot ?pc l"
    and ps \<equiv> "perp_up ?pc l"
    and m \<equiv> "drop_perp ?pc l"
    and pd' \<equiv> "perp_foot ?pc' l'"
    and ps' \<equiv> "perp_up ?pc' l'"
    and m' \<equiv> "drop_perp ?pc' l'"

  have "pp \<in> S" and "pp' \<in> S" and "pq \<in> S" and "pq' \<in> S"
    unfolding pp_def and pp'_def and pq_def and pq'_def
    by (simp_all add: Rep_hyp2 endpoint_in_S)

  from `a \<noteq> b` and `a' \<noteq> b'`
  have "?pa \<noteq> ?pb" and "?pa' \<noteq> ?pb'" by (unfold Rep_hyp2_inject)
  moreover
  have "proj2_incident ?pa l" and "proj2_incident ?pb l"
    and "proj2_incident ?pa' l'" and "proj2_incident ?pb' l'"
    by (unfold l_def l'_def) (rule proj2_line_through_incident)+
  ultimately have "proj2_incident pp l" and "proj2_incident pp' l'"
    and "proj2_incident pq l" and "proj2_incident pq' l'"
    unfolding pp_def and pp'_def and pq_def and pq'_def
    by (simp_all add: Rep_hyp2 endpoint_in_S_incident)

  from `pp \<in> S` and `pp' \<in> S` and `proj2_incident pp l`
    and `proj2_incident pp' l'` and `proj2_incident ?pa l`
    and `proj2_incident ?pa' l'`
  have "right_angle pp pd ps" and "right_angle pp' pd' ps'"
    unfolding pd_def and ps_def and pd'_def and ps'_def
    by (simp_all add: Rep_hyp2
      perp_foot_up_right_angle [of pp ?pc ?pa l]
      perp_foot_up_right_angle [of pp' ?pc' ?pa' l'])
  with right_angle_to_right_angle [of pp pd ps pp' pd' ps']
  obtain J where "is_K2_isometry J" and "apply_cltn2 pp J = pp'"
    and "apply_cltn2 pd J = pd'" and "apply_cltn2 ps J = ps'"
    by auto

  let ?paJ = "apply_cltn2 ?pa J"
    and ?pbJ = "apply_cltn2 ?pb J"
    and ?pcJ = "apply_cltn2 ?pc J"
    and ?pdJ = "apply_cltn2 pd J"
    and ?ppJ = "apply_cltn2 pp J"
    and ?pqJ = "apply_cltn2 pq J"
    and ?psJ = "apply_cltn2 ps J"
    and ?lJ = "apply_cltn2_line l J"
    and ?mJ = "apply_cltn2_line m J"

  have "proj2_incident pd l" and "proj2_incident pd' l'"
    and "proj2_incident pd m" and "proj2_incident pd' m'"
    by (unfold pd_def pd'_def m_def m'_def) (rule perp_foot_incident)+

  from `proj2_incident pp l` and `proj2_incident pq l`
    and `proj2_incident pd l` and `proj2_incident ?pa l`
    and `proj2_incident ?pb l`
  have "proj2_set_Col {pp,pq,pd,?pa}" and "proj2_set_Col {pp,pq,?pa,?pb}"
    by (unfold pd_def proj2_set_Col_def) (simp_all add: exI [of _ l])

  from `?pa \<noteq> ?pb` and `?pa' \<noteq> ?pb'`
  have "pp \<noteq> pq" and "pp' \<noteq> pq'"
    unfolding pp_def and pq_def and pp'_def and pq'_def
    by (simp_all add: Rep_hyp2 endpoint_in_S_swap)

  from `proj2_incident ?pa l` and `proj2_incident ?pa' l'`
  have "pd \<in> hyp2" and "pd' \<in> hyp2"
    unfolding pd_def and pd'_def
    by (simp_all add: Rep_hyp2 perp_foot_hyp2 [of ?pa l ?pc]
      perp_foot_hyp2 [of ?pa' l' ?pc'])

  from `proj2_incident ?pa l` and `proj2_incident ?pa' l'`
  have "ps \<in> S" and "ps' \<in> S"
    unfolding ps_def and ps'_def
    by (simp_all add: Rep_hyp2 perp_up_in_S [of ?pc ?pa l]
      perp_up_in_S [of ?pc' ?pa' l'])

  from `pd \<in> hyp2` and `pp \<in> S` and `ps \<in> S`
  have "pd \<noteq> pp" and "?pa \<noteq> pp" and "?pb \<noteq> pp" and "pd \<noteq> ps"
    by (simp_all add: Rep_hyp2 hyp2_S_not_equal)

  from `is_K2_isometry J` and `pq \<in> S`
  have "?pqJ \<in> S" by (unfold is_K2_isometry_def) simp

  from `pd \<noteq> pp` and `proj2_incident pd l` and `proj2_incident pp l`
    and `proj2_incident pd' l'` and `proj2_incident pp' l'`
  have "?lJ = l'"
    unfolding `?pdJ = pd'` [symmetric] and `?ppJ = pp'` [symmetric]
    by (rule apply_cltn2_line_unique)
  from `proj2_incident pq l` and `proj2_incident ?pa l`
    and `proj2_incident ?pb l`
  have "proj2_incident ?pqJ l'" and "proj2_incident ?paJ l'"
    and "proj2_incident ?pbJ l'"
    by (unfold `?lJ = l'` [symmetric]) simp_all

  from `?pa' \<noteq> ?pb'` and `?pqJ \<in> S` and `proj2_incident ?pa' l'`
    and `proj2_incident ?pb' l'` and `proj2_incident ?pqJ l'`
  have "?pqJ = pp' \<or> ?pqJ = pq'"
    unfolding pp'_def and pq'_def
    by (simp add: Rep_hyp2 endpoints_in_S_incident_unique)
  moreover
  from `pp \<noteq> pq` and apply_cltn2_injective
  have "pp' \<noteq> ?pqJ" by (unfold `?ppJ = pp'` [symmetric]) fast
  ultimately have "?pqJ = pq'" by simp

  from `?pa' \<noteq> ?pb'`
  have "cross_ratio pp' pq' pd' ?pa'
    = (cosh_dist ?pb' ?pc' * sqrt (exp_2dist ?pa' ?pb') - cosh_dist ?pa' ?pc')
      / (cosh_dist ?pa' ?pc' * exp_2dist ?pa' ?pb'
        - cosh_dist ?pb' ?pc' * sqrt (exp_2dist ?pa' ?pb'))"
    unfolding pp'_def and pq'_def and pd'_def and l'_def
    by (simp add: Rep_hyp2 perp_foot_cross_ratio_formula)
  also from assms
  have "\<dots> = (cosh_dist ?pb ?pc * sqrt (exp_2dist ?pa ?pb) - cosh_dist ?pa ?pc)
    / (cosh_dist ?pa ?pc * exp_2dist ?pa ?pb
      - cosh_dist ?pb ?pc * sqrt (exp_2dist ?pa ?pb))"
    by (simp add: real_hyp2_C_exp_2dist real_hyp2_C_cosh_dist)
  also from `?pa \<noteq> ?pb`
  have "\<dots> = cross_ratio pp pq pd ?pa"
    unfolding pp_def and pq_def and pd_def and l_def
    by (simp add: Rep_hyp2 perp_foot_cross_ratio_formula)
  also from `proj2_set_Col {pp,pq,pd,?pa}` and `pp \<noteq> pq` and `pd \<noteq> pp`
    and `?pa \<noteq> pp`
  have "\<dots> = cross_ratio ?ppJ ?pqJ ?pdJ ?paJ" by (simp add: cross_ratio_cltn2)
  also from `?ppJ = pp'` and `?pqJ = pq'` and `?pdJ = pd'`
  have "\<dots> = cross_ratio pp' pq' pd' ?paJ" by simp
  finally
  have "cross_ratio pp' pq' pd' ?paJ = cross_ratio pp' pq' pd' ?pa'" by simp

  from `is_K2_isometry J`
  have "?paJ \<in> hyp2" and "?pbJ \<in> hyp2" and "?pcJ \<in> hyp2"
    by (rule apply_cltn2_Rep_hyp2)+

  from `proj2_incident pp' l'` and `proj2_incident pq' l'`
    and `proj2_incident pd' l'` and `proj2_incident ?paJ l'`
    and `proj2_incident ?pa' l'` and `proj2_incident ?pbJ l'`
    and `proj2_incident ?pb' l'`
  have "proj2_set_Col {pp',pq',pd',?paJ}" and "proj2_set_Col {pp',pq',pd',?pa'}"
    and "proj2_set_Col {pp',pq',?pa',?pbJ}"
    and "proj2_set_Col {pp',pq',?pa',?pb'}"
    by (unfold proj2_set_Col_def) (simp_all add: exI [of _ l'])
  with `pp' \<noteq> pq'` and `pp' \<in> S` and `pq' \<in> S` and `pd' \<in> hyp2`
    and `?paJ \<in> hyp2` and `?pbJ \<in> hyp2`
  have "are_endpoints_in_S pp' pq' pd' ?paJ"
    and "are_endpoints_in_S pp' pq' pd' ?pa'"
    and "are_endpoints_in_S pp' pq' ?pa' ?pbJ"
    and "are_endpoints_in_S pp' pq' ?pa' ?pb'"
    by (unfold are_endpoints_in_S_def) (simp_all add: Rep_hyp2)
  hence "cross_ratio_correct pp' pq' pd' ?paJ"
    and "cross_ratio_correct pp' pq' pd' ?pa'"
    and "cross_ratio_correct pp' pq' ?pa' ?pbJ"
    and "cross_ratio_correct pp' pq' ?pa' ?pb'"
    by (simp_all add: are_endpoints_in_S_cross_ratio_correct)

  from `cross_ratio_correct pp' pq' pd' ?paJ`
    and `cross_ratio_correct pp' pq' pd' ?pa'`
    and `cross_ratio pp' pq' pd' ?paJ = cross_ratio pp' pq' pd' ?pa'`
  have "?paJ = ?pa'" by (simp add: cross_ratio_unique)
  with `?ppJ = pp'` and `?pqJ = pq'`
  have "cross_ratio pp' pq' ?pa' ?pbJ = cross_ratio ?ppJ ?pqJ ?paJ ?pbJ" by simp
  also from `proj2_set_Col {pp,pq,?pa,?pb}` and `pp \<noteq> pq` and `?pa \<noteq> pp`
    and `?pb \<noteq> pp`
  have "\<dots> = cross_ratio pp pq ?pa ?pb" by (rule cross_ratio_cltn2)
  also from `a \<noteq> b` and `a b \<congruent>\<^sub>K a' b'`
  have "\<dots> = cross_ratio pp' pq' ?pa' ?pb'"
    unfolding pp_def pq_def pp'_def pq'_def
    by (rule real_hyp2_C_cross_ratio_endpoints_in_S)
  finally have "cross_ratio pp' pq' ?pa' ?pbJ = cross_ratio pp' pq' ?pa' ?pb'" .
  with `cross_ratio_correct pp' pq' ?pa' ?pbJ`
    and `cross_ratio_correct pp' pq' ?pa' ?pb'`
  have "?pbJ = ?pb'" by (rule cross_ratio_unique)

  let ?cc = "cart2_pt ?pc"
    and ?cd = "cart2_pt pd"
    and ?cs = "cart2_pt ps"
    and ?cc' = "cart2_pt ?pc'"
    and ?cd' = "cart2_pt pd'"
    and ?cs' = "cart2_pt ps'"
    and ?ccJ = "cart2_pt ?pcJ"
    and ?cdJ = "cart2_pt ?pdJ"
    and ?csJ = "cart2_pt ?psJ"

  from `proj2_incident ?pa l` and `proj2_incident ?pa' l'`
  have "B\<^sub>\<real> ?cd ?cc ?cs" and "B\<^sub>\<real> ?cd' ?cc' ?cs'"
    unfolding pd_def and ps_def and pd'_def and ps'_def
    by (simp_all add: Rep_hyp2 perp_up_at_end [of ?pc ?pa l]
      perp_up_at_end [of ?pc' ?pa' l'])

  from `pd \<in> hyp2` and `ps \<in> S` and `is_K2_isometry J`
    and `B\<^sub>\<real> ?cd ?cc ?cs`
  have "B\<^sub>\<real> ?cdJ ?ccJ ?csJ" by (simp add: Rep_hyp2 statement_63)
  hence "B\<^sub>\<real> ?cd' ?ccJ ?cs'" by (unfold `?pdJ = pd'` `?psJ = ps'`)

  from `?paJ = ?pa'` have "cosh_dist ?pa' ?pcJ = cosh_dist ?paJ ?pcJ" by simp
  also from `is_K2_isometry J`
  have "\<dots> = cosh_dist ?pa ?pc" by (simp add: Rep_hyp2 K2_isometry_cosh_dist)
  also from `a c \<congruent>\<^sub>K a' c'`
  have "\<dots> = cosh_dist ?pa' ?pc'" by (rule real_hyp2_C_cosh_dist)
  finally have "cosh_dist ?pa' ?pcJ = cosh_dist ?pa' ?pc'" .

  have "M_perp l' m'" by (unfold m'_def) (rule drop_perp_perp)

  have "proj2_incident ?pc m" and "proj2_incident ?pc' m'"
    by (unfold m_def m'_def) (rule drop_perp_incident)+

  from `proj2_incident ?pa l` and `proj2_incident ?pa' l'`
  have "proj2_incident ps m" and "proj2_incident ps' m'"
    unfolding ps_def and m_def and ps'_def and m'_def
    by (simp_all add: Rep_hyp2 perp_up_incident [of ?pc ?pa l]
      perp_up_incident [of ?pc' ?pa' l'])
  with `pd \<noteq> ps` and `proj2_incident pd m` and `proj2_incident pd' m'`
  have "?mJ = m'"
    unfolding `?pdJ = pd'` [symmetric] and `?psJ = ps'` [symmetric]
    by (simp add: apply_cltn2_line_unique)
  from `proj2_incident ?pc m`
  have "proj2_incident ?pcJ m'" by (unfold `?mJ = m'` [symmetric]) simp
  with `M_perp l' m'` and Rep_hyp2 [of a'] and `pd' \<in> hyp2` and `?pcJ \<in> hyp2`
    and Rep_hyp2 [of c'] and `proj2_incident ?pa' l'`
    and `proj2_incident pd' l'` and `proj2_incident pd' m'`
    and `proj2_incident ?pc' m'`
  have "cosh_dist pd' ?pcJ = cosh_dist ?pa' ?pcJ / cosh_dist pd' ?pa'"
    and "cosh_dist pd' ?pc' = cosh_dist ?pa' ?pc' / cosh_dist pd' ?pa'"
    by (simp_all add: cosh_dist_perp_divide)
  with `cosh_dist ?pa' ?pcJ = cosh_dist ?pa' ?pc'`
  have "cosh_dist pd' ?pcJ = cosh_dist pd' ?pc'" by simp
  with `pd' \<in> hyp2` and `?pcJ \<in> hyp2`  and `?pc' \<in> hyp2` and `ps' \<in> S`
    and `B\<^sub>\<real> ?cd' ?ccJ ?cs'` and `B\<^sub>\<real> ?cd' ?cc' ?cs'`
  have "?pcJ = ?pc'" by (rule cosh_dist_unique)
  with `?paJ = ?pa'` and `?pbJ = ?pb'`
  have "hyp2_cltn2 a J = a'" and "hyp2_cltn2 b J = b'" and "hyp2_cltn2 c J = c'"
    by (unfold hyp2_cltn2_def) (simp_all add: Rep_hyp2_inverse)
  with `is_K2_isometry J`
  show "\<exists> J. is_K2_isometry J
    \<and> hyp2_cltn2 a J = a' \<and> hyp2_cltn2 b J = b' \<and> hyp2_cltn2 c J = c'"
    by (simp add: exI [of _ J])
qed

theorem hyp2_axiom5:
  "\<forall> a b c d a' b' c' d'.
  a \<noteq> b \<and> B\<^sub>K a b c \<and> B\<^sub>K a' b' c' \<and> a b \<congruent>\<^sub>K a' b' \<and> b c \<congruent>\<^sub>K b' c'
    \<and> a d \<congruent>\<^sub>K a' d' \<and> b d \<congruent>\<^sub>K b' d'
  \<longrightarrow> c d \<congruent>\<^sub>K c' d'"
proof standard+
  fix a b c d a' b' c' d'
  assume "a \<noteq> b \<and> B\<^sub>K a b c \<and> B\<^sub>K a' b' c' \<and> a b \<congruent>\<^sub>K a' b' \<and> b c \<congruent>\<^sub>K b' c'
    \<and> a d \<congruent>\<^sub>K a' d' \<and> b d \<congruent>\<^sub>K b' d'"
  hence "a \<noteq> b" and "B\<^sub>K a b c" and "B\<^sub>K a' b' c'" and "a b \<congruent>\<^sub>K a' b'"
    and "b c \<congruent>\<^sub>K b' c'" and "a d \<congruent>\<^sub>K a' d'" and "b d \<congruent>\<^sub>K b' d'"
    by simp_all

  from `a b \<congruent>\<^sub>K a' b'` and `b d \<congruent>\<^sub>K b' d'` and `a d \<congruent>\<^sub>K a' d'` and statement69 [of a b a' b' d d']
  obtain J where "is_K2_isometry J" and "hyp2_cltn2 a J = a'"
    and "hyp2_cltn2 b J = b'" and "hyp2_cltn2 d J = d'"
    by auto

  let ?aJ = "hyp2_cltn2 a J"
    and ?bJ = "hyp2_cltn2 b J"
    and ?cJ = "hyp2_cltn2 c J"
    and ?dJ = "hyp2_cltn2 d J"

  from `a \<noteq> b` and `a b \<congruent>\<^sub>K a' b'`
  have "a' \<noteq> b'" by (auto simp add: hyp2.A3')

  from `is_K2_isometry J` and `B\<^sub>K a b c`
  have "B\<^sub>K ?aJ ?bJ ?cJ" by (rule real_hyp2_B_hyp2_cltn2)
  hence "B\<^sub>K a' b' ?cJ" by (unfold `?aJ = a'` `?bJ = b'`)

  from `is_K2_isometry J`
  have "b c \<congruent>\<^sub>K ?bJ ?cJ" by (rule real_hyp2_C_hyp2_cltn2)
  hence "b c \<congruent>\<^sub>K b' ?cJ" by (unfold `?bJ = b'`)
  from this and `b c \<congruent>\<^sub>K b' c'` have "b' ?cJ \<congruent>\<^sub>K b' c'" by (rule hyp2.A2')
  with `a' \<noteq> b'` and `B\<^sub>K a' b' ?cJ` and `B\<^sub>K a' b' c'`
  have "?cJ = c'" by (rule hyp2_extend_segment_unique)
  from `is_K2_isometry J`
  show "c d \<congruent>\<^sub>K c' d'"
    unfolding `?cJ = c'` [symmetric] and `?dJ = d'` [symmetric]
    by (rule real_hyp2_C_hyp2_cltn2)
qed

interpretation hyp2: tarski_first5 real_hyp2_C real_hyp2_B
  using hyp2_axiom4 and hyp2_axiom5
  by unfold_locales

subsection {* The Klein--Beltrami model satisfies axioms 6, 7, and 11 *}

theorem hyp2_axiom6: "\<forall> a b. B\<^sub>K a b a \<longrightarrow> a = b"
proof standard+
  fix a b
  let ?ca = "cart2_pt (Rep_hyp2 a)"
    and ?cb = "cart2_pt (Rep_hyp2 b)"
  assume "B\<^sub>K a b a"
  hence "B\<^sub>\<real> ?ca ?cb ?ca" by (unfold real_hyp2_B_def hyp2_rep_def)
  hence "?ca = ?cb" by (rule real_euclid.A6')
  hence "Rep_hyp2 a = Rep_hyp2 b" by (simp add: Rep_hyp2 hyp2_S_cart2_inj)
  thus "a = b" by (unfold Rep_hyp2_inject)
qed

lemma between_inverse:
  assumes "B\<^sub>\<real> (hyp2_rep p) v (hyp2_rep q)"
  shows "hyp2_rep (hyp2_abs v) = v"
proof -
  let ?u = "hyp2_rep p"
  let ?w = "hyp2_rep q"
  have "norm ?u < 1" and "norm ?w < 1" by (rule norm_hyp2_rep_lt_1)+

  from `B\<^sub>\<real> ?u v ?w`
  obtain l where "l \<ge> 0" and "l \<le> 1" and "v - ?u = l *\<^sub>R (?w - ?u)"
    by (unfold real_euclid_B_def) auto
  from `v - ?u = l *\<^sub>R (?w - ?u)`
  have "v = l *\<^sub>R ?w + (1 - l) *\<^sub>R ?u" by (simp add: algebra_simps)
  hence "norm v \<le> norm (l *\<^sub>R ?w) + norm ((1 - l) *\<^sub>R ?u)"
    by (simp only: norm_triangle_ineq [of "l *\<^sub>R ?w" "(1 - l) *\<^sub>R ?u"])
  with `l \<ge> 0` and `l \<le> 1`
  have "norm v \<le> l *\<^sub>R norm ?w + (1 - l) *\<^sub>R norm ?u" by simp

  have "norm v < 1"
  proof cases
    assume "l = 0"
    with `v = l *\<^sub>R ?w + (1 - l) *\<^sub>R ?u`
    have "v = ?u" by simp
    with `norm ?u < 1` show "norm v < 1" by simp
  next
    assume "l \<noteq> 0"
    with `norm ?w < 1` and `l \<ge> 0` have "l *\<^sub>R norm ?w < l" by simp

    with `norm ?u < 1` and `l \<le> 1`
      and mult_mono [of "1 - l" "1 - l" "norm ?u" 1]
    have "(1 - l) *\<^sub>R norm ?u \<le> 1 - l" by simp
    with `l *\<^sub>R norm ?w < l`
    have "l *\<^sub>R norm ?w + (1 - l) *\<^sub>R norm ?u < 1" by simp
    with `norm v \<le> l *\<^sub>R norm ?w + (1 - l) *\<^sub>R norm ?u`
    show "norm v < 1" by simp
  qed
  thus "hyp2_rep (hyp2_abs v) = v" by (rule hyp2_rep_abs)
qed

lemma between_switch:
  assumes "B\<^sub>\<real> (hyp2_rep p) v (hyp2_rep q)"
  shows "B\<^sub>K p (hyp2_abs v) q"
proof -
  from assms have "hyp2_rep (hyp2_abs v) = v" by (rule between_inverse)
  with assms show "B\<^sub>K p (hyp2_abs v) q" by (unfold real_hyp2_B_def) simp
qed

theorem hyp2_axiom7:
  "\<forall> a b c p q. B\<^sub>K a p c \<and> B\<^sub>K b q c \<longrightarrow> (\<exists> x. B\<^sub>K p x b \<and> B\<^sub>K q x a)"
proof auto
  fix a b c p q
  let ?ca = "hyp2_rep a"
    and ?cb = "hyp2_rep b"
    and ?cc = "hyp2_rep c"
    and ?cp = "hyp2_rep p"
    and ?cq = "hyp2_rep q"
  assume "B\<^sub>K a p c" and "B\<^sub>K b q c"
  hence "B\<^sub>\<real> ?ca ?cp ?cc" and "B\<^sub>\<real> ?cb ?cq ?cc" by (unfold real_hyp2_B_def)
  with real_euclid.A7' [of ?ca ?cp ?cc ?cb ?cq]
  obtain cx where "B\<^sub>\<real> ?cp cx ?cb" and "B\<^sub>\<real> ?cq cx ?ca" by auto
  hence "B\<^sub>K p (hyp2_abs cx) b" and "B\<^sub>K q (hyp2_abs cx) a"
    by (simp_all add: between_switch)
  thus "\<exists> x. B\<^sub>K p x b \<and> B\<^sub>K q x a" by (simp add: exI [of _ "hyp2_abs cx"])
qed

theorem hyp2_axiom11:
  "\<forall> X Y. (\<exists> a. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>K a x y)
  \<longrightarrow> (\<exists> b. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>K x b y)"
proof (rule allI)+
  fix X Y :: "hyp2 set"
  show "(\<exists> a. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>K a x y)
    \<longrightarrow> (\<exists> b. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>K x b y)"
  proof cases
    assume "X = {} \<or> Y = {}"
    thus "(\<exists> a. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>K a x y)
      \<longrightarrow> (\<exists> b. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>K x b y)" by auto
  next
    assume "\<not> (X = {} \<or> Y = {})"
    hence "X \<noteq> {}" and "Y \<noteq> {}" by simp_all
    then obtain w and z where "w \<in> X" and "z \<in> Y" by auto

    show "(\<exists> a. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>K a x y)
      \<longrightarrow> (\<exists> b. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>K x b y)"
    proof
      assume "\<exists> a. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>K a x y"
      then obtain a where "\<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>K a x y" ..

      let ?cX = "hyp2_rep ` X"
        and ?cY = "hyp2_rep ` Y"
        and ?ca = "hyp2_rep a"
        and ?cw = "hyp2_rep w"
        and ?cz = "hyp2_rep z"

      from `\<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>K a x y`
      have "\<forall> cx cy. cx \<in> ?cX \<and> cy \<in> ?cY \<longrightarrow> B\<^sub>\<real> ?ca cx cy"
        by (unfold real_hyp2_B_def) auto
      with real_euclid.A11' [of ?cX ?cY ?ca]
      obtain cb where "\<forall> cx cy. cx \<in> ?cX \<and> cy \<in> ?cY \<longrightarrow> B\<^sub>\<real> cx cb cy" by auto
      with `w \<in> X` and `z \<in> Y` have "B\<^sub>\<real> ?cw cb ?cz" by simp
      hence "hyp2_rep (hyp2_abs cb) = cb" (is "hyp2_rep ?b = cb")
        by (rule between_inverse)
      with `\<forall> cx cy. cx \<in> ?cX \<and> cy \<in> ?cY \<longrightarrow> B\<^sub>\<real> cx cb cy`
      have "\<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>K x ?b y"
        by (unfold real_hyp2_B_def) simp
      thus "\<exists> b. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>K x b y" by (rule exI)
    qed
  qed
qed

interpretation tarski_absolute_space real_hyp2_C real_hyp2_B
  using hyp2_axiom6 and hyp2_axiom7 and hyp2_axiom11
  by unfold_locales

subsection {* The Klein--Beltrami model satisfies the dimension-specific axioms *}

lemma hyp2_rep_abs_examples:
  shows "hyp2_rep (hyp2_abs 0) = 0" (is "hyp2_rep ?a = ?ca")
  and "hyp2_rep (hyp2_abs (vector [1/2,0])) = vector [1/2,0]"
  (is "hyp2_rep ?b = ?cb")
  and "hyp2_rep (hyp2_abs (vector [0,1/2])) = vector [0,1/2]"
  (is "hyp2_rep ?c = ?cc")
  and "hyp2_rep (hyp2_abs (vector [1/4,1/4])) = vector [1/4,1/4]"
  (is "hyp2_rep ?d = ?cd")
  and "hyp2_rep (hyp2_abs (vector [1/2,1/2])) = vector [1/2,1/2]"
  (is "hyp2_rep ?t = ?ct")
proof -
  have "norm ?ca < 1" and "norm ?cb < 1" and "norm ?cc < 1" and "norm ?cd < 1"
    and "norm ?ct < 1"
    by (unfold norm_vec_def setL2_def) (simp_all add: sum_2 power2_eq_square)
  thus "hyp2_rep ?a = ?ca" and "hyp2_rep ?b = ?cb" and "hyp2_rep ?c = ?cc"
    and "hyp2_rep ?d = ?cd" and "hyp2_rep ?t = ?ct"
    by (simp_all add: hyp2_rep_abs)
qed

theorem hyp2_axiom8: "\<exists> a b c. \<not> B\<^sub>K a b c \<and> \<not> B\<^sub>K b c a \<and> \<not> B\<^sub>K c a b"
proof -
  let ?ca = "0 :: real^2"
    and ?cb = "vector [1/2,0] :: real^2"
    and ?cc = "vector [0,1/2] :: real^2"
  let ?a = "hyp2_abs ?ca"
    and ?b = "hyp2_abs ?cb"
    and ?c = "hyp2_abs ?cc"
  from hyp2_rep_abs_examples and non_Col_example
  have "\<not> (hyp2.Col ?a ?b ?c)"
    by (unfold hyp2.Col_def real_euclid.Col_def real_hyp2_B_def) simp
  thus "\<exists> a b c. \<not> B\<^sub>K a b c \<and> \<not> B\<^sub>K b c a \<and> \<not> B\<^sub>K c a b"
    unfolding hyp2.Col_def
    by simp (rule exI)+
qed

theorem hyp2_axiom9:
  "\<forall> p q a b c. p \<noteq> q \<and> a p \<congruent>\<^sub>K a q \<and> b p \<congruent>\<^sub>K b q \<and> c p \<congruent>\<^sub>K c q
  \<longrightarrow> B\<^sub>K a b c \<or> B\<^sub>K b c a \<or> B\<^sub>K c a b"
proof (rule allI)+
  fix p q a b c
  show "p \<noteq> q \<and> a p \<congruent>\<^sub>K a q \<and> b p \<congruent>\<^sub>K b q \<and> c p \<congruent>\<^sub>K c q
    \<longrightarrow> B\<^sub>K a b c \<or> B\<^sub>K b c a \<or> B\<^sub>K c a b"
  proof
    assume "p \<noteq> q \<and> a p \<congruent>\<^sub>K a q \<and> b p \<congruent>\<^sub>K b q \<and> c p \<congruent>\<^sub>K c q"
    hence "p \<noteq> q" and "a p \<congruent>\<^sub>K a q" and "b p \<congruent>\<^sub>K b q" and "c p \<congruent>\<^sub>K c q" by simp_all

    let ?pp = "Rep_hyp2 p"
      and ?pq = "Rep_hyp2 q"
      and ?pa = "Rep_hyp2 a"
      and ?pb = "Rep_hyp2 b"
      and ?pc = "Rep_hyp2 c"
    def l \<equiv> "proj2_line_through ?pp ?pq"
    def m \<equiv> "drop_perp ?pa l"
      and ps \<equiv> "endpoint_in_S ?pp ?pq"
      and pt \<equiv> "endpoint_in_S ?pq ?pp"
      and stpq \<equiv> "exp_2dist ?pp ?pq"

    from `p \<noteq> q` have "?pp \<noteq> ?pq" by (simp add: Rep_hyp2_inject)

    from Rep_hyp2
    have "stpq > 0" by (unfold stpq_def) (simp add: exp_2dist_positive)
    hence "sqrt stpq * sqrt stpq = stpq"
      by (simp add: real_sqrt_mult [symmetric])

    from Rep_hyp2 and `?pp \<noteq> ?pq`
    have "stpq \<noteq> 1" by (unfold stpq_def) (auto simp add: exp_2dist_1_equal)

    have "z_non_zero ?pa" and "z_non_zero ?pb" and "z_non_zero ?pc"
      by (simp_all add: Rep_hyp2 hyp2_S_z_non_zero)

    have "\<forall> pd \<in> {?pa,?pb,?pc}.
      cross_ratio ps pt (perp_foot pd l) ?pp = 1 / (sqrt stpq)"
    proof
      fix pd
      assume "pd \<in> {?pa,?pb,?pc}"
      with Rep_hyp2 have "pd \<in> hyp2" by auto

      def pe \<equiv> "perp_foot pd l"
        and x \<equiv> "cosh_dist ?pp pd"

      from `pd \<in> {?pa,?pb,?pc}` and `a p \<congruent>\<^sub>K a q` and `b p \<congruent>\<^sub>K b q`
        and `c p \<congruent>\<^sub>K c q`
      have "cosh_dist pd ?pp = cosh_dist pd ?pq"
        by (auto simp add: real_hyp2_C_cosh_dist)
      with `pd \<in> hyp2` and Rep_hyp2
      have "x = cosh_dist ?pq pd" by (unfold x_def) (simp add: cosh_dist_swap)

      from Rep_hyp2 [of p] and `pd \<in> hyp2` and cosh_dist_positive [of ?pp pd]
      have "x \<noteq> 0" by (unfold x_def) simp

      from Rep_hyp2 and `pd \<in> hyp2` and `?pp \<noteq> ?pq`
      have "cross_ratio ps pt pe ?pp
        = (cosh_dist ?pq pd * sqrt stpq - cosh_dist ?pp pd)
        / (cosh_dist ?pp pd *  stpq - cosh_dist ?pq pd * sqrt stpq)"
        unfolding ps_def and pt_def and pe_def and l_def and stpq_def
        by (simp add: perp_foot_cross_ratio_formula)
      also from x_def and `x = cosh_dist ?pq pd`
      have "\<dots> = (x * sqrt stpq - x) / (x * stpq - x * sqrt stpq)" by simp
      also from `sqrt stpq * sqrt stpq = stpq`
      have "\<dots> = (x * sqrt stpq - x) / ((x * sqrt stpq - x) * sqrt stpq)"
        by (simp add: algebra_simps)
      also from `x \<noteq> 0` and `stpq \<noteq> 1` have "\<dots> = 1 / sqrt stpq" by simp
      finally show "cross_ratio ps pt pe ?pp = 1 / sqrt stpq" .
    qed
    hence "cross_ratio ps pt (perp_foot ?pa l) ?pp = 1 / sqrt stpq" by simp

    have "\<forall> pd \<in> {?pa,?pb,?pc}. proj2_incident pd m"
    proof
      fix pd
      assume "pd \<in> {?pa,?pb,?pc}"
      with Rep_hyp2 have "pd \<in> hyp2" by auto
      with Rep_hyp2 and `?pp \<noteq> ?pq` and proj2_line_through_incident
      have "cross_ratio_correct ps pt ?pp (perp_foot pd l)"
        and "cross_ratio_correct ps pt ?pp (perp_foot ?pa l)"
        unfolding ps_def and pt_def and l_def
        by (simp_all add: endpoints_in_S_perp_foot_cross_ratio_correct)

      from `pd \<in> {?pa,?pb,?pc}`
        and `\<forall> pd \<in> {?pa,?pb,?pc}.
        cross_ratio ps pt (perp_foot pd l) ?pp = 1 / (sqrt stpq)`
      have "cross_ratio ps pt (perp_foot pd l) ?pp = 1 / sqrt stpq" by auto
      with `cross_ratio ps pt (perp_foot ?pa l) ?pp = 1 / sqrt stpq`
      have "cross_ratio ps pt (perp_foot pd l) ?pp
        = cross_ratio ps pt (perp_foot ?pa l) ?pp"
        by simp
      hence "cross_ratio ps pt ?pp (perp_foot pd l)
        = cross_ratio ps pt ?pp (perp_foot ?pa l)"
        by (simp add: cross_ratio_swap_34 [of ps pt _ ?pp])
      with `cross_ratio_correct ps pt ?pp (perp_foot pd l)`
        and `cross_ratio_correct ps pt ?pp (perp_foot ?pa l)`
      have "perp_foot pd l = perp_foot ?pa l" by (rule cross_ratio_unique)
      with Rep_hyp2 [of p] and `pd \<in> hyp2`
        and proj2_line_through_incident [of ?pp ?pq]
        and perp_foot_eq_implies_drop_perp_eq [of ?pp pd l ?pa]
      have "drop_perp pd l = m" by (unfold m_def l_def) simp
      with drop_perp_incident [of pd l] show "proj2_incident pd m" by simp
    qed
    hence "proj2_set_Col {?pa,?pb,?pc}"
      by (unfold proj2_set_Col_def) (simp add: exI [of _ m])
    hence "proj2_Col ?pa ?pb ?pc" by (simp add: proj2_Col_iff_set_Col)
    with `z_non_zero ?pa` and `z_non_zero ?pb` and `z_non_zero ?pc`
    have "real_euclid.Col (hyp2_rep a) (hyp2_rep b) (hyp2_rep c)"
      by (unfold hyp2_rep_def) (simp add: proj2_Col_iff_euclid_cart2)
    thus "B\<^sub>K a b c \<or> B\<^sub>K b c a \<or> B\<^sub>K c a b"
      by (unfold real_hyp2_B_def real_euclid.Col_def)
  qed
qed

interpretation hyp2: tarski_absolute real_hyp2_C real_hyp2_B
  using hyp2_axiom8 and hyp2_axiom9
  by unfold_locales

subsection {* The Klein--Beltrami model violates the Euclidean axiom *}

theorem hyp2_axiom10_false:
  shows "\<not> (\<forall> a b c d t. B\<^sub>K a d t \<and> B\<^sub>K b d c \<and> a \<noteq> d
  \<longrightarrow> (\<exists> x y. B\<^sub>K a b x \<and> B\<^sub>K a c y \<and> B\<^sub>K x t y))"
proof
  assume "\<forall> a b c d t. B\<^sub>K a d t \<and> B\<^sub>K b d c \<and> a \<noteq> d
    \<longrightarrow> (\<exists> x y. B\<^sub>K a b x \<and> B\<^sub>K a c y \<and> B\<^sub>K x t y)"

  let ?ca = "0 :: real^2"
    and ?cb = "vector [1/2,0] :: real^2"
    and ?cc = "vector [0,1/2] :: real^2"
    and ?cd = "vector [1/4,1/4] :: real^2"
    and ?ct = "vector [1/2,1/2] :: real^2"
  let ?a = "hyp2_abs ?ca"
    and ?b = "hyp2_abs ?cb"
    and ?c = "hyp2_abs ?cc"
    and ?d = "hyp2_abs ?cd"
    and ?t = "hyp2_abs ?ct"

  have "?cd = (1/2) *\<^sub>R ?ct" and "?cd - ?cb = (1/2) *\<^sub>R (?cc - ?cb)"
    by (unfold vector_def) (simp_all add: vec_eq_iff)
  hence "B\<^sub>\<real> ?ca ?cd ?ct" and "B\<^sub>\<real> ?cb ?cd ?cc"
    by (unfold real_euclid_B_def) (simp_all add: exI [of _ "1/2"])
  hence "B\<^sub>K ?a ?d ?t" and "B\<^sub>K ?b ?d ?c"
    by (unfold real_hyp2_B_def) (simp_all add: hyp2_rep_abs_examples)

  have "?a \<noteq> ?d"
  proof
    assume "?a = ?d"
    hence "hyp2_rep ?a = hyp2_rep ?d" by simp
    hence "?ca = ?cd" by (simp add: hyp2_rep_abs_examples)
    thus False by (simp add: vec_eq_iff forall_2)
  qed
  with `B\<^sub>K ?a ?d ?t` and `B\<^sub>K ?b ?d ?c`
    and `\<forall> a b c d t. B\<^sub>K a d t \<and> B\<^sub>K b d c \<and> a \<noteq> d
    \<longrightarrow> (\<exists> x y. B\<^sub>K a b x \<and> B\<^sub>K a c y \<and> B\<^sub>K x t y)`
  obtain x and y where "B\<^sub>K ?a ?b x" and "B\<^sub>K ?a ?c y" and "B\<^sub>K x ?t y"
    by blast

  let ?cx = "hyp2_rep x"
    and ?cy = "hyp2_rep y"
  from `B\<^sub>K ?a ?b x` and `B\<^sub>K ?a ?c y` and `B\<^sub>K x ?t y`
  have "B\<^sub>\<real> ?ca ?cb ?cx" and "B\<^sub>\<real> ?ca ?cc ?cy" and "B\<^sub>\<real> ?cx ?ct ?cy"
    by (unfold real_hyp2_B_def) (simp_all add: hyp2_rep_abs_examples)

  from `B\<^sub>\<real> ?ca ?cb ?cx` and `B\<^sub>\<real> ?ca ?cc ?cy` and `B\<^sub>\<real> ?cx ?ct ?cy`
  obtain j and k and l where "?cb - ?ca = j *\<^sub>R (?cx - ?ca)"
    and "?cc - ?ca = k *\<^sub>R (?cy - ?ca)"
    and "l \<ge> 0" and "l \<le> 1" and "?ct - ?cx = l *\<^sub>R (?cy - ?cx)"
    by (unfold real_euclid_B_def) fast

  from `?cb - ?ca = j *\<^sub>R (?cx - ?ca)` and `?cc - ?ca = k *\<^sub>R (?cy - ?ca)`
  have "j \<noteq> 0" and "k \<noteq> 0" by (auto simp add: vec_eq_iff forall_2)
  with `?cb - ?ca = j *\<^sub>R (?cx - ?ca)` and `?cc - ?ca = k *\<^sub>R (?cy - ?ca)`
  have "?cx = (1/j) *\<^sub>R ?cb" and "?cy = (1/k) *\<^sub>R ?cc" by simp_all
  hence "?cx$2 = 0" and "?cy$1 = 0" by simp_all

  from `?ct - ?cx = l *\<^sub>R (?cy - ?cx)`
  have "?ct = (1 - l) *\<^sub>R ?cx + l *\<^sub>R ?cy" by (simp add: algebra_simps)
  with `?cx$2 = 0` and `?cy$1 = 0`
  have "?ct$1 = (1 - l) * (?cx$1)" and "?ct$2 = l * (?cy$2)" by simp_all
  hence "l * (?cy$2) = 1/2" and "(1 - l) * (?cx$1) = 1/2" by simp_all

  have "?cx$1 \<le> \<bar>?cx$1\<bar>" by simp
  also have "\<dots> \<le> norm ?cx" by (rule component_le_norm_cart)
  also have "\<dots> < 1" by (rule norm_hyp2_rep_lt_1)
  finally have "?cx$1 < 1" .
  with `l \<le> 1` and mult_less_cancel_left [of "1 - l" "?cx$1" 1]
  have "(1 - l) * ?cx$1 \<le> 1 - l" by auto
  with `(1 - l) * (?cx$1) = 1/2` have "l \<le> 1/2" by simp

  have "?cy$2 \<le> \<bar>?cy$2\<bar>" by simp
  also have "\<dots> \<le> norm ?cy" by (rule component_le_norm_cart)
  also have "\<dots> < 1" by (rule norm_hyp2_rep_lt_1)
  finally have "?cy$2 < 1" .
  with `l \<ge> 0` and mult_less_cancel_left [of l "?cy$2" 1]
  have "l * ?cy$2 \<le> l" by auto
  with `l * (?cy$2) = 1/2` have "l \<ge> 1/2" by simp
  with `l \<le> 1/2` have "l = 1/2" by simp
  with `l * (?cy$2) = 1/2` have "?cy$2 = 1" by simp
  with `?cy$2 < 1` show False by simp
qed

theorem hyp2_not_tarski: "\<not> (tarski real_hyp2_C real_hyp2_B)"
  using hyp2_axiom10_false
  by (unfold tarski_def tarski_space_def tarski_space_axioms_def) simp

text {* Therefore axiom 10 is independent.*}

end
