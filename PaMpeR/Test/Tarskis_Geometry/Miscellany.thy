(*  Title:       Miscellaneous results
    Author:      Tim Makarios <tjm1983 at gmail.com>, 2012
    Maintainer:  Tim Makarios <tjm1983 at gmail.com>
*)

(* After Isabelle 2012, some of these theorems
may be moved to the Isabelle repository *)

section "Miscellaneous results"

theory Miscellany
imports
  "HOL-Analysis.Cartesian_Euclidean_Space"
  Metric "../Assertion_Checker"
begin

lemma unordered_pair_element_equality:
  assumes "{p, q} = {r, s}" and "p = r"
  shows "q = s"
proof cases
  assume "p = q"
  with `{p, q} = {r, s}` have "{r, s} = {q}" by simp
  thus "q = s" by simp
next
  assume "p \<noteq> q"
  with `{p, q} = {r, s}` have "{r, s} - {p} = {q}" by auto
  moreover
    from `p = r` have "{r, s} - {p} \<subseteq> {s}" by auto
  ultimately have "{q} \<subseteq> {s}" by simp
  thus "q = s" by simp
qed

lemma unordered_pair_equality: "{p, q} = {q, p}"
  by auto

lemma cosine_rule:
  fixes a b c :: "real ^ ('n::finite)"
  shows "(norm_dist a c)\<^sup>2 =
  (norm_dist a b)\<^sup>2 + (norm_dist b c)\<^sup>2 + 2 * ((a - b) \<bullet> (b - c))"
proof -
  have "(a - b) + (b - c) = a - c" by simp
  with dot_norm [of "a - b" "b - c"]
    have "(a - b) \<bullet> (b - c) =
        ((norm (a - c))\<^sup>2 - (norm (a - b))\<^sup>2 - (norm (b - c))\<^sup>2) / 2"
      by simp
  thus ?thesis by simp
qed

lemma scalar_equiv: "r *s x = r *\<^sub>R x"assert_nth_true 70 assert_nth_true 71 assert_nth_true 72
  by vector

lemma norm_dist_dot: "(norm_dist x y)\<^sup>2 = (x - y) \<bullet> (x - y)"
  by (simp add: power2_norm_eq_inner)

definition dep2 :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> bool" where
  "dep2 u v \<equiv> \<exists>w r s. u = r *\<^sub>R w \<and> v = s *\<^sub>R w"

lemma real2_eq:
  fixes u v :: "real^2"
  assumes "u$1 = v$1" and "u$2 = v$2"
  shows "u = v"
  by (simp add: vec_eq_iff [of u v] forall_2 assms)

definition rotate2 :: "real^2 \<Rightarrow> real^2" where
  "rotate2 x \<equiv> vector [-x$2, x$1]"

declare vector_2 [simp]

lemma rotate2 [simp]:
  "(rotate2 x)$1 = -x$2"
  "(rotate2 x)$2 = x$1"
  by (simp add: rotate2_def)+

lemma rotate2_rotate2 [simp]: "rotate2 (rotate2 x) = -x"
proof -
  have "(rotate2 (rotate2 x))$1 = -x$1" and "(rotate2 (rotate2 x))$2 = -x$2"
    by simp+
  with real2_eq show "rotate2 (rotate2 x) = -x" by simp
qed

lemma rotate2_dot [simp]: "(rotate2 u) \<bullet> (rotate2 v) = u \<bullet> v"
  unfolding inner_vec_def
  by (simp add: sum_2)

lemma rotate2_scaleR [simp]: "rotate2 (k *\<^sub>R x) = k *\<^sub>R (rotate2 x)"
proof -
  have "(rotate2 (k *\<^sub>R x))$1 = (k *\<^sub>R (rotate2 x))$1" and
    "(rotate2 (k *\<^sub>R x))$2 = (k *\<^sub>R (rotate2 x))$2" by simp+
  with real2_eq show ?thesis by simp
qed

lemma rotate2_uminus [simp]: "rotate2 (-x) = -(rotate2 x)"
proof -
  from scaleR_minus_left [of 1] have
    "-1 *\<^sub>R x = -x" and "-1 *\<^sub>R (rotate2 x) = -(rotate2 x)" by auto
  with rotate2_scaleR [of "-1" x] show ?thesis by simp
qed

lemma rotate2_eq [iff]: "rotate2 x = rotate2 y \<longleftrightarrow> x = y"
proof
  assume "x = y"
  thus "rotate2 x = rotate2 y" by simp
next
  assume "rotate2 x = rotate2 y"
  hence "rotate2 (rotate2 x) = rotate2 (rotate2 y)" by simp
  hence "-(-x) = -(-y)" by simp
  thus "x = y" by simp
qed

lemma dot2_rearrange_1:
  fixes u x :: "real^2"
  assumes "u \<bullet> x = 0" and "x$1 \<noteq> 0"
  shows "u = (u$2 / x$1) *\<^sub>R (rotate2 x)" (is "u = ?u'")
proof -
  from `u \<bullet> x = 0` have "u$1 * x$1 = -(u$2) * (x$2)"
    unfolding inner_vec_def
    by (simp add: sum_2)
  hence "u$1 * x$1 / x$1 = -u$2 / x$1 * x$2" by simp
  with `x$1 \<noteq> 0` have "u$1 = ?u'$1" by simp
  from `x$1 \<noteq> 0` have "u$2 = ?u'$2" by simp
  with `u$1 = ?u'$1` and real2_eq show "u = ?u'" by simp
qed

lemma dot2_rearrange_2:
  fixes u x :: "real^2"
  assumes "u \<bullet> x = 0" and "x$2 \<noteq> 0"
  shows "u = -(u$1 / x$2) *\<^sub>R (rotate2 x)" (is "u = ?u'")
proof -
  from assms and dot2_rearrange_1 [of "rotate2 u" "rotate2 x"] have
    "rotate2 u = rotate2 ?u'" by simp
  thus "u = ?u'" by blast
qed

lemma dot2_rearrange:
  fixes u x :: "real^2"
  assumes "u \<bullet> x = 0" and "x \<noteq> 0"
  shows "\<exists>k. u = k *\<^sub>R (rotate2 x)"
proof cases
  assume "x$1 = 0"
  with real2_eq [of x 0] and `x \<noteq> 0` have "x$2 \<noteq> 0" by auto
  with dot2_rearrange_2 and `u \<bullet> x = 0` show ?thesis by blast
next
  assume "x$1 \<noteq> 0"
  with dot2_rearrange_1 and `u \<bullet> x = 0` show ?thesis by blast
qed

lemma real2_orthogonal_dep2:
  fixes u v x :: "real^2"
  assumes "x \<noteq> 0" and "u \<bullet> x = 0" and "v \<bullet> x = 0"
  shows "dep2 u v"
proof -
  let ?w = "rotate2 x"
  from dot2_rearrange and assms have
    "\<exists>r s. u = r *\<^sub>R ?w \<and> v = s *\<^sub>R ?w" by simp
  with dep2_def show ?thesis by auto
qed

lemma dot_left_diff_distrib:
  fixes u v x :: "real^('n::finite)"
  shows "(u - v) \<bullet> x = (u \<bullet> x) - (v \<bullet> x)"
proof -
  have "(u \<bullet> x) - (v \<bullet> x) = (\<Sum>i\<in>UNIV. u$i * x$i) - (\<Sum>i\<in>UNIV. v$i * x$i)"
    unfolding inner_vec_def
    by simp
  also from sum_subtractf [of "\<lambda> i. u$i * x$i" "\<lambda> i. v$i * x$i"] have
    "\<dots> = (\<Sum>i\<in>UNIV. u$i * x$i - v$i * x$i)" by simp
  also from left_diff_distrib [where 'a = real] have
    "\<dots> = (\<Sum>i\<in>UNIV. (u$i - v$i) * x$i)" by simp
  also have
    "\<dots> = (u - v) \<bullet> x"
    unfolding inner_vec_def
    by simp
  finally show ?thesis ..
qed

lemma dot_right_diff_distrib:
  fixes u v x :: "real^('n::finite)"
  shows "x \<bullet> (u - v) = (x \<bullet> u) - (x \<bullet> v)"
proof -
  from inner_commute have "x \<bullet> (u - v) = (u - v) \<bullet> x" by auto
  also from dot_left_diff_distrib [of u v x] have
    "\<dots> = u \<bullet> x - v \<bullet> x" .
  also from inner_commute [of x] have
    "\<dots> = x \<bullet> u - x \<bullet> v" by simp
  finally show ?thesis .
qed

lemma am_gm2:
  fixes a b :: real
  assumes "a \<ge> 0" and "b \<ge> 0"
  shows "sqrt (a * b) \<le> (a + b) / 2"
  and "sqrt (a * b) = (a + b) / 2 \<longleftrightarrow> a = b"
proof -
  have "0 \<le> (a - b) * (a - b)" and "0 = (a - b) * (a - b) \<longleftrightarrow> a = b" by simp+
  with right_diff_distrib [of "a - b" a b] and left_diff_distrib [of a b] have
    "0 \<le> a * a - 2 * a * b + b * b"
    and "0 = a * a - 2 * a * b + b * b \<longleftrightarrow> a = b" by auto
  hence "4 * a * b \<le> a * a + 2 * a * b + b * b"
    and "4 * a * b = a * a + 2 * a * b + b * b \<longleftrightarrow> a = b" by auto
  with distrib_right [of "a + b" a b] and distrib_left [of a b] have
    "4 * a * b \<le> (a + b) * (a + b)"
    and "4 * a * b = (a + b) * (a + b) \<longleftrightarrow> a = b" by (simp add: field_simps)+
  with real_sqrt_le_mono [of "4 * a * b" "(a + b) * (a + b)"]
    and real_sqrt_eq_iff [of "4 * a * b" "(a + b) * (a + b)"] have
    "sqrt (4 * a * b) \<le> sqrt ((a + b) * (a + b))"
    and "sqrt (4 * a * b) = sqrt ((a + b) * (a + b)) \<longleftrightarrow> a = b" by simp+
  with `a \<ge> 0` and `b \<ge> 0` have "sqrt (4 * a * b) \<le> a + b"
    and "sqrt (4 * a * b) = a + b \<longleftrightarrow> a = b" by simp+
  with real_sqrt_abs2 [of 2] and real_sqrt_mult [of 4 "a * b"] show
    "sqrt (a * b) \<le> (a + b) / 2"
    and "sqrt (a * b) = (a + b) / 2 \<longleftrightarrow> a = b" by (simp add: ac_simps)+
qed

lemma refl_on_allrel: "refl_on A (A \<times> A)"
  unfolding refl_on_def
  by simp

lemma refl_on_restrict:
  assumes "refl_on A r"
  shows "refl_on (A \<inter> B) (r \<inter> B \<times> B)"
proof -
  from `refl_on A r` and refl_on_allrel [of B] and refl_on_Int
  show ?thesis by auto
qed

lemma sym_allrel: "sym (A \<times> A)"
  unfolding sym_def
  by simp

lemma sym_restrict:
  assumes "sym r"
  shows "sym (r \<inter> A \<times> A)"
proof -
  from `sym r` and sym_allrel and sym_Int
  show ?thesis by auto
qed

lemma trans_allrel: "trans (A \<times> A)"
  unfolding trans_def
  by simp

lemma equiv_Int:
  assumes "equiv A r" and "equiv B s"
  shows "equiv (A \<inter> B) (r \<inter> s)"
proof -
  from assms and refl_on_Int [of A r B s] and sym_Int and trans_Int
  show ?thesis
    unfolding equiv_def
    by auto
qed

lemma equiv_allrel: "equiv A (A \<times> A)"
  unfolding equiv_def
  by (simp add: refl_on_allrel sym_allrel trans_allrel)

lemma equiv_restrict:
  assumes "equiv A r"
  shows "equiv (A \<inter> B) (r \<inter> B \<times> B)"
proof -
  from `equiv A r` and equiv_allrel [of B] and equiv_Int
  show ?thesis by auto
qed

lemma scalar_vector_matrix_assoc:
  fixes k :: real and x :: "real^('n::finite)" and A :: "real^('m::finite)^'n"
  shows "(k *\<^sub>R x) v* A = k *\<^sub>R (x v* A)"
proof -
  { fix i
    from sum_distrib_left [of k "\<lambda>j. x$j * A$j$i" UNIV]
    have "(\<Sum>j\<in>UNIV. k * (x$j * A$j$i)) = k * (\<Sum>j\<in>UNIV. x$j * A$j$i)" .. }
  thus "(k *\<^sub>R x) v* A = k *\<^sub>R (x v* A)"
    unfolding vector_matrix_mult_def
    by (simp add: vec_eq_iff algebra_simps)
qed

lemma vector_scalar_matrix_ac:
  fixes k :: real and x :: "real^('n::finite)" and A :: "real^('m::finite)^'n"
  shows "x v* (k *\<^sub>R A) = k *\<^sub>R (x v* A)"
proof -
  have "x v* (k *\<^sub>R A) = (k *\<^sub>R x) v* A"
    unfolding vector_matrix_mult_def
    by (simp add: algebra_simps)
  with scalar_vector_matrix_assoc
  show "x v* (k *\<^sub>R A) = k *\<^sub>R (x v* A)"
    by auto
qed

lemma vector_matrix_left_distrib:
  fixes x y :: "real^('n::finite)" and A :: "real^('m::finite)^'n"
  shows "(x + y) v* A = x v* A + y v* A"
  unfolding vector_matrix_mult_def
  by (simp add: algebra_simps sum.distrib vec_eq_iff)

lemma times_zero_vector [simp]: "A *v 0 = 0"
  unfolding matrix_vector_mult_def
  by (simp add: vec_eq_iff)

lemma invertible_times_eq_zero:
  fixes x :: "real^('n::finite)" and A :: "real^'n^'n"
  assumes "invertible A" and "A *v x = 0"
  shows "x = 0"
proof -
  from `invertible A`
    and someI_ex [of "\<lambda>A'. A ** A' = mat 1 \<and> A' ** A = mat 1"]
  have "matrix_inv A ** A = mat 1"
    unfolding invertible_def matrix_inv_def
    by simp
  hence "x = (matrix_inv A ** A) *v x" by (simp add: matrix_vector_mul_lid)
  also have "\<dots> = matrix_inv A *v (A *v x)"
    by (simp add: matrix_vector_mul_assoc)
  also from `A *v x = 0` have "\<dots> = 0" by simp
  finally show "x = 0" .
qed

lemma vector_transpose_matrix [simp]: "x v* transpose A = A *v x"
  unfolding transpose_def vector_matrix_mult_def matrix_vector_mult_def
  by simp

lemma transpose_matrix_vector [simp]: "transpose A *v x = x v* A"
  unfolding transpose_def vector_matrix_mult_def matrix_vector_mult_def
  by simp

lemma transpose_invertible:
  fixes A :: "real^('n::finite)^'n"
  assumes "invertible A"
  shows "invertible (transpose A)"
proof -
  from `invertible A` obtain A' where "A ** A' = mat 1" and "A' ** A = mat 1"
    unfolding invertible_def
    by auto
  with matrix_transpose_mul [of A A'] and matrix_transpose_mul [of A' A]
  have "transpose A' ** transpose A = mat 1" and "transpose A ** transpose A' = mat 1"
    by (simp add: transpose_mat)+
  thus "invertible (transpose A)"
    unfolding invertible_def
    by auto
qed

lemma times_invertible_eq_zero:
  fixes x :: "real^('n::finite)" and A :: "real^'n^'n"
  assumes "invertible A" and "x v* A = 0"
  shows "x = 0"
proof -
  from transpose_invertible and `invertible A` have "invertible (transpose A)" by auto
  with invertible_times_eq_zero [of "transpose A" x] and `x v* A = 0`
  show "x = 0" by simp
qed

lemma matrix_id_invertible:
  "invertible (mat 1 :: ('a::semiring_1)^('n::finite)^'n)"
proof -
  from matrix_mul_lid [of "mat 1 :: 'a^'n^'n"]
  show "invertible (mat 1 :: 'a^'n^'n)"
    unfolding invertible_def
    by auto
qed

lemma Image_refl_on_nonempty:
  assumes "refl_on A r" and "x \<in> A"
  shows "x \<in> r``{x}"
proof
  from `refl_on A r` and `x \<in> A` show "(x, x) \<in> r"
    unfolding refl_on_def
    by simp
qed

lemma quotient_element_nonempty:
  assumes "equiv A r" and "X \<in> A//r"
  shows "\<exists> x. x \<in> X"
proof -
  from `X \<in> A//r` obtain x where "x \<in> A" and "X = r``{x}"
    unfolding quotient_def
    by auto
  with equiv_class_self [of A r x] and `equiv A r` show "\<exists> x. x \<in> X" by auto
qed

lemma zero_3: "(3::3) = 0"
  by simp

lemma card_suc_ge_insert:
  fixes A and x
  shows "card A + 1 \<ge> card (insert x A)"
proof cases
  assume "finite A"
  with card_insert_if [of A x] show "card A + 1 \<ge> card (insert x A)" by simp
next
  assume "infinite A"
  thus "card A + 1 \<ge> card (insert x A)" by simp
qed

lemma card_le_UNIV:
  fixes A :: "('n::finite) set"
  shows "card A \<le> CARD('n)"
  by (simp add: card_mono)

lemma partition_Image_element:
  assumes "equiv A r" and "X \<in> A//r" and "x \<in> X"
  shows "r``{x} = X"
proof -
  from Union_quotient and assms have "x \<in> A" by auto
  with quotientI [of x A r] have "r``{x} \<in> A//r" by simp

  from equiv_class_self and `equiv A r` and `x \<in> A` have "x \<in> r``{x}" by simp

  from `equiv A r` and `x \<in> A` have "(x, x) \<in> r"
    unfolding equiv_def and refl_on_def
    by simp

  with quotient_eqI [of A r X "r``{x}" x x]
    and assms and `Image r {x} \<in> A//r` and `x \<in> Image r {x}`
  show "r``{x} = X" by simp
qed

lemma card_insert_ge: "card (insert x A) \<ge> card A"
proof cases
  assume "finite A"
  with card_insert_le [of A x] show "card (insert x A) \<ge> card A" by simp
next
  assume "infinite A"
  hence "card A = 0" by simp
  thus "card (insert x A) \<ge> card A" by simp
qed

lemma choose_1:
  assumes "card S = 1"
  shows "\<exists> x. S = {x}"
  using `card S = 1` and card_eq_SucD [of S 0]
  by simp

lemma choose_2:
  assumes "card S = 2"
  shows "\<exists> x y. S = {x,y}"
proof -
  from `card S = 2` and card_eq_SucD [of S 1]
  obtain x and T where "S = insert x T" and "card T = 1" by auto
  from `card T = 1` and choose_1 obtain y where "T = {y}" by auto
  with `S = insert x T` have "S = {x,y}" by simp
  thus "\<exists> x y. S = {x,y}" by auto
qed

lemma choose_3:
  assumes "card S = 3"
  shows "\<exists> x y z. S = {x,y,z}"
proof -
  from `card S = 3` and card_eq_SucD [of S 2]
  obtain x and T where "S = insert x T" and "card T = 2" by auto
  from `card T = 2` and choose_2 [of T] obtain y and z where "T = {y,z}" by auto
  with `S = insert x T` have "S = {x,y,z}" by simp
  thus "\<exists> x y z. S = {x,y,z}" by auto
qed

lemma card_gt_0_diff_singleton:
  assumes "card S > 0" and "x \<in> S"
  shows "card (S - {x}) = card S - 1"
proof -
  from `card S > 0` have "finite S" by (rule card_ge_0_finite)
  with `x \<in> S`
  show "card (S - {x}) = card S - 1" by (simp add: card_Diff_singleton)
qed

lemma eq_3_or_of_3:
  fixes j :: 4
  shows "j = 3 \<or> (\<exists> j'::3. j = of_int (Rep_bit1 j'))"
proof (induct j)
  fix j_int :: int
  assume "0 \<le> j_int"
  assume "j_int < int CARD(4)"
  hence "j_int \<le> 3" by simp

  show "of_int j_int = (3::4) \<or> (\<exists> j'::3. of_int j_int = of_int (Rep_bit1 j'))"
  proof cases
    assume "j_int = 3"
    thus
      "of_int j_int = (3::4) \<or> (\<exists> j'::3. of_int j_int = of_int (Rep_bit1 j'))"
      by simp
  next
    assume "j_int \<noteq> 3"
    with `j_int \<le> 3` have "j_int < 3" by simp
    with `0 \<le> j_int` have "j_int \<in> {0..<3}" by simp
    hence "Rep_bit1 (Abs_bit1 j_int :: 3) = j_int"
      by (simp add: bit1.Abs_inverse)
    hence "of_int j_int = of_int (Rep_bit1 (Abs_bit1 j_int :: 3))" by simp
    thus
      "of_int j_int = (3::4) \<or> (\<exists> j'::3. of_int j_int = of_int (Rep_bit1 j'))"
      by auto
  qed
qed

lemma sgn_plus:
  fixes x y :: "'a::linordered_idom"
  assumes "sgn x = sgn y"
  shows "sgn (x + y) = sgn x"
proof cases
  assume "x = 0"
  with `sgn x = sgn y` have "y = 0" by (simp add: sgn_0_0)
  with `x = 0` show "sgn (x + y) = sgn x" by (simp add: sgn_0_0)
next
  assume "x \<noteq> 0"
  show "sgn (x + y) = sgn x"
  proof cases
    assume "x > 0"
    with `sgn x = sgn y` and sgn_1_pos [where ?'a = 'a] have "y > 0" by simp
    with `x > 0` and sgn_1_pos [where ?'a = 'a]
    show "sgn (x + y) = sgn x" by simp
  next
    assume "\<not> x > 0"
    with `x \<noteq> 0` have "x < 0" by simp
    with `sgn x = sgn y` and sgn_1_neg [where ?'a = 'a] have "y < 0" by auto
    with `x < 0` and sgn_1_neg [where ?'a = 'a]
    show "sgn (x + y) = sgn x" by simp
  qed
qed

lemma sgn_div:
  fixes x y :: "'a::linordered_field"
  assumes "y \<noteq> 0" and "sgn x = sgn y"
  shows "x / y > 0"
proof cases
  assume "y > 0"
  with `sgn x = sgn y` and sgn_1_pos [where ?'a = 'a] have "x > 0" by simp
  with `y > 0` show "x / y > 0" by (simp add: zero_less_divide_iff)
next
  assume "\<not> y > 0"
  with `y \<noteq> 0` have "y < 0" by simp
  with `sgn x = sgn y` and sgn_1_neg [where ?'a = 'a] have "x < 0" by simp
  with `y < 0` show "x / y > 0" by (simp add: zero_less_divide_iff)
qed

lemma abs_plus:
  fixes x y :: "'a::linordered_idom"
  assumes "sgn x = sgn y"
  shows "\<bar>x + y\<bar> = \<bar>x\<bar> + \<bar>y\<bar>"
proof -
  from `sgn x = sgn y` have "sgn (x + y) = sgn x" by (rule sgn_plus)
  hence "\<bar>x + y\<bar> = (x + y) * sgn x" by (simp add: abs_sgn)
  also from `sgn x = sgn y`
  have "\<dots> = x * sgn x + y * sgn y" by (simp add: algebra_simps)
  finally show "\<bar>x + y\<bar> = \<bar>x\<bar> + \<bar>y\<bar>" by (simp add: abs_sgn)
qed

lemma sgn_plus_abs:
  fixes x y :: "'a::linordered_idom"
  assumes "\<bar>x\<bar> > \<bar>y\<bar>"
  shows "sgn (x + y) = sgn x"
proof cases
  assume "x > 0"
  with `\<bar>x\<bar> > \<bar>y\<bar>` have "x + y > 0" by simp
  with `x > 0` show "sgn (x + y) = sgn x" by simp
next
  assume "\<not> x > 0"

  from `\<bar>x\<bar> > \<bar>y\<bar>` have "x \<noteq> 0" by simp
  with `\<not> x > 0` have "x < 0" by simp
  with `\<bar>x\<bar> > \<bar>y\<bar>` have "x + y < 0" by simp
  with `x < 0` show "sgn (x + y) = sgn x" by simp
qed

lemma sqrt_4 [simp]: "sqrt 4 = 2"
proof -
  have "sqrt 4 = sqrt (2 * 2)" by simp
  thus "sqrt 4 = 2" by (unfold real_sqrt_abs2) simp
qed

end
