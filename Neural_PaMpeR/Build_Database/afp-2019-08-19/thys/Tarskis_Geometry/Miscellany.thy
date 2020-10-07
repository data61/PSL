(*  Title:       Miscellaneous results
    Author:      Tim Makarios <tjm1983 at gmail.com>, 2012
    Maintainer:  Tim Makarios <tjm1983 at gmail.com>
*)

(*Some of these theorems were moved to the Isabelle repository *)

section "Miscellaneous results"

theory Miscellany
imports Metric
begin

lemma unordered_pair_element_equality:
  assumes "{p, q} = {r, s}" and "p = r"
  shows "q = s"
  using assms by (auto simp: doubleton_eq_iff)

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

lemma scalar_equiv: "r *s x = r *\<^sub>R x"
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
  from \<open>u \<bullet> x = 0\<close> have "u$1 * x$1 = -(u$2) * (x$2)"
    unfolding inner_vec_def
    by (simp add: sum_2)
  hence "u$1 * x$1 / x$1 = -u$2 / x$1 * x$2" by simp
  with \<open>x$1 \<noteq> 0\<close> have "u$1 = ?u'$1" by simp
  from \<open>x$1 \<noteq> 0\<close> have "u$2 = ?u'$2" by simp
  with \<open>u$1 = ?u'$1\<close> and real2_eq show "u = ?u'" by simp
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
  with real2_eq [of x 0] and \<open>x \<noteq> 0\<close> have "x$2 \<noteq> 0" by auto
  with dot2_rearrange_2 and \<open>u \<bullet> x = 0\<close> show ?thesis by blast
next
  assume "x$1 \<noteq> 0"
  with dot2_rearrange_1 and \<open>u \<bullet> x = 0\<close> show ?thesis by blast
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
  fixes u v x :: "real^'n"
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
  fixes u v x :: "real^'n"
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
  with \<open>a \<ge> 0\<close> and \<open>b \<ge> 0\<close> have "sqrt (4 * a * b) \<le> a + b"
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
  from \<open>refl_on A r\<close> and refl_on_allrel [of B] and refl_on_Int
  show ?thesis by auto
qed

lemma sym_allrel: "sym (A \<times> A)"
  unfolding sym_def
  by simp

lemma sym_restrict:
  assumes "sym r"
  shows "sym (r \<inter> A \<times> A)"
proof -
  from \<open>sym r\<close> and sym_allrel and sym_Int
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
  from \<open>equiv A r\<close> and equiv_allrel [of B] and equiv_Int
  show ?thesis by auto
qed

lemma invertible_times_eq_zero:
  fixes x :: "real^'n" and A :: "real^'n^'n"
  assumes "invertible A" and "A *v x = 0"
  shows "x = 0"
  using assms invertible_def matrix_left_invertible_ker by blast

lemma times_invertible_eq_zero:
  fixes x :: "real^'n" and A :: "real^'n^'n"
  assumes "invertible A" and "x v* A = 0"
  shows "x = 0"
  using transpose_invertible assms invertible_times_eq_zero by fastforce

lemma matrix_id_invertible:
  "invertible (mat 1 :: ('a::semiring_1)^'n^'n)"
  by (simp add: invertible_def)

lemma Image_refl_on_nonempty:
  assumes "refl_on A r" and "x \<in> A"
  shows "x \<in> r``{x}"
proof
  from \<open>refl_on A r\<close> and \<open>x \<in> A\<close> show "(x, x) \<in> r"
    unfolding refl_on_def
    by simp
qed

lemma quotient_element_nonempty:
  assumes "equiv A r" and "X \<in> A//r"
  shows "\<exists> x. x \<in> X"
  using assms in_quotient_imp_non_empty by fastforce

lemma zero_3: "(3::3) = 0"
  by simp

lemma card_suc_ge_insert:
  fixes A and x
  shows "card A + 1 \<ge> card (insert x A)"
  using card_insert_le_m1 by fastforce

lemma card_le_UNIV:
  fixes A :: "('n::finite) set"
  shows "card A \<le> CARD('n)"
  by (simp add: card_mono)

lemma partition_Image_element:
  assumes "equiv A r" and "X \<in> A//r" and "x \<in> X"
  shows "r``{x} = X"
  by (metis Image_singleton_iff assms equiv_class_eq_iff quotientE)

lemma card_insert_ge: "card (insert x A) \<ge> card A"
  by (metis card_infinite card_insert_le zero_le)

lemma choose_1:
  assumes "card S = 1"
  shows "\<exists> x. S = {x}"
  using \<open>card S = 1\<close> and card_eq_SucD [of S 0]
  by simp

lemma choose_2:
  assumes "card S = 2"
  shows "\<exists> x y. S = {x,y}"
proof -
  from \<open>card S = 2\<close> and card_eq_SucD [of S 1]
  obtain x and T where "S = insert x T" and "card T = 1" by auto
  from \<open>card T = 1\<close> and choose_1 obtain y where "T = {y}" by auto
  with \<open>S = insert x T\<close> have "S = {x,y}" by simp
  thus "\<exists> x y. S = {x,y}" by auto
qed

lemma choose_3:
  assumes "card S = 3"
  shows "\<exists> x y z. S = {x,y,z}"
proof -
  from \<open>card S = 3\<close> and card_eq_SucD [of S 2]
  obtain x and T where "S = insert x T" and "card T = 2" by auto
  from \<open>card T = 2\<close> and choose_2 [of T] obtain y and z where "T = {y,z}" by auto
  with \<open>S = insert x T\<close> have "S = {x,y,z}" by simp
  thus "\<exists> x y z. S = {x,y,z}" by auto
qed

lemma card_gt_0_diff_singleton:
  assumes "card S > 0" and "x \<in> S"
  shows "card (S - {x}) = card S - 1"
proof -
  from \<open>card S > 0\<close> have "finite S" by (rule card_ge_0_finite)
  with \<open>x \<in> S\<close>
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
    with \<open>j_int \<le> 3\<close> have "j_int < 3" by simp
    with \<open>0 \<le> j_int\<close> have "j_int \<in> {0..<3}" by simp
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
  by (simp add: assms same_sgn_sgn_add)

lemma sgn_div:
  fixes x y :: "'a::linordered_field"
  assumes "y \<noteq> 0" and "sgn x = sgn y"
  shows "x / y > 0"
  using assms sgn_1_pos sgn_eq_0_iff by fastforce

lemma abs_plus:
  fixes x y :: "'a::linordered_idom"
  assumes "sgn x = sgn y"
  shows "\<bar>x + y\<bar> = \<bar>x\<bar> + \<bar>y\<bar>"
  by (simp add: assms same_sgn_abs_add)

lemma sgn_plus_abs:
  fixes x y :: "'a::linordered_idom"
  assumes "\<bar>x\<bar> > \<bar>y\<bar>"
  shows "sgn (x + y) = sgn x"
  by (cases "x > 0") (use assms in auto)

end
