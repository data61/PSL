(*  Title:       Some extra results about linear algebra
    Author:      Tim Makarios <tjm1983 at gmail.com>, 2012
    Maintainer:  Tim Makarios <tjm1983 at gmail.com>
*)

(* Some of these theorems previously here have been moved to the Isabelle repository *)

section "Linear algebra"

theory Linear_Algebra2
imports Miscellany
begin

lemma exhaust_4:
  fixes x :: 4
  shows "x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4"
proof (induct x)
  case (of_int z)
  hence "0 \<le> z" and "z < 4" by simp_all
  hence "z = 0 \<or> z = 1 \<or> z = 2 \<or> z = 3" by arith
  thus ?case by auto
qed

lemma forall_4: "(\<forall> i::4. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3 \<and> P 4"
  by (metis exhaust_4)

lemma UNIV_4: "(UNIV::(4 set)) = {1, 2, 3, 4}"
  using exhaust_4
  by auto

lemma vector_4:
  fixes w :: "'a::zero"
  shows "(vector [w, x, y, z] :: 'a^4)$1 = w"
  and  "(vector [w, x, y, z] :: 'a^4)$2 = x"
  and  "(vector [w, x, y, z] :: 'a^4)$3 = y"
  and  "(vector [w, x, y, z] :: 'a^4)$4 = z"
  unfolding vector_def
  by simp_all

definition
  is_basis :: "(real^'n) set \<Rightarrow> bool" where
  "is_basis S \<equiv> independent S \<and> span S = UNIV"

lemma card_finite:
  assumes "card S = CARD('n::finite)"
  shows "finite S"
proof -
  from \<open>card S = CARD('n)\<close> have "card S \<noteq> 0" by simp
  with card_eq_0_iff [of S] show "finite S" by simp
qed

lemma independent_is_basis:
  fixes B :: "(real^'n) set"
  shows "independent B \<and> card B = CARD('n) \<longleftrightarrow> is_basis B"
proof
  assume L: "independent B \<and> card B = CARD('n)" 
  then have "card (Basis::(real^'n) set) = card B"
    by simp
  with L show "is_basis B"
    by (metis (no_types) card_eq_dim dim_UNIV independent_bound is_basis_def subset_antisym top_greatest)
next
  assume "is_basis B"
  then  show "independent B \<and> card B = CARD('n)"
    by (metis DIM_cart DIM_real basis_card_eq_dim dim_UNIV is_basis_def mult.right_neutral top.extremum)
qed

lemma basis_finite:
  fixes B :: "(real^'n) set"
  assumes "is_basis B"
  shows "finite B"
proof -
  from independent_is_basis [of B] and \<open>is_basis B\<close> have "card B = CARD('n)"
    by simp
  with card_finite [of B, where 'n = 'n] show "finite B" by simp
qed

lemma basis_expand:
  assumes "is_basis B"
  shows "\<exists>c. v = (\<Sum>w\<in>B. (c w) *\<^sub>R w)"
proof -
  from \<open>is_basis B\<close> have "v \<in> span B" unfolding is_basis_def by simp
  from basis_finite [of B] and \<open>is_basis B\<close> have "finite B" by simp
  with span_finite [of B] and \<open>v \<in> span B\<close>
  show "\<exists>c. v = (\<Sum>w\<in>B. (c w) *\<^sub>R w)" by (simp add: scalar_equiv) auto
qed

lemma not_span_independent_insert:
  fixes v :: "('a::real_vector)^'n"
  assumes "independent S" and "v \<notin> span S"
  shows "independent (insert v S)"
  by (simp add: assms independent_insert)

lemma orthogonal_sum:
  fixes v :: "real^'n"
  assumes "\<And>w. w\<in>S \<Longrightarrow> orthogonal v w"
  shows "orthogonal v (\<Sum>w\<in>S. c w *s w)"
  by (metis (no_types, lifting) assms orthogonal_clauses(1,2) orthogonal_rvsum scalar_equiv sum.infinite)

lemma orthogonal_self_eq_0:
  fixes v :: "('a::real_inner)^'n"
  assumes "orthogonal v v"
  shows "v = 0"
  using inner_eq_zero_iff [of v] and assms
  unfolding orthogonal_def
  by simp

lemma orthogonal_in_span_eq_0:
  fixes v :: "real^'n"
  assumes "v \<in> span S" and "\<And>w. w\<in>S \<Longrightarrow> orthogonal v w"
  shows "v = 0"
  using assms orthogonal_self orthogonal_to_span by blast

lemma orthogonal_independent:
  fixes v :: "real^'n"
  assumes "independent S" and "v \<noteq> 0" and "\<And>w. w\<in>S \<Longrightarrow> orthogonal v w"
  shows "independent (insert v S)"
  using assms not_span_independent_insert orthogonal_in_span_eq_0 by blast

lemma dot_scaleR_mult:
  shows "(k *\<^sub>R a) \<bullet> b = k * (a \<bullet> b)" and "a \<bullet> (k *\<^sub>R b) = k * (a \<bullet> b)"
  by auto

lemma dependent_explicit_finite:
  fixes S :: "(('a::{real_vector,field})^'n) set"
  assumes "finite S"
  shows "dependent S \<longleftrightarrow> (\<exists> u. (\<exists> v\<in>S. u v \<noteq> 0) \<and> (\<Sum> v\<in>S. u v *\<^sub>R v) = 0)"
  by (simp add: assms dependent_finite)

lemma dependent_explicit_2:
  fixes v w :: "('a::{field,real_vector})^'n"
  assumes "v \<noteq> w"
  shows "dependent {v, w} \<longleftrightarrow> (\<exists> i j. (i \<noteq> 0 \<or> j \<noteq> 0) \<and> i *\<^sub>R v + j *\<^sub>R w = 0)"
proof
  let ?S = "{v, w}"
  have "finite ?S" by simp

  { assume "dependent ?S"
    with dependent_explicit_finite [of ?S] and \<open>finite ?S\<close> and \<open>v \<noteq> w\<close>
    show "\<exists> i j. (i \<noteq> 0 \<or> j \<noteq> 0) \<and> i *\<^sub>R v + j *\<^sub>R w = 0" by auto }

  { assume "\<exists> i j. (i \<noteq> 0 \<or> j \<noteq> 0) \<and> i *\<^sub>R v + j *\<^sub>R w = 0"
    then obtain i and j where "i \<noteq> 0 \<or> j \<noteq> 0" and "i *\<^sub>R v + j *\<^sub>R w = 0" by auto
    let ?u = "\<lambda> x. if x = v then i else j"
    from \<open>i \<noteq> 0 \<or> j \<noteq> 0\<close> and \<open>v \<noteq> w\<close> have "\<exists> x\<in>?S. ?u x \<noteq> 0" by simp
    from \<open>i *\<^sub>R v + j *\<^sub>R w = 0\<close> and \<open>v \<noteq> w\<close>
    have "(\<Sum> x\<in>?S. ?u x *\<^sub>R x) = 0" by simp
    with dependent_explicit_finite [of ?S]
      and \<open>finite ?S\<close> and \<open>\<exists> x\<in>?S. ?u x \<noteq> 0\<close>
    show "dependent ?S" by best }
qed

subsection "Matrices"
    
lemma zero_not_invertible:
  "\<not> (invertible (0::real^'n^'n))"
  using invertible_times_eq_zero matrix_vector_mult_0 by blast

text \<open>Based on matrix-vector-column in
  HOL/Multivariate\_Analysis/Euclidean\_Space.thy in Isabelle 2009-1:\<close>
lemma vector_matrix_row:
  fixes x :: "('a::comm_semiring_1)^'m" and A :: "('a^'n^'m)"
  shows "x v* A = (\<Sum> i\<in>UNIV. (x$i) *s (A$i))"
  unfolding vector_matrix_mult_def
  by (simp add: vec_eq_iff mult.commute)

lemma matrix_inv:
  assumes "invertible M"
  shows "matrix_inv M ** M = mat 1"
  and "M ** matrix_inv M = mat 1"
  using \<open>invertible M\<close> and someI_ex [of "\<lambda> N. M ** N = mat 1 \<and> N ** M = mat 1"]
  unfolding invertible_def and matrix_inv_def
  by simp_all

lemma matrix_inv_invertible:
  assumes "invertible M"
  shows "invertible (matrix_inv M)"
  using \<open>invertible M\<close> and matrix_inv
  unfolding invertible_def [of "matrix_inv M"]
  by auto

lemma invertible_times_non_zero:
  fixes M :: "real^'n^'n"
  assumes "invertible M" and "v \<noteq> 0"
  shows "M *v v \<noteq> 0"
  using \<open>invertible M\<close> and \<open>v \<noteq> 0\<close> and invertible_times_eq_zero [of M v]
  by auto

lemma matrix_right_invertible_ker:
  fixes M :: "real^('m::finite)^'n"
  shows "(\<exists> M'. M ** M' = mat 1) \<longleftrightarrow> (\<forall> x. x v* M = 0 \<longrightarrow> x = 0)"
  using left_invertible_transpose matrix_left_invertible_ker by force

lemma left_invertible_iff_invertible:
  fixes M :: "real^'n^'n"
  shows "(\<exists> N. N ** M = mat 1) \<longleftrightarrow> invertible M"
  by (simp add: invertible_def matrix_left_right_inverse)

lemma right_invertible_iff_invertible:
  fixes M :: "real^'n^'n"
  shows "(\<exists> N. M ** N = mat 1) \<longleftrightarrow> invertible M"
  by (simp add: invertible_def matrix_left_right_inverse)

definition symmatrix :: "'a^'n^'n \<Rightarrow> bool" where
  "symmatrix M \<equiv> transpose M = M"

lemma symmatrix_preserve:
  fixes M N :: "('a::comm_semiring_1)^'n^'n"
  assumes "symmatrix M"
  shows "symmatrix (N ** M ** transpose N)"
proof -
  have "transpose (N ** M ** transpose N) = N ** (M ** transpose N)"
    by (metis (no_types) transpose_transpose assms matrix_transpose_mul symmatrix_def)
  then show ?thesis
    by (simp add: matrix_mul_assoc symmatrix_def)
qed

lemma non_zero_mult_invertible_non_zero:
  fixes M :: "real^'n^'n"
  assumes "v \<noteq> 0" and "invertible M"
  shows "v v* M \<noteq> 0"
  using \<open>v \<noteq> 0\<close> and \<open>invertible M\<close> and times_invertible_eq_zero
  by auto

end
