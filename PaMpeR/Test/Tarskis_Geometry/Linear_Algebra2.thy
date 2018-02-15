(*  Title:       Some extra results about linear algebra
    Author:      Tim Makarios <tjm1983 at gmail.com>, 2012
    Maintainer:  Tim Makarios <tjm1983 at gmail.com>
*)

(* After Isabelle 2012, some of these theorems
may be moved to the Isabelle repository *)

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
  is_basis :: "(real^('n::finite)) set \<Rightarrow> bool" where
  "is_basis S \<equiv> independent S \<and> span S = UNIV"

lemma card_finite:
  assumes "card S = CARD('n::finite)"
  shows "finite S"
proof -
  from `card S = CARD('n)` have "card S \<noteq> 0" by simp
  with card_eq_0_iff [of S] show "finite S" by simp
qed

lemma independent_is_basis:
  fixes B :: "(real^('n::finite)) set"
  shows "independent B \<and> card B = CARD('n) \<longleftrightarrow> is_basis B"
proof
  assume "independent B \<and> card B = CARD('n)"
  hence "independent B" and "card B = CARD('n)" by simp+
  from card_finite [of B, where 'n = 'n] and `card B = CARD('n)`
  have "finite B" by simp
  from `card B = CARD('n)`
  have "card B = dim (UNIV :: ((real^'n) set))"
    by (simp add: dim_UNIV)
  with card_eq_dim [of B UNIV] and `finite B` and `independent B`
  have "span B = UNIV" by auto
  with `independent B` show "is_basis B" unfolding is_basis_def ..
next
  assume "is_basis B"
  hence "independent B" unfolding is_basis_def ..
  moreover have "card B = CARD('n)"
  proof -
    have "B \<subseteq> UNIV" by simp
    moreover
    { from `is_basis B` have "UNIV \<subseteq> span B" and "independent B"
        unfolding is_basis_def
        by simp+ }
    ultimately have "card B = dim (UNIV::((real^'n) set))"
      using basis_card_eq_dim [of B UNIV]
      by simp
    then show "card B = CARD('n)" by (simp add: dim_UNIV)
  qed
  ultimately show "independent B \<and> card B = CARD('n)" ..
qed

lemma basis_finite:
  fixes B :: "(real^('n::finite)) set"
  assumes "is_basis B"
  shows "finite B"
proof -
  from independent_is_basis [of B] and `is_basis B` have "card B = CARD('n)"
    by simp
  with card_finite [of B, where 'n = 'n] show "finite B" by simp
qed

lemma basis_expand:
  assumes "is_basis B"
  shows "\<exists>c. v = (\<Sum>w\<in>B. (c w) *\<^sub>R w)"
proof -
  from `is_basis B` have "v \<in> span B" unfolding is_basis_def by simp
  from basis_finite [of B] and `is_basis B` have "finite B" by simp
  with span_finite [of B] and `v \<in> span B`
  show "\<exists>c. v = (\<Sum>w\<in>B. (c w) *\<^sub>R w)" by (simp add: scalar_equiv) auto
qed

lemma not_span_independent_insert:
  fixes v :: "('a::real_vector)^'n"
  assumes "independent S" and "v \<notin> span S"
  shows "independent (insert v S)"
proof -
  from span_superset and `v \<notin> span S` have "v \<notin> S" by auto
  with independent_insert [of v S] and `independent S` and `v \<notin> span S`
  show "independent (insert v S)" by simp
qed

lemma in_span_eq:
  fixes v :: "('a::real_vector)^'b"
  assumes "v \<in> span S"
  shows "span (insert v S) = span S"
proof
  { fix w
    assume "w \<in> span (insert v S)"
    with `v \<in> span S` have "w \<in> span S" by (rule span_trans) }
  thus "span (insert v S) \<subseteq> span S" ..

  have "S \<subseteq> insert v S" by (rule subset_insertI)
  thus "span S \<subseteq> span (insert v S)" by (rule span_mono)
qed

lemma dot_sum_distrib_left:
  fixes v :: "real^'n"
  shows "v \<bullet> (\<Sum> j\<in>S. w j) = (\<Sum> j\<in>S. v \<bullet> (w j))"
proof -
  have "v \<bullet> (\<Sum> j\<in>S. w j) = (\<Sum> i\<in>UNIV. v$i * (\<Sum> j\<in>S. (w j)$i))"
    unfolding inner_vec_def
    by simp
  also from sum_distrib_left [where ?A = S and ?'b = real]
  have "\<dots> = (\<Sum> i\<in>UNIV. \<Sum> j\<in>S. v$i * (w j)$i)" by simp
  also from sum.commute [of "\<lambda> i j. v$i * (w j)$i" S UNIV]
  have "\<dots> = (\<Sum> j\<in>S. \<Sum> i\<in>UNIV. v$i * (w j)$i)" by simp
  finally show "v \<bullet> (\<Sum> j\<in>S. w j) = (\<Sum> j\<in>S. v \<bullet> (w j))"
    unfolding inner_vec_def
    by simp
qed

lemma orthogonal_sum:
  fixes v :: "real^'n"
  assumes "\<forall> w\<in>S. orthogonal v w"
  shows "orthogonal v (\<Sum> w\<in>S. c w *s w)"
proof -
  from dot_sum_distrib_left [of v]
  have "v \<bullet> (\<Sum> w\<in>S. c w *s w) = (\<Sum> w\<in>S. v \<bullet> (c w *s w))" by auto
  with inner_scaleR_right [of v]
  have "v \<bullet> (\<Sum> w\<in>S. c w *s w) = (\<Sum> w\<in>S. c w * (v \<bullet> w))"
    by (simp add: scalar_equiv)
  with `\<forall> w\<in>S. orthogonal v w` show "orthogonal v (\<Sum> w\<in>S. c w *s w)"
    unfolding orthogonal_def
    by simp
qed

lemma orthogonal_self_eq_0:
  fixes v :: "('a::real_inner)^('n::finite)"
  assumes "orthogonal v v"
  shows "v = 0"
  using inner_eq_zero_iff [of v] and assms
  unfolding orthogonal_def
  by simp

lemma orthogonal_in_span_eq_0:
  fixes v :: "real^('n::finite)"
  assumes "v \<in> span S" and "\<forall> w\<in>S. orthogonal v w"
  shows "v = 0"
proof -
  from span_explicit [of S] and `v \<in> span S`
  obtain T and u where "T \<subseteq> S" and "v = (\<Sum> w\<in>T. u w *\<^sub>R w)" by auto
  from `\<forall> w\<in>S. orthogonal v w` and `T \<subseteq> S` have "\<forall> w\<in>T. orthogonal v w" by auto
  with orthogonal_sum [of T v u] and `v = (\<Sum> w\<in>T. u w *\<^sub>R w)`
  have "orthogonal v v" by (auto simp add: scalar_equiv)
  with orthogonal_self_eq_0 show "v = 0" by auto
qed

lemma orthogonal_independent:
  fixes v :: "real^('n::finite)"
  assumes "independent S" and "v \<noteq> 0" and "\<forall> w\<in>S. orthogonal v w"
  shows "independent (insert v S)"
proof -
  from orthogonal_in_span_eq_0 and `v \<noteq> 0` and `\<forall> w\<in>S. orthogonal v w`
  have "v \<notin> span S" by auto
  with not_span_independent_insert and `independent S`
  show "independent (insert v S)" by auto
qed

lemma card_ge_dim:
  fixes S :: "(real^('n::finite)) set"
  assumes "finite S"
  shows "card S \<ge> dim S"
proof -
  from span_inc have "S \<subseteq> span S" by auto
  with span_card_ge_dim [of S "span S"] and `finite S`
  have "card S \<ge> dim (span S)" by simp
  with dim_span [of S] show "card S \<ge> dim S" by simp
qed

lemma dot_scaleR_mult:
  shows "(k *\<^sub>R a) \<bullet> b = k * (a \<bullet> b)" and "a \<bullet> (k *\<^sub>R b) = k * (a \<bullet> b)"
  unfolding inner_vec_def
  by (simp_all add: algebra_simps sum_distrib_left)

lemma dependent_explicit_finite:
  fixes S :: "(('a::{real_vector,field})^'n) set"
  assumes "finite S"
  shows "dependent S \<longleftrightarrow> (\<exists> u. (\<exists> v\<in>S. u v \<noteq> 0) \<and> (\<Sum> v\<in>S. u v *\<^sub>R v) = 0)"
proof
  assume "dependent S"
  with dependent_explicit [of S]
  obtain S' and u where
    "S' \<subseteq> S" and "\<exists> v\<in>S'. u v \<noteq> 0" and "(\<Sum> v\<in>S'. u v *\<^sub>R v) = 0"
    by auto
  let ?u' = "\<lambda> v. if v \<in> S' then u v else 0"
  from `S' \<subseteq> S` and `\<exists> v\<in>S'. u v \<noteq> 0` have "\<exists> v\<in>S. ?u' v \<noteq> 0" by auto
  moreover from sum.mono_neutral_cong_right [of S S' "\<lambda> v. ?u' v *\<^sub>R v"]
    and `S' \<subseteq> S` and `(\<Sum> v\<in>S'. u v *\<^sub>R v) = 0` and `finite S`
  have "(\<Sum> v\<in>S. ?u' v *\<^sub>R v) = 0" by simp
  ultimately show "(\<exists> u. (\<exists> v\<in>S. u v \<noteq> 0) \<and> (\<Sum> v\<in>S. u v *\<^sub>R v) = 0)" by auto
next
  assume "(\<exists> u. (\<exists> v\<in>S. u v \<noteq> 0) \<and> (\<Sum> v\<in>S. u v *\<^sub>R v) = 0)"
  with dependent_explicit [of S] and `finite S`
  show "dependent S" by auto
qed

lemma dependent_explicit_2:
  fixes v w :: "('a::{field,real_vector})^'n"
  assumes "v \<noteq> w"
  shows "dependent {v, w} \<longleftrightarrow> (\<exists> i j. (i \<noteq> 0 \<or> j \<noteq> 0) \<and> i *\<^sub>R v + j *\<^sub>R w = 0)"
proof
  let ?S = "{v, w}"
  have "finite ?S" by simp

  { assume "dependent ?S"
    with dependent_explicit_finite [of ?S] and `finite ?S` and `v \<noteq> w`
    show "\<exists> i j. (i \<noteq> 0 \<or> j \<noteq> 0) \<and> i *\<^sub>R v + j *\<^sub>R w = 0" by auto }

  { assume "\<exists> i j. (i \<noteq> 0 \<or> j \<noteq> 0) \<and> i *\<^sub>R v + j *\<^sub>R w = 0"
    then obtain i and j where "i \<noteq> 0 \<or> j \<noteq> 0" and "i *\<^sub>R v + j *\<^sub>R w = 0" by auto
    let ?u = "\<lambda> x. if x = v then i else j"
    from `i \<noteq> 0 \<or> j \<noteq> 0` and `v \<noteq> w` have "\<exists> x\<in>?S. ?u x \<noteq> 0" by simp
    from `i *\<^sub>R v + j *\<^sub>R w = 0` and `v \<noteq> w`
    have "(\<Sum> x\<in>?S. ?u x *\<^sub>R x) = 0" by simp
    with dependent_explicit_finite [of ?S]
      and `finite ?S` and `\<exists> x\<in>?S. ?u x \<noteq> 0`
    show "dependent ?S" by best }
qed

subsection "Matrices"

lemma zero_times:
  "0 ** A = (0::real^('n::finite)^'n)"
  unfolding matrix_matrix_mult_def and zero_vec_def
  by simp

lemma zero_not_invertible:
  "\<not> (invertible (0::real^('n::finite)^'n))"
proof -
  let ?\<Lambda> = "0::real^'n^'n"
  let ?I = "mat 1::real^'n^'n"
  let ?k = "undefined :: 'n"
  have "?I $ ?k $ ?k \<noteq> ?\<Lambda> $ ?k $ ?k"
    unfolding mat_def
    by simp
  hence "?\<Lambda> \<noteq> ?I" by auto
  from zero_times have "\<forall> A. ?\<Lambda> ** A = ?\<Lambda>" by auto
  with `?\<Lambda> \<noteq> ?I` show "\<not> (invertible ?\<Lambda>)"
    unfolding invertible_def
    by simp
qed

text {* Based on matrix-vector-column in
  HOL/Multivariate\_Analysis/Euclidean\_Space.thy in Isabelle 2009-1: *}
lemma vector_matrix_row:
  fixes x :: "('a::comm_semiring_1)^'m" and A :: "('a^'n^'m)"
  shows "x v* A = (\<Sum> i\<in>UNIV. (x$i) *s (A$i))"
  unfolding vector_matrix_mult_def
  by (simp add: vec_eq_iff mult.commute)

lemma invertible_mult:
  fixes A B :: "real^('n::finite)^'n"
  assumes "invertible A" and "invertible B"
  shows "invertible (A ** B)"
proof -
  from `invertible A` and `invertible B`
  obtain A' and B' where "A ** A' = mat 1" and "A' ** A = mat 1"
    and "B ** B' = mat 1" and "B' ** B = mat 1"
    unfolding invertible_def
    by auto
  have "(A ** B) ** (B' ** A') = A ** (B ** B') ** A'"
    by (simp add: matrix_mul_assoc)
  with `A ** A' = mat 1` and `B ** B' = mat 1`
  have "(A ** B) ** (B' ** A') = mat 1" by (auto simp add: matrix_mul_rid)
  with matrix_left_right_inverse have "(B' ** A') ** (A ** B) = mat 1" by auto
  with `(A ** B) ** (B' ** A') = mat 1`
  show "invertible (A ** B)"
    unfolding invertible_def
    by auto
qed

lemma scalar_matrix_assoc:
  fixes A :: "real^'m^'n"
  shows "k *\<^sub>R (A ** B) = (k *\<^sub>R A) ** B"
proof -
  have "\<forall> i j. (k *\<^sub>R (A ** B))$i$j = ((k *\<^sub>R A) ** B)$i$j"
  proof standard+
    fix i j
    have "(k *\<^sub>R (A ** B))$i$j = k * (\<Sum> l\<in>UNIV. A$i$l * B$l$j)"
      unfolding matrix_matrix_mult_def
      by simp
    also from scaleR_right.sum [of k "\<lambda> l. A$i$l * B$l$j" UNIV]
    have "\<dots> = (\<Sum> l\<in>UNIV. k * A$i$l * B$l$j)" by (simp add: algebra_simps)
    finally show "(k *\<^sub>R (A ** B))$i$j = ((k *\<^sub>R A) ** B)$i$j"
      unfolding matrix_matrix_mult_def
      by simp
  qed
  thus "k *\<^sub>R (A ** B) = (k *\<^sub>R A) ** B" by (simp add: vec_eq_iff)
qed

lemma transpose_scalar: "transpose (k *\<^sub>R A) = k *\<^sub>R transpose A"
  unfolding transpose_def
  by (simp add: vec_eq_iff)

lemma transpose_iff [iff]: "transpose A = transpose B \<longleftrightarrow> A = B"
proof
  assume "transpose A = transpose B"
  with transpose_transpose [of A] have "A = transpose (transpose B)" by simp
  with transpose_transpose [of B] show "A = B" by simp
next
  assume "A = B"
  thus "transpose A = transpose B" by simp
qed

lemma matrix_scalar_ac:
  fixes A :: "real^'m^'n"
  shows "A ** (k *\<^sub>R B) = k *\<^sub>R A ** B"
proof -
  from matrix_transpose_mul [of A "k *\<^sub>R B"] and transpose_scalar [of k B]
  have "transpose (A ** (k *\<^sub>R B)) = k *\<^sub>R transpose B ** transpose A"
    by simp
  also from matrix_transpose_mul [of A B] and transpose_scalar [of k "A ** B"]
  have "\<dots> = transpose (k *\<^sub>R A ** B)" by (simp add: scalar_matrix_assoc)
  finally show "A ** (k *\<^sub>R B) = k *\<^sub>R A ** B" by simp
qed

lemma scalar_invertible:
  fixes A :: "real^'m^'n"
  assumes "k \<noteq> 0" and "invertible A"
  shows "invertible (k *\<^sub>R A)"
proof -
  from `invertible A`
  obtain A' where "A ** A' = mat 1" and "A' ** A = mat 1"
    unfolding invertible_def
    by auto
  with `k \<noteq> 0`
  have "(k *\<^sub>R A) ** ((1/k) *\<^sub>R A') = mat 1"
    and "((1/k) *\<^sub>R A') ** (k *\<^sub>R A) = mat 1"
    by (simp_all add: matrix_scalar_ac)
  thus "invertible (k *\<^sub>R A)"
    unfolding invertible_def
    by auto
qed

lemma matrix_inv:
  assumes "invertible M"
  shows "matrix_inv M ** M = mat 1"
  and "M ** matrix_inv M = mat 1"
  using `invertible M` and someI_ex [of "\<lambda> N. M ** N = mat 1 \<and> N ** M = mat 1"]
  unfolding invertible_def and matrix_inv_def
  by simp_all

lemma matrix_inv_invertible:
  assumes "invertible M"
  shows "invertible (matrix_inv M)"
  using `invertible M` and matrix_inv
  unfolding invertible_def [of "matrix_inv M"]
  by auto

lemma vector_matrix_mul_rid:
  fixes v :: "('a::semiring_1)^('n::finite)"
  shows "v v* mat 1 = v"
proof -
  have "v v* mat 1 = transpose (mat 1) *v v" by simp
  thus "v v* mat 1 = v" by (simp only: transpose_mat matrix_vector_mul_lid)
qed

lemma vector_matrix_mul_assoc:
  fixes v :: "('a::comm_semiring_1)^'n"
  shows "(v v* M) v* N = v v* (M ** N)"
proof -
  from matrix_vector_mul_assoc
  have "transpose N *v (transpose M *v v) = (transpose N ** transpose M) *v v" by fast
  thus "(v v* M) v* N = v v* (M ** N)"
    by (simp add: matrix_transpose_mul [symmetric])
qed

lemma matrix_scalar_vector_ac:
  fixes A :: "real^('m::finite)^('n::finite)"
  shows "A *v (k *\<^sub>R v) = k *\<^sub>R A *v v"
proof -
  have "A *v (k *\<^sub>R v) = k *\<^sub>R (v v* transpose A)"
    by (subst scalar_vector_matrix_assoc [symmetric]) simp
  also have "\<dots> = v v* k *\<^sub>R transpose A"
    by (subst vector_scalar_matrix_ac) simp
  also have "\<dots> = v v* transpose (k *\<^sub>R A)" by (subst transpose_scalar) simp
  also have "\<dots> = k *\<^sub>R A *v v" by simp
  finally show "A *v (k *\<^sub>R v) = k *\<^sub>R A *v v" .
qed

lemma scalar_matrix_vector_assoc:
  fixes A :: "real^('m::finite)^('n::finite)"
  shows "k *\<^sub>R (A *v v) = k *\<^sub>R A *v v"
proof -
  have "k *\<^sub>R (A *v v) = k *\<^sub>R (v v* transpose A)" by simp
  also have "\<dots> = v v* k *\<^sub>R transpose A"
    by (rule vector_scalar_matrix_ac [symmetric])
  also have "\<dots> = v v* transpose (k *\<^sub>R A)" apply (subst transpose_scalar) ..
  finally show "k *\<^sub>R (A *v v) = k *\<^sub>R A *v v" by simp
qed

lemma invertible_times_non_zero:
  fixes M :: "real^'n^('n::finite)"
  assumes "invertible M" and "v \<noteq> 0"
  shows "M *v v \<noteq> 0"
  using `invertible M` and `v \<noteq> 0` and invertible_times_eq_zero [of M v]
  by auto

lemma matrix_right_invertible_ker:
  fixes M :: "real^('m::finite)^('n::finite)"
  shows "(\<exists> M'. M ** M' = mat 1) \<longleftrightarrow> (\<forall> x. x v* M = 0 \<longrightarrow> x = 0)"
proof
  assume "\<exists> M'. M ** M' = mat 1"
  then obtain M' where "M ** M' = mat 1" ..
  have "transpose (M ** M') = transpose (mat 1)" apply (subst `M ** M' = mat 1`) ..
  hence "transpose M' ** transpose M = mat 1"
    by (simp add: matrix_transpose_mul transpose_mat)
  hence "\<exists> M''. M'' ** transpose M = mat 1" ..
  with matrix_left_invertible_ker [of "transpose M"]
  have "\<forall> x. transpose M *v x = 0 \<longrightarrow> x = 0" by simp
  thus "\<forall> x. x v* M = 0 \<longrightarrow> x = 0" by simp
next
  assume "\<forall> x. x v* M = 0 \<longrightarrow> x = 0"
  hence "\<forall> x. transpose M *v x = 0 \<longrightarrow> x = 0" by simp
  with matrix_left_invertible_ker [of "transpose M"]
  obtain M'' where "M'' ** transpose M = mat 1" by auto
  hence "transpose (M'' ** transpose M) = transpose (mat 1)" by simp
  hence "M ** transpose M'' = mat 1"
    by (simp add: matrix_transpose_mul transpose_transpose transpose_mat)
  thus "\<exists> M'. M ** M' = mat 1" ..
qed

lemma left_invertible_iff_invertible:
  fixes M :: "real^('n::finite)^'n"
  shows "(\<exists> N. N ** M = mat 1) \<longleftrightarrow> invertible M"
  using matrix_left_right_inverse
  unfolding invertible_def
  by auto

lemma right_invertible_iff_invertible:
  fixes M :: "real^('n::finite)^'n"
  shows "(\<exists> N. M ** N = mat 1) \<longleftrightarrow> invertible M"
  using left_invertible_iff_invertible
  by (subst matrix_left_right_inverse) auto

definition symmatrix :: "'a^'n^'n \<Rightarrow> bool" where
  "symmatrix M \<equiv> transpose M = M"

lemma symmatrix_preserve:
  fixes M N :: "('a::comm_semiring_1)^'n^'n"
  assumes "symmatrix M"
  shows "symmatrix (N ** M ** transpose N)"
proof -
  have "transpose (N ** M ** transpose N) = N ** transpose M ** transpose N"
    by (simp add: matrix_transpose_mul transpose_transpose matrix_mul_assoc)
  with `symmatrix M`
  show "symmatrix (N ** M ** transpose N)"
    unfolding symmatrix_def
    by simp
qed

lemma matrix_vector_right_distrib:
  fixes v w :: "real^('n::finite)" and M :: "real^'n^('m::finite)"
  shows "M *v (v + w) = M *v v + M *v w"
proof -
  have "M *v (v + w) = (v + w) v* transpose M" by simp
  also have "\<dots> = v v* transpose M + w v* transpose M"
    by (rule vector_matrix_left_distrib [of v w "transpose M"])
  finally show "M *v (v + w) = M *v v + M *v w" by simp
qed

lemma non_zero_mult_invertible_non_zero:
  fixes M :: "real^'n^'n"
  assumes "v \<noteq> 0" and "invertible M"
  shows "v v* M \<noteq> 0"
  using `v \<noteq> 0` and `invertible M` and times_invertible_eq_zero
  by auto

end
