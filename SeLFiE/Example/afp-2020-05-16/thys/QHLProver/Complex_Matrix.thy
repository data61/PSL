section \<open>Complex matrices\<close>

theory Complex_Matrix
  imports 
    "Jordan_Normal_Form.Matrix" 
    "Jordan_Normal_Form.Conjugate" 
    "Jordan_Normal_Form.Jordan_Normal_Form_Existence"
begin

subsection \<open>Trace of a matrix\<close>

definition trace :: "'a::ring mat \<Rightarrow> 'a" where
  "trace A = (\<Sum> i \<in> {0 ..< dim_row A}. A $$ (i,i))"

lemma trace_zero [simp]:
  "trace (0\<^sub>m n n) = 0"
  by (simp add: trace_def)

lemma trace_id [simp]:
  "trace (1\<^sub>m n) = n"
  by (simp add: trace_def)

lemma trace_comm:
  fixes A B :: "'a::comm_ring mat"
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
  shows "trace (A * B) = trace (B * A)"
proof (simp add: trace_def)
  have "(\<Sum>i = 0..<n. (A * B) $$ (i, i)) = (\<Sum>i = 0..<n. \<Sum>j = 0..<n. A $$ (i,j) * B $$ (j,i))"
    apply (rule sum.cong) using assms by (auto simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>j = 0..<n. \<Sum>i = 0..<n. A $$ (i,j) * B $$ (j,i))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j = 0..<n. col A j \<bullet> row B j)"
    by (metis (no_types, lifting) A B atLeastLessThan_iff carrier_matD index_col index_row scalar_prod_def sum.cong)
  also have "\<dots> = (\<Sum>j = 0..<n. row B j \<bullet> col A j)"
    apply (rule sum.cong) apply auto
    apply (subst comm_scalar_prod[where n=n]) apply auto
    using assms by auto
  also have "\<dots> = (\<Sum>j = 0..<n. (B * A) $$ (j, j))"
    apply (rule sum.cong) using assms by auto
  finally show "(\<Sum>i = 0..<dim_row A. (A * B) $$ (i, i)) = (\<Sum>i = 0..<dim_row B. (B * A) $$ (i, i))"
    using A B by auto
qed

lemma trace_add_linear:
  fixes A B :: "'a::comm_ring mat"
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
  shows "trace (A + B) = trace A + trace B" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>i=0..<n. A$$(i, i) + B$$(i, i))" unfolding trace_def using A B by auto
  also have "\<dots> = (\<Sum>i=0..<n. A$$(i, i)) + (\<Sum>i=0..<n. B$$(i, i))" by (auto simp add: sum.distrib)
  finally have l: "?lhs = (\<Sum>i=0..<n. A$$(i, i)) + (\<Sum>i=0..<n. B$$(i, i))".
  have r: "?rhs = (\<Sum>i=0..<n. A$$(i, i)) + (\<Sum>i=0..<n. B$$(i, i))" unfolding trace_def using A B by auto
  from l r show ?thesis by auto
qed

lemma trace_minus_linear:
  fixes A B :: "'a::comm_ring mat"
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
  shows "trace (A - B) = trace A - trace B" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>i=0..<n. A$$(i, i) - B$$(i, i))" unfolding trace_def using A B by auto
  also have "\<dots> = (\<Sum>i=0..<n. A$$(i, i)) - (\<Sum>i=0..<n. B$$(i, i))" by (auto simp add: sum_subtractf)
  finally have l: "?lhs = (\<Sum>i=0..<n. A$$(i, i)) - (\<Sum>i=0..<n. B$$(i, i))".
  have r: "?rhs = (\<Sum>i=0..<n. A$$(i, i)) - (\<Sum>i=0..<n. B$$(i, i))" unfolding trace_def using A B by auto
  from l r show ?thesis by auto
qed

lemma trace_smult: 
  assumes "A \<in> carrier_mat n n"
  shows "trace (c \<cdot>\<^sub>m A) = c * trace A"
proof -
  have "trace (c \<cdot>\<^sub>m A) = (\<Sum>i = 0..<dim_row A. c * A $$ (i, i))" unfolding trace_def using assms by auto
  also have "\<dots> = c * (\<Sum>i = 0..<dim_row A. A $$ (i, i))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = c * trace A" unfolding trace_def by auto
  ultimately show ?thesis by auto
qed

subsection \<open>Conjugate of a vector\<close>

lemma conjugate_scalar_prod:
  fixes v w :: "'a::conjugatable_ring vec"
  assumes "dim_vec v = dim_vec w"
  shows "conjugate (v \<bullet> w) = conjugate v \<bullet> conjugate w"
  using assms by (simp add: scalar_prod_def sum_conjugate conjugate_dist_mul)

subsection \<open>Inner product\<close>

abbreviation inner_prod :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a :: conjugatable_ring"
  where "inner_prod v w \<equiv> w \<bullet>c v"

lemma conjugate_scalar_prod_Im [simp]:
  "Im (v \<bullet>c v) = 0"
  by (simp add: scalar_prod_def conjugate_vec_def sum.neutral)

lemma conjugate_scalar_prod_Re [simp]:
  "Re (v \<bullet>c v) \<ge> 0"
  by (simp add: scalar_prod_def conjugate_vec_def sum_nonneg)

lemma self_cscalar_prod_geq_0:
  fixes v ::  "'a::conjugatable_ordered_field vec"
  shows "v \<bullet>c v \<ge> 0"
  by (auto simp add: scalar_prod_def, rule sum_nonneg, rule conjugate_square_positive)

lemma inner_prod_distrib_left:
  fixes u v w :: "('a::conjugatable_field) vec"
  assumes dimu: "u \<in> carrier_vec n" and dimv:"v \<in> carrier_vec n" and dimw: "w \<in> carrier_vec n" 
  shows "inner_prod (v + w) u = inner_prod v u + inner_prod w u" (is "?lhs = ?rhs")
proof -
  have dimcv: "conjugate v \<in> carrier_vec n" and dimcw: "conjugate w \<in> carrier_vec n" using assms by auto
  have dimvw: "conjugate (v + w) \<in> carrier_vec n" using assms by auto
  have "u \<bullet> (conjugate (v + w)) = u \<bullet> conjugate v + u \<bullet> conjugate w"
    using dimv dimw dimu dimcv dimcw 
    by (metis conjugate_add_vec scalar_prod_add_distrib)
  then show ?thesis by auto
qed

lemma inner_prod_distrib_right:
  fixes u v w :: "('a::conjugatable_field) vec"
  assumes dimu: "u \<in> carrier_vec n" and dimv:"v \<in> carrier_vec n" and dimw: "w \<in> carrier_vec n" 
  shows "inner_prod u (v + w) = inner_prod u v + inner_prod u w" (is "?lhs = ?rhs")
proof -
  have dimvw: "v + w \<in> carrier_vec n" using assms by auto
  have dimcu: "conjugate u \<in> carrier_vec n" using assms by auto
  have "(v + w) \<bullet> (conjugate u) = v \<bullet> conjugate u + w \<bullet> conjugate u"
    apply (simp add: comm_scalar_prod[OF dimvw dimcu])
    apply (simp add: scalar_prod_add_distrib[OF dimcu dimv dimw])
    apply (insert dimv dimw dimcu, simp add: comm_scalar_prod[of _ n])
    done
  then show ?thesis by auto
qed                

lemma inner_prod_minus_distrib_right:
  fixes u v w :: "('a::conjugatable_field) vec"
  assumes dimu: "u \<in> carrier_vec n" and dimv:"v \<in> carrier_vec n" and dimw: "w \<in> carrier_vec n" 
  shows "inner_prod u (v - w) = inner_prod u v - inner_prod u w" (is "?lhs = ?rhs")
proof -
  have dimvw: "v - w \<in> carrier_vec n" using assms by auto
  have dimcu: "conjugate u \<in> carrier_vec n" using assms by auto
  have "(v - w) \<bullet> (conjugate u) = v \<bullet> conjugate u - w \<bullet> conjugate u"
    apply (simp add: comm_scalar_prod[OF dimvw dimcu])
    apply (simp add: scalar_prod_minus_distrib[OF dimcu dimv dimw])
    apply (insert dimv dimw dimcu, simp add: comm_scalar_prod[of _ n])
    done
  then show ?thesis by auto
qed                

lemma inner_prod_smult_right:
  fixes u v :: "complex vec"
  assumes dimu: "u \<in> carrier_vec n" and dimv:"v \<in> carrier_vec n" 
  shows "inner_prod (a \<cdot>\<^sub>v u) v = conjugate a * inner_prod u v" (is "?lhs = ?rhs")
  using assms apply (simp add: scalar_prod_def conjugate_dist_mul) 
  apply (subst sum_distrib_left) by (rule sum.cong, auto)

lemma inner_prod_smult_left:
  fixes u v :: "complex vec"
  assumes dimu: "u \<in> carrier_vec n" and dimv: "v \<in> carrier_vec n" 
  shows "inner_prod u (a \<cdot>\<^sub>v v) = a * inner_prod u v" (is "?lhs = ?rhs")
  using assms apply (simp add: scalar_prod_def) 
  apply (subst sum_distrib_left) by (rule sum.cong, auto)

lemma inner_prod_smult_left_right:
  fixes u v :: "complex vec"
  assumes dimu: "u \<in> carrier_vec n" and dimv: "v \<in> carrier_vec n" 
  shows "inner_prod (a \<cdot>\<^sub>v u) (b \<cdot>\<^sub>v v) = conjugate a * b  * inner_prod u v" (is "?lhs = ?rhs")
  using assms apply (simp add: scalar_prod_def) 
  apply (subst sum_distrib_left) by (rule sum.cong, auto)

lemma inner_prod_swap:
  fixes x y :: "complex vec"
  assumes "y \<in> carrier_vec n" and "x \<in> carrier_vec n" 
  shows "inner_prod y x = conjugate (inner_prod x y)"
  apply (simp add: scalar_prod_def)
  apply (rule sum.cong) using assms by auto

text \<open>Cauchy-Schwarz theorem for complex vectors. This is analogous to aux\_Cauchy
  and Cauchy\_Schwarz\_ineq in Generalizations2.thy in QR\_Decomposition. Consider
  merging and moving to Isabelle library.\<close>
lemma aux_Cauchy:
  fixes x y :: "complex vec"
  assumes "x \<in> carrier_vec n" and "y \<in> carrier_vec n"
  shows "0 \<le> inner_prod x x + a * (inner_prod x y) + (cnj a) * ((cnj (inner_prod x y)) + a * (inner_prod y y))"
proof -
  have "(inner_prod (x+ a \<cdot>\<^sub>v y) (x+a \<cdot>\<^sub>v y)) = (inner_prod (x+a \<cdot>\<^sub>v y) x) + (inner_prod (x+a \<cdot>\<^sub>v y) (a \<cdot>\<^sub>v y))" 
    apply (subst inner_prod_distrib_right) using assms by auto
  also have "\<dots> = inner_prod x x + (a) * (inner_prod x y) + cnj a * ((cnj (inner_prod x y)) + (a) * (inner_prod y y))"
    apply (subst (1 2) inner_prod_distrib_left[of _ n]) apply (auto simp add: assms)
    apply (subst (1 2) inner_prod_smult_right[of _ n]) apply (auto simp add: assms)
    apply (subst inner_prod_smult_left[of _ n]) apply (auto simp add: assms)
    apply (subst inner_prod_swap[of y n x]) apply (auto simp add: assms)
    unfolding distrib_left
    by auto
  finally show ?thesis by (metis self_cscalar_prod_geq_0)
qed

lemma Cauchy_Schwarz_complex_vec:
  fixes x y :: "complex vec"
  assumes "x \<in> carrier_vec n" and "y \<in> carrier_vec n"
  shows "inner_prod x y * inner_prod y x \<le> inner_prod x x * inner_prod y y"
proof -
  define cnj_a where "cnj_a = - (inner_prod x y)/ cnj (inner_prod y y)"
  define a where "a = cnj (cnj_a)"
  have cnj_rw: "(cnj a) = cnj_a" 
    unfolding a_def by (simp)
  have rw_0: "cnj (inner_prod x y) + a * (inner_prod y y) = 0"
    unfolding a_def cnj_a_def using assms(1) assms(2) conjugate_square_eq_0_vec by fastforce
  have "0 \<le>  (inner_prod x x + a * (inner_prod x y) + (cnj a) * ((cnj (inner_prod x y)) + a * (inner_prod y y)))"
    using aux_Cauchy assms by auto
  also have "\<dots> =  (inner_prod x x + a * (inner_prod x y))" unfolding rw_0 by auto
  also have "\<dots> =  (inner_prod x x - (inner_prod x y) * cnj (inner_prod x y) / (inner_prod y y))" 
  unfolding a_def cnj_a_def by simp
  finally have " 0 \<le>  (inner_prod x x - (inner_prod x y) * cnj (inner_prod x y) / (inner_prod y y)) " .
  hence "0 \<le> (inner_prod x x - (inner_prod x y) * cnj (inner_prod x y) / (inner_prod y y)) * (inner_prod y y)" by auto
  also have "\<dots> = ((inner_prod x x)*(inner_prod y y) - (inner_prod x y) * cnj (inner_prod x y))"
    by (smt add.inverse_neutral add_diff_cancel diff_0 diff_divide_eq_iff divide_cancel_right mult_eq_0_iff nonzero_mult_div_cancel_right rw_0)
  finally have "(inner_prod x y) * cnj (inner_prod x y) \<le> (inner_prod x x)*(inner_prod y y)" by auto
  then show ?thesis 
    apply (subst inner_prod_swap[of y n x]) by (auto simp add: assms)
qed

subsection \<open>Hermitian adjoint of a matrix\<close>

abbreviation adjoint where "adjoint \<equiv> mat_adjoint"

lemma adjoint_dim_row [simp]:
  "dim_row (adjoint A) = dim_col A" by (simp add: mat_adjoint_def)

lemma adjoint_dim_col [simp]:
  "dim_col (adjoint A) = dim_row A" by (simp add: mat_adjoint_def)

lemma adjoint_dim:
  "A \<in> carrier_mat n n \<Longrightarrow> adjoint A \<in> carrier_mat n n"
  using adjoint_dim_col adjoint_dim_row by blast

lemma adjoint_def:
  "adjoint A = mat (dim_col A) (dim_row A) (\<lambda>(i,j). conjugate (A $$ (j,i)))"
  unfolding mat_adjoint_def mat_of_rows_def by auto

lemma adjoint_eval:
  assumes "i < dim_col A" "j < dim_row A"
  shows "(adjoint A) $$ (i,j) = conjugate (A $$ (j,i))"
  using assms by (simp add: adjoint_def)

lemma adjoint_row:
  assumes "i < dim_col A"
  shows "row (adjoint A) i = conjugate (col A i)"
  apply (rule eq_vecI)
  using assms by (auto simp add: adjoint_eval)

lemma adjoint_col:
  assumes "i < dim_row A"
  shows "col (adjoint A) i = conjugate (row A i)"
  apply (rule eq_vecI)
  using assms by (auto simp add: adjoint_eval)

text \<open>The identity <v, A w> = <A* v, w>\<close>
lemma adjoint_def_alter:
  fixes v w :: "'a::conjugatable_field vec"
    and A :: "'a::conjugatable_field mat"
  assumes dims: "v \<in> carrier_vec n" "w \<in> carrier_vec m" "A \<in> carrier_mat n m"
  shows "inner_prod v (A *\<^sub>v w) = inner_prod (adjoint A *\<^sub>v v) w" (is "?lhs = ?rhs")
proof -
  from dims have "?lhs = (\<Sum>i=0..<dim_vec v. (\<Sum>j=0..<dim_vec w.
                conjugate (v$i) * A$$(i, j) * w$j))"
    apply (simp add: scalar_prod_def sum_distrib_right )
    apply (rule sum.cong, simp)
    apply (rule sum.cong, auto)
    done
  moreover from assms have "?rhs = (\<Sum>i=0..<dim_vec v. (\<Sum>j=0..<dim_vec w.
                conjugate (v$i) * A$$(i, j) * w$j))"
    apply (simp add: scalar_prod_def  adjoint_eval 
                     sum_conjugate conjugate_dist_mul sum_distrib_left)
    apply (subst sum.swap[where ?A = "{0..<n}"])
    apply (rule sum.cong, simp)
    apply (rule sum.cong, auto)
    done
  ultimately show ?thesis by simp
qed

lemma adjoint_one:
  shows "adjoint (1\<^sub>m n) = (1\<^sub>m n::complex mat)"
  apply (rule eq_matI) 
  by (auto simp add: adjoint_eval)

lemma adjoint_scale:
  fixes A :: "'a::conjugatable_field mat"
  shows "adjoint (a \<cdot>\<^sub>m A) = (conjugate a) \<cdot>\<^sub>m adjoint A"
  apply (rule eq_matI) using conjugatable_ring_class.conjugate_dist_mul
  by (auto simp add: adjoint_eval)

lemma adjoint_add:
  fixes A B :: "'a::conjugatable_field mat"
  assumes "A \<in> carrier_mat n m" "B \<in> carrier_mat n m"
  shows "adjoint (A + B) = adjoint A + adjoint B"
  apply (rule eq_matI)
  using assms conjugatable_ring_class.conjugate_dist_add 
  by( auto simp add: adjoint_eval)

lemma adjoint_minus:
  fixes A B :: "'a::conjugatable_field mat"
  assumes "A \<in> carrier_mat n m" "B \<in> carrier_mat n m"
  shows "adjoint (A - B) = adjoint A - adjoint B"
  apply (rule eq_matI)
  using assms apply(auto simp add: adjoint_eval)
  by (metis add_uminus_conv_diff conjugate_dist_add conjugate_neg)

lemma adjoint_mult:
  fixes A B :: "'a::conjugatable_field mat"
  assumes "A \<in> carrier_mat n m" "B \<in> carrier_mat m l"
  shows "adjoint (A * B) = adjoint B * adjoint A"
proof (rule eq_matI, auto simp add: adjoint_eval adjoint_row adjoint_col)
  fix i j
  assume "i < dim_col B" "j < dim_row A"
  show "conjugate (row A j \<bullet> col B i) = conjugate (col B i) \<bullet> conjugate (row A j)"
    using assms apply (simp add: conjugate_scalar_prod)
    apply (subst comm_scalar_prod[where n="dim_row B"])
    by (auto simp add: carrier_vecI)
qed

lemma adjoint_adjoint:
  fixes A :: "'a::conjugatable_field mat"
  shows "adjoint (adjoint A) = A"
  by (rule eq_matI, auto simp add: adjoint_eval)

lemma trace_adjoint_positive:
  fixes A :: "complex mat"
  shows "trace (A * adjoint A) \<ge> 0"
  apply (auto simp add: trace_def adjoint_col)
  apply (rule sum_nonneg) by auto

subsection \<open>Algebraic manipulations on matrices\<close>

lemma right_add_zero_mat[simp]:
  "(A :: 'a :: monoid_add mat) \<in> carrier_mat nr nc \<Longrightarrow> A + 0\<^sub>m nr nc = A"
  by (intro eq_matI, auto)

lemma add_carrier_mat':
  "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow> A + B \<in> carrier_mat nr nc"
  by simp

lemma minus_carrier_mat':
  "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow> A - B \<in> carrier_mat nr nc"
  by auto

lemma swap_plus_mat:
  fixes A B C :: "'a::semiring_1 mat"
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
  shows "A + B + C = A + C + B"
  by (metis assms assoc_add_mat comm_add_mat)

lemma uminus_mat:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  shows "-A = (-1) \<cdot>\<^sub>m A"
  by auto

ML_file "mat_alg.ML"
method_setup mat_assoc = {* mat_assoc_method *}
  "Normalization of expressions on matrices"

lemma mat_assoc_test:
  fixes A B C D :: "complex mat"
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n" "D \<in> carrier_mat n n"
  shows
    "(A * B) * (C * D) = A * B * C * D"
    "adjoint (A * adjoint B) * C = B * (adjoint A * C)"
    "A * 1\<^sub>m n * 1\<^sub>m n * B * 1\<^sub>m n = A * B"
    "(A - B) + (B - C) = A + (-B) + B + (-C)"
    "A + (B - C) = A + B - C"
    "A - (B + C + D) = A - B - C - D"
    "(A + B) * (B + C) = A * B + B * B + A * C + B * C"
    "A - B = A + (-1) \<cdot>\<^sub>m B"
    "A * (B - C) * D = A * B * D - A * C * D"
    "trace (A * B * C) = trace (B * C * A)"
    "trace (A * B * C * D) = trace (C * D * A * B)"
    "trace (A + B * C) = trace A + trace (C * B)"
    "A + B = B + A"
    "A + B + C = C + B + A"
    "A + B + (C + D) = A + C + (B + D)"
  using assms by (mat_assoc n)+

subsection \<open>Hermitian matrices\<close>

text \<open>A Hermitian matrix is a matrix that is equal to its Hermitian adjoint.\<close>
definition hermitian :: "'a::conjugatable_field mat \<Rightarrow> bool" where
  "hermitian A \<longleftrightarrow> (adjoint A = A)"

lemma hermitian_one:
  shows "hermitian ((1\<^sub>m n)::('a::conjugatable_field mat))"
  unfolding hermitian_def 
proof-
  have "conjugate (1::'a) = 1"   
    apply (subst mult_1_right[symmetric, of "conjugate 1"])
    apply (subst conjugate_id[symmetric, of "conjugate 1 * 1"])
    apply (subst conjugate_dist_mul)
    apply auto
    done
  then show "adjoint ((1\<^sub>m n)::('a::conjugatable_field mat)) = (1\<^sub>m n)" 
    by (auto simp add: adjoint_eval) 
qed

subsection \<open>Inverse matrices\<close>

lemma inverts_mat_symm:
  fixes A B :: "'a::field mat"
  assumes dim: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
    and AB: "inverts_mat A B"
  shows "inverts_mat B A"
proof -
  have "A * B = 1\<^sub>m n" using dim AB unfolding inverts_mat_def by auto
  with dim have "B * A = 1\<^sub>m n"  by (rule mat_mult_left_right_inverse)
  then show "inverts_mat B A" using dim inverts_mat_def by auto
qed

lemma inverts_mat_unique:
  fixes A B C :: "'a::field mat"
  assumes dim: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n" 
    and AB: "inverts_mat A B" and AC: "inverts_mat A C"
  shows "B = C"
proof -
  have AB1: "A * B = 1\<^sub>m n" using AB dim unfolding inverts_mat_def by auto
  have "A * C = 1\<^sub>m n" using AC dim unfolding inverts_mat_def by auto
  then have CA1: "C * A = 1\<^sub>m n" using mat_mult_left_right_inverse[of A n C] dim by auto
  then have "C = C * 1\<^sub>m n" using dim by auto
  also have "\<dots> = C * (A * B)" using AB1 by auto
  also have "\<dots> = (C * A) * B" using dim by auto
  also have "\<dots> = 1\<^sub>m n * B" using CA1 by auto
  also have "\<dots> = B" using dim by auto
  finally show "B = C" ..
qed

subsection \<open>Unitary matrices\<close>

text \<open>A unitary matrix is a matrix whose Hermitian adjoint is also its inverse.\<close>
definition unitary :: "'a::conjugatable_field mat \<Rightarrow> bool" where
  "unitary A \<longleftrightarrow> A \<in> carrier_mat (dim_row A) (dim_row A) \<and> inverts_mat A (adjoint A)"

lemma unitaryD2:
  assumes "A \<in> carrier_mat n n"
  shows "unitary A \<Longrightarrow> inverts_mat (adjoint A) A"
  using assms adjoint_dim inverts_mat_symm unitary_def by blast

lemma unitary_simps [simp]:
  "A \<in> carrier_mat n n \<Longrightarrow> unitary A \<Longrightarrow> adjoint A * A = 1\<^sub>m n"
  "A \<in> carrier_mat n n \<Longrightarrow> unitary A \<Longrightarrow> A * adjoint A = 1\<^sub>m n"
  apply (metis adjoint_dim_row carrier_matD(2) inverts_mat_def unitaryD2)
  by (simp add: inverts_mat_def unitary_def)

lemma unitary_adjoint [simp]:
  assumes "A \<in> carrier_mat n n" "unitary A"
  shows "unitary (adjoint A)" 
  unfolding unitary_def
  using  adjoint_dim[OF assms(1)] assms by (auto simp add: unitaryD2[OF assms] adjoint_adjoint)

lemma unitary_one:
  shows "unitary ((1\<^sub>m n)::('a::conjugatable_field mat))"
  unfolding unitary_def 
proof -
  define I where I_def[simp]: "I \<equiv> ((1\<^sub>m n)::('a::conjugatable_field mat))"
  have dim: "I \<in> carrier_mat n n" by auto
  have "hermitian I" using hermitian_one  by auto
  hence "adjoint I = I" using hermitian_def by auto
  with dim show "I \<in> carrier_mat (dim_row I) (dim_row I) \<and> inverts_mat I (adjoint I)" 
    unfolding inverts_mat_def using dim by auto
qed

lemma unitary_zero:
  fixes A :: "'a::conjugatable_field mat"
  assumes "A \<in> carrier_mat 0 0"
  shows "unitary A"
  unfolding unitary_def inverts_mat_def Let_def using assms by auto

lemma unitary_elim:
  assumes dims: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "P \<in> carrier_mat n n"
    and uP: "unitary P" and eq: "P * A * adjoint P = P * B * adjoint P"
  shows "A = B"
proof -
  have dimaP: "adjoint P \<in> carrier_mat n n" using dims by auto
  have iv: "inverts_mat P (adjoint P)" using uP unitary_def by auto
  then have "P * (adjoint P) = 1\<^sub>m n" using inverts_mat_def dims by auto
  then have aPP: "adjoint P * P = 1\<^sub>m n" using mat_mult_left_right_inverse[OF dims(3) dimaP] by auto
  have "adjoint P * (P * A * adjoint P) * P = (adjoint P * P) * A * (adjoint P * P)" 
    using dims dimaP by (mat_assoc n)
  also have "\<dots> = 1\<^sub>m n * A * 1\<^sub>m n" using aPP by auto
  also have "\<dots> = A" using dims by auto
  finally have eqA: "A = adjoint P * (P * A * adjoint P) * P" ..
  have "adjoint P * (P * B * adjoint P) * P = (adjoint P * P) * B * (adjoint P * P)" 
    using dims dimaP by (mat_assoc n)
  also have "\<dots> = 1\<^sub>m n * B * 1\<^sub>m n" using aPP by auto
  also have "\<dots> = B" using dims by auto
  finally have eqB: "B = adjoint P * (P * B * adjoint P) * P" ..
  then show ?thesis using eqA eqB eq by auto
qed

lemma unitary_is_corthogonal:
  fixes U :: "'a::conjugatable_field mat"
  assumes dim: "U \<in> carrier_mat n n" 
    and U: "unitary U"
  shows "corthogonal_mat U"
  unfolding corthogonal_mat_def Let_def
proof (rule conjI)
  have dima: "adjoint U \<in> carrier_mat n n" using dim by auto
  have aUU: "mat_adjoint U * U = (1\<^sub>m n)"
    apply (insert U[unfolded unitary_def] dim dima, drule conjunct2)
    apply (drule inverts_mat_symm[of "U", OF dim dima], unfold inverts_mat_def, auto)
    done
  then show "diagonal_mat (mat_adjoint U * U)"
    by (simp add: diagonal_mat_def)
  show "\<forall>i<dim_col U. (mat_adjoint U * U) $$ (i, i) \<noteq> 0" using dim by (simp add: aUU)
qed

lemma unitary_times_unitary:
  fixes P Q :: "'a:: conjugatable_field mat"
  assumes dim: "P \<in> carrier_mat n n" "Q \<in> carrier_mat n n"
    and uP: "unitary P" and uQ: "unitary Q"
  shows "unitary (P * Q)"
proof -
  have dim_pq: "P * Q \<in> carrier_mat n n" using dim by auto
  have "(P * Q) * adjoint (P * Q) = P * (Q * adjoint Q) * adjoint P" using dim by (mat_assoc n)
  also have "\<dots> = P * (1\<^sub>m n) * adjoint P" using uQ dim by auto
  also have "\<dots> = P * adjoint P" using dim by (mat_assoc n)
  also have "\<dots> = 1\<^sub>m n" using uP dim by simp
  finally have "(P * Q) * adjoint (P * Q) = 1\<^sub>m n" by auto
  hence "inverts_mat (P * Q) (adjoint (P * Q))" 
    using inverts_mat_def dim_pq by auto
  thus "unitary (P*Q)" using unitary_def dim_pq by auto
qed

lemma unitary_operator_keep_trace:
  fixes U A :: "complex mat"
  assumes dU: "U \<in> carrier_mat n n" and dA: "A \<in> carrier_mat n n" and u: "unitary U"
  shows "trace A = trace (adjoint U * A * U)"
proof -
  have u': "U * adjoint U = 1\<^sub>m n" using u unfolding unitary_def inverts_mat_def using dU by auto
  have "trace (adjoint U * A * U) = trace (U * adjoint U * A)" using dU dA by (mat_assoc n)
  also have "\<dots> = trace A" using u' dA by auto
  finally show ?thesis by auto
qed

subsection \<open>Normalization of vectors\<close>

definition vec_norm :: "complex vec \<Rightarrow> complex" where
  "vec_norm v \<equiv> csqrt (v \<bullet>c v)"

lemma vec_norm_geq_0:
  fixes v :: "complex vec"
  shows "vec_norm v \<ge> 0"
  unfolding vec_norm_def by (insert self_cscalar_prod_geq_0[of v], simp)

lemma vec_norm_zero:
  fixes v ::  "complex vec"
  assumes dim: "v \<in> carrier_vec n"
  shows "vec_norm v = 0 \<longleftrightarrow> v = 0\<^sub>v n"
  unfolding vec_norm_def
  by (subst conjugate_square_eq_0_vec[OF dim, symmetric], rule csqrt_eq_0)

lemma vec_norm_ge_0:
  fixes v ::  "complex vec"
  assumes dim_v: "v \<in> carrier_vec n" and neq0: "v \<noteq> 0\<^sub>v n"
  shows "vec_norm v > 0"
proof -
  have geq: "vec_norm v \<ge> 0" using vec_norm_geq_0 by auto
  have neq: "vec_norm v \<noteq> 0" 
    apply (insert dim_v neq0)
    apply (drule vec_norm_zero, auto)
    done
  show ?thesis using neq geq by (rule dual_order.not_eq_order_implies_strict)
qed

definition vec_normalize :: "complex vec \<Rightarrow> complex vec" where
  "vec_normalize v = (if (v = 0\<^sub>v (dim_vec v)) then v else 1 / (vec_norm v) \<cdot>\<^sub>v v)"

lemma normalized_vec_dim[simp]:
  assumes "(v::complex vec) \<in> carrier_vec n"
  shows "vec_normalize v \<in> carrier_vec n"
  unfolding vec_normalize_def using assms by auto

lemma vec_eq_norm_smult_normalized:
  shows "v = vec_norm v \<cdot>\<^sub>v vec_normalize v"
proof (cases "v = 0\<^sub>v (dim_vec v)")
  define n where "n = dim_vec v"
  then have dimv: "v \<in> carrier_vec n" by auto
  then have dimnv: "vec_normalize v \<in> carrier_vec n" by auto
  {
    case True
    then have v0: "v = 0\<^sub>v n" using n_def by auto
    then have n0: "vec_norm v = 0" using vec_norm_def by auto
    have "vec_norm v \<cdot>\<^sub>v vec_normalize v = 0\<^sub>v n" 
      unfolding smult_vec_def by (auto simp add: n0 carrier_vecD[OF dimnv])
    then show ?thesis using v0 by auto
    next
    case False
    then have v: "v \<noteq> 0\<^sub>v n" using n_def by auto
    then have ge0: "vec_norm v > 0" using vec_norm_ge_0 dimv by auto
    have "vec_normalize v = (1 / vec_norm v) \<cdot>\<^sub>v v" using False vec_normalize_def by auto
    then have "vec_norm v \<cdot>\<^sub>v vec_normalize v = (vec_norm v * (1 / vec_norm v)) \<cdot>\<^sub>v v"
      using smult_smult_assoc by auto
    also have "\<dots> = v" using ge0 by auto
    finally have "v = vec_norm v \<cdot>\<^sub>v vec_normalize v"..
    then show "v = vec_norm v \<cdot>\<^sub>v vec_normalize v" using v by auto
  }
qed

lemma normalized_cscalar_prod:
  fixes v w :: "complex vec"
  assumes dim_v: "v \<in> carrier_vec n" and dim_w: "w \<in> carrier_vec n"
  shows "v \<bullet>c w = (vec_norm v * vec_norm w) * (vec_normalize v \<bullet>c vec_normalize w)"
  unfolding vec_normalize_def apply (split if_split, split if_split)
proof (intro conjI impI)
  note dim0 = dim_v dim_w
  have dim: "dim_vec v = n" "dim_vec w = n" using dim0 by auto
  {
    assume "w = 0\<^sub>v n" "v = 0\<^sub>v n"
    then have lhs: "v \<bullet>c w = 0" by auto
    then moreover have rhs: "vec_norm v * vec_norm w * (v \<bullet>c w) = 0" by auto
    ultimately have "v \<bullet>c w = vec_norm v * vec_norm w * (v \<bullet>c w)" by auto
  }
  with dim show "w = 0\<^sub>v (dim_vec w) \<Longrightarrow> v = 0\<^sub>v (dim_vec v) \<Longrightarrow> v \<bullet>c w = vec_norm v * vec_norm w * (v \<bullet>c w)" by auto
  {
    assume asm: "w = 0\<^sub>v n" "v \<noteq> 0\<^sub>v n"
    then have w0: "conjugate w = 0\<^sub>v n" by auto
    with dim0 have "(1 / vec_norm v \<cdot>\<^sub>v v) \<bullet>c w = 0" by auto
    then moreover have rhs: "vec_norm v * vec_norm w * ((1 / vec_norm v \<cdot>\<^sub>v v) \<bullet>c w) = 0" by auto
    moreover have "v \<bullet>c w = 0" using w0 dim0 by auto
    ultimately have "v \<bullet>c w = vec_norm v * vec_norm w * ((1 / vec_norm v \<cdot>\<^sub>v v) \<bullet>c w)" by auto
  }
  with dim show "w = 0\<^sub>v (dim_vec w) \<Longrightarrow> v \<noteq> 0\<^sub>v (dim_vec v) \<Longrightarrow> v \<bullet>c w = vec_norm v * vec_norm w * ((1 / vec_norm v \<cdot>\<^sub>v v) \<bullet>c w)" by auto
  {
    assume asm: "w \<noteq> 0\<^sub>v n" "v = 0\<^sub>v n"
    with dim0 have "v \<bullet>c (1 / vec_norm w \<cdot>\<^sub>v w) = 0" by auto
    then moreover have rhs: "vec_norm v * vec_norm w * (v \<bullet>c (1 / vec_norm w \<cdot>\<^sub>v w)) = 0" by auto
    moreover have "v \<bullet>c w = 0" using asm dim0 by auto
    ultimately have "v \<bullet>c w = vec_norm v * vec_norm w * (v \<bullet>c (1 / vec_norm w \<cdot>\<^sub>v w))" by auto
  }
  with dim show "w \<noteq> 0\<^sub>v (dim_vec w) \<Longrightarrow> v = 0\<^sub>v (dim_vec v) \<Longrightarrow> v \<bullet>c w = vec_norm v * vec_norm w * (v \<bullet>c (1 / vec_norm w \<cdot>\<^sub>v w))" by auto
  {
    assume asmw: "w \<noteq> 0\<^sub>v n" and asmv: "v \<noteq> 0\<^sub>v n"
    have "vec_norm w > 0" by (insert asmw dim0, rule vec_norm_ge_0, auto)
    then have cw: "conjugate (1 / vec_norm w) = 1 / vec_norm w" by (simp add: complex_eq_iff complex_is_Real_iff) 
    from dim0 have 
      "((1 / vec_norm v \<cdot>\<^sub>v v) \<bullet>c (1 / vec_norm w \<cdot>\<^sub>v w)) = 1 / vec_norm v * (v \<bullet>c (1 / vec_norm w \<cdot>\<^sub>v w))" by auto
    also have "\<dots> = 1 / vec_norm v * (v \<bullet> (conjugate (1 / vec_norm w) \<cdot>\<^sub>v conjugate w))"
      by (subst conjugate_smult_vec, auto)
    also have "\<dots> = 1 / vec_norm v * conjugate (1 / vec_norm w) * (v \<bullet> conjugate w)" using dim by auto
    also have "\<dots> = 1 / vec_norm v * (1 / vec_norm w) * (v \<bullet>c w)" using vec_norm_ge_0 cw by auto
    finally have eq1: "(1 / vec_norm v \<cdot>\<^sub>v v) \<bullet>c (1 / vec_norm w \<cdot>\<^sub>v w) = 1 / vec_norm v * (1 / vec_norm w) * (v \<bullet>c w)" .
    then have "vec_norm v * vec_norm w * ((1 / vec_norm v \<cdot>\<^sub>v v) \<bullet>c (1 / vec_norm w \<cdot>\<^sub>v w)) = (v \<bullet>c w)" 
      by (subst eq1, insert vec_norm_ge_0[of v n, OF dim_v asmv] vec_norm_ge_0[of w n, OF dim_w asmw], auto)
  }
  with dim show " w \<noteq> 0\<^sub>v (dim_vec w) \<Longrightarrow> v \<noteq> 0\<^sub>v (dim_vec v) \<Longrightarrow> v \<bullet>c w = vec_norm v * vec_norm w * ((1 / vec_norm v \<cdot>\<^sub>v v) \<bullet>c (1 / vec_norm w \<cdot>\<^sub>v w))" by auto
qed

lemma normalized_vec_norm :
  fixes v :: "complex vec"
  assumes dim_v: "v \<in> carrier_vec n" 
    and neq0: "v \<noteq> 0\<^sub>v n"
  shows "vec_normalize v \<bullet>c vec_normalize v = 1"
  unfolding vec_normalize_def
proof (simp, rule conjI)
  show "v = 0\<^sub>v (dim_vec v) \<longrightarrow> v \<bullet>c v = 1" using neq0 dim_v by auto
  have dim_a: "(vec_normalize v) \<in> carrier_vec n" "conjugate (vec_normalize v) \<in> carrier_vec n" using dim_v vec_normalize_def by auto 
  note dim = dim_v dim_a
  have nvge0: "vec_norm v > 0" using vec_norm_ge_0 neq0 dim_v by auto
  then have vvvv: "v \<bullet>c v = (vec_norm v) * (vec_norm v)" unfolding vec_norm_def by (metis power2_csqrt power2_eq_square)
  from nvge0 have "conjugate (vec_norm v) = vec_norm v" by (simp add: complex_eq_iff complex_is_Real_iff) 
  then have "v \<bullet>c (1 / vec_norm v \<cdot>\<^sub>v v) = 1 / vec_norm v * (v \<bullet>c v)" 
    by (subst conjugate_smult_vec, auto)
  also have "\<dots> = 1 / vec_norm v * vec_norm v * vec_norm v" using vvvv by auto
  also have "\<dots> = vec_norm v" by auto
  finally have "v \<bullet>c (1 / vec_norm v \<cdot>\<^sub>v v) = vec_norm v".
  then show "v \<noteq> 0\<^sub>v (dim_vec v) \<longrightarrow> vec_norm v \<noteq> 0 \<and> v \<bullet>c (1 / vec_norm v \<cdot>\<^sub>v v) = vec_norm v" 
    using neq0 nvge0 by auto
qed

lemma normalize_zero:
  assumes "v \<in> carrier_vec n"
  shows "vec_normalize v = 0\<^sub>v n \<longleftrightarrow> v = 0\<^sub>v n"
proof
  show "v = 0\<^sub>v n \<Longrightarrow> vec_normalize v = 0\<^sub>v n" unfolding vec_normalize_def by auto
next
  have "v \<noteq> 0\<^sub>v n \<Longrightarrow> vec_normalize v \<noteq> 0\<^sub>v n" unfolding vec_normalize_def 
  proof (simp, rule impI)
    assume asm: "v \<noteq> 0\<^sub>v n"
    then have "vec_norm v > 0" using vec_norm_ge_0 assms by auto
    then have nvge0: "1 / vec_norm v > 0" by (simp add: complex_is_Real_iff)
    have "\<exists>k < n. v $ k \<noteq> 0" using asm assms by auto
    then obtain k where kn: "k < n" and  vkneq0: "v $ k \<noteq> 0" by auto
    then have "(1 / vec_norm v \<cdot>\<^sub>v v) $ k = (1 / vec_norm v) * (v $ k)" 
      using assms carrier_vecD index_smult_vec(1) by blast
    with nvge0 vkneq0 have "(1 / vec_norm v \<cdot>\<^sub>v v) $ k \<noteq> 0" by auto
    then show "1 / vec_norm v \<cdot>\<^sub>v v \<noteq> 0\<^sub>v n" using assms kn by fastforce
  qed
  then show "vec_normalize v = 0\<^sub>v n \<Longrightarrow> v = 0\<^sub>v n" by auto
qed

lemma normalize_normalize[simp]:
  "vec_normalize (vec_normalize v) = vec_normalize v"
proof (rule disjE[of "v = 0\<^sub>v (dim_vec v)" "v \<noteq> 0\<^sub>v (dim_vec v)"], auto)
  let ?n = "dim_vec v"
{
  assume "v = 0\<^sub>v ?n"
  then have "vec_normalize v = v" unfolding vec_normalize_def by auto
  then show "vec_normalize (vec_normalize v) = vec_normalize v" by auto
}
  assume neq0: "v \<noteq> 0\<^sub>v ?n"
  have dim: "v \<in> carrier_vec ?n" by auto
  have "vec_norm (vec_normalize v) = 1" unfolding vec_norm_def
    using normalized_vec_norm[OF dim neq0] by auto
  then show "vec_normalize (vec_normalize v) = vec_normalize v" 
    by (subst (1) vec_normalize_def, simp)
qed

subsection \<open>Spectral decomposition of normal complex matrices\<close>

lemma normalize_keep_corthogonal:
  fixes vs :: "complex vec list"
  assumes cor: "corthogonal vs" and dims: "set vs \<subseteq> carrier_vec n"
  shows "corthogonal (map vec_normalize vs)"
  unfolding corthogonal_def
proof (rule allI, rule impI, rule allI, rule impI, goal_cases)
  case c: (1 i j)
  let ?m = "length vs"
  have len: "length (map vec_normalize vs) = ?m" by auto
  have dim: "\<And>k. k < ?m \<Longrightarrow> (vs ! k) \<in> carrier_vec n" using dims by auto
  have map: "\<And>k. k < ?m \<Longrightarrow>  map vec_normalize vs ! k = vec_normalize (vs ! k)" by auto

  have eq1: "\<And>j k. j < ?m \<Longrightarrow> k < ?m \<Longrightarrow> ((vs ! j) \<bullet>c (vs ! k) = 0) = (j \<noteq> k)" using assms unfolding corthogonal_def by auto
  then have "\<And>k. k < ?m \<Longrightarrow> (vs ! k) \<bullet>c (vs ! k) \<noteq> 0 " by auto
  then have "\<And>k. k < ?m \<Longrightarrow> (vs ! k) \<noteq> (0\<^sub>v n)" using dim 
    by (auto simp add: conjugate_square_eq_0_vec[of _ n, OF dim])
  then have vnneq0: "\<And>k. k < ?m \<Longrightarrow> vec_norm (vs ! k) \<noteq> 0" using vec_norm_zero[OF dim] by auto
  then have i0: "vec_norm (vs ! i) \<noteq> 0" and j0: "vec_norm (vs ! j) \<noteq> 0" using c by auto
  have "(vs ! i) \<bullet>c (vs ! j) = vec_norm (vs ! i) * vec_norm (vs ! j) * (vec_normalize (vs ! i) \<bullet>c vec_normalize (vs ! j))"
    by (subst normalized_cscalar_prod[of "vs ! i" n "vs ! j"], auto, insert dim c, auto)
  with i0 j0 have "(vec_normalize (vs ! i) \<bullet>c vec_normalize (vs ! j) = 0) = ((vs ! i) \<bullet>c (vs ! j) = 0)" by auto
  with eq1 c have "(vec_normalize (vs ! i) \<bullet>c vec_normalize (vs ! j) = 0) = (i \<noteq> j)" by auto
  with map c show "(map vec_normalize vs ! i \<bullet>c map vec_normalize vs ! j = 0) = (i \<noteq> j)" by auto
qed

lemma normalized_corthogonal_mat_is_unitary:
  assumes W: "set ws \<subseteq> carrier_vec n"
    and orth: "corthogonal ws"
    and len: "length ws = n"
  shows "unitary (mat_of_cols n (map vec_normalize ws))" (is "unitary ?W")
proof -
  define vs where "vs = map vec_normalize ws"
  define W where "W = mat_of_cols n vs"
  have W': "set vs \<subseteq> carrier_vec n" using assms vs_def by auto
  then have W'': "\<And>k. k < length vs \<Longrightarrow> vs ! k \<in> carrier_vec n" by auto
  have orth': "corthogonal vs" using assms normalize_keep_corthogonal vs_def by auto
  have len'[simp]: "length vs = n" using assms vs_def by auto
  have dimW: "W \<in> carrier_mat n n" using W_def len by auto
  have "adjoint W \<in> carrier_mat n n" using dimW by auto
  then have dimaW: "mat_adjoint W \<in> carrier_mat n n" by auto
  {
    fix i j assume i: "i < n" and j: "j < n"
    have dimws: "(ws ! i) \<in> carrier_vec n" "(ws ! j) \<in> carrier_vec n" using W len i j by auto
    have "(ws ! i) \<bullet>c (ws ! i) \<noteq> 0" "(ws ! j) \<bullet>c (ws ! j) \<noteq> 0" using orth corthogonal_def[of ws] len i j by auto
    then have neq0: "(ws ! i) \<noteq> 0\<^sub>v n" "(ws ! j) \<noteq> 0\<^sub>v n"
      by (auto simp add: conjugate_square_eq_0_vec[of "ws ! i" n])
    then have "vec_norm (ws ! i) > 0" "vec_norm (ws ! j) > 0" using vec_norm_ge_0 dimws by auto
    then have ge0: "vec_norm (ws ! i) * vec_norm (ws ! j) > 0" by auto
    have ws': "vs ! i = vec_normalize (ws ! i)" 
        "vs ! j = vec_normalize (ws ! j)" 
      using len i j vs_def by auto
    have ii1: "(vs ! i) \<bullet>c (vs ! i) = 1" 
      apply (simp add: ws')
      apply (rule normalized_vec_norm[of "ws ! i"], rule dimws, rule neq0)
      done
    have ij0: "i \<noteq> j \<Longrightarrow> (ws ! i)  \<bullet>c (ws ! j) = 0" using i j 
      by (insert orth, auto simp add: corthogonal_def[of ws] len)
    have "i \<noteq> j \<Longrightarrow> (ws ! i)  \<bullet>c (ws ! j) =  (vec_norm (ws ! i) * vec_norm (ws ! j)) * ((vs ! i) \<bullet>c (vs ! j))"
      apply (auto simp add: ws')
      apply (rule normalized_cscalar_prod)
       apply (rule dimws, rule dimws)
      done
    with ij0 have ij0': "i \<noteq> j \<Longrightarrow> (vs ! i) \<bullet>c (vs ! j) = 0" using ge0 by auto
    have cWk: "\<And>k. k < n \<Longrightarrow> col W k = vs ! k" unfolding W_def 
    apply (subst col_mat_of_cols)
      apply (auto simp add: W'')
      done
    have "(mat_adjoint W * W) $$ (j, i) = row (mat_adjoint W) j \<bullet> col W i"
      by (insert dimW i j dimaW, auto)
    also have "\<dots> = conjugate (col W j) \<bullet> col W i" 
      by (insert dimW i j dimaW, auto simp add: mat_adjoint_def)
    also have "\<dots> = col W i \<bullet> conjugate (col W j)" using comm_scalar_prod[of "col W i" n] dimW by auto
    also have "\<dots> = (vs ! i) \<bullet>c (vs ! j)" using W_def col_mat_of_cols i j len cWk by auto
    finally have "(mat_adjoint W * W) $$ (j, i) = (vs ! i) \<bullet>c (vs ! j)".
    then have "(mat_adjoint W * W) $$ (j, i) = (if (j = i) then 1 else 0)"
      by (auto simp add: ii1 ij0')
  }
  note maWW = this
  then have "mat_adjoint W * W = 1\<^sub>m n" unfolding one_mat_def using dimW dimaW
    by (auto simp add: maWW adjoint_def)
  then have iv0: "adjoint W * W = 1\<^sub>m n"  by auto
  have dimaW: "adjoint W \<in> carrier_mat n n" using dimaW by auto
  then have iv1: "W * adjoint W  = 1\<^sub>m n" using mat_mult_left_right_inverse dimW iv0 by auto
  then show "unitary W" unfolding unitary_def inverts_mat_def using dimW dimaW iv0 iv1 by auto 
qed

lemma normalize_keep_eigenvector:
  assumes ev: "eigenvector A v e" 
    and dim: "A \<in> carrier_mat n n" "v \<in> carrier_vec n"
  shows "eigenvector A (vec_normalize v) e"
  unfolding eigenvector_def
proof 
  show "vec_normalize v \<in> carrier_vec (dim_row A)" using dim by auto
  have eg: "A *\<^sub>v v = e \<cdot>\<^sub>v v" using ev dim eigenvector_def by auto
  have vneq0: "v \<noteq> 0\<^sub>v n" using ev dim unfolding eigenvector_def by auto
  then have s0: "vec_normalize v \<noteq> 0\<^sub>v n" 
    by (insert dim, subst normalize_zero[of v], auto)
  from vneq0 have vvge0: "vec_norm v > 0" using vec_norm_ge_0 dim by auto
  have s1: "A *\<^sub>v vec_normalize v = e \<cdot>\<^sub>v vec_normalize v" unfolding vec_normalize_def 
    using vneq0 dim 
    apply (auto, simp add: mult_mat_vec)
    apply (subst eg, auto)
    done
  with s0 dim show "vec_normalize v \<noteq> 0\<^sub>v (dim_row A) \<and> A *\<^sub>v vec_normalize v = e \<cdot>\<^sub>v vec_normalize v" by auto
qed

lemma four_block_mat_adjoint:
  fixes A B C D :: "'a::conjugatable_field mat"
  assumes dim: "A \<in> carrier_mat nr1 nc1" "B \<in> carrier_mat nr1 nc2"
  "C \<in> carrier_mat nr2 nc1" "D \<in> carrier_mat nr2 nc2"
  shows "adjoint (four_block_mat A B C D) 
    = four_block_mat (adjoint A) (adjoint C) (adjoint B) (adjoint D)"
  by (rule eq_matI, insert dim, auto simp add: adjoint_eval)

fun unitary_schur_decomposition :: "complex mat \<Rightarrow> complex list \<Rightarrow> complex mat \<times> complex mat \<times> complex mat" where 
  "unitary_schur_decomposition A [] = (A, 1\<^sub>m (dim_row A), 1\<^sub>m (dim_row A))"
| "unitary_schur_decomposition A (e # es) = (let
       n = dim_row A;
       n1 = n - 1;
       v' = find_eigenvector A e;
       v = vec_normalize v';
       ws0 = gram_schmidt n (basis_completion v);
       ws = map vec_normalize ws0;
       W = mat_of_cols n ws;
       W' = corthogonal_inv W;
       A' = W' * A * W;
       (A1,A2,A0,A3) = split_block A' 1 1;
       (B,P,Q) = unitary_schur_decomposition A3 es;
       z_row = (0\<^sub>m 1 n1);
       z_col = (0\<^sub>m n1 1);
       one_1 = 1\<^sub>m 1
     in (four_block_mat A1 (A2 * P) A0 B, 
     W * four_block_mat one_1 z_row z_col P, 
     four_block_mat one_1 z_row z_col Q * W'))"

theorem unitary_schur_decomposition:
  assumes A: "(A::complex mat) \<in> carrier_mat n n"
      and c: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> es. [:- e, 1:])"
      and B: "unitary_schur_decomposition A es = (B,P,Q)"
  shows "similar_mat_wit A B P Q \<and> upper_triangular B \<and> diag_mat B = es \<and> unitary P \<and> (Q = adjoint P)"
  using assms
proof (induct es arbitrary: n A B P Q)
  case Nil
  with degree_monic_char_poly[of A n] 
  show ?case by (auto intro: similar_mat_wit_refl simp: diag_mat_def unitary_zero)
next
  case (Cons e es n A C P Q)
  let ?n1 = "n - 1"
  from Cons have A: "A \<in> carrier_mat n n" and dim: "dim_row A = n" by auto
  let ?cp = "char_poly A"
  from Cons(3)
  have cp: "?cp = [: -e, 1 :] * (\<Prod>e \<leftarrow> es. [:- e, 1:])" by auto
  have mon: "monic (\<Prod>e\<leftarrow> es. [:- e, 1:])" by (rule monic_prod_list, auto)
  have deg: "degree ?cp = Suc (degree (\<Prod>e\<leftarrow> es. [:- e, 1:]))" unfolding cp
    by (subst degree_mult_eq, insert mon, auto)
  with degree_monic_char_poly[OF A] have n: "n \<noteq> 0" by auto
  define v' where "v' = find_eigenvector A e"
  define v where "v = vec_normalize v'"
  define b where "b = basis_completion v"
  define ws0 where "ws0 = gram_schmidt n b"
  define ws where "ws = map vec_normalize ws0"
  define W where "W = mat_of_cols n ws"
  define W' where "W' = corthogonal_inv W"
  define A' where "A' = W' * A * W"
  obtain A1 A2 A0 A3 where splitA': "split_block A' 1 1 = (A1,A2,A0,A3)"
    by (cases "split_block A' 1 1", auto)
  obtain B P' Q' where schur: "unitary_schur_decomposition A3 es = (B,P',Q')" 
    by (cases "unitary_schur_decomposition A3 es", auto)
  let ?P' = "four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 ?n1) (0\<^sub>m ?n1 1) P'"
  let ?Q' = "four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 ?n1) (0\<^sub>m ?n1 1) Q'"
  have C: "C = four_block_mat A1 (A2 * P') A0 B" and P: "P = W * ?P'" and Q: "Q = ?Q' * W'"
    using Cons(4) unfolding unitary_schur_decomposition.simps
    Let_def list.sel dim
    v'_def[symmetric] v_def[symmetric] b_def[symmetric] ws0_def[symmetric] ws_def[symmetric] W'_def[symmetric] W_def[symmetric]
    A'_def[symmetric] split splitA' schur by auto
  have e: "eigenvalue A e" 
    unfolding eigenvalue_root_char_poly[OF A] cp by simp
  from find_eigenvector[OF A e] have ev': "eigenvector A v' e" unfolding v'_def .
  then have "v' \<in> carrier_vec n" unfolding eigenvector_def using A by auto
  with ev' have ev: "eigenvector A v e" unfolding v_def using A dim normalize_keep_eigenvector by auto
  from this[unfolded eigenvector_def]
  have v[simp]: "v \<in> carrier_vec n" and v0: "v \<noteq> 0\<^sub>v n" using A by auto
  interpret cof_vec_space n "TYPE(complex)" .
  from basis_completion[OF v v0, folded b_def]
  have span_b: "span (set b) = carrier_vec n" and dist_b: "distinct b" 
    and indep: "\<not> lin_dep (set b)" and b: "set b \<subseteq> carrier_vec n" and hdb: "hd b = v" 
    and len_b: "length b = n" by auto
  from hdb len_b n obtain vs where bv: "b = v # vs" by (cases b, auto)
  from gram_schmidt_result[OF b dist_b indep refl, folded ws0_def]
  have ws0: "set ws0 \<subseteq> carrier_vec n" "corthogonal ws0" "length ws0 = n" 
    by (auto simp: len_b)
  then have ws: "set ws \<subseteq> carrier_vec n" "corthogonal ws" "length ws = n" unfolding ws_def
    using normalize_keep_corthogonal by auto
  have ws0ne: "ws0 \<noteq> []" using `length ws0 = n` n by auto
  from gram_schmidt_hd[OF v, of vs, folded bv] have hdws0: "hd ws0 = (vec_normalize v')" unfolding ws0_def v_def .
  have "hd ws = vec_normalize (hd ws0)" unfolding ws_def using hd_map[OF ws0ne]  by auto
  then have hdws: "hd ws = v" unfolding v_def using normalize_normalize[of v'] hdws0 by auto
  have orth_W: "corthogonal_mat W" using orthogonal_mat_of_cols ws unfolding W_def.
  have W: "W \<in> carrier_mat n n"
    using ws unfolding W_def using mat_of_cols_carrier(1)[of n ws] by auto
  have W': "W' \<in> carrier_mat n n" unfolding W'_def corthogonal_inv_def using W 
    by (auto simp: mat_of_rows_def)  
  from corthogonal_inv_result[OF orth_W] 
  have W'W: "inverts_mat W' W" unfolding W'_def .
  hence WW': "inverts_mat W W'" using mat_mult_left_right_inverse[OF W' W] W' W
    unfolding inverts_mat_def by auto
  have A': "A' \<in> carrier_mat n n" using W W' A unfolding A'_def by auto
  have A'A_wit: "similar_mat_wit A' A W' W"
    by (rule similar_mat_witI[of _ _ n], insert W W' A A' W'W WW', auto simp: A'_def
    inverts_mat_def)
  hence A'A: "similar_mat A' A" unfolding similar_mat_def by blast
  from similar_mat_wit_sym[OF A'A_wit] have simAA': "similar_mat_wit A A' W W'" by auto
  have eigen[simp]: "A *\<^sub>v v = e \<cdot>\<^sub>v v" and v0: "v \<noteq> 0\<^sub>v n"
    using v_def v'_def find_eigenvector[OF A e] A normalize_keep_eigenvector
    unfolding eigenvector_def by auto
  let ?f = "(\<lambda> i. if i = 0 then e else 0)"
  have col0: "col A' 0 = vec n ?f"
    unfolding A'_def W'_def W_def
    using corthogonal_col_ev_0[OF A v v0 eigen n hdws ws].
  from A' n have "dim_row A' = 1 + ?n1" "dim_col A' = 1 + ?n1" by auto
  from split_block[OF splitA' this] have A2: "A2 \<in> carrier_mat 1 ?n1"
    and A3: "A3 \<in> carrier_mat ?n1 ?n1" 
    and A'block: "A' = four_block_mat A1 A2 A0 A3" by auto
  have A1id: "A1 = mat 1 1 (\<lambda> _. e)"
    using splitA'[unfolded split_block_def Let_def] arg_cong[OF col0, of "\<lambda> v. v $ 0"] A' n
    by (auto simp: col_def)
  have A1: "A1 \<in> carrier_mat 1 1" unfolding A1id by auto
  {
    fix i
    assume "i < ?n1"
    with arg_cong[OF col0, of "\<lambda> v. v $ Suc i"] A'
    have "A' $$ (Suc i, 0) = 0" by auto
  } note A'0 = this
  have A0id: "A0 = 0\<^sub>m ?n1 1"
    using splitA'[unfolded split_block_def Let_def] A'0 A' by auto
  have A0: "A0 \<in> carrier_mat ?n1 1" unfolding A0id by auto
  from cp char_poly_similar[OF A'A]
  have cp: "char_poly A' = [: -e,1 :] * (\<Prod> e \<leftarrow> es. [:- e, 1:])" by simp
  also have "char_poly A' = char_poly A1 * char_poly A3" 
    unfolding A'block A0id
    by (rule char_poly_four_block_zeros_col[OF A1 A2 A3])
  also have "char_poly A1 = [: -e,1 :]"
    by (simp add: A1id char_poly_defs det_def signof_def sign_def)
  finally have cp: "char_poly A3 = (\<Prod> e \<leftarrow> es. [:- e, 1:])"
    by (metis mult_cancel_left pCons_eq_0_iff zero_neq_one)
  from Cons(1)[OF A3 cp schur]
  have simIH: "similar_mat_wit A3 B P' Q'" and ut: "upper_triangular B" and diag: "diag_mat B = es"
    and uP': "unitary P'" and Q'P': "Q' = adjoint P'"
    by auto
  from similar_mat_witD2[OF A3 simIH] 
  have B: "B \<in> carrier_mat ?n1 ?n1" and P': "P' \<in> carrier_mat ?n1 ?n1" and Q': "Q' \<in> carrier_mat ?n1 ?n1" 
    and PQ': "P' * Q' = 1\<^sub>m ?n1" by auto
  have A0_eq: "A0 = P' * A0 * 1\<^sub>m 1" unfolding A0id using P' by auto
  have simA'C: "similar_mat_wit A' C ?P' ?Q'" unfolding A'block C
    by (rule similar_mat_wit_four_block[OF similar_mat_wit_refl[OF A1] simIH _ A0_eq A1 A3 A0],
    insert PQ' A2 P' Q', auto)
  have ut1: "upper_triangular A1" unfolding A1id by auto
  have ut: "upper_triangular C" unfolding C A0id
    by (intro upper_triangular_four_block[OF _ B ut1 ut], auto simp: A1id)
  from A1id have diagA1: "diag_mat A1 = [e]" unfolding diag_mat_def by auto
  from diag_four_block_mat[OF A1 B] have diag: "diag_mat C = e # es" unfolding diag diagA1 C by simp

  have aW: "adjoint W \<in> carrier_mat n n" using W by auto
  have aW': "adjoint W' \<in> carrier_mat n n" using W' by auto
  have "unitary W" using W_def ws_def ws0 normalized_corthogonal_mat_is_unitary by auto
  then have ivWaW: "inverts_mat W (adjoint W)" using unitary_def W aW by auto
  with WW' have W'aW: "W' = (adjoint W)" using inverts_mat_unique W W' aW by auto
  then have "adjoint W' = W" using adjoint_adjoint by auto
  with ivWaW have "inverts_mat W' (adjoint W')" using inverts_mat_symm W aW W'aW by auto
  then have "unitary W'" using unitary_def W' by auto

  have newP': "P' \<in> carrier_mat (n - Suc 0) (n - Suc 0)" using P' by auto
  have rl: "\<And> x1 x2 x3 x4 y1 y2 y3 y4 f. x1 = y1 \<Longrightarrow> x2 = y2 \<Longrightarrow> x3 = y3 \<Longrightarrow> x4 = y4 \<Longrightarrow> f x1 x2 x3 x4 = f y1 y2 y3 y4" by simp
  have Q'aP': "?Q' = adjoint ?P'"
    apply (subst four_block_mat_adjoint, auto simp add: newP')
    apply (rule rl[where f2 = four_block_mat])
       apply (auto simp add: eq_matI adjoint_eval Q'P')
    done
  have "adjoint P = adjoint ?P' * adjoint W"  using W newP' n
    apply (simp add: P)
    apply (subst adjoint_mult[of W, symmetric])
     apply (auto simp add: W P' carrier_matD[of W n n])
    done
  also have "\<dots> = ?Q' * W'" using Q'aP' W'aW by auto
  also have "\<dots> = Q" using Q by auto
  finally have QaP: "Q = adjoint P" ..

  from similar_mat_wit_trans[OF simAA' simA'C, folded P Q] have smw: "similar_mat_wit A C P Q" by blast
  then have dimP: "P \<in> carrier_mat n n" and dimQ: "Q \<in> carrier_mat n n" unfolding similar_mat_wit_def using A by auto
  from smw have "P * Q = 1\<^sub>m n" unfolding similar_mat_wit_def using A  by auto
  then have "inverts_mat P Q" using inverts_mat_def dimP by auto
  then have uP: "unitary P" using QaP unitary_def dimP by auto
    
  from ut similar_mat_wit_trans[OF simAA' simA'C, folded P Q] diag uP QaP
  show ?case by blast
qed

lemma complex_mat_char_poly_factorizable:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  shows "\<exists>as. char_poly A =  (\<Prod> a \<leftarrow> as. [:- a, 1:]) \<and> length as = n"
proof -
  let ?ca = "char_poly A"
  have ex0: "\<exists>bs. Polynomial.smult (lead_coeff ?ca) (\<Prod>b\<leftarrow>bs. [:- b, 1:]) = ?ca \<and>
     length bs = degree ?ca"
    by (simp add: fundamental_theorem_algebra_factorized)
  then obtain bs where " Polynomial.smult (lead_coeff ?ca) (\<Prod>b\<leftarrow>bs. [:- b, 1:]) = ?ca \<and>
     length bs = degree ?ca" by auto
  moreover have "lead_coeff ?ca = (1::complex)" 
    using assms degree_monic_char_poly by blast
  ultimately have ex1: "?ca = (\<Prod>b\<leftarrow>bs. [:- b, 1:]) \<and> length bs = degree ?ca" by auto
  moreover have "degree ?ca = n"
    by (simp add: assms degree_monic_char_poly)
  ultimately show ?thesis by auto
qed

lemma complex_mat_has_unitary_schur_decomposition:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  shows "\<exists>B P es. similar_mat_wit A B P (adjoint P) \<and> unitary P 
    \<and> char_poly A = (\<Prod> (e :: complex) \<leftarrow> es. [:- e, 1:]) \<and> diag_mat B = es"
proof -
  have "\<exists>es. char_poly A =  (\<Prod> e \<leftarrow> es. [:- e, 1:]) \<and> length es = n" 
    using assms by (simp add: complex_mat_char_poly_factorizable)
  then obtain es where es: "char_poly A =  (\<Prod> e \<leftarrow> es. [:- e, 1:]) \<and> length es = n" by auto
  obtain B P Q where B: "unitary_schur_decomposition A es = (B,P,Q)" by (cases "unitary_schur_decomposition A es", auto)

  have "similar_mat_wit A B P Q \<and> upper_triangular B \<and> unitary P \<and> (Q = adjoint P) \<and> 
   char_poly A = (\<Prod> (e :: complex) \<leftarrow> es. [:- e, 1:]) \<and> diag_mat B = es" using assms es B
    by (auto simp add: unitary_schur_decomposition)
  then show ?thesis by auto
qed

lemma normal_upper_triangular_matrix_is_diagonal:
  fixes A :: "'a::conjugatable_ordered_field mat"
  assumes "A \<in> carrier_mat n n"
    and tri: "upper_triangular A"
    and norm: "A * adjoint A = adjoint A * A"
  shows "diagonal_mat A"
proof (rule disjE[of "n = 0" "n > 0"], blast)
  have dim: "dim_row A = n" "dim_col A = n" using assms by auto
  from norm have eq0: "\<And>i j. (A * adjoint A)$$(i,j) = (adjoint A * A)$$(i,j)" by auto
  have nat_induct_strong: 
    "\<And>P. (P::nat\<Rightarrow>bool) 0 \<Longrightarrow> (\<And>i. i < n \<Longrightarrow> (\<And>k. k < i \<Longrightarrow> P k) \<Longrightarrow> P i) \<Longrightarrow> (\<And>i. i < n \<Longrightarrow> P i)"
    by (metis dual_order.strict_trans infinite_descent0 linorder_neqE_nat)
  show "n = 0 \<Longrightarrow> ?thesis" using dim unfolding diagonal_mat_def by auto
  show "n > 0 \<Longrightarrow> ?thesis" unfolding diagonal_mat_def dim
    apply (rule allI, rule impI)
    apply (rule nat_induct_strong)
  proof (rule allI, rule impI, rule impI)
    assume asm: "n > 0"
    from tri upper_triangularD[of A 0 j] dim have z0: "\<And>j. 0< j \<Longrightarrow> j < n \<Longrightarrow> A$$(j, 0) = 0" 
      by auto
    then have ada00: "(adjoint A * A)$$(0,0) = conjugate (A$$(0,0)) * A$$(0,0)"
      using asm dim by (auto simp add: scalar_prod_def adjoint_eval sum.atLeast_Suc_lessThan)
    have aad00: "(A * adjoint A)$$(0,0) = (\<Sum>k=0..<n. A$$(0, k) * conjugate (A$$(0, k)))"
      using asm dim by (auto simp add: scalar_prod_def adjoint_eval)
    moreover have 
      "\<dots> = A$$(0,0) * conjugate (A$$(0,0))
          + (\<Sum>k=1..<n. A$$(0, k) * conjugate (A$$(0, k)))"
      using dim asm by (subst sum.atLeast_Suc_lessThan[of 0 n "\<lambda>k. A$$(0, k) * conjugate (A$$(0, k))"], auto)
    ultimately have f1tneq0: "(\<Sum>k=(Suc 0)..<n. A$$(0, k) * conjugate (A$$(0, k))) = 0"
      using eq0 ada00 by (simp)
    have geq0: "\<And>k. k < n \<Longrightarrow> A$$(0, k) * conjugate (A$$(0, k)) \<ge> 0"  
      using conjugate_square_positive by auto
    have "\<And>k. 1 \<le> k \<Longrightarrow> k < n \<Longrightarrow> A$$(0, k) * conjugate (A$$(0, k)) = 0"
      by (rule sum_nonneg_0[of "{1..<n}"], auto, rule geq0, auto, rule f1tneq0)
    with dim asm show 
      case0: "\<And>j. 0 < n \<Longrightarrow> j < n \<Longrightarrow> 0 \<noteq> j \<Longrightarrow> A $$ (0, j) = 0"
      by auto
    {
      fix i
      assume asm: "n > 0" "i < n" "i > 0"
        and ih: "\<And>k. k < i \<Longrightarrow> \<forall>j<n. k \<noteq> j \<longrightarrow> A $$ (k, j) = 0"
      then have "\<And>j. j<n \<Longrightarrow> i \<noteq> j \<Longrightarrow> A $$ (i, j) = 0"
      proof -
        have inter_part: "\<And>b m e. (b::nat) < e \<Longrightarrow> b < m \<Longrightarrow> m < e \<Longrightarrow> {b..<m} \<union> {m..<e} = {b..<e}" by auto
        then have  
          "\<And>b m e f. (b::nat) < e \<Longrightarrow> b < m \<Longrightarrow> m < e 
            \<Longrightarrow> (\<Sum>k=b..<e. f k) = (\<Sum>k\<in>{b..<m}\<union>{m..<e}. f k)"
          using sum.union_disjoint by auto
        then have sum_part:
          "\<And>b m e f. (b::nat) < e \<Longrightarrow> b < m \<Longrightarrow> m < e 
                      \<Longrightarrow> (\<Sum>k=b..<e. f k) = (\<Sum>k=b..<m. f k) + (\<Sum>k=m..<e. f k)"
          by (auto simp add: sum.union_disjoint)
        from tri upper_triangularD[of A j i] asm dim have 
            zsi0: "\<And>j. j < i \<Longrightarrow> A$$(i, j) = 0" by auto
        from tri upper_triangularD[of A j i] asm dim have 
            zsi1: "\<And>k. i < k \<Longrightarrow> k < n \<Longrightarrow> A$$(k, i) = 0" by auto
        have 
          "(A * adjoint A)$$(i, i) 
          = (\<Sum>k=0..<n. conjugate (A$$(i, k)) * A$$(i, k))" using asm dim
          apply (auto simp add: scalar_prod_def adjoint_eval)
          apply (rule sum.cong, auto)
          done
        also have
          "\<dots> = (\<Sum>k=0..<i. conjugate (A$$(i, k)) * A$$(i, k))
              + (\<Sum>k=i..<n. conjugate (A$$(i, k)) * A$$(i, k))"
          using asm
          by (auto simp add: sum_part[of 0 n i])
        also have
          "\<dots> = (\<Sum>k=i..<n. conjugate (A$$(i, k)) * A$$(i, k))"
          using zsi0
          by auto
        also have
          "\<dots> = conjugate (A$$(i, i)) * A$$(i, i) 
            + (\<Sum>k=(Suc i)..<n. conjugate (A$$(i, k)) * A$$(i, k))"
          using asm
          by (auto simp add: sum.atLeast_Suc_lessThan)
        finally have
          adaii: "(A * adjoint A)$$(i, i) 
            = conjugate (A$$(i, i)) * A$$(i, i) 
            + (\<Sum>k=(Suc i)..<n. conjugate (A$$(i, k)) * A$$(i, k))" .
        have 
          "(adjoint A * A)$$(i, i) = (\<Sum>k=0..<n. conjugate (A$$(k, i)) * A$$(k, i))"
          using asm dim by (auto simp add: scalar_prod_def adjoint_eval)
        also have
          "\<dots> = (\<Sum>k=0..<i. conjugate (A$$(k, i)) * A$$(k, i))
              + (\<Sum>k=i..<n. conjugate (A$$(k, i)) * A$$(k, i))"
          using asm by (auto simp add: sum_part[of 0 n i])
        also have 
            "\<dots> = (\<Sum>k=i..<n. conjugate (A$$(k, i)) * A$$(k, i))"
          using asm ih by auto
        also have
            "\<dots> = conjugate (A$$(i, i)) * A$$(i, i)"
          using asm zsi1 by (auto simp add: sum.atLeast_Suc_lessThan)
        finally have "(adjoint A * A)$$(i, i) = conjugate (A$$(i, i)) * A$$(i, i)" .
        with adaii eq0 have 
          fsitoneq0: "(\<Sum>k=(Suc i)..<n. conjugate (A$$(i, k)) * A$$(i, k)) = 0" by auto
        have "\<And>k. k<n \<Longrightarrow> i < k \<Longrightarrow> conjugate (A$$(i, k)) * A$$(i, k) = 0"
          by (rule sum_nonneg_0[of "{(Suc i)..<n}"], auto, subst mult.commute, 
              rule conjugate_square_positive, rule fsitoneq0)
        then have "\<And>k. k<n  \<Longrightarrow> i<k \<Longrightarrow> A $$ (i, k) = 0" by auto
        with zsi0 show "\<And>j. j<n \<Longrightarrow> i \<noteq> j \<Longrightarrow> A $$ (i, j) = 0" 
          by (metis linorder_neqE_nat)
      qed
    }
    with case0 show "\<And>i ia.
       0 < n \<Longrightarrow>
       i < n \<Longrightarrow>
       ia < n \<Longrightarrow>
       (\<And>k. k < ia \<Longrightarrow> \<forall>j<n. k \<noteq> j \<longrightarrow> A $$ (k, j) = 0) \<Longrightarrow>
       \<forall>j<n. ia \<noteq> j \<longrightarrow> A $$ (ia, j) = 0" by auto
  qed
qed

lemma normal_complex_mat_has_spectral_decomposition:
  assumes A: "(A::complex mat) \<in> carrier_mat n n"
    and normal: "A * adjoint A  = adjoint A * A"
    and c: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> es. [:- e, 1:])"
    and B: "unitary_schur_decomposition A es = (B,P,Q)"
  shows "similar_mat_wit A B P (adjoint P) \<and> diagonal_mat B \<and> diag_mat B = es \<and> unitary P"
proof -
  have smw: "similar_mat_wit A B P (adjoint P)" 
    and ut: "upper_triangular B"
    and uP: "unitary P" 
    and dB: "diag_mat B = es"
    and "(Q = adjoint P)"
    using assms by (auto simp add: unitary_schur_decomposition)
  from smw have dimP: "P \<in> carrier_mat n n" and dimB: "B \<in> carrier_mat n n" 
    and dimaP: "adjoint P \<in> carrier_mat n n"
    unfolding similar_mat_wit_def using A by auto
  have dimaB: "adjoint B \<in> carrier_mat n n" using dimB by auto
  note dims = dimP dimB dimaP dimaB

  have "inverts_mat P (adjoint P)" using unitary_def uP dims by auto
  then have iaPP: "inverts_mat (adjoint P) P" using inverts_mat_symm using dims by auto
  have aPP: "adjoint P * P = 1\<^sub>m n" using dims iaPP unfolding inverts_mat_def by auto
  from smw have A: "A = P * B * (adjoint P)" unfolding similar_mat_wit_def Let_def by auto
  then have aA: "adjoint A = P * adjoint B * adjoint P" 
    by (insert A dimP dimB dimaP, auto simp add: adjoint_mult[of _ n n _ n] adjoint_adjoint)
  have "A * adjoint A = (P * B * adjoint P) * (P * adjoint B * adjoint P)" using A aA by auto
  also have "\<dots> = P * B * (adjoint P * P) * (adjoint B * adjoint P)" using dims by (mat_assoc n)
  also have "\<dots> = P * B * 1\<^sub>m n * (adjoint B * adjoint P)" using dims aPP by (auto)
  also have "\<dots> = P * B * adjoint B * adjoint P" using dims by (mat_assoc n)
  finally have "A * adjoint A = P * B * adjoint B * adjoint P".
  then have "adjoint P * (A * adjoint A) * P = (adjoint P * P) * B * adjoint B * (adjoint P * P)"
    using dims by (simp add: assoc_mult_mat[of _ n n _ n _ n])
  also have "\<dots> = 1\<^sub>m n * B * adjoint B * 1\<^sub>m n" using aPP by auto
  also have "\<dots> = B * adjoint B" using dims by auto
  finally have eq0: "adjoint P * (A * adjoint A) * P = B * adjoint B".

  have "adjoint A * A = (P * adjoint B * adjoint P) * (P * B * adjoint P)" using A aA by auto
  also have "\<dots> = P * adjoint B * (adjoint P * P) * (B * adjoint P)" using dims by (mat_assoc n)
  also have "\<dots> = P * adjoint B * 1\<^sub>m n * (B * adjoint P)" using dims aPP by (auto)
  also have "\<dots> = P * adjoint B * B * adjoint P" using dims by (mat_assoc n)  
  finally have "adjoint A * A = P * adjoint B * B * adjoint P" by auto
  then have "adjoint P * (adjoint A * A) * P = (adjoint P * P) * adjoint B * B * (adjoint P * P)"
    using dims by (simp add: assoc_mult_mat[of _ n n _ n _ n])
  also have "\<dots> = 1\<^sub>m n * adjoint B * B * 1\<^sub>m n" using aPP by auto
  also have "\<dots> = adjoint B * B" using dims by auto
  finally have eq1: "adjoint P * (adjoint A * A) * P = adjoint B * B".

  from normal have "adjoint P * (adjoint A * A) * P = adjoint P * (A * adjoint A) * P" by auto
  with eq0 eq1 have "B * adjoint B = adjoint B * B" by auto
  with ut dims have "diagonal_mat B" using normal_upper_triangular_matrix_is_diagonal by auto
  with smw uP dB show "similar_mat_wit A B P (adjoint P) \<and> diagonal_mat B \<and> diag_mat B = es \<and> unitary P" by auto
qed

lemma complex_mat_has_jordan_nf:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  shows "\<exists>n_as. jordan_nf A n_as"
proof -
  have "\<exists>as. char_poly A =  (\<Prod> a \<leftarrow> as. [:- a, 1:]) \<and> length as = n" 
    using assms by (simp add: complex_mat_char_poly_factorizable)
  then show ?thesis using assms
    by (auto simp add: jordan_nf_iff_linear_factorization)
qed

lemma hermitian_is_normal:
  assumes "hermitian A"
  shows "A * adjoint A = adjoint A * A"
  using assms by (auto simp add: hermitian_def)

lemma hermitian_eigenvalue_real:
  assumes dim: "(A::complex mat) \<in> carrier_mat n n"
    and hA: "hermitian A"
    and c: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> es. [:- e, 1:])"
    and B: "unitary_schur_decomposition A es = (B,P,Q)"
  shows "similar_mat_wit A B P (adjoint P) \<and> diagonal_mat B \<and> diag_mat B = es 
    \<and> unitary P \<and> (\<forall>i < n. B$$(i, i) \<in> Reals)"
proof -
  have normal: "A * adjoint A = adjoint A * A" using hA hermitian_is_normal by auto
  then have schur: "similar_mat_wit A B P (adjoint P) \<and> diagonal_mat B \<and> diag_mat B = es \<and> unitary P"
    using normal_complex_mat_has_spectral_decomposition[OF dim normal c B] by (simp)
  then have "similar_mat_wit A B P (adjoint P)" 
    and uP: "unitary P" and dB: "diag_mat B = es"
    using assms by auto
  then have A: "A = P * B * (adjoint P)" 
    and dimB: "B \<in> carrier_mat n n" and dimP: "P \<in> carrier_mat n n"
    unfolding similar_mat_wit_def Let_def using dim by auto
  then have dimaB: "adjoint B \<in> carrier_mat n n" by auto
  have "adjoint A = adjoint (adjoint P) * adjoint (P * B)" 
    apply (subst A)
    apply (subst adjoint_mult[of "P * B" n n "adjoint P" n])
      apply (insert dimB dimP, auto)
    done
  also have "\<dots> = P * adjoint (P * B)" by (auto simp add: adjoint_adjoint)
  also have "\<dots> = P * (adjoint B * adjoint P)" using dimB dimP by (auto simp add: adjoint_mult)
  also have "\<dots> = P * adjoint B * adjoint P" using dimB dimP by (subst assoc_mult_mat[symmetric, of P n n "adjoint B" n "adjoint P" n], auto)
  finally have aA: "adjoint A = P * adjoint B * adjoint P" .
  have "A = adjoint A" using hA hermitian_def[of A] by auto
  then have "P * B * adjoint P = P * adjoint B * adjoint P" using A aA by auto
  then have BaB: "B = adjoint B" using unitary_elim[OF dimB dimaB dimP] uP by auto
  {
    fix i 
    assume "i < n"
    then have "B$$(i, i) = conjugate (B$$(i, i))" 
      apply (subst BaB)
      by (insert dimB, simp add: adjoint_eval)
    then have "B$$(i, i) \<in> Reals" unfolding conjugate_complex_def 
      using Reals_cnj_iff by auto
  }
  then have "\<forall>i<n. B$$(i, i) \<in> Reals" by auto
  with schur show ?thesis by auto
qed

lemma hermitian_inner_prod_real:
  assumes dimA: "(A::complex mat) \<in> carrier_mat n n"
    and dimv: "v \<in> carrier_vec n"
    and hA: "hermitian A"
  shows "inner_prod v (A *\<^sub>v v) \<in> Reals"
proof -
  obtain es where es: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> es. [:- e, 1:])" 
    using complex_mat_char_poly_factorizable dimA by auto
  obtain B P Q where "unitary_schur_decomposition A es = (B,P,Q)" 
    by (cases "unitary_schur_decomposition A es", auto)
  then have "similar_mat_wit A B P (adjoint P) \<and> diagonal_mat B \<and> diag_mat B = es 
    \<and> unitary P \<and> (\<forall>i < n. B$$(i, i) \<in> Reals)"
    using hermitian_eigenvalue_real dimA es hA by auto
  then have A: "A = P * B * (adjoint P)" and dB: "diagonal_mat B"
    and Bii: "\<And>i. i < n \<Longrightarrow> B$$(i, i) \<in> Reals"
    and dimB: "B \<in> carrier_mat n n" and dimP: "P \<in> carrier_mat n n" and dimaP: "adjoint P \<in> carrier_mat n n"
    unfolding similar_mat_wit_def Let_def using dimA by auto
  define w where "w = (adjoint P) *\<^sub>v v"
  then have dimw: "w \<in> carrier_vec n" using dimaP dimv by auto
  from A have "inner_prod v (A *\<^sub>v v) = inner_prod v ((P * B * (adjoint P)) *\<^sub>v v)" by auto
  also have "\<dots> = inner_prod v ((P * B) *\<^sub>v ((adjoint P) *\<^sub>v v))" using dimP dimB dimv
    by (subst assoc_mult_mat_vec[of _ n n "adjoint P" n], auto)
  also have "\<dots> = inner_prod v (P *\<^sub>v (B *\<^sub>v ((adjoint P) *\<^sub>v v)))" using dimP dimB dimv dimaP
    by (subst assoc_mult_mat_vec[of _ n n "B" n], auto)
  also have "\<dots> = inner_prod w (B *\<^sub>v w)" unfolding w_def 
    apply (rule adjoint_def_alter[OF _ _ dimP])
     apply (insert mult_mat_vec_carrier[OF dimB mult_mat_vec_carrier[OF dimaP dimv]], auto simp add: dimv)
    done

  also have "\<dots> = (\<Sum>i=0..<n. (\<Sum>j=0..<n.
                conjugate (w$i) * B$$(i, j) * w$j))" unfolding scalar_prod_def using dimw dimB
    apply (simp add: scalar_prod_def sum_distrib_right)
    apply (rule sum.cong, auto, rule sum.cong, auto)
    done
  also have "\<dots> = (\<Sum>i=0..<n. B$$(i, i) *  conjugate (w$i) * w$i)" 
    apply (rule sum.cong, auto)
    apply (simp add: sum.remove)
    apply (insert dB[unfolded diagonal_mat_def] dimB, auto)
    done
  finally have sum: "inner_prod v (A *\<^sub>v v) = (\<Sum>i=0..<n. B$$(i, i) *  conjugate (w$i) * w$i)" .
  have "\<And>i. i < n \<Longrightarrow> B$$(i, i) *  conjugate (w$i) * w$i \<in> Reals" using Bii by (simp add: Reals_cnj_iff)
  then have "(\<Sum>i=0..<n. B$$(i, i) *  conjugate (w$i) * w$i) \<in> Reals" by auto
  then show ?thesis using sum by auto
qed

lemma unit_vec_bracket:
  fixes A :: "complex mat"
  assumes dimA: "A \<in> carrier_mat n n" and i: "i < n"
  shows "inner_prod (unit_vec n i) (A *\<^sub>v (unit_vec n i)) = A$$(i, i)"
proof -
  define w where "(w::complex vec) = unit_vec n i"
  have "A *\<^sub>v w = col A i" using i dimA w_def by auto
  then have 1: "inner_prod w (A *\<^sub>v w) = inner_prod w (col A i)" using w_def by auto
  have "conjugate w = w" unfolding w_def unit_vec_def conjugate_vec_def using i by auto
  then have 2: "inner_prod w (col A i) = A$$(i, i)" using i dimA w_def by auto
  from 1 2 show "inner_prod w (A *\<^sub>v w) = A$$(i, i)" by auto
qed

lemma spectral_decomposition_extract_diag:
  fixes P B :: "complex mat"
  assumes dimP: "P \<in> carrier_mat n n" and dimB: "B \<in> carrier_mat n n"
    and uP: "unitary P" and dB: "diagonal_mat B" and i: "i < n"
  shows "inner_prod (col P i) (P * B * (adjoint P) *\<^sub>v (col P i)) = B$$(i, i)"
proof -
  have dimaP: "adjoint P\<in> carrier_mat n n" using dimP by auto
  have uaP: "unitary (adjoint P)" using unitary_adjoint uP dimP by auto
  then have "inverts_mat (adjoint P) P" by (simp add: unitary_def adjoint_adjoint)
  then have iv: "(adjoint P) * P = 1\<^sub>m n" using dimaP inverts_mat_def by auto
  define v where "v = col P i"
  then have dimv: "v \<in> carrier_vec n" using dimP by auto
  define w where "(w::complex vec) = unit_vec n i"
  then have dimw: "w \<in> carrier_vec n" by auto
  have BaPv: "B *\<^sub>v (adjoint P *\<^sub>v v) \<in> carrier_vec n" using dimB dimaP dimv by auto
  have "(adjoint P) *\<^sub>v v = (col (adjoint P * P) i)" 
    by (simp add: col_mult2[OF dimaP dimP i, symmetric] v_def)
  then have aPv: "(adjoint P) *\<^sub>v v = w"
    by (auto simp add: iv i w_def)
  have "inner_prod v (P * B * (adjoint P) *\<^sub>v v) = inner_prod v ((P * B) *\<^sub>v ((adjoint P) *\<^sub>v v))" using dimP dimB dimv
    by (subst assoc_mult_mat_vec[of _ n n "adjoint P" n], auto)
  also have "\<dots> = inner_prod v (P *\<^sub>v (B *\<^sub>v ((adjoint P) *\<^sub>v v)))" using dimP dimB dimv dimaP
    by (subst assoc_mult_mat_vec[of _ n n "B" n], auto)
  also have "\<dots> = inner_prod (adjoint P *\<^sub>v v) (B *\<^sub>v (adjoint P *\<^sub>v v))" 
    by (simp add: adjoint_def_alter[OF dimv BaPv dimP])
  also have "\<dots> = inner_prod w (B *\<^sub>v w)" using aPv by auto
  also have "\<dots> = B$$(i, i)" using w_def unit_vec_bracket dimB i by auto
  finally show "inner_prod v (P * B * (adjoint P) *\<^sub>v v) = B$$(i, i)".
qed

lemma hermitian_inner_prod_zero:
  fixes A :: "complex mat"
  assumes dimA: "A \<in> carrier_mat n n" and hA: "hermitian A"
    and zero: "\<forall>v\<in>carrier_vec n. inner_prod v (A *\<^sub>v v) = 0"
  shows "A = 0\<^sub>m n n"
proof -
  obtain es where es: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> es. [:- e, 1:])" 
    using complex_mat_char_poly_factorizable dimA by auto
  obtain B P Q where "unitary_schur_decomposition A es = (B,P,Q)" 
    by (cases "unitary_schur_decomposition A es", auto)
  then have "similar_mat_wit A B P (adjoint P) \<and> diagonal_mat B \<and> diag_mat B = es 
    \<and> unitary P \<and> (\<forall>i < n. B$$(i, i) \<in> Reals)"
    using hermitian_eigenvalue_real dimA es hA by auto
  then have A: "A = P * B * (adjoint P)" and dB: "diagonal_mat B"
    and Bii: "\<And>i. i < n \<Longrightarrow> B$$(i, i) \<in> Reals"
    and dimB: "B \<in> carrier_mat n n" and dimP: "P \<in> carrier_mat n n" and dimaP: "adjoint P \<in> carrier_mat n n"
    and uP: "unitary P"
    unfolding similar_mat_wit_def Let_def unitary_def using dimA by auto
  then have uaP: "unitary (adjoint P)" using unitary_adjoint by auto
  then have "inverts_mat (adjoint P) P" by (simp add: unitary_def adjoint_adjoint)
  then have iv: "adjoint P * P = 1\<^sub>m n" using dimaP inverts_mat_def by auto
  have "B = 0\<^sub>m n n"
  proof-
    {
      fix i assume i: "i < n"
      define v where "v = col P i"
      then have dimv: "v \<in> carrier_vec n" using v_def dimP by auto
      have "inner_prod v (A *\<^sub>v v) = B$$(i, i)" unfolding A v_def
        using spectral_decomposition_extract_diag[OF dimP dimB uP dB i]  by auto
      moreover have "inner_prod v (A *\<^sub>v v) = 0" using dimv zero by auto
      ultimately have "B$$(i, i) = 0" by auto
    }
    note zB = this
    show "B = 0\<^sub>m n n" by (insert zB dB dimB, rule eq_matI, auto simp add: diagonal_mat_def)
  qed
  then show "A = 0\<^sub>m n n" using A dimB dimP dimaP by auto
qed

lemma complex_mat_decomposition_to_hermitian:
  fixes A :: "complex mat"
  assumes dim: "A \<in> carrier_mat n n"
  shows "\<exists>B C. hermitian B \<and> hermitian C \<and> A = B + \<i> \<cdot>\<^sub>m C \<and> B \<in> carrier_mat n n \<and> C \<in> carrier_mat n n"
proof -
  obtain B C where B: "B = (1 / 2) \<cdot>\<^sub>m (A + adjoint A)" 
    and C: "C = (-\<i> / 2) \<cdot>\<^sub>m (A - adjoint A)" by auto
  then have dimB: "B \<in> carrier_mat n n" and dimC: "C \<in> carrier_mat n n" using dim by auto
  have "hermitian B" unfolding B hermitian_def using dim
    by (auto simp add: adjoint_eval)
  moreover have "hermitian C" unfolding C hermitian_def using dim
    apply (subst eq_matI)
       apply (auto simp add: adjoint_eval algebra_simps)
    done
  moreover have "A = B + \<i> \<cdot>\<^sub>m C" using dim B C 
    apply (subst eq_matI)
       apply (auto simp add: adjoint_eval algebra_simps)
    done
  ultimately show ?thesis using dimB dimC by auto
qed

subsection \<open>Outer product\<close>

definition outer_prod :: "'a::conjugatable_field vec \<Rightarrow> 'a vec \<Rightarrow> 'a mat" where
  "outer_prod v w = mat (dim_vec v) 1 (\<lambda>(i, j). v $ i) * mat 1 (dim_vec w) (\<lambda>(i, j). (conjugate w) $ j)"

lemma outer_prod_dim[simp]:
  fixes v w :: "'a::conjugatable_field vec"
  assumes v: "v \<in> carrier_vec n" and w: "w \<in> carrier_vec m"
  shows "outer_prod v w \<in> carrier_mat n m"
  unfolding outer_prod_def using assms mat_of_cols_carrier mat_of_rows_carrier by auto

lemma mat_of_vec_mult_eq_scalar_prod:
  fixes v w :: "'a::conjugatable_field vec"
  assumes "v \<in> carrier_vec n" and "w \<in> carrier_vec n"
  shows "mat 1 (dim_vec v) (\<lambda>(i, j). (conjugate v) $ j) * mat (dim_vec w) 1 (\<lambda>(i, j). w $ i) 
    = mat 1 1 (\<lambda>k. inner_prod v w)"
  apply (rule eq_matI) using assms apply (simp add: scalar_prod_def) apply (rule sum.cong) by auto

lemma one_dim_mat_mult_is_scale:
  fixes A B :: "('a::conjugatable_field mat)"
  assumes "B \<in> carrier_mat 1 n"
  shows "(mat 1 1 (\<lambda>k. a)) * B = a \<cdot>\<^sub>m B"
  apply (rule eq_matI) using assms by (auto simp add: scalar_prod_def)

lemma outer_prod_mult_outer_prod:
  fixes a b c d :: "'a::conjugatable_field vec"
  assumes a: "a \<in> carrier_vec d1" and b: "b \<in> carrier_vec d2"
    and c: "c \<in> carrier_vec d2" and d: "d \<in> carrier_vec d3"
  shows "outer_prod a b * outer_prod c d = inner_prod b c \<cdot>\<^sub>m outer_prod a d"
proof -
  let ?ma = "mat (dim_vec a) 1 (\<lambda>(i, j). a $ i)"
  let ?mb = "mat 1 (dim_vec b) (\<lambda>(i, j). (conjugate b) $ j)"
  let ?mc = "mat (dim_vec c) 1 (\<lambda>(i, j). c $ i)"
  let ?md = "mat 1 (dim_vec d) (\<lambda>(i, j). (conjugate d) $ j)"
  have "(?ma * ?mb) * (?mc * ?md) = ?ma * (?mb * (?mc * ?md))"
    apply (subst assoc_mult_mat[of "?ma" d1 1 "?mb" d2 "?mc * ?md" d3] )
    using assms by auto
  also have "\<dots> = ?ma * ((?mb * ?mc) * ?md)"
    apply (subst assoc_mult_mat[symmetric, of "?mb" 1 d2 "?mc" 1 "?md" d3])
    using assms by auto
  also have "\<dots> = ?ma * ((mat 1 1 (\<lambda>k. inner_prod b c)) * ?md)"
    apply (subst mat_of_vec_mult_eq_scalar_prod[of b d2 c]) using assms by auto
  also have "\<dots> = ?ma * (inner_prod b c \<cdot>\<^sub>m ?md)" 
    apply (subst one_dim_mat_mult_is_scale) using assms by auto
  also have "\<dots> = (inner_prod b c) \<cdot>\<^sub>m (?ma * ?md)" using assms by auto
  finally show ?thesis unfolding outer_prod_def by auto
qed

lemma index_outer_prod:
  fixes v w :: "'a::conjugatable_field vec"
  assumes v: "v \<in> carrier_vec n" and w: "w \<in> carrier_vec m"
    and ij: "i < n" "j < m"
  shows "(outer_prod v w)$$(i, j) = v $ i * conjugate (w $ j)"
  unfolding outer_prod_def using assms by (simp add: scalar_prod_def)

lemma mat_of_vec_mult_vec:
  fixes a b c :: "'a::conjugatable_field vec"
  assumes a: "a \<in> carrier_vec d" and b: "b \<in> carrier_vec d"
  shows "mat 1 d (\<lambda>(i, j). (conjugate a) $ j) *\<^sub>v b = vec 1 (\<lambda>k. inner_prod a b)"
  apply (rule eq_vecI) 
   apply (simp add: scalar_prod_def carrier_vecD[OF a] carrier_vecD[OF b])
  apply (rule sum.cong) by auto

lemma mat_of_vec_mult_one_dim_vec:
  fixes a b :: "'a::conjugatable_field vec"
  assumes a: "a \<in> carrier_vec d" 
  shows "mat d 1 (\<lambda>(i, j). a $ i) *\<^sub>v vec 1 (\<lambda>k. c) = c \<cdot>\<^sub>v a"
  apply (rule eq_vecI)
  by (auto simp add: scalar_prod_def carrier_vecD[OF a])

lemma outer_prod_mult_vec:
  fixes a b c :: "'a::conjugatable_field vec"
  assumes a: "a \<in> carrier_vec d1" and b: "b \<in> carrier_vec d2"
    and c: "c \<in> carrier_vec d2"
  shows "outer_prod a b *\<^sub>v c = inner_prod b c \<cdot>\<^sub>v a"
proof -
  have "outer_prod a b *\<^sub>v c 
    = mat d1 1 (\<lambda>(i, j). a $ i) 
    * mat 1 d2 (\<lambda>(i, j). (conjugate b) $ j)
    *\<^sub>v c" unfolding outer_prod_def using assms by auto
  also have "\<dots> = mat d1 1 (\<lambda>(i, j). a $ i) 
    *\<^sub>v (mat 1 d2 (\<lambda>(i, j). (conjugate b) $ j)
    *\<^sub>v c)" apply (subst assoc_mult_mat_vec) using assms by auto
  also have "\<dots> = mat d1 1 (\<lambda>(i, j). a $ i) 
    *\<^sub>v vec 1 (\<lambda>k. inner_prod b c)" using mat_of_vec_mult_vec[of b] assms by auto
  also have "\<dots> = inner_prod b c \<cdot>\<^sub>v a" using mat_of_vec_mult_one_dim_vec assms by auto
  finally show ?thesis by auto
qed

lemma trace_outer_prod_right:
  fixes A :: "'a::conjugatable_field mat" and v w :: "'a vec"
  assumes A: "A \<in> carrier_mat n n"
    and v: "v \<in> carrier_vec n" and w: "w \<in> carrier_vec n"
  shows "trace (A * outer_prod v w) = inner_prod w (A *\<^sub>v v)" (is "?lhs = ?rhs")
proof -
  define B where "B = outer_prod v w"
  then have B: "B \<in> carrier_mat n n" using assms by auto
  have "trace(A * B) = (\<Sum>i = 0..<n. \<Sum>j = 0..<n. A $$ (i,j) * B $$ (j,i))"
    unfolding trace_def using A B by (simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>i = 0..<n. \<Sum>j = 0..<n. A $$ (i,j) * v $ j * conjugate (w $ i))"
    unfolding B_def
    apply (rule sum.cong, simp, rule sum.cong, simp)
    by (insert v w, auto simp add: index_outer_prod)
  finally have "?lhs = (\<Sum>i = 0..<n. \<Sum>j = 0..<n. A $$ (i,j) * v $ j * conjugate (w $ i))" using B_def by auto
  moreover have "?rhs = (\<Sum>i = 0..<n. \<Sum>j = 0..<n. A $$ (i,j) * v $ j * conjugate (w $ i))" using A v w
    by (simp add: scalar_prod_def sum_distrib_right)
  ultimately show ?thesis by auto
qed

lemma trace_outer_prod:
  fixes v w :: "('a::conjugatable_field vec)"
  assumes v: "v \<in> carrier_vec n" and w: "w \<in> carrier_vec n"
  shows "trace (outer_prod v w) = inner_prod w v" (is "?lhs = ?rhs")
proof -
  have "(1\<^sub>m n) * (outer_prod v w) = outer_prod v w" apply (subst left_mult_one_mat) using outer_prod_dim assms by auto
  moreover have "1\<^sub>m n *\<^sub>v v = v" using assms by auto
  ultimately show ?thesis using trace_outer_prod_right[of "1\<^sub>m n" n v w] assms by auto
qed

lemma inner_prod_outer_prod:
  fixes a b c d :: "'a::conjugatable_field vec"
  assumes a: "a \<in> carrier_vec n" and b: "b \<in> carrier_vec n"
    and c: "c \<in> carrier_vec m" and d: "d \<in> carrier_vec m"
  shows "inner_prod a (outer_prod b c *\<^sub>v d) = inner_prod a b * inner_prod c d" (is "?lhs = ?rhs")
proof -
  define P where "P = outer_prod b c"
  then have dimP: "P \<in> carrier_mat n m" using assms by auto
  have "inner_prod a (P *\<^sub>v d) = (\<Sum>i=0..<n. (\<Sum>j=0..<m. conjugate (a$i) * P$$(i, j) * d$j))" using assms dimP
    apply (simp add: scalar_prod_def sum_distrib_right)
    apply (rule sum.cong, auto)
    apply (rule sum.cong, auto)
    done
  also have "\<dots> = (\<Sum>i=0..<n. (\<Sum>j=0..<m. conjugate (a$i) * b$i * conjugate(c$j) * d$j))"
    using P_def b c by(simp add: index_outer_prod algebra_simps)
  finally have eq: "?lhs = (\<Sum>i=0..<n. (\<Sum>j=0..<m. conjugate (a$i) * b$i * conjugate(c$j) * d$j))" using P_def by auto

  have "?rhs = (\<Sum>i=0..<n. conjugate (a$i) * b$i) * (\<Sum>j=0..<m. conjugate(c$j) * d$j)" using assms 
    by (auto simp add: scalar_prod_def algebra_simps)
  also have "\<dots> = (\<Sum>i=0..<n. (\<Sum>j=0..<m. conjugate (a$i) * b$i * conjugate(c$j) * d$j))"
    using assms by (simp add: sum_product algebra_simps)
  finally show "?lhs = ?rhs" using eq by auto
qed

subsection \<open>Semi-definite matrices\<close>

definition positive :: "complex mat \<Rightarrow> bool" where
  "positive A \<longleftrightarrow>
     A \<in> carrier_mat (dim_col A) (dim_col A) \<and>
     (\<forall>v. dim_vec v = dim_col A \<longrightarrow> inner_prod v (A *\<^sub>v v) \<ge> 0)"

lemma positive_iff_normalized_vec:
  "positive A \<longleftrightarrow>
    A \<in> carrier_mat (dim_col A) (dim_col A) \<and>
    (\<forall>v. (dim_vec v = dim_col A \<and> vec_norm v = 1) \<longrightarrow> inner_prod v (A *\<^sub>v v) \<ge> 0)"
proof (rule)
  assume "positive A"
  then show "A \<in> carrier_mat (dim_col A) (dim_col A) \<and> 
    (\<forall>v. dim_vec v = dim_col A \<and> vec_norm v = 1 \<longrightarrow> 0 \<le> inner_prod v (A *\<^sub>v v))"
    unfolding positive_def by auto
next
  define n where "n = dim_col A"
  assume "A \<in> carrier_mat (dim_col A) (dim_col A) \<and> (\<forall>v. dim_vec v = dim_col A \<and> vec_norm v = 1 \<longrightarrow> 0 \<le> inner_prod v (A *\<^sub>v v))"
  then have A: "A \<in> carrier_mat (dim_col A) (dim_col A)" and geq0: "\<forall>v. dim_vec v = dim_col A \<and> vec_norm v = 1 \<longrightarrow> 0 \<le> inner_prod v (A *\<^sub>v v)" by auto
  then have dimA: "A \<in> carrier_mat n n" using n_def[symmetric] by auto
  {
    fix v assume dimv: "(v::complex vec) \<in> carrier_vec n"
    have "0 \<le> inner_prod v (A *\<^sub>v v)"
    proof (cases "v = 0\<^sub>v n")
      case True
      then show "0 \<le> inner_prod v (A *\<^sub>v v)" using dimA by auto
    next
      case False
      then have 1: "vec_norm v > 0" using vec_norm_ge_0 dimv by auto
      then have cnv: "cnj (vec_norm v) = vec_norm v" using Reals_cnj_iff complex_is_Real_iff by auto
      define w where "w = vec_normalize v"
      then have dimw: "w \<in> carrier_vec n" using dimv by auto
      have nvw: "v = vec_norm v \<cdot>\<^sub>v w" using w_def vec_eq_norm_smult_normalized by auto
      have "vec_norm w = 1" using normalized_vec_norm[OF dimv False] vec_norm_def w_def by auto
      then have 2: "0 \<le> inner_prod w (A *\<^sub>v w)" using geq0 dimw dimA by auto
      have "inner_prod v (A *\<^sub>v v) = vec_norm v * vec_norm v * inner_prod w (A *\<^sub>v w)" using dimA dimv dimw
        apply (subst (1 2) nvw)
        apply (subst mult_mat_vec, simp, simp)
        apply (subst scalar_prod_smult_left[of "(A *\<^sub>v w)" "conjugate (vec_norm v \<cdot>\<^sub>v w)" "vec_norm v"], simp)
        apply (simp add: conjugate_smult_vec cnv)
        done
      also have "\<dots> \<ge> 0" using 1 2 by auto
      finally show "0 \<le> inner_prod v (A *\<^sub>v v)" by auto
    qed
  }
  then have geq: "\<forall>v. dim_vec v = dim_col A \<longrightarrow> 0 \<le> inner_prod v (A *\<^sub>v v)" using dimA by auto
  show "positive A" unfolding positive_def 
    by (rule, simp add: A, rule geq)
qed

lemma positive_is_hermitian:
  fixes A :: "complex mat"
  assumes pA: "positive A"
  shows "hermitian A"
proof -
  define n where "n = dim_col A"
  then have dimA: "A \<in> carrier_mat n n" using positive_def pA by auto
  obtain B C where B: "hermitian B" and C: "hermitian C" and A: "A = B + \<i> \<cdot>\<^sub>m C"
    and dimB: "B \<in> carrier_mat n n" and dimC: "C \<in> carrier_mat n n" and dimiC: "\<i> \<cdot>\<^sub>m C \<in> carrier_mat n n"
    using complex_mat_decomposition_to_hermitian[OF dimA] by auto
  {
    fix v :: "complex vec" assume dimv: "v \<in> carrier_vec n"
    have dimvA: "dim_vec v = dim_col A" using dimv dimA by auto
    have "inner_prod v (A *\<^sub>v v) = inner_prod v (B *\<^sub>v v) + inner_prod v ((\<i> \<cdot>\<^sub>m C) *\<^sub>v v)"
      unfolding A using dimB dimiC dimv by (simp add: add_mult_distrib_mat_vec inner_prod_distrib_right)
    moreover have "inner_prod v ((\<i> \<cdot>\<^sub>m C) *\<^sub>v v) = \<i> * inner_prod v (C *\<^sub>v v)" using dimv dimC
      apply (simp add: scalar_prod_def sum_distrib_left cong: sum.cong)
      apply (rule sum.cong, auto)
      done
    ultimately have ABC: "inner_prod v (A *\<^sub>v v) = inner_prod v (B *\<^sub>v v) + \<i> * inner_prod v (C *\<^sub>v v)" by auto
    moreover have "inner_prod v (B *\<^sub>v v) \<in> Reals" using B dimB dimv hermitian_inner_prod_real by auto
    moreover have "inner_prod v (C *\<^sub>v v) \<in> Reals" using C dimC dimv hermitian_inner_prod_real by auto
    moreover have "inner_prod v (A *\<^sub>v v) \<in> Reals" using pA unfolding positive_def 
      apply (rule) 
      apply (fold n_def)
      apply (simp add: complex_is_Real_iff[of "inner_prod v (A *\<^sub>v v)"])
      apply (auto simp add: dimvA)
      done
    ultimately have "inner_prod v (C *\<^sub>v v) = 0" using of_real_Re by fastforce
  } 
  then have "C = 0\<^sub>m n n" using hermitian_inner_prod_zero dimC C by auto
  then have "A = B" using A dimC dimB by auto
  then show "hermitian A" using B by auto
qed

lemma positive_eigenvalue_positive:
  assumes dimA: "(A::complex mat) \<in> carrier_mat n n"
    and pA: "positive A"
    and c: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> es. [:- e, 1:])"
    and B: "unitary_schur_decomposition A es = (B,P,Q)"
  shows "\<And>i. i < n \<Longrightarrow> B$$(i, i) \<ge> 0"
proof -
  have hA: "hermitian A" using positive_is_hermitian pA by auto
  have "similar_mat_wit A B P (adjoint P) \<and> diagonal_mat B \<and> diag_mat B = es 
    \<and> unitary P \<and> (\<forall>i < n. B$$(i, i) \<in> Reals)"
    using hermitian_eigenvalue_real dimA hA B c by auto
  then have A: "A = P * B * (adjoint P)" and dB: "diagonal_mat B"
    and Bii: "\<And>i. i < n \<Longrightarrow> B$$(i, i) \<in> Reals"
    and dimB: "B \<in> carrier_mat n n" and dimP: "P \<in> carrier_mat n n" and dimaP: "adjoint P \<in> carrier_mat n n"
    and uP: "unitary P" 
    unfolding similar_mat_wit_def Let_def unitary_def using dimA by auto
  {
    fix i assume i: "i < n"
    define v where "v = col P i"
    then have dimv: "v \<in> carrier_vec n" using v_def dimP by auto
    have "inner_prod v (A *\<^sub>v v) = B$$(i, i)" unfolding A v_def
      using spectral_decomposition_extract_diag[OF dimP dimB uP dB i]  by auto
    moreover have "inner_prod v (A *\<^sub>v v) \<ge> 0" using dimv pA dimA positive_def by auto
    ultimately show "B$$(i, i) \<ge> 0" by auto
  }
qed

lemma diag_mat_mult_diag_mat:
  fixes B D :: "'a::semiring_0 mat"
  assumes dimB: "B \<in> carrier_mat n n" and dimD: "D \<in> carrier_mat n n"
    and dB: "diagonal_mat B" and dD: "diagonal_mat D"
  shows "B * D = mat n n (\<lambda>(i,j). (if i = j then (B$$(i, i)) * (D$$(i, i)) else 0))"
proof(rule eq_matI, auto)
  have Bij: "\<And>x y. x < n \<Longrightarrow> y < n \<Longrightarrow> x \<noteq> y \<Longrightarrow> B$$(x, y) = 0" using dB diagonal_mat_def dimB by auto
  have Dij: "\<And>x y. x < n \<Longrightarrow> y < n \<Longrightarrow> x \<noteq> y \<Longrightarrow> D$$(x, y) = 0" using dD diagonal_mat_def dimD by auto
{
  fix i j assume ij: "i < n" "j < n"
  have "(B * D) $$ (i, j) = (\<Sum>k=0..<n. (B $$ (i, k)) * (D $$ (k, j)))" using dimB dimD
    by (auto simp add: scalar_prod_def ij)
  also have "\<dots> = B$$(i, i) * D$$(i, j)"
    apply (simp add: sum.remove[of _i] ij)
    apply (simp add: Bij Dij ij)
    done
  finally have "(B * D) $$ (i, j) = B$$(i, i) * D$$(i, j)".
}
  note BDij = this
  from BDij show "\<And>j. j < n \<Longrightarrow> (B * D) $$ (j, j) = B $$ (j, j) * D $$ (j, j)" by auto
  from BDij show "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> (B * D) $$ (i, j) = 0" using Bij Dij by auto
  from assms show "dim_row B = n" "dim_col D = n" by auto
qed

lemma positive_only_if_decomp:
  assumes dimA: "A \<in> carrier_mat n n" and pA: "positive A"
  shows "\<exists>M \<in> carrier_mat n n. M * adjoint M = A"
proof -
  from pA have hA: "hermitian A" using positive_is_hermitian by auto
  obtain es where es: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> es. [:- e, 1:])" 
    using complex_mat_char_poly_factorizable dimA by auto
  obtain B P Q where schur: "unitary_schur_decomposition A es = (B,P,Q)" 
    by (cases "unitary_schur_decomposition A es", auto)
  then have "similar_mat_wit A B P (adjoint P) \<and> diagonal_mat B \<and> diag_mat B = es 
    \<and> unitary P \<and> (\<forall>i < n. B$$(i, i) \<in> Reals)"
    using hermitian_eigenvalue_real dimA es hA by auto
  then have A: "A = P * B * (adjoint P)" and dB: "diagonal_mat B"
    and Bii: "\<And>i. i < n \<Longrightarrow> B$$(i, i) \<in> Reals"
    and dimB: "B \<in> carrier_mat n n" and dimP: "P \<in> carrier_mat n n" and dimaP: "adjoint P \<in> carrier_mat n n"
    unfolding similar_mat_wit_def Let_def using dimA by auto
  have Bii: "\<And>i. i < n \<Longrightarrow> B$$(i, i) \<ge> 0" using pA dimA es schur positive_eigenvalue_positive by auto
  define D where "D = mat n n (\<lambda>(i, j). (if (i = j) then csqrt (B$$(i, i)) else 0))"
  then have dimD: "D \<in> carrier_mat n n" and dimaD: "adjoint D \<in> carrier_mat n n" using dimB by auto
  have dD: "diagonal_mat D" using dB D_def unfolding diagonal_mat_def by auto
  then have daD: "diagonal_mat (adjoint D)" by (simp add: adjoint_eval diagonal_mat_def)
  have Dii: "\<And>i. i < n \<Longrightarrow> D$$(i, i) = csqrt (B$$(i, i))" using dimD D_def by auto
  {
    fix i assume i: "i < n"
    define c where "c = csqrt (B$$(i, i))"
    have c: "c \<ge> 0" using Bii i c_def by auto
    then have "conjugate c = c" 
      using Reals_cnj_iff complex_is_Real_iff by auto
    then have "c * cnj c = B$$(i, i)" using c_def c unfolding conjugate_complex_def by (metis power2_csqrt power2_eq_square)
  }  
  note cBii = this
  have "D * adjoint D = mat n n (\<lambda>(i,j). (if (i = j) then B$$(i, i) else 0))"
    apply (simp add: diag_mat_mult_diag_mat[OF dimD dimaD dD daD])
    apply (rule eq_matI, auto simp add: D_def adjoint_eval cBii)
    done
  also have "\<dots> = B" using dimB dB[unfolded diagonal_mat_def] by auto
  finally have DaDB: "D * adjoint D = B".
  define M where "M = P * D"
  then have dimM: "M \<in> carrier_mat n n" using dimP dimD by auto
  have "M * adjoint M = (P * D) * (adjoint D * adjoint P)" using M_def adjoint_mult[OF dimP dimD] by auto
  also have "\<dots> = P * (D * adjoint D) * (adjoint P)" using dimP dimD by (mat_assoc n)
  also have "\<dots> = P * B * (adjoint P)" using DaDB by auto
  finally have "M * adjoint M = A" using A by auto
  with dimM show "\<exists>M \<in> carrier_mat n n. M * adjoint M = A" by auto
qed

lemma positive_if_decomp:
  assumes dimA: "A \<in> carrier_mat n n" and "\<exists>M. M * adjoint M = A"
  shows "positive A"
proof -
  from assms obtain M where M: "M * adjoint M = A" by auto
  define m where "m = dim_col M"
  have dimM: "M \<in> carrier_mat n m" using M dimA m_def by auto
{
  fix v assume dimv: "(v::complex vec) \<in> carrier_vec n"
  have dimaM: "adjoint M \<in> carrier_mat m n" using dimM by auto
  have dimaMv: "(adjoint M) *\<^sub>v v \<in> carrier_vec m" using dimaM dimv by auto
  have "inner_prod v (A *\<^sub>v v) = inner_prod v (M * adjoint M *\<^sub>v v)" using M by auto
  also have "\<dots> = inner_prod v (M *\<^sub>v (adjoint M *\<^sub>v v))" using assoc_mult_mat_vec dimM dimaM dimv by auto
  also have "\<dots> = inner_prod (adjoint M *\<^sub>v v) (adjoint M *\<^sub>v v)" using adjoint_def_alter[OF dimv dimaMv dimM] by auto
  also have "\<dots> \<ge> 0" using self_cscalar_prod_geq_0 by auto
  finally have "inner_prod v (A *\<^sub>v v) \<ge> 0".
}
  note geq0 = this
  from dimA geq0 show "positive A" using positive_def by auto
qed

lemma positive_iff_decomp:
  assumes dimA: "A \<in> carrier_mat n n"
  shows "positive A \<longleftrightarrow> (\<exists>M\<in>carrier_mat n n. M * adjoint M = A)"
proof
  assume pA: "positive A"
  then show "\<exists>M\<in>carrier_mat n n. M * adjoint M = A" using positive_only_if_decomp assms by auto
next
  assume "\<exists>M\<in>carrier_mat n n. M * adjoint M = A"
  then obtain M where M: "M * adjoint M = A" by auto
  then show "positive A" using M positive_if_decomp assms by auto
qed

lemma positive_dim_eq:
  assumes "positive A"
  shows "dim_row A = dim_col A"
  using carrier_matD(1)[of A "dim_col A" "dim_col A"]  assms[unfolded positive_def] by simp

lemma positive_zero:
  "positive (0\<^sub>m n n)"
  by (simp add: positive_def zero_mat_def mult_mat_vec_def scalar_prod_def)

lemma positive_one:
  "positive (1\<^sub>m n)"
proof (rule positive_if_decomp)
  show "1\<^sub>m n \<in> carrier_mat n n" by auto
  have "adjoint (1\<^sub>m n) = 1\<^sub>m n" using hermitian_one hermitian_def by auto
  then have "1\<^sub>m n * adjoint (1\<^sub>m n) = 1\<^sub>m n" by auto
  then show "\<exists>M. M * adjoint M = 1\<^sub>m n" by fastforce
qed

lemma positive_antisym:
  assumes pA: "positive A" and pnA: "positive (-A)"
  shows "A = 0\<^sub>m (dim_col A) (dim_col A)"
proof -
  define n where "n = dim_col A"
  from pA have dimA: "A \<in> carrier_mat n n" and dimnA: "-A \<in> carrier_mat n n"
    using positive_def n_def by auto
  from pA have hA: "hermitian A" using positive_is_hermitian by auto
  obtain es where es: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> es. [:- e, 1:])" 
    using complex_mat_char_poly_factorizable dimA by auto
  obtain B P Q where schur: "unitary_schur_decomposition A es = (B,P,Q)" 
    by (cases "unitary_schur_decomposition A es", auto)
  then have "similar_mat_wit A B P (adjoint P) \<and> diagonal_mat B \<and> unitary P"
    using hermitian_eigenvalue_real dimA es hA by auto
  then have A: "A = P * B * (adjoint P)" and dB: "diagonal_mat B" and uP: "unitary P"
    and dimB: "B \<in> carrier_mat n n" and dimnB: "-B \<in> carrier_mat n n"
    and dimP: "P \<in> carrier_mat n n" and dimaP: "adjoint P \<in> carrier_mat n n"
    unfolding similar_mat_wit_def Let_def using dimA by auto
  from es schur have geq0: "\<And>i. i < n \<Longrightarrow> B$$(i, i) \<ge> 0" using positive_eigenvalue_positive dimA pA by auto
  from A have nA: "-A = P * (-B) * (adjoint P)" using mult_smult_assoc_mat dimB dimP dimaP by auto
  from dB have dnB: "diagonal_mat (-B)" by (simp add: diagonal_mat_def)
  {
    fix i assume i: "i < n"
    define v where "v = col P i"
    then have dimv: "v \<in> carrier_vec n" using v_def dimP by auto
    have "inner_prod v ((-A) *\<^sub>v v) = (-B)$$(i, i)" unfolding nA v_def
      using spectral_decomposition_extract_diag[OF dimP dimnB uP dnB i]  by auto
    moreover have "inner_prod v ((-A) *\<^sub>v v) \<ge> 0" using dimv pnA dimnA positive_def by auto
    ultimately have "B$$(i, i) \<le> 0" using dimB i by auto
    moreover have "B$$(i, i) \<ge> 0" using i geq0 by auto
    ultimately have "B$$(i, i) = 0" by (metis no_atp(10))
  }
  then have "B = 0\<^sub>m n n" using dimB dB[unfolded diagonal_mat_def]
    by (subst eq_matI, auto)
  then show "A = 0\<^sub>m n n" using A dimB dimP dimaP by auto
qed

lemma positive_add:
  assumes pA: "positive A" and pB: "positive B"
    and dimA: "A \<in> carrier_mat n n" and dimB: "B \<in> carrier_mat n n"
  shows "positive (A + B)"
  unfolding positive_def
proof
  have dimApB: "A + B \<in> carrier_mat n n" using dimA dimB by auto
  then show "A + B \<in> carrier_mat (dim_col (A + B)) (dim_col (A + B))" using carrier_matD[of "A+B"] by auto
  {
    fix v assume dimv: "(v::complex vec) \<in> carrier_vec n"
    have 1: "inner_prod v (A *\<^sub>v v) \<ge> 0" using dimv pA[unfolded positive_def] dimA by auto
    have 2: "inner_prod v (B *\<^sub>v v) \<ge> 0" using dimv pB[unfolded positive_def] dimB by auto
    have "inner_prod v ((A + B) *\<^sub>v v) = inner_prod v (A *\<^sub>v v) + inner_prod v (B *\<^sub>v v)"
      using dimA dimB dimv by (simp add: add_mult_distrib_mat_vec inner_prod_distrib_right) 
    also have "\<dots> \<ge> 0" using 1 2 by auto
    finally have "inner_prod v ((A + B) *\<^sub>v v) \<ge> 0".
  }
  note geq0 = this
  then have "\<And>v. dim_vec v = n \<Longrightarrow> 0 \<le> inner_prod v ((A + B) *\<^sub>v v)" by auto
  then show "\<forall>v. dim_vec v = dim_col (A + B) \<longrightarrow> 0 \<le> inner_prod v ((A + B) *\<^sub>v v)" using dimApB by auto
qed

lemma positive_trace:
  assumes "A \<in> carrier_mat n n" and "positive A"
  shows "trace A \<ge> 0"
  using assms positive_iff_decomp trace_adjoint_positive by auto

lemma positive_close_under_left_right_mult_adjoint:
  fixes M A :: "complex mat"
  assumes dM: "M \<in> carrier_mat n n" and dA: "A \<in> carrier_mat n n" 
    and pA: "positive A"
  shows "positive (M * A * adjoint M)"
  unfolding positive_def
proof (rule, simp add: mult_carrier_mat[OF mult_carrier_mat[OF dM dA] adjoint_dim[OF dM]] carrier_matD[OF dM], rule, rule)
  have daM: "adjoint M \<in> carrier_mat n n" using dM by auto
  fix v::"complex vec" assume "dim_vec v = dim_col (M * A * adjoint M)"
  then have dv: "v \<in> carrier_vec n" using assms by auto
  then have "adjoint M *\<^sub>v v \<in> carrier_vec n" using daM by auto
  have assoc: "M * A * adjoint M *\<^sub>v v = M *\<^sub>v (A *\<^sub>v (adjoint M *\<^sub>v v))"
    using dA dM daM dv by (auto simp add: assoc_mult_mat_vec[of _ n n _ n])
  have "inner_prod v (M * A * adjoint M *\<^sub>v v) = inner_prod (adjoint M *\<^sub>v v) (A *\<^sub>v (adjoint M *\<^sub>v v))"
    apply (subst assoc)
    apply (subst adjoint_def_alter[where ?A = "M"])
    by (auto simp add: dv dA daM dM carrier_matD[OF dM] mult_mat_vec_carrier[of _ n n])
  also have "\<dots> \<ge> 0" using dA dv daM pA positive_def by auto
  finally show "inner_prod v (M * A * adjoint M *\<^sub>v v) \<ge> 0" by auto
qed

lemma positive_same_outer_prod:
  fixes v w :: "complex vec"
  assumes v: "v \<in> carrier_vec n" 
  shows "positive (outer_prod v v)"
proof -
  have d1: "adjoint (mat (dim_vec v) 1 (\<lambda>(i, j). v $ i)) \<in> carrier_mat 1 n" using assms by auto
  have d2: "mat 1 (dim_vec v) (\<lambda>(i, y). conjugate v $ y) \<in> carrier_mat 1 n" using assms by auto
  have dv: "dim_vec v = n" using assms by auto
  have "mat 1 (dim_vec v) (\<lambda>(i, y). conjugate v $ y) = adjoint (mat (dim_vec v) 1 (\<lambda>(i, j). v $ i))" (is "?r = adjoint ?l")
    apply (rule eq_matI) 
    subgoal for i j by (simp add: dv adjoint_eval)
    using d1 d2 by auto
  then have "outer_prod v v = ?l * adjoint ?l" unfolding outer_prod_def by auto
  then have "\<exists>M. M * adjoint M = outer_prod v v" by auto
  then show "positive (outer_prod v v)" using positive_if_decomp[OF outer_prod_dim[OF v v]] by auto
qed

lemma smult_smult_mat: 
  fixes k :: complex and l :: complex
  assumes "A \<in> carrier_mat nr n"
  shows "k \<cdot>\<^sub>m (l \<cdot>\<^sub>m A) = (k * l) \<cdot>\<^sub>m A" by auto

lemma positive_smult: 
  assumes "A \<in> carrier_mat n n"
    and "positive A"
    and "c \<ge> 0"
  shows "positive (c \<cdot>\<^sub>m A)"
proof -
  have sc: "csqrt c \<ge> 0" using assms(3) by fastforce
  obtain M where dimM: "M \<in> carrier_mat n n" and A: "M * adjoint M = A" using assms(1-2) positive_iff_decomp by auto
  have "c \<cdot>\<^sub>m A  = c \<cdot>\<^sub>m (M * adjoint M)" using A by auto
  have ccsq: "conjugate (csqrt c) = (csqrt c)" using sc Reals_cnj_iff[of "csqrt c"] complex_is_Real_iff by auto
  have MM: "(M * adjoint M) \<in> carrier_mat n n" using A assms by fastforce
  have leftd: "c  \<cdot>\<^sub>m (M * adjoint M) \<in> carrier_mat n n" using A assms by fastforce
  have rightd: "(csqrt c \<cdot>\<^sub>m M) * (adjoint (csqrt c \<cdot>\<^sub>m M))\<in> carrier_mat n n" using A assms by fastforce
  have "(csqrt c \<cdot>\<^sub>m M) * (adjoint (csqrt c \<cdot>\<^sub>m M)) = (csqrt c \<cdot>\<^sub>m M) * ((conjugate (csqrt c)) \<cdot>\<^sub>m  adjoint M)"
    using adjoint_scale assms(1) by (metis adjoint_scale)
  also have "\<dots> = (csqrt c \<cdot>\<^sub>m M) * (csqrt c \<cdot>\<^sub>m adjoint M)" using sc ccsq by fastforce
  also have "\<dots> = csqrt c \<cdot>\<^sub>m (M * (csqrt c \<cdot>\<^sub>m adjoint M))"
    using mult_smult_assoc_mat index_smult_mat(2,3) by fastforce
  also have "\<dots> =  csqrt c \<cdot>\<^sub>m ((csqrt c) \<cdot>\<^sub>m (M * adjoint M))"
    using mult_smult_distrib by fastforce
  also have "\<dots> = c \<cdot>\<^sub>m (M * adjoint M)" 
    using smult_smult_mat[of "M * adjoint M" n n "(csqrt c)" "(csqrt c)"]  MM sc
    by (metis power2_csqrt power2_eq_square )   
  also have "\<dots> = c \<cdot>\<^sub>m A" using A by auto
  finally have "(csqrt c \<cdot>\<^sub>m M) * (adjoint (csqrt c \<cdot>\<^sub>m M)) = c \<cdot>\<^sub>m A" by auto
  moreover have "c \<cdot>\<^sub>m A \<in> carrier_mat n n" using assms(1) by auto
  moreover have "csqrt c \<cdot>\<^sub>m M \<in> carrier_mat n n" using dimM by auto
  ultimately show ?thesis using positive_iff_decomp by auto
qed

text \<open>Version of previous theorem for real numbers\<close>
lemma positive_scale: 
  fixes c :: real
  assumes  "A \<in> carrier_mat n n"
    and "positive A"
    and "c \<ge> 0"
  shows "positive (c \<cdot>\<^sub>m A)"
  apply (rule positive_smult) using assms by auto

subsection \<open>L\"{o}wner partial order\<close>

definition lowner_le :: "complex mat \<Rightarrow> complex mat \<Rightarrow> bool"  (infix "\<le>\<^sub>L" 50) where
  "A \<le>\<^sub>L B \<longleftrightarrow> dim_row A = dim_row B \<and> dim_col A = dim_col B \<and> positive (B - A)"

lemma lowner_le_refl:
  assumes "A \<in> carrier_mat n n"
  shows "A \<le>\<^sub>L A"
  unfolding lowner_le_def
  apply (simp add: minus_r_inv_mat[OF assms])
  by (rule positive_zero)

lemma lowner_le_antisym:
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
    and L1: "A \<le>\<^sub>L B" and L2: "B \<le>\<^sub>L A"
  shows "A = B"
proof -
  from L1 have P1: "positive (B - A)" by (simp add: lowner_le_def)
  from L2 have P2: "positive (A - B)" by (simp add: lowner_le_def)
  have "A - B = - (B - A)" using A B by auto
  then have P3: "positive (- (B - A))" using P2 by auto
  have BA: "B - A \<in> carrier_mat n n" using A B by auto
  have "B - A = 0\<^sub>m n n" using BA by (subst positive_antisym[OF P1 P3], auto)
  then have "B + (-A) + A = 0\<^sub>m n n + A" using A B minus_add_uminus_mat[OF B A] by auto
  then have "B + (-A + A) = 0\<^sub>m n n + A" using A B by auto
  then show "A = B" using A B BA uminus_l_inv_mat[OF A] by auto
qed

lemma lowner_le_inner_prod_le:
  fixes A B :: "complex mat" and v :: "complex vec"
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
    and v: "v \<in> carrier_vec n"
    and "A \<le>\<^sub>L B"
  shows "inner_prod v (A *\<^sub>v v) \<le> inner_prod v (B *\<^sub>v v)"
proof -
  from assms have "positive (B-A)" by (auto simp add: lowner_le_def)
  with assms have geq: "inner_prod v ((B-A) *\<^sub>v v) \<ge> 0" 
    unfolding positive_def by auto
  have "inner_prod v ((B-A) *\<^sub>v v) = inner_prod v (B *\<^sub>v v) - inner_prod v (A *\<^sub>v v)" 
    unfolding minus_add_uminus_mat[OF B A]
    by (subst add_mult_distrib_mat_vec[OF B _ v], insert A B v, auto simp add: inner_prod_distrib_right[OF v])
  then show ?thesis using geq by auto
qed

lemma lowner_le_trans:
  fixes A B C :: "complex mat"
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n" and C: "C \<in> carrier_mat n n"
    and L1: "A \<le>\<^sub>L B" and L2: "B \<le>\<^sub>L C"
  shows "A \<le>\<^sub>L C"
  unfolding lowner_le_def
proof (auto simp add: carrier_matD[OF A] carrier_matD[OF C])
  have dim: "C - A \<in> carrier_mat n n" using A C by auto
  {
    fix v assume v: "(v::complex vec) \<in> carrier_vec n"
    from L1 have "inner_prod v (A *\<^sub>v v) \<le> inner_prod v (B *\<^sub>v v)" using lowner_le_inner_prod_le A B v by auto
    also from L2 have "\<dots> \<le> inner_prod v (C *\<^sub>v v)" using lowner_le_inner_prod_le B C v by auto
    finally have "inner_prod v (A *\<^sub>v v) \<le> inner_prod v (C *\<^sub>v v)".
    then have "inner_prod v (C *\<^sub>v v) - inner_prod v (A *\<^sub>v v) \<ge> 0" by auto
    then have "inner_prod v ((C - A) *\<^sub>v v) \<ge> 0" using A C v
      apply (subst minus_add_uminus_mat[OF C A])
      apply (subst add_mult_distrib_mat_vec[OF C _ v], simp)
      apply (simp add: inner_prod_distrib_right[OF v])
      done
  }
  note leq = this
  show "positive (C - A)" unfolding positive_def
    apply (rule, simp add: carrier_matD[OF A] dim)
    apply (subst carrier_matD[OF dim], insert leq, auto)
    done
qed

lemma lowner_le_imp_trace_le:
  assumes "A \<in> carrier_mat n n" and "B \<in> carrier_mat n n"
    and "A \<le>\<^sub>L B"
  shows "trace A \<le> trace B"
proof -
  have "positive (B - A)" using assms lowner_le_def by auto
  moreover have "B - A \<in> carrier_mat n n" using assms by auto
  ultimately have "trace (B - A) \<ge> 0" using positive_trace by auto
  moreover have "trace (B - A) = trace B - trace A" using trace_minus_linear assms by auto
  ultimately have "trace B - trace A \<ge> 0" by auto
  then show "trace A \<le> trace B" by auto
qed

lemma lowner_le_add:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n" "D \<in> carrier_mat n n"
    and "A \<le>\<^sub>L B" "C \<le>\<^sub>L D"
  shows "A + C \<le>\<^sub>L B + D"
proof -
  have "B + D - (A + C) = B - A + (D - C) " using assms by auto
  then have "positive (B + D - (A + C))" using assms unfolding lowner_le_def using positive_add
    by (metis minus_carrier_mat)
  then show "A + C \<le>\<^sub>L B + D" unfolding lowner_le_def using assms by fastforce
qed

lemma lowner_le_swap:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" 
    and "A \<le>\<^sub>L B" 
  shows "-B \<le>\<^sub>L -A"
proof -
  have "positive (B - A)" using assms lowner_le_def by fastforce
  moreover have "B - A = (-A) - (-B)" using assms by fastforce
  ultimately have "positive ((-A) - (-B))" by auto
  then show ?thesis using lowner_le_def assms by fastforce
qed

lemma lowner_le_minus:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n" "D \<in> carrier_mat n n"
    and "A \<le>\<^sub>L B" "C \<le>\<^sub>L D"
  shows "A - D \<le>\<^sub>L B - C"
proof -
  have "positive (D - C)" using assms lowner_le_def by auto
  then have "-D \<le>\<^sub>L -C" using lowner_le_swap assms by auto
  then have "A + (-D) \<le>\<^sub>L B + (-C)" using lowner_le_add[of "A" n  "B"] assms by auto
  moreover have "A + (-D) = A - D" and "B + (-C) = B - C" by auto
  ultimately show ?thesis by auto
qed

lemma outer_prod_le_one:
  assumes "v \<in> carrier_vec n"
    and "inner_prod v v \<le> 1"
  shows "outer_prod v v \<le>\<^sub>L 1\<^sub>m n"
proof -
  let ?o = "outer_prod v v"
  have do: "?o \<in> carrier_mat n n" using assms by auto
  {
    fix u :: "complex vec" assume "dim_vec u = n"
    then have du: "u \<in> carrier_vec n" by auto
    have r: "inner_prod u u \<in> Reals" apply (simp add: scalar_prod_def carrier_vecD[OF du])
      using complex_In_mult_cnj_zero complex_is_Real_iff by blast
    have geq0: "inner_prod u u \<ge> 0" 
      using self_cscalar_prod_geq_0 by auto

    have "inner_prod u (?o *\<^sub>v u) = inner_prod u v * inner_prod v u"
      apply (subst inner_prod_outer_prod)
      using du assms by auto
    also have "\<dots> \<le> inner_prod u u * inner_prod v v" using Cauchy_Schwarz_complex_vec du assms by auto
    also have "\<dots> \<le> inner_prod u u" using assms(2) r geq0 
      by (simp add: mult_right_le_one_le)
    finally have le: "inner_prod u (?o *\<^sub>v u) \<le> inner_prod u u".

    have "inner_prod u ((1\<^sub>m n - ?o) *\<^sub>v u) = inner_prod u ((1\<^sub>m n *\<^sub>v u) - ?o *\<^sub>v u)"
      apply (subst minus_mult_distrib_mat_vec) using do du by auto
    also have "\<dots> = inner_prod u u - inner_prod u (?o *\<^sub>v u)"
      apply (subst inner_prod_minus_distrib_right)
      using du do by auto
    also have "\<dots> \<ge> 0" using le by auto
    finally have "inner_prod u ((1\<^sub>m n - ?o) *\<^sub>v u) \<ge> 0" by auto
  }
  then have "positive (1\<^sub>m n - outer_prod v v)"
    unfolding positive_def using do by auto
  then show ?thesis unfolding lowner_le_def using do by auto
qed

lemma zero_lowner_le_positiveD:
  fixes A :: "complex mat"
  assumes dA: "A \<in> carrier_mat n n" and le: "0\<^sub>m n n \<le>\<^sub>L A"
  shows "positive A"
  using assms unfolding lowner_le_def by (subgoal_tac "A - 0\<^sub>m n n = A", auto)

lemma zero_lowner_le_positiveI:
  fixes A :: "complex mat"
  assumes dA: "A \<in> carrier_mat n n" and le: "positive A"
  shows "0\<^sub>m n n \<le>\<^sub>L A"
  using assms unfolding lowner_le_def by (subgoal_tac "A - 0\<^sub>m n n = A", auto)

lemma lowner_le_trans_positiveI:
  fixes A B :: "complex mat"
  assumes dA: "A \<in> carrier_mat n n" and pA: "positive A" and le: "A \<le>\<^sub>L B"
  shows "positive B"
proof -
  have dB: "B \<in> carrier_mat n n" using le dA lowner_le_def by auto
  have "0\<^sub>m n n \<le>\<^sub>L A" using zero_lowner_le_positiveI dA pA by auto
  then have "0\<^sub>m n n \<le>\<^sub>L B" using dA dB le by (simp add: lowner_le_trans[of _ n A B])
  then show ?thesis using dB zero_lowner_le_positiveD by auto
qed

lemma lowner_le_keep_under_measurement:
  fixes M A B :: "complex mat"
  assumes dM: "M \<in> carrier_mat n n" and dA: "A \<in> carrier_mat n n" and dB: "B \<in> carrier_mat n n"
    and le: "A \<le>\<^sub>L B"
  shows "adjoint M * A * M \<le>\<^sub>L adjoint M * B * M"
  unfolding lowner_le_def
proof (rule conjI, fastforce)+
  have daM: "adjoint M \<in> carrier_mat n n" using dM by auto
  have dBmA: "B - A \<in> carrier_mat n n" using dB dA by fastforce
  have "positive (B - A)" using le lowner_le_def by auto
  then have p: "positive (adjoint M * (B - A) * M)" 
    using positive_close_under_left_right_mult_adjoint[OF daM dBmA] adjoint_adjoint[of M] by auto
  moreover have e: "adjoint M * (B - A) * M = adjoint M * B * M - adjoint M * A * M" using dM dB dA by (mat_assoc n)
  ultimately show "positive (adjoint M * B * M - adjoint M * A * M)" by auto
qed

lemma smult_distrib_left_minus_mat:
  fixes A B :: "'a::comm_ring_1 mat"
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  shows "c \<cdot>\<^sub>m (B - A) = c \<cdot>\<^sub>m B - c \<cdot>\<^sub>m A"
  using assms by (auto simp add: minus_add_uminus_mat add_smult_distrib_left_mat)

lemma lowner_le_smultc:
  fixes c :: complex
  assumes "c \<ge> 0" "A \<le>\<^sub>L B" "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  shows "c \<cdot>\<^sub>m A \<le>\<^sub>L c \<cdot>\<^sub>m B"
proof -
  have eqBA: "c \<cdot>\<^sub>m (B - A) = c \<cdot>\<^sub>m B - c \<cdot>\<^sub>m A"
    using assms by (auto simp add: smult_distrib_left_minus_mat)

  have "positive (B - A)" using assms(2) unfolding lowner_le_def by auto
  then have "positive (c \<cdot>\<^sub>m (B - A))" using positive_smult[of "B-A" n c] assms by fastforce
  moreover have "c \<cdot>\<^sub>m A \<in> carrier_mat n n" using index_smult_mat(2,3) assms(3) by auto
  moreover have "c \<cdot>\<^sub>m B \<in> carrier_mat n n" using index_smult_mat(2,3) assms(4) by auto 
  ultimately show ?thesis unfolding lowner_le_def using eqBA by fastforce
qed

lemma lowner_le_smult:
  fixes c :: real
  assumes "c \<ge> 0" "A \<le>\<^sub>L B" "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  shows "c \<cdot>\<^sub>m A \<le>\<^sub>L c \<cdot>\<^sub>m B"
  apply (rule lowner_le_smultc) using assms by auto

lemma minus_smult_vec_distrib:
  fixes w :: "'a::comm_ring_1 vec"
  shows "(a - b) \<cdot>\<^sub>v w = a \<cdot>\<^sub>v w - b \<cdot>\<^sub>v w"
  apply (rule eq_vecI)
  by (auto simp add: scalar_prod_def algebra_simps)

lemma smult_mat_mult_mat_vec_assoc:
  fixes A :: "'a::comm_ring_1 mat"
  assumes A: "A \<in> carrier_mat n m" and w: "w \<in> carrier_vec m"
  shows "a \<cdot>\<^sub>m A *\<^sub>v w = a \<cdot>\<^sub>v (A *\<^sub>v w)"
  apply (rule eq_vecI)
   apply (simp add: scalar_prod_def carrier_matD[OF A] carrier_vecD[OF w])
   apply (subst sum_distrib_left) apply (rule sum.cong, simp)
  by auto

lemma mult_mat_vec_smult_vec_assoc:
  fixes A :: "'a::comm_ring_1 mat"
  assumes A: "A \<in> carrier_mat n m" and w: "w \<in> carrier_vec m"
  shows "A *\<^sub>v (a \<cdot>\<^sub>v w) = a \<cdot>\<^sub>v (A *\<^sub>v w)"
  apply (rule eq_vecI)
   apply (simp add: scalar_prod_def carrier_matD[OF A] carrier_vecD[OF w])
   apply (subst sum_distrib_left) apply (rule sum.cong, simp)
  by auto 

lemma outer_prod_left_right_mat:
  fixes A B :: "complex mat"
  assumes du: "u \<in> carrier_vec d2" and dv: "v \<in> carrier_vec d3"
    and dA: "A \<in> carrier_mat d1 d2" and dB: "B \<in> carrier_mat d3 d4"
  shows "A * (outer_prod u v) * B = (outer_prod (A *\<^sub>v u) (adjoint B *\<^sub>v v))"
  unfolding outer_prod_def
proof -
  have eq1: "A * (mat (dim_vec u) 1 (\<lambda>(i, j). u $ i)) = mat (dim_vec (A *\<^sub>v u)) 1 (\<lambda>(i, j). (A *\<^sub>v u) $ i)"
    apply (rule eq_matI)
    by (auto simp add: dA du scalar_prod_def)
  have conj: "conjugate a * b = conjugate ((a::complex) * conjugate b) " for a b by auto
  have eq2: "mat 1 (dim_vec v) (\<lambda>(i, y). conjugate v $ y) * B = mat 1 (dim_vec (adjoint B *\<^sub>v v)) (\<lambda>(i, y). conjugate (adjoint B *\<^sub>v v) $ y)"
    apply (rule eq_matI)
      apply (auto simp add: carrier_matD[OF dB] carrier_vecD[OF dv] scalar_prod_def adjoint_def conjugate_vec_def sum_conjugate )
    apply (rule sum.cong)
    by (auto simp add: conj)
  have "A * (mat (dim_vec u) 1 (\<lambda>(i, j). u $ i) * mat 1 (dim_vec v) (\<lambda>(i, y). conjugate v $ y)) * B =
       (A * (mat (dim_vec u) 1 (\<lambda>(i, j). u $ i))) *(mat 1 (dim_vec v) (\<lambda>(i, y). conjugate v $ y)) * B"
    using dA du dv dB assoc_mult_mat[OF dA, of "mat (dim_vec u) 1 (\<lambda>(i, j). u $ i)" 1 "mat 1 (dim_vec v) (\<lambda>(i, y). conjugate v $ y)"] by fastforce
  also have "\<dots> = (A * (mat (dim_vec u) 1 (\<lambda>(i, j). u $ i))) *((mat 1 (dim_vec v) (\<lambda>(i, y). conjugate v $ y)) * B)"
    using dA du dv dB assoc_mult_mat[OF _ _ dB, of "(A * (mat (dim_vec u) 1 (\<lambda>(i, j). u $ i)))" d1 1] by fastforce
  finally show "A * (mat (dim_vec u) 1 (\<lambda>(i, j). u $ i) * mat 1 (dim_vec v) (\<lambda>(i, y). conjugate v $ y)) * B =
    mat (dim_vec (A *\<^sub>v u)) 1 (\<lambda>(i, j). (A *\<^sub>v u) $ i) * mat 1 (dim_vec (adjoint B *\<^sub>v v)) (\<lambda>(i, y). conjugate (adjoint B *\<^sub>v v) $ y)" 
    using eq1 eq2 by auto
qed

subsection \<open>Density operators\<close>

definition density_operator :: "complex mat \<Rightarrow> bool" where
  "density_operator A \<longleftrightarrow> positive A \<and> trace A = 1"

definition partial_density_operator :: "complex mat \<Rightarrow> bool" where
  "partial_density_operator A \<longleftrightarrow> positive A \<and> trace A \<le> 1"

lemma pure_state_self_outer_prod_is_partial_density_operator:
  fixes v :: "complex vec"
  assumes dimv: "v \<in> carrier_vec n" and nv: "vec_norm v = 1"
  shows "partial_density_operator (outer_prod v v)"
  unfolding partial_density_operator_def
proof
  have dimov: "outer_prod v v \<in> carrier_mat n n" using dimv by auto
  show "positive (outer_prod v v)" unfolding positive_def
  proof (rule, simp add: carrier_matD(2)[OF dimov] dimov, rule allI, rule impI)
    fix w assume "dim_vec (w::complex vec) = dim_col (outer_prod v v)"
    then have dimw: "w \<in> carrier_vec n"  using dimov carrier_vecI by auto
    then have "inner_prod w ((outer_prod v v) *\<^sub>v w) = inner_prod w v * inner_prod v w" 
      using inner_prod_outer_prod dimw dimv by auto
    also have "\<dots> = inner_prod w v * conjugate (inner_prod w v)" using dimw dimv
      apply (subst conjugate_scalar_prod[of v "conjugate w"], simp)
      apply (subst conjugate_vec_sprod_comm[of "conjugate v" _ "conjugate w"], auto)
       apply (rule carrier_vec_conjugate[OF dimv])
      apply (rule carrier_vec_conjugate[OF dimw])
      done
    also have "\<dots> \<ge> 0" by auto
    finally show "inner_prod w ((outer_prod v v) *\<^sub>v w) \<ge> 0".
  qed
  have eq: "trace (outer_prod v v) = (\<Sum>i=0..<n. v$i * conjugate(v$i))" unfolding trace_def 
    apply (subst carrier_matD(1)[OF dimov])
    apply (simp add: index_outer_prod[OF dimv dimv])
    done
  have "vec_norm v = csqrt (\<Sum>i=0..<n. v$i * conjugate(v$i))" unfolding vec_norm_def using dimv
    by (simp add: scalar_prod_def)
  then have "(\<Sum>i=0..<n. v$i * conjugate(v$i)) = 1" using nv by auto
  with eq show "trace (outer_prod v v) \<le> 1" by auto
qed

(* Lemma 2.1 *)
lemma lowner_le_trace:
  assumes A: "A \<in> carrier_mat n n"
    and B: "B \<in> carrier_mat n n"
  shows "A \<le>\<^sub>L B \<longleftrightarrow> (\<forall>\<rho>\<in>carrier_mat n n. partial_density_operator \<rho> \<longrightarrow> trace (A * \<rho>) \<le> trace (B * \<rho>))"
proof (rule iffI)
  have dimBmA: "B - A \<in> carrier_mat n n" using A B by auto
  {
    assume "A \<le>\<^sub>L B"
    then have pBmA: "positive (B - A)" using lowner_le_def by auto
    moreover have "B - A \<in> carrier_mat n n" using assms by auto
    ultimately have "\<exists>M\<in>carrier_mat n n. M * adjoint M = B - A" using positive_iff_decomp[of "B - A"] by auto
    then obtain M where dimM: "M \<in> carrier_mat n n" and M: "M * adjoint M = B - A" by auto
    {
      fix \<rho> assume dimr: "\<rho> \<in> carrier_mat n n" and pdr: "partial_density_operator \<rho>"
      have eq: "trace(B * \<rho>) - trace(A * \<rho>) = trace((B - A) * \<rho>)" using A B dimr
        apply (subst minus_mult_distrib_mat, auto)
        apply (subst trace_minus_linear, auto)
        done
      have pr: "positive \<rho>" using pdr partial_density_operator_def by auto
      then have "\<exists>P\<in>carrier_mat n n. \<rho> = P * adjoint P" using positive_iff_decomp dimr by auto
      then obtain P where dimP: "P \<in> carrier_mat n n" and P: "\<rho> = P * adjoint P" by auto
      have "trace((B - A) * \<rho>) = trace(M * adjoint M * (P * adjoint P))" using P M by auto
      also have "\<dots> = trace((adjoint P * M) * adjoint (adjoint P * M))" using dimM dimP by (mat_assoc n)
      also have "\<dots> \<ge> 0" using trace_adjoint_positive by auto
      finally have "trace((B - A) * \<rho>) \<ge> 0".
      with eq have " trace (B * \<rho>) - trace (A * \<rho>) \<ge> 0" by auto
    }
    then show "\<forall>\<rho>\<in>carrier_mat n n. partial_density_operator \<rho> \<longrightarrow> trace (A * \<rho>) \<le> trace (B * \<rho>)" by auto
  }

  {
    assume asm: "\<forall>\<rho>\<in>carrier_mat n n. partial_density_operator \<rho> \<longrightarrow> trace (A * \<rho>) \<le> trace (B * \<rho>)"
    have "positive (B - A)" 
    proof -
      {
        fix v assume "dim_vec (v::complex vec) = dim_col (B - A) \<and> vec_norm v = 1"
        then have dimv: "v \<in> carrier_vec n" and nv: "vec_norm v = 1"
          using carrier_matD[OF dimBmA] carrier_vecI by auto
        have dimov: "outer_prod v v \<in> carrier_mat n n" using dimv by auto
        then have "partial_density_operator (outer_prod v v)" 
          using dimv nv pure_state_self_outer_prod_is_partial_density_operator by auto
        then have leq: "trace(A * (outer_prod v v)) \<le> trace(B * (outer_prod v v))" using asm dimov by auto
        have "trace((B - A) * (outer_prod v v)) = trace(B * (outer_prod v v)) - trace(A * (outer_prod v v))" using A B dimov
          apply (subst minus_mult_distrib_mat, auto)
          apply (subst trace_minus_linear, auto)
          done
        then have "trace((B - A) * (outer_prod v v)) \<ge> 0" using leq by auto
        then have "inner_prod v ((B - A) *\<^sub>v v) \<ge> 0" using trace_outer_prod_right[OF dimBmA dimv dimv] by auto
      }
      then show "positive (B - A)" using positive_iff_normalized_vec[of "B - A"] dimBmA A by simp
    qed
    then show "A \<le>\<^sub>L B" using lowner_le_def A B by auto
  }
qed

lemma lowner_le_traceI:
  assumes "A \<in> carrier_mat n n"
    and "B \<in> carrier_mat n n"
    and "\<And>\<rho>. \<rho> \<in> carrier_mat n n \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> trace (A * \<rho>) \<le> trace (B * \<rho>)"
  shows "A \<le>\<^sub>L B"
  using lowner_le_trace assms by auto

lemma trace_pdo_eq_imp_eq:
  assumes A: "A \<in> carrier_mat n n"
    and B: "B \<in> carrier_mat n n"
    and teq: "\<And>\<rho>. \<rho> \<in> carrier_mat n n \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> trace (A * \<rho>) = trace (B * \<rho>)"
  shows "A = B"
proof -
  from teq have "A \<le>\<^sub>L B" using lowner_le_trace[OF A B] teq by auto
  moreover from teq have "B \<le>\<^sub>L A" using lowner_le_trace[OF B A] teq by auto
  ultimately show "A = B" using lowner_le_antisym A B by auto
qed

lemma lowner_le_traceD:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "\<rho> \<in> carrier_mat n n"
    and "A \<le>\<^sub>L B"
    and "partial_density_operator \<rho>"
  shows "trace (A * \<rho>) \<le> trace (B * \<rho>)"
  using lowner_le_trace assms by blast

lemma sum_only_one_neq_0:
  assumes "finite A" and "j \<in> A" and "\<And>i. i \<in> A \<Longrightarrow> i \<noteq> j \<Longrightarrow> g i = 0"
  shows "sum g A = g j" 
proof -
  have "{j} \<subseteq> A" using assms by auto
  moreover have "\<forall>i\<in>A - {j}. g i = 0" using assms by simp
  ultimately have "sum g A = sum g {j}" using assms 
    by (auto simp add: comm_monoid_add_class.sum.mono_neutral_right[of A "{j}" g])
  moreover have "sum g {j} = g j" by simp
  ultimately show ?thesis by auto
qed

end
