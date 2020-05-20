(*  Title:       Square Matrices
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Square Matrices \<close>

text\<open> The general solution for affine systems of ODEs involves the exponential function. 
Unfortunately, this operation is only available in Isabelle for the type class ``banach''. 
Hence, we define a type of square matrices and prove that it is an instance of this class.\<close>

theory SQ_MTX
  imports MTX_Norms

begin

subsection \<open> Definition \<close>

typedef 'm sq_mtx = "UNIV::(real^'m^'m) set"
  morphisms to_vec to_mtx by simp

declare to_mtx_inverse [simp]
    and to_vec_inverse [simp]

setup_lifting type_definition_sq_mtx

lift_definition sq_mtx_ith :: "'m sq_mtx \<Rightarrow> 'm \<Rightarrow> (real^'m)" (infixl "$$" 90) is "($)" .

lift_definition sq_mtx_vec_mult :: "'m sq_mtx \<Rightarrow> (real^'m) \<Rightarrow> (real^'m)" (infixl "*\<^sub>V" 90) is "(*v)" .

lift_definition vec_sq_mtx_prod :: "(real^'m) \<Rightarrow> 'm sq_mtx \<Rightarrow> (real^'m)" is "(v*)" .

lift_definition sq_mtx_diag :: "(('m::finite) \<Rightarrow> real) \<Rightarrow> ('m::finite) sq_mtx" (binder "\<d>\<i>\<a>\<g> " 10) 
  is diag_mat .

lift_definition sq_mtx_transpose :: "('m::finite) sq_mtx \<Rightarrow> 'm sq_mtx" ("_\<^sup>\<dagger>") is transpose .

lift_definition sq_mtx_inv :: "('m::finite) sq_mtx \<Rightarrow> 'm sq_mtx" ("_\<^sup>-\<^sup>1" [90]) is matrix_inv .

lift_definition sq_mtx_row :: "'m \<Rightarrow> ('m::finite) sq_mtx \<Rightarrow> real^'m" ("\<r>\<o>\<w>") is row .

lift_definition sq_mtx_col :: "'m \<Rightarrow> ('m::finite) sq_mtx \<Rightarrow> real^'m" ("\<c>\<o>\<l>")  is column .

lemma to_vec_eq_ith: "(to_vec A) $ i = A $$ i"
  by transfer simp

lemma to_mtx_ith[simp]: 
  "(to_mtx A) $$ i1 = A $ i1"
  "(to_mtx A) $$ i1 $ i2 = A $ i1 $ i2"
  by (transfer, simp)+

lemma to_mtx_vec_lambda_ith[simp]: "to_mtx (\<chi> i j. x i j) $$ i1 $ i2 = x i1 i2"
  by (simp add: sq_mtx_ith_def)

lemma sq_mtx_eq_iff:
  shows "A = B = (\<forall>i j. A $$ i $ j = B $$ i $ j)"
    and "A = B = (\<forall>i. A $$ i = B $$ i)"
  by (transfer, simp add: vec_eq_iff)+

lemma sq_mtx_diag_simps[simp]:
  "i = j \<Longrightarrow> sq_mtx_diag f $$ i $ j = f i"
  "i \<noteq> j \<Longrightarrow> sq_mtx_diag f $$ i $ j = 0"
  "sq_mtx_diag f $$ i = axis i (f i)"
  unfolding sq_mtx_diag_def by (simp_all add: axis_def vec_eq_iff)

lemma sq_mtx_diag_vec_mult: "(\<d>\<i>\<a>\<g> i. f i) *\<^sub>V s = (\<chi> i. f i * s$i)"
  by (simp add: matrix_vector_mul_diag_mat sq_mtx_diag.abs_eq sq_mtx_vec_mult.abs_eq)

lemma sq_mtx_vec_mult_diag_axis: "(\<d>\<i>\<a>\<g> i. f i) *\<^sub>V (axis i k) = axis i (f i * k)"
  unfolding sq_mtx_diag_vec_mult axis_def by auto

lemma sq_mtx_vec_mult_eq: "m *\<^sub>V x = (\<chi> i. sum (\<lambda>j. (m $$ i $ j) * (x $ j)) UNIV)"
  by (transfer, simp add: matrix_vector_mult_def)

lemma sq_mtx_transpose_transpose[simp]: "(A\<^sup>\<dagger>)\<^sup>\<dagger> = A"
  by (transfer, simp)

lemma transpose_mult_vec_canon_row[simp]: "(A\<^sup>\<dagger>) *\<^sub>V (\<e> i) = \<r>\<o>\<w> i A"
  by transfer (simp add: row_def transpose_def axis_def matrix_vector_mult_def)

lemma row_ith[simp]: "\<r>\<o>\<w> i A = A $$ i"
  by transfer (simp add: row_def)

lemma mtx_vec_mult_canon: "A *\<^sub>V (\<e> i) = \<c>\<o>\<l> i A" 
  by (transfer, simp add: matrix_vector_mult_basis)


subsection \<open> Ring of square matrices \<close>

instantiation sq_mtx :: (finite) ring 
begin

lift_definition plus_sq_mtx :: "'a sq_mtx \<Rightarrow> 'a sq_mtx \<Rightarrow> 'a sq_mtx" is "(+)" .

lift_definition zero_sq_mtx :: "'a sq_mtx" is "0" .

lift_definition uminus_sq_mtx :: "'a sq_mtx \<Rightarrow> 'a sq_mtx" is "uminus" .

lift_definition minus_sq_mtx :: "'a sq_mtx \<Rightarrow> 'a sq_mtx \<Rightarrow> 'a sq_mtx" is "(-)" .

lift_definition times_sq_mtx :: "'a sq_mtx \<Rightarrow> 'a sq_mtx \<Rightarrow> 'a sq_mtx" is "(**)" .

declare plus_sq_mtx.rep_eq [simp]
    and minus_sq_mtx.rep_eq [simp]

instance apply intro_classes
  by(transfer, simp add: algebra_simps matrix_mul_assoc matrix_add_rdistrib matrix_add_ldistrib)+

end

lemma sq_mtx_zero_ith[simp]: "0 $$ i = 0"
  by (transfer, simp)

lemma sq_mtx_zero_nth[simp]: "0 $$ i $ j = 0"
  by transfer simp

lemma sq_mtx_plus_eq: "A + B = to_mtx (\<chi> i j. A$$i$j + B$$i$j)"
  by transfer (simp add: vec_eq_iff)

lemma sq_mtx_plus_ith[simp]:"(A + B) $$ i = A $$ i + B $$ i"
  unfolding sq_mtx_plus_eq by (simp add: vec_eq_iff)

lemma sq_mtx_uminus_eq: "- A = to_mtx (\<chi> i j. - A$$i$j)"
  by transfer (simp add: vec_eq_iff)

lemma sq_mtx_minus_eq: "A - B = to_mtx (\<chi> i j. A$$i$j - B$$i$j)"
  by transfer (simp add: vec_eq_iff)

lemma sq_mtx_minus_ith[simp]:"(A - B) $$ i = A $$ i - B $$ i"
  unfolding sq_mtx_minus_eq by (simp add: vec_eq_iff)

lemma sq_mtx_times_eq: "A * B = to_mtx (\<chi> i j. sum (\<lambda>k. A$$i$k * B$$k$j) UNIV)"
  by transfer (simp add: matrix_matrix_mult_def)

lemma sq_mtx_plus_diag_diag[simp]: "sq_mtx_diag f + sq_mtx_diag g = (\<d>\<i>\<a>\<g> i. f i + g i)"
  by (subst sq_mtx_eq_iff) (simp add: axis_def)

lemma sq_mtx_minus_diag_diag[simp]: "sq_mtx_diag f - sq_mtx_diag g = (\<d>\<i>\<a>\<g> i. f i - g i)"
  by (subst sq_mtx_eq_iff) (simp add: axis_def)

lemma sum_sq_mtx_diag[simp]: "(\<Sum>n<m. sq_mtx_diag (g n)) = (\<d>\<i>\<a>\<g> i. \<Sum>n<m. (g n i))" for m::nat
  by (induct m, simp, subst sq_mtx_eq_iff, simp_all)

lemma sq_mtx_mult_diag_diag[simp]: "sq_mtx_diag f * sq_mtx_diag g = (\<d>\<i>\<a>\<g> i. f i * g i)"
  by (simp add: matrix_mul_diag_diag sq_mtx_diag.abs_eq times_sq_mtx.abs_eq)

lemma sq_mtx_mult_diagl: "(\<d>\<i>\<a>\<g> i. f i) * A = to_mtx (\<chi> i j. f i * A $$ i $ j)"
  by transfer (simp add: matrix_mul_diag_matl)

lemma sq_mtx_mult_diagr: "A * (\<d>\<i>\<a>\<g> i. f i) = to_mtx (\<chi> i j. A $$ i $ j * f j)"
  by transfer (simp add: matrix_matrix_mul_diag_matr)

lemma mtx_vec_mult_0l[simp]: "0 *\<^sub>V x = 0"
  by (simp add: sq_mtx_vec_mult.abs_eq zero_sq_mtx_def)

lemma mtx_vec_mult_0r[simp]: "A *\<^sub>V 0 = 0"
  by (transfer, simp)

lemma mtx_vec_mult_add_rdistr: "(A + B) *\<^sub>V x = A *\<^sub>V x + B *\<^sub>V x"
  unfolding plus_sq_mtx_def 
  apply(transfer)
  by (simp add: matrix_vector_mult_add_rdistrib)

lemma mtx_vec_mult_add_rdistl: "A *\<^sub>V (x + y) = A *\<^sub>V x + A *\<^sub>V y"
  unfolding plus_sq_mtx_def 
  apply transfer
  by (simp add: matrix_vector_right_distrib)

lemma mtx_vec_mult_minus_rdistrib: "(A - B) *\<^sub>V x = A *\<^sub>V x - B *\<^sub>V x"
  unfolding minus_sq_mtx_def by(transfer, simp add: matrix_vector_mult_diff_rdistrib)

lemma mtx_vec_mult_minus_ldistrib: "A *\<^sub>V (x - y) =  A *\<^sub>V x -  A *\<^sub>V y"
  by (metis (no_types, lifting) add_diff_cancel diff_add_cancel 
      matrix_vector_right_distrib sq_mtx_vec_mult.rep_eq)

lemma sq_mtx_times_vec_assoc: "(A * B) *\<^sub>V x = A *\<^sub>V (B *\<^sub>V x)"
  by (transfer, simp add: matrix_vector_mul_assoc)

lemma sq_mtx_vec_mult_sum_cols: "A *\<^sub>V x = sum (\<lambda>i. x $ i *\<^sub>R \<c>\<o>\<l> i A) UNIV"
  by(transfer) (simp add: matrix_mult_sum scalar_mult_eq_scaleR)


subsection \<open> Real normed vector space of square matrices \<close>

instantiation sq_mtx :: (finite) real_normed_vector 
begin

definition norm_sq_mtx :: "'a sq_mtx \<Rightarrow> real" where "\<parallel>A\<parallel> = \<parallel>to_vec A\<parallel>\<^sub>o\<^sub>p"

lift_definition scaleR_sq_mtx :: "real \<Rightarrow> 'a sq_mtx \<Rightarrow> 'a sq_mtx" is scaleR .

definition sgn_sq_mtx :: "'a sq_mtx \<Rightarrow> 'a sq_mtx" 
  where "sgn_sq_mtx A = (inverse (\<parallel>A\<parallel>)) *\<^sub>R A"

definition dist_sq_mtx :: "'a sq_mtx \<Rightarrow> 'a sq_mtx \<Rightarrow> real" 
  where "dist_sq_mtx A B = \<parallel>A - B\<parallel>" 

definition uniformity_sq_mtx :: "('a sq_mtx \<times> 'a sq_mtx) filter" 
  where "uniformity_sq_mtx = (INF e\<in>{0<..}. principal {(x, y). dist x y < e})"

definition open_sq_mtx :: "'a sq_mtx set \<Rightarrow> bool" 
  where "open_sq_mtx U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"

instance apply intro_classes 
  unfolding sgn_sq_mtx_def open_sq_mtx_def dist_sq_mtx_def uniformity_sq_mtx_def
            prefer 10 
            apply(transfer, simp add: norm_sq_mtx_def op_norm_triangle)
           prefer 9 
           apply(simp_all add: norm_sq_mtx_def zero_sq_mtx_def op_norm_eq_0)
  by (transfer, simp add: norm_sq_mtx_def op_norm_scaleR algebra_simps)+

end

lemma sq_mtx_scaleR_eq: "c *\<^sub>R A = to_mtx (\<chi> i j. c *\<^sub>R A $$ i $ j)"
  by transfer (simp add: vec_eq_iff)

lemma scaleR_to_mtx_ith[simp]: "c *\<^sub>R (to_mtx A) $$ i1 $ i2 = c * A $ i1 $ i2"
  by transfer (simp add: scaleR_vec_def)

lemma sq_mtx_scaleR_ith[simp]: "(c *\<^sub>R A) $$ i = (c  *\<^sub>R (A $$ i))"
  by (unfold scaleR_sq_mtx_def, transfer, simp)

lemma scaleR_sq_mtx_diag: "c *\<^sub>R sq_mtx_diag f = (\<d>\<i>\<a>\<g> i. c * f i)"
  by (subst sq_mtx_eq_iff, simp add: axis_def)

lemma scaleR_mtx_vec_assoc: "(c *\<^sub>R A) *\<^sub>V x = c *\<^sub>R (A *\<^sub>V x)"
  unfolding scaleR_sq_mtx_def sq_mtx_vec_mult_def apply simp
  by (simp add: scaleR_matrix_vector_assoc)

lemma mtx_vec_scaleR_commute: "A *\<^sub>V (c *\<^sub>R x) = c *\<^sub>R (A *\<^sub>V x)"
  unfolding scaleR_sq_mtx_def sq_mtx_vec_mult_def apply(simp, transfer)
  by (simp add: vector_scaleR_commute)

lemma mtx_times_scaleR_commute: "A * (c *\<^sub>R B) = c *\<^sub>R (A * B)" for A::"('n::finite) sq_mtx"
  unfolding sq_mtx_scaleR_eq sq_mtx_times_eq 
  apply(simp add: to_mtx_inject)
  apply(simp add: vec_eq_iff fun_eq_iff)
  by (simp add: semiring_normalization_rules(19) vector_space_over_itself.scale_sum_right)

lemma le_mtx_norm: "m \<in> {\<parallel>A *\<^sub>V x\<parallel> |x. \<parallel>x\<parallel> = 1} \<Longrightarrow> m \<le> \<parallel>A\<parallel>"
  using cSup_upper[of _ "{\<parallel>(to_vec A) *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"]
  by (simp add: op_norm_set_proptys(2) op_norm_def norm_sq_mtx_def sq_mtx_vec_mult.rep_eq)

lemma norm_vec_mult_le: "\<parallel>A *\<^sub>V x\<parallel> \<le> (\<parallel>A\<parallel>) * (\<parallel>x\<parallel>)"
  by (simp add: norm_matrix_le_mult_op_norm norm_sq_mtx_def sq_mtx_vec_mult.rep_eq)

lemma bounded_bilinear_sq_mtx_vec_mult: "bounded_bilinear (\<lambda>A s. A *\<^sub>V s)"
  apply (rule bounded_bilinear.intro, simp_all add: mtx_vec_mult_add_rdistr 
      mtx_vec_mult_add_rdistl scaleR_mtx_vec_assoc mtx_vec_scaleR_commute)
  by (rule_tac x=1 in exI, auto intro!: norm_vec_mult_le)

lemma norm_sq_mtx_def2: "\<parallel>A\<parallel> = Sup {\<parallel>A *\<^sub>V x\<parallel> |x. \<parallel>x\<parallel> = 1}"
  unfolding norm_sq_mtx_def op_norm_def sq_mtx_vec_mult_def by simp

lemma norm_sq_mtx_def3: "\<parallel>A\<parallel> = (SUP x. (\<parallel>A *\<^sub>V x\<parallel>) / (\<parallel>x\<parallel>))"
  unfolding norm_sq_mtx_def onorm_def sq_mtx_vec_mult_def by simp

lemma norm_sq_mtx_diag: "\<parallel>sq_mtx_diag f\<parallel> = Max {\<bar>f i\<bar> |i. i \<in> UNIV}"
  unfolding norm_sq_mtx_def apply transfer
  by (rule op_norm_diag_mat_eq)

lemma sq_mtx_norm_le_sum_col: "\<parallel>A\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>\<c>\<o>\<l> i A\<parallel>)"
  using op_norm_le_sum_column[of "to_vec A"] 
  apply(simp add: norm_sq_mtx_def)
  by(transfer, simp add: op_norm_le_sum_column)

lemma norm_le_transpose: "\<parallel>A\<parallel> \<le> \<parallel>A\<^sup>\<dagger>\<parallel>"
  unfolding norm_sq_mtx_def by transfer (rule op_norm_le_transpose)

lemma norm_eq_norm_transpose[simp]: "\<parallel>A\<^sup>\<dagger>\<parallel> = \<parallel>A\<parallel>"
  using norm_le_transpose[of A] and norm_le_transpose[of "A\<^sup>\<dagger>"] by simp

lemma norm_column_le_norm: "\<parallel>A $$ i\<parallel> \<le> \<parallel>A\<parallel>"
  using norm_vec_mult_le[of "A\<^sup>\<dagger>" "\<e> i"] by simp


subsection \<open> Real normed algebra of square matrices \<close>

instantiation sq_mtx :: (finite) real_normed_algebra_1
begin

lift_definition one_sq_mtx :: "'a sq_mtx" is "to_mtx (mat 1)" .

lemma sq_mtx_one_idty: "1 * A = A" "A * 1 = A" for A :: "'a sq_mtx"
  by(transfer, transfer, unfold mat_def matrix_matrix_mult_def, simp add: vec_eq_iff)+

lemma sq_mtx_norm_1: "\<parallel>(1::'a sq_mtx)\<parallel> = 1"
  unfolding one_sq_mtx_def norm_sq_mtx_def 
  apply(simp add: op_norm_def)
  apply(subst cSup_eq[of _ 1])
  using ex_norm_eq_1 by auto

lemma sq_mtx_norm_times: "\<parallel>A * B\<parallel> \<le> (\<parallel>A\<parallel>) * (\<parallel>B\<parallel>)" for A :: "'a sq_mtx"
  unfolding norm_sq_mtx_def times_sq_mtx_def by(simp add: op_norm_matrix_matrix_mult_le)

instance 
  apply intro_classes 
  apply(simp_all add: sq_mtx_one_idty sq_mtx_norm_1 sq_mtx_norm_times)
  apply(simp_all add: to_mtx_inject vec_eq_iff one_sq_mtx_def zero_sq_mtx_def mat_def)
  by(transfer, simp add: scalar_matrix_assoc matrix_scalar_ac)+

end

lemma sq_mtx_one_ith_simps[simp]: "1 $$ i $ i = 1" "i \<noteq> j \<Longrightarrow> 1 $$ i $ j = 0"
  unfolding one_sq_mtx_def mat_def by simp_all

lemma of_nat_eq_sq_mtx_diag[simp]: "of_nat m = (\<d>\<i>\<a>\<g> i. m)"
  by (induct m) (simp, subst sq_mtx_eq_iff, simp add: axis_def)+

lemma mtx_vec_mult_1[simp]: "1 *\<^sub>V s = s"
  by (auto simp: sq_mtx_vec_mult_def one_sq_mtx_def 
      mat_def vec_eq_iff matrix_vector_mult_def)

lemma sq_mtx_diag_one[simp]: "(\<d>\<i>\<a>\<g> i. 1) = 1"
  by (subst sq_mtx_eq_iff, simp add: one_sq_mtx_def mat_def axis_def)

abbreviation "mtx_invertible A \<equiv> invertible (to_vec A)"

lemma mtx_invertible_def: "mtx_invertible A \<longleftrightarrow> (\<exists>A'. A' * A = 1 \<and> A * A' = 1)"
  apply (unfold sq_mtx_inv_def times_sq_mtx_def one_sq_mtx_def invertible_def, clarsimp, safe)
   apply(rule_tac x="to_mtx A'" in exI, simp)
  by (rule_tac x="to_vec A'" in exI, simp add: to_mtx_inject)

lemma mtx_invertibleI:
  assumes "A * B = 1" and "B * A = 1"
  shows "mtx_invertible A"
  using assms unfolding mtx_invertible_def by auto

lemma mtx_invertibleD[simp]:
  assumes "mtx_invertible A" 
  shows "A\<^sup>-\<^sup>1 * A = 1" and "A * A\<^sup>-\<^sup>1 = 1"
  apply (unfold sq_mtx_inv_def times_sq_mtx_def one_sq_mtx_def)
  using assms by simp_all

lemma mtx_invertible_inv[simp]: "mtx_invertible A \<Longrightarrow> mtx_invertible (A\<^sup>-\<^sup>1)"
  using mtx_invertibleD mtx_invertibleI by blast

lemma mtx_invertible_one[simp]: "mtx_invertible 1"
  by (simp add: one_sq_mtx.rep_eq)

lemma sq_mtx_inv_unique:
  assumes "A * B = 1" and "B * A = 1"
  shows "A\<^sup>-\<^sup>1 = B"
  by (metis (no_types, lifting) assms mtx_invertibleD(2) 
      mtx_invertibleI mult.assoc sq_mtx_one_idty(1))

lemma sq_mtx_inv_idempotent[simp]: "mtx_invertible A \<Longrightarrow> A\<^sup>-\<^sup>1\<^sup>-\<^sup>1 = A"
  using mtx_invertibleD sq_mtx_inv_unique by blast

lemma sq_mtx_inv_mult:
  assumes "mtx_invertible A" and "mtx_invertible B"
  shows "(A * B)\<^sup>-\<^sup>1 = B\<^sup>-\<^sup>1 * A\<^sup>-\<^sup>1"
  by (simp add: assms matrix_inv_matrix_mul sq_mtx_inv_def times_sq_mtx_def)

lemma sq_mtx_inv_one[simp]: "1\<^sup>-\<^sup>1 = 1"
  by (simp add: sq_mtx_inv_unique)

definition similar_sq_mtx :: "('n::finite) sq_mtx \<Rightarrow> 'n sq_mtx \<Rightarrow> bool" (infixr "\<sim>" 25)
  where "(A \<sim> B) \<longleftrightarrow> (\<exists> P. mtx_invertible P \<and> A = P\<^sup>-\<^sup>1 * B * P)"

lemma similar_sq_mtx_matrix: "(A \<sim> B) = similar_matrix (to_vec A) (to_vec B)"
  apply(unfold similar_matrix_def similar_sq_mtx_def, safe)
   apply (metis sq_mtx_inv.rep_eq times_sq_mtx.rep_eq)
  by (metis UNIV_I sq_mtx_inv.abs_eq times_sq_mtx.abs_eq to_mtx_inverse to_vec_inverse)

lemma similar_sq_mtx_refl[simp]: "A \<sim> A"
  by (unfold similar_sq_mtx_def, rule_tac x="1" in exI, simp)

lemma similar_sq_mtx_simm: "A \<sim> B \<Longrightarrow> B \<sim> A"
  apply(unfold similar_sq_mtx_def, clarsimp)
  apply(rule_tac x="P\<^sup>-\<^sup>1" in exI, simp add: mult.assoc)
  by (metis mtx_invertibleD(2) mult.assoc mult.left_neutral)

lemma similar_sq_mtx_trans: "A \<sim> B \<Longrightarrow> B \<sim> C \<Longrightarrow> A \<sim> C"
  unfolding similar_sq_mtx_matrix using similar_matrix_trans by blast

lemma power_sq_mtx_diag: "(sq_mtx_diag f)^n = (\<d>\<i>\<a>\<g> i. f i^n)"
  by (induct n, simp_all)

lemma power_similiar_sq_mtx_diag_eq:
  assumes "mtx_invertible P"
      and "A = P\<^sup>-\<^sup>1 * (sq_mtx_diag f) * P"
    shows "A^n = P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i^n) * P"
proof(induct n, simp_all add: assms)
  fix n::nat
  have "P\<^sup>-\<^sup>1 * sq_mtx_diag f * P * (P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i ^ n) * P) = 
  P\<^sup>-\<^sup>1 * sq_mtx_diag f * (\<d>\<i>\<a>\<g> i. f i ^ n) * P"
    by (metis (no_types, lifting) assms(1) mtx_invertibleD(2) mult.assoc mult.right_neutral)
  also have "... = P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i * f i ^ n) * P"
    by (simp add: mult.assoc) 
  finally show "P\<^sup>-\<^sup>1 * sq_mtx_diag f * P * (P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i ^ n) * P) = 
  P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i * f i ^ n) * P" .
qed

lemma power_similar_sq_mtx_diag:
  assumes "A \<sim> (sq_mtx_diag f)"
  shows "A^n \<sim> (\<d>\<i>\<a>\<g> i. f i^n)"
  using assms power_similiar_sq_mtx_diag_eq 
  unfolding similar_sq_mtx_def by blast


subsection \<open> Banach space of square matrices \<close>

lemma Cauchy_cols:
  fixes X :: "nat \<Rightarrow> ('a::finite) sq_mtx" 
  assumes "Cauchy X"
  shows "Cauchy (\<lambda>n. \<c>\<o>\<l> i (X n))" 
proof(unfold Cauchy_def dist_norm, clarsimp)
  fix \<epsilon>::real assume "\<epsilon> > 0"
  then obtain M where M_def:"\<forall>m\<ge>M. \<forall>n\<ge>M. \<parallel>X m - X n\<parallel> < \<epsilon>"
    using \<open>Cauchy X\<close> unfolding Cauchy_def by(simp add: dist_sq_mtx_def) metis
  {fix m n assume "m \<ge> M" and "n \<ge> M"
    hence "\<epsilon> > \<parallel>X m - X n\<parallel>" 
      using M_def by blast
    moreover have "\<parallel>X m - X n\<parallel> \<ge> \<parallel>(X m - X n) *\<^sub>V \<e> i\<parallel>"
      by(rule le_mtx_norm[of _ "X m - X n"], force)
    moreover have "\<parallel>(X m - X n) *\<^sub>V \<e> i\<parallel> = \<parallel>X m *\<^sub>V \<e> i - X n *\<^sub>V \<e> i\<parallel>"
      by (simp add: mtx_vec_mult_minus_rdistrib)
    moreover have "... = \<parallel>\<c>\<o>\<l> i (X m) - \<c>\<o>\<l> i (X n)\<parallel>"
      by (simp add: mtx_vec_mult_minus_rdistrib mtx_vec_mult_canon)
    ultimately have "\<parallel>\<c>\<o>\<l> i (X m) - \<c>\<o>\<l> i (X n)\<parallel> < \<epsilon>" 
      by linarith}
  thus "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<parallel>\<c>\<o>\<l> i (X m) - \<c>\<o>\<l> i (X n)\<parallel> < \<epsilon>" 
    by blast
qed

lemma col_convergence:
  assumes "\<forall>i. (\<lambda>n. \<c>\<o>\<l> i (X n)) \<longlonglongrightarrow> L $ i" 
  shows "X \<longlonglongrightarrow> to_mtx (transpose L)"
proof(unfold LIMSEQ_def dist_norm, clarsimp)
  let ?L = "to_mtx (transpose L)"
  let ?a = "CARD('a)" fix \<epsilon>::real assume "\<epsilon> > 0"
  hence "\<epsilon> / ?a > 0" by simp
  hence "\<forall>i. \<exists> N. \<forall>n\<ge>N. \<parallel>\<c>\<o>\<l> i (X n) - L $ i\<parallel> < \<epsilon>/?a"
    using assms unfolding LIMSEQ_def dist_norm convergent_def by blast
  then obtain N where "\<forall>i. \<forall>n\<ge>N. \<parallel>\<c>\<o>\<l> i (X n) - L $ i\<parallel> < \<epsilon>/?a"
    using finite_nat_minimal_witness[of "\<lambda> i n. \<parallel>\<c>\<o>\<l> i (X n) - L $ i\<parallel> < \<epsilon>/?a"] by blast
  also have "\<And>i n. (\<c>\<o>\<l> i (X n) - L $ i) = (\<c>\<o>\<l> i (X n - ?L))"
    unfolding minus_sq_mtx_def by(transfer, simp add: transpose_def vec_eq_iff column_def)
  ultimately have N_def:"\<forall>i. \<forall>n\<ge>N. \<parallel>\<c>\<o>\<l> i (X n - ?L)\<parallel> < \<epsilon>/?a" 
    by auto
  have "\<forall>n\<ge>N. \<parallel>X n - ?L\<parallel> < \<epsilon>"
  proof(rule allI, rule impI)
    fix n::nat assume "N \<le> n"
    hence "\<forall> i. \<parallel>\<c>\<o>\<l> i (X n - ?L)\<parallel> < \<epsilon>/?a"
      using N_def by blast
    hence "(\<Sum>i\<in>UNIV. \<parallel>\<c>\<o>\<l> i (X n - ?L)\<parallel>) < (\<Sum>(i::'a)\<in>UNIV. \<epsilon>/?a)"
      using sum_strict_mono[of _ "\<lambda>i. \<parallel>\<c>\<o>\<l> i (X n - ?L)\<parallel>"] by force
    moreover have "\<parallel>X n - ?L\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>\<c>\<o>\<l> i (X n - ?L)\<parallel>)"
      using sq_mtx_norm_le_sum_col by blast
    moreover have "(\<Sum>(i::'a)\<in>UNIV. \<epsilon>/?a) = \<epsilon>" 
      by force
    ultimately show "\<parallel>X n - ?L\<parallel> < \<epsilon>" 
      by linarith
  qed
  thus "\<exists>no. \<forall>n\<ge>no. \<parallel>X n - ?L\<parallel> < \<epsilon>" 
    by blast
qed

instance sq_mtx :: (finite) banach
proof(standard)
  fix X :: "nat \<Rightarrow> 'a sq_mtx"
  assume "Cauchy X"
  hence "\<And>i. Cauchy (\<lambda>n. \<c>\<o>\<l> i (X n))"
    using Cauchy_cols by blast
  hence obs: "\<forall>i. \<exists>! L. (\<lambda>n. \<c>\<o>\<l> i (X n)) \<longlonglongrightarrow> L"
    using Cauchy_convergent convergent_def LIMSEQ_unique by fastforce
  define L where "L = (\<chi> i. lim (\<lambda>n. \<c>\<o>\<l> i (X n)))"
  hence "\<forall>i. (\<lambda>n. \<c>\<o>\<l> i (X n)) \<longlonglongrightarrow> L $ i" 
    using obs theI_unique[of "\<lambda>L. (\<lambda>n. \<c>\<o>\<l> _ (X n)) \<longlonglongrightarrow> L" "L $ _"] by (simp add: lim_def)
  thus "convergent X"
    using col_convergence unfolding convergent_def by blast
qed

lemma exp_similiar_sq_mtx_diag_eq:
  assumes "mtx_invertible P"
      and "A = P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i) * P"
    shows "exp A = P\<^sup>-\<^sup>1 * exp (\<d>\<i>\<a>\<g> i. f i) * P"
proof(unfold exp_def power_similiar_sq_mtx_diag_eq[OF assms])
  have "(\<Sum>n. P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i ^ n) * P /\<^sub>R fact n) = 
  (\<Sum>n. P\<^sup>-\<^sup>1 * ((\<d>\<i>\<a>\<g> i. f i ^ n) /\<^sub>R fact n) * P)"
    by simp
  also have "... = (\<Sum>n. P\<^sup>-\<^sup>1 * ((\<d>\<i>\<a>\<g> i. f i ^ n) /\<^sub>R fact n)) * P"
    apply(subst suminf_multr[OF bounded_linear.summable[OF bounded_linear_mult_right]])
    unfolding power_sq_mtx_diag[symmetric] by (simp_all add: summable_exp_generic)
  also have "... = P\<^sup>-\<^sup>1 * (\<Sum>n. (\<d>\<i>\<a>\<g> i. f i ^ n) /\<^sub>R fact n) * P"
    apply(subst suminf_mult[of _ "P\<^sup>-\<^sup>1"])
    unfolding power_sq_mtx_diag[symmetric] 
    by (simp_all add: summable_exp_generic)
  finally show "(\<Sum>n. P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i ^ n) * P /\<^sub>R fact n) = 
  P\<^sup>-\<^sup>1 * (\<Sum>n. sq_mtx_diag f ^ n /\<^sub>R fact n) * P"
    unfolding power_sq_mtx_diag by simp
qed

lemma exp_similiar_sq_mtx_diag:
  assumes "A \<sim> sq_mtx_diag f"
  shows "exp A \<sim> exp (sq_mtx_diag f)"
  using assms exp_similiar_sq_mtx_diag_eq 
  unfolding similar_sq_mtx_def by blast

lemma suminf_sq_mtx_diag:
  assumes "\<forall>i. (\<lambda>n. f n i) sums (suminf (\<lambda>n. f n i))"
  shows "(\<Sum>n. (\<d>\<i>\<a>\<g> i. f n i)) = (\<d>\<i>\<a>\<g> i. \<Sum>n. f n i)"
proof(rule suminfI, unfold sums_def LIMSEQ_iff, clarsimp simp: norm_sq_mtx_diag)
  let ?g = "\<lambda>n i. \<bar>(\<Sum>n<n. f n i) - (\<Sum>n. f n i)\<bar>"
  fix r::real assume "r > 0"
  have "\<forall>i. \<exists>no. \<forall>n\<ge>no. ?g n i < r"
    using assms \<open>r > 0\<close> unfolding sums_def LIMSEQ_iff by clarsimp 
  then obtain N where key: "\<forall>i. \<forall>n\<ge>N. ?g n i < r"
    using finite_nat_minimal_witness[of "\<lambda>i n. ?g n i < r"] by blast
  {fix n::nat
    assume "n \<ge> N"
    obtain i where i_def: "Max {x. \<exists>i. x = ?g n i} = ?g n i"
      using cMax_finite_ex[of "{x. \<exists>i. x = ?g n i}"] by auto
    hence "?g n i < r"
      using key \<open>n \<ge> N\<close> by blast
    hence "Max {x. \<exists>i. x = ?g n i} < r"
      unfolding i_def[symmetric] .}
  thus "\<exists>N. \<forall>n\<ge>N. Max {x. \<exists>i. x = ?g n i} < r"
    by blast
qed

lemma exp_sq_mtx_diag: "exp (sq_mtx_diag f) = (\<d>\<i>\<a>\<g> i. exp (f i))"
  apply(unfold exp_def, simp add: power_sq_mtx_diag scaleR_sq_mtx_diag)
  apply(rule suminf_sq_mtx_diag)
  using exp_converges[of "f _"] 
  unfolding sums_def LIMSEQ_iff exp_def by force

lemma exp_scaleR_diagonal1:
  assumes "mtx_invertible P" and "A = P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i) * P"
    shows "exp (t *\<^sub>R A) = P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. exp (t * f i)) * P"
proof-
  have "exp (t *\<^sub>R A) = exp (P\<^sup>-\<^sup>1 * (t *\<^sub>R sq_mtx_diag f) * P)"
    using assms by simp
  also have "... = P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. exp (t * f i)) * P"
    by (metis assms(1) exp_similiar_sq_mtx_diag_eq exp_sq_mtx_diag scaleR_sq_mtx_diag)
  finally show "exp (t *\<^sub>R A) = P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. exp (t * f i)) * P" .
qed

lemma exp_scaleR_diagonal2:
  assumes "mtx_invertible P" and "A = P * (\<d>\<i>\<a>\<g> i. f i) * P\<^sup>-\<^sup>1"
    shows "exp (t *\<^sub>R A) = P * (\<d>\<i>\<a>\<g> i. exp (t * f i)) * P\<^sup>-\<^sup>1"
  apply(subst sq_mtx_inv_idempotent[OF assms(1), symmetric])
  apply(rule exp_scaleR_diagonal1)
  by (simp_all add: assms)


subsection \<open> Examples \<close>

definition "mtx A = to_mtx (vector (map vector A))"

lemma vector_nth_eq: "(vector A) $ i = foldr (\<lambda>x f n. (f (n + 1))(n := x)) A (\<lambda>n x. 0) 1 i"
  unfolding vector_def by simp

lemma mtx_ith_eq[simp]: "mtx A $$ i $ j = foldr (\<lambda>x f n. (f (n + 1))(n := x))
  (map (\<lambda>l. vec_lambda (foldr (\<lambda>x f n. (f (n + 1))(n := x)) l (\<lambda>n x. 0) 1)) A) (\<lambda>n x. 0) 1 i $ j"
  unfolding mtx_def vector_def by (simp add: vector_nth_eq)

subsubsection \<open> 2x2 matrices \<close>

lemma mtx2_eq_iff: "(mtx 
  ([a1, b1] # 
   [c1, d1] # []) :: 2 sq_mtx) = mtx 
  ([a2, b2] # 
   [c2, d2] # []) \<longleftrightarrow> a1 = a2 \<and> b1 = b2 \<and> c1 = c2 \<and> d1 = d2"
  apply(simp add: sq_mtx_eq_iff, safe)
  using exhaust_2 by force+

lemma mtx2_to_mtx: "mtx 
  ([a, b] # 
   [c, d] # []) = 
  to_mtx (\<chi> i j::2. if i=1 \<and> j=1 then a 
  else (if i=1 \<and> j=2 then b 
  else (if i=2 \<and> j=1 then c 
  else d)))"
  apply(subst sq_mtx_eq_iff)
  using exhaust_2 by force

abbreviation diag2 :: "real \<Rightarrow> real \<Rightarrow> 2 sq_mtx" 
  where "diag2 \<iota>\<^sub>1 \<iota>\<^sub>2 \<equiv> mtx 
   ([\<iota>\<^sub>1, 0] # 
    [0, \<iota>\<^sub>2] # [])"

lemma diag2_eq: "diag2 (\<iota> 1) (\<iota> 2) = (\<d>\<i>\<a>\<g> i. \<iota> i)"
  apply(simp add: sq_mtx_eq_iff)
  using exhaust_2 by (force simp: axis_def)

lemma one_mtx2: "(1::2 sq_mtx) = diag2 1 1"
  apply(subst sq_mtx_eq_iff)
  using exhaust_2 by force

lemma zero_mtx2: "(0::2 sq_mtx) = diag2 0 0"
  by (simp add: sq_mtx_eq_iff)

lemma scaleR_mtx2: "k *\<^sub>R mtx 
  ([a, b] # 
   [c, d] # []) = mtx 
  ([k*a, k*b] # 
   [k*c, k*d] # [])"
  by (simp add: sq_mtx_eq_iff)

lemma uminus_mtx2: "-mtx 
  ([a, b] # 
   [c, d] # []) = (mtx 
  ([-a, -b] # 
   [-c, -d] # [])::2 sq_mtx)"
  by (simp add: sq_mtx_uminus_eq sq_mtx_eq_iff)

lemma plus_mtx2: "mtx 
  ([a1, b1] # 
   [c1, d1] # []) + mtx 
  ([a2, b2] # 
   [c2, d2] # []) = ((mtx 
  ([a1+a2, b1+b2] # 
   [c1+c2, d1+d2] # []))::2 sq_mtx)"
  by (simp add: sq_mtx_eq_iff)

lemma minus_mtx2: "mtx 
  ([a1, b1] # 
   [c1, d1] # []) - mtx 
  ([a2, b2] # 
   [c2, d2] # []) = ((mtx 
  ([a1-a2, b1-b2] # 
   [c1-c2, d1-d2] # []))::2 sq_mtx)"
  by (simp add: sq_mtx_eq_iff)

lemma times_mtx2: "mtx 
  ([a1, b1] # 
   [c1, d1] # []) * mtx 
  ([a2, b2] # 
   [c2, d2] # []) = ((mtx 
  ([a1*a2+b1*c2, a1*b2+b1*d2] # 
   [c1*a2+d1*c2, c1*b2+d1*d2] # []))::2 sq_mtx)"
  unfolding sq_mtx_times_eq UNIV_2
  by (simp add: sq_mtx_eq_iff)

subsubsection \<open> 3x3 matrices \<close>

lemma mtx3_to_mtx: "mtx 
  ([a\<^sub>1\<^sub>1, a\<^sub>1\<^sub>2, a\<^sub>1\<^sub>3] # 
   [a\<^sub>2\<^sub>1, a\<^sub>2\<^sub>2, a\<^sub>2\<^sub>3] # 
   [a\<^sub>3\<^sub>1, a\<^sub>3\<^sub>2, a\<^sub>3\<^sub>3] # []) = 
  to_mtx (\<chi> i j::3. if i=1 \<and> j=1 then a\<^sub>1\<^sub>1
  else (if i=1 \<and> j=2 then a\<^sub>1\<^sub>2 
  else (if i=1 \<and> j=3 then a\<^sub>1\<^sub>3 
  else (if i=2 \<and> j=1 then a\<^sub>2\<^sub>1
  else (if i=2 \<and> j=2 then a\<^sub>2\<^sub>2 
  else (if i=2 \<and> j=3 then a\<^sub>2\<^sub>3 
  else (if i=3 \<and> j=1 then a\<^sub>3\<^sub>1 
  else (if i=3 \<and> j=2 then a\<^sub>3\<^sub>2 
  else a\<^sub>3\<^sub>3))))))))"
  apply(simp add: sq_mtx_eq_iff)
  using exhaust_3 by force

abbreviation diag3 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 3 sq_mtx" 
  where "diag3 \<iota>\<^sub>1 \<iota>\<^sub>2 \<iota>\<^sub>3 \<equiv> mtx 
  ([\<iota>\<^sub>1, 0, 0] # 
   [0, \<iota>\<^sub>2, 0] # 
   [0, 0, \<iota>\<^sub>3] # [])"

lemma diag3_eq: "diag3 (\<iota> 1) (\<iota> 2) (\<iota> 3) = (\<d>\<i>\<a>\<g> i. \<iota> i)"
  apply(simp add: sq_mtx_eq_iff)
  using exhaust_3 by (force simp: axis_def)

lemma one_mtx3: "(1::3 sq_mtx) = diag3 1 1 1"
  apply(subst sq_mtx_eq_iff)
  using exhaust_3 by force

lemma zero_mtx3: "(0::3 sq_mtx) = diag3 0 0 0"
  by (simp add: sq_mtx_eq_iff)

lemma scaleR_mtx3: "k *\<^sub>R mtx 
  ([a\<^sub>1\<^sub>1, a\<^sub>1\<^sub>2, a\<^sub>1\<^sub>3] # 
   [a\<^sub>2\<^sub>1, a\<^sub>2\<^sub>2, a\<^sub>2\<^sub>3] # 
   [a\<^sub>3\<^sub>1, a\<^sub>3\<^sub>2, a\<^sub>3\<^sub>3] # []) = mtx 
  ([k*a\<^sub>1\<^sub>1, k*a\<^sub>1\<^sub>2, k*a\<^sub>1\<^sub>3] # 
   [k*a\<^sub>2\<^sub>1, k*a\<^sub>2\<^sub>2, k*a\<^sub>2\<^sub>3] # 
   [k*a\<^sub>3\<^sub>1, k*a\<^sub>3\<^sub>2, k*a\<^sub>3\<^sub>3] # [])"
  by (simp add: sq_mtx_eq_iff)

lemma plus_mtx3: "mtx 
  ([a\<^sub>1\<^sub>1, a\<^sub>1\<^sub>2, a\<^sub>1\<^sub>3] # 
   [a\<^sub>2\<^sub>1, a\<^sub>2\<^sub>2, a\<^sub>2\<^sub>3] # 
   [a\<^sub>3\<^sub>1, a\<^sub>3\<^sub>2, a\<^sub>3\<^sub>3] # []) + mtx 
  ([b\<^sub>1\<^sub>1, b\<^sub>1\<^sub>2, b\<^sub>1\<^sub>3] # 
   [b\<^sub>2\<^sub>1, b\<^sub>2\<^sub>2, b\<^sub>2\<^sub>3] # 
   [b\<^sub>3\<^sub>1, b\<^sub>3\<^sub>2, b\<^sub>3\<^sub>3] # []) = (mtx 
  ([a\<^sub>1\<^sub>1+b\<^sub>1\<^sub>1, a\<^sub>1\<^sub>2+b\<^sub>1\<^sub>2, a\<^sub>1\<^sub>3+b\<^sub>1\<^sub>3] # 
   [a\<^sub>2\<^sub>1+b\<^sub>2\<^sub>1, a\<^sub>2\<^sub>2+b\<^sub>2\<^sub>2, a\<^sub>2\<^sub>3+b\<^sub>2\<^sub>3] # 
   [a\<^sub>3\<^sub>1+b\<^sub>3\<^sub>1, a\<^sub>3\<^sub>2+b\<^sub>3\<^sub>2, a\<^sub>3\<^sub>3+b\<^sub>3\<^sub>3] # [])::3 sq_mtx)"
  by (subst sq_mtx_eq_iff) simp

lemma minus_mtx3: "mtx 
  ([a\<^sub>1\<^sub>1, a\<^sub>1\<^sub>2, a\<^sub>1\<^sub>3] # 
   [a\<^sub>2\<^sub>1, a\<^sub>2\<^sub>2, a\<^sub>2\<^sub>3] # 
   [a\<^sub>3\<^sub>1, a\<^sub>3\<^sub>2, a\<^sub>3\<^sub>3] # []) - mtx 
  ([b\<^sub>1\<^sub>1, b\<^sub>1\<^sub>2, b\<^sub>1\<^sub>3] # 
   [b\<^sub>2\<^sub>1, b\<^sub>2\<^sub>2, b\<^sub>2\<^sub>3] # 
   [b\<^sub>3\<^sub>1, b\<^sub>3\<^sub>2, b\<^sub>3\<^sub>3] # []) = (mtx 
  ([a\<^sub>1\<^sub>1-b\<^sub>1\<^sub>1, a\<^sub>1\<^sub>2-b\<^sub>1\<^sub>2, a\<^sub>1\<^sub>3-b\<^sub>1\<^sub>3] # 
   [a\<^sub>2\<^sub>1-b\<^sub>2\<^sub>1, a\<^sub>2\<^sub>2-b\<^sub>2\<^sub>2, a\<^sub>2\<^sub>3-b\<^sub>2\<^sub>3] # 
   [a\<^sub>3\<^sub>1-b\<^sub>3\<^sub>1, a\<^sub>3\<^sub>2-b\<^sub>3\<^sub>2, a\<^sub>3\<^sub>3-b\<^sub>3\<^sub>3] # [])::3 sq_mtx)"
  by (simp add: sq_mtx_eq_iff)

lemma times_mtx3: "mtx 
  ([a\<^sub>1\<^sub>1, a\<^sub>1\<^sub>2, a\<^sub>1\<^sub>3] # 
   [a\<^sub>2\<^sub>1, a\<^sub>2\<^sub>2, a\<^sub>2\<^sub>3] # 
   [a\<^sub>3\<^sub>1, a\<^sub>3\<^sub>2, a\<^sub>3\<^sub>3] # []) * mtx 
  ([b\<^sub>1\<^sub>1, b\<^sub>1\<^sub>2, b\<^sub>1\<^sub>3] # 
   [b\<^sub>2\<^sub>1, b\<^sub>2\<^sub>2, b\<^sub>2\<^sub>3] # 
   [b\<^sub>3\<^sub>1, b\<^sub>3\<^sub>2, b\<^sub>3\<^sub>3] # []) = (mtx 
  ([a\<^sub>1\<^sub>1*b\<^sub>1\<^sub>1+a\<^sub>1\<^sub>2*b\<^sub>2\<^sub>1+a\<^sub>1\<^sub>3*b\<^sub>3\<^sub>1, a\<^sub>1\<^sub>1*b\<^sub>1\<^sub>2+a\<^sub>1\<^sub>2*b\<^sub>2\<^sub>2+a\<^sub>1\<^sub>3*b\<^sub>3\<^sub>2, a\<^sub>1\<^sub>1*b\<^sub>1\<^sub>3+a\<^sub>1\<^sub>2*b\<^sub>2\<^sub>3+a\<^sub>1\<^sub>3*b\<^sub>3\<^sub>3] # 
   [a\<^sub>2\<^sub>1*b\<^sub>1\<^sub>1+a\<^sub>2\<^sub>2*b\<^sub>2\<^sub>1+a\<^sub>2\<^sub>3*b\<^sub>3\<^sub>1, a\<^sub>2\<^sub>1*b\<^sub>1\<^sub>2+a\<^sub>2\<^sub>2*b\<^sub>2\<^sub>2+a\<^sub>2\<^sub>3*b\<^sub>3\<^sub>2, a\<^sub>2\<^sub>1*b\<^sub>1\<^sub>3+a\<^sub>2\<^sub>2*b\<^sub>2\<^sub>3+a\<^sub>2\<^sub>3*b\<^sub>3\<^sub>3] # 
   [a\<^sub>3\<^sub>1*b\<^sub>1\<^sub>1+a\<^sub>3\<^sub>2*b\<^sub>2\<^sub>1+a\<^sub>3\<^sub>3*b\<^sub>3\<^sub>1, a\<^sub>3\<^sub>1*b\<^sub>1\<^sub>2+a\<^sub>3\<^sub>2*b\<^sub>2\<^sub>2+a\<^sub>3\<^sub>3*b\<^sub>3\<^sub>2, a\<^sub>3\<^sub>1*b\<^sub>1\<^sub>3+a\<^sub>3\<^sub>2*b\<^sub>2\<^sub>3+a\<^sub>3\<^sub>3*b\<^sub>3\<^sub>3] # [])::3 sq_mtx)"
  unfolding sq_mtx_times_eq
  unfolding UNIV_3 by (simp add: sq_mtx_eq_iff)

end