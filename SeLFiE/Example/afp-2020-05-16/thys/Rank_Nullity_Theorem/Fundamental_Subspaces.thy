(*  
    Title:      Fundamental_Subspaces.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Maintainer: Jose Divasón <jose.divasonm at unirioja.es>
*)

section\<open>Fundamental Subspaces\<close>

theory Fundamental_Subspaces
imports 
    Miscellaneous
begin

subsection\<open>The fundamental subspaces of a matrix\<close>

subsubsection\<open>Definitions\<close>

definition left_null_space :: "'a::{semiring_1}^'n^'m => ('a^'m) set"
  where "left_null_space A = {x. x v* A = 0}"

definition null_space :: "'a::{semiring_1}^'n^'m => ('a^'n) set"
  where "null_space A = {x. A *v x = 0}"

definition row_space :: "'a::{field}^'n^'m=>('a^'n) set"
  where "row_space A = vec.span (rows A)"

definition col_space :: "'a::{field}^'n^'m=>('a^'m) set"
  where "col_space A = vec.span (columns A)"

subsubsection\<open>Relationships among them\<close>

lemma left_null_space_eq_null_space_transpose: "left_null_space A = null_space (transpose A)"
  unfolding null_space_def left_null_space_def transpose_vector ..

lemma null_space_eq_left_null_space_transpose: "null_space A = left_null_space (transpose A)" 
  using left_null_space_eq_null_space_transpose[of "transpose A"]
  unfolding transpose_transpose ..

lemma row_space_eq_col_space_transpose:
  fixes A::"'a::{field}^'columns^'rows"
  shows "row_space A = col_space (transpose A)"
  unfolding col_space_def row_space_def columns_transpose[of A] ..

lemma col_space_eq_row_space_transpose:
  fixes A::"'a::{field}^'n^'m"
  shows "col_space A = row_space (transpose A)"
  unfolding col_space_def row_space_def unfolding rows_transpose[of A] ..


subsection\<open>Proving that they are subspaces\<close>

lemma subspace_null_space:
  fixes A::"'a::{field}^'n^'m"
  shows "vec.subspace (null_space A)"
  by (auto simp: vec.subspace_def null_space_def vec.scale vec.add)

lemma subspace_left_null_space:
  fixes A::"'a::{field}^'n^'m"
  shows "vec.subspace (left_null_space A)"
  unfolding left_null_space_eq_null_space_transpose using subspace_null_space .

lemma subspace_row_space:
  shows "vec.subspace (row_space A)" by (metis row_space_def vec.subspace_span)

lemma subspace_col_space:
  shows "vec.subspace (col_space A)" by (metis col_space_def vec.subspace_span)
  
subsection\<open>More useful properties and equivalences\<close>

lemma col_space_eq:
  fixes A::"'a::{field}^'m::{finite, wellorder}^'n"
  shows "col_space A = {y. \<exists>x. A *v x = y}"
proof (unfold col_space_def vec.span_finite[OF finite_columns], auto)
  fix x
  show "A *v x \<in> range (\<lambda>u. \<Sum>v\<in>columns A. u v *s v)" using matrix_vmult_column_sum[of A x] by auto
next
  fix u::"('a, 'n) vec \<Rightarrow> 'a"
  let ?g="\<lambda>y. {i. y=column i A}"
  let ?x="(\<chi> i. if i=(LEAST a. a \<in> ?g (column i A)) then u (column i A) else 0)"
  show "\<exists>x. A *v x = (\<Sum>v\<in>columns A. u v *s v)"
  proof (unfold matrix_mult_sum, rule exI[of _ "?x"], auto)
    have inj: "inj_on ?g (columns A)" unfolding inj_on_def unfolding columns_def by auto
    have union_univ: "\<Union>(?g`(columns A)) = UNIV" unfolding columns_def by auto               
    have "sum (\<lambda>i.(if i = (LEAST a. column i A = column a A) then u (column i A) else 0) *s column i A) UNIV 
        = sum (\<lambda>i. (if i = (LEAST a. column i A = column a A) then u (column i A) else 0) *s column i A) (\<Union>(?g`(columns A)))"
      unfolding union_univ ..
    also have "... = sum (sum (\<lambda>i.(if i = (LEAST a. column i A = column a A) then u (column i A) else 0) *s column i A)) (?g`(columns A))" 
      by (rule sum.Union_disjoint[unfolded o_def], auto)
    also have "... = sum ((sum (\<lambda>i.(if i = (LEAST a. column i A = column a A) then u (column i A) else 0) *s column i A)) \<circ> ?g) 
        (columns A)" by (rule sum.reindex, simp add: inj)
    also have "... = sum (\<lambda>y. u y *s y) (columns A)"
    proof (rule sum.cong, auto)
      fix x
      assume x_in_cols: "x \<in> columns A"
      obtain b where b: "x=column b A" using x_in_cols unfolding columns_def by blast
      let ?f="(\<lambda>i. (if i = (LEAST a. column i A = column a A) then u (column i A) else 0) *s column i A)" 
      have sum_rw: "sum ?f ({i. x = column i A} - {LEAST a. x = column a A}) = 0"
        by (rule sum.neutral, auto)
      have "sum ?f {i. x = column i A} = ?f (LEAST a. x = column a A) + sum ?f ({i. x = column i A} - {LEAST a. x = column a A})" 
        apply (rule sum.remove, auto, rule LeastI_ex) 
        using x_in_cols unfolding columns_def by auto
      also have "... = ?f (LEAST a. x = column a A)" unfolding sum_rw by simp
      also have "... = u x *s x"
      proof (auto, rule LeastI2)
        show "x = column b A" using b .
        fix xa
        assume x: "x = column xa A"
        show "u (column xa A) *s column xa A = u x *s x" unfolding x ..
      next
        assume "(LEAST a. x = column a A) \<noteq> (LEAST a. column (LEAST c. x = column c A) A = column a A)"
        moreover have "(LEAST a. x = column a A) = (LEAST a. column (LEAST c. x = column c A) A = column a A)"
          by (rule Least_equality[symmetric], rule LeastI2, simp_all add: b, rule Least_le, metis (lifting, full_types) LeastI)
        ultimately show "u x = 0" by contradiction
      qed
      finally show " (\<Sum>i | x = column i A. (if i = (LEAST a. column i A = column a A) then u (column i A) else 0) *s column i A) = u x *s x" .
    qed
    finally show "(\<Sum>i\<in>UNIV. (if i = (LEAST a. column i A = column a A) then u (column i A) else 0) *s column i A) = (\<Sum>y\<in>columns A. u y *s y)" .
  qed
qed


corollary col_space_eq':
  fixes A::"'a::{field}^'m::{finite, wellorder}^'n"
  shows "col_space A = range (\<lambda>x. A *v x)"
  unfolding col_space_eq by auto

lemma row_space_eq:
  fixes A::"'a::{field}^'m^'n::{finite, wellorder}"
  shows "row_space A = {w. \<exists>y. (transpose A) *v y = w}"
  unfolding row_space_eq_col_space_transpose col_space_eq ..

lemma null_space_eq_ker:
  fixes f::"('a::field^'n) => ('a^'m)"
  assumes lf: "Vector_Spaces.linear (*s) (*s) f"
  shows "null_space (matrix f) = {x. f x = 0}" 
  unfolding null_space_def using matrix_works [OF lf] by auto

lemma col_space_eq_range:
  fixes f::"('a::field^'n::{finite, wellorder}) \<Rightarrow> ('a^'m)"
  assumes lf: "Vector_Spaces.linear (*s) (*s) f"
  shows "col_space (matrix f) = range f"
  unfolding col_space_eq unfolding matrix_works[OF lf] by blast

lemma null_space_is_preserved:
  fixes A::"'a::{field}^'cols^'rows"
  assumes P: "invertible P"
  shows "null_space (P**A) = null_space A"
  unfolding null_space_def 
  using P matrix_inv_left matrix_left_invertible_ker matrix_vector_mul_assoc matrix_vector_mult_0_right
  by metis

lemma row_space_is_preserved:
  fixes A::"'a::{field}^'cols^'rows::{finite, wellorder}" 
    and P::"'a::{field}^'rows::{finite, wellorder}^'rows::{finite, wellorder}"
  assumes P: "invertible P"
  shows "row_space (P**A) = row_space A"
proof (auto)
  fix w
  assume w: "w \<in> row_space (P**A)"
  from this obtain y where w_By: "w=(transpose (P**A)) *v y" 
    unfolding row_space_eq[of "P ** A" ] by fast
  have "w = (transpose (P**A)) *v y" using w_By .
  also have "... = ((transpose A) ** (transpose P)) *v y" unfolding matrix_transpose_mul ..
  also have "... = (transpose A) *v ((transpose P) *v y)" unfolding matrix_vector_mul_assoc ..
  finally show "w \<in> row_space A" unfolding row_space_eq by blast
next
  fix w
  assume w: "w \<in> row_space A"
  from this obtain y where w_Ay: "w=(transpose A) *v y" unfolding row_space_eq by fast
  have "w = (transpose A) *v y" using w_Ay .
  also have "... = (transpose ((matrix_inv P) ** (P**A))) *v y" 
    by (metis P matrix_inv_left matrix_mul_assoc matrix_mul_lid)
  also have "... = (transpose (P**A) ** (transpose (matrix_inv P))) *v y" 
    unfolding matrix_transpose_mul ..
  also have "... = transpose (P**A) *v (transpose (matrix_inv P) *v y)" 
    unfolding matrix_vector_mul_assoc ..
  finally show "w \<in> row_space (P**A)"  unfolding row_space_eq by blast
qed
end
