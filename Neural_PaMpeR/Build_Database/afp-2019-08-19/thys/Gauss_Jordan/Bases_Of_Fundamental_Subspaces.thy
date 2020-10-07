(*  
    Title:      Bases_Of_Fundamental_Subspaces.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Bases of the four fundamental subspaces\<close>

theory Bases_Of_Fundamental_Subspaces
imports 
  Gauss_Jordan_PA
begin

subsection\<open>Computation of the bases of the fundamental subspaces\<close>

definition "basis_null_space A = {row i (P_Gauss_Jordan (transpose A)) | i. to_nat i \<ge> rank A}"
definition "basis_row_space A = {row i (Gauss_Jordan A) |i. row i (Gauss_Jordan A) \<noteq> 0}"
definition "basis_col_space A = {row i (Gauss_Jordan (transpose A)) |i. row i (Gauss_Jordan (transpose A)) \<noteq> 0}"
definition "basis_left_null_space A = {row i (P_Gauss_Jordan A) | i. to_nat i \<ge> rank A}"

subsection\<open>Relatioships amongst the bases\<close>

lemma basis_null_space_eq_basis_left_null_space_transpose: 
  "basis_null_space A = basis_left_null_space (transpose A)"
unfolding basis_null_space_def
unfolding basis_left_null_space_def
unfolding rank_transpose[of A, symmetric] ..

lemma basis_null_space_transpose_eq_basis_left_null_space:
shows "basis_null_space (transpose A) = basis_left_null_space A"
by (metis transpose_transpose basis_null_space_eq_basis_left_null_space_transpose)

lemma basis_col_space_eq_basis_row_space_transpose:
  "basis_col_space A = basis_row_space (transpose A)"
unfolding basis_col_space_def basis_row_space_def ..

subsection\<open>Code equations\<close>

text\<open>Code equations to make more efficient the computations.\<close>
lemma basis_null_space_code[code]: "basis_null_space A = (let GJ = Gauss_Jordan_PA (transpose A); 
                                                               rank_A = (if A = 0 then 0 else to_nat (GREATEST a. row a (snd GJ) \<noteq> 0) + 1) 
                                                               in {row i (fst GJ) | i. to_nat i \<ge> rank_A})"
unfolding basis_null_space_def Let_def P_Gauss_Jordan_def
unfolding Gauss_Jordan_PA_eq
unfolding rank_transpose[symmetric, of A]
unfolding rank_Gauss_Jordan_code[of "transpose A"]
unfolding Let_def
unfolding transpose_zero ..

lemma basis_row_space_code[code]: "basis_row_space A = (let A' = Gauss_Jordan A in {row i A' |i. row i A' \<noteq> 0})"
unfolding basis_row_space_def Let_def ..

lemma basis_col_space_code[code]: "basis_col_space A = (let A' = Gauss_Jordan (transpose A) in {row i A' |i. row i A' \<noteq> 0})"
unfolding basis_col_space_def Let_def ..

lemma basis_left_null_space_code[code]: "basis_left_null_space A = (let GJ = Gauss_Jordan_PA A; 
                                                               rank_A = (if A = 0 then 0 else to_nat (GREATEST a. row a (snd GJ) \<noteq> 0) + 1)
                                                               in {row i (fst GJ) | i. to_nat i \<ge> rank_A})"
unfolding basis_left_null_space_def Let_def P_Gauss_Jordan_def
unfolding Gauss_Jordan_PA_eq
unfolding rank_Gauss_Jordan_code[of "A"]
unfolding Let_def
unfolding transpose_zero ..

subsection\<open>Demonstrations that they are bases\<close>

text\<open>We prove that we have obtained a basis for each subspace\<close>

lemma independent_basis_left_null_space:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "vec.independent (basis_left_null_space A)"
proof (unfold basis_left_null_space_def, rule vec.independent_mono)
show "vec.independent (rows (P_Gauss_Jordan A))"
  by (metis P_Gauss_Jordan_def det_dependent_rows invertible_det_nz invertible_fst_Gauss_Jordan_PA)
show "{row i (P_Gauss_Jordan A) |i. rank A \<le> to_nat i} \<subseteq> (rows (P_Gauss_Jordan A))" unfolding rows_def by fast
qed

lemma card_basis_left_null_space_eq_dim:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "card (basis_left_null_space A) = vec.dim (left_null_space A)"
proof -
let ?f="\<lambda>n. row (from_nat (n + (rank A))) (P_Gauss_Jordan A)"
have "card (basis_left_null_space A) = card {row i (P_Gauss_Jordan A) | i. to_nat i \<ge> rank A}" unfolding basis_left_null_space_def ..
also have "... = card {..<(vec.dimension TYPE('a) TYPE('rows)) - rank A}"
  proof (rule bij_betw_same_card[symmetric, of ?f], unfold bij_betw_def, rule conjI)
    show "inj_on ?f {..<(vec.dimension TYPE('a) TYPE('rows)) - rank A}" unfolding inj_on_def
      proof (auto, rule ccontr, unfold dimension_vector)
        fix x y
        assume x: "x <CARD('rows) - rank A"
          and y: "y < CARD('rows) - rank A"
          and eq: "row (from_nat (x + rank A)) (P_Gauss_Jordan A) = row (from_nat (y + rank A)) (P_Gauss_Jordan A)"
          and x_not_y: "x \<noteq> y"          
          have "det (P_Gauss_Jordan A) = 0" 
            proof (rule det_identical_rows[OF _ eq])          
              have "(x + rank A) \<noteq> (y + rank A)" using x_not_y x y by simp
              thus "(from_nat (x + rank A)::'rows) \<noteq> from_nat (y + rank A)" by (metis (mono_tags) from_nat_eq_imp_eq less_diff_conv x y)
            qed
          moreover have "invertible (P_Gauss_Jordan A)" by (metis P_Gauss_Jordan_def invertible_fst_Gauss_Jordan_PA)
          ultimately show False  unfolding invertible_det_nz by contradiction
       qed
       show "?f  ` {..<(vec.dimension TYPE('a) TYPE('rows)) - rank A} = {row i (P_Gauss_Jordan A) |i. rank A \<le> to_nat i}"
       proof (unfold image_def dimension_vector, auto, metis le_add2 less_diff_conv to_nat_from_nat_id)
        fix i::'rows
        assume rank_le_i: "rank A \<le> to_nat i"
        show "\<exists>x\<in>{..<CARD('rows) - rank A}. row i (P_Gauss_Jordan A) = row (from_nat (x + rank A)) (P_Gauss_Jordan A)"
            proof (rule bexI[of _ "(to_nat i - rank A)"])
              have "i = (from_nat (to_nat i - rank A + rank A))" by (metis rank_le_i from_nat_to_nat_id le_add_diff_inverse2)
              thus "row i (P_Gauss_Jordan A) = row (from_nat (to_nat i - rank A + rank A)) (P_Gauss_Jordan A)" by presburger
              show "to_nat i - rank A \<in> {..<CARD('rows) - rank A}" using rank_le_i by (metis diff_less_mono lessThan_def mem_Collect_eq to_nat_less_card)
            qed
        qed
        qed
        also have "... = (vec.dimension TYPE('a) TYPE('rows)) - rank A" unfolding card_lessThan ..
        also have "... = vec.dim (null_space (transpose A))" unfolding dim_null_space rank_transpose ..
        also have "... = vec.dim (left_null_space A)" unfolding left_null_space_eq_null_space_transpose ..
        finally show ?thesis .
qed


lemma basis_left_null_space_in_left_null_space:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "basis_left_null_space A \<subseteq> left_null_space A"
  proof (unfold basis_left_null_space_def left_null_space_def, auto)
    fix i::'rows
    assume rank_le_i: " rank A \<le> to_nat i"
    have "row i (P_Gauss_Jordan A) v* A = ((P_Gauss_Jordan A) $ i) v* A" unfolding row_def vec_nth_inverse ..
    also have "... = ((P_Gauss_Jordan A) ** A) $ i" unfolding row_matrix_matrix_mult by simp
    also have "... = (Gauss_Jordan A) $ i" unfolding P_Gauss_Jordan_def Gauss_Jordan_PA_eq[symmetric] using fst_Gauss_Jordan_PA by metis
    also have "... = 0" by (rule rank_less_row_i_imp_i_is_zero[OF rank_le_i])
    finally show "row i (P_Gauss_Jordan A) v* A = 0" .
qed


lemma left_null_space_subset_span_basis:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows  "left_null_space A \<subseteq> vec.span (basis_left_null_space A)"
proof (rule vec.card_ge_dim_independent)
show "basis_left_null_space A \<subseteq> left_null_space A" by (rule basis_left_null_space_in_left_null_space)
show "vec.independent (basis_left_null_space A)" by (rule independent_basis_left_null_space)
show "vec.dim (left_null_space A) \<le> card (basis_left_null_space A)"
  proof -
    have "{x. x v* A = 0} = {x. (transpose A) *v x = 0}" by (metis transpose_vector)
    thus ?thesis using card_basis_left_null_space_eq_dim by (metis order_refl)
  qed
qed

corollary basis_left_null_space:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "vec.independent (basis_left_null_space A) \<and> 
       left_null_space A = vec.span (basis_left_null_space A)"
by (metis basis_left_null_space_in_left_null_space independent_basis_left_null_space 
  left_null_space_subset_span_basis vec.span_subspace subspace_left_null_space)


corollary basis_null_space:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "vec.independent (basis_null_space A) \<and> 
       null_space A = vec.span (basis_null_space A)"
unfolding basis_null_space_eq_basis_left_null_space_transpose
unfolding null_space_eq_left_null_space_transpose
by (rule basis_left_null_space)


lemma basis_row_space_subset_row_space:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "basis_row_space A \<subseteq> row_space A"
  proof -
    have "basis_row_space A = {row i (Gauss_Jordan A) |i. row i (Gauss_Jordan A) \<noteq> 0}" unfolding basis_row_space_def ..
    also have "... \<subseteq> row_space (Gauss_Jordan A)"
      proof (unfold row_space_def, clarify)
        fix i assume "row i (Gauss_Jordan A) \<noteq> 0" 
        show "row i (Gauss_Jordan A) \<in> vec.span (rows (Gauss_Jordan A))"
          using rows_def vec.span_base by auto
      qed
      also have "... = row_space A" unfolding Gauss_Jordan_PA_eq[symmetric] unfolding fst_Gauss_Jordan_PA[symmetric]
      by (rule row_space_is_preserved[OF invertible_fst_Gauss_Jordan_PA])
      finally show ?thesis .
qed


lemma row_space_subset_span_basis_row_space:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "row_space A \<subseteq> vec.span (basis_row_space A)"
proof (rule vec.card_ge_dim_independent)
show "basis_row_space A \<subseteq> row_space A" by (rule basis_row_space_subset_row_space)
show "vec.independent (basis_row_space A)" unfolding basis_row_space_def by (rule independent_not_zero_rows_rref[OF rref_Gauss_Jordan])
show "vec.dim (row_space A) \<le> card (basis_row_space A)"
unfolding basis_row_space_def
using rref_rank[OF rref_Gauss_Jordan, of A] unfolding row_rank_def[symmetric] rank_def[symmetric] rank_Gauss_Jordan[symmetric] by fastforce
qed



lemma basis_row_space:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "vec.independent (basis_row_space A)
  \<and> vec.span (basis_row_space A) = row_space A"
proof (rule conjI)
  show "vec.independent (basis_row_space A)" unfolding basis_row_space_def using independent_not_zero_rows_rref[OF rref_Gauss_Jordan] .
  show "vec.span (basis_row_space A) = row_space A"
    proof (rule vec.span_subspace)
      show "basis_row_space A \<subseteq> row_space A" by (rule basis_row_space_subset_row_space)
      show "row_space A \<subseteq> vec.span (basis_row_space A)" by (rule row_space_subset_span_basis_row_space)
      show "vec.subspace (row_space A)" by (rule subspace_row_space)
    qed
qed
 
corollary basis_col_space:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "vec.independent (basis_col_space A)
  \<and> vec.span (basis_col_space A) = col_space A"
unfolding col_space_eq_row_space_transpose basis_col_space_eq_basis_row_space_transpose
by (rule basis_row_space)

end
