(*  
    Title:      Bases_Of_Fundamental_Subspaces_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Bases of the four fundamental subspaces over IArrays\<close>

theory Bases_Of_Fundamental_Subspaces_IArrays
imports 
  Bases_Of_Fundamental_Subspaces
  Gauss_Jordan_PA_IArrays  
begin

subsection\<open>Computation of bases of the fundamental subspaces using IArrays\<close>

text\<open>We have made the definitions as efficient as possible.\<close>
definition "basis_left_null_space_iarrays A 
  = (let GJ = Gauss_Jordan_iarrays_PA A;
          rank_A = length [x\<leftarrow>IArray.list_of (snd GJ) . \<not> is_zero_iarray x]
          in set (map (\<lambda>i. row_iarray i (fst GJ)) [(rank_A)..<(nrows_iarray A)]))"
definition "basis_null_space_iarrays A
    = (let GJ= Gauss_Jordan_iarrays_PA (transpose_iarray A);
          rank_A = length [x\<leftarrow>IArray.list_of (snd GJ) . \<not> is_zero_iarray x]
          in set (map (\<lambda>i. row_iarray i (fst GJ)) [(rank_A)..<(ncols_iarray A)]))"
definition "basis_row_space_iarrays A = 
  (let GJ= Gauss_Jordan_iarrays A;
       rank_A = length [x\<leftarrow>IArray.list_of (GJ) . \<not> is_zero_iarray x]
       in set (map (\<lambda>i. row_iarray i (GJ)) [0..<rank_A]))"
definition "basis_col_space_iarrays A = basis_row_space_iarrays (transpose_iarray A)"


text\<open>The following lemmas make easier the proofs of equivalence between abstract versions and concrete versions.
      They are false if we remove \<open>matrix_to_iarray\<close>\<close>

lemma basis_null_space_iarrays_eq:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "basis_null_space_iarrays (matrix_to_iarray A) 
  = set (map (\<lambda>i. row_iarray i (fst (Gauss_Jordan_iarrays_PA (transpose_iarray (matrix_to_iarray A))))) [(rank_iarray (matrix_to_iarray A))..<(ncols_iarray (matrix_to_iarray A))])"
unfolding basis_null_space_iarrays_def Let_def
unfolding matrix_to_iarray_rank[symmetric, of A]
unfolding rank_transpose[symmetric, of A] 
unfolding matrix_to_iarray_rank
unfolding rank_iarrays_code
unfolding matrix_to_iarray_transpose[symmetric] 
unfolding snd_Gauss_Jordan_iarrays_PA_eq ..

lemma basis_row_space_iarrays_eq:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "basis_row_space_iarrays (matrix_to_iarray A) = set (map (\<lambda>i. row_iarray i (Gauss_Jordan_iarrays (matrix_to_iarray A))) [0..<(rank_iarray (matrix_to_iarray A))])"
unfolding basis_row_space_iarrays_def Let_def rank_iarrays_code ..

lemma basis_left_null_space_iarrays_eq:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "basis_left_null_space_iarrays (matrix_to_iarray A) = basis_null_space_iarrays (transpose_iarray (matrix_to_iarray A))"
unfolding basis_left_null_space_iarrays_def
unfolding basis_null_space_iarrays_def Let_def
unfolding matrix_to_iarray_transpose[symmetric]
unfolding transpose_transpose
unfolding matrix_to_iarray_ncols[symmetric]
unfolding ncols_transpose
unfolding matrix_to_iarray_nrows ..

subsection\<open>Code equations\<close>

lemma vec_to_iarray_basis_null_space[code_unfold]:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows  "vec_to_iarray` (basis_null_space A) = basis_null_space_iarrays (matrix_to_iarray A)"
proof (unfold basis_null_space_def basis_null_space_iarrays_eq, auto, unfold image_def, auto)
fix i::'cols
assume rank_le_i: "rank A \<le> to_nat i"
show "\<exists>x\<in>{rank_iarray (matrix_to_iarray A)..<ncols_iarray (matrix_to_iarray A)}.
vec_to_iarray (row i (P_Gauss_Jordan (transpose A))) = row_iarray x (fst (Gauss_Jordan_iarrays_PA (transpose_iarray (matrix_to_iarray A))))"
proof (rule bexI[of _ "to_nat i"])
show "to_nat i \<in> {rank_iarray (matrix_to_iarray A)..<ncols_iarray (matrix_to_iarray A)}"
  unfolding matrix_to_iarray_ncols[symmetric]
  using rank_le_i to_nat_less_card[of i]
  unfolding matrix_to_iarray_rank ncols_def by fastforce
show "vec_to_iarray (row i (P_Gauss_Jordan (transpose A))) 
    = row_iarray (to_nat i) (fst (Gauss_Jordan_iarrays_PA (transpose_iarray (matrix_to_iarray A))))"
unfolding matrix_to_iarray_transpose[symmetric]
unfolding matrix_to_iarray_fst_Gauss_Jordan_PA[symmetric]
unfolding P_Gauss_Jordan_def
unfolding vec_to_iarray_row ..
qed
next
fix i assume rank_le_i: "rank_iarray (matrix_to_iarray A) \<le> i"
        and i_less_nrows: "i < ncols_iarray (matrix_to_iarray A)"
hence i_less_card:"i < CARD ('cols)"
  unfolding matrix_to_iarray_ncols[symmetric] ncols_def by simp
show "\<exists>x. (\<exists>i. x = row i (P_Gauss_Jordan (transpose A)) \<and> rank A \<le> to_nat i) \<and>
            row_iarray i (fst (Gauss_Jordan_iarrays_PA (transpose_iarray (matrix_to_iarray A)))) = vec_to_iarray x"
proof (rule exI[of _ "row (from_nat i) (P_Gauss_Jordan (transpose A))"], rule conjI)
show "\<exists>ia. row (from_nat i) (P_Gauss_Jordan (transpose A)) = row ia (P_Gauss_Jordan (transpose A)) \<and>
         rank A \<le> to_nat ia"
         by (rule exI[of _ "from_nat i"],simp add: rank_le_i to_nat_from_nat_id[OF i_less_card] matrix_to_iarray_rank)
show "row_iarray i (fst (Gauss_Jordan_iarrays_PA (transpose_iarray (matrix_to_iarray A)))) =
    vec_to_iarray (row (from_nat i) (P_Gauss_Jordan (transpose A)))"
unfolding matrix_to_iarray_transpose[symmetric]
unfolding matrix_to_iarray_fst_Gauss_Jordan_PA[symmetric]
unfolding P_Gauss_Jordan_def
unfolding vec_to_iarray_row to_nat_from_nat_id[OF i_less_card] ..
qed
qed


corollary vec_to_iarray_basis_left_null_space[code_unfold]:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "vec_to_iarray` (basis_left_null_space A) = basis_left_null_space_iarrays (matrix_to_iarray A)"
proof -
have rw: "basis_left_null_space A = basis_null_space (transpose A)"
by (metis transpose_transpose basis_null_space_eq_basis_left_null_space_transpose)
show ?thesis unfolding rw unfolding basis_left_null_space_iarrays_eq
using vec_to_iarray_basis_null_space[of "transpose A"]
unfolding matrix_to_iarray_transpose[symmetric] .
qed


lemma vec_to_iarray_basis_row_space[code_unfold]:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows  "vec_to_iarray` (basis_row_space A) = basis_row_space_iarrays (matrix_to_iarray A)"
proof (unfold basis_row_space_def basis_row_space_iarrays_eq, auto, unfold image_def, auto)
fix i
assume i: "row i (Gauss_Jordan A) \<noteq> 0"
show "\<exists>x\<in>{0..<rank_iarray (matrix_to_iarray A)}. vec_to_iarray (row i (Gauss_Jordan A)) = row_iarray x (Gauss_Jordan_iarrays (matrix_to_iarray A))"
  proof (rule bexI[of _ "to_nat i"])
    show "vec_to_iarray (row i (Gauss_Jordan A)) = row_iarray (to_nat i) (Gauss_Jordan_iarrays (matrix_to_iarray A))"
      unfolding vec_to_iarray_row matrix_to_iarray_Gauss_Jordan ..
    show "to_nat i \<in> {0..<rank_iarray (matrix_to_iarray A)}"
    by (auto, unfold matrix_to_iarray_rank[symmetric],
      metis (full_types) i iarray_to_vec_vec_to_iarray not_less rank_less_row_i_imp_i_is_zero row_iarray_def vec_matrix vec_to_iarray_row)
  qed
next
fix i
assume i: "i < rank_iarray (matrix_to_iarray A)"
hence i_less_rank: "i < rank A" unfolding matrix_to_iarray_rank .  
show "\<exists>x. (\<exists>i. x = row i (Gauss_Jordan A) \<and> row i (Gauss_Jordan A) \<noteq> 0) \<and> row_iarray i (Gauss_Jordan_iarrays (matrix_to_iarray A)) = vec_to_iarray x"
proof (rule exI[of _ "row (from_nat i) (Gauss_Jordan A)"], rule conjI)
have not_zero_i: "\<not> is_zero_row (from_nat i) (Gauss_Jordan A)"
 proof (unfold is_zero_row_def, rule greatest_ge_nonzero_row')
 show "reduced_row_echelon_form_upt_k (Gauss_Jordan A) (ncols (Gauss_Jordan A))" by (metis rref_Gauss_Jordan rref_implies_rref_upt)
 have A_not_0: "A \<noteq> 0" using i_less_rank by (metis less_nat_zero_code rank_0)
 hence Gauss_not_0: "Gauss_Jordan A \<noteq> 0" by (metis Gauss_Jordan_not_0)
have "i \<le> to_nat (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))" using i_less_rank unfolding rank_eq_suc_to_nat_greatest[OF A_not_0] by auto
thus "from_nat i \<le> (GREATEST m. \<not> is_zero_row_upt_k m (ncols (Gauss_Jordan A)) (Gauss_Jordan A))" unfolding is_zero_row_def[symmetric] by (metis leD not_le_imp_less to_nat_le)
 show "\<not> (\<forall>a. is_zero_row_upt_k a (ncols (Gauss_Jordan A)) (Gauss_Jordan A))" using Gauss_not_0 unfolding is_zero_row_def[symmetric] is_zero_row_def' by (metis vec_eq_iff zero_index)
qed 
have i_less_card: "i<CARD('rows)" using i_less_rank rank_le_nrows[of A] unfolding nrows_def by simp
show "\<exists>ia. row (from_nat i) (Gauss_Jordan A) = row ia (Gauss_Jordan A) \<and> row ia (Gauss_Jordan A) \<noteq> 0"
  apply (rule exI[of _ "from_nat i"], simp) using not_zero_i unfolding row_def is_zero_row_def' vec_nth_inverse by auto
show "row_iarray i (Gauss_Jordan_iarrays (matrix_to_iarray A)) = vec_to_iarray (row (from_nat i) (Gauss_Jordan A))"
unfolding matrix_to_iarray_Gauss_Jordan[symmetric] vec_to_iarray_row to_nat_from_nat_id[OF i_less_card] by rule
qed
qed


corollary vec_to_iarray_basis_col_space[code_unfold]:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows  "vec_to_iarray` (basis_col_space A) = basis_col_space_iarrays (matrix_to_iarray A)"
unfolding basis_col_space_eq_basis_row_space_transpose basis_col_space_iarrays_def
unfolding matrix_to_iarray_transpose[symmetric]
unfolding vec_to_iarray_basis_row_space ..

end
