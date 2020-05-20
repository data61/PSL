(*  
    Title:      Inverse_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Inverse of a matrix using the Gauss Jordan algorithm over nested IArrays\<close>

theory Inverse_IArrays
imports 
  Inverse
  Gauss_Jordan_PA_IArrays
begin

subsection\<open>Definitions\<close>

definition "invertible_iarray A = (rank_iarray A = nrows_iarray A)"
definition "inverse_matrix_iarray A = (if invertible_iarray A then Some(fst(Gauss_Jordan_iarrays_PA A)) else None)"
definition "matrix_to_iarray_option A = (if A \<noteq> None then Some (matrix_to_iarray (the A)) else None)"

subsection\<open>Some lemmas and code generation\<close>
lemma matrix_inv_Gauss_Jordan_iarrays_PA:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
assumes inv_A: "invertible A"
shows "matrix_to_iarray (matrix_inv A) = fst (Gauss_Jordan_iarrays_PA (matrix_to_iarray A))"
by (metis inv_A matrix_inv_Gauss_Jordan_PA matrix_to_iarray_fst_Gauss_Jordan_PA)

lemma matrix_to_iarray_invertible[code_unfold]:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "invertible A = invertible_iarray (matrix_to_iarray A)"
unfolding invertible_iarray_def invertible_eq_full_rank[of A] matrix_to_iarray_rank matrix_to_iarray_nrows ..

lemma matrix_to_iarray_option_inverse_matrix:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "matrix_to_iarray_option (inverse_matrix A) = (inverse_matrix_iarray (matrix_to_iarray A))"
proof (unfold inverse_matrix_def, auto)
assume inv_A: "invertible A"
show "matrix_to_iarray_option (Some (matrix_inv A)) = inverse_matrix_iarray (matrix_to_iarray A)"
unfolding matrix_to_iarray_option_def unfolding inverse_matrix_iarray_def using inv_A unfolding matrix_to_iarray_invertible
using matrix_inv_Gauss_Jordan_iarrays_PA[OF inv_A] by auto
next
assume not_inv_A: "\<not> invertible A"
show "matrix_to_iarray_option None = inverse_matrix_iarray (matrix_to_iarray A)"
unfolding matrix_to_iarray_option_def inverse_matrix_iarray_def
using not_inv_A unfolding matrix_to_iarray_invertible by simp
qed

lemma matrix_to_iarray_option_inverse_matrix_code[code_unfold]:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "matrix_to_iarray_option (inverse_matrix A) = (let matrix_to_iarray_A = matrix_to_iarray A; GJ = Gauss_Jordan_iarrays_PA matrix_to_iarray_A
  in if nrows_iarray matrix_to_iarray_A = length [x\<leftarrow>IArray.list_of (snd GJ) . \<not> is_zero_iarray x] then Some (fst GJ) else None)"
unfolding matrix_to_iarray_option_inverse_matrix
unfolding inverse_matrix_iarray_def
unfolding invertible_iarray_def
unfolding rank_iarrays_code
unfolding Let_def
unfolding matrix_to_iarray_snd_Gauss_Jordan_PA[symmetric]
unfolding Gauss_Jordan_PA_eq
unfolding matrix_to_iarray_Gauss_Jordan by presburger


lemma[code_unfold]:
shows "inverse_matrix_iarray A = (let A' = (Gauss_Jordan_iarrays_PA A); nrows = IArray.length A in 
                                (if length [x\<leftarrow>IArray.list_of (snd A') . \<not> is_zero_iarray x] = nrows 
                                then Some (fst A') else None))"
unfolding inverse_matrix_iarray_def invertible_iarray_def rank_iarrays_code Let_def
unfolding nrows_iarray_def snd_Gauss_Jordan_iarrays_PA_eq ..


end
