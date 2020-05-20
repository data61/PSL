(*  
    Title:      QR_Decomposition_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>QR Decomposition over iarrays\<close>

theory QR_Decomposition_IArrays 
imports 
  Gram_Schmidt_IArrays
begin

subsection\<open>QR Decomposition refinement over iarrays\<close>

definition "norm_iarray A = sqrt (A \<bullet>i A)"

definition "divide_by_norm_iarray A  = tabulate2 (nrows_iarray A) (ncols_iarray A)
  (\<lambda>a b. ((1/norm_iarray (column_iarray b A)) *\<^sub>R (column_iarray b A)) !! a)"

definition "QR_decomposition_iarrays A = (let Q = divide_by_norm_iarray (Gram_Schmidt_matrix_iarrays A) 
  in (Q, transpose_iarray Q **i A))"

lemma vec_to_iarray_norm[code_unfold]:
  shows "(norm A) = norm_iarray (vec_to_iarray A)" 
  unfolding norm_eq_sqrt_inner norm_iarray_def
  unfolding vec_to_iarray_inner ..


lemma matrix_to_iarray_divide_by_norm[code_unfold]:
  fixes A::"real^'cols::{mod_type}^'rows::{mod_type}"
  shows "matrix_to_iarray (divide_by_norm A) = divide_by_norm_iarray (matrix_to_iarray A)"
proof (unfold iarray_exhaust2 list_eq_iff_nth_eq, rule conjI, auto, unfold IArray.sub_def[symmetric] IArray.length_def[symmetric])
  show"IArray.length (matrix_to_iarray (divide_by_norm A)) = IArray.length (divide_by_norm_iarray (matrix_to_iarray A))"
    unfolding matrix_to_iarray_def divide_by_norm_iarray_def tabulate2_def unfolding nrows_iarray_def by auto
  fix i assume i:"i < IArray.length (matrix_to_iarray (divide_by_norm A))"
  show "IArray.length (matrix_to_iarray (divide_by_norm A) !! i) = IArray.length (divide_by_norm_iarray (matrix_to_iarray A) !! i)"
    unfolding matrix_to_iarray_def divide_by_norm_iarray_def tabulate2_def 
    unfolding nrows_iarray_def ncols_iarray_def o_def
  proof -
    have f1: "i < card (UNIV::'rows set)" by (metis i length_eq_card_rows)
    have "\<And>x\<^sub>4. vec_to_iarray x\<^sub>4 = IArray (map (\<lambda>uua. x\<^sub>4 $ (from_nat uua::'cols)::real) [0..<card (UNIV::'cols set)])" by (simp add: vec_to_iarray_def)
    hence "0 < card (UNIV::'rows set) \<and> length (IArray.list_of (IArray (map (\<lambda>R. IArray.of_fun (\<lambda>Ra. ((1 / norm_iarray (column_iarray Ra (IArray (map (\<lambda>R. vec_to_iarray (A $ from_nat R)) [0..<card (UNIV::'rows set)])))) *\<^sub>R column_iarray Ra (IArray (map (\<lambda>R. vec_to_iarray (A $ from_nat R)) [0..<card (UNIV::'rows set)]))) !! R) (card (UNIV::'cols set))) [0..<card (UNIV::'rows set)]) !! i)) = length (IArray.list_of (IArray (map (\<lambda>R. vec_to_iarray (divide_by_norm A $ from_nat R)) [0..<card (UNIV::'rows set)]) !! i))" using f1 by auto
    thus "IArray.length (IArray (map (\<lambda>x. vec_to_iarray (divide_by_norm A $ from_nat x)) [0..<card (UNIV::'rows set)]) !! i) = IArray.length (IArray.of_fun (\<lambda>i. IArray.of_fun (\<lambda>b. ((1 / norm_iarray (column_iarray b (IArray (map (\<lambda>x. vec_to_iarray (A $ from_nat x)) [0..<card (UNIV::'rows set)])))) *\<^sub>R column_iarray b (IArray (map (\<lambda>x. vec_to_iarray (A $ from_nat x)) [0..<card (UNIV::'rows set)]))) !! i) (IArray.length (IArray (map (\<lambda>x. vec_to_iarray (A $ from_nat x)) [0..<card (UNIV::'rows set)]) !! 0))) (IArray.length (IArray (map (\<lambda>x. vec_to_iarray (A $ from_nat x)) [0..<card (UNIV::'rows set)]))) !! i)" by (simp add: vec_to_iarray_def)
  qed
  fix ia assume ia: "ia < IArray.length (matrix_to_iarray (divide_by_norm A) !! i)"
  have i_nrows: "i<nrows A" using i unfolding matrix_to_iarray_def nrows_def by auto
  have ia_ncols: "ia<ncols A" using ia unfolding matrix_to_iarray_def o_def vec_to_iarray_def ncols_def
    by (auto, metis (no_types) Ex_list_of_length i_nrows length_map list_of.simps map_nth nrows_def nth_map)
  have i_nrows_iarray: "i<nrows_iarray (matrix_to_iarray A)" using i_nrows by (metis matrix_to_iarray_nrows)
  have ia_ncols_iarray: "ia<ncols_iarray (matrix_to_iarray A)" using ia_ncols by (metis matrix_to_iarray_ncols)
  show "matrix_to_iarray (divide_by_norm A) !! i !! ia 
    = divide_by_norm_iarray (matrix_to_iarray A) !! i !! ia"
    unfolding divide_by_norm_def divide_by_norm_iarray_def 
    unfolding matrix_to_iarray_nth[of _ "from_nat i::'rows" "from_nat ia::'cols",
      unfolded to_nat_from_nat_id[OF i_nrows[unfolded nrows_def]]
      to_nat_from_nat_id[OF ia_ncols[unfolded ncols_def]]]
    unfolding tabulate2_def
    unfolding of_fun_nth[OF i_nrows_iarray]
    unfolding of_fun_nth[OF ia_ncols_iarray]
    unfolding vec_to_iarray_column'[OF ia_ncols, symmetric]
    unfolding vec_to_iarray_norm[symmetric]
    unfolding vector_scaleR_component
    unfolding vec_to_iarray_scaleR[symmetric]
    unfolding vec_to_iarray_nth[OF i_nrows[unfolded nrows_def]]
    unfolding normalize_def
    by auto
qed


lemma matrix_to_iarray_fst_QR_decomposition[code_unfold]:
  shows "matrix_to_iarray (fst (QR_decomposition A)) = fst (QR_decomposition_iarrays (matrix_to_iarray A))"
proof (unfold iarray_exhaust2 list_eq_iff_nth_eq, rule conjI, auto, unfold IArray.sub_def[symmetric] IArray.length_def[symmetric])
  fix i ia
  show "IArray.length (matrix_to_iarray (fst (QR_decomposition A))) 
    = IArray.length (fst (QR_decomposition_iarrays (matrix_to_iarray A)))"
    and "IArray.length (matrix_to_iarray (fst (QR_decomposition A)) !! i) 
    = IArray.length (fst (QR_decomposition_iarrays (matrix_to_iarray A)) !! i)"
    and "matrix_to_iarray (fst (QR_decomposition A)) !! i !! ia 
    = fst (QR_decomposition_iarrays (matrix_to_iarray A)) !! i !! ia"
    unfolding QR_decomposition_def QR_decomposition_iarrays_def Let_def fst_conv
    unfolding matrix_to_iarray_divide_by_norm
    unfolding matrix_to_iarray_Gram_Schmidt_matrix by rule+
qed


lemma matrix_to_iarray_snd_QR_decomposition[code_unfold]:
  shows "matrix_to_iarray (snd (QR_decomposition A)) = snd (QR_decomposition_iarrays (matrix_to_iarray A))"
proof (unfold iarray_exhaust2 list_eq_iff_nth_eq, rule conjI, auto, unfold IArray.sub_def[symmetric] IArray.length_def[symmetric])
  fix i ia
  show "IArray.length (matrix_to_iarray (snd (QR_decomposition A)))
    = IArray.length (snd (QR_decomposition_iarrays (matrix_to_iarray A)))"
    and "IArray.length (matrix_to_iarray (snd (QR_decomposition A)) !! i) 
    = IArray.length (snd (QR_decomposition_iarrays (matrix_to_iarray A)) !! i)" 
    and "matrix_to_iarray (snd (QR_decomposition A)) !! i !! ia 
    = snd (QR_decomposition_iarrays (matrix_to_iarray A)) !! i !! ia"
    unfolding QR_decomposition_iarrays_def QR_decomposition_def Let_def snd_conv
    unfolding matrix_to_iarray_matrix_matrix_mult
    unfolding matrix_to_iarray_transpose
    unfolding matrix_to_iarray_divide_by_norm
    unfolding matrix_to_iarray_Gram_Schmidt_matrix by rule+
qed

definition "matrix_to_iarray_pair X = (matrix_to_iarray (fst X), matrix_to_iarray (snd X))"

lemma matrix_to_iarray_QR_decomposition[code_unfold]:
  shows "matrix_to_iarray_pair (QR_decomposition A) =  QR_decomposition_iarrays (matrix_to_iarray A)"
  unfolding matrix_to_iarray_pair_def
  unfolding matrix_to_iarray_fst_QR_decomposition
  unfolding matrix_to_iarray_snd_QR_decomposition by simp
end
