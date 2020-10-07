(* 
    Title:      Code_Cayley_Hamilton_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Code Cayley Hamilton\<close>

theory Code_Cayley_Hamilton_IArrays
  imports 
  Cayley_Hamilton.Cayley_Hamilton
  Echelon_Form_Det_IArrays
begin


subsection\<open>Implementations over immutable arrays of some definitions 
  presented in the Cayley-Hamilton development\<close>

definition scalar_matrix_mult_iarrays :: "('a::ab_semigroup_mult) \<Rightarrow> ('a iarray iarray) \<Rightarrow> ('a iarray iarray)" 
  (infixl "*ssi" 70) where "c *ssi A = tabulate2 (nrows_iarray A) (ncols_iarray A) (% i j. c * (A !! i !! j))"

definition "minorM_iarrays A i j = tabulate2  (nrows_iarray A) (ncols_iarray A) 
  (%k l. if k = i \<and> l = j then 1 else if k = i \<or> l = j then 0 else A !! k !! l)"
definition "cofactor_iarrays A i j = det_iarrays_rings (minorM_iarrays A i j)"
definition "cofactorM_iarrays A = tabulate2 (nrows_iarray A) (nrows_iarray A) 
  (%i j. cofactor_iarrays A i j)"
definition "adjugate_iarrays A = transpose_iarray (cofactorM_iarrays A)"

lemma matrix_to_iarray_scalar_matrix_mult[code_unfold]: 
  "matrix_to_iarray (k *k A) = k *ssi (matrix_to_iarray A)"
proof -
  have n_rw: "nrows_iarray (IArray (map (\<lambda>x. vec_to_iarray (A $ from_nat x)) [0..<CARD('c)])) 
    = CARD('c)" unfolding nrows_iarray_def by auto
  have n_rw2: "nrows_iarray (IArray (map (\<lambda>x. IArray (map (\<lambda>i. A $ from_nat x $ from_nat i) 
    [0..<CARD('b)])) [0..<CARD('c)])) = CARD('c)"   unfolding nrows_iarray_def by auto
  have n_rw3: "ncols_iarray (IArray (map (\<lambda>x. IArray (map (\<lambda>i. A $ from_nat x $ from_nat i) 
    [0..<CARD('b)])) [0..<CARD('c)])) = CARD('b)"
    unfolding ncols_iarray_def by auto
  show ?thesis
    unfolding matrix_to_iarray_def o_def matrix_scalar_mult_def scalar_matrix_mult_iarrays_def
      tabulate2_def vec_to_iarray_def 
    by (simp add: n_rw n_rw2 n_rw3)
qed

lemma matrix_to_iarray_minorM[code_unfold]: 
  "matrix_to_iarray (minorM A i j) = minorM_iarrays (matrix_to_iarray A) (to_nat i) (to_nat j)"
proof -
  have n_rw: "nrows_iarray (IArray (map (\<lambda>x. IArray (map (\<lambda>i. A $ from_nat x $ from_nat i) 
    [0..<CARD('b)])) [0..<CARD('c)])) = CARD('c)"
    unfolding nrows_iarray_def by auto
  have n_rw2: "ncols_iarray (IArray (map (\<lambda>x. IArray (map (\<lambda>i. A $ from_nat x $ from_nat i) 
    [0..<CARD('b)])) [0..<CARD('c)])) = CARD('b)"
    unfolding ncols_iarray_def by simp
  show ?thesis
    unfolding matrix_to_iarray_def o_def
    minorM_def minorM_iarrays_def
    tabulate2_def vec_to_iarray_def 
    by (auto simp add: n_rw n_rw2 to_nat_from_nat_id)
qed

lemma matrix_to_iarray_cofactor[code_unfold]: 
  "(cofactor A i j) = cofactor_iarrays (matrix_to_iarray A) (to_nat i) (to_nat j)"
   unfolding o_def cofactor_iarrays_def cofactor_def cofactorM_def
   unfolding matrix_to_iarray_minorM[symmetric]
   unfolding matrix_to_iarray_det_euclidean_ring[symmetric] by simp

lemma matrix_to_iarray_cofactorM[code_unfold]: 
  "matrix_to_iarray (cofactorM A) = cofactorM_iarrays (matrix_to_iarray A)"
proof -
  have n_rw: "nrows_iarray (IArray (map (\<lambda>x. IArray (map (\<lambda>i. A $ from_nat x $ from_nat i) 
    [0..<CARD('b)])) [0..<CARD('b)])) = CARD('b)"
    unfolding nrows_iarray_def by simp
  show ?thesis
    unfolding cofactorM_iarrays_def tabulate2_def cofactorM_def
    by (auto simp add: n_rw matrix_to_iarray_cofactor
        matrix_to_iarray_def o_def vec_to_iarray_def to_nat_from_nat_id)
qed

lemma matrix_to_iarray_adjugate[code_unfold]: 
  "matrix_to_iarray (adjugate A) = adjugate_iarrays (matrix_to_iarray A)"
  unfolding adjugate_def adjugate_iarrays_def
  unfolding matrix_to_iarray_cofactorM[symmetric]
  unfolding matrix_to_iarray_transpose[symmetric] ..

end
