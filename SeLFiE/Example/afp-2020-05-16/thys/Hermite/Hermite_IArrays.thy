(*  
    Title:      Hermite_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Hermite Normal Form refined to immutable arrays\<close>

theory Hermite_IArrays
imports 
  Hermite
  Echelon_Form.Echelon_Form_IArrays
begin

subsection\<open>Definition of the algorithm over immutable arrays\<close>

primrec Hermite_reduce_above_iarrays :: "'a::unique_euclidean_ring iarray iarray \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> 'a iarray iarray"
where "Hermite_reduce_above_iarrays A 0 i j res  = A"
    | "Hermite_reduce_above_iarrays A (Suc n) i j res  = (let i'=n; 
    Aij = A !! i !! j;
    Ai'j = A !! i' !! j
    in 
    Hermite_reduce_above_iarrays (row_add_iarray A  i' i (((res Aij (Ai'j)) - (Ai'j)) div Aij)) n i j res)"

definition "Hermite_of_row_i_iarray ass res A i = (
  if is_zero_iarray (A !! i) 
     then A 
  else
    let j = least_non_zero_position_of_vector (A !! i); Aij= (A !! i !! j);
    A' = mult_row_iarray A i ((ass Aij) div Aij)
    in Hermite_reduce_above_iarrays A' i i j res)"

definition "Hermite_of_upt_row_i_iarrays A i ass res  = foldl (Hermite_of_row_i_iarray ass res) A [0..<i]"

definition "Hermite_of_iarrays A ass res bezout = 
  (let A'= echelon_form_of_iarrays A bezout 
  in Hermite_of_upt_row_i_iarrays A' (nrows_iarray A) ass res)"

subsection\<open>Proving the equivalence between definitions of both representations\<close>

lemma matrix_to_iarray_Hermite_reduce_above:
  fixes A::"'a::{unique_euclidean_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes "n<nrows A"
  shows "matrix_to_iarray (Hermite_reduce_above A n i j res) 
  = Hermite_reduce_above_iarrays (matrix_to_iarray A) n (to_nat i) (to_nat j) res"
  using assms
proof (induct n arbitrary: A)
  case 0 thus ?case by auto
next
  case (Suc n)
  have n: "n<nrows A"
    using Suc.prems unfolding nrows_def by simp
  obtain a::'rows where n_tna: "n = to_nat a"
    by (metis Suc.prems Suc_lessD nrows_def to_nat_from_nat_id)
  show ?case 
    unfolding Hermite_reduce_above.simps
    unfolding Hermite_reduce_above_iarrays.simps
    unfolding Let_def sub_def[symmetric]
    unfolding n_tna 
    unfolding matrix_to_iarray_row_add[symmetric] from_nat_to_nat_id 
    unfolding matrix_to_iarray_nth
    unfolding n_tna[symmetric]
    by (rule Suc.hyps, auto simp add: nrows_def n[unfolded nrows_def])
qed

lemma matrix_to_iarray_Hermite_of_row_i[code_unfold]:
  fixes A::"'a::{unique_euclidean_ring}^'cols::{mod_type}^'rows::{mod_type}"
  shows "matrix_to_iarray (Hermite_of_row_i ass res A i) 
  = Hermite_of_row_i_iarray ass res (matrix_to_iarray A) (to_nat i)"
proof -
  have zero_rw: "is_zero_iarray (matrix_to_iarray A !! to_nat i) = is_zero_row i A"
    by (simp add: is_zero_iarray_eq_iff is_zero_row_eq_row_zero vec_to_iarray_row')
  show ?thesis
  proof (cases "is_zero_row i A")
    case True thus ?thesis 
      unfolding Hermite_of_row_i_def Hermite_of_row_i_iarray_def Let_def zero_rw by auto
  next
    case False
    have Ain: "A $ i $ (LEAST n. A $ i $ n \<noteq> 0) \<noteq> 0" 
      using False
      by (metis (mono_tags, lifting) LeastI is_zero_row_def')
    have l: "least_non_zero_position_of_vector (matrix_to_iarray A !! to_nat i) = to_nat (LEAST n. A $ i $ n \<noteq> 0)"
    proof -
      have least_rw: " (LEAST n. A $ i $ n \<noteq> 0 \<and> 0 \<le> n) =  (LEAST n. A $ i $ n \<noteq> 0)"
        by (rule Least_equality, auto simp add: least_mod_type Ain Least_le)
      have v_rw: "\<not> vector_all_zero_from_index (to_nat (0::'cols), vec_to_iarray (A $ i))" 
        using False least_mod_type
        unfolding vector_all_zero_from_index_eq[of 0 "A$i", symmetric] is_zero_row_def' by auto
      show ?thesis using vec_to_iarray_least_non_zero_position_of_vector_from_index[OF v_rw]
        unfolding least_rw least_non_zero_position_of_vector_def to_nat_0 vec_matrix .
    qed
    show ?thesis
      unfolding Hermite_of_row_i_def Hermite_of_row_i_iarray_def Let_def
      unfolding zero_rw[symmetric]
      unfolding matrix_to_iarray_mult_row[symmetric]
      unfolding l
      unfolding matrix_to_iarray_nth
      by (auto, rule matrix_to_iarray_Hermite_reduce_above, simp add: nrows_def to_nat_less_card)
  qed
qed



lemma matrix_to_iarray_Hermite_of_upt_row_i:
  fixes A::"'a::{unique_euclidean_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes i: "i\<le>nrows A"
  shows "matrix_to_iarray (Hermite_of_upt_row_i A i ass res) 
  = Hermite_of_upt_row_i_iarrays (matrix_to_iarray A) i ass res"
  using i
proof (induct i arbitrary: A)
  case 0
  thus ?case by (simp add: Hermite_of_upt_row_i_def Hermite_of_upt_row_i_iarrays_def)
next
  case (Suc i)
  have i: "i<nrows A" using Suc.prems unfolding nrows_def by simp
  have "matrix_to_iarray (Hermite_of_upt_row_i A (Suc i) ass res) 
    = matrix_to_iarray (Hermite_of_row_i ass res (Hermite_of_upt_row_i A i ass res) (from_nat i))"
    unfolding Hermite_of_upt_row_i_def by auto
  also have "... = (Hermite_of_row_i_iarray ass res 
    (matrix_to_iarray (Hermite_of_upt_row_i A i ass res)) (to_nat (from_nat i::'rows)))"
    unfolding matrix_to_iarray_Hermite_of_row_i ..
  also have "... = (Hermite_of_row_i_iarray ass res (matrix_to_iarray (Hermite_of_upt_row_i A i ass res)) i)"
    using to_nat_from_nat_id[OF i[unfolded nrows_def]] by simp
  also have "... = (Hermite_of_row_i_iarray ass res 
    (Hermite_of_upt_row_i_iarrays (matrix_to_iarray A) i ass res) i)"
    using Suc.hyps i unfolding nrows_def by simp
  also have "... =  Hermite_of_upt_row_i_iarrays (matrix_to_iarray A) (Suc i) ass res"
    unfolding Hermite_of_upt_row_i_iarrays_def by simp
  finally show ?case .
qed

lemma matrix_to_iarray_Hermite_of[code_unfold]:
  shows "matrix_to_iarray (Hermite_of A ass res bezout) 
  = Hermite_of_iarrays (matrix_to_iarray A) ass res bezout"
proof -
  have n: "nrows A \<le> nrows (echelon_form_of A bezout)" unfolding nrows_def by simp
  show ?thesis
    unfolding Hermite_of_def Hermite_of_iarrays_def Let_def
    unfolding matrix_to_iarray_Hermite_of_upt_row_i[OF n]
    unfolding matrix_to_iarray_echelon_form_of
    unfolding matrix_to_iarray_nrows ..
qed

subsection\<open>Examples of execution using immutable arrays\<close>

value[code] "let A = list_of_list_to_matrix ([[37,8,6],[5,4,-8],[3,24,-7]])::int^3^3
  in matrix_to_iarray (Hermite_of A ass_function_euclidean res_function_euclidean euclid_ext2)"

value[code] "let A = IArray[IArray[37,8,6::int],IArray[5,4,-8],IArray[3,24,-7]]
  in (Hermite_of_iarrays A ass_function_euclidean res_function_euclidean euclid_ext2)"

value[code] "let A = list_of_list_to_matrix ([[[:3,4,5:],[:-2,1:]],[[:-1,0,2:],[:0,1,4,1:]]])::real poly^2^2
  in matrix_to_iarray (Hermite_of A ass_function_euclidean res_function_euclidean euclid_ext2)"

end
