(*  
    Title:      Code_Matrix.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Code generation for vectors and matrices\<close>

theory Code_Matrix
imports 
  Rank_Nullity_Theorem.Miscellaneous
  Code_Set
begin

text\<open>In this file the code generator is set up properly to allow the execution of matrices 
      represented as funcions over finite types.\<close>

lemmas vec.vec_nth_inverse[code abstype]

lemma [code abstract]: "vec_nth 0 = (%x. 0)" by (metis zero_index)
lemma [code abstract]: "vec_nth 1 = (%x. 1)" by (metis one_index)
lemma [code abstract]: "vec_nth (a + b) =  (%i. a$i + b$i)" by (metis vector_add_component)
lemma [code abstract]: "vec_nth (a - b) =  (%i. a$i - b$i)" by (metis vector_minus_component)
lemma [code abstract]: "vec_nth (vec n) = (\<lambda>i. n)" unfolding vec_def by fastforce
lemma [code abstract]: "vec_nth (a * b) =  (%i. a$i * b$i)" unfolding vector_mult_component by auto
lemma [code abstract]: "vec_nth (c *s x) = (\<lambda>i. c * (x$i))" unfolding vector_scalar_mult_def by auto
lemma [code abstract]: "vec_nth (a - b) =  (%i. a$i - b$i)" by (metis vector_minus_component)

definition mat_mult_row 
  where "mat_mult_row m m' f = vec_lambda (%c. sum (%k. ((m$f)$k) * ((m'$k)$c)) (UNIV :: 'n::finite set))"

lemma mat_mult_row_code [code abstract]:
  "vec_nth (mat_mult_row m m' f) = (%c. sum (%k. ((m$f)$k) * ((m'$k)$c)) (UNIV :: 'n::finite set))"
  by(simp add: mat_mult_row_def fun_eq_iff)

lemma mat_mult [code abstract]: "vec_nth (m ** m') = mat_mult_row m m'"
  unfolding matrix_matrix_mult_def mat_mult_row_def[abs_def]
  using vec_lambda_beta by auto

lemma matrix_vector_mult_code [code abstract]:
  "vec_nth (A *v x) = (%i. (\<Sum>j\<in>UNIV. A $ i $ j * x $ j))" unfolding matrix_vector_mult_def by fastforce

lemma vector_matrix_mult_code [code abstract]:
  "vec_nth (x v* A) = (%j. (\<Sum>i\<in>UNIV. A $ i $ j * x $ i))" unfolding vector_matrix_mult_def by fastforce

definition mat_row
  where "mat_row k i = vec_lambda (%j. if i = j then k else 0)"

lemma mat_row_code [code abstract]:
  "vec_nth (mat_row k i) = (%j. if i = j then k else 0)" unfolding mat_row_def by auto

lemma [code abstract]: "vec_nth (mat k) = mat_row k"
  unfolding mat_def unfolding mat_row_def[abs_def] by auto

definition transpose_row
   where "transpose_row A i = vec_lambda (%j. A $ j $ i)"

lemma transpose_row_code [code abstract]:
  "vec_nth (transpose_row A i) = (%j.  A $ j $ i)" by (metis transpose_row_def vec_lambda_beta)

lemma transpose_code[code abstract]:
  "vec_nth (transpose A) = transpose_row A"
  by (auto simp: transpose_def transpose_row_def)

lemma [code abstract]: "vec_nth (row i A) =  (($) (A $ i))" unfolding row_def by fastforce
lemma [code abstract]: "vec_nth (column j A) = (%i. A $ i $ j)" unfolding column_def by fastforce

definition "rowvector_row v i = vec_lambda (%j. (v$j))"

lemma rowvector_row_code [code abstract]:
  "vec_nth (rowvector_row v i) = (%j. (v$j))" unfolding rowvector_row_def by auto

lemma [code abstract]: "vec_nth (rowvector v) = rowvector_row v"
  unfolding rowvector_def unfolding rowvector_row_def[abs_def] by auto

definition "columnvector_row v i = vec_lambda (%j. (v$i))"

lemma columnvector_row_code [code abstract]:
  "vec_nth (columnvector_row v i) = (%j. (v$i))" unfolding columnvector_row_def by auto

lemma [code abstract]: "vec_nth (columnvector v) = columnvector_row v"
  unfolding columnvector_def unfolding columnvector_row_def[abs_def] by auto

end
