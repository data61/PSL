(*  
    Title:      Examples_QR_IArrays_Symbolic.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Examples of execution using symbolic computation and iarrays\<close>

theory Examples_QR_IArrays_Symbolic
imports
  Examples_QR_Abstract_Symbolic
  QR_Decomposition_IArrays
begin

subsection\<open>Execution of the QR decomposition using symbolic computation and iarrays\<close>

definition "show_vec_real_iarrays v = IArray.of_fun (\<lambda>i. show_real (v !! i)) (IArray.length v)"

lemma vec_to_iarray_show_vec_real[code_unfold]: "vec_to_iarray (show_vec_real v) 
  = show_vec_real_iarrays (vec_to_iarray v)"
  unfolding show_vec_real_def show_vec_real_iarrays_def vec_to_iarray_def by auto

text\<open>The following function is used to print elements of type vec as lists of characters; 
  useful for printing vectors in the output panel.\<close>

definition "print_vec = IArray.list_of \<circ> show_vec_real_iarrays \<circ> vec_to_iarray"

definition "show_matrix_real_iarrays A = IArray.of_fun (\<lambda>i. show_vec_real_iarrays (A !! i)) (IArray.length A)"

lemma matrix_to_iarray_show_matrix_real[code_unfold]: "matrix_to_iarray (show_matrix_real v) 
  = show_matrix_real_iarrays (matrix_to_iarray v)"
  unfolding show_matrix_real_iarrays_def show_matrix_real_def
  unfolding matrix_to_iarray_def 
  by (simp add: vec_to_iarray_show_vec_real)

text\<open>The following functions are useful to print matrices as lists of lists of characters; 
  useful for printing in the output panel.\<close>

definition "print_vec_mat = IArray.list_of \<circ> show_vec_real_iarrays"

definition "print_mat_aux A = IArray.of_fun (\<lambda>i. print_vec_mat (A !! i)) (IArray.length A)"

definition "print_mat = IArray.list_of \<circ> print_mat_aux \<circ> matrix_to_iarray"

subsubsection\<open>Examples\<close>

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,0]]::real^3^3 in 
  iarray_of_iarray_to_list_of_list (matrix_to_iarray (show_matrix_real (divide_by_norm A)))"

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray (show_matrix_real (fst (QR_decomposition A))))"

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray (show_matrix_real (snd (QR_decomposition A))))"

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray 
    (show_matrix_real ((fst (QR_decomposition A)) ** (snd (QR_decomposition A)))))"

value "let A = list_of_list_to_matrix [[1,2,3],[9,4,5],[0,0,4],[1,2,3]]::real^3^4 in rank A = ncols A"

value "let A = list_of_list_to_matrix [[1,2,3],[9,4,5],[0,0,4],[1,2,3]]::real^3^4; 
  b = list_to_vec [1,2,3,4]::real^4 in
  print_result_solve (solve A b)"

value "let A = list_of_list_to_matrix [[1,2,3],[9,4,5],[0,0,4],[1,2,3]]::real^3^4; 
  b = list_to_vec [1,2,3,4]::real^4
  in
  vec_to_list (show_vec_real (the (inverse_matrix (snd (QR_decomposition A))) ** transpose (fst (QR_decomposition A)) *v b))"

value "let A = list_of_list_to_matrix [[1,2,3],[9,4,5],[0,0,4],[1,2,3]]::real^3^4; 
  b = list_to_vec [1,2,3,4]::real^4
  in matrix_to_list_of_list (show_matrix_real ((snd (QR_decomposition A))))"


text\<open>least squares solution\<close>

definition "A \<equiv> list_of_list_to_matrix [[1,3/5,3],[9,4,5/3],[0,0,4],[1,2,3]]::real^3^4"
definition "b \<equiv> list_to_vec [1,2,3,4]::real^4"

value "let Q = fst (QR_decomposition A); R = snd (QR_decomposition A)
  in print_vec ((the (inverse_matrix R) ** transpose Q *v b))"

text\<open>A times least squares solution\<close>

value "let Q = fst (QR_decomposition A); R = snd (QR_decomposition A)
  in print_vec (A *v (the (inverse_matrix R) ** transpose Q *v b))"

text\<open>The matrix Q\<close>

value "print_mat (fst (QR_decomposition A))"

text\<open>The matrix R\<close>

value "print_mat (snd (QR_decomposition A))"

text\<open>The inverse of matrix R\<close>

value "let R = snd (QR_decomposition A) in print_mat (the (inverse_matrix R))"

text\<open>The least squares solution is in the left null space of A\<close>

value "let Q = fst (QR_decomposition A); R = snd (QR_decomposition A);
           b2 = (A *v (the (inverse_matrix R) ** transpose Q *v b))
       in print_vec ((b - b2)v* A)"

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4],[3,5,4]]::real^3^4 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray 
    (show_matrix_real ((fst (QR_decomposition A)) ** (snd (QR_decomposition A)))))"

value "let A = IArray[IArray[1,2,4],IArray[9,4,5::real],IArray[0,0,0]] in 
   iarray_of_iarray_to_list_of_list (show_matrix_real_iarrays (divide_by_norm_iarray A))"  

value "let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4]] in
  iarray_of_iarray_to_list_of_list (show_matrix_real_iarrays (fst (QR_decomposition_iarrays A)))"
  
value "let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4]] in
  iarray_of_iarray_to_list_of_list (show_matrix_real_iarrays (snd (QR_decomposition_iarrays A)))"

value "let A = list_of_list_to_matrix [[1,2,3],[9,4,5],[0,0,4],[1,2,3]]::real^3^4 in rank A = ncols A"

value "let A = list_of_list_to_matrix [[1,2,3],[9,4,5],[0,0,4],[1,2,3]]::real^3^4; 
  b = list_to_vec [1,2,3,4]::real^4 in
  print_result_solve (solve A b)"

value "let A = list_of_list_to_matrix [[1,2,3],[9,4,5],[0,0,4],[1,2,3]]::real^3^4; 
  b = list_to_vec [1,2,3,4]::real^4
  in
  vec_to_list (show_vec_real (the (inverse_matrix (snd (QR_decomposition A))) ** transpose (fst (QR_decomposition A)) *v b))"

value "let A = list_of_list_to_matrix [[1,2,3],[9,4,5],[0,0,4],[1,2,3]]::real^3^4; 
  b = list_to_vec [1,2,3,4]::real^4
  in matrix_to_list_of_list (show_matrix_real ((snd (QR_decomposition A))))"

value "let A = list_of_list_to_matrix [[1,2,3],[9,4,5],[0,0,4],[1,2,3]]::real^3^4; 
  b = list_to_vec [1,2,3,4]::real^4;
  b2 = (A *v (the (inverse_matrix (snd (QR_decomposition A))) ** transpose (fst (QR_decomposition A)) *v b))
  in
  vec_to_list (show_vec_real ((b - b2)v* A))"

value "let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4]] in
  iarray_of_iarray_to_list_of_list (show_matrix_real_iarrays 
    ((fst (QR_decomposition_iarrays A)) **i (snd (QR_decomposition_iarrays A))))"
  
value "let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4],IArray[3,5,4]]in
  iarray_of_iarray_to_list_of_list (show_matrix_real_iarrays 
    ((fst (QR_decomposition_iarrays A)) **i (snd (QR_decomposition_iarrays A))))"


text\<open>The following example is presented in Chapter 1 of the book
\<open>Numerical Methods in Scientific Computing\<close> by Dahlquist and Bjorck\<close>

value "let A = list_of_list_to_matrix 
  [[1,-0.6691],[1,-0.3907],[1,-0.1219],[1,0.3090],[1,0.5878]]::real^2^5; 
  b = list_to_vec [0.3704,0.5,0.6211,0.8333,0.9804]::real^5;
  QR = (QR_decomposition A);
  Q = fst QR;
  R = snd QR
  in print_vec (the (inverse_matrix R) ** transpose Q *v b)"


(*
  Limitation: if the input matrix has irrational numbers, then we won't be working in the same
  field extension so the computation will fail.
*)

(*
value[code] "let A = list_of_list_to_matrix [[1,sqrt 2,4],[sqrt 5,4,5],[0,sqrt 7,4]]::real^3^3 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray (show_matrix_real ((fst (QR_decomposition A)))))"
*)

definition "example = (let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4],IArray[3,5,4]]in
  iarray_of_iarray_to_list_of_list (show_matrix_real_iarrays 
    ((fst (QR_decomposition_iarrays A)) **i (snd (QR_decomposition_iarrays A)))))"

export_code example in SML module_name QR

end
