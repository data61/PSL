(*  
    Title:      Examples_QR_Abstract_Symbolic.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Examples of execution using symbolic computation\<close>

theory Examples_QR_Abstract_Symbolic
imports
 QR_Decomposition
 Real_Impl.Real_Unique_Impl
begin

subsection\<open>Execution of the QR decomposition using symbolic computation\<close>

subsubsection\<open>Some previous definitions and lemmas\<close>

text\<open>The symbolic computation is based on the René Thiemann's work about implementing
field extensions of the form Q[sqrt(b)].\<close>

definition "show_vec_real v = (\<chi> i. show_real (v $ i))"

lemma [code abstract]: "vec_nth (show_vec_real v) = (% i. show_real (v $ i))"
unfolding show_vec_real_def by auto

definition "show_matrix_real A = (\<chi> i. show_vec_real (A $ i))"

lemma[code abstract]: "vec_nth (show_matrix_real A) = (% i. show_vec_real (A $ i))"
unfolding show_matrix_real_def by auto

subsubsection\<open>Examples\<close>

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,0]]::real^3^3 in 
  matrix_to_list_of_list (show_matrix_real (divide_by_norm A))"

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  matrix_to_list_of_list (show_matrix_real (fst (QR_decomposition A)))" 

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  matrix_to_list_of_list (show_matrix_real (snd (QR_decomposition A)))"

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  matrix_to_list_of_list (show_matrix_real ((fst (QR_decomposition A)) ** (snd (QR_decomposition A))))"

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4],[3,5,4]]::real^3^4 in
  matrix_to_list_of_list (show_matrix_real ((fst (QR_decomposition A)) ** (snd (QR_decomposition A))))"


(*Case m \<ge> n and dependent columns*)
value "let A = list_of_list_to_matrix [[1,2,1],[9,4,9],[2,0,2],[0,5,0]]::real^3^4 in
  matrix_to_list_of_list (show_matrix_real ((fst (QR_decomposition A)) ** (snd (QR_decomposition A))))"

value "let A = list_of_list_to_matrix [[1,2,1],[9,4,9],[2,0,2],[0,5,0]]::real^3^4 in
  matrix_to_list_of_list (show_matrix_real (fst (QR_decomposition A)))"

value "let A = list_of_list_to_matrix [[1,2,1],[9,4,9],[2,0,2],[0,5,0]]::real^3^4 in
  vec_to_list (show_vec_real ((column 0 (fst (QR_decomposition A)))))"

value "let A = list_of_list_to_matrix [[1,2,1],[9,4,9],[2,0,2],[0,5,0]]::real^3^4 in
  vec_to_list (show_vec_real ((column 1 (fst (QR_decomposition A)))))"

value "let A = list_of_list_to_matrix [[1,2,1],[9,4,9],[2,0,2],[0,5,0]]::real^3^4 in
  matrix_to_list_of_list (show_matrix_real (snd (QR_decomposition A)))" (*R is not invertible*)

(*Case m < n and dependent columns*)

value "let A = list_of_list_to_matrix [[1,2,1],[9,4,9]]::real^3^2 in
  matrix_to_list_of_list (show_matrix_real ((fst (QR_decomposition A)) ** (snd (QR_decomposition A))))"

value "let A = list_of_list_to_matrix [[1,2,1],[9,4,9]]::real^3^2 in
  matrix_to_list_of_list (show_matrix_real ((fst (QR_decomposition A))))"

value "let A = list_of_list_to_matrix [[1,2,1],[9,4,9]]::real^3^2 in
  matrix_to_list_of_list (show_matrix_real ((snd (QR_decomposition A))))"

(*
  Limitation: if the input matrix has irrational numbers, then probably we won't be working in the same
  field extension so the computation will fail.
*)

(*
value "let A = list_of_list_to_matrix [[1,sqrt 2,4],[sqrt 5,4,5],[0,sqrt 7,4]]::real^3^3 in
  matrix_to_list_of_list (show_matrix_real ((fst (QR_decomposition A))))"
*)

definition "example1 = (let A = list_of_list_to_matrix [[1,2,1],[9,4,9]]::real^3^2 in
  matrix_to_list_of_list (show_matrix_real ((snd (QR_decomposition A)))))"

export_code example1 in SML module_name QR

end
