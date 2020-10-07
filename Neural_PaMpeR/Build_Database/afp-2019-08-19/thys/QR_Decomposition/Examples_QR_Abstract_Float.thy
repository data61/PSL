(*  
    Title:      Examples_QR_Abstract_Float.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Examples of execution using floats\<close>

theory Examples_QR_Abstract_Float
imports
  QR_Decomposition
  Gauss_Jordan.Code_Real_Approx_By_Float_Haskell
begin

subsubsection\<open>Examples\<close>

definition "example1 = (let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,0]]::real^3^3 in 
  matrix_to_list_of_list (divide_by_norm A))"

definition "example2 = (let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  matrix_to_list_of_list (fst (QR_decomposition A)))" 

definition "example3 = (let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  matrix_to_list_of_list (snd (QR_decomposition A)))"

definition "example4 = (let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  matrix_to_list_of_list (fst (QR_decomposition A) ** (snd (QR_decomposition A))))"

definition "example5 = (let A = list_of_list_to_matrix [[1,sqrt 2,4],[sqrt 5,4,5],[0,sqrt 7,4]]::real^3^3 in
  matrix_to_list_of_list (fst (QR_decomposition A)))"

export_code example1 example2 example3 example4 example5 in SML module_name "QR"

end
