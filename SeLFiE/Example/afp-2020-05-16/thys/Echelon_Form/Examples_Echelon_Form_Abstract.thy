(*  
    Title:      Examples_Echelon_Form_Abstract.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Examples of execution over matrices represented as functions\<close>

theory Examples_Echelon_Form_Abstract
imports
  Code_Cayley_Hamilton
  Gauss_Jordan.Examples_Gauss_Jordan_Abstract
  Echelon_Form_Inverse
  "HOL-Computational_Algebra.Field_as_Ring"
begin

text\<open>The definitions introduced in this file will be also used in 
  the computations presented in file @{file \<open>Examples_Echelon_Form_IArrays.thy\<close>}. 
  Some of these definitions are not even used in this file since they are quite 
  time consuming.\<close>

definition test_real_6x4 :: "real^6^4"
  where "test_real_6x4 = list_of_list_to_matrix
        [[0,0,0,0,0,0],
         [0,1,0,0,0,0],
         [0,0,0,0,0,0],
         [0,0,0,0,8,2]]"
  
value "matrix_to_list_of_list (minorM test_real_6x4 0 0)"

value "cofactor (mat 1::rat^3^3) 0 0"

value "vec_to_list (cofactorM_row  (mat 1::int^3^3) 1)"

value "matrix_to_list_of_list (cofactorM  (mat 1::int^3^3))"

definition test_rat_3x3 :: "rat^3^3"
  where "test_rat_3x3 = list_of_list_to_matrix [[3,5,1],[2,1,3],[1,2,1]]"

value "matrix_to_list_of_list (matpow test_rat_3x3 5)" 

definition test_int_3x3 :: "int^3^3"
  where "test_int_3x3 = list_of_list_to_matrix [[3,2,8], [0,3,9], [8,7,9]]"

value "det test_int_3x3"

definition test_real_3x3 :: "real^3^3"
  where "test_real_3x3 = list_of_list_to_matrix [[3,5,1],[2,1,3],[1,2,1]]"

value "charpoly test_real_3x3"

text\<open>We check that the Cayley-Hamilton theorem holds for this particular case:\<close>

value "matrix_to_list_of_list (evalmat (charpoly test_real_3x3) test_real_3x3)"

definition test_int_3x3_02 :: "int^3^3"
  where "test_int_3x3_02 = list_of_list_to_matrix [[3,5,1],[2,1,3],[1,2,1]]"

value "matrix_to_list_of_list (adjugate test_int_3x3_02)"

text\<open>The following integer matrix is not invertible, so the result is \<open>None\<close>\<close>

value "inverse_matrix test_int_3x3_02"

definition test_int_3x3_03 :: "int^3^3"
  where "test_int_3x3_03 = list_of_list_to_matrix [[1,-2,4],[1,-1,1],[0,1,-2]]"

value "matrix_to_list_of_list (the (inverse_matrix test_int_3x3_03))"

text\<open>We check that the previous inverse has been correctly computed:\<close>

value "test_int_3x3_03 ** (the (inverse_matrix test_int_3x3_03)) = (mat 1::int^3^3)"

definition test_int_8x8 :: "int^8^8"
  where "test_int_8x8 = list_of_list_to_matrix 
       [[ 3, 2, 3, 6, 2, 8, 5, 6],
        [ 0, 5, 5, 2, 3, 9, 4, 7],
        [ 8, 7, 9, 1, 4,-2, 2, 0],
        [ 0, 1, 5, 6, 5, 1, 1, 4],
        [ 0, 3, 4, 5, 2,-4, 2, 1],
        [ 6, 8, 6, 2, 2,-3, 3, 5],
        [-2, 4,-2, 6, 7, 8, 0, 3],
        [ 7, 1, 3, 0,-9,-3, 4,-5]]"

text\<open>SLOW; several minutes.\<close>

(*value "det test_int_8x8"

value "matrix_to_list_of_list (echelon_form_of test_int_8x8 euclid_ext2)"*)

text\<open>The following definitions will be used in 
  file @{file \<open>Examples_Echelon_Form_IArrays.thy\<close>}.
  Using the abstract version of matrices would produce lengthy computations.\<close>

definition test_int_6x6 :: "int^6^6"
  where "test_int_6x6 = list_of_list_to_matrix 
    [[ 3, 2, 3, 6, 2, 8],
     [ 0, 5, 5, 2, 3, 9],
     [ 8, 7, 9, 1, 4,-2],
     [ 0, 1, 5, 6, 5, 1],
     [ 0, 3, 4, 5, 2,-4],
     [ 6, 8, 6, 2, 2,-3]]"

definition test_real_6x6 :: "real^6^6"
  where "test_real_6x6 = list_of_list_to_matrix 
    [[ 3, 2, 3, 6, 2, 8],
     [ 0, 5, 5, 2, 3, 9],
     [ 8, 7, 9, 1, 4,-2],
     [ 0, 1, 5, 6, 5, 1],
     [ 0, 3, 4, 5, 2,-4],
     [ 6, 8, 6, 2, 2,-3]]"

definition test_int_20x20 :: "int^20^20"
  where "test_int_20x20 =  list_of_list_to_matrix 
    [[3,2,3,6,2,8,5,9,8,7,5,4,7,8,9,8,7,4,5,2],
     [0,5,5,2,3,9,1,2,4,6,1,2,3,6,5,4,5,8,7,1],
     [8,7,9,1,4,-2,8,7,1,4,1,4,5,8,7,4,1,0,0,2],
     [0,1,5,6,5,1,3,5,4,9,3,2,1,4,5,6,9,8,7,4],
     [0,3,4,5,2,-4,0,2,1,0,0,0,1,2,4,5,1,1,2,0],
     [6,8,6,2,2,-3,2,4,7,9,1,2,3,6,5,4,1,2,8,7],
     [3,8,3,6,2,8,8,9,6,7,8,9,7,8,9,5,4,1,2,3,0],
     [0,8,5,2,8,9,1,2,4,6,4,6,5,8,7,9,8,7,4,5],
     [8,8,8,1,4,-2,8,7,1,4,5,5,5,6,4,5,1,2,3,6],
     [0,8,5,6,5,1,3,5,4,9::int,1,2,3,5,4,7,8,9,6,4],
     [3,2,3,6,2,8,5,9,8,7,5,4,7,3,9,8,7,4,5,2],
     [0,5,5,2,3,9,1,2,4,3,1,2,3,6,5,4,5,8,7,1],
     [1,7,9,1,4,-2,8,7,1,4,1,4,5,8,7,4,1,0,0,2],
     [1,1,5,6,5,1,3,5,4,9,3,4,5,6,9,8,7,4,5,4],
     [3,3,4,5,2,-4,0,2,1,0,0,3,1,2,4,5,1,1,2,0],
     [4,8,6,5,2,-3,2,4,2,9,1,2,3,2,5,4,1,2,8,7],
     [5,8,3,6,2,2,9,9,6,7,2,7,7,2,9,5,4,1,2,3,0],
     [2,8,5,2,8,9,5,2,4,6,4,6,5,2,7,1,8,7,4,5],
     [2,1,8,1,4,-2,8,3,1,4,5,5,5,6,4,5,1,2,3,6],
     [0,2,5,6,5,1,3,5,4,9::int,1,2,3,5,4,7,8,9,6,4]]"
     


definition test_int_20x20_2 :: "int^20^20"
where "test_int_20x20_2 = list_of_list_to_matrix
      [[58,18,18,41,68,62,6,21,19,78,34,22,108,63,71,38,43,52,37,24],
      [18,51,29,91,76,98,56,37,47,61,88,99,88,78,210,57,27,87,72,79],
      [49,19,81,107,43,34,69,28,101,39,21,910,27,53,15,38,5,34,47,23],
      [97,102,68,27,56,56,102,210,68,56,24,33,88,110,71,23,35,36,72,1],
      [63,11,39,16,32,81,16,98,94,26,53,23,11,51,98,51,81,57,610,85],
      [46,61,68,710,11,105,3,5,61,210,67,34,108,10,44,71,36,66,38,42],
      [39,75,106,42,36,92,110,42,89,105,11,108,22,61,65,101,410,1,1,31],
      [106,94,24,63,16,75,47,82,62,210,52,57,810,41,55,93,73,58,41,82],
      [55,49,102,9,8,41,12,110,109,310,95,51,103,71,92,85,910,410,17,21],
      [31,2,77,93,8,98,510,94,56,5,12,91,69,31,62,4,11,5,92,65],
      [22,29,103,34,64,11,9,610,1,19,35,24,21,49,31,43,81,102,14,11],
      [75,81,5,109,61,110,19,46,55,23,31,1,98,28,56,2,83,81,91,41],
      [4,510,58,41,38,106,99,103,31,84,110,63,17,105,210,61,95,103,63,51],
      [38,32,510,62,410,14,86,310,59,69,107,13,29,610,38,103,43,98,98,1],
      [101,11,3,101,99,810,10,3,510,8,35,62,45,49,34,86,63,66,71,9],
      [16,5,77,110,109,13,63,54,310,102,92,103,310,26,15,22,66,106,210,91],
      [13,810,66,51,91,84,19,25,110,41,51,87,27,79,18,69,99,95,11,46],
      [410,910,62,89,43,23,108,52,33,67,31,105,26,106,108,85,87,68,56,23],
      [310,68,21,91,107,85,94,28,101,34,109,27,63,84,25,106,65,81,7,310],
      [42,63,27,24,1010,11,107,69,910,810,31,15,97,3,56,77,51,108,31,26::int]]"
end

