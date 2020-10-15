(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Code Equations for All Algorithms\<close>

text \<open>In this theory we load all executable algorithms, i.e., Gauss-Jordan, determinants,
  Jordan normal form computation, etc., and perform some basic tests.\<close>

theory Matrix_Impl
imports 
  Matrix_IArray_Impl
  Gauss_Jordan_IArray_Impl
  Determinant_Impl
  Show_Matrix
  Jordan_Normal_Form_Existence
  Show.Show_Instances
begin

text \<open>For determinants we require class @{class idom_divide}, so integers, rationals, etc. can be used.\<close>
value[code] "det (mat_of_rows_list 4 [[1 :: int, 4, 9, -1], [-3, -1, 5, 4], [4, 2, 0,2], [8,-9, 5,7]])"
value[code] "det (mat_of_rows_list 4 [[1 :: rat, 4, 9, -1], [-3, -1, 5, 4], [4, 2, 0,2], [8,-9, 5,7]])"

text \<open>Since polynomials require @{class field} elements to be in class @{class idom_divide}, the implementation
  of characteristic polynomials is not applicable for integer matrices, but it is for rational and real matrices.\<close>

value[code] "char_poly (mat_of_rows_list 4 [[1 :: real, 4, 9, -1], [-3, -1, 5, 4], [4, 2, 0,2], [8,-9, 5,7]])"

text \<open>Also Jordan normal form computation requires matrices over @{class field} entries.\<close>

value[code] "triangular_to_jnf_vector (mat_of_rows_list 6 [
  [3,4,1,4,7,18], 
  [0,3,0,8,9,4], 
  [0,0,3,2,0,4], 
  [0,0,0,5,17,7],
  [0,0,0,0,5,3], 
  [0,0,0,0,0,3 :: rat]])"

value[code] "show (mat_of_rows_list 3 [[1, 4, 5], [3, 6, 8]] * mat 3 4 (\<lambda> (i,j). i + 2 * j))"

text \<open>Inverses can only be computed for matrices over fields.\<close>

value[code] "show (mat_inverse (mat_of_rows_list 4 [[1 :: rat, 4, 9, -1], [-3, -1, 5, 4], [4, 2, 0,2], [8,-9, 5,7]]))"

value[code] "show (mat_inverse (mat_of_rows_list 4 [[1 :: rat, 4, 9, -1], [-3, -1, 5, 4], [-2, 3,14,3], [8,-9, 5,7]]))"

end
