(*  
    Title:      Examples_Echelon_Form_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Examples of computations using immutable arrays\<close>

theory Examples_Echelon_Form_IArrays
imports
  Echelon_Form_Inverse_IArrays
  "HOL-Library.Code_Target_Numeral"
  Gauss_Jordan.Examples_Gauss_Jordan_Abstract
  Examples_Echelon_Form_Abstract
begin

text\<open>The file @{file \<open>Examples_Echelon_Form_Abstract.thy\<close>} is only imported to 
  include the definitions of matrices that we use in the following examples. 
  Otherwise, it could be removed.\<close>

subsection\<open>Computing echelon forms, determinants, characteristic polynomials and so on using
  immutable arrays\<close>

subsubsection\<open>Serializing gcd\<close>

text\<open>First of all, we serialize the gcd to the ones of PolyML and MLton as we did in the
  Gauss-Jordan development.\<close>

context
includes integer.lifting
begin

lift_definition gcd_integer :: "integer => integer => integer"
  is "gcd :: int => int => int" .

lemma gcd_integer_code [code]:
"gcd_integer l k = \<bar>if l = (0::integer) then k else gcd_integer l (\<bar>k\<bar> mod \<bar>l\<bar>)\<bar>"
  by transfer (simp add: gcd_code_int [symmetric] ac_simps)

end

code_printing
 constant "abs :: integer => _" \<rightharpoonup> (SML) "IntInf.abs"
 | constant "gcd_integer :: integer => _ => _" \<rightharpoonup> (SML) "(PolyML.IntInf.gcd ((_),(_)))" (*Only for Poly/ML*)
 (* | constant "gcd_integer :: integer => _ => _" \<rightharpoonup> (SML) "(MLton.IntInf.gcd ((_),(_)))"*) (*Only for MLton*)

lemma gcd_code [code]:
  "gcd a b = int_of_integer (gcd_integer (of_int a) (of_int b))"
  by (metis gcd_integer.abs_eq int_of_integer_integer_of_int integer_of_int_eq_of_int)

code_printing
  constant "abs :: real => real" \<rightharpoonup>
    (SML) "Real.abs"

declare [[code drop: "abs :: real \<Rightarrow> real"]]
  
code_printing
constant "divmod_integer :: integer => _ => _" \<rightharpoonup> (SML) "(IntInf.divMod ((_),(_)))"

subsubsection\<open>Examples\<close>

value "det test_int_3x3"

value "det test_int_3x3_03"

value "det test_int_6x6"

value "det test_int_8x8"

value "det test_int_20x20"

value "charpoly test_real_3x3"
  
value "charpoly test_real_6x6"

value "inverse_matrix test_int_3x3_02"

value "matrix_to_iarray (echelon_form_of test_int_3x3 euclid_ext2)"

value "matrix_to_iarray (echelon_form_of test_int_8x8 euclid_ext2)"

text\<open>The following computations are much faster when code is exported.\<close>

(*value "matrix_to_iarray (echelon_form_of_euclidean test_int_20x20)"*)

(*value "echelon_form_of_iarrays (matrix_to_iarray test_int_20x20) euclid_ext2"*)

(*value "matrix_to_iarray (echelon_form_of test_int_20x20 euclid_ext2)"*)

text\<open>The following matrix will have an integer inverse since its determinant is equal to one\<close>

value "det test_int_3x3_03"

value "the (matrix_to_iarray_option (inverse_matrix test_int_3x3_03))"

text\<open>We check that the previous inverse has been correctly computed:\<close>

value "matrix_matrix_mult_iarray 
              (matrix_to_iarray test_int_3x3_03) 
              (the (matrix_to_iarray_option (inverse_matrix test_int_3x3_03)))"

value "matrix_matrix_mult_iarray 
              (the (matrix_to_iarray_option (inverse_matrix test_int_3x3_03)))
              (matrix_to_iarray test_int_3x3_03)"

text\<open>The following matrices have determinant different from zero, 
    and thus do not have an integer inverse\<close>
              
value "det test_int_6x6"
              
value "matrix_to_iarray_option (inverse_matrix test_int_6x6)"

value "det test_int_20x20"
             
value "matrix_to_iarray_option (inverse_matrix test_int_20x20)"

text\<open>The inverse in dimension 20 has (trivial) inverse.\<close>

value "the (matrix_to_iarray_option (inverse_matrix (mat 1::int^20^20)))"

value "the (matrix_to_iarray_option (inverse_matrix (mat 1::int^20^20))) = matrix_to_iarray (mat 1::int^20^20)"


definition "print_echelon_int (A::int^20^20) = echelon_form_of_iarrays (matrix_to_iarray A) euclid_ext2"

text\<open>Performance is better when code is exported. In addition, it depends on the growth of 
the integer coefficients of the matrices. For instance, \<open>test_int_20x20\<close>
is a matrix of integer numbers between $-10$ and $10$. The computation of its echelon form (by means
of \<open>print_echelon_int\<close>) needs about 2 seconds. However, the matrix \<open>test_int_20x20_2\<close>
has elements between $0$ and $1010$. The computation of its echelon form (by means
of \<open>print_echelon_int\<close> too) needs about 0.310 seconds. These benchmarks have been carried
out in a laptop with an i5-3360M processor with 4 GB of RAM.\<close>

export_code charpoly det echelon_form_of test_int_8x8 test_int_20x20 test_int_20x20_2 print_echelon_int
  in SML module_name Echelon (*file "Echelon.sml"*)

(*
  PolyML.use "Echelon.sml"; open Echelon; open Timer; 
  let val now=startCPUTimer (); in print_echelon_int (test_int_20x20); checkCPUTimes (now) end;
*)

(*Analogously, code can be exported to Haskell using the file Code_Rational presented in the
  Gauss-Jordan AFP entry.*)

end
