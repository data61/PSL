(*  
    Title:      Examples_Gauss_Jordan_Abstract.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Examples of computations over abstract matrices\<close>

theory Examples_Gauss_Jordan_Abstract
imports 
  Determinants2
  Inverse
  System_Of_Equations
  Code_Bit
  "HOL-Library.Code_Target_Numeral"
begin
subsection\<open>Transforming a list of lists to an abstract matrix\<close>

text\<open>Definitions to transform a matrix to a list of list and vice versa\<close>
definition vec_to_list :: "'a^'n::{finite, enum} => 'a list"
  where "vec_to_list A = map (($) A) (enum_class.enum::'n list)"

definition matrix_to_list_of_list :: "'a^'n::{finite, enum}^'m::{finite, enum} => 'a list list"
  where "matrix_to_list_of_list A = map (vec_to_list) (map (($) A) (enum_class.enum::'m list))"

text\<open>This definition should be equivalent to \<open>vector_def\<close> (in suitable types)\<close>
definition list_to_vec :: "'a list => 'a^'n::{finite, enum, mod_type}"
  where "list_to_vec xs = vec_lambda (% i. xs ! (to_nat i))"

lemma [code abstract]: "vec_nth (list_to_vec xs) = (%i. xs ! (to_nat i))"
  unfolding list_to_vec_def by fastforce

definition list_of_list_to_matrix :: "'a list list => 'a^'n::{finite, enum, mod_type}^'m::{finite, enum, mod_type}"
  where "list_of_list_to_matrix xs = vec_lambda (%i. list_to_vec (xs ! (to_nat i)))"

lemma [code abstract]: "vec_nth (list_of_list_to_matrix xs) = (%i. list_to_vec (xs ! (to_nat i)))"
  unfolding list_of_list_to_matrix_def by auto

subsection\<open>Examples\<close>

text\<open>The following three lemmas are presented in both this file and in the 
\<open>Examples_Gauss_Jordan_IArrays\<close> one. They allow a more convenient printing of rational and
real numbers after evaluation. They have already been added to the repository version of Isabelle, 
so after Isabelle2014 they should be removed from here.\<close>

lemma [code_post]:
  "int_of_integer (- 1) = - 1"
 by simp

lemma [code_abbrev]:
 "(of_rat (- 1) :: real) = - 1"
  by simp

lemma [code_post]:
 "(of_rat (- (1 / numeral k)) :: real) = - 1 / numeral k"
 "(of_rat (- (numeral k / numeral l)) :: real) = - numeral k / numeral l"
 by (simp_all add: of_rat_divide of_rat_minus)

subsubsection\<open>Ranks and dimensions\<close>
text\<open>Examples on computing ranks, dimensions of row space, null space and col space and the Gauss Jordan algorithm\<close>

value "matrix_to_list_of_list (Gauss_Jordan (list_of_list_to_matrix ([[1,0,0,0,0,0],[0,1,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,8,2]])::real^6^4))"
value "matrix_to_list_of_list (Gauss_Jordan (list_of_list_to_matrix ([[1,-2,1,-3,0],[3,-6,2,-7,0]])::rat^5^2))"
value "matrix_to_list_of_list (Gauss_Jordan (list_of_list_to_matrix ([[1,0,0,1,1],[1,0,1,1,1]])::bit^5^2))"
value "(reduced_row_echelon_form_upt_k (list_of_list_to_matrix ([[1,0,8],[0,1,9],[0,0,0]])::real^3^3)) 3"
value "matrix_to_list_of_list (Gauss_Jordan (list_of_list_to_matrix [[Complex 1 1,Complex 1 (- 1), Complex 0 0],[Complex 2 (- 1),Complex 1 3, Complex 7 3]]::complex^3^2))"
value "DIM(real^5)"
value "vec.dimension (TYPE(bit)) (TYPE(5))"
value "vec.dimension (TYPE(real)) (TYPE(2))"
(*value "complex_over_reals.dimension"*)
(*value "vector_space_over_itself.dimension (TYPE(real))"*)
value "DIM(real^5^4)"
value "row_rank (list_of_list_to_matrix [[1,0,0,7,5],[1,0,4,8,-1],[1,0,0,9,8],[1,2,3,6,5]]::real^5^4)"
value "vec.dim (row_space (list_of_list_to_matrix [[1,0,0,7,5],[1,0,4,8,-1],[1,0,0,9,8],[1,2,3,6,5]]::real^5^4))"
value "col_rank (list_of_list_to_matrix [[1,0,0,7,5],[1,0,4,8,-1],[1,0,0,9,8],[1,2,3,6,5]]::real^5^4)"
value "vec.dim (col_space (list_of_list_to_matrix [[1,0,0,7,5],[1,0,4,8,-1],[1,0,0,9,8],[1,2,3,6,5]]::real^5^4))"
value "rank (list_of_list_to_matrix [[1,0,0,7,5],[1,0,4,8,-1],[1,0,0,9,8],[1,2,3,6,5]]::real^5^4)"
value "vec.dim (null_space (list_of_list_to_matrix [[1,0,0,7,5],[1,0,4,8,-1],[1,0,0,9,8],[1,2,3,6,5]]::real^5^4))"
value "rank (list_of_list_to_matrix [[Complex 1 1,Complex 1 (- 1), Complex 0 0],[Complex 2 (- 1),Complex 1 3, Complex 7 3]]::complex^3^2)"

subsubsection\<open>Inverse of a matrix\<close>
text\<open>Examples on computing the inverse of matrices\<close>

value "let A=(list_of_list_to_matrix [[1,1,2,4,5,9,8],[3,0,8,4,5,0,8],[3,2,0,4,5,9,8], [3,2,8,0,5,9,8] ,[3,2,8,4,0,9,8] ,[3,2,8,4,5,0,8], [3,2,8,4,5,9,0]]::real^7^7)
                    in matrix_to_list_of_list (P_Gauss_Jordan A)"
value "let A=(list_of_list_to_matrix [[1,1,2,4,5,9,8],[3,0,8,4,5,0,8],[3,2,0,4,5,9,8], [3,2,8,0,5,9,8] ,[3,2,8,4,0,9,8] ,[3,2,8,4,5,0,8], [3,2,8,4,5,9,0]]::real^7^7) in 
              matrix_to_list_of_list (A ** (P_Gauss_Jordan A))"
value "let A=(list_of_list_to_matrix [[1,1,2,4,5,9,8],[3,0,8,4,5,0,8],[3,2,0,4,5,9,8], [3,2,8,0,5,9,8] ,[3,2,8,4,0,9,8] ,[3,2,8,4,5,0,8], [3,2,8,4,5,9,0]]::real^7^7)
                    in (inverse_matrix A)"
value "let A=(list_of_list_to_matrix [[1,1,2,4,5,9,8],[3,0,8,4,5,0,8],[3,2,0,4,5,9,8], [3,2,8,0,5,9,8] ,[3,2,8,4,0,9,8] ,[3,2,8,4,5,0,8], [3,2,8,4,5,9,0]]::real^7^7)
                    in matrix_to_list_of_list (the (inverse_matrix A))"
value "let A=(list_of_list_to_matrix [[1,1,1,1,1,1,1],[2,2,2,2,2,2,2],[3,2,0,4,5,9,8], [3,2,8,0,5,9,8] ,[3,2,8,4,0,9,8] ,[3,2,8,4,5,0,8], [3,2,8,4,5,9,0]]::real^7^7)
                    in (inverse_matrix A)"
value "let A=(list_of_list_to_matrix [[Complex 1 1,Complex 1 (- 1), Complex 0 0],[Complex 1 1,Complex 1 (- 1), Complex 8 0],[Complex 2 (- 1),Complex 1 3, Complex 7 3]]::complex^3^3)
                    in matrix_to_list_of_list (the (inverse_matrix A))"


subsubsection\<open>Determinant of a matrix\<close>
text\<open>Examples on computing determinants of matrices\<close>

value "(let A = list_of_list_to_matrix[[1,2,7,8,9],[3,4,12,10,7],[-5,4,8,7,4],[0,1,2,4,8],[9,8,7,13,11]]::real^5^5 in det A)"
value "det (list_of_list_to_matrix ([[1,0,0],[0,1,0],[0,0,1]])::real^3^3)"
value "det (list_of_list_to_matrix ([[1,8,9,1,47],[7,2,2,5,9],[3,2,7,7,4],[9,8,7,5,1],[1,2,6,4,5]])::rat^5^5)"


subsubsection\<open>Bases of the fundamental subspaces\<close>
text\<open>Examples on computing basis for null space, row space, column space and left null space\<close>
(*Null_space basis:*)
value "let A = (list_of_list_to_matrix ([[1,3,-2,0,2,0],[2,6,-5,-2,4,-3],[0,0,5,10,0,15],[2,6,0,8,4,18]])::real^6^4) 
  in vec_to_list` (basis_null_space A)"
value "let A = (list_of_list_to_matrix ([[3,4,0,7],[1,-5,2,-2],[-1,4,0,3],[1,-1,2,2]])::real^4^4) 
  in vec_to_list` (basis_null_space A)"
(*Row_space basis*)
value "let A = (list_of_list_to_matrix ([[1,3,-2,0,2,0],[2,6,-5,-2,4,-3],[0,0,5,10,0,15],[2,6,0,8,4,18]])::real^6^4) 
    in vec_to_list` (basis_row_space A)"
value "let A = (list_of_list_to_matrix ([[3,4,0,7],[1,-5,2,-2],[-1,4,0,3],[1,-1,2,2]])::real^4^4) 
  in vec_to_list` (basis_row_space A)"
(*Col_space basis*)
value "let A = (list_of_list_to_matrix ([[1,3,-2,0,2,0],[2,6,-5,-2,4,-3],[0,0,5,10,0,15],[2,6,0,8,4,18]])::real^6^4) 
    in vec_to_list` (basis_col_space A)"
value "let A = (list_of_list_to_matrix ([[3,4,0,7],[1,-5,2,-2],[-1,4,0,3],[1,-1,2,2]])::real^4^4) 
  in vec_to_list` (basis_col_space A)"
(*Left_null_space basis*)
value "let A = (list_of_list_to_matrix ([[1,3,-2,0,2,0],[2,6,-5,-2,4,-3],[0,0,5,10,0,15],[2,6,0,8,4,18]])::real^6^4) 
    in vec_to_list` (basis_left_null_space A)"
value "let A = (list_of_list_to_matrix ([[3,4,0,7],[1,-5,2,-2],[-1,4,0,3],[1,-1,2,2]])::real^4^4) 
  in vec_to_list` (basis_left_null_space A)"

subsubsection\<open>Consistency and inconsistency\<close>
text\<open>Examples on checking the consistency/inconsistency of a system of equations\<close>
value "independent_and_consistent (list_of_list_to_matrix ([[1,0,0],[0,1,0],[0,0,1],[0,0,0],[0,0,0]])::real^3^5) (list_to_vec([2,3,4,0,0])::real^5)"
value "consistent (list_of_list_to_matrix ([[1,0,0],[0,1,0],[0,0,1],[0,0,0],[0,0,0]])::real^3^5) (list_to_vec([2,3,4,0,0])::real^5)"
value "inconsistent (list_of_list_to_matrix ([[1,0,0],[0,1,0],[3,0,1],[0,7,0],[0,0,9]])::real^3^5) (list_to_vec([2,0,4,0,0])::real^5)"
value "dependent_and_consistent (list_of_list_to_matrix ([[1,0,0],[0,1,0]])::real^3^2) (list_to_vec([3,4])::real^2)"
value "independent_and_consistent (mat 1::real^3^3) (list_to_vec([3,4,5])::real^3)"

subsubsection\<open>Solving systems of linear equations\<close>

text\<open>Examples on solving linear systems.\<close>

definition print_result_solve
  where "print_result_solve A = (if A = None then None else Some (vec_to_list (fst (the A)), vec_to_list` (snd (the A))))" 

value "let A = (list_of_list_to_matrix [[4,5,8],[9,8,7],[4,6,1]]::real^3^3);
                  b=(list_to_vec [4,5,8]::real^3)
                  in (print_result_solve (solve A b))"

value "let A = (list_of_list_to_matrix [[0,0,0],[0,0,0],[0,0,1]]::real^3^3);
                  b=(list_to_vec [4,5,0]::real^3)
                  in (print_result_solve (solve A b))"

value "let A = (list_of_list_to_matrix [[3,2,5,2,7],[6,4,7,4,5],[3,2,-1,2,-11],[6,4,1,4,-13]]::real^5^4); 
                  b=(list_to_vec [0,0,0,0]::real^4)
                  in (print_result_solve (solve A b))"

value "let A = (list_of_list_to_matrix [[1,2,1],[-2,-3,-1],[2,4,2]]::real^3^3); 
                  b=(list_to_vec [-2,1,-4]::real^3)
                  in (print_result_solve (solve A b))"

value "let A = (list_of_list_to_matrix [[1,1,-4,10],[3,-2,-2,6]]::real^4^2); 
                  b=(list_to_vec [24,15]::real^2)
                  in (print_result_solve (solve A b))"

end
