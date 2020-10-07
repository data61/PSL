(*  
    Title:      Examples_Gauss_Jordan_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Examples of computations over matrices represented as nested IArrays\<close>

theory Examples_Gauss_Jordan_IArrays
imports
  System_Of_Equations_IArrays
  Determinants_IArrays
  Inverse_IArrays
  Code_Bit
  "HOL-Library.Code_Target_Numeral"
(*"HOL-Library.Code_Real_Approx_By_Float"*)
begin

subsection\<open>Transformations between nested lists nested IArrays\<close>
definition iarray_of_iarray_to_list_of_list :: "'a iarray iarray => 'a list list"
  where "iarray_of_iarray_to_list_of_list A = map IArray.list_of (map ((!!) A) [0..<IArray.length A])"

text\<open>The following definitions are also in the file \<open>Examples_on_Gauss_Jordan_Abstract\<close>.\<close>

text\<open>Definitions to transform a matrix to a list of list and vice versa\<close>
definition vec_to_list :: "'a^'n::{finite, enum} => 'a list"
  where "vec_to_list A = map (($) A) (enum_class.enum::'n list)"

definition matrix_to_list_of_list :: "'a^'n::{finite, enum}^'m::{finite, enum} => 'a list list"
  where "matrix_to_list_of_list A = map (vec_to_list) (map (($) A) (enum_class.enum::'m list))"

text\<open>This definition should be equivalent to \<open>vector_def\<close> (in suitable types)\<close>
definition list_to_vec :: "'a list => 'a^'n::{enum, mod_type}"
  where "list_to_vec xs = vec_lambda (% i. xs ! (to_nat i))"

lemma [code abstract]: "vec_nth (list_to_vec xs) = (%i. xs ! (to_nat i))"
  unfolding list_to_vec_def by fastforce

definition list_of_list_to_matrix :: "'a list list => 'a^'n::{enum, mod_type}^'m::{enum, mod_type}"
  where "list_of_list_to_matrix xs = vec_lambda (%i. list_to_vec (xs ! (to_nat i)))"

lemma [code abstract]: "vec_nth (list_of_list_to_matrix xs) = (%i. list_to_vec (xs ! (to_nat i)))"
  unfolding list_of_list_to_matrix_def by auto

subsection\<open>Examples\<close>

text\<open>The following three lemmas are presented in both this file and in the 
\<open>Examples_Gauss_Jordan_Abstract\<close> one. They allow a more convenient printing of rational and
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

text\<open>From here on, we do the computations in two ways. The first one consists of executing the abstract functions (which internally will execute the ones over iarrays).
The second one runs directly the functions over iarrays.\<close>

subsubsection\<open>Ranks, dimensions and Gauss Jordan algorithm\<close>
text\<open>In the following examples, the theorem \<open>matrix_to_iarray_rank\<close> (which is the file \<open>Gauss_Jordan_IArrays\<close> 
  and it is a code unfold theorem) assures that the computation will be carried out using the iarrays representation.\<close>
value "vec.dim (col_space (list_of_list_to_matrix [[1,0,0,7,5],[1,0,4,8,-1],[1,0,0,9,8],[1,2,3,6,5]]::real^5^4))"
value "rank (list_of_list_to_matrix [[1,0,0,7,5],[1,0,4,8,-1],[1,0,0,9,8],[1,2,3,6,5]]::real^5^4)" 
value "vec.dim (null_space (list_of_list_to_matrix [[1,0,0,7,5],[1,0,4,8,-1],[1,0,0,9,8],[1,2,3,6,5]]::rat^5^4))"

value "rank_iarray (IArray[IArray[1::rat,0,0,7,5],IArray[1,0,4,8,-1],IArray[1,0,0,9,8],IArray[1,2,3,6,5]])" 
(*Identical matrices with coefficients in Z2 and R could have different rank in each field:*)
value "rank_iarray (IArray[IArray[1::real,0,1],IArray[1,1,0],IArray[0,1,1]])"
value "rank_iarray (IArray[IArray[1::bit,0,1],IArray[1,1,0],IArray[0,1,1]])"

text\<open>Examples on computing the Gauss Jordan algorithm.\<close>
value "iarray_of_iarray_to_list_of_list (matrix_to_iarray (Gauss_Jordan (list_of_list_to_matrix [[Complex 1 1,Complex 1 (- 1), Complex 0 0],[Complex 2 (- 1),Complex 1 3, Complex 7 3]]::complex^3^2)))"
value "iarray_of_iarray_to_list_of_list (Gauss_Jordan_iarrays(IArray[IArray[Complex 1 1,Complex 1 (- 1),Complex 0 0],IArray[Complex 2 (- 1),Complex 1 3,Complex 7 3]]))"

subsubsection\<open>Inverse of a matrix\<close>
text\<open>Examples on inverting matrices\<close>

definition "print_result_some_iarrays A = (if A = None then None else Some (iarray_of_iarray_to_list_of_list (the A)))" 

value "let A=(list_of_list_to_matrix [[1,1,2,4,5,9,8],[3,0,8,4,5,0,8],[3,2,0,4,5,9,8],[3,2,8,0,5,9,8],[3,2,8,4,0,9,8],[3,2,8,4,5,0,8],[3,2,8,4,5,9,0]]::real^7^7)
                    in print_result_some_iarrays (matrix_to_iarray_option (inverse_matrix A))"
value "let A=(IArray[IArray[1::real,1,2,4,5,9,8],IArray[3,0,8,4,5,0,8],IArray[3,2,0,4,5,9,8],IArray[3,2,8,0,5,9,8],IArray[3,2,8,4,0,9,8],IArray[3,2,8,4,5,0,8],IArray[3,2,8,4,5,9,0]])
                    in print_result_some_iarrays (inverse_matrix_iarray A)"

subsubsection\<open>Determinant of a matrix\<close>
text\<open>Examples on computing determinants of matrices\<close>

value "det (list_of_list_to_matrix ([[1,8,9,1,47],[7,2,2,5,9],[3,2,7,7,4],[9,8,7,5,1],[1,2,6,4,5]])::rat^5^5)"
value "det (list_of_list_to_matrix [[1,2,7,8,9],[3,4,12,10,7],[-5,4,8,7,4],[0,1,2,4,8],[9,8,7,13,11]]::rat^5^5)"

value "det_iarrays (IArray[IArray[1::real,2,7,8,9],IArray[3,4,12,10,7],IArray[-5,4,8,7,4],IArray[0,1,2,4,8],IArray[9,8,7,13,11]])"
value "det_iarrays (IArray[IArray[286,662,263,246,642,656,351,454,339,848],
IArray[307,489,667,908,103,47,120,133,85,834],
IArray[69,732,285,147,527,655,732,661,846,202],
IArray[463,855,78,338,786,954,593,550,913,378],
IArray[90,926,201,362,985,341,540,912,494,427],
IArray[384,511,12,627,131,620,987,996,445,216],
IArray[385,538,362,643,567,804,499,914,332,512],
IArray[879,159,312,187,827,503,823,893,139,546],
IArray[800,376,331,363,840,737,911,886,456,848],
IArray[900,737,280,370,121,195,958,862,957,754::real]])"


subsubsection\<open>Bases of the fundamental subspaces\<close>
text\<open>Examples on computing basis for null space, row space, column space and left null space.\<close>
(*Null_space basis:*)
value "let A = (list_of_list_to_matrix ([[1,3,-2,0,2,0],[2,6,-5,-2,4,-3],[0,0,5,10,0,15],[2,6,0,8,4,18]])::real^6^4) 
  in vec_to_list` (basis_null_space A)"
value "let A = (list_of_list_to_matrix ([[3,4,0,7],[1,-5,2,-2],[-1,4,0,3],[1,-1,2,2]])::real^4^4) 
  in vec_to_list` (basis_null_space A)"

value "let A = (IArray[IArray[1::real,3,-2,0,2,0],IArray[2,6,-5,-2,4,-3],IArray[0,0,5,10,0,15],IArray[2,6,0,8,4,18]]) 
  in IArray.list_of` (basis_null_space_iarrays A)"
value "let A = (IArray[IArray[3::real,4,0,7],IArray[1,-5,2,-2],IArray[-1,4,0,3],IArray[1,-1,2,2]])
  in IArray.list_of` (basis_null_space_iarrays A)"

(*Row_space basis*)
value "let A = (list_of_list_to_matrix ([[1,3,-2,0,2,0],[2,6,-5,-2,4,-3],[0,0,5,10,0,15],[2,6,0,8,4,18]])::real^6^4) 
    in vec_to_list` (basis_row_space A)"
value "let A = (list_of_list_to_matrix ([[3,4,0,7],[1,-5,2,-2],[-1,4,0,3],[1,-1,2,2]])::real^4^4) 
  in vec_to_list` (basis_row_space A)"

value "let A = (IArray[IArray[1::real,3,-2,0,2,0],IArray[2,6,-5,-2,4,-3],IArray[0,0,5,10,0,15],IArray[2,6,0,8,4,18]]) 
  in IArray.list_of` (basis_row_space_iarrays A)"
value "let A = (IArray[IArray[3::real,4,0,7],IArray[1,-5,2,-2],IArray[-1,4,0,3],IArray[1,-1,2,2]])
  in IArray.list_of` (basis_row_space_iarrays A)"

(*Col_space basis*)
value "let A = (list_of_list_to_matrix ([[1,3,-2,0,2,0],[2,6,-5,-2,4,-3],[0,0,5,10,0,15],[2,6,0,8,4,18]])::real^6^4) 
    in vec_to_list` (basis_col_space A)"
value "let A = (list_of_list_to_matrix ([[3,4,0,7],[1,-5,2,-2],[-1,4,0,3],[1,-1,2,2]])::real^4^4) 
  in vec_to_list` (basis_col_space A)"

value "let A = (IArray[IArray[1::real,3,-2,0,2,0],IArray[2,6,-5,-2,4,-3],IArray[0,0,5,10,0,15],IArray[2,6,0,8,4,18]]) 
  in IArray.list_of` (basis_col_space_iarrays A)"
value "let A = (IArray[IArray[3::real,4,0,7],IArray[1,-5,2,-2],IArray[-1,4,0,3],IArray[1,-1,2,2]])
  in IArray.list_of` (basis_col_space_iarrays A)"

(*Left_null_space basis*)
value "let A = (list_of_list_to_matrix ([[1,3,-2,0,2,0],[2,6,-5,-2,4,-3],[0,0,5,10,0,15],[2,6,0,8,4,18]])::real^6^4) 
    in vec_to_list` (basis_left_null_space A)"
value "let A = (list_of_list_to_matrix ([[3,4,0,7],[1,-5,2,-2],[-1,4,0,3],[1,-1,2,2]])::real^4^4) 
  in vec_to_list` (basis_left_null_space A)"

value "let A = (IArray[IArray[1::real,3,-2,0,2,0],IArray[2,6,-5,-2,4,-3],IArray[0,0,5,10,0,15],IArray[2,6,0,8,4,18]]) 
  in IArray.list_of` (basis_left_null_space_iarrays A)"
value "let A = (IArray[IArray[3::real,4,0,7],IArray[1,-5,2,-2],IArray[-1,4,0,3],IArray[1,-1,2,2]])
  in IArray.list_of` (basis_left_null_space_iarrays A)"


subsubsection\<open>Consistency and inconsistency\<close>

text\<open>Examples on checking the consistency/inconsistency of a system of equations. The theorems \<open>matrix_to_iarray_independent_and_consistent\<close> and 
\<open>matrix_to_iarray_dependent_and_consistent\<close> which are code theorems and they are in the file \<open>System_Of_Equations_IArrays\<close>
assure the execution using the iarrays representation.\<close>

value "independent_and_consistent (list_of_list_to_matrix ([[1,0,0],[0,1,0],[0,0,1],[0,0,0],[0,0,0]])::real^3^5) (list_to_vec([2,3,4,0,0])::real^5)"
value "consistent (list_of_list_to_matrix ([[1,0,0],[0,1,0],[0,0,1],[0,0,0],[0,0,0]])::real^3^5) (list_to_vec([2,3,4,0,0])::real^5)"
value "inconsistent (list_of_list_to_matrix ([[1,0,0],[0,1,0],[3,0,1],[0,7,0],[0,0,9]])::real^3^5) (list_to_vec([2,0,4,0,0])::real^5)"
value "dependent_and_consistent (list_of_list_to_matrix ([[1,0,0],[0,1,0]])::real^3^2) (list_to_vec([3,4])::real^2)"
value "independent_and_consistent (mat 1::real^3^3) (list_to_vec([3,4,5])::real^3)"


subsubsection\<open>Solving systems of linear equations\<close>
text\<open>Examples on solving linear systems.\<close>
definition "print_result_system_iarrays A = (if A = None then None else Some (IArray.list_of (fst (the A)), IArray.list_of` (snd (the A))))" 

value "let A = (list_of_list_to_matrix [[0,0,0],[0,0,0],[0,0,1]]::real^3^3); b=(list_to_vec [4,5,0]::real^3);
                  result = pair_vec_vecset (solve A b)
                  in print_result_system_iarrays (result)"
value "let A = (list_of_list_to_matrix [[3,2,5,2,7],[6,4,7,4,5],[3,2,-1,2,-11],[6,4,1,4,-13]]::real^5^4); b=(list_to_vec [0,0,0,0]::real^4);
                  result = pair_vec_vecset (solve A b)
                  in print_result_system_iarrays (result)"
value "let A = (list_of_list_to_matrix [[4,5,8],[9,8,7],[4,6,1]]::real^3^3); b=(list_to_vec [4,5,8]::real^3);
                  result = pair_vec_vecset (solve A b)
                  in print_result_system_iarrays (result)"

value "let A = (IArray[IArray[0::real,0,0],IArray[0,0,0],IArray[0,0,1]]); b=(IArray[4,5,0]);
                  result = (solve_iarrays A b)
                  in print_result_system_iarrays (result)"
value "let A = (IArray[IArray[3::real,2,5,2,7],IArray[6,4,7,4,5],IArray[3,2,-1,2,-11],IArray[6,4,1,4,-13]]); b=(IArray[0,0,0,0]);
                  result = (solve_iarrays A b)
                  in print_result_system_iarrays (result)"
value "let A = (IArray[IArray[4,5,8],IArray[9::real,8,7],IArray[4,6::real,1]]); b=(IArray[4,5,8]);
                  result = (solve_iarrays A b)
                  in print_result_system_iarrays (result)"

export_code
  rank_iarray
  inverse_matrix_iarray
  det_iarrays
  consistent_iarrays
  inconsistent_iarrays
  independent_and_consistent_iarrays
  dependent_and_consistent_iarrays
  basis_left_null_space_iarrays
  basis_null_space_iarrays
  basis_col_space_iarrays
  basis_row_space_iarrays
  solve_iarrays
  in SML
end
