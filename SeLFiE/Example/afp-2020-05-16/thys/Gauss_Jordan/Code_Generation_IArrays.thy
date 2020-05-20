(*  
    Title:      Code_Generation_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Exporting code to SML and Haskell\<close>

theory Code_Generation_IArrays
imports
  Examples_Gauss_Jordan_IArrays
begin

subsection\<open>Exporting code\<close>

text\<open>The following two equations are necessary to execute code. If we don't remove them from code unfold, the exported code
will not work (there exist problems with the number 1 and number 0. Those problems appear when the HMA library is imported).\<close>

lemma [code_unfold del]: "1 \<equiv> real_of_rat 1" by simp
lemma [code_unfold del]: "0 \<equiv> real_of_rat 0" by simp

definition "matrix_z2 = IArray[IArray[0,1], IArray[1,1::bit], IArray[1,0::bit]]"
definition "matrix_rat = IArray[IArray[1,0,8], IArray[5.7,22,1], IArray[41,-58/7,78::rat]]"
definition "matrix_real = IArray[IArray[0,1], IArray[1,-2::real]]"
definition "vec_rat = IArray[21,5,7::rat]"

definition "print_result_Gauss A = iarray_of_iarray_to_list_of_list (Gauss_Jordan_iarrays A)"
definition "print_rank A = rank_iarray A"
definition "print_det A = det_iarrays A"

definition "print_result_z2 = print_result_Gauss (matrix_z2)"
definition "print_result_rat = print_result_Gauss (matrix_rat)"
definition "print_result_real = print_result_Gauss (matrix_real)"

definition "print_rank_z2 = print_rank (matrix_z2)"
definition "print_rank_rat = print_rank (matrix_rat)"
definition "print_rank_real = print_rank (matrix_real)"

definition "print_det_rat = print_det (matrix_rat)"
definition "print_det_real = print_det (matrix_real)"

definition "print_inverse A = inverse_matrix_iarray A"
definition "print_inverse_real A = print_inverse (matrix_real)"
definition "print_inverse_rat A = print_inverse (matrix_rat)"

definition "print_system A b = print_result_system_iarrays (solve_iarrays A b)"
definition "print_system_rat = print_result_system_iarrays (solve_iarrays matrix_rat vec_rat)"

subsection\<open>The Mathematica bug\<close>

text\<open>Varona et al \cite{VA} detected that the commercial software \<open>Mathematica\<registered>\<close>, 
in its versions 8.0, 9.0 and 9.0.1, was computing erroneously determinants of matrices 
of big integers, even for small dimensions  (in their work they present an example of a 
matrix of dimension \<open>14 \<times> 14\<close>). The situation is
such that even the same determinant, computed twice, produces two different and wrong results.

Here we reproduce that example. The computation of the determinant is correctly carried out by
the exported code from this formalization, in both SML and Haskell.
\<close>

definition "powersMatrix = 
IArray[
IArray[10^123,0,0,0,0,0,0,0,0,0,0,0,0,0],
IArray[0,10^152,0,0,0,0,0,0,0,0,0,0,0,0],
IArray[0,0,10^185,0,0,0,0,0,0,0,0,0,0,0],
IArray[0,0,0,10^220,0,0,0,0,0,0,0,0,0,0],
IArray[0,0,0,0,10^397,0,0,0,0,0,0,0,0,0],
IArray[0,0,0,0,0,10^449,0,0,0,0,0,0,0,0],
IArray[0,0,0,0,0,0,10^503,0,0,0,0,0,0,0],
IArray[0,0,0,0,0,0,0,10^563,0,0,0,0,0,0],
IArray[0,0,0,0,0,0,0,0,10^979,0,0,0,0,0],
IArray[0,0,0,0,0,0,0,0,0,10^1059,0,0,0,0],
IArray[0,0,0,0,0,0,0,0,0,0,10^1143,0,0,0],
IArray[0,0,0,0,0,0,0,0,0,0,0,10^1229,0,0],
IArray[0,0,0,0,0,0,0,0,0,0,0,0,10^1319,0],
IArray[0,0,0,0,0,0,0,0,0,0,0,0,0,(10^1412)::rat]]"


definition "basicMatrix = 
IArray[
IArray[-32, 69, 89,-60,-83,-22,-14,-58,85,56,-65,-30,-86,-9],
IArray[6, 99, 11, 57, 47,-42,-48,-65, 25, 50,-70,-3,-90, 31],
IArray[78, 38, 12, 64,-67,-4,-52,-65, 19, 71, 38,-17, 51,-3],
IArray[-93, 30, 89, 22, 13, 48,-73, 93, 11,-97,-49, 61,-25,-4],
IArray[54,-22, 54,-53,-52, 64, 19, 1, 81,-72,-11, 50, 0,-81],
IArray[65,-58, 3, 57, 19, 77, 76,-57,-80, 22, 93,-85, 67, 58],
IArray[29,-58, 47, 87, 3,-6,-81, 5, 98, 86,-98, 51,-62,-66],
IArray[93,-77, 16,-64, 48, 84, 97, 75, 89, 63, 34,-98,-94, 19],
IArray[45,-99, 3,-57, 32, 60, 74, 4, 69, 98,-40,-69,-28,-26],
IArray[-13, 51,-99,-2, 48, 71,-81,-32, 78, 27,-28,-22, 22, 94],
IArray[11, 72,-74, 86, 79,-58,-89, 80, 70, 55,-49, 51,-42, 66],
IArray[-72, 53, 49,-46, 17,-22,-48,-40,-28,-85, 88,-30, 74, 32],
IArray[-92,-22,-90, 67,-25,-28,-91,-8, 32,-41, 10, 6, 85, 21],
IArray[47,-73,-30,-60, 99, 9,-86,-70, 84, 55, 19, 69, 11,-84::rat]]"

definition "smallMatrix=
IArray[
IArray[528, 853,-547,-323, 393,-916,-11,-976, 279,-665, 906,-277, 103,-485],
IArray[878, 910,-306,-260, 575,-765,-32, 94, 254, 276,-156, 625,-8,-566],
IArray[-357, 451,-475, 327,-84, 237, 647, 505,-137, 363,-808, 332, 222,-998],
IArray[-76, 26,-778, 505, 942,-561,-350, 698,-532,-507,-78,-758, 346,-545],
IArray[-358, 18,-229,-880,-955,-346, 550,-958, 867,-541,-962, 646, 932, 168],
IArray[192, 233, 620,955,-877, 281, 357,-226,-820, 513,-882, 536,-237, 877],
IArray[-234,-71,-831, 880,-135,-249,-427, 737, 664, 298,-552,-1,-712,-691],
IArray[80, 748, 684, 332, 730,-111,-643, 102,-242,-82,-28, 585, 207,-986],
IArray[967, 1,-494, 633, 891,-907,-586, 129, 688, 150,-501,-298, 704,-68],
IArray[406,-944,-533,-827, 615, 907,-443,-350, 700,-878, 706, 1,800, 120],
IArray[33,-328,-543, 583,-443,-635,904,-745,-398,-110, 751, 660, 474, 255],
IArray[-537,-311, 829, 28, 175, 182,-930, 258,-808,-399,-43,-68,-553, 421],
IArray[-373,-447,-252,-619,-418, 764, 994,-543,-37,-845, 30,-704, 147,-534],
IArray[638,-33, 932,-335,-75,-676,-934, 239, 210, 665, 414,-803, 564,-805::rat]]"

definition "bigMatrix=(basicMatrix **i powersMatrix) + smallMatrix"

end
