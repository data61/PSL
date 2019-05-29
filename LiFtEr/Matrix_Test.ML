(*  Title:      PSL/LiFtEr/Matrix_Test.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Unit test for utility fucntions about matrices.
*)
structure Matrix_Test =
struct

open Matrix;

val rc_123456789 = RCMatrix (
Row [Column [1,2,3],
     Column [4,5,6],
     Column [7,8,9]]);

val rc_147258369 = RCMatrix (
Row [Column [1,4,7],
     Column [2,5,8],
     Column [3,6,9]]);

val cr_147258369 = CRMatrix (
Column [Row [1,4,7],
        Row [2,5,8],
        Row [3,6,9]]);

val cr_123456789 = CRMatrix (
Column [Row [1,2,3],
        Row [4,5,6],
        Row [7,8,9]]);

val _ = @{assert} ((SOME cr_147258369) = rcmatrix_to_crmatrix rc_123456789);
val _ = @{assert} ((SOME rc_123456789) = crmatrix_to_rcmatrix cr_147258369);
val _ = @{assert} ((SOME rc_147258369) = transpose_rcmatrix   rc_123456789);
val _ = @{assert} ((SOME cr_147258369) = transpose_crmatrix   cr_123456789);
val _ = @{assert} (SOME 3 = Matrix.rcmatrix_to_element_at_mth_row_nth_column rc_123456789 0 2);
val _ = @{assert} (SOME 3 = Matrix.crmatrix_to_element_at_mth_row_nth_column cr_123456789 0 2);

end;
