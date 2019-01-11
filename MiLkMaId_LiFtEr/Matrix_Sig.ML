(*  Title:      PSL/MiLkMaId_LiFtEr/Matrix_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Utility fucntions about matrices.
*)
signature MATRIX =
sig

(*I guess the massive use of data-constructors is sub-optimal in terms of run-time performance.
 * However, the code base is less confusing with those data-constructors, and the run-time
 * performance is not critical in this project.*)
datatype 'a row                   = Row      of 'a list;
datatype 'a column                = Column   of 'a list;
datatype 'a row_of_columns_matrix = RCMatrix of 'a column row;
datatype 'a column_of_rows_matrix = CRMatrix of 'a row column;

val nth_of_a_column    : 'a column -> int -> 'a;
val nth_of_a_row       : 'a row    -> int -> 'a;
val numbs_in_a_row     : 'a row    -> int;
val numbs_in_a_column  : 'a column -> int;
val dest_row           : 'a row    -> 'a list;
val dest_column        : 'a column -> 'a list;
val map_row            :('a -> 'b) -> 'a row -> 'b row;
val map_column         :('a -> 'b) -> 'a column -> 'b column;
val dest_rcmatrix      : 'a row_of_columns_matrix -> 'a column row;
val dest_crmatrix      : 'a column_of_rows_matrix -> 'a row    column;
val map_rcmatrix       :('a -> 'b) -> 'a row_of_columns_matrix -> 'b row_of_columns_matrix;
val map_crmatrix       :('a -> 'b) -> 'a column_of_rows_matrix -> 'b column_of_rows_matrix;

val rcmatrix_to_columns: 'a row_of_columns_matrix -> 'a column list;
val crmatrix_to_rows   : 'a column_of_rows_matrix -> 'a row    list;

val rcmatrix_to_element_at_mth_row_nth_column: 'a row_of_columns_matrix -> int (*row_index*) -> int (*column_index*) -> 'a option;
(*TODO: rename*)
val are_same_ints: ''a list -> bool;

val is_regular_rcmatrix   : 'a row_of_columns_matrix -> bool;
val is_regular_crmatrix   : 'a column_of_rows_matrix -> bool;
val rcmatrix_to_nth_column: 'a row_of_columns_matrix -> int -> 'a column;
val crmatrix_to_nth_row   : 'a column_of_rows_matrix -> int -> 'a row;
val rcmatrix_to_nth_row   : 'a row_of_columns_matrix -> int -> 'a row;
val crmatrix_to_nth_column: 'a column_of_rows_matrix -> int -> 'a column;
val rcmatrix_to_crmatrix  : 'a row_of_columns_matrix -> 'a column_of_rows_matrix option;
val crmatrix_to_rcmatrix  : 'a column_of_rows_matrix -> 'a row_of_columns_matrix option;
val transpose_rcmatrix    : 'a row_of_columns_matrix -> 'a row_of_columns_matrix option;
val transpose_crmatrix    : 'a column_of_rows_matrix -> 'a column_of_rows_matrix option;
end;