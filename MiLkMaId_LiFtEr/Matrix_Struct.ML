(*  Title:      PSL/MiLkMaId_LiFtEr/Matrix_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Utility fucntions about matrices.
*)
structure Matrix: MATRIX =
struct

(*I guess the massive use of data-constructors is sub-optimal in terms of run-time performance.
 * However, the code base is less confusing with those data-constructors, and the run-time
 * performance is not critical in this project.*)
datatype 'a row                   = Row      of 'a list;
datatype 'a column                = Column   of 'a list;
datatype 'a row_of_columns_matrix = RCMatrix of 'a column row;
datatype 'a column_of_rows_matrix = CRMatrix of 'a row column;

fun nth_of_a_column     (Column   rows)    (n:int) = nth    rows    n;
fun nth_of_a_row        (Row      columns) (n:int) = nth    columns n;
fun numbs_in_a_row      (Row      columns)         = length columns;
fun numbs_in_a_column   (Column   rows)            = length rows;
fun row_to_list         (Row      columns)         = columns: 'a list;
fun column_to_list      (Column   rows)            = rows   : 'a list;
fun dest_rcmatrix       (RCMatrix row_of_columns)  = row_of_columns: 'a column row;
fun dest_crmatrix       (CRMatrix column_of_rows)  = column_of_rows: 'a row column;
fun rcmatrix_to_columns (RCMatrix row_of_columns)  = row_to_list    row_of_columns: 'a column list;
fun crmatrix_to_rows    (CRMatrix column_of_rows)  = column_to_list column_of_rows: 'a row list;

fun rcmatrix_to_element_at_mth_row_nth_column (RCMatrix row_of_columns: 'a row_of_columns_matrix) (row_index: int) (column_index: int) =
     SOME row_of_columns
 >>= try (fn row    => nth_of_a_row    row    row_index)
 >>= try (fn column => nth_of_a_column column column_index);

fun are_same_ints (x::xs) = forall (curry (op =) x) xs
 |  are_same_ints []      = true;

(* How to check if a matrix is regular or not. *)
fun is_regular_rcmatrix (RCMatrix row_of_columns:'a row_of_columns_matrix) =
  let
    val numbers_of_elems_in_columns = map numbs_in_a_column (row_to_list row_of_columns);
  in
    are_same_ints numbers_of_elems_in_columns
  end;

fun is_regular_crmatrix (CRMatrix column_of_rows:'a column_of_rows_matrix) =
  let
    val numbers_of_elems_in_rows = map numbs_in_a_row (column_to_list column_of_rows);
  in
    are_same_ints numbers_of_elems_in_rows
  end;

fun rcmatrix_to_nth_column (rcmatrix:'a row_of_columns_matrix) (n:int) =
  let
    val list_of_columns  = rcmatrix_to_columns rcmatrix: 'a column list;
  in
    nth list_of_columns n: 'a column
  end;

fun crmatrix_to_nth_row (crmatrix:'a column_of_rows_matrix) (n:int) =
  let
    val list_of_rows  = crmatrix_to_rows crmatrix: 'a row list;
  in
    nth list_of_rows n: 'a row
  end;

fun rcmatrix_to_nth_row (rcmatrix:'a row_of_columns_matrix) (n:int) =
  let
    val list_of_columns = rcmatrix_to_columns rcmatrix                               : 'a column list;
    val nth_row_elems   = map (fn column => nth_of_a_column column n) list_of_columns: 'a list;
  in
    Row nth_row_elems: 'a row
  end;

fun crmatrix_to_nth_column (crmatrix:'a column_of_rows_matrix) (n:int) =
  let
    val list_of_rows     = crmatrix_to_rows crmatrix                      : 'a row list;
    val nth_column_elems = map (fn row => nth_of_a_row row n) list_of_rows: 'a list;
  in
    Column nth_column_elems: 'a column
  end;

local

fun rcmatrix_to_crmatrix' (rcmatrix: 'a row_of_columns_matrix) =
  let
    val list_of_columns  = rcmatrix_to_columns rcmatrix    : 'a column list;
    val opt_first_column = try hd list_of_columns          : 'a column option;
    val opt_numb_rows    = opt_first_column
                       >>= try column_to_list
                       >>= try length                      : int option;
    val numb_rows        = Option.getOpt (opt_numb_rows, 0): int;
    val list_of_rows = List.tabulate (numb_rows, rcmatrix_to_nth_row rcmatrix): 'a row list;
    val column_of_rows = Column list_of_rows: 'a row column;
    val crmatrix       = CRMatrix column_of_rows;
  in
    crmatrix: 'a column_of_rows_matrix
  end;

in

fun rcmatrix_to_crmatrix (rcmatrix: 'a row_of_columns_matrix) =
  if   is_regular_rcmatrix rcmatrix
  then SOME (rcmatrix_to_crmatrix' rcmatrix)
  else NONE;

end;

local

fun crmatrix_to_rcmatrix' (crmatrix: 'a column_of_rows_matrix) =
  let
    val list_of_rows     = crmatrix_to_rows crmatrix    : 'a row list;
    val opt_first_row    = try hd list_of_rows          : 'a row option;
    val opt_numb_columns = opt_first_row
                       >>= try row_to_list
                       >>= try length                : int option;
    val numb_columns     = Option.getOpt (opt_numb_columns, 0): int;
    val list_of_columns  = List.tabulate (numb_columns, crmatrix_to_nth_column crmatrix): 'a column list;
    val row_of_columns   = Row list_of_columns: 'a column row;
    val rcmatrix         = RCMatrix row_of_columns;
  in
    rcmatrix: 'a row_of_columns_matrix
  end;

in

fun crmatrix_to_rcmatrix (crmatrix: 'a column_of_rows_matrix) =
  if   is_regular_crmatrix crmatrix
  then SOME (crmatrix_to_rcmatrix' crmatrix)
  else NONE;                                             

end;

end;