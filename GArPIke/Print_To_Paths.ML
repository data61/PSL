(*  Title:      PSL/SeLFeE/src/Print_To_Paths_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** signature PRINT_TO_PATHS ***)
signature PRINT_TO_PATHS =
sig

type path;
type path_to_unode_table;
type print_to_paths_table;

val print_to_paths_table_to_prints: print_to_paths_table -> strings;
val path_to_unode_table_to_print_to_paths_table: path_to_unode_table -> print_to_paths_table;

end;

(*** functor from_Path_Table_and_Path_To_Unode_to_Print_To_Paths ***)
functor from_Path_Table_and_Path_To_Unode_to_Print_To_Paths (Path_Table: TABLE): PRINT_TO_PATHS =
struct

type path = Path_Table.key;
type path_to_unode_table  = UN.unode Path_Table.table;
type print_to_paths_table = Path_Table.key list Print_Table.table;

fun print_to_paths_table_to_prints table = Print_Table.keys table;

fun path_to_unode_table_to_print_to_paths_table (inner_path_to_unode_table:UN.unode Path_Table.table) =
  let
    val path_n_unode_list    = Path_Table.dest inner_path_to_unode_table: (Path_Table.key * UN.unode) list;
    val path_n_print_list    = List.map (apsnd #print) path_n_unode_list: (Path_Table.key * string) list;
    val print_n_path_list    = map swap path_n_print_list               : (string * Path_Table.key) list;
    val print_to_paths_table = Print_Table.make_list print_n_path_list  : print_to_paths_table;
  in
    print_to_paths_table: print_to_paths_table
  end;

end;