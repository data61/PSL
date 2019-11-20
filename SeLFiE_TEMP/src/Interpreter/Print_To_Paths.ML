(*  Title:      PSL/SeLFeE/src/Print_To_Paths_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** signature PRINT_TO_PATHS ***)
signature PRINT_TO_PATHS =
sig

type path_to_unode_table;
type print_to_paths_table;

val path_to_unode_table_to_print_to_paths_table: path_to_unode_table -> print_to_paths_table;

end;

(*** structure INNER_PRINT_TO_INNER_PATHS ***)
structure Print_To_Paths: PRINT_TO_PATHS =
struct

type path_to_unode_table  = UN.unode Inner_Path_Table.table;
type print_to_paths_table = UN.inner_path list Print_Table.table;

fun path_to_unode_table_to_print_to_paths_table (inner_path_to_unode_table:path_to_unode_table) =
  let
    val inner_path_n_unode_list    = Inner_Path_Table.dest inner_path_to_unode_table      : (UN.inner_path * UN.unode ) list;
    val inner_path_n_print_list    = List.map (apsnd #print) inner_path_n_unode_list: (UN.inner_path * UN.print) list;
    val print_n_inner_path_list    = map swap inner_path_n_print_list               : (UN.print * UN.inner_path) list;
    val print_to_inner_paths_table = Print_Table.make_list print_n_inner_path_list  : print_to_paths_table;
  in
    print_to_inner_paths_table: print_to_paths_table
  end;

end;

(*** structure Outer_Print_To_Outer_Paths ***)
structure Outer_Print_To_Outer_Paths: PRINT_TO_PATHS =
struct

type path_to_unode_table  = Outer_Path_To_Outer_Unode.path_to_unode_table;
type print_to_paths_table = outer_path list Print_Table.table;

fun path_to_unode_table_to_print_to_paths_table (outer_path_to_outer_unode_table: Outer_Path_To_Outer_Unode.path_to_unode_table) =
  let
    val outer_path_n_outer_unode_list    = Outer_Path_Table.dest outer_path_to_outer_unode_table;
    val outer_path_n_print_list          = List.map (apsnd (#print o #unode)) outer_path_n_outer_unode_list: (outer_path * UN.print) list;
    val outer_print_n_outer_path_list    = map swap outer_path_n_print_list                                : (UN.print * outer_path) list;
    val outer_print_to_outer_paths_table = Print_Table.make_list outer_print_n_outer_path_list             : print_to_paths_table;
  in
    outer_print_to_outer_paths_table: print_to_paths_table
  end;

end;