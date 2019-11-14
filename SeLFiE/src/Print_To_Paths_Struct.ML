(*  Title:      PSL/SeLFeE/src/Print_To_Paths_struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Print_To_Paths: PRINT_TO_PATHS =
struct

open Path_To_Unode;

type print_to_paths_table = UN.path list Print_Table.table;

fun path_to_unode_table_to_print_to_paths_table (path_to_unode_table:path_to_unode_table) =
  let
    val path_n_unode_list      = Path_Table.dest path_to_unode_table                        : (UN.path * UN.unode ) list;
    val path_n_print_list      = List.map (apsnd #print) path_n_unode_list                  : (UN.path * UN.print) list;
    val print_n_path_list      = map swap path_n_print_list                                 : (UN.print * UN.path) list;
    val print_to_paths_table   = Print_Table.make_list print_n_path_list                    : print_to_paths_table;
  in
    print_to_paths_table: print_to_paths_table
  end;

end;