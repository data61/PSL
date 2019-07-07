(*  Title:      PSL/SeLFeE/src/Print_To_Full_Paths_struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Print_To_Full_Paths: PRINT_TO_FULL_PATHS =
struct

open Full_Path_To_Fpunode;

type print_to_full_paths_table = full_path list Print_Table.table;

fun full_path_to_fpunode_table_to_print_to_paths_table (full_path_to_fpunode_table:full_path_to_fpunode_table) =
  let
    val full_path_n_fpunode_list = Full_Path_Table.dest full_path_to_fpunode_table            : (full_path * fpunode ) list;
    val full_path_n_print_list   = List.map (apsnd (#print o #unode)) full_path_n_fpunode_list: (full_path * UN.print) list;
    val print_n_full_path_list   = map swap full_path_n_print_list                            : (UN.print * full_path) list;
    val print_to_paths_table     = Print_Table.make_list print_n_full_path_list               : print_to_full_paths_table;
  in
    print_to_paths_table: print_to_full_paths_table
  end;

end;