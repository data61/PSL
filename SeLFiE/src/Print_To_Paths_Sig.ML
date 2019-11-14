(*  Title:      PSL/SeLFeE/src/Print_To_Paths_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature PRINT_TO_PATHS =
sig

type path_to_unode_table  = Path_To_Unode.path_to_unode_table;
type print_to_paths_table = UN.path list Print_Table.table;

val path_to_unode_table_to_print_to_paths_table: path_to_unode_table -> print_to_paths_table;

end;