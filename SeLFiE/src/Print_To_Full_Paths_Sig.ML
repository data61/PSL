(*  Title:      PSL/SeLFeE/src/Print_To_Full_Paths_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature PRINT_TO_FULL_PATHS =
sig

type print_to_full_paths_table = full_path list Print_Table.table;

val full_path_to_fpunode_table_to_print_to_paths_table: Full_Path_To_Fpunode.full_path_to_fpunode_table -> print_to_full_paths_table;

end;