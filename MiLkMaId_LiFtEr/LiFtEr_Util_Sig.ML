(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Util_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Helper functions for LiFtEr.
*)
signature LIFTER_UTIL =
sig

(*Use One_Term.keys to implement it.*)

val unode_table_to_lowest_fvars: Term_Table.unode_table -> Unique_Node.path list;

val path_to_ancestor_paths: Unique_Node.path -> Unique_Node.path list;

val path_to_descendent_paths: Unique_Node.path -> Unique_Node.path list;

end;