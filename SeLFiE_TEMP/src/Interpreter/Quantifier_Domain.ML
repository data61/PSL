(*  Title:      PSL/SeLFiE/src/Eval_Quantifier_Domain.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** signature: QUANTIFIER_DOMAIN  ***)
signature QUANTIFIER_DOMAIN =
sig

type qtyp;
type parameter;

val  qtyp_to_qdomain: qtyp -> parameter list;

type path;
type path_to_node_table;
type print_to_paths_table;

val mk_all_paths:  Proof.state -> term -> path list;
val mk_all_prints: Proof.state -> term -> SeLFiE_Util.prints;

end;

(*** structure: Inner_Quantifier_Domain  ***)
structure Inner_Quantifier_Domain: QUANTIFIER_DOMAIN =
struct

datatype qtyp  = QPath | QPrint | QNumber;
type parameter = Eval_Inner_Parameter_With_Bool.parameter;

val qtyp_to_qdomain = undefined: qtyp -> parameter list;

type path  = UN.inner_path;
type path_to_node_table   = path Path_Table.table;
type print_to_paths_table = path list Print_Table.table;

fun mk_all_paths  pst term = Inner_Path_To_Inner_Unode.pst_n_trm_to_path_to_unode_table pst term |> Path_Table.keys: path list;
fun mk_all_prints pst term =
  let
    val path_to_node_table   = Inner_Path_To_Inner_Unode.pst_n_trm_to_path_to_unode_table pst term          : Inner_Path_To_Inner_Unode.path_to_unode_table;
    val print_to_paths_table = Print_To_Paths.path_to_unode_table_to_print_to_paths_table path_to_node_table: print_to_paths_table;
  in
    Print_Table.keys print_to_paths_table
  end;
end;

structure Outer_Quantifier_Domain: QUANTIFIER_DOMAIN =
struct

datatype qtyp  = QPath | QPrint | QNumber;
type parameter = Eval_Outer_Parameter_With_Bool.parameter;

val qtyp_to_qdomain = undefined: qtyp -> parameter list;

type path                 = outer_path;
type path_to_node_table   = outer_path Outer_Path_Table.table;
type print_to_paths_table = outer_path Print_Table.table;

fun mk_all_paths  pst _ = Outer_Path_To_Outer_Unode.pst_n_trm_to_path_to_unode_table pst Term.dummy |> Outer_Path_Table.keys: outer_path list;
fun mk_all_prints pst term =
  let
    val outer_path_to_outer_unode_table   = Outer_Path_To_Outer_Unode.pst_n_trm_to_path_to_unode_table pst Term.dummy
      : Outer_Path_To_Outer_Unode.path_to_unode_table;
    val outer_print_to_outer_paths_table = Outer_Print_To_Outer_Paths.path_to_unode_table_to_print_to_paths_table outer_path_to_outer_unode_table
      : Outer_Print_To_Outer_Paths.print_to_paths_table;
  in
    Print_Table.keys outer_print_to_outer_paths_table
  end;
end;

functor from_Path_To_Unode_and_Print_To_Paths_to_Quantifier_Domain
  (structure Path_To_Unode : PATH_TO_UNODE
   and       Print_To_Paths: PRINT_TO_PATHS) =
struct

end;