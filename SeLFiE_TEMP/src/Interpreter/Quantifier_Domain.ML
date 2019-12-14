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

(*** functor: make_Quantifier_Domain  ***)
functor make_Quantifier_Domain
  (structure Print_To_Paths:PRINT_TO_PATHS
         and Path_To_Unode :PATH_TO_UNODE
         and Eval_Variable:EVAL_VARIABLE
   sharing type Print_To_Paths.path                = Path_To_Unode.path
   sharing type Print_To_Paths.path_to_unode_table = Path_To_Unode.path_to_unode_table): QUANTIFIER_DOMAIN =
struct

datatype qtyp  = QPath | QPrint | QNumber;
type parameter = Eval_Variable.parameter;

val qtyp_to_qdomain = undefined: qtyp -> parameter list;

type path                 = Print_To_Paths.path;
type path_to_node_table   = Path_To_Unode.path_to_unode_table;
type print_to_paths_table = Print_To_Paths.print_to_paths_table;

fun mk_all_paths  pst term = Path_To_Unode.pst_n_trm_to_path_to_unode_table pst term |> Path_To_Unode.table_to_paths: path list;
fun mk_all_prints pst term =
  let
    val path_to_node_table   = Path_To_Unode.pst_n_trm_to_path_to_unode_table pst term                      : Path_To_Unode.path_to_unode_table;
    val print_to_paths_table = Print_To_Paths.path_to_unode_table_to_print_to_paths_table path_to_node_table: print_to_paths_table;
  in
    Print_To_Paths.print_to_paths_table_to_prints print_to_paths_table
  end;

fun mk_all_numbers _ = ();(*TODO*)

end;