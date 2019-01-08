(*  Title:      PSL/MiLkMaId_LiFtEr/Term_Table_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The conversion to transform term to a format more amenable to LiFtEr.
The overall work-flow is:
  term                === trm_to_trm_w_prnt ==========================> (* Unique_Node *)
  trm_w_prnt          === trm_w_prnt_to_utrm_w_prnt ==================> (* Unique_Node *)
  utrm_w_prnt         === utrm_w_prnt_to_futrm_w_prnt ================> (* Unique_Node *)
  futrm_w_prnt        === futrm_w_prnt_to_futrm_w_prnt_n_path ========> (* Unique_Node *)
  futrm_w_prnt_n_path === futrm_w_prnt_n_path_to_unique_nodes ========> (* Unique_Node *)
  unique_nodes        === unique_nodes_to_unique_nodes_w_auxiliary ===> (* Term_Table  *)
  nodes_w_auxiliary
*)

(*** Term_Table ***)
structure Term_Table: TERM_TABLE =
struct

val list_fold = fold;
open One_Term;
open Unique_Node;

type trm_table     = unique_node_wo_path table;
type trm_table_aux = unique_node_w_aux_wo_path table;

fun split_unique_node (unode:unique_node): path * unique_node_wo_path =
 (#path unode                  : path,
  {node = #node unode          : node,
   print = #print unode: print}: unique_node_wo_path);

fun to_be_folded (key_val_pair:(path * 'a)) (table: 'a table) = update_new key_val_pair table;

fun list_to_table (key_val_pairs: (path * 'a) list) = list_fold to_be_folded key_val_pairs empty; 

fun unique_nodes_to_trm_table (unodes:unique_nodes) = List.map split_unique_node unodes |> list_to_table;

val unique_node_wo_path_to_unique_node_w_auxiliary = undefined: unique_node_wo_path table -> Proof.state -> trm_table_aux;

type print_to_paths_table = Unique_Node.path list Print_Table.table;

val print_to_paths = undefined: Unique_Node.print -> Unique_Node.path list;

type abs_pstate =
  {fst_subg: trm_table,
   usings  : trm_table list};

type abs_pstate_w_aux =
  {fst_subg: trm_table_aux,
   usings  : trm_table_aux list};

end;