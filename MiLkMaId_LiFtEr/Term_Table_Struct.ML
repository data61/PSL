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
structure OT = One_Term;
structure UN = Unique_Node;
structure PT = Print_Table;

type trm_table     = UN.unique_node_wo_path OT.table;
type trm_table_aux = UN.unique_node_w_aux_wo_path OT.table;

fun split_unique_node (unode:UN.unique_node): UN.path * UN.unique_node_wo_path =
 (#path unode                     : UN.path,
  {node = #node unode             : UN.node,
   print = #print unode: UN.print}: UN.unique_node_wo_path);

fun to_be_folded (key_val_pair:(UN.path * 'a)) (table: 'a OT.table) = OT.update_new key_val_pair table;

fun list_to_table (key_val_pairs: (UN.path * 'a) list) = list_fold to_be_folded key_val_pairs OT.empty;

fun unique_nodes_to_trm_table (unodes:UN.unique_nodes) = List.map split_unique_node unodes |> list_to_table;

val unique_node_wo_path_to_unique_node_w_auxiliary = undefined: UN.unique_node_wo_path OT.table -> Proof.state -> trm_table_aux;

type print_to_paths_table = Unique_Node.path list Print_Table.table;

val print_to_paths = undefined: Unique_Node.print -> Unique_Node.path list;

fun gen_trm_table_to_print_paths_table (trm_table) (get_print)=
  let
    val path_n_unode_s    = One_Term.dest trm_table;
    val path_n_print_s    = List.map (apsnd get_print) path_n_unode_s;
    val print_n_path_s    = map swap path_n_print_s;
    val print_paths_table = PT.make_list print_n_path_s;
  in
    print_paths_table: print_to_paths_table
  end;

fun trm_table_to_print_paths_table     (trm_table:    trm_table    ) = gen_trm_table_to_print_paths_table trm_table     (#print: UN.unique_node_wo_path       -> UN.print): print_to_paths_table;
fun trm_table_aux_to_print_paths_table (trm_table_aux:trm_table_aux) = gen_trm_table_to_print_paths_table trm_table_aux (#print: UN.unique_node_w_aux_wo_path -> UN.print): print_to_paths_table;

type abs_pstate =
  {fst_subg: trm_table,
   usings  : trm_table list};

type abs_pstate_w_aux =
  {fst_subg: trm_table_aux,
   usings  : trm_table_aux list};

end;