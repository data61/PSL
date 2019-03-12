(*  Title:      PSL/MiLkMaId_LiFtEr/Term_Table_Sig.ML
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
  abs_pstate_w_aux = {subgoals: unode_aux_n_path_tables,
                      usings  : unode_aux_n_path_tables}
*)

(*** One_Term ***)
local

(* path_ord: This definition is more or less arbitrary. *)
fun path_ord ([],    []   ) = EQUAL
  | path_ord (_,     []   ) = GREATER
  | path_ord ([],     _   ) = LESS
  | path_ord (x::xs, y::ys) = case Int.compare (x, y) of
      EQUAL => path_ord (xs, ys)
    | diff  => diff;

fun prnt_ord (LiFtEr_Util.Print p1, LiFtEr_Util.Print p2) = String.compare (p1, p2);

in

structure One_Term    = Table (type key = Unique_Node.path  val ord = path_ord): TABLE;
structure Print_Table = Table (type key = Unique_Node.print val ord = prnt_ord): TABLE;

end;

(*** TERM_TABLE ***)
signature TERM_TABLE =
sig

type unode_table     = Unique_Node.unique_node_wo_path One_Term.table;
type unode_aux_table = Unique_Node.unique_node_w_aux_wo_path One_Term.table;

val unique_nodes_to_trm_table                     : Unique_Node.unique_nodes -> unode_table;
val unique_node_wo_path_to_unique_node_w_auxiliary: unode_table -> Proof.state -> unode_aux_table;

type paths_table  = Unique_Node.path list Print_Table.table;
type paths_tables = paths_table list;

val unode_table_to_print_paths_table    : unode_table     -> paths_table;
val unode_aux_table_to_print_paths_table: unode_aux_table -> paths_table;

type unode_n_path_table      = {unode_table    : unode_table,     paths_table: paths_table};
type unode_aux_n_path_table  = {unode_aux_table: unode_aux_table, paths_table: paths_table};
type unode_n_path_tables     = unode_n_path_table list;
type unode_aux_n_path_tables = unode_aux_n_path_table list;

val unode_table_to_unode_n_print_table        : unode_table     -> unode_n_path_table;
val unode_aux_table_to_unode_aux_n_print_table: unode_aux_table -> unode_aux_n_path_table;

val print_n_paths_table_to_paths: paths_table -> Unique_Node.print -> Unique_Node.path list;

type abs_pstate =
  {subgoals: unode_n_path_tables,
   usings  : unode_n_path_tables};

type abs_pstate_w_aux =
  {subgoals: unode_aux_n_path_tables,
   usings  : unode_aux_n_path_tables};

val pstate_to_abs_pstate_w_aux: Proof.state -> abs_pstate_w_aux;

(* location: first sub-goal = Nth_Subg 0. *)
datatype location = Nth_Subg of int | Chained_Fact of int;
type path_n_loc   = Unique_Node.path * location;
type path_n_locs  = path_n_loc list;

val in_subgoals     : location -> bool;
val in_chained_facts: location -> bool;
val same_location   : (location * location) -> bool;

val abs_pstate_w_aux_to_unode_aux_n_path_tables     : abs_pstate_w_aux -> paths_tables;
val abs_pstate_w_aux_n_loc_to_unode_aux_n_path_table: abs_pstate_w_aux -> location -> unode_aux_n_path_table;
val print_n_abs_pstate_w_aux_to_path_n_locs         : abs_pstate_w_aux -> LiFtEr_Util.print -> path_n_locs;

(*Use One_Term.keys to implement it.*)
val unode_aux_table_to_depth   : unode_aux_table -> int option;
val unode_table_to_lowest_fvars: unode_table -> Unique_Node.path list;
val path_to_ancestor_paths     : Unique_Node.path -> Unique_Node.path list;
val path_to_descendent_paths   : Unique_Node.path -> Unique_Node.path list;

end;