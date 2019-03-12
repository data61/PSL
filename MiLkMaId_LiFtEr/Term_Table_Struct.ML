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

type unode_table     = UN.unique_node_wo_path       OT.table;
type unode_aux_table = UN.unique_node_w_aux_wo_path OT.table;

fun split_unique_node (unode:UN.unique_node): UN.path * UN.unique_node_wo_path =
 (#path unode                     : UN.path,
  {node = #node unode             : UN.node,
   print = #print unode: UN.print}: UN.unique_node_wo_path);

fun to_be_folded (key_val_pair:(UN.path * 'a)) (table: 'a OT.table) = OT.update_new key_val_pair table;

fun list_to_table (key_val_pairs: (UN.path * 'a) list) = list_fold to_be_folded key_val_pairs OT.empty;

fun unique_nodes_to_trm_table (unodes:UN.unique_nodes) = List.map split_unique_node unodes |> list_to_table;

val unique_node_wo_path_to_unique_node_w_auxiliary = undefined: UN.unique_node_wo_path OT.table -> Proof.state -> unode_aux_table;

type paths_table  = Unique_Node.path list Print_Table.table;
type paths_tables = paths_table list;

fun gen_trm_table_to_print_paths_table (trm_table) (get_print)=
  let
    val path_n_unode_s    = One_Term.dest trm_table;
    val path_n_print_s    = List.map (apsnd get_print) path_n_unode_s;
    val print_n_path_s    = map swap path_n_print_s;
    val print_paths_table = PT.make_list print_n_path_s;
  in
    print_paths_table: paths_table
  end;

fun unode_table_to_print_paths_table     (unode_table    :unode_table    ) = gen_trm_table_to_print_paths_table unode_table     (#print: UN.unique_node_wo_path       -> UN.print): paths_table;
fun unode_aux_table_to_print_paths_table (unode_aux_table:unode_aux_table) = gen_trm_table_to_print_paths_table unode_aux_table (#print: UN.unique_node_w_aux_wo_path -> UN.print): paths_table;

type unode_n_path_table      = {unode_table    : unode_table,     paths_table: paths_table};
type unode_aux_n_path_table  = {unode_aux_table: unode_aux_table, paths_table: paths_table};
type unode_n_path_tables     = unode_n_path_table list;
type unode_aux_n_path_tables = unode_aux_n_path_table list;

fun unode_table_to_unode_n_print_table (unode_table:unode_table) =
  {unode_table = unode_table,
   paths_table = unode_table_to_print_paths_table unode_table}: unode_n_path_table;

fun unode_aux_table_to_unode_aux_n_print_table (unode_aux_table:unode_aux_table) =
  {unode_aux_table = unode_aux_table,
   paths_table     = unode_aux_table_to_print_paths_table unode_aux_table}: unode_aux_n_path_table;

fun print_n_paths_table_to_paths (paths_table:paths_table) (print: UN.print) =
  Print_Table.lookup_list paths_table print;

type abs_pstate =
  {subgoals: unode_n_path_table list,
   usings  : unode_n_path_table list};

type abs_pstate_w_aux =
  {subgoals: unode_aux_n_path_tables,
   usings  : unode_aux_n_path_tables};


fun pstate_to_abs_pstate_w_aux (pst:Proof.state): abs_pstate_w_aux =
  let
    val chained_facts = Isabelle_Utils.pstate_to_usings pst
                     |> map Thm.prop_of: terms;
    val subgoals = Isabelle_Utils.pst_to_subgs pst: terms;
  in
  {subgoals = [],
   usings   = []}
  end;
(*
type abs_pstate_w_aux =
  {subgoals: unode_aux_n_path_tables,
   usings  : unode_aux_n_path_tables};
*)

(* location: first sub-goal = Nth_Subg 0. *)
datatype location = Nth_Subg of int | Chained_Fact of int;
type path_n_loc   = UN.path * location;
type path_n_locs  = path_n_loc list;

fun in_subgoals (Nth_Subg _:location) = true
  | in_subgoals  _                    = false;

fun in_chained_facts (Chained_Fact _:location) = true
  | in_chained_facts   _                       = false;

fun same_location (Nth_Subg     n1, Nth_Subg     n2) = n1 = n2
  | same_location (Chained_Fact n1, Chained_Fact n2) = n1 = n2
  | same_location  _                                 = false;

fun abs_pstate_w_aux_to_unode_aux_n_path_tables ({subgoals, usings}:abs_pstate_w_aux) =
  map #paths_table (subgoals @ usings): paths_tables;

fun abs_pstate_w_aux_n_loc_to_unode_aux_n_path_table (pst:abs_pstate_w_aux) (Nth_Subg     n) = nth (#subgoals pst) n
  | abs_pstate_w_aux_n_loc_to_unode_aux_n_path_table (pst:abs_pstate_w_aux) (Chained_Fact n) = nth (#usings   pst) n

fun print_n_abs_pstate_w_aux_to_path_n_locs ({subgoals, usings}:abs_pstate_w_aux) (print:UN.print) =
  let
    val (ptables_in_subgs, ptables_in_usings) = apply2 (map #paths_table) (subgoals, usings)                                                  : (paths_tables * paths_tables);
    fun minus_one (x:int)                     = x - 1                                                                                         : int;
    val ptables_n_locs_in_subgs               = Utils.index ptables_in_subgs  |> map swap |> map (apsnd minus_one) |> map (apsnd Nth_Subg)    : (paths_table * location) list;
    val ptables_n_locs_in_usings              = Utils.index ptables_in_usings |> map swap |> map (apsnd minus_one) |> map (apsnd Chained_Fact): (paths_table * location) list;
    val ptables_n_locs_in_subgs2              = map (apfst (Utils.flip PT.lookup_list print)) ptables_n_locs_in_subgs                         : (UN.paths * location) list;
    val ptables_n_locs_in_usings2             = map (apfst (Utils.flip PT.lookup_list print)) ptables_n_locs_in_usings                        : (UN.paths * location) list;
    fun merge ([]:'a list, y:'b) = []
      | merge (x::xs     , y:'b) = (x, y) :: merge (xs, y);
    val ptables_n_locs_in_subgs3              = map merge ptables_n_locs_in_subgs2  |> flat          : path_n_locs;
    val ptables_n_locs_in_usings3             = map merge ptables_n_locs_in_usings2 |> flat          : path_n_locs;
    val path_n_locs                           = ptables_n_locs_in_subgs3 @ ptables_n_locs_in_usings3 : path_n_locs;
  in
    path_n_locs
  end;

(*Use One_Term.keys to implement it.*)
fun unode_aux_table_to_depth (unode_aux_table:unode_aux_table) =
  let
    val max_path_n_node_w_aux_wo_path_option = OT.max unode_aux_table                      : (UN.path * UN.unique_node_w_aux_wo_path) option;
    val max_path_option                      = max_path_n_node_w_aux_wo_path_option <$> fst: UN.path option;
    val depth_option                         = max_path_option <$> length                  : int option;
  in
    depth_option
  end;

val unode_table_to_lowest_fvars = undefined: unode_table      -> Unique_Node.path list;
val path_to_ancestor_paths      = undefined: Unique_Node.path -> Unique_Node.path list;
val path_to_descendent_paths    = undefined: Unique_Node.path -> Unique_Node.path list;

end;