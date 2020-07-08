(*  Title:      PSL/SeLFeE/src/Path_To_Unode.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

This is an improved version of Term_Table.
Term_Table was initially invented for LiFtEr, in which we only needed Full_Path_Table.
In SeLFiEr, however, 

The overall work-flow is:
Proof.state & term ==== pst_n_trm_to_path_to_unode_table ====> (*Path_To_Unode.ML*)
    (term * Proof.state  ==== trm_to_trm_w_prnt =======================================> (* in Unique_Node   *)
     trm_w_prnt          ==== trm_w_prnt_to_utrm_w_prnt ===============================> (* in Unique_Node   *)
     utrm_w_prnt         ==== utrm_w_prnt_to_futrm_w_prnt =============================> (* in Unique_Node   *)
     futrm_w_prnt        ==== futrm_w_prnt_to_futrm_w_prnt_n_path =====================> (* in Unique_Node   *)
     futrm_w_prnt_n_path ==== futrm_w_prnt_n_path_to_unodes ===========================> (* in Unique_Node   *)
     unodes              ==== unodes_to_unode_table ===================================> (* in Path_To_Unode *)
     path_to_unode_table)
*)

(*** signature PAHT_TO_UNODE ***)
signature PATH_TO_UNODE =
sig

datatype table_type = Inner_Table | Outer_Table;
val      table_type: table_type;

type path;
type path_to_unode_table;

val table_to_paths                  : path_to_unode_table -> path list;
val lookup                          : path_to_unode_table -> path -> UN.unode option;
val pst_n_trm_to_path_to_unode_table: Proof.state -> term -> path_to_unode_table;
val pst_n_term_n_path_to_cname      : Proof.state -> term -> path -> string option;

end;

local

fun path_n_table_to_cname (path) (table) (lookup) =
  let
    val unode_option  = lookup table path             : UN.unode option;
    val print_option  = Option.map #print unode_option: string option;
  in
    print_option
  end;

in

(*** Inner_Path_To_Inner_Unode ***)
structure Inner_Path_To_Unode: PATH_TO_UNODE =
struct

structure Path_Table = Inner_Path_Table;

val table_to_paths = Path_Table.keys;

structure UN  = Unique_Node;

datatype table_type = Inner_Table | Outer_Table;
val      table_type = Inner_Table;

type path                = UN.inner_path;
type path_to_unode_table = UN.unode Path_Table.table;

fun lookup (table:path_to_unode_table) (path:path) = Inner_Path_Table.lookup table path: UN.unode option;

fun unodes_to_unode_table (unodes:UN.unodes) =
   List.map (fn unode => (#inner_path unode, unode)) unodes |> Path_Table.make;

type print_to_paths_table  = UN.inner_path list Print_Table.table;
type print_to_paths_tables = print_to_paths_table list;

type one_term  = {path_to_unode_table: path_to_unode_table, print_to_paths_table: print_to_paths_table};

fun pst_n_trm_to_path_to_unode_table (pst:Proof.state) (trm:term) =
  let
    val ctxt                      = Proof.context_of pst                : Proof.context;
    val unodes                    = UN.context_n_term_to_unodes ctxt trm: UN.unodes;
    val inner_path_to_unode_table = unodes_to_unode_table unodes        : path_to_unode_table;
  in
    inner_path_to_unode_table: path_to_unode_table
  end;

fun pst_n_term_n_path_to_cname (pst:Proof.state) (term:term) (path:path) =
  let
    val table = pst_n_trm_to_path_to_unode_table pst term: path_to_unode_table;
  in
    path_n_table_to_cname path table lookup
  end;

end;

(*** Outer_Path_To_Outer_Unode ***)
structure Outer_Path_To_Unode: PATH_TO_UNODE =
struct

structure Path_Table = Outer_Path_Table;

val table_to_paths = Path_Table.keys;

datatype table_type = Inner_Table | Outer_Table;
val      table_type = Outer_Table;

type path = outer_path;

type outer_unode =
  {unode     : UN.unode,
   location  : location};

type path_to_unode_table = UN.unode Outer_Path_Table.table;

fun lookup (table:path_to_unode_table) (path:path) = Outer_Path_Table.lookup table path: UN.unode option;

type outer_path_to_outer_unode_table = outer_unode Outer_Path_Table.table;

fun pst_to_location_n_term_list (pst:Proof.state) =
  let
    val chained_facts_trms = Isabelle_Utils.pstate_to_usings pst |> map Thm.prop_of: terms;
    val subgoals_trms      = Isabelle_Utils.pst_to_subgs pst                       : terms;
    datatype loc = Subg | Chained;
    fun add_loc (Subg:loc)    (i:int, trm:term) = (Subgoal i,      trm)
      | add_loc (Chained:loc) (i:int, trm:term) = (Chained_Fact i, trm);
    val chained_facts_pairs = Utils.add_index chained_facts_trms |> map (add_loc Chained): (location * term) list;
    val subgoals_pairs      = Utils.add_index subgoals_trms      |> map (add_loc Subg   ): (location * term) list;
    val result              = chained_facts_pairs @ subgoals_pairs;
  in
    result: (location * term) list
  end;

fun pst_n_location_n_term_list_to_location_n_path_to_unode_table (pst:Proof.state) (outer_pairs:(location * term) list) =
  let
    val ctxt = Proof.context_of pst: Proof.context;
    fun pst_n_location_n_term_list_to_location_n_path_to_unode_table'  [] acc = acc
      | pst_n_location_n_term_list_to_location_n_path_to_unode_table' ((loc, trm)::pairs:(location * term) list) acc =
        let
          val unodes              = UN.context_n_term_to_unodes ctxt trm   : UN.unodes;
          val path_to_unode_table = Term_Table.unodes_to_unode_table unodes: UN.unode Inner_Path_Table.table;
        in
          pst_n_location_n_term_list_to_location_n_path_to_unode_table' pairs ((loc, path_to_unode_table)::acc)
        end;                                     
  in
    pst_n_location_n_term_list_to_location_n_path_to_unode_table' outer_pairs []
   : (location * UN.unode Inner_Path_Table.table) list
  end;

fun location_n_path_to_unode_table_to_outer_path_to_fp_unode_table (loc:location, path_to_unode_table) =
  let
    val path_unode_pairs                   = Inner_Path_Table.dest path_to_unode_table: (UN.inner_path * UN.unode) list;
    fun unode_to_fp_unode (unode:UN.unode) = {unode = unode, location = loc}:outer_unode;
    fun path_unode_pairs_to_outer_path_fp_node_pair (inner_path:UN.inner_path, unode:UN.unode) =
        ((loc, inner_path), unode_to_fp_unode unode): (outer_path * outer_unode);
    val outer_path_fp_node_pairs     = map path_unode_pairs_to_outer_path_fp_node_pair path_unode_pairs: (outer_path * outer_unode) list;
    val outer_path_to_fp_unode_table = Outer_Path_Table.make outer_path_fp_node_pairs                  : outer_path_to_outer_unode_table;
  in
    outer_path_to_fp_unode_table: outer_path_to_outer_unode_table
  end;

fun location_n_path_to_unode_table_list_to_location_n_outer_path_to_fp_unode_table_list' [] acc = acc
  | location_n_path_to_unode_table_list_to_location_n_outer_path_to_fp_unode_table_list' ((loc, path_to_unode_table)::pairs) acc =
    let
      val outer_path_to_fp_unode_table = location_n_path_to_unode_table_to_outer_path_to_fp_unode_table (loc, path_to_unode_table):outer_unode Outer_Path_Table.table;
    in
      location_n_path_to_unode_table_list_to_location_n_outer_path_to_fp_unode_table_list' pairs ((loc, outer_path_to_fp_unode_table)::acc)
    end;

fun location_n_path_to_unode_table_list_to_location_n_outer_path_to_fp_unode_table_list (pairs:(location * Term_Table.inner_path_to_unode_table) list) =
    location_n_path_to_unode_table_list_to_location_n_outer_path_to_fp_unode_table_list' pairs [];

fun eq_fp_unodes (fpn1:outer_unode, fpn2:outer_unode) =
  let
    val loc1                   = #location fpn1;
    val loc2                   = #location fpn2;
    val same_loc               = loc1 = loc2: bool;
    val fp_unode_to_inner_path = #inner_path o #unode: outer_unode -> Unique_Node.inner_path;
    val same_inner_path        = apply2 fp_unode_to_inner_path (fpn1, fpn2) |> uncurry Unique_Node.are_same_inner_path: bool; 
  in
    same_loc andalso same_inner_path
  end;

fun merge_outer_path_to_fp_unode_tables (tables:outer_path_to_outer_unode_table list): outer_path_to_outer_unode_table =
  fold  (Outer_Path_Table.merge eq_fp_unodes |> curry) tables Outer_Path_Table.empty;

fun pst_n_trm_to_path_to_outer_unode_table (pst:Proof.state) _: outer_path_to_outer_unode_table =
  let
    val loc_n_trm_list = pst_to_location_n_term_list pst: (location * term) list;
    val loc_path_to_unode_table_list               = pst_n_location_n_term_list_to_location_n_path_to_unode_table pst loc_n_trm_list                                 : (location * Term_Table.inner_path_to_unode_table) list;
    val loc_n_outer_path_to_outer_unode_table_list = location_n_path_to_unode_table_list_to_location_n_outer_path_to_fp_unode_table_list loc_path_to_unode_table_list: (location * outer_path_to_outer_unode_table) list;
    val outer_path_to_outer_unode_table_list       = map snd loc_n_outer_path_to_outer_unode_table_list                                                              : outer_path_to_outer_unode_table list;
    val outer_path_to_outer_unode_table            = merge_outer_path_to_fp_unode_tables outer_path_to_outer_unode_table_list                                        : outer_path_to_outer_unode_table;
  in
    outer_path_to_outer_unode_table: outer_path_to_outer_unode_table
  end;

fun pst_n_trm_to_path_to_unode_table (pst:Proof.state) _: path_to_unode_table =
  let
    val outer_path_to_outer_unode_table = pst_n_trm_to_path_to_outer_unode_table pst ();
    val outer_path_to_unode_table       = Path_Table.map (fn _ => fn {unode, ...}:outer_unode => unode) outer_path_to_outer_unode_table
  in
    outer_path_to_unode_table
  end;

fun pst_n_term_n_path_to_cname (pst:Proof.state) (term:term) (path:path) =
  let
    val table = pst_n_trm_to_path_to_unode_table pst term: path_to_unode_table;
  in
    path_n_table_to_cname path table lookup
  end;

end;

end;

signature GEN_PATH_TO_UNODE =
sig

structure Inner_Path_To_Unode: PATH_TO_UNODE;
structure Outer_Path_To_Unode: PATH_TO_UNODE;

datatype path_type = Inner_Path_Type | Outer_Path_Type;
datatype gen_path  = Inner_Path of UN.inner_path | Outer_Path of outer_path;

datatype gen_path_to_unode_table =
  Inner_Path_To_Unode of Inner_Path_To_Unode.path_to_unode_table
| Outer_Path_To_Unode of Outer_Path_To_Unode.path_to_unode_table;

val gen_table_n_gen_path_to_unode: gen_path_to_unode_table -> gen_path -> UN.unode;

val path_is_in_subgoal              : gen_path -> bool;
val path_is_in_chained_fact         : gen_path -> bool;
val path_is_in_nth_subgoal          : gen_path -> int -> bool;
val path_is_in_nth_chained_fact     : gen_path -> int -> bool;

end;

structure Gen_Path_To_Unode: GEN_PATH_TO_UNODE =
struct

structure Inner_Path_To_Unode = Inner_Path_To_Unode;
structure Outer_Path_To_Unode = Outer_Path_To_Unode;

datatype path_type = Inner_Path_Type | Outer_Path_Type;
datatype gen_path  = Inner_Path of UN.inner_path | Outer_Path of outer_path;
datatype gen_path_to_unode_table =
  Inner_Path_To_Unode of Inner_Path_To_Unode.path_to_unode_table
| Outer_Path_To_Unode of Outer_Path_To_Unode.path_to_unode_table;

fun gen_table_n_gen_path_to_unode (Inner_Path_To_Unode table) (Inner_Path path) =  Inner_Path_To_Unode.lookup table path |> Utils.the' "gen_table_path_to_unode_failed with Inner_Path"
  | gen_table_n_gen_path_to_unode (Outer_Path_To_Unode table) (Outer_Path path) =  Outer_Path_To_Unode.lookup table path |> Utils.the' "gen_table_path_to_unode_failed with Outer_Path"
  | gen_table_n_gen_path_to_unode _ _ = error "gen_table_n_gen_path_to_unode failed."

fun path_is_in_subgoal          (Outer_Path (Subgoal _, _)) = true : bool
  | path_is_in_subgoal          (Outer_Path  _            ) = false
  | path_is_in_subgoal          (Inner_Path  _            ) = true: bool(*because Are_In_Same_Location is used for Is_Deeper_Than in Eval_Syntactic_Sugar.ML*)

fun path_is_in_chained_fact     (Outer_Path (Chained_Fact _, _)) = true : bool
  | path_is_in_chained_fact     (Outer_Path  _                 ) = false
  | path_is_in_chained_fact     (Inner_Path  _                 ) = true: bool;(*because Are_In_Same_Location is used for Is_Deeper_Than in Eval_Syntactic_Sugar.ML*)

fun path_is_in_nth_subgoal      (Outer_Path (Subgoal nth_subg, _)) number = nth_subg = number
  | path_is_in_nth_subgoal      (Outer_Path  _                   ) _      = false
  | path_is_in_nth_subgoal      (Inner_Path  _                   ) _      = true: bool;(*because Are_In_Same_Location is used for Is_Deeper_Than in Eval_Syntactic_Sugar.ML*)

fun path_is_in_nth_chained_fact (Outer_Path (Chained_Fact nth_fact, _)) number = nth_fact = number
  | path_is_in_nth_chained_fact (Outer_Path  _                        ) _      = false
  | path_is_in_nth_chained_fact (Inner_Path  _                        ) _      = true: bool;(*because Are_In_Same_Location is used for Is_Deeper_Than in Eval_Syntactic_Sugar.ML*)

end;