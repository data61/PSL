(*  Title:      PSL/SeLFiE/src/Preprocessor/Term_Table_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The conversion to transform term to a format more amenable to LiFtEr.
The overall work-flow is:
Proof.state            ==== pst_to_lifter_pst ================================================>                                             (* in Term_Table *)
   (Proof.state & term     ==== pst_n_trm_to_one_term ========================================>                                             (* in Term_Table *)
       (term                          ==== trm_to_trm_w_prnt =======================================>                                       (* in Unique_Node *)
        trm_w_prnt                    ==== trm_w_prnt_to_utrm_w_prnt ===============================>                                       (* in Unique_Node *)
        utrm_w_prnt                   ==== utrm_w_prnt_to_futrm_w_prnt =============================>                                       (* in Unique_Node *)
        futrm_w_prnt                  ==== futrm_w_prnt_to_futrm_w_prnt_n_inner_path =====================>                                 (* in Unique_Node *)
        futrm_w_prnt_n_inner_path     ==== futrm_w_prnt_n_inner_path_to_unodes ===========================>                                 (* in Unique_Node *)
        unodes                        ==== unodes_to_unode_table ===================================>                                       (* in Term_Table  *)
        inner_path_to_unode_table     ==== inner_path_to_unode_table_to_inner_path_to_unode_aux_table ==========>                           (* in Term_Table  *)
           (unode                         ==== unode_n_pst_to_unode_w_aux =========================> unode_w_aux                            (* in Unique_Node *))
        inner_path_to_unode_aux_table ==== inner_path_to_unode_aux_table_to_one_term =====================>                                 (* in Term_Table  *)
           (inner_path_to_unode_aux_table ==== inner_path_to_unode_aux_table_to_print_to_inner_paths_table ====> print_to_inner_paths_table (* in Term_Table  *))
        one_term)
    one_term)
lifter_pst
*)

(*** TERM_TABLE ***)
signature TERM_TABLE =
sig

type inner_path_to_unode_table     = UN.unode       Inner_Path_Table.table;

val unodes_to_unode_table: UN.unodes -> UN.unode Inner_Path_Table.table;

type print_to_inner_paths_table  = UN.inner_paths Print_Table.table;
type print_to_inner_paths_tables = print_to_inner_paths_table list;

val print_to_inner_paths_table_n_print_to_inner_paths: print_to_inner_paths_table -> UN.print -> UN.inner_paths;

(* location: first sub-goal = Nth_Subg 0. *)
datatype location       = Nth_Subg of int | Chained_Fact of int;
type inner_path_n_loc   = UN.inner_path * location;
type inner_path_n_locs  = inner_path_n_loc list;

val in_subgoals     : location -> bool;
val in_chained_facts: location -> bool;
val same_location   : (location * location) -> bool;

(*Use One_Term.keys to implement it.*)
val inner_paths_at_the_same_level            : UN.inner_path -> UN.inner_path -> bool;(*TODO: Move this to Unique_Node?*)
val inner_path1_is_an_arg_of_inner_path2     : UN.inner_path -> UN.inner_path -> bool;
val inner_path1_is_nth_arg_of_inner_path2    : UN.inner_path -> int -> UN.inner_path -> bool;
val inner_path_to_unode_table_to_lowest_fvars: inner_path_to_unode_table -> UN.inner_paths;
val inner_path_to_ancestor_inner_paths       : UN.inner_path -> UN.inner_paths;
val inner_path_to_descendent_inner_paths     : UN.inner_path -> UN.inner_paths;

end;

(*** Term_Table ***)
structure Term_Table: TERM_TABLE =
struct

type inner_path_to_unode_table     = UN.unode       Inner_Path_Table.table;

fun unodes_to_unode_table (unodes:UN.unodes) =
   List.map (fn unode => (#inner_path unode, unode)) unodes |> Inner_Path_Table.make: UN.unode Inner_Path_Table.table;

type print_to_inner_paths_table  = Unique_Node.inner_path list Print_Table.table;
type print_to_inner_paths_tables = print_to_inner_paths_table list;

fun gen_trm_table_to_print_to_inner_paths_table (trm_table:'a Inner_Path_Table.table) (get_print:'a -> UN.print) =
  let
    val inner_path_n_unode_s       = Inner_Path_Table.dest trm_table;
    val inner_path_n_print_s       = List.map (apsnd get_print) inner_path_n_unode_s;
    val print_n_inner_path_s       = map swap inner_path_n_print_s;
    val print_to_inner_paths_table = Print_Table.make_list print_n_inner_path_s;
  in
    print_to_inner_paths_table: print_to_inner_paths_table
  end;

fun print_to_inner_paths_table_n_print_to_inner_paths (print_to_inner_paths_table:print_to_inner_paths_table) (print: UN.print) =
  Print_Table.lookup_list print_to_inner_paths_table print;

(* location: first sub-goal = Nth_Subg 0. *)(*TODO: should I declare this here?*)
datatype location = Nth_Subg of int | Chained_Fact of int;
type inner_path_n_loc   = UN.inner_path * location;
type inner_path_n_locs  = inner_path_n_loc list;

fun in_subgoals (Nth_Subg _:location) = true
  | in_subgoals  _                    = false;

fun in_chained_facts (Chained_Fact _:location) = true
  | in_chained_facts   _                       = false;

fun same_location (Nth_Subg     n1, Nth_Subg     n2) = n1 = n2
  | same_location (Chained_Fact n1, Chained_Fact n2) = n1 = n2
  | same_location  _                                 = false;

fun inner_paths_at_the_same_level (inner_path1:UN.inner_path) (inner_path2:UN.inner_path) =
  let
    val lengths = apply2 length (inner_path1, inner_path2): (int * int);
  in
    uncurry equal lengths: bool
  end;

fun inner_path1_is_an_arg_of_inner_path2 (inner_path1:UN.inner_path) (inner_path2:UN.inner_path) =
  let
    val inner_path1_last_option = try Utils.last inner_path1: int option;
    val inner_path2_last_option = try Utils.last inner_path2: int option;
    (*TODO: This is not always correct. We have to exclude Abstraction by checking the parent node.
     *      For this, we need the inner_path_to_node table. *)
    val inner_path2_is_func     = Option.map (      equal 0) inner_path2_last_option |> Utils.is_some_true: bool;
    val inner_path1_is_arg      = Option.map (not o equal 0) inner_path1_last_option |> Utils.is_some_true: bool;
  in
    inner_paths_at_the_same_level inner_path1 inner_path2 andalso inner_path2_is_func andalso inner_path1_is_arg
  end;

fun inner_path1_is_nth_arg_of_inner_path2 (inner_path1:UN.inner_path) (n:int) (inner_path2:UN.inner_path) =
  let
    val inner_path1_last_option = try Utils.last inner_path1: int option;
    val inner_path2_last_option = try Utils.last inner_path2: int option;
    (*TODO: This is not always correct. We have to exclude Abstraction by checking the parent node.
     *      For this, we need the inner_path_to_node table. *)
    val inner_path2_is_func    = Option.map (equal 0) inner_path2_last_option |> Utils.is_some_true: bool;
    (* "n + 1" because the "0" is used for the function (or lambda abstraction).*)
    val inner_path1_is_nth_arg = Option.map (equal (n + 1)) inner_path1_last_option |> Utils.is_some_true: bool;
  in
    inner_paths_at_the_same_level inner_path1 inner_path2 andalso inner_path2_is_func andalso inner_path1_is_nth_arg
  end;

val inner_path_to_unode_table_to_lowest_fvars = undefined: inner_path_to_unode_table -> Unique_Node.inner_path list;
val inner_path_to_ancestor_inner_paths        = undefined: Unique_Node.inner_path -> Unique_Node.inner_path list;
val inner_path_to_descendent_inner_paths      = undefined: Unique_Node.inner_path -> Unique_Node.inner_path list;

end;