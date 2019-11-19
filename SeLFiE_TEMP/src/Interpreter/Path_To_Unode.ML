(*  Title:      PSL/SeLFeE/src/Path_To_Unode.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

This is an improved version of Term_Table.
Term_Table was initially invented for LiFtEr, in which we only needed Full_Path_Table.
In SeLFiEr, however, 

The overall work-flow is:
    (term * Proof.state  ==== trm_to_trm_w_prnt =======================================>                      (* in Unique_Node *)
     trm_w_prnt          ==== trm_w_prnt_to_utrm_w_prnt ===============================>                      (* in Unique_Node *)
     utrm_w_prnt         ==== utrm_w_prnt_to_futrm_w_prnt =============================>                      (* in Unique_Node *)
     futrm_w_prnt        ==== futrm_w_prnt_to_futrm_w_prnt_n_path =====================>                      (* in Unique_Node *)
     futrm_w_prnt_n_path ==== futrm_w_prnt_n_path_to_unodes ===========================>                      (* in Unique_Node *)
     unodes              ==== unodes_to_unode_table ===================================>                      (* in Path_To_Unode  *)
     path_to_unode_table)
*)

(*** signature PAHT_TO_UNODE ***)
signature PATH_TO_UNODE =
sig

type path;
type path_to_unode_table;
val pst_n_trm_to_path_to_unode_table: Proof.state -> term -> path_to_unode_table;

end;

(*** Inner_Path_To_Inner_Unode ***)
structure Inner_Path_To_Inner_Unode: PATH_TO_UNODE =
struct

structure PaT = Path_Table;
structure UN  = Unique_Node;
structure PrT = Print_Table;

type path                = UN.path;
type path_to_unode_table = UN.unode PaT.table;

fun unodes_to_unode_table (unodes:UN.unodes) =
   List.map (fn unode => (#path unode, unode)) unodes |> PaT.make;

fun path_to_unode_aux_table_n_pst_to_print_to_paths_table (unode_table:path_to_unode_table) (pst:Proof.state) =
  let
    (* We use the K combinator  because we do not change key*)
    fun unode_to_unode_w_aux (unode:UN.unode) = UN.unode_n_pst_to_unode_w_aux unode pst;
    val path_to_unode_table_to_path_to_unode_aux_table  = PaT.map (K unode_to_unode_w_aux)
      : path_to_unode_table -> UN.unode_w_aux PaT.table;
  in
    path_to_unode_table_to_path_to_unode_aux_table unode_table: UN.unode_w_aux PaT.table
  end;

type print_to_paths_table  = UN.path list Print_Table.table;
type print_to_paths_tables = print_to_paths_table list;

fun gen_trm_table_to_print_to_paths_table (trm_table:'a PaT.table) (get_print:'a -> UN.print) =
  let
    val path_n_unode_s       = PaT.dest trm_table;
    val path_n_print_s       = List.map (apsnd get_print) path_n_unode_s;
    val print_n_path_s       = map swap path_n_print_s;
    val print_to_paths_table = PrT.make_list print_n_path_s;
  in
    print_to_paths_table: print_to_paths_table
  end;

type one_term  = {path_to_unode_table: path_to_unode_table, print_to_paths_table: print_to_paths_table};

fun print_to_paths_table_n_print_to_paths (print_to_paths_table:print_to_paths_table) (print: UN.print) =
  Print_Table.lookup_list print_to_paths_table print;

fun path_to_unode_table_to_depth (path_to_unode_aux_table:path_to_unode_table) =
  let
    val keys         = PaT.keys path_to_unode_aux_table;
    val key_lengs    = map length keys                   : ints;
    val depth_option = Utils.ints_to_max_option key_lengs: int option;
  in
    depth_option
  end;

fun paths_at_the_same_level (path1:UN.path) (path2:UN.path) =
  let
    val lengths = apply2 length (path1, path2): (int * int);
  in
    uncurry equal lengths: bool
  end;

fun path1_is_an_arg_of_path2 (path1:UN.path) (path2:UN.path) =
  let
    val path1_last_option = try Utils.last path1: int option;
    val path2_last_option = try Utils.last path2: int option;
    (*TODO: This is not always correct. We have to exclude Abstraction by checking the parent node.
     *      For this, we need the path_to_node table. *)
    val path2_is_func     = Option.map (      equal 0) path2_last_option |> Utils.is_some_true: bool;
    val path1_is_arg      = Option.map (not o equal 0) path1_last_option |> Utils.is_some_true: bool;
  in
    paths_at_the_same_level path1 path2 andalso path2_is_func andalso path1_is_arg
  end;

fun path1_is_nth_arg_of_path2 (path1:UN.path) (n:int) (path2:UN.path) =
  let
    val path1_last_option = try Utils.last path1: int option;
    val path2_last_option = try Utils.last path2: int option;
    (*TODO: This is not always correct. We have to exclude Abstraction by checking the parent node.
     *      For this, we need the path_to_node table. *)
    val path2_is_func    = Option.map (equal 0) path2_last_option |> Utils.is_some_true: bool;
    (* "n + 1" because the "0" is used for the function (or lambda abstraction).*)
    val path1_is_nth_arg = Option.map (equal (n + 1)) path1_last_option |> Utils.is_some_true: bool;
  in
    paths_at_the_same_level path1 path2 andalso path2_is_func andalso path1_is_nth_arg
  end;

val path_to_unode_table_to_lowest_fvars = undefined: path_to_unode_table -> UN.path list;
val path_to_ancestor_paths              = undefined: UN.path -> UN.path list;
val path_to_descendent_paths            = undefined: UN.path -> UN.path list;

fun pst_n_trm_to_path_to_unode_table (pst:Proof.state) (trm:term) =
  let
    val ctxt                    = Proof.context_of pst;
    val trm_w_prnt              = UN.trm_to_trm_w_prnt ctxt trm;
    val utrm_w_prnt             = UN.trm_w_prnt_to_utrm_w_prnt trm_w_prnt;
    val futrm_w_prnt            = UN.utrm_w_prnt_to_futrm_w_prnt utrm_w_prnt;
    val futrm_w_prnt_n_path     = UN.futrm_w_prnt_to_futrm_w_prnt_n_path futrm_w_prnt;
    val unodes                  = UN.futrm_w_prnt_n_path_to_unodes futrm_w_prnt_n_path;
    val path_to_unode_table     = unodes_to_unode_table unodes: path_to_unode_table;
  in
    path_to_unode_table: path_to_unode_table
  end;

end;

(*TODO: probably these types and functions should be defined in SeLFiE_Util, not here.*)
datatype location = Subgoal of int | Chained_Fact of int;

(*TODO: remove are_same_location. (op =) can do the job.*)
fun are_same_location (Subgoal      n) (Subgoal      m) = n = m
  | are_same_location (Chained_Fact n) (Chained_Fact m) = n = m
  | are_same_location  _                _               = false;

type outer_path = location * UN.path;

(*This definition is more or less arbitrary.*)
fun outer_path_ord ((Subgoal n, path1), (Subgoal m, path2)) =
    (case Int.compare (n, m) of EQUAL => path_ord (path1, path2) | diff  => diff)
  | outer_path_ord ((Chained_Fact n, path1), (Chained_Fact m, path2)) =
    (case Int.compare (n, m) of EQUAL => path_ord (path1, path2) | diff  => diff)
  | outer_path_ord ((Subgoal      _, _), (Chained_Fact _, _)) = GREATER
  | outer_path_ord ((Chained_Fact _, _), (Subgoal      _, _)) = LESS

fun outer_path_eq (full_p1:outer_path, full_p2:outer_path) = case outer_path_ord (full_p1, full_p2) of
  EQUAL => true | _ => false;

(*** Outer_Path_Table  ***)
structure Outer_Path_Table  = Table (type key = outer_path  val ord = outer_path_ord): TABLE;

(*** Outer_Path_To_Outer_Unode  ***)
structure Outer_Path_To_Outer_Unode: PATH_TO_UNODE =
struct

type path = outer_path;

type outer_unode =
  {unode     : UN.unode,
   location  : location};

type path_to_unode_table = outer_unode Outer_Path_Table.table;

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
          val trm_w_prnt          = UN.trm_to_trm_w_prnt ctxt trm;
          val utrm_w_prnt         = UN.trm_w_prnt_to_utrm_w_prnt trm_w_prnt;
          val futrm_w_prnt        = UN.utrm_w_prnt_to_futrm_w_prnt utrm_w_prnt;
          val futrm_w_prnt_n_path = UN.futrm_w_prnt_to_futrm_w_prnt_n_path futrm_w_prnt;
          val unodes              = UN.futrm_w_prnt_n_path_to_unodes futrm_w_prnt_n_path;
          val path_to_unode_table = Term_Table.unodes_to_unode_table unodes: UN.unode Path_Table.table;
        in
          pst_n_location_n_term_list_to_location_n_path_to_unode_table' pairs ((loc, path_to_unode_table)::acc)
        end;                                     
  in
    pst_n_location_n_term_list_to_location_n_path_to_unode_table' outer_pairs []
   : (location * UN.unode Path_Table.table) list
  end;

fun location_n_path_to_unode_table_to_outer_path_to_fp_unode_table (loc:location, path_to_unode_table) =
  let
    val path_unode_pairs                   = Path_Table.dest path_to_unode_table: (UN.path * UN.unode) list;
    fun unode_to_fp_unode (unode:UN.unode) = {unode = unode, location = loc}:outer_unode;
    fun path_unode_pairs_to_outer_path_fp_node_pair (path:UN.path, unode:UN.unode) =
        ((loc, path), unode_to_fp_unode unode): (outer_path * outer_unode);
    val outer_path_fp_node_pairs     = map path_unode_pairs_to_outer_path_fp_node_pair path_unode_pairs: (outer_path * outer_unode) list;
    val outer_path_to_fp_unode_table = Outer_Path_Table.make outer_path_fp_node_pairs                  : outer_path_to_outer_unode_table;
  in
    outer_path_to_fp_unode_table: outer_path_to_outer_unode_table
  end;

fun location_n_path_to_unode_table_list_to_location_n_outer_path_to_fp_unode_table_list' [] _ = []
  | location_n_path_to_unode_table_list_to_location_n_outer_path_to_fp_unode_table_list' ((loc, path_to_unode_table)::pairs) acc =
    let
      val outer_path_to_fp_unode_table = location_n_path_to_unode_table_to_outer_path_to_fp_unode_table (loc, path_to_unode_table):outer_unode Outer_Path_Table.table;
    in
      location_n_path_to_unode_table_list_to_location_n_outer_path_to_fp_unode_table_list' pairs ((loc, outer_path_to_fp_unode_table)::acc)
    end;

fun location_n_path_to_unode_table_list_to_location_n_outer_path_to_fp_unode_table_list (pairs:(location * Term_Table.path_to_unode_table) list) =
    location_n_path_to_unode_table_list_to_location_n_outer_path_to_fp_unode_table_list' pairs [];

fun eq_fp_unodes (fpn1:outer_unode, fpn2:outer_unode) =
  let
    val loc1             = #location fpn1;
    val loc2             = #location fpn2;
    val same_loc         = are_same_location loc1 loc2: bool;
    val fp_unode_to_path = #path o #unode: outer_unode -> Unique_Node.path;
    val same_path        = apply2 fp_unode_to_path (fpn1, fpn2) |> uncurry Unique_Node.are_same_path: bool; 
  in
    same_loc andalso same_path
  end;

fun merge_outer_path_to_fp_unode_tables (tables:outer_path_to_outer_unode_table list): outer_path_to_outer_unode_table =
  fold  (Outer_Path_Table.merge eq_fp_unodes |> curry) tables Outer_Path_Table.empty;

fun pst_n_trm_to_path_to_unode_table (pst:Proof.state) _: outer_path_to_outer_unode_table =
  let
    val loc_n_trm_list = pst_to_location_n_term_list pst: (location * term) list;
    val loc_path_to_unode_table_list           = pst_n_location_n_term_list_to_location_n_path_to_unode_table pst loc_n_trm_list                                      : (location * Term_Table.path_to_unode_table) list;
    val loc_n_outer_path_to_outer_unode_table_list  = location_n_path_to_unode_table_list_to_location_n_outer_path_to_fp_unode_table_list loc_path_to_unode_table_list: (location * outer_path_to_outer_unode_table) list;
    val outer_path_to_outer_unode_table_list        = map snd loc_n_outer_path_to_outer_unode_table_list                                                              : outer_path_to_outer_unode_table list;
    val outer_path_to_outer_unode_table             = merge_outer_path_to_fp_unode_tables outer_path_to_outer_unode_table_list                                        : outer_path_to_outer_unode_table;
  in
    outer_path_to_outer_unode_table: outer_path_to_outer_unode_table
  end;

fun outer_unode_to_unode ({unode,...}:outer_unode) = unode;

fun outer_unode_to_node ({unode,...}:outer_unode) = #node unode: UN.node;

fun outer_unode2_to_unode2 (fpun1, fpun2) = apply2 outer_unode_to_unode (fpun1, fpun2): (UN.unode * UN.unode);

fun outer_unode2_to_node2 (fpun1, fpun2) = apply2 outer_unode_to_node (fpun1, fpun2): (UN.node * UN.node);

end;