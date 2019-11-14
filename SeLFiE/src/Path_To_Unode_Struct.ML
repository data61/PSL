(*  Title:      PSL/LiFtEr/src/Full_Path_To_FPUnode_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The conversion to transform term to a format more amenable to LiFtEr.
The overall work-flow is:
Proof.state            ==== pst_to_lifter_pst ================================================>                      (* in Term_Table *)
   (Proof.state & term     ==== pst_n_trm_to_one_term ========================================>                      (* in Term_Table *)
       (term                    ==== trm_to_trm_w_prnt =======================================>                      (* in Unique_Node *)
        trm_w_prnt              ==== trm_w_prnt_to_utrm_w_prnt ===============================>                      (* in Unique_Node *)
        utrm_w_prnt             ==== utrm_w_prnt_to_futrm_w_prnt =============================>                      (* in Unique_Node *)
        futrm_w_prnt            ==== futrm_w_prnt_to_futrm_w_prnt_n_path =====================>                      (* in Unique_Node *)
        futrm_w_prnt_n_path     ==== futrm_w_prnt_n_path_to_unodes ===========================>                      (* in Unique_Node *)
        unodes                  ==== unodes_to_unode_table ===================================>                      (* in Term_Table  *)
        path_to_unode_table     ==== path_to_unode_table_to_path_to_unode_aux_table ==========>                      (* in Term_Table  *)
           (unode                    ==== unode_n_pst_to_unode_w_aux =========================> unode_w_aux          (* in Unique_Node *))
        path_to_unode_aux_table ==== path_to_unode_aux_table_to_one_term =====================>                      (* in Term_Table  *)
           (path_to_unode_aux_table  ==== path_to_unode_aux_table_to_print_to_paths_table ====> print_to_paths_table (* in Term_Table  *))
        one_term)
    one_term)
lifter_pst
*)

(*** Path_To_Unode ***)
structure Path_To_Unode =
struct

structure PaT = Path_Table;
structure UN  = Unique_Node;
structure PrT = Print_Table;

type path_to_unode_table     = UN.unode       PaT.table;

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