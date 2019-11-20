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

(*** Path_Table and Print_Table ***)

(* inner_path_ord: This definition is more or less arbitrary. *)
fun inner_path_ord ([],    []   ) = EQUAL
  | inner_path_ord (_,     []   ) = GREATER
  | inner_path_ord ([],     _   ) = LESS
  | inner_path_ord (x::xs, y::ys) = case Int.compare (x, y) of
      EQUAL => inner_path_ord (xs, ys)
    | diff  => diff;

fun prnt_ord (SeLFiE_Util.Print p1, SeLFiE_Util.Print p2) = String.compare (p1, p2);

structure UN               = Unique_Node;
structure Inner_Path_Table = Table (type key = UN.inner_path  val ord = inner_path_ord): TABLE;
structure Print_Table      = Table (type key = UN.print val ord = prnt_ord): TABLE;

(*** TERM_TABLE ***)
signature TERM_TABLE =
sig

type inner_path_to_unode_table     = UN.unode       Inner_Path_Table.table;
type inner_path_to_unode_aux_table = UN.unode_w_aux Inner_Path_Table.table;
(*TODO: Double-check if this causes problems to Poly/ML's type checker.
 *      E.g. 
 *       - location_n_inner_path_to_unode_table_to_full_inner_path_to_fp_unode_table in Outer_Path_To_Outer_Unode.ML
 *       - location_n_inner_path_to_unode_table_list_to_location_n_full_inner_path_to_fp_unode_table_list in the same file.*)

val unodes_to_unode_table                    : UN.unodes -> UN.unode Inner_Path_Table.table;
val inner_path_to_unode_aux_table_n_pst_to_print_to_inner_paths_table: inner_path_to_unode_table -> Proof.state -> inner_path_to_unode_aux_table;

type print_to_inner_paths_table  = UN.inner_paths Print_Table.table;
type print_to_inner_paths_tables = print_to_inner_paths_table list;

val print_to_inner_paths_table_n_print_to_inner_paths: print_to_inner_paths_table -> UN.print -> UN.inner_paths;

type one_term  = {inner_path_to_unode_aux_table: inner_path_to_unode_aux_table, print_to_inner_paths_table: print_to_inner_paths_table};
type one_terms = one_term list;

val inner_path_to_unode_aux_table_to_one_term: inner_path_to_unode_aux_table -> one_term;
val pst_n_trm_to_one_term                    : Proof.state -> term -> one_term;

type lifter_pst =
  {subgoals: one_terms,
   usings  : one_terms};

val pst_to_lifter_pst: Proof.state -> lifter_pst;

(* location: first sub-goal = Nth_Subg 0. *)
datatype location       = Nth_Subg of int | Chained_Fact of int;
type inner_path_n_loc   = UN.inner_path * location;
type inner_path_n_locs  = inner_path_n_loc list;

val in_subgoals     : location -> bool;
val in_chained_facts: location -> bool;
val same_location   : (location * location) -> bool;

val lifter_pst_to_print_to_inner_paths_tables: lifter_pst -> print_to_inner_paths_tables;
val lifter_pst_n_loc_to_one_term             : lifter_pst -> location -> one_term;
val lifter_pst_n_print_to_inner_path_n_locs  : lifter_pst -> SeLFiE_Util.print -> inner_path_n_locs;

(*Use One_Term.keys to implement it.*)
val inner_paths_at_the_same_level            : UN.inner_path -> UN.inner_path -> bool;(*TODO: Move this to Unique_Node?*)
val inner_path1_is_an_arg_of_inner_path2     : UN.inner_path -> UN.inner_path -> bool;
val inner_path1_is_nth_arg_of_inner_path2    : UN.inner_path -> int -> UN.inner_path -> bool;
val inner_path_to_unode_aux_table_to_depth   : inner_path_to_unode_aux_table -> int option;
val inner_path_to_unode_table_to_lowest_fvars: inner_path_to_unode_table -> UN.inner_paths;
val inner_path_to_ancestor_inner_paths       : UN.inner_path -> UN.inner_paths;
val inner_path_to_descendent_inner_paths     : UN.inner_path -> UN.inner_paths;

end;

(*** Term_Table ***)
structure Term_Table: TERM_TABLE =
struct

structure UN  = Unique_Node;
structure PrT = Print_Table;

type inner_path_to_unode_table     = UN.unode       Inner_Path_Table.table;
type inner_path_to_unode_aux_table = UN.unode_w_aux Inner_Path_Table.table;

fun unodes_to_unode_table (unodes:UN.unodes) =
   List.map (fn unode => (#inner_path unode, unode)) unodes |> Inner_Path_Table.make: UN.unode Inner_Path_Table.table;

fun inner_path_to_unode_aux_table_n_pst_to_print_to_inner_paths_table (unode_table:inner_path_to_unode_table) (pst:Proof.state) =
  let
    (* We use the K combinator  because we do not change key*)
    fun unode_to_unode_w_aux (unode:UN.unode) = UN.unode_n_pst_to_unode_w_aux unode pst;
    val inner_path_to_unode_table_to_inner_path_to_unode_aux_table  = Inner_Path_Table.map (K unode_to_unode_w_aux)
      : inner_path_to_unode_table -> UN.unode_w_aux Inner_Path_Table.table;
  in
    inner_path_to_unode_table_to_inner_path_to_unode_aux_table unode_table: UN.unode_w_aux Inner_Path_Table.table
  end;

type print_to_inner_paths_table  = Unique_Node.inner_path list Print_Table.table;
type print_to_inner_paths_tables = print_to_inner_paths_table list;

fun gen_trm_table_to_print_to_inner_paths_table (trm_table:'a Inner_Path_Table.table) (get_print:'a -> UN.print) =
  let
    val inner_path_n_unode_s       = Inner_Path_Table.dest trm_table;
    val inner_path_n_print_s       = List.map (apsnd get_print) inner_path_n_unode_s;
    val print_n_inner_path_s       = map swap inner_path_n_print_s;
    val print_to_inner_paths_table = PrT.make_list print_n_inner_path_s;
  in
    print_to_inner_paths_table: print_to_inner_paths_table
  end;

fun inner_path_to_unode_aux_table_to_print_to_inner_paths_table (inner_path_to_unode_aux_table:inner_path_to_unode_aux_table) =
  gen_trm_table_to_print_to_inner_paths_table inner_path_to_unode_aux_table #print: print_to_inner_paths_table;

type one_term  = {inner_path_to_unode_aux_table: inner_path_to_unode_aux_table, print_to_inner_paths_table: print_to_inner_paths_table};
type one_terms = one_term list;

fun inner_path_to_unode_aux_table_to_one_term (inner_path_to_unode_aux_table:inner_path_to_unode_aux_table) =
  {inner_path_to_unode_aux_table  = inner_path_to_unode_aux_table,
   print_to_inner_paths_table     = inner_path_to_unode_aux_table_to_print_to_inner_paths_table inner_path_to_unode_aux_table}: one_term;

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

type lifter_pst =
  {subgoals: one_terms,
   usings  : one_terms};

fun lifter_pst_to_print_to_inner_paths_tables ({subgoals, usings}:lifter_pst) =
  map #print_to_inner_paths_table (subgoals @ usings): print_to_inner_paths_tables;

fun lifter_pst_n_loc_to_one_term (pst:lifter_pst) (Nth_Subg     n) = nth (#subgoals pst) n
  | lifter_pst_n_loc_to_one_term (pst:lifter_pst) (Chained_Fact n) = nth (#usings   pst) n

fun lifter_pst_n_print_to_inner_path_n_locs ({subgoals, usings}:lifter_pst) (print:UN.print) =
  let
    val (ptables_in_subgs, ptables_in_usings) = apply2 (map #print_to_inner_paths_table) (subgoals, usings)                                   : (print_to_inner_paths_tables * print_to_inner_paths_tables);
    fun minus_one (x:int)                     = x - 1                                                                                         : int;
    val ptables_n_locs_in_subgs               = Utils.index ptables_in_subgs  |> map swap |> map (apsnd minus_one) |> map (apsnd Nth_Subg)    : (print_to_inner_paths_table * location) list;
    val ptables_n_locs_in_usings              = Utils.index ptables_in_usings |> map swap |> map (apsnd minus_one) |> map (apsnd Chained_Fact): (print_to_inner_paths_table * location) list;
    val ptables_n_locs_in_subgs2              = map (apfst (Utils.flip PrT.lookup_list print)) ptables_n_locs_in_subgs                        : (UN.inner_paths * location) list;
    val ptables_n_locs_in_usings2             = map (apfst (Utils.flip PrT.lookup_list print)) ptables_n_locs_in_usings                       : (UN.inner_paths * location) list;
    fun merge ([]:'a list, _:'b) = []
      | merge (x::xs     , y:'b) = (x, y) :: merge (xs, y);
    val ptables_n_locs_in_subgs3              = map merge ptables_n_locs_in_subgs2  |> flat          : inner_path_n_locs;
    val ptables_n_locs_in_usings3             = map merge ptables_n_locs_in_usings2 |> flat          : inner_path_n_locs;
    val inner_path_n_locs                     = ptables_n_locs_in_subgs3 @ ptables_n_locs_in_usings3 : inner_path_n_locs;
  in
    inner_path_n_locs
  end;

fun inner_path_to_unode_aux_table_to_depth (inner_path_to_unode_aux_table:inner_path_to_unode_aux_table) =
  let
    val keys         = Inner_Path_Table.keys inner_path_to_unode_aux_table;
    val key_lengs    = map length keys                   : ints;
    val depth_option = Utils.ints_to_max_option key_lengs: int option;
  in
    depth_option
  end;

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

fun pst_n_trm_to_one_term (pst:Proof.state) (trm:term): one_term =
  let
    val ctxt                          = Proof.context_of pst;
    val trm_w_prnt                    = UN.trm_to_trm_w_prnt ctxt trm;
    val utrm_w_prnt                   = UN.trm_w_prnt_to_utrm_w_prnt trm_w_prnt;
    val futrm_w_prnt                  = UN.utrm_w_prnt_to_futrm_w_prnt utrm_w_prnt;
    val futrm_w_prnt_n_inner_path     = UN.futrm_w_prnt_to_futrm_w_prnt_n_inner_path futrm_w_prnt;
    val unodes                        = UN.futrm_w_prnt_n_inner_path_to_unodes futrm_w_prnt_n_inner_path;
    val inner_path_to_unode_table     = unodes_to_unode_table unodes: inner_path_to_unode_table;
    val inner_path_to_unode_aux_table = inner_path_to_unode_aux_table_n_pst_to_print_to_inner_paths_table inner_path_to_unode_table pst;
    val one_term                      = inner_path_to_unode_aux_table_to_one_term inner_path_to_unode_aux_table;
  in
    one_term: one_term
  end;

fun pst_to_lifter_pst (pst:Proof.state): lifter_pst =
  let
    val chained_facts_trms = Isabelle_Utils.pstate_to_usings pst |> map Thm.prop_of: terms;
    val subgoals_trms      = Isabelle_Utils.pst_to_subgs pst                       : terms;
    fun process_trms (trms:terms) = map (pst_n_trm_to_one_term pst) trms           : one_terms;
  in
    {subgoals = process_trms subgoals_trms,
     usings   = process_trms chained_facts_trms}
  end;

end;