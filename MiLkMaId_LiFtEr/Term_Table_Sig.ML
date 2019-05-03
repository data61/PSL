(*  Title:      PSL/MiLkMaId_LiFtEr/Term_Table_Sig.ML
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

(*** Path_Table and Print_Table ***)
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

structure UN          = Unique_Node;
structure Path_Table  = Table (type key = UN.path  val ord = path_ord): TABLE;
structure Print_Table = Table (type key = UN.print val ord = prnt_ord): TABLE;

end;

(*** TERM_TABLE ***)
signature TERM_TABLE =
sig

type path_to_unode_table     = UN.unode       Path_Table.table;
type path_to_unode_aux_table = UN.unode_w_aux Path_Table.table;

val unodes_to_unode_table                    : UN.unodes -> path_to_unode_table;
val path_to_unode_aux_table_n_pst_to_print_to_paths_table: path_to_unode_table -> Proof.state -> path_to_unode_aux_table;

type print_to_paths_table  = UN.paths Print_Table.table;
type print_to_paths_tables = print_to_paths_table list;

val print_to_paths_table_n_print_to_paths: print_to_paths_table -> UN.print -> UN.paths;

type one_term  = {path_to_unode_aux_table: path_to_unode_aux_table, print_to_paths_table: print_to_paths_table};
type one_terms = one_term list;

val path_to_unode_aux_table_to_one_term: path_to_unode_aux_table -> one_term;
val pst_n_trm_to_one_term              : Proof.state -> term -> one_term;

type lifter_pst =
  {subgoals: one_terms,
   usings  : one_terms};

val pst_to_lifter_pst: Proof.state -> lifter_pst;

(* location: first sub-goal = Nth_Subg 0. *)
datatype location = Nth_Subg of int | Chained_Fact of int;
type path_n_loc   = UN.path * location;
type path_n_locs  = path_n_loc list;

val in_subgoals     : location -> bool;
val in_chained_facts: location -> bool;
val same_location   : (location * location) -> bool;

val lifter_pst_to_print_to_paths_tables: lifter_pst -> print_to_paths_tables;
val lifter_pst_n_loc_to_one_term       : lifter_pst -> location -> one_term;
val print_n_lifter_pst_to_path_n_locs  : lifter_pst -> LiFtEr_Util.print -> path_n_locs;

(*Use One_Term.keys to implement it.*)
val path_to_unode_aux_table_to_depth   : path_to_unode_aux_table -> int option;
val path_to_unode_table_to_lowest_fvars: path_to_unode_table -> UN.paths;
val path_to_ancestor_paths             : UN.path -> UN.paths;
val path_to_descendent_paths           : UN.path -> UN.paths;

end;