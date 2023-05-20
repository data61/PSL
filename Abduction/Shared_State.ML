(*
 * Shared_State.ML
 * Authors:
 *   Yutaka Nagashima
 *)
(* TODO: Use Synchronized.var *)
signature SHARED_STATE =
sig

type abduction_graph;

type term_refute_table;

val empty_term_refute_table: term_refute_table;

val defined: term_refute_table -> term -> bool;

val lookup: term_refute_table -> term -> bool;

val insert: term * bool -> term_refute_table -> term_refute_table;

val is_refuted: Proof.state -> term_refute_table -> term -> bool * term_refute_table;

val are_refuted: Proof.state -> terms -> term_refute_table -> bool;

end;

structure Shared_State: SHARED_STATE =
struct

type abduction_graph = Update_Abduction_Graph.abduction_graph;

structure Term_Refuted_Table = Table (type key = term val ord = Term_Ord.term_ord);

type term_refute_table = bool Term_Refuted_Table.table; (*true = refuted, false = not refuted*)

val empty_term_refute_table = Term_Refuted_Table.empty;

val defined = Term_Refuted_Table.defined;

val lookup = Utils.the' "lookup in Shared_State failed." oo Term_Refuted_Table.lookup;

fun insert (cnjctr:term, refuted:bool) (table:term_refute_table) =
  case try (Term_Refuted_Table.insert (op =) (cnjctr, refuted)) table
  of NONE           => table
   | SOME new_table => new_table;

fun is_refuted (pst:Proof.state) (table:term_refute_table) (cnjctr:term) =
  let
    val is_already_checked = defined table cnjctr: bool;
    val result =
      if   is_already_checked
      then (lookup table cnjctr, table)
      else
        let
          val refuted = TBC_Utils.term_has_counterexample_in_pst pst cnjctr;
          val new_table = insert (cnjctr, refuted) table;
        in
          (refuted, new_table): bool * term_refute_table
        end;
  in
    result
  end;

fun update_refuted (pairs: (term * bool) list) (old_tb:term_refute_table) =
  fold insert pairs old_tb: term_refute_table;

fun are_refuted (pst:Proof.state) (cnjctrs:terms) (old_tb:term_refute_table) =
  let
    val cnjctrs_not_checked = filter_out (defined old_tb) cnjctrs: terms;
    fun quickcheck (cnjctr:term): (term * bool) = (cnjctr, TBC_Utils.term_has_counterexample_in_pst pst cnjctr);
    val newly_checked_results = map quickcheck cnjctrs_not_checked: (term * bool) list;
    (*TODO: new_tb should be computed atomically*)
    val new_tb = update_refuted newly_checked_results old_tb: term_refute_table;
    val result = exists (lookup new_tb) cnjctrs: bool;
  in
    result
  end;

end;