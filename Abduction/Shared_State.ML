(*
 * Shared_State.ML
 * Authors:
 *   Yutaka Nagashima
 *)
(* TODO: Use Synchronized.var *)
signature SHARED_STATE =
sig

type abduction_graph;

val any_of_these_is_refuted: Proof.state -> terms -> bool;

end;

structure Shared_State: SHARED_STATE =
struct

type abduction_graph = Abduction_Graph.abduction_graph;

local

structure Term_Refuted_Table  = Table (type key = term val ord = Term_Ord.term_ord);
type term_refute_table        = bool Term_Refuted_Table.table; (*true = refuted, false = not refuted*)
type synched_refutation_table = term_refute_table Synchronized.var;

val defined          = Term_Refuted_Table.defined;
val lookup           = Utils.the' "lookup in Shared_State failed." oo Term_Refuted_Table.lookup;
val refutation_table = Synchronized.var "refutation_table" Term_Refuted_Table.empty: synched_refutation_table;

(*Once we refute a term. The term remains refuted in the table forever.*)
fun insert (cnjctr:term, refuted:bool) (table:term_refute_table) =
  case try (Term_Refuted_Table.insert (op =) (cnjctr, refuted)) table
  of NONE           => table
   | SOME new_table => new_table;

in

fun update_synched_refutation_table (pair: (term * bool)) = Synchronized.change refutation_table (insert pair): unit;

fun is_refuted (pst:Proof.state) (cnjctr:term) =
  let
    val old_table         = Synchronized.value refutation_table                                                : term_refute_table;
    val already_checked   = defined old_table cnjctr                                                           : bool;
    fun quickcheck cnjctr = (cnjctr, TBC_Utils.term_has_counterexample_in_pst pst cnjctr)                      : (term * bool);
    val _                 = if already_checked then () else update_synched_refutation_table (quickcheck cnjctr): unit;
    val new_table         = Synchronized.value refutation_table                                                : term_refute_table;
    val result            = lookup new_table cnjctr                                                            : bool;
  in
    result
  end;

fun any_of_these_is_refuted (pst:Proof.state) (terms:terms) = exists (is_refuted pst) terms;

end;

end;