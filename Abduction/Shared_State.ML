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
val get_lemma_name         : Proof.context -> term -> string;
(*TODO: share abduction_graph*)

end;

structure Shared_State: SHARED_STATE =
struct

type abduction_graph = Abduction_Graph.abduction_graph;

structure Term_Table = Table (type key = term val ord = Term_Ord.term_ord);
val defined          = Term_Table.defined;

local

type term_refute_table        = bool Term_Table.table; (*true = refuted, false = not refuted*)
type synched_refutation_table = term_refute_table Synchronized.var;

val refutation_table = Synchronized.var "refutation_table" Term_Table.empty: synched_refutation_table;
val lookup           = Utils.the' "lookup for get_lemma_name failed." oo Term_Table.lookup;
(*Once we refute a term. The term remains refuted in the table forever.*)
fun insert (cnjctr:term, refuted:bool) (table:term_refute_table) =
  case try (Term_Table.insert (op =) (cnjctr, refuted)) table
  of NONE           => table
   | SOME new_table => new_table;

in

fun is_refuted (pst:Proof.state) (cnjctr:term) =
  let
    val old_table         = Synchronized.value refutation_table                          : term_refute_table;
    val already_checked   = defined old_table cnjctr                                     : bool;
    fun quickcheck cnjctr = (cnjctr, TBC_Utils.term_has_counterexample_in_pst pst cnjctr): (term * bool);
    val _                 =
      if   already_checked then ()
      else
        let
          (* It is okay to spend some time to run quick-check before calling Synchronized.change:
           * Even if other threads find a counter-example for the same conjecture,
           * the result should be the same. *)
          val pair = quickcheck cnjctr
        in
          Synchronized.change refutation_table (insert pair): unit
        end;
    val new_table         = Synchronized.value refutation_table                          : term_refute_table;
    val result            = lookup new_table cnjctr                                      : bool;
  in
    result
  end;

fun any_of_these_is_refuted (pst:Proof.state) (terms:terms) = exists (is_refuted pst) terms;

end;

local

type term_lemma_name_table    = string Term_Table.table;
type synched_lemma_name_table = term_lemma_name_table Synchronized.var;

val lemma_name_table = Synchronized.var "lemma_name_table" Term_Table.empty: synched_lemma_name_table;
val lookup           = Utils.the' "lookup for get_lemma_name failed." oo Term_Table.lookup;
fun insert (cnjctr:term, lemma_name:string) (old_table:term_lemma_name_table) =
  if   defined old_table cnjctr
  then old_table
  else Term_Table.insert (op =) (cnjctr, lemma_name) old_table;

in

fun get_lemma_name (ctxt:Proof.context) (term:term) =
  let
    fun mk_new_name_pair _ = (term, Top_Down_Util.mk_new_lemma_name ctxt)                            : (term * string);
    val _                  = Synchronized.change lemma_name_table (insert (mk_new_name_pair ()))     : unit;
    val new_table          = Synchronized.value lemma_name_table                                     : term_lemma_name_table;
    val result             = lookup new_table term                                                   : string;
  in
    result
  end;

end;

end;