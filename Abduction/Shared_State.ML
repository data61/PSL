(*
 * Shared_State.ML
 * Authors:
 *   Yutaka Nagashima
 *)
signature SHARED_STATE =
sig

type abduction_graph;

val clean_refuation_table  : unit -> unit;
val is_refuted             : Proof.state   -> term  -> bool;
val any_of_these_is_refuted: Proof.state   -> terms -> bool;
val clean_lemma_name_table : unit -> unit;
val get_lemma_name         : Proof.context -> term  -> string;
val get_orkey_name         : Proof.context -> Abduction_Graph.key -> string;

type synched_abduction_graph = abduction_graph Synchronized.var;

val mk_synched_abduction_graph       : Proof.context -> term -> synched_abduction_graph;
val update_is_branch                 : Abduction_Graph.key -> synched_abduction_graph -> unit;
val add_andnodes                     : terms -> synched_abduction_graph -> Abduction_Graph.keys;
val add_child_ornode                 : Proof.context -> synched_abduction_graph -> (string * term) -> unit;
val add_edges_from_andnode_to_ornodes: Abduction_Graph.key -> synched_abduction_graph -> unit;
val update_after_proving_ornode      : strings -> Abduction_Graph.key -> Proof.context -> synched_abduction_graph -> unit;

val final_goal_proved_completely     : synched_abduction_graph -> bool;

val new_node: (Abduction_Graph.key * Abduction_Graph.abduction_node) -> synched_abduction_graph -> unit;
val add_edge: (Abduction_Graph.key * Abduction_Graph.key) -> synched_abduction_graph -> unit;

end;

structure Shared_State: SHARED_STATE =
struct

type abduction_graph = Abduction_Graph.abduction_graph;

structure Term_Table = Table (type key = term val ord = Term_Ord.term_ord);
val defined          = Term_Table.defined;

local

type term2bool_table          = bool Term_Table.table; (*true = refuted, false = not refuted*)
type synched_refutation_table = term2bool_table Synchronized.var;
val refutation_table = Synchronized.var "refutation_table" Term_Table.empty: synched_refutation_table;
val lookup           = Utils.the' "lookup for is_refuted failed." oo Term_Table.lookup;
(*Once we refute a term. The term remains refuted in the table forever.*)
fun insert (cnjctr:term, refuted:bool) (table:term2bool_table) =
  case try (Term_Table.insert (op =) (cnjctr, refuted)) table
  of NONE           => table
   | SOME new_table => new_table;

in

fun clean_refuation_table _ = Synchronized.change refutation_table (K Term_Table.empty): unit;

fun is_refuted (pst:Proof.state) (cnjctr:term) =
  let
    val cnjctr_prop       = if Top_Down_Util.is_prop cnjctr then cnjctr else HOLogic.mk_Trueprop cnjctr: term;
    val old_table         = Synchronized.value refutation_table                                        : term2bool_table;
    val already_checked   = defined old_table cnjctr_prop                                              : bool;
    fun quickcheck cnjctr = (cnjctr, TBC_Utils.term_has_counterexample_in_pst pst cnjctr)              : (term * bool);
    val _                 =
      if   already_checked then ()
      else
        let
          (* It is okay to spend some time to run quick-check before calling Synchronized.change:
           * Even if other threads find a counter-example for the same conjecture,
           * the result should be the same. *)
          val pair = quickcheck cnjctr_prop
        in
          Synchronized.change refutation_table (insert pair): unit
        end;
    val new_table         = Synchronized.value refutation_table: term2bool_table;
    val result            = lookup new_table cnjctr_prop       : bool;
(*
    val _ = tracing "\n"
val _ = "Quick-Checking this:"
val _ = tracing (Isabelle_Utils.trm_to_string (Proof.context_of pst) cnjctr);
    val _ = tracing ((if result then "" else "NOT ") ^ " REFUTED according to the table")
    val result_wo_using_table = TBC_Utils.term_has_counterexample_in_pst pst cnjctr;
*)

(*
    val _ = tracing ((if result then "" else "NOT ") ^ " REFUTED W/O using the table")
*)
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

fun clean_lemma_name_table _ = Synchronized.change lemma_name_table (K Term_Table.empty): unit;

fun get_lemma_name (ctxt:Proof.context) (term:term) =
  let
    val standardized_term  = Top_Down_Util.standardize_vnames term                              : term;
    fun mk_new_name_pair _ = (standardized_term, Top_Down_Util.mk_new_lemma_name ctxt false)    : (term * string);
    val _                  = Synchronized.change lemma_name_table (insert (mk_new_name_pair ())): unit;
    val new_table          = Synchronized.value lemma_name_table                                : term_lemma_name_table;
    val result             = lookup new_table standardized_term                                 : string;
  in
    result
  end;

end;

structure AG  = Abduction_Graph;
structure UAG = Update_Abduction_Graph;

fun get_orkey_name (ctxt:Proof.context) ((AG.Or_N, [term]): AG.key) = get_lemma_name ctxt term
  | get_orkey_name _ _ = error "get_orkey_name failed. Not an orkey."

type synched_abduction_graph = abduction_graph Synchronized.var;

fun mk_synched_abduction_graph (ctxt:Proof.context) (goal:term) =
  let
    val initial_graph = AG.mk_initial_graph ctxt goal;
  in
    Synchronized.var "abduction_graph" initial_graph
  end;

fun update_is_branch (key:AG.key) (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph (UAG.update_is_branch key): unit;

fun add_andnodes (andterms:terms) (sagraph:synched_abduction_graph) =
  Synchronized.change_result sagraph (UAG.add_andnode andterms): AG.keys;

fun add_child_ornode (ctxt:Proof.context) (sagraph:synched_abduction_graph) (lemma_name:string, lemma_term:term) =
  Synchronized.change sagraph (UAG.add_child_ornode ctxt (lemma_name, lemma_term)): unit;

fun add_edges_from_andnode_to_ornodes (key:AG.key) (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph (UAG.add_edges_from_andnode_to_ornodes key): unit;

fun update_after_proving_ornode (proof:strings) (orkey:AG.key) (ctxt:Proof.context) (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph (UAG.update_after_proving_ornode proof orkey ctxt): unit;

fun final_goal_proved_completely (sagraph:synched_abduction_graph) =
  let
    val agraph = Synchronized.value sagraph: AG.abduction_graph;
  in
    AG.final_goal_proved_completely agraph: bool
  end;

fun new_node (key: AG.key, node:AG.abduction_node) (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph (AG.PGraph.new_node (key, node)): unit;

fun add_edge (parent_key: AG.key, child_key: AG.key) (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph (AG.PGraph.add_edge (parent_key, child_key)): unit;

end;