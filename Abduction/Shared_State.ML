(*
 * Shared_State.ML
 * Authors:
 *   Yutaka Nagashima
 *)
signature SHARED_STATE =
sig

type debug = bool;
type proved_simps = (string * term) list; (*lemma name, lemma term*)
type synched_proved_simps = (string * term) list Synchronized.var;

val mk_synched_proved_simps: unit -> synched_proved_simps;
val lookup_proved_simps: synched_proved_simps -> string -> term option;
val add_proved_simp: synched_proved_simps -> (string * term) -> unit;

type abduction_graph;

type term2real_table;
type synched_term2real_table;
val mk_term2real_table     : unit -> synched_term2real_table;
type refutation_cache_statistics = {size: int, hits: int, misses: int};
val refutation_cache_statistics: synched_term2real_table -> refutation_cache_statistics;
val refute                 : debug -> synched_term2real_table -> Proof.state -> term  -> real;
val is_refuted             : synched_term2real_table -> Proof.state -> term  -> bool;
val refute_any_of_these    : debug -> synched_term2real_table -> Proof.state -> terms -> real;
val any_of_these_is_refuted: synched_term2real_table -> Proof.state -> terms -> bool;

(*TODO: Do we really need a table that maps terms to lemma names? Can we use Abduction_Graph for this?*)
type term2string_table;
type synched_term2string_table;
val mk_term2string_table: unit -> synched_term2string_table;
val get_lemma_name      : synched_term2string_table -> Proof.context -> string -> term  -> string;
(*TODO: Do we really need get_orkey_name even though we have get_lemma_name?*)
val get_orkey_name      : synched_term2string_table -> Proof.context -> Abduction_Graph.key -> string;

type synched_abduction_graph = abduction_graph Synchronized.var;
val mk_synched_abduction_graph                    : Proof.context -> term -> synched_abduction_graph;
val update_is_branch                              : Abduction_Graph.key -> synched_abduction_graph -> unit;
val add_andnodes                                  : terms -> synched_abduction_graph -> Abduction_Graph.keys;
val add_child_ornode                              : Proof.context -> synched_abduction_graph -> (string * term) -> unit;
val add_edges_from_andnode_to_ornodes             : Abduction_Graph.key -> synched_abduction_graph -> unit;

val update_proved_completely                      : Abduction_Graph.key -> synched_abduction_graph -> unit;
val update_proof_n_proof_id                       : (*proof*)strings -> (*or*)Abduction_Graph.key -> synched_abduction_graph -> unit;

val update_importance_of_ornode                   : synched_abduction_graph -> Abduction_Graph.key -> unit;
val update_attacked                               : synched_abduction_graph -> Abduction_Graph.key -> unit;

val update_after_proving_ornode                   : strings -> Abduction_Graph.key -> Proof.context -> synched_abduction_graph -> unit;
val update_after_connecting_andnd_to_existing_ornd: Proof.context -> synched_abduction_graph -> (*or_key*)Abduction_Graph.keys -> unit list;
val try_to_prove_ornode_and_update_graph          : Proof.state -> synched_abduction_graph -> Abduction_Graph.key -> unit;

val final_goal_proved_completely                  : synched_abduction_graph -> bool;

val new_node: (Abduction_Graph.key * Abduction_Graph.abduction_node) -> synched_abduction_graph -> unit;
val add_edge: (Abduction_Graph.key * Abduction_Graph.key) -> synched_abduction_graph -> unit;

end;

structure Shared_State: SHARED_STATE =
struct

type debug = bool;
type proved_simps = (string * term) list; (*lemma name, lemma term*)
type synched_proved_simps = (string * term) list Synchronized.var;

fun mk_synched_proved_simps _ = Synchronized.var "synchronized_proved_simps" []: synched_proved_simps;

fun lookup_proved_simps (salist:synched_proved_simps) (name:string) =
  let
    val alist = Synchronized.value salist;
  in
     AList.lookup (op =) alist name
  end;

fun add_proved_simp (salist:synched_proved_simps) (new_simp:(string * term)) =
    Synchronized.change salist (AList.update (op =) new_simp);

type abduction_graph = Abduction_Graph.abduction_graph;

structure Term_Table = Table (type key = term val ord = Term_Ord.term_ord);
val defined          = Term_Table.defined;

datatype refutation_cache_entry = Refuting | Refuted of real;

type refutation_cache_statistics = {size: int, hits: int, misses: int};
type term2real_table =
 {table : refutation_cache_entry Term_Table.table,
  hits  : int,                     (*calls served from the cache or by waiting for an in-progress result*)
  misses: int};                    (*calls that actually ran Quickcheck/Nitpick*)
type synched_term2real_table = term2real_table Synchronized.var;

fun empty_term2real_table () =
  {table = Term_Table.empty, hits = 0, misses = 0}: term2real_table;

fun mk_term2real_table _ =
  Synchronized.var "synched_term2real_table" (empty_term2real_table ()): synched_term2real_table;

fun finished_cache_entry (_, Refuted _) = true
  | finished_cache_entry _              = false;

fun refutation_cache_statistics (synched_table:synched_term2real_table) =
  let
    val {table, hits, misses} = Synchronized.value synched_table;
    val size = Term_Table.dest table |> filter finished_cache_entry |> length;
  in
    {size = size, hits = hits, misses = misses}: refutation_cache_statistics
  end;

local

(*
 * reserve_or_get is the synchronization point for the refutation cache.
 *
 * - If the term is already refuted/not-refuted, this is an exact cache hit.
 * - If another thread is already checking the same term, this thread waits; once
 *   the result is published, this call is counted as a hit because it avoided
 *   another Quickcheck/Nitpick run.
 * - If the term is new, this call reserves the term and is counted as one miss.
 *
 * Therefore, misses count actual expensive refutation checks, and hits count
 * calls that avoided such checks.  The expensive check itself is deliberately
 * performed outside the lock.
 *)
fun reserve_or_get (synched_table:synched_term2real_table) (cnjctr:term): real option =
  Synchronized.guarded_access synched_table
    (fn ({table, hits, misses}:term2real_table) =>
      case Term_Table.lookup table cnjctr of
        SOME (Refuted r) =>
          SOME (SOME r, {table = table, hits = hits + 1, misses = misses})
      | SOME Refuting =>
          NONE
      | NONE =>
          SOME (NONE,
            {table = Term_Table.update (cnjctr, Refuting) table,
             hits = hits,
             misses = misses + 1}));

fun publish_result (synched_table:synched_term2real_table) (cnjctr:term, r:real): unit =
  Synchronized.change synched_table
    (fn ({table, hits, misses}:term2real_table) =>
      {table = Term_Table.update (cnjctr, Refuted r) table,
       hits = hits,
       misses = misses});

fun quickcheck pst cnjctr =
  TBC_Utils.term_has_counterexample_in_pst pst cnjctr: real;

(*Once we refute a term. The term remains refuted in the table forever.*)
in

fun refute (_(*debug*): bool) (synched_table:synched_term2real_table) (pst:Proof.state) (cnjctr:term): real =
  let
    val cnjctr_prop       = if Top_Down_Util.is_prop cnjctr then cnjctr else HOLogic.mk_Trueprop cnjctr: term;
    val cnjctr_prop_clean = Top_Down_Util.standardize_vnames cnjctr_prop
                         |> Isabelle_Utils.strip_atyp
                         |> Utils.try_with @{prop "True"} (Syntax.check_prop (Proof.context_of pst))  : term;
    (* If syntax check fails for this conjecture for some unknown reasons, we consider that we cannot refute it.
     * The reasons is that we have already applied type-checking prior to this stage.
     * So, if Syntax.check_prop fails here, it is caused by some unknown reasons, for which
     * we do not want to refute the conjecture. *)
    val cached = reserve_or_get synched_table cnjctr_prop_clean: real option;
  in
    case cached of
      SOME r => r
    | NONE =>
        let
          val r = quickcheck pst cnjctr_prop_clean;
          val _ = publish_result synched_table (cnjctr_prop_clean, r);
        in
          r
        end
  end;

fun is_refuted (synched_table:synched_term2real_table) (pst:Proof.state) (cnjctr:term): bool =
    Real.== (refute false synched_table pst cnjctr, 0.0);

fun any_of_these_is_refuted (synched_table:synched_term2real_table) (pst:Proof.state) (terms:terms) =
    exists (is_refuted synched_table pst) terms;

fun refute_any_of_these (debug:bool) (synched_table:synched_term2real_table) (pst:Proof.state) (terms:terms) =
  let
    val importances = map (refute debug synched_table pst) terms: real list;
    val result = if exists (fn impo => Real.== (impo, 0.0)) importances then 0.0 else 1.0;
  in result
  end;

end;

type term2string_table         = string Term_Table.table;
type synched_term2string_table = term2string_table Synchronized.var;

fun mk_term2string_table _ = Synchronized.var "synched_term2string_table" Term_Table.empty: synched_term2string_table;

local

val lookup = Utils.the' "lookup for term2string_table failed." oo Term_Table.lookup;
fun insert_string (cnjctr:term, lemma_name:string) (old_table:term2string_table) =
  case try (Term_Table.insert (op =) (cnjctr, lemma_name)) old_table
  of NONE           => old_table
   | SOME new_table => new_table;

in

fun get_lemma_name (synched_table:synched_term2string_table) (ctxt:Proof.context) (candidate:string) (term:term) =
  let
    val standardized_term  = Top_Down_Util.standardize_vnames term                      : term;
    val old_table          = Synchronized.value synched_table                           : term2string_table;
    val already_checked    = defined old_table standardized_term                        : bool;
    val mk_new_lemma_name  = Top_Down_Util.mk_new_lemma_name                            : Proof.context -> bool -> string -> string;
    fun mk_new_name_pair _ = (standardized_term, mk_new_lemma_name ctxt false candidate): (term * string);
    val _ =
      if   already_checked then ()
      else
        let
          (* It is okay to spend some time to run quick-check before calling Synchronized.change:
           * Even if other threads find a counter-example for the same conjecture,
           * the result should be the same. *)
          val pair = mk_new_name_pair standardized_term
        in
          Synchronized.change synched_table (insert_string pair): unit
        end;
    val new_table = Synchronized.value synched_table  : term2string_table;
    val result    = lookup new_table standardized_term: string;
  in
    result
  end;

end;

structure AG  = Abduction_Graph;
structure UAG = Update_Abduction_Graph;

fun get_orkey_name (synched_table:synched_term2string_table) (ctxt:Proof.context) ((AG.Or_N, [term]): AG.key) =
    get_lemma_name synched_table ctxt "" term
  | get_orkey_name _ _ _ = error "get_orkey_name failed. Not an orkey."

type synched_abduction_graph = abduction_graph Synchronized.var;

fun mk_synched_abduction_graph (ctxt:Proof.context) (goal:term) =
  let
    val initial_graph_wo_imp = AG.mk_initial_graph ctxt goal;
    val initial_graph_w_imp  = UAG.update_importance (AG.Or_N, [goal]) 1.0 initial_graph_wo_imp
  in
    Synchronized.var "abduction_graph" initial_graph_w_imp
  end;

fun update_is_branch (key:AG.key) (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph (UAG.update_is_branch key): unit;

fun add_andnodes (andterms:terms) (sagraph:synched_abduction_graph) =
  Synchronized.change_result sagraph (UAG.add_andnode andterms): AG.keys;

fun add_child_ornode (ctxt:Proof.context) (sagraph:synched_abduction_graph) (lemma_name:string, lemma_term:term) =
  Synchronized.change sagraph (UAG.add_child_ornode ctxt (lemma_name, lemma_term)): unit;

fun add_edges_from_andnode_to_ornodes (key:AG.key) (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph (UAG.add_edges_from_andnode_to_ornodes key): unit;

fun update_proved_completely (key:AG.key) (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph (UAG.update_proved_completely key): unit;

fun update_proof_n_proof_id (proof:strings) (key:AG.key) (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph (UAG.update_proof_n_proof_id proof key): unit;

fun update_importance_of_ornode (sagraph:synched_abduction_graph) (orkey:AG.key) =
  Synchronized.change sagraph (UAG.update_importance_of_ornode orkey): unit;

fun update_attacked (sagraph:synched_abduction_graph) (orkey:AG.key) =
  Synchronized.change sagraph (UAG.update_attacked orkey): unit;

fun update_after_proving_ornode (proof:strings) (orkey:AG.key) (ctxt:Proof.context) (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph (UAG.update_after_proving_ornode proof orkey ctxt): unit;

fun update_after_connecting_andnd_to_existing_ornd' (ctxt:Proof.context) (sagraph:synched_abduction_graph) (orkey:AG.key) =
  Synchronized.change sagraph (UAG.update_after_connecting_andnd_to_existing_ornd orkey ctxt): unit;

fun update_after_connecting_andnd_to_existing_ornd (ctxt:Proof.context) (sagraph:synched_abduction_graph) (orkeys:AG.keys) =
  map (update_after_connecting_andnd_to_existing_ornd' ctxt sagraph) orkeys;

fun try_to_prove_ornode_and_update_graph (pst:Proof.state) (sagraph:synched_abduction_graph) (orkey:AG.key) =
  let
    val graph       = Synchronized.value sagraph               : abduction_graph;
    val maybe_proof = AG.prove_orkey_completely orkey graph pst: strings option;
    val _           = update_attacked sagraph orkey            : unit;
  in
      if is_some maybe_proof (*ornode was proved completely.*)
      then
        let
          val proof      = the maybe_proof: strings;
          val _          = update_after_proving_ornode proof orkey (Proof.context_of pst) sagraph;
        in
           ()
        end
      else ()
  end;

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

(*** signature TOP_DOWN_CONJECTURING ***)
signature TOP_DOWN_CONJECTURING =
sig

val top_down_conjectures: Shared_State.synched_term2string_table -> Proof.state -> term -> (string * term) list;

end;