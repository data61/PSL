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

type filter_statistics_snapshot =
 {top_loop_index: int,
  refutation_checked: int,
  refutation_refuted: int,
  refutation_survived: int,
  abduction_checked_conjectures: int,
  abduction_used_conjectures: int,
  abduction_discarded_conjectures: int,
  orelse_rejected_conjectures: int,
  orelse_too_large: int,
  orelse_eq_to_final_goal_from_tactic: int,
  orelse_concl_is_eq_to_final_goal: int,
  orelse_has_func_with_three_occs_in_a_row: int,
  orelse_concls_are_same: int,
  orelse_concl_of_conj_refuted: int};
type synched_filter_statistics;
datatype orelse_filter_reason =
    Orelse_Too_Large
  | Orelse_Eq_To_Final_Goal_From_Tactic
  | Orelse_Concl_Is_Eq_To_Final_Goal
  | Orelse_Has_Func_With_Three_Occs_In_A_Row
  | Orelse_Concls_Are_Same
  | Orelse_Concl_Of_Conj_Refuted;
val mk_filter_statistics              : unit -> synched_filter_statistics;
val reset_filter_statistics_for_loop  : synched_filter_statistics -> int -> unit;
val filter_statistics_snapshot        : synched_filter_statistics -> filter_statistics_snapshot;
val record_abduction_filter_input     : synched_filter_statistics -> terms -> unit;
val record_abduction_filter_used      : synched_filter_statistics -> terms -> unit;
val record_orelse_filter_rejection    : synched_filter_statistics -> orelse_filter_reason -> term -> unit;

type term2real_table;
type synched_term2real_table;
val mk_term2real_table     : synched_filter_statistics option -> synched_term2real_table;
val refutation_cache_statistics_enabled: unit -> bool;
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

type graph_update_statistics =
 {node_attempts: int,
  nodes_created: int,
  node_reuses: int,
  ornode_attempts: int,
  ornodes_created: int,
  ornodes_reused: int,
  andnode_attempts: int,
  andnodes_created: int,
  andnodes_reused: int,
  edge_node_attempts: int,
  edge_nodes_created: int,
  edge_nodes_reused: int,
  edge_attempts: int,
  edges_created: int,
  edge_reuses: int,
  or_expansion_attempts: int,
  or_expansions_started: int};

type synched_abduction_graph;
val mk_synched_abduction_graph                    : Proof.context -> term -> synched_abduction_graph;
val value_of_graph                                : synched_abduction_graph -> abduction_graph;
val graph_update_statistics                       : synched_abduction_graph -> graph_update_statistics;
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

type filter_statistics_snapshot =
 {top_loop_index: int,
  refutation_checked: int,
  refutation_refuted: int,
  refutation_survived: int,
  abduction_checked_conjectures: int,
  abduction_used_conjectures: int,
  abduction_discarded_conjectures: int,
  orelse_rejected_conjectures: int,
  orelse_too_large: int,
  orelse_eq_to_final_goal_from_tactic: int,
  orelse_concl_is_eq_to_final_goal: int,
  orelse_has_func_with_three_occs_in_a_row: int,
  orelse_concls_are_same: int,
  orelse_concl_of_conj_refuted: int};

datatype orelse_filter_reason =
    Orelse_Too_Large
  | Orelse_Eq_To_Final_Goal_From_Tactic
  | Orelse_Concl_Is_Eq_To_Final_Goal
  | Orelse_Has_Func_With_Three_Occs_In_A_Row
  | Orelse_Concls_Are_Same
  | Orelse_Concl_Of_Conj_Refuted;

type filter_loop_statistics =
 {top_loop_index: int,
  refutation_checked: unit Term_Table.table,
  refutation_refuted: unit Term_Table.table,
  refutation_survived: unit Term_Table.table,
  abduction_checked_conjectures: unit Term_Table.table,
  abduction_used_conjectures: unit Term_Table.table,
  orelse_rejected_conjectures: unit Term_Table.table,
  orelse_too_large: unit Term_Table.table,
  orelse_eq_to_final_goal_from_tactic: unit Term_Table.table,
  orelse_concl_is_eq_to_final_goal: unit Term_Table.table,
  orelse_has_func_with_three_occs_in_a_row: unit Term_Table.table,
  orelse_concls_are_same: unit Term_Table.table,
  orelse_concl_of_conj_refuted: unit Term_Table.table};

type synched_filter_statistics = filter_loop_statistics Synchronized.var;

fun filter_statistics_enabled () =
  getenv "PSL_EVAL_MODE" = "1" andalso getenv "PSL_EVAL_ABDUCTION_STATS_DIR" <> "";

fun empty_filter_loop_statistics (top_loop_index:int): filter_loop_statistics =
 {top_loop_index = top_loop_index,
  refutation_checked = Term_Table.empty,
  refutation_refuted = Term_Table.empty,
  refutation_survived = Term_Table.empty,
  abduction_checked_conjectures = Term_Table.empty,
  abduction_used_conjectures = Term_Table.empty,
  orelse_rejected_conjectures = Term_Table.empty,
  orelse_too_large = Term_Table.empty,
  orelse_eq_to_final_goal_from_tactic = Term_Table.empty,
  orelse_concl_is_eq_to_final_goal = Term_Table.empty,
  orelse_has_func_with_three_occs_in_a_row = Term_Table.empty,
  orelse_concls_are_same = Term_Table.empty,
  orelse_concl_of_conj_refuted = Term_Table.empty};

fun mk_filter_statistics _ =
  Synchronized.var "abduction_filter_statistics" (empty_filter_loop_statistics 0): synched_filter_statistics;

fun reset_filter_statistics_for_loop (synched_stats:synched_filter_statistics) (top_loop_index:int) =
  if filter_statistics_enabled ()
  then Synchronized.change synched_stats (fn _ => empty_filter_loop_statistics top_loop_index)
  else ();

fun insert_unit (trm:term) (table:unit Term_Table.table) =
  Term_Table.update (trm, ()) table;

fun canonical_filter_term (trm:term) =
  Top_Down_Util.standardize_vnames trm |> Isabelle_Utils.strip_atyp: term;

fun record_refutation_filter_result (stats_opt:synched_filter_statistics option) (cnjctr:term) (is_refuted:bool): unit =
  case stats_opt of
      NONE => ()
    | SOME synched_stats =>
        if not (filter_statistics_enabled ())
        then ()
        else
          let
            val clean = canonical_filter_term cnjctr;
          in
            Synchronized.change synched_stats
              (fn {top_loop_index, refutation_checked, refutation_refuted, refutation_survived,
                   abduction_checked_conjectures, abduction_used_conjectures,
                   orelse_rejected_conjectures, orelse_too_large,
                   orelse_eq_to_final_goal_from_tactic, orelse_concl_is_eq_to_final_goal,
                   orelse_has_func_with_three_occs_in_a_row, orelse_concls_are_same,
                   orelse_concl_of_conj_refuted} =>
                {top_loop_index = top_loop_index,
                 refutation_checked = insert_unit clean refutation_checked,
                 refutation_refuted = if is_refuted then insert_unit clean refutation_refuted else refutation_refuted,
                 refutation_survived = if is_refuted then refutation_survived else insert_unit clean refutation_survived,
                 abduction_checked_conjectures = abduction_checked_conjectures,
                 abduction_used_conjectures = abduction_used_conjectures,
                 orelse_rejected_conjectures = orelse_rejected_conjectures,
                 orelse_too_large = orelse_too_large,
                 orelse_eq_to_final_goal_from_tactic = orelse_eq_to_final_goal_from_tactic,
                 orelse_concl_is_eq_to_final_goal = orelse_concl_is_eq_to_final_goal,
                 orelse_has_func_with_three_occs_in_a_row = orelse_has_func_with_three_occs_in_a_row,
                 orelse_concls_are_same = orelse_concls_are_same,
                 orelse_concl_of_conj_refuted = orelse_concl_of_conj_refuted})
          end;

fun record_terms_into_table (terms:terms) (table:unit Term_Table.table) =
  fold (insert_unit o canonical_filter_term) terms table;

fun record_abduction_filter_input (synched_stats:synched_filter_statistics) (terms:terms): unit =
  if not (filter_statistics_enabled ())
  then ()
  else
    Synchronized.change synched_stats
      (fn {top_loop_index, refutation_checked, refutation_refuted, refutation_survived,
           abduction_checked_conjectures, abduction_used_conjectures,
           orelse_rejected_conjectures, orelse_too_large,
           orelse_eq_to_final_goal_from_tactic, orelse_concl_is_eq_to_final_goal,
           orelse_has_func_with_three_occs_in_a_row, orelse_concls_are_same,
           orelse_concl_of_conj_refuted} =>
        {top_loop_index = top_loop_index,
         refutation_checked = refutation_checked,
         refutation_refuted = refutation_refuted,
         refutation_survived = refutation_survived,
         abduction_checked_conjectures = record_terms_into_table terms abduction_checked_conjectures,
         abduction_used_conjectures = abduction_used_conjectures,
         orelse_rejected_conjectures = orelse_rejected_conjectures,
         orelse_too_large = orelse_too_large,
         orelse_eq_to_final_goal_from_tactic = orelse_eq_to_final_goal_from_tactic,
         orelse_concl_is_eq_to_final_goal = orelse_concl_is_eq_to_final_goal,
         orelse_has_func_with_three_occs_in_a_row = orelse_has_func_with_three_occs_in_a_row,
         orelse_concls_are_same = orelse_concls_are_same,
         orelse_concl_of_conj_refuted = orelse_concl_of_conj_refuted});

fun record_abduction_filter_used (synched_stats:synched_filter_statistics) (terms:terms): unit =
  if not (filter_statistics_enabled ())
  then ()
  else
    Synchronized.change synched_stats
      (fn {top_loop_index, refutation_checked, refutation_refuted, refutation_survived,
           abduction_checked_conjectures, abduction_used_conjectures,
           orelse_rejected_conjectures, orelse_too_large,
           orelse_eq_to_final_goal_from_tactic, orelse_concl_is_eq_to_final_goal,
           orelse_has_func_with_three_occs_in_a_row, orelse_concls_are_same,
           orelse_concl_of_conj_refuted} =>
        {top_loop_index = top_loop_index,
         refutation_checked = refutation_checked,
         refutation_refuted = refutation_refuted,
         refutation_survived = refutation_survived,
         abduction_checked_conjectures = abduction_checked_conjectures,
         abduction_used_conjectures = record_terms_into_table terms abduction_used_conjectures,
         orelse_rejected_conjectures = orelse_rejected_conjectures,
         orelse_too_large = orelse_too_large,
         orelse_eq_to_final_goal_from_tactic = orelse_eq_to_final_goal_from_tactic,
         orelse_concl_is_eq_to_final_goal = orelse_concl_is_eq_to_final_goal,
         orelse_has_func_with_three_occs_in_a_row = orelse_has_func_with_three_occs_in_a_row,
         orelse_concls_are_same = orelse_concls_are_same,
         orelse_concl_of_conj_refuted = orelse_concl_of_conj_refuted});

fun record_orelse_filter_rejection (synched_stats:synched_filter_statistics) (reason:orelse_filter_reason) (cnjctr:term): unit =
  if not (filter_statistics_enabled ())
  then ()
  else
    let
      val clean = canonical_filter_term cnjctr;
      fun update_reason_table Orelse_Too_Large table = insert_unit clean table
        | update_reason_table _ table = table;
      fun update_eq_goal_table Orelse_Eq_To_Final_Goal_From_Tactic table = insert_unit clean table
        | update_eq_goal_table _ table = table;
      fun update_concl_eq_goal_table Orelse_Concl_Is_Eq_To_Final_Goal table = insert_unit clean table
        | update_concl_eq_goal_table _ table = table;
      fun update_three_occs_table Orelse_Has_Func_With_Three_Occs_In_A_Row table = insert_unit clean table
        | update_three_occs_table _ table = table;
      fun update_concls_same_table Orelse_Concls_Are_Same table = insert_unit clean table
        | update_concls_same_table _ table = table;
      fun update_concl_refuted_table Orelse_Concl_Of_Conj_Refuted table = insert_unit clean table
        | update_concl_refuted_table _ table = table;
    in
      Synchronized.change synched_stats
        (fn {top_loop_index, refutation_checked, refutation_refuted, refutation_survived,
             abduction_checked_conjectures, abduction_used_conjectures,
             orelse_rejected_conjectures, orelse_too_large,
             orelse_eq_to_final_goal_from_tactic, orelse_concl_is_eq_to_final_goal,
             orelse_has_func_with_three_occs_in_a_row, orelse_concls_are_same,
             orelse_concl_of_conj_refuted} =>
          {top_loop_index = top_loop_index,
           refutation_checked = refutation_checked,
           refutation_refuted = refutation_refuted,
           refutation_survived = refutation_survived,
           abduction_checked_conjectures = abduction_checked_conjectures,
           abduction_used_conjectures = abduction_used_conjectures,
           orelse_rejected_conjectures = insert_unit clean orelse_rejected_conjectures,
           orelse_too_large = update_reason_table reason orelse_too_large,
           orelse_eq_to_final_goal_from_tactic = update_eq_goal_table reason orelse_eq_to_final_goal_from_tactic,
           orelse_concl_is_eq_to_final_goal = update_concl_eq_goal_table reason orelse_concl_is_eq_to_final_goal,
           orelse_has_func_with_three_occs_in_a_row = update_three_occs_table reason orelse_has_func_with_three_occs_in_a_row,
           orelse_concls_are_same = update_concls_same_table reason orelse_concls_are_same,
           orelse_concl_of_conj_refuted = update_concl_refuted_table reason orelse_concl_of_conj_refuted})
    end;

fun table_size (table:unit Term_Table.table) = Term_Table.dest table |> length;

fun filter_statistics_snapshot (synched_stats:synched_filter_statistics) =
  let
    val {top_loop_index, refutation_checked, refutation_refuted, refutation_survived,
         abduction_checked_conjectures, abduction_used_conjectures,
         orelse_rejected_conjectures, orelse_too_large,
         orelse_eq_to_final_goal_from_tactic, orelse_concl_is_eq_to_final_goal,
         orelse_has_func_with_three_occs_in_a_row, orelse_concls_are_same,
         orelse_concl_of_conj_refuted} = Synchronized.value synched_stats;
    val checked = table_size abduction_checked_conjectures;
    val used = table_size abduction_used_conjectures;
    val discarded = Int.max (0, checked - used);
  in
   {top_loop_index = top_loop_index,
    refutation_checked = table_size refutation_checked,
    refutation_refuted = table_size refutation_refuted,
    refutation_survived = table_size refutation_survived,
    abduction_checked_conjectures = checked,
    abduction_used_conjectures = used,
    abduction_discarded_conjectures = discarded,
    orelse_rejected_conjectures = table_size orelse_rejected_conjectures,
    orelse_too_large = table_size orelse_too_large,
    orelse_eq_to_final_goal_from_tactic = table_size orelse_eq_to_final_goal_from_tactic,
    orelse_concl_is_eq_to_final_goal = table_size orelse_concl_is_eq_to_final_goal,
    orelse_has_func_with_three_occs_in_a_row = table_size orelse_has_func_with_three_occs_in_a_row,
    orelse_concls_are_same = table_size orelse_concls_are_same,
    orelse_concl_of_conj_refuted = table_size orelse_concl_of_conj_refuted}: filter_statistics_snapshot
  end;

datatype refutation_cache_entry = Refuting | Refuted of real;

type refutation_cache_statistics = {size: int, hits: int, misses: int};
type term2real_table =
 {table : refutation_cache_entry Term_Table.table,
  hits  : int,                     (*calls served from the cache or by waiting for an in-progress result*)
  misses: int,                     (*calls that actually ran Quickcheck/Nitpick*)
  filter_statistics: synched_filter_statistics option};
type synched_term2real_table = term2real_table Synchronized.var;

fun empty_term2real_table filter_statistics =
  {table = Term_Table.empty, hits = 0, misses = 0, filter_statistics = filter_statistics}: term2real_table;

fun mk_term2real_table filter_statistics =
  Synchronized.var "synched_term2real_table" (empty_term2real_table filter_statistics): synched_term2real_table;

fun refutation_cache_statistics_enabled () =
  getenv "PSL_EVAL_MODE" = "1" andalso getenv "PSL_EVAL_ABDUCTION_STATS_DIR" <> "";

fun finished_cache_entry (_, Refuted _) = true
  | finished_cache_entry _              = false;

fun refutation_cache_statistics (synched_table:synched_term2real_table) =
  if not (refutation_cache_statistics_enabled ())
  then {size = 0, hits = 0, misses = 0}: refutation_cache_statistics
  else
    let
      val {table, hits, misses, filter_statistics = _} = Synchronized.value synched_table;
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
fun reserve_or_get (count_enabled:bool) (synched_table:synched_term2real_table) (cnjctr:term): real option =
  Synchronized.guarded_access synched_table
    (fn ({table, hits, misses, filter_statistics}:term2real_table) =>
      case Term_Table.lookup table cnjctr of
        SOME (Refuted r) =>
          SOME (SOME r, {table = table, hits = hits + (if count_enabled then 1 else 0), misses = misses,
                         filter_statistics = filter_statistics})
      | SOME Refuting =>
          NONE
      | NONE =>
          SOME (NONE,
            {table = Term_Table.update (cnjctr, Refuting) table,
             hits = hits,
             misses = misses + (if count_enabled then 1 else 0),
             filter_statistics = filter_statistics}));

fun publish_result (synched_table:synched_term2real_table) (cnjctr:term, r:real): unit =
  Synchronized.change synched_table
    (fn ({table, hits, misses, filter_statistics}:term2real_table) =>
      {table = Term_Table.update (cnjctr, Refuted r) table,
       hits = hits,
       misses = misses,
       filter_statistics = filter_statistics});

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
    val ({filter_statistics, ...}: term2real_table) = Synchronized.value synched_table;
    val cached = reserve_or_get (refutation_cache_statistics_enabled ()) synched_table cnjctr_prop_clean: real option;
    fun record r = record_refutation_filter_result filter_statistics cnjctr_prop_clean (Real.== (r, 0.0));
  in
    case cached of
      SOME r => (record r; r)
    | NONE =>
        let
          val r = quickcheck pst cnjctr_prop_clean;
          val _ = publish_result synched_table (cnjctr_prop_clean, r);
          val _ = record r;
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

type graph_update_statistics =
 {node_attempts: int,
  nodes_created: int,
  node_reuses: int,
  ornode_attempts: int,
  ornodes_created: int,
  ornodes_reused: int,
  andnode_attempts: int,
  andnodes_created: int,
  andnodes_reused: int,
  edge_node_attempts: int,
  edge_nodes_created: int,
  edge_nodes_reused: int,
  edge_attempts: int,
  edges_created: int,
  edge_reuses: int,
  or_expansion_attempts: int,
  or_expansions_started: int};

type abduction_graph_state =
 {graph: abduction_graph,
  statistics: graph_update_statistics};

type synched_abduction_graph = abduction_graph_state Synchronized.var;

fun empty_graph_update_statistics () =
 {node_attempts = 0,
  nodes_created = 0,
  node_reuses = 0,
  ornode_attempts = 0,
  ornodes_created = 0,
  ornodes_reused = 0,
  andnode_attempts = 0,
  andnodes_created = 0,
  andnodes_reused = 0,
  edge_node_attempts = 0,
  edge_nodes_created = 0,
  edge_nodes_reused = 0,
  edge_attempts = 0,
  edges_created = 0,
  edge_reuses = 0,
  or_expansion_attempts = 0,
  or_expansions_started = 0}: graph_update_statistics;

fun value_of_graph (sagraph:synched_abduction_graph) =
  #graph (Synchronized.value sagraph): abduction_graph;

fun graph_update_statistics (sagraph:synched_abduction_graph) =
  #statistics (Synchronized.value sagraph): graph_update_statistics;

fun mk_synched_abduction_graph (ctxt:Proof.context) (goal:term) =
  let
    val initial_graph_wo_imp = AG.mk_initial_graph ctxt goal;
    val initial_graph_w_imp  = UAG.update_importance (AG.Or_N, [goal]) 1.0 initial_graph_wo_imp;
    val initial_statistics =
      let
        val st = empty_graph_update_statistics ();
      in
        {node_attempts = #node_attempts st + 1,
         nodes_created = #nodes_created st + 1,
         node_reuses = #node_reuses st,
         ornode_attempts = #ornode_attempts st + 1,
         ornodes_created = #ornodes_created st + 1,
         ornodes_reused = #ornodes_reused st,
         andnode_attempts = #andnode_attempts st,
         andnodes_created = #andnodes_created st,
         andnodes_reused = #andnodes_reused st,
         edge_node_attempts = #edge_node_attempts st,
         edge_nodes_created = #edge_nodes_created st,
         edge_nodes_reused = #edge_nodes_reused st,
         edge_attempts = #edge_attempts st,
         edges_created = #edges_created st,
         edge_reuses = #edge_reuses st,
         or_expansion_attempts = #or_expansion_attempts st,
         or_expansions_started = #or_expansions_started st}
      end: graph_update_statistics;
  in
    Synchronized.var "abduction_graph" {graph = initial_graph_w_imp, statistics = initial_statistics}
  end;

fun node_defined (graph:abduction_graph) (key:AG.key): bool =
  (AG.PGraph.get_node graph key; true) handle AG.PGraph.UNDEF _ => false;

fun edge_defined (graph:abduction_graph) (parent_key:AG.key, child_key:AG.key): bool =
  member AG.equal_keys (AG.PGraph.immediate_succs graph parent_key) child_key
  handle AG.PGraph.UNDEF _ => false;

fun bump_node_statistics (key:AG.key) (created:bool)
    ({node_attempts, nodes_created, node_reuses,
      ornode_attempts, ornodes_created, ornodes_reused,
      andnode_attempts, andnodes_created, andnodes_reused,
      edge_node_attempts, edge_nodes_created, edge_nodes_reused,
      edge_attempts, edges_created, edge_reuses,
      or_expansion_attempts, or_expansions_started}:graph_update_statistics) =
  let
    val is_or = AG.is_ornode key;
    val is_and = AG.is_andnode key;
    val is_edge_node = AG.is_or2and_edge key;
  in
   {node_attempts = node_attempts + 1,
    nodes_created = nodes_created + (if created then 1 else 0),
    node_reuses = node_reuses + (if created then 0 else 1),
    ornode_attempts = ornode_attempts + (if is_or then 1 else 0),
    ornodes_created = ornodes_created + (if is_or andalso created then 1 else 0),
    ornodes_reused = ornodes_reused + (if is_or andalso not created then 1 else 0),
    andnode_attempts = andnode_attempts + (if is_and then 1 else 0),
    andnodes_created = andnodes_created + (if is_and andalso created then 1 else 0),
    andnodes_reused = andnodes_reused + (if is_and andalso not created then 1 else 0),
    edge_node_attempts = edge_node_attempts + (if is_edge_node then 1 else 0),
    edge_nodes_created = edge_nodes_created + (if is_edge_node andalso created then 1 else 0),
    edge_nodes_reused = edge_nodes_reused + (if is_edge_node andalso not created then 1 else 0),
    edge_attempts = edge_attempts,
    edges_created = edges_created,
    edge_reuses = edge_reuses,
    or_expansion_attempts = or_expansion_attempts,
    or_expansions_started = or_expansions_started}
  end;

fun bump_edge_statistics (created:bool)
    ({node_attempts, nodes_created, node_reuses,
      ornode_attempts, ornodes_created, ornodes_reused,
      andnode_attempts, andnodes_created, andnodes_reused,
      edge_node_attempts, edge_nodes_created, edge_nodes_reused,
      edge_attempts, edges_created, edge_reuses,
      or_expansion_attempts, or_expansions_started}:graph_update_statistics) =
   {node_attempts = node_attempts,
    nodes_created = nodes_created,
    node_reuses = node_reuses,
    ornode_attempts = ornode_attempts,
    ornodes_created = ornodes_created,
    ornodes_reused = ornodes_reused,
    andnode_attempts = andnode_attempts,
    andnodes_created = andnodes_created,
    andnodes_reused = andnodes_reused,
    edge_node_attempts = edge_node_attempts,
    edge_nodes_created = edge_nodes_created,
    edge_nodes_reused = edge_nodes_reused,
    edge_attempts = edge_attempts + 1,
    edges_created = edges_created + (if created then 1 else 0),
    edge_reuses = edge_reuses + (if created then 0 else 1),
    or_expansion_attempts = or_expansion_attempts,
    or_expansions_started = or_expansions_started};

fun bump_expansion_statistics (started:bool)
    ({node_attempts, nodes_created, node_reuses,
      ornode_attempts, ornodes_created, ornodes_reused,
      andnode_attempts, andnodes_created, andnodes_reused,
      edge_node_attempts, edge_nodes_created, edge_nodes_reused,
      edge_attempts, edges_created, edge_reuses,
      or_expansion_attempts, or_expansions_started}:graph_update_statistics) =
   {node_attempts = node_attempts,
    nodes_created = nodes_created,
    node_reuses = node_reuses,
    ornode_attempts = ornode_attempts,
    ornodes_created = ornodes_created,
    ornodes_reused = ornodes_reused,
    andnode_attempts = andnode_attempts,
    andnodes_created = andnodes_created,
    andnodes_reused = andnodes_reused,
    edge_node_attempts = edge_node_attempts,
    edge_nodes_created = edge_nodes_created,
    edge_nodes_reused = edge_nodes_reused,
    edge_attempts = edge_attempts,
    edges_created = edges_created,
    edge_reuses = edge_reuses,
    or_expansion_attempts = or_expansion_attempts + 1,
    or_expansions_started = or_expansions_started + (if started then 1 else 0)};

fun add_node_measured (key:AG.key, node:AG.abduction_node)
    ({graph, statistics}:abduction_graph_state): abduction_graph_state =
  let
    val existed = node_defined graph key: bool;
    val graph' = if existed then graph else AG.PGraph.new_node (key, node) graph;
    val statistics' = bump_node_statistics key (not existed) statistics;
  in
    {graph = graph', statistics = statistics'}
  end;

fun add_edge_measured (parent_key:AG.key, child_key:AG.key)
    ({graph, statistics}:abduction_graph_state): abduction_graph_state =
  let
    val existed = edge_defined graph (parent_key, child_key): bool;
    val graph' = if existed then graph else AG.PGraph.add_edge (parent_key, child_key) graph;
    val statistics' = bump_edge_statistics (not existed) statistics;
  in
    {graph = graph', statistics = statistics'}
  end;

fun change_graph f (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph (fn {graph, statistics} => {graph = f graph, statistics = statistics});

fun update_is_branch (key:AG.key) (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph
    (fn ({graph, statistics}:abduction_graph_state) =>
      let
        val was_branch = node_defined graph key andalso AG.is_branch graph key;
        val graph' = UAG.update_is_branch key graph;
        val statistics' = bump_expansion_statistics (not was_branch) statistics;
      in
        {graph = graph', statistics = statistics'}
      end): unit;

fun add_andnodes (andterms:terms) (sagraph:synched_abduction_graph) =
  let
    val pair as (and_key, _) = AG.mk_andnode andterms;
  in
    Synchronized.change_result sagraph
      (fn state => ([and_key], add_node_measured pair state)): AG.keys
  end;

fun add_child_ornode (ctxt:Proof.context) (sagraph:synched_abduction_graph) (lemma_name:string, lemma_term:term) =
  let
    val pair = AG.mk_ornode ctxt false lemma_name lemma_term;
  in
    Synchronized.change sagraph (add_node_measured pair): unit
  end;

fun add_edges_from_andnode_to_ornodes (and_key as (AG.And_N, terms):AG.key) (sagraph:synched_abduction_graph) =
  let
    val ornode_keys = map (fn trm => (AG.Or_N, [trm])) terms: AG.keys;
  in
    Synchronized.change sagraph
      (fn state => fold (fn target_key => add_edge_measured (and_key, target_key)) ornode_keys state): unit
  end
 | add_edges_from_andnode_to_ornodes _ _ = error "add_edges_from_andnode_to_ornodes failed.";

fun update_proved_completely (key:AG.key) (sagraph:synched_abduction_graph) =
  change_graph (UAG.update_proved_completely key) sagraph: unit;

fun update_proof_n_proof_id (proof:strings) (key:AG.key) (sagraph:synched_abduction_graph) =
  change_graph (UAG.update_proof_n_proof_id proof key) sagraph: unit;

fun update_importance_of_ornode (sagraph:synched_abduction_graph) (orkey:AG.key) =
  change_graph (UAG.update_importance_of_ornode orkey) sagraph: unit;

fun update_attacked (sagraph:synched_abduction_graph) (orkey:AG.key) =
  change_graph (UAG.update_attacked orkey) sagraph: unit;

fun update_after_proving_ornode (proof:strings) (orkey:AG.key) (ctxt:Proof.context) (sagraph:synched_abduction_graph) =
  change_graph (UAG.update_after_proving_ornode proof orkey ctxt) sagraph: unit;

fun update_after_connecting_andnd_to_existing_ornd' (ctxt:Proof.context) (sagraph:synched_abduction_graph) (orkey:AG.key) =
  change_graph (UAG.update_after_connecting_andnd_to_existing_ornd orkey ctxt) sagraph: unit;

fun update_after_connecting_andnd_to_existing_ornd (ctxt:Proof.context) (sagraph:synched_abduction_graph) (orkeys:AG.keys) =
  map (update_after_connecting_andnd_to_existing_ornd' ctxt sagraph) orkeys;

fun try_to_prove_ornode_and_update_graph (pst:Proof.state) (sagraph:synched_abduction_graph) (orkey:AG.key) =
  let
    val graph       = value_of_graph sagraph                 : abduction_graph;
    val maybe_proof = AG.prove_orkey_completely orkey graph pst: strings option;
    val _           = update_attacked sagraph orkey          : unit;
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
  AG.final_goal_proved_completely (value_of_graph sagraph): bool;

fun new_node (key: AG.key, node:AG.abduction_node) (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph (add_node_measured (key, node)): unit;

fun add_edge (parent_key: AG.key, child_key: AG.key) (sagraph:synched_abduction_graph) =
  Synchronized.change sagraph (add_edge_measured (parent_key, child_key)): unit;

end;

(*** signature TOP_DOWN_CONJECTURING ***)
signature TOP_DOWN_CONJECTURING =
sig

val top_down_conjectures: Shared_State.synched_term2string_table -> Proof.state -> term -> (string * term) list;

end;