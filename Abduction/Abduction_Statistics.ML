(*
 * Abduction_Statistics.ML
 *
 * Structured statistics for AbductionProver evaluation.
 *)

signature ABDUCTION_STATISTICS =
sig

type loop_entry =
 {depth: int,
  reachable_keys: int,
  reachable_or_nodes: int,
  reachable_or_leaf_nodes: int,
  worth_expanding: int,
  selected_ornodes: int,
  selection_rate: real,
  num_processors: int,
  graph_nodes: int,
  graph_edges: int,
  graph_or_nodes: int,
  graph_and_nodes: int,
  graph_or2and_edge_nodes: int,
  graph_avg_indegree: real,
  graph_max_indegree: int,
  graph_scc_count: int,
  graph_cyclic_scc_count: int,
  graph_largest_scc_size: int,
  graph_or_projected_edges: int,
  graph_or_projected_avg_indegree: real,
  graph_or_projected_max_indegree: int,
  graph_or_projected_scc_count: int,
  graph_or_projected_cyclic_scc_count: int,
  graph_or_projected_largest_scc_size: int,
  graph_and_projected_edges: int,
  graph_and_projected_avg_indegree: real,
  graph_and_projected_max_indegree: int,
  graph_and_projected_scc_count: int,
  graph_and_projected_cyclic_scc_count: int,
  graph_and_projected_largest_scc_size: int,
  graph_node_attempts: int,
  graph_nodes_created: int,
  graph_node_reuses: int,
  graph_node_reuse_rate: real,
  graph_ornode_attempts: int,
  graph_ornodes_created: int,
  graph_ornodes_reused: int,
  graph_ornode_reuse_rate: real,
  graph_andnode_attempts: int,
  graph_andnodes_created: int,
  graph_andnodes_reused: int,
  graph_andnode_reuse_rate: real,
  graph_edge_node_attempts: int,
  graph_edge_nodes_created: int,
  graph_edge_nodes_reused: int,
  graph_edge_node_reuse_rate: real,
  graph_edge_attempts: int,
  graph_edges_created: int,
  graph_edge_reuses: int,
  graph_edge_reuse_rate: real,
  or_expansion_attempts: int,
  or_expansions_started: int,
  or_expansion_reuse_rate: real,
  refutation_cache_size: int,
  refutation_cache_hits: int,
  refutation_cache_misses: int,
  refutation_cache_hit_rate: real,
  filter_refutation_checked: int,
  filter_refutation_refuted: int,
  filter_refutation_survived: int,
  filter_refutation_survival_rate: real,
  filter_abduction_checked_conjectures: int,
  filter_abduction_used_conjectures: int,
  filter_abduction_discarded_conjectures: int,
  filter_abduction_retention_rate: real,
  filter_orelse_rejected_conjectures: int,
  filter_orelse_too_large: int,
  filter_orelse_eq_to_final_goal_from_tactic: int,
  filter_orelse_concl_is_eq_to_final_goal: int,
  filter_orelse_has_func_with_three_occs_in_a_row: int,
  filter_orelse_concls_are_same: int,
  filter_orelse_concl_of_conj_refuted: int,
  elapsed_sec: real};

type decremental_entry =
 {top_loop_index: int,
  parent_or_name: string,
  is_root_or_node: bool,
  decremental_round_index: int,
  decremental_limit: int,
  candidate_sets_before: int,
  selected_sets: int,
  carried_over_sets: int,
  skipped_duplicate_sets: int,
  skipped_subsumed_sets: int,
  actual_proof_attempts: int,
  successful_attempts: int,
  failed_attempts: int,
  decremental_exact_duplicate_hits: int,
  decremental_failed_subsumption_hits: int,
  decremental_cache_hits: int,
  decremental_cache_misses: int,
  decremental_exact_duplicate_hit_rate: real,
  decremental_avoidance_rate: real,
  new_sets: int,
  candidate_sets_after: int,
  accepted_edges_in_round: int,
  accepted_edges_so_far: int,
  selected_cardinality_min: int,
  selected_cardinality_median: int,
  selected_cardinality_max: int,
  attempted_cardinality_min: int,
  attempted_cardinality_median: int,
  attempted_cardinality_max: int,
  next_cardinality_min: int,
  next_cardinality_median: int,
  next_cardinality_max: int,
  selected_depth_min: int,
  selected_depth_median: int,
  selected_depth_max: int,
  attempted_depth_min: int,
  attempted_depth_median: int,
  attempted_depth_max: int,
  next_depth_min: int,
  next_depth_median: int,
  next_depth_max: int,
  decremental_elapsed_sec: real};

type statistics;
type synched_statistics = statistics Synchronized.var;

val mk_statistics: unit -> synched_statistics;
val enabled: unit -> bool;
val record_loop: Proof.state -> synched_statistics -> loop_entry -> unit;
val record_decremental_entries: Proof.state -> decremental_entry list -> unit;

end;

structure Abduction_Statistics: ABDUCTION_STATISTICS =
struct

type loop_entry =
 {depth: int,
  reachable_keys: int,
  reachable_or_nodes: int,
  reachable_or_leaf_nodes: int,
  worth_expanding: int,
  selected_ornodes: int,
  selection_rate: real,
  num_processors: int,
  graph_nodes: int,
  graph_edges: int,
  graph_or_nodes: int,
  graph_and_nodes: int,
  graph_or2and_edge_nodes: int,
  graph_avg_indegree: real,
  graph_max_indegree: int,
  graph_scc_count: int,
  graph_cyclic_scc_count: int,
  graph_largest_scc_size: int,
  graph_or_projected_edges: int,
  graph_or_projected_avg_indegree: real,
  graph_or_projected_max_indegree: int,
  graph_or_projected_scc_count: int,
  graph_or_projected_cyclic_scc_count: int,
  graph_or_projected_largest_scc_size: int,
  graph_and_projected_edges: int,
  graph_and_projected_avg_indegree: real,
  graph_and_projected_max_indegree: int,
  graph_and_projected_scc_count: int,
  graph_and_projected_cyclic_scc_count: int,
  graph_and_projected_largest_scc_size: int,
  graph_node_attempts: int,
  graph_nodes_created: int,
  graph_node_reuses: int,
  graph_node_reuse_rate: real,
  graph_ornode_attempts: int,
  graph_ornodes_created: int,
  graph_ornodes_reused: int,
  graph_ornode_reuse_rate: real,
  graph_andnode_attempts: int,
  graph_andnodes_created: int,
  graph_andnodes_reused: int,
  graph_andnode_reuse_rate: real,
  graph_edge_node_attempts: int,
  graph_edge_nodes_created: int,
  graph_edge_nodes_reused: int,
  graph_edge_node_reuse_rate: real,
  graph_edge_attempts: int,
  graph_edges_created: int,
  graph_edge_reuses: int,
  graph_edge_reuse_rate: real,
  or_expansion_attempts: int,
  or_expansions_started: int,
  or_expansion_reuse_rate: real,
  refutation_cache_size: int,
  refutation_cache_hits: int,
  refutation_cache_misses: int,
  refutation_cache_hit_rate: real,
  filter_refutation_checked: int,
  filter_refutation_refuted: int,
  filter_refutation_survived: int,
  filter_refutation_survival_rate: real,
  filter_abduction_checked_conjectures: int,
  filter_abduction_used_conjectures: int,
  filter_abduction_discarded_conjectures: int,
  filter_abduction_retention_rate: real,
  filter_orelse_rejected_conjectures: int,
  filter_orelse_too_large: int,
  filter_orelse_eq_to_final_goal_from_tactic: int,
  filter_orelse_concl_is_eq_to_final_goal: int,
  filter_orelse_has_func_with_three_occs_in_a_row: int,
  filter_orelse_concls_are_same: int,
  filter_orelse_concl_of_conj_refuted: int,
  elapsed_sec: real};

type decremental_entry =
 {top_loop_index: int,
  parent_or_name: string,
  is_root_or_node: bool,
  decremental_round_index: int,
  decremental_limit: int,
  candidate_sets_before: int,
  selected_sets: int,
  carried_over_sets: int,
  skipped_duplicate_sets: int,
  skipped_subsumed_sets: int,
  actual_proof_attempts: int,
  successful_attempts: int,
  failed_attempts: int,
  decremental_exact_duplicate_hits: int,
  decremental_failed_subsumption_hits: int,
  decremental_cache_hits: int,
  decremental_cache_misses: int,
  decremental_exact_duplicate_hit_rate: real,
  decremental_avoidance_rate: real,
  new_sets: int,
  candidate_sets_after: int,
  accepted_edges_in_round: int,
  accepted_edges_so_far: int,
  selected_cardinality_min: int,
  selected_cardinality_median: int,
  selected_cardinality_max: int,
  attempted_cardinality_min: int,
  attempted_cardinality_median: int,
  attempted_cardinality_max: int,
  next_cardinality_min: int,
  next_cardinality_median: int,
  next_cardinality_max: int,
  selected_depth_min: int,
  selected_depth_median: int,
  selected_depth_max: int,
  attempted_depth_min: int,
  attempted_depth_median: int,
  attempted_depth_max: int,
  next_depth_min: int,
  next_depth_median: int,
  next_depth_max: int,
  decremental_elapsed_sec: real};

type statistics = {loop_entries: loop_entry list};
type synched_statistics = statistics Synchronized.var;

fun mk_statistics () =
  Synchronized.var "Abduction_Statistics.statistics" {loop_entries = []}: synched_statistics;

fun safe_char c =
  if Char.isAlphaNum c orelse c = #"_" then str c else "_";

fun safe_name s = String.translate safe_char s;

fun theory_name_of_pst pst =
  Proof.context_of pst
  |> Local_Theory.exit_global
  |> Context.theory_name {long = true}
  |> safe_name;

fun stats_dir () = getenv "PSL_EVAL_ABDUCTION_STATS_DIR";

fun enabled () = getenv "PSL_EVAL_MODE" = "1" andalso stats_dir () <> "";

fun base_path pst suffix =
  Path.append (Path.explode (stats_dir ()))
    (Path.basic ("abduction_" ^ theory_name_of_pst pst ^ suffix));

fun int_to_csv i = Int.toString i;
fun real_to_csv r = Real.toString r;
fun bool_to_csv b = if b then "true" else "false";

fun needs_csv_quotes s =
  exists (fn c => c = #"," orelse c = #"\"" orelse c = #"\n" orelse c = #"\r") (String.explode s);

fun quote_csv_char #"\"" = "\"\""
  | quote_csv_char c = str c;

fun string_to_csv s =
  let
    val escaped = String.translate quote_csv_char s;
  in
    if needs_csv_quotes s then "\"" ^ escaped ^ "\"" else escaped
  end;

fun append_line_with_header path header line =
  if File.exists path
  then File.append path line
  else File.write path (header ^ line);

val loop_header =
  "depth,reachable_keys,reachable_or_nodes,reachable_or_leaf_nodes,worth_expanding,selected_ornodes,selection_rate,num_processors,graph_nodes,graph_edges,graph_or_nodes,graph_and_nodes,graph_or2and_edge_nodes,graph_avg_indegree,graph_max_indegree,graph_scc_count,graph_cyclic_scc_count,graph_largest_scc_size,graph_or_projected_edges,graph_or_projected_avg_indegree,graph_or_projected_max_indegree,graph_or_projected_scc_count,graph_or_projected_cyclic_scc_count,graph_or_projected_largest_scc_size,graph_and_projected_edges,graph_and_projected_avg_indegree,graph_and_projected_max_indegree,graph_and_projected_scc_count,graph_and_projected_cyclic_scc_count,graph_and_projected_largest_scc_size,graph_node_attempts,graph_nodes_created,graph_node_reuses,graph_node_reuse_rate,graph_ornode_attempts,graph_ornodes_created,graph_ornodes_reused,graph_ornode_reuse_rate,graph_andnode_attempts,graph_andnodes_created,graph_andnodes_reused,graph_andnode_reuse_rate,graph_edge_node_attempts,graph_edge_nodes_created,graph_edge_nodes_reused,graph_edge_node_reuse_rate,graph_edge_attempts,graph_edges_created,graph_edge_reuses,graph_edge_reuse_rate,or_expansion_attempts,or_expansions_started,or_expansion_reuse_rate,refutation_cache_size,refutation_cache_hits,refutation_cache_misses,refutation_cache_hit_rate,filter_refutation_checked,filter_refutation_refuted,filter_refutation_survived,filter_refutation_survival_rate,filter_abduction_checked_conjectures,filter_abduction_used_conjectures,filter_abduction_discarded_conjectures,filter_abduction_retention_rate,filter_orelse_rejected_conjectures,filter_orelse_too_large,filter_orelse_eq_to_final_goal_from_tactic,filter_orelse_concl_is_eq_to_final_goal,filter_orelse_has_func_with_three_occs_in_a_row,filter_orelse_concls_are_same,filter_orelse_concl_of_conj_refuted,elapsed_sec\n";

fun loop_entry_to_csv
    ({depth, reachable_keys, reachable_or_nodes, reachable_or_leaf_nodes, worth_expanding, selected_ornodes, selection_rate,
      num_processors, graph_nodes, graph_edges, graph_or_nodes, graph_and_nodes,
      graph_or2and_edge_nodes, graph_avg_indegree, graph_max_indegree,
      graph_scc_count, graph_cyclic_scc_count, graph_largest_scc_size,
      graph_or_projected_edges, graph_or_projected_avg_indegree,
      graph_or_projected_max_indegree, graph_or_projected_scc_count,
      graph_or_projected_cyclic_scc_count, graph_or_projected_largest_scc_size,
      graph_and_projected_edges, graph_and_projected_avg_indegree,
      graph_and_projected_max_indegree, graph_and_projected_scc_count,
      graph_and_projected_cyclic_scc_count, graph_and_projected_largest_scc_size,
      graph_node_attempts, graph_nodes_created, graph_node_reuses, graph_node_reuse_rate,
      graph_ornode_attempts, graph_ornodes_created, graph_ornodes_reused, graph_ornode_reuse_rate,
      graph_andnode_attempts, graph_andnodes_created, graph_andnodes_reused, graph_andnode_reuse_rate,
      graph_edge_node_attempts, graph_edge_nodes_created, graph_edge_nodes_reused, graph_edge_node_reuse_rate,
      graph_edge_attempts, graph_edges_created, graph_edge_reuses, graph_edge_reuse_rate,
      or_expansion_attempts, or_expansions_started, or_expansion_reuse_rate,
      refutation_cache_size, refutation_cache_hits, refutation_cache_misses,
      refutation_cache_hit_rate,
      filter_refutation_checked, filter_refutation_refuted, filter_refutation_survived,
      filter_refutation_survival_rate,
      filter_abduction_checked_conjectures, filter_abduction_used_conjectures,
      filter_abduction_discarded_conjectures, filter_abduction_retention_rate,
      filter_orelse_rejected_conjectures, filter_orelse_too_large,
      filter_orelse_eq_to_final_goal_from_tactic, filter_orelse_concl_is_eq_to_final_goal,
      filter_orelse_has_func_with_three_occs_in_a_row, filter_orelse_concls_are_same,
      filter_orelse_concl_of_conj_refuted,
      elapsed_sec}: loop_entry) =
  String.concatWith ","
    [int_to_csv depth,
     int_to_csv reachable_keys,
     int_to_csv reachable_or_nodes,
     int_to_csv reachable_or_leaf_nodes,
     int_to_csv worth_expanding,
     int_to_csv selected_ornodes,
     real_to_csv selection_rate,
     int_to_csv num_processors,
     int_to_csv graph_nodes,
     int_to_csv graph_edges,
     int_to_csv graph_or_nodes,
     int_to_csv graph_and_nodes,
     int_to_csv graph_or2and_edge_nodes,
     real_to_csv graph_avg_indegree,
     int_to_csv graph_max_indegree,
     int_to_csv graph_scc_count,
     int_to_csv graph_cyclic_scc_count,
     int_to_csv graph_largest_scc_size,
     int_to_csv graph_or_projected_edges,
     real_to_csv graph_or_projected_avg_indegree,
     int_to_csv graph_or_projected_max_indegree,
     int_to_csv graph_or_projected_scc_count,
     int_to_csv graph_or_projected_cyclic_scc_count,
     int_to_csv graph_or_projected_largest_scc_size,
     int_to_csv graph_and_projected_edges,
     real_to_csv graph_and_projected_avg_indegree,
     int_to_csv graph_and_projected_max_indegree,
     int_to_csv graph_and_projected_scc_count,
     int_to_csv graph_and_projected_cyclic_scc_count,
     int_to_csv graph_and_projected_largest_scc_size,
     int_to_csv graph_node_attempts,
     int_to_csv graph_nodes_created,
     int_to_csv graph_node_reuses,
     real_to_csv graph_node_reuse_rate,
     int_to_csv graph_ornode_attempts,
     int_to_csv graph_ornodes_created,
     int_to_csv graph_ornodes_reused,
     real_to_csv graph_ornode_reuse_rate,
     int_to_csv graph_andnode_attempts,
     int_to_csv graph_andnodes_created,
     int_to_csv graph_andnodes_reused,
     real_to_csv graph_andnode_reuse_rate,
     int_to_csv graph_edge_node_attempts,
     int_to_csv graph_edge_nodes_created,
     int_to_csv graph_edge_nodes_reused,
     real_to_csv graph_edge_node_reuse_rate,
     int_to_csv graph_edge_attempts,
     int_to_csv graph_edges_created,
     int_to_csv graph_edge_reuses,
     real_to_csv graph_edge_reuse_rate,
     int_to_csv or_expansion_attempts,
     int_to_csv or_expansions_started,
     real_to_csv or_expansion_reuse_rate,
     int_to_csv refutation_cache_size,
     int_to_csv refutation_cache_hits,
     int_to_csv refutation_cache_misses,
     real_to_csv refutation_cache_hit_rate,
     int_to_csv filter_refutation_checked,
     int_to_csv filter_refutation_refuted,
     int_to_csv filter_refutation_survived,
     real_to_csv filter_refutation_survival_rate,
     int_to_csv filter_abduction_checked_conjectures,
     int_to_csv filter_abduction_used_conjectures,
     int_to_csv filter_abduction_discarded_conjectures,
     real_to_csv filter_abduction_retention_rate,
     int_to_csv filter_orelse_rejected_conjectures,
     int_to_csv filter_orelse_too_large,
     int_to_csv filter_orelse_eq_to_final_goal_from_tactic,
     int_to_csv filter_orelse_concl_is_eq_to_final_goal,
     int_to_csv filter_orelse_has_func_with_three_occs_in_a_row,
     int_to_csv filter_orelse_concls_are_same,
     int_to_csv filter_orelse_concl_of_conj_refuted,
     real_to_csv elapsed_sec] ^ "\n";

fun write_loop_entry pst entry =
  if enabled ()
  then append_line_with_header (base_path pst ".loops.csv") loop_header (loop_entry_to_csv entry)
  else ();

fun record_loop pst synched_statistics entry =
  if not (enabled ())
  then ()
  else
    let
      val _ =
        Synchronized.change synched_statistics
          (fn {loop_entries} => {loop_entries = entry :: loop_entries});
      val _ = write_loop_entry pst entry;
    in
      ()
    end;

val decremental_header =
  "top_loop_index,parent_or_name,is_root_or_node,decremental_round_index,decremental_limit,candidate_sets_before,selected_sets,carried_over_sets,skipped_duplicate_sets,skipped_subsumed_sets,actual_proof_attempts,successful_attempts,failed_attempts,decremental_exact_duplicate_hits,decremental_failed_subsumption_hits,decremental_cache_hits,decremental_cache_misses,decremental_exact_duplicate_hit_rate,decremental_avoidance_rate,new_sets,candidate_sets_after,accepted_edges_in_round,accepted_edges_so_far,selected_cardinality_min,selected_cardinality_median,selected_cardinality_max,attempted_cardinality_min,attempted_cardinality_median,attempted_cardinality_max,next_cardinality_min,next_cardinality_median,next_cardinality_max,selected_depth_min,selected_depth_median,selected_depth_max,attempted_depth_min,attempted_depth_median,attempted_depth_max,next_depth_min,next_depth_median,next_depth_max,decremental_elapsed_sec\n";

fun decremental_entry_to_csv
    ({top_loop_index, parent_or_name, is_root_or_node, decremental_round_index,
      decremental_limit, candidate_sets_before, selected_sets, carried_over_sets,
      skipped_duplicate_sets, skipped_subsumed_sets, actual_proof_attempts,
      successful_attempts, failed_attempts, decremental_exact_duplicate_hits,
      decremental_failed_subsumption_hits, decremental_cache_hits,
      decremental_cache_misses, decremental_exact_duplicate_hit_rate,
      decremental_avoidance_rate, new_sets, candidate_sets_after,
      accepted_edges_in_round, accepted_edges_so_far,
      selected_cardinality_min, selected_cardinality_median, selected_cardinality_max,
      attempted_cardinality_min, attempted_cardinality_median, attempted_cardinality_max,
      next_cardinality_min, next_cardinality_median, next_cardinality_max,
      selected_depth_min, selected_depth_median, selected_depth_max,
      attempted_depth_min, attempted_depth_median, attempted_depth_max,
      next_depth_min, next_depth_median, next_depth_max,
      decremental_elapsed_sec}: decremental_entry) =
  String.concatWith ","
    [int_to_csv top_loop_index,
     string_to_csv parent_or_name,
     bool_to_csv is_root_or_node,
     int_to_csv decremental_round_index,
     int_to_csv decremental_limit,
     int_to_csv candidate_sets_before,
     int_to_csv selected_sets,
     int_to_csv carried_over_sets,
     int_to_csv skipped_duplicate_sets,
     int_to_csv skipped_subsumed_sets,
     int_to_csv actual_proof_attempts,
     int_to_csv successful_attempts,
     int_to_csv failed_attempts,
     int_to_csv decremental_exact_duplicate_hits,
     int_to_csv decremental_failed_subsumption_hits,
     int_to_csv decremental_cache_hits,
     int_to_csv decremental_cache_misses,
     real_to_csv decremental_exact_duplicate_hit_rate,
     real_to_csv decremental_avoidance_rate,
     int_to_csv new_sets,
     int_to_csv candidate_sets_after,
     int_to_csv accepted_edges_in_round,
     int_to_csv accepted_edges_so_far,
     int_to_csv selected_cardinality_min,
     int_to_csv selected_cardinality_median,
     int_to_csv selected_cardinality_max,
     int_to_csv attempted_cardinality_min,
     int_to_csv attempted_cardinality_median,
     int_to_csv attempted_cardinality_max,
     int_to_csv next_cardinality_min,
     int_to_csv next_cardinality_median,
     int_to_csv next_cardinality_max,
     int_to_csv selected_depth_min,
     int_to_csv selected_depth_median,
     int_to_csv selected_depth_max,
     int_to_csv attempted_depth_min,
     int_to_csv attempted_depth_median,
     int_to_csv attempted_depth_max,
     int_to_csv next_depth_min,
     int_to_csv next_depth_median,
     int_to_csv next_depth_max,
     real_to_csv decremental_elapsed_sec] ^ "\n";

fun record_decremental_entries pst entries =
  if enabled ()
  then
    let
      val path = base_path pst ".decremental.csv";
      val lines = map decremental_entry_to_csv entries |> String.concat;
    in
      if lines = "" then ()
      else append_line_with_header path decremental_header lines
    end
  else ();

end;
